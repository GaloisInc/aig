module Data.AIG.Operations 
  ( BV
  , length
  , at
  , (!)
  , generateM_msb0
  , generate_msb0
  , replicate
  , bvFromInteger
  , asUnsigned
  , asSigned
  , bvToList

  , neg
  , add
  , sub
  , mul

  , squot
  , srem
  , uquot
  , urem
 
  , shl
  , sshr
  , ushr
  , rol
  , ror
  , bvEq
  , sle
  , slt
  , ule
  , ult
  , sext
  , zext
  , msb

  , (++)
  , concat
  , slice
  , zipWithM
  
  ) where

import Control.Applicative
import Control.Exception
import Control.Monad.State hiding (zipWithM)
import Data.Bits ((.|.), setBit, shiftL, testBit)
import qualified Data.Vector as V
import Prelude hiding (and, concat, length, not, or, replicate, splitAt, tail, (++))

import Data.AIG.Interface

-- | A full adder which takes three inputs and returns output and carry.
halfAdder :: IsAIG l g => g s -> l s -> l s -> IO (l s, l s)
halfAdder g b c = do
  b_or_c <- or g b c
  c_out <- and g b c
  s <- and g b_or_c (not c_out)
  return (s, c_out)

-- | A full adder which takes three inputs and returns output and carry.
fullAdder :: IsAIG l g => g s -> l s -> l s -> l s -> IO (l s, l s)
fullAdder g a b c_in = do
  a_xor_b <- xor g a b
  s <- xor g a_xor_b c_in
  a_and_b <- and g a b
  c_out <- or g a_and_b =<< and g a_xor_b c_in
  return (s, c_out)

-- | A new symbolic integer.
newtype BV l = BV { unBV :: V.Vector l }

instance Functor BV where
  fmap f (BV v) = BV (f <$> v)

length :: BV l -> Int
length (BV v) = V.length v

tail :: BV l -> BV l
tail (BV v) = BV (V.tail v)

generate_lsb0 :: Int -> (Int -> l) -> BV l
generate_lsb0 c f = BV (V.generate c (\i -> f ((c-1)-i)))

generateM_lsb0 :: Monad m => Int -> (Int -> m l) -> m (BV l)
generateM_lsb0 c f = return . BV . V.reverse =<< V.generateM c (\i -> f ((c-1)-i))

generate_msb0 :: Int -> (Int -> l) -> BV l
generate_msb0 c f = BV (V.generate c f)

generateM_msb0 :: Monad m => Int -> (Int -> m l) -> m (BV l)
generateM_msb0 c f = return . BV =<< V.generateM c f

replicate :: Int -> l -> BV l
replicate c e = BV (V.replicate c e)

-- | x `at` 0 is the most significant bit.
at :: BV l -> Int -> l
at (BV v) i = v V.! i

-- | Append two bitvectors, with the most significant bitvector given first.
(++) :: BV l -> BV l -> BV l
BV x ++ BV y = BV (x V.++ y)

concat :: [BV l] -> BV l
concat v = BV (V.concat (unBV <$> v))

slice :: BV l -> Int -> Int -> BV l
slice (BV v) i n = BV (V.slice i n v)

zipWithM :: (l -> l -> IO l) -> BV l -> BV l -> IO (BV l)
zipWithM f (BV x) (BV y) = assert (V.length x == V.length y) $
  BV <$> V.zipWithM f x y

-- | Convert a bitvector to a list, most significant bit first.
bvToList :: BV l -> [l]
bvToList (BV v) = V.toList v

-- | x ! 0 is the least significant bit.
(!) :: BV l -> Int -> l
(!) v i = v `at` (length v - 1 - i)

bvFromInteger :: IsAIG l g => g s -> Int -> Integer -> BV (l s)
bvFromInteger g n v = generate_lsb0 n $ \i -> constant g (v `testBit` i)

asUnsigned :: IsAIG l g => g s -> BV (l s) -> Maybe Integer
asUnsigned g v = go 0 0
  where n = length v
        go x i | i >= n = return x
        go x i = do
          b <- asConstant g (v `at` i)
          let y  = if b then 1 else 0
          let z = x `shiftL` 1 .|. y
          seq z $ go z (i+1)

asSigned :: IsAIG l g => g s -> BV (l s) -> Maybe Integer
asSigned g v = assert (n > 0) $ go 0 1
  where n = length v
        m = n-1
        go x i | i < m = do
          b <- asConstant g (v `at` i)
          let y  = if b then 1 else 0
          let z = x `shiftL` 1 .|. y
          seq z $ go z (i+1)
        go x i = do
          msbv <- asConstant g (v `at` i)
          return $ if msbv then x - 2^m
                           else x

msb :: BV l -> l
msb v = v `at` 0

ite :: IsAIG l g => g s -> l s -> BV (l s) -> BV (l s) -> IO (BV (l s))
ite g c x y = zipWithM (mux g c) x y

iteM :: IsAIG l g => g s -> l s -> IO (BV (l s)) -> IO (BV (l s)) -> IO (BV (l s))
iteM g c x y 
  | c === trueLit g = x
  | c === falseLit g = y
  | otherwise = join $ zipWithM (mux g c) <$> x <*> y

-- | Implements a ripple carry adder.
ripple_add :: IsAIG l g 
           => g s
           -> BV (l s)
           -> BV (l s)
           -> l s
           -> IO (BV (l s), l s)
ripple_add _ x _ c | length x == 0 = return (x, c)
ripple_add g x y c0 = do
  let unfold i = StateT $ \c -> do
        fullAdder g (x `at` i) (y `at` i) c
  runStateT (generateM_lsb0 (length x) unfold) c0

-- | A subtraction circuit which takes three inputs and returns output and carry.
fullSub :: IsAIG l g => g s -> l s -> l s -> l s -> IO (l s, l s)
fullSub g x y b_in = do
  y_eq_b <- eq g y b_in
  s <- eq g x y_eq_b

  y_and_b <- and g y b_in
  c2 <- and g (not x) =<< or g y b_in
  b_out <- or g y_and_b c2
  return (s, b_out)

-- | Subtract two bit vectors, returning result and borrow bit.
full_sub :: IsAIG l g
         => g s 
         -> BV (l s)
         -> BV (l s)
         -> IO (BV (l s), l s)
full_sub g x _ | length x == 0 = return (x,falseLit g)
full_sub g x y = do
  let unfold i = StateT $ \b -> fullSub g (x `at` i) (y `at` i) b
  runStateT (generateM_lsb0 (length x) unfold) (falseLit g)

-- | Negate the vector
neg :: IsAIG l g => g s -> BV (l s) -> IO (BV (l s))
neg g x = evalStateT (generateM_lsb0 (length x) unfold) (trueLit g)
  where unfold i = StateT $ \c -> halfAdder g (not (x `at` i)) c

-- | Add two bitvectors with the same size.
add :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
add g x y = fst <$> ripple_add g x y (falseLit g)

-- | Subtract one bitvector from another with the same size.
sub :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
sub g x y = fst <$> ripple_add g x (not <$> y) (trueLit g)

-- | Multiply two bitvectors with the same size.
mul :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
mul g x y = do
  -- Create mutable array to store result.
  let n = length y
  -- Function to update bits.
  let updateBits i z | i == n = return z
      updateBits i z = do
        z_inc <- add g z (shlC g x i)
        z' <- ite g (y ! i) z_inc z        
        updateBits (i+1) z'
  updateBits 0 $ replicate (length x) (falseLit g)

-- | Compute the quotient of two signed bitvectors with the same size.
squot :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
squot g x y = fst <$> squotRem g x y

-- | Compute the division remainder of two signed bitvectors with the same size.
srem :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
srem g x y = snd <$> squotRem g x y

-- | Cons value to head of a list and shift other elements to left.
shiftL1 :: BV l -> l -> BV l
shiftL1 (BV v) e = assert (V.length v > 0) $ BV (V.tail v `V.snoc` e)

-- | Cons value to start of list and shift other elements right.
shiftR1 :: l -> BV l -> BV l
shiftR1 e (BV v) = assert (V.length v > 0) $ BV (e `V.cons` V.init v)

splitAt :: Int -> BV l -> (BV l, BV l)
splitAt n (BV v) = (BV x, BV y)
  where (x,y) = V.splitAt n v

stepN :: Monad m => Int -> (a -> m a) -> a -> m a 
stepN n f x
  | n > 0 = stepN (n-1) f =<< f x
  | otherwise = return x

-- | Return absolute value of signed bitvector.
sabs :: IsAIG l g => g s -> BV (l s) -> IO (BV (l s))
sabs g x = assert (length x > 0) $ negWhen g x (msb x)


negWhen :: IsAIG l g => g s -> BV (l s) -> l s -> IO (BV (l s))
negWhen g x c = iteM g c (neg g x) (return x)

-- | Bitblast version of unsigned @quotRem@.
uquotRem :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s), BV (l s))
uquotRem g dividend divisor = do
  let n = length dividend
  assert (n == length divisor) $ do
    -- Given an n-bit dividend and divisor, 'initial' is the starting value of
    -- the 2n-bit "remainder register" that carries both the quotient and remainder;
    let initial = zext g dividend (2*n)
    let divStep i p rr | i == n = return (q `shiftL1` p, r)
          where (r,q) = splitAt n rr
        divStep i p rr = do
          let rs = rr `shiftL1` p
          let (r,q) = splitAt n rs
           -- Subtract the divisor from the left half of the "remainder register"
          (s,b) <- full_sub g r divisor
          divStep (i+1) (not b) =<< ite g b rs (s ++ q)
    divStep 0 (falseLit g) initial

-- Perform quotRem on the absolute value of the operands.  Then, negate the
-- quotient if the signs of the operands differ and make the sign of a nonzero
-- remainder to match that of the dividend.
squotRem :: IsAIG l g
         => g s
         -> BV (l s)
         -> BV (l s)
         -> IO (BV (l s), BV (l s))
squotRem g dividend' divisor' = do
  let n = length dividend'
  assert (n > 0 && n == length divisor') $ do
    let dsign = msb dividend'
    dividend <- sabs g dividend'
    divisor  <- sabs g divisor'
    -- Given an n-bit dividend and divisor, 'initial' is the starting value of
    -- the 2n-bit "remainder register" that carries both the quotient and remainder;
    let initial = zext g dividend (2*n)
    let divStep rrOrig = do
          let (r,q) = splitAt n rrOrig
          s <- sub g r divisor
          ite g (msb s)
                (rrOrig `shiftL1` falseLit g)     -- rem < 0, orig rr's quot lsl'd w/ 0
                ((s ++ q) `shiftL1` trueLit g) -- rem >= 0, new rr's quot lsl'd w/ 1
    (qr,rr) <- splitAt n <$> stepN n divStep (initial `shiftL1` falseLit g)
    q' <- negWhen g qr =<< xor g dsign (msb divisor')
    r' <- negWhen g (falseLit g `shiftR1` rr) dsign
    return (q', r')

-- | Compute the quotient of two unsigned bitvectors with the same size.
uquot :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
uquot g x y = fst <$> uquotRem g x y

-- | Compute the division remainder of two unsigned bitvectors with the same size.
urem :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
urem g x y = snd <$> uquotRem g x y

-- | Test equality of two bitvectors with the same size.
bvEq :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
bvEq g x y = go 0 (trueLit g)
  where n = length x
        go i r | i == n = return r
        go i r = go (i+1) =<< and g r =<< eq g (x `at` i) (y `at` i)

-- | Unsigned less-than on bitvector with the same size.
ult :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
ult g x y = snd <$> full_sub g x y

-- | Unsigned less-than-or-equal on bitvector with the same size.
ule :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
ule g x y = not <$> ult g y x

-- | Signed less-than on bitvector with the same size.
slt :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
slt g x y = do
  let xs = x `at` 0 
  let ys = y `at` 0
  -- x is negative and y is positive.
  c0 <- and g xs (not ys)
  -- x is positive and y is negative.
  c1 <- and g (not xs) ys
  c2 <- and g (not c1) =<< ult g (tail x) (tail y)
  or g c0 c2

-- | Signed less-than-or-equal on bitvector with the same size.
sle :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
sle g x y = not <$> slt g y x

-- | @sext v n@ sign extends @v@ to be a vector with length @n@.
-- This function requires that @n >= length v@ and @length v > 0@.
sext :: BV l -> Int -> BV l
sext v r = assert (r >= n && n > 0) $ replicate (r - n) (msb v) ++ v
  where n = length v

-- | @zext g v n@ zero extends @v@ to be a vector with length @n@.
-- This function requires that @n >= length v@.
zext :: IsAIG l g => g s -> BV (l s) -> Int -> BV (l s)
zext g v r = assert (r >= n) $ replicate (r - n) (falseLit g) ++ v
  where n = length v

-- | @lMuxInteger mergeFn maxValue lv valueFn@ returns a circuit
-- whose result is @valueFn v@ when @lv@ has value @v@.
muxInteger :: (Integral i, Monad m)
           => (l -> m a -> m a -> m a)
           -> i -- ^ Maximum value input vector is allowed to take.
           -> BV l -- ^ Input vector
           -> (i -> m a)
           -> m a
muxInteger mergeFn maxValue vx valueFn = impl (length vx) 0
  where impl _ y | y >= toInteger maxValue = valueFn maxValue
        impl 0 y = valueFn (fromInteger y)
        impl i y = mergeFn (vx ! j) (impl j (y `setBit` j)) (impl j y)
          where j = i - 1

shl :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
shl g x y = muxInteger (iteM g) (length x) y (return . shlC g x)

-- | Shift left by a constant.
shlC :: IsAIG l g => g s -> BV (l s) -> Int -> BV (l s)
shlC g x s0 = slice x j (n-j) ++ replicate j (falseLit g)
  where n = length x
        j = min n s0

-- | Shift left by a constant.
shrC :: l s -> BV (l s) -> Int -> BV (l s)
shrC c x s0 = replicate j c ++ slice x 0 (n-j)
  where n = length x
        j = min n s0

sshr :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
sshr g x y = muxInteger (iteM g) (length x) y (return . shrC (msb x) x)

ushr :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
ushr g x y = muxInteger (iteM g) (length x) y (return . shrC (falseLit g) x)

-- | Rotate left by a constant.
rolC :: BV (l s) -> Int -> BV (l s)
rolC (BV x) i
  | V.null x  = BV x
  | otherwise = BV (V.drop j x V.++ V.take j x)
  where j = i `mod` V.length x

-- | Rotate right by a constant.
rorC :: BV (l s) -> Int -> BV (l s)
rorC x i = rolC x (- i)

-- | Rotate left.
rol :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
rol g x y = do
  r <- urem g y (bvFromInteger g (length y) (toInteger (length x)))
  muxInteger (iteM g) (length x - 1) r (return . rolC x)

-- | Rotate right.
ror :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
ror g x y = do
  r <- urem g y (bvFromInteger g (length y) (toInteger (length x)))
  muxInteger (iteM g) (length x - 1) r (return . rorC x)
