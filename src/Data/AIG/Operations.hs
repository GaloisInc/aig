{- |
Module      : Data.AIG.Operations
Copyright   : (c) Galois, Inc. 2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : portable

A collection of higher-level operations (mostly 2's complement arithmetic operations)
that can be built from the primitive And-Inverter Graph interface.
-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
module Data.AIG.Operations
  ( -- * Bitvectors
    BV
  , empty
  , length
  , at
  , (!)
  , (++)
  , concat
  , take
  , drop
  , slice
  , sliceRev
  , zipWith
  , zipWithM
  , msb
  , lsb
  , bvSame
  , bvShow

    -- ** Building bitvectors
  , generateM_msb0
  , generate_msb0
  , generateM_lsb0
  , generate_lsb0
  , replicate
  , replicateM
  , bvFromInteger
  , bvFromList
  , muxInteger
  , singleton

    -- ** Lazy operators
  , lAnd
  , lAnd'
  , lOr
  , lOr'
  , lXor
  , lXor'
  , lEq
  , lEq'
  , lNot
  , lNot'

    -- ** Conditionals
  , ite
  , iteM

    -- ** Deconstructing bitvectors
  , asUnsigned
  , asSigned
  , bvToList

    -- * Numeric operations on bitvectors
    -- ** Addition and subtraction
  , neg
  , add
  , addC
  , sub
  , subC
  , addConst
  , subConst

    -- ** Multiplication and division
  , mul
  , mulFull
  , wallaceMultiply
  , smulFull
  , squot
  , srem
  , uquot
  , urem

    -- ** Shifts and rolls
  , shl
  , sshr
  , ushr
  , rol
  , ror

    -- ** Numeric comparisons
  , bvEq
  , isZero
  , nonZero
  , sle
  , slt
  , ule
  , ult
  , sabs

    -- ** Extensions
  , sext
  , zext
  , trunc
  , zeroIntCoerce
  , signIntCoerce

    -- * Priority encoder, lg2, and related functions
  , priorityEncode
  , logBase2_down
  , logBase2_up
  , countLeadingZeros
  , countTrailingZeros

    -- * Polynomial multiplication, division and modulus in the finite
    --   Galois Field GF(2^n)
  , pmul
  , pdiv
  , pmod
  ) where

import Control.Applicative hiding (empty)
import Control.Exception (assert)
import qualified Control.Monad
import Control.Monad.State hiding (zipWithM, replicateM, mapM, sequence)
import Data.Bits ((.|.), setBit, shiftL, testBit)
#if MIN_VERSION_base(4,8,0)
import qualified Data.Bits as Bits
#endif

import qualified Data.Vector as V
import qualified Data.Vector.Generic.Mutable as MV

import Prelude()
import Prelude.Compat
  hiding (and, concat, length, not, or, replicate, splitAt, tail, (++), take, drop, zipWith, mapM)
import qualified Prelude.Compat as Prelude

import Data.AIG.Interface
import Data.AIG.AddTree

-- | A BitVector consists of a sequence of symbolic bits and can be used
--   for symbolic machine-word arithmetic.  Bits are stored in
--   most-significant-bit first order.
newtype BV l = BV { unBV :: V.Vector l }
  deriving ( Eq
           , Ord
           , Show
           , Functor
           , Foldable
           , Traversable
           )

-- | Empty bitvector
empty :: BV l
empty = BV V.empty

-- | Number of bits in a bit vector
length :: BV l -> Int
length (BV v) = V.length v

tail :: BV l -> BV l
tail (BV v) = BV (V.tail v)

-- | Generate a bitvector of length @n@, using function @f@ to specify the bit literals.
--   The indexes to @f@ are given in LSB-first order, i.e., @f 0@ is the least significant bit.
{-# INLINE generate_lsb0 #-}
generate_lsb0
   :: Int            -- ^ @n@, length of the generated bitvector
   -> (Int -> l)     -- ^ @f@, function to calculate bit literals
   -> BV l
generate_lsb0 c f = BV (V.reverse (V.generate c f))

-- | Generate a bitvector of length @n@, using monadic function @f@ to generate the bit literals.
--   The indexes to @f@ are given in LSB-first order, i.e., @f 0@ is the least significant bit.
{-# INLINE generateM_lsb0 #-}
generateM_lsb0
   :: MonadIO m
   => Int            -- ^ @n@, length of the generated bitvector
   -> (Int -> m l)   -- ^ @f@, computation to generate a bit literal
   -> m (BV l)
generateM_lsb0 c f = do
   mv <- liftIO (MV.new c)
   let buildVec i | i >= c = liftIO (V.unsafeFreeze mv) >>= return . BV
                  | otherwise = (f i >>= liftIO . MV.unsafeWrite mv (c-i-1)) >> (buildVec $! (i+1))
   buildVec 0
--generateM_lsb0 c f = return . BV . V.reverse =<< V.generateM c f

{-# INLINE generateM_scan_lsb0 #-}
generateM_scan_lsb0
   :: MonadIO m
   => Int            -- ^ @n@, length of the generated bitvector
   -> (Int -> a -> m (l,a))   -- ^ @f@, computation to generate a bit literal
   -> a
   -> m (BV l, a)
generateM_scan_lsb0 c f a0 = do
   mv <- liftIO (MV.new c)
   let buildVec i a | i >= c = liftIO (V.unsafeFreeze mv) >>= \v -> return (BV v, a)
                    | otherwise = do (x,a') <- f i a
                                     liftIO (MV.unsafeWrite mv (c-i-1) x)
                                     (buildVec $! (i+1)) a'
   buildVec 0 a0


-- | Generate a bitvector of length @n@, using function @f@ to specify the bit literals.
--   The indexes to @f@ are given in MSB-first order, i.e., @f 0@ is the most significant bit.
{-# INLINE generate_msb0 #-}
generate_msb0
   :: Int            -- ^ @n@, length of the generated bitvector
   -> (Int -> l)     -- ^ @f@, function to calculate bit literals
   -> BV l
generate_msb0 c f = BV (V.generate c f)

-- | Generate a bitvector of length @n@, using monadic function @f@ to generate the bit literals.
--   The indexes to @f@ are given in MSB-first order, i.e., @f 0@ is the most significant bit.
{-# INLINE generateM_msb0 #-}
generateM_msb0
   :: Monad m
   => Int            -- ^ @n@, length of the generated bitvector
   -> (Int -> m l)   -- ^ @f@, computation to generate a bit literal
   -> m (BV l)
generateM_msb0 c f = return . BV =<< V.generateM c f

-- | Generate a bit vector of length @n@ where every bit value is literal @l@.
replicate
   :: Int   -- ^ @n@, length of the bitvector
   -> l     -- ^ @l@, the value to replicate
   -> BV l
replicate c e = BV (V.replicate c e)

-- | Generate a bit vector of length @n@ where every bit value is generated in turn by @m@.
replicateM
   :: Monad m
   => Int     -- ^ @n@, length of the bitvector
   -> m l     -- ^ @m@, the computation to produce a literal
   -> m (BV l)
replicateM c e = return . BV =<< V.replicateM c e

-- | Generate a one-element bitvector containing the given literal
singleton :: l -> BV l
singleton = BV . V.singleton

-- | Project the individual bits of a BitVector.
--   @x `at` 0@ is the most significant bit.
--   It is an error to request an out-of-bounds bit.
at :: BV l -> Int -> l
at (BV v) i = v V.! i

-- | Append two bitvectors, with the most significant bitvector given first.
(++) :: BV l -> BV l -> BV l
BV x ++ BV y = BV (x V.++ y)

-- | Concatenate a list of bitvectors, with the most significant bitvector at the
--   head of the list.
concat :: [BV l] -> BV l
concat v = BV (V.concat (unBV <$> v))

-- | Project out the `n` most significant bits from a bitvector.
take :: Int -> BV l -> BV l
take i (BV v) = BV (V.take i v)

-- | Drop the @n@ most significant bits from a bitvector.
drop :: Int -> BV l -> BV l
drop i (BV v) = BV (V.drop i v)

-- | Extract @n@ bits starting at index @i@.
--   The vector must contain at least @i+n@ elements
slice :: BV l
      -> Int   -- ^ @i@, 0-based start index
      -> Int   -- ^ @n@, bits to take
      -> BV l  -- ^ a vector consisting of the bits from @i@ to @i+n-1@
slice (BV v) i n = BV (V.slice i n v)


-- | Extract @n@ bits starting at index @i@, counting from
--   the end of the vector instead of the beginning.
--   The vector must contain at least @i+n@ elements.
sliceRev
      :: BV l
      -> Int   -- ^ @i@, 0-based start index from the end of the vector
      -> Int   -- ^ @n@, bits to take
      -> BV l
sliceRev (BV v) i n = BV (V.slice i' n v)
  where i' = V.length v - i - n

-- | Combine two bitvectors with a bitwise function
zipWith :: (l -> l -> l) -> BV l -> BV l -> BV l
zipWith f (BV x) (BV y) = assert (V.length x == V.length y) $ BV $ V.zipWith f x y

-- | Combine two bitvectors with a bitwise monadic combiner action.
zipWithM :: Monad m => (l -> l -> m l) -> BV l -> BV l -> m (BV l)
zipWithM f (BV x) (BV y) = assert (V.length x == V.length y) $ V.zipWithM f x y >>= return . BV

-- | Convert a bitvector to a list, most significant bit first.
bvToList :: BV l -> [l]
bvToList (BV v) = V.toList v

-- | Convert a list to a bitvector, assuming big-endian bit order.
bvFromList :: [l] -> BV l
bvFromList xs = BV (V.fromList xs)

-- | Select bits from a bitvector, starting from the least significant bit.
--   @x ! 0@ is the least significant bit.
--   It is an error to request an out-of-bounds bit.
(!) :: BV l -> Int -> l
(!) v i = v `at` (length v - 1 - i)

-- | Display a bitvector as a string of bits with most significant bits first.
--   Concrete literals are displayed as '0' or '1', whereas symbolic literals are displayed as 'x'.
bvShow :: IsAIG l g => g s -> BV (l s) -> String
bvShow g v = map f $ bvToList v
 where f x | x === trueLit g  = '1'
           | x === falseLit g = '0'
           | otherwise = 'x'

-- | Generate a bitvector from an integer value, using 2's complement representation.
bvFromInteger
   :: IsAIG l g
   => g s
   -> Int       -- ^ number of bits in the resulting bitvector
   -> Integer   -- ^ integer value
   -> BV (l s)
bvFromInteger g n v = generate_msb0 n $ \i -> constant g (v `testBit` (n-i-1))
   --generate_lsb0 n $ \i -> constant g (v `testBit` i)

-- | Interpret a bitvector as an unsigned integer.  Return @Nothing@ if
--   the bitvector is not concrete.
asUnsigned :: IsAIG l g => g s -> BV (l s) -> Maybe Integer
asUnsigned g v = go 0 0
  where n = length v
        go x i | i >= n = return x
        go x i = do
          b <- asConstant g (v `at` i)
          let y = if b then 1 else 0
          let z = (x `shiftL` 1) .|. y
          seq z $ go z (i+1)

-- | Interpret a bitvector as a signed integer.  Return @Nothing@ if
--   the bitvector is not concrete.
asSigned :: IsAIG l g => g s -> BV (l s) -> Maybe Integer
asSigned g v = assert (n > 0) $ (signfix =<< asUnsigned g (drop 1 v))
  where n = length v
        signfix x
            | msb v === trueLit g  = Just (x - 2^(n-1))
            | msb v === falseLit g = Just x
            | otherwise = Nothing

-- | Retrieve the most significant bit of a bitvector.
msb :: BV l -> l
msb v = v `at` 0

-- | Retrieve the least significant bit of a bitvector.
lsb :: BV l -> l
lsb v = v ! 0

-- | If-then-else combinator for bitvectors.
ite
   :: IsAIG l g
   => g s
   -> l s          -- ^ test bit
   -> BV (l s)     -- ^ then bitvector
   -> BV (l s)     -- ^ else bitvector
   -> IO (BV (l s))
ite g c x y = zipWithM (mux g c) x y

-- | If-then-else combinator for bitvector computations with optimistic
--   shortcutting.  If the test bit is concrete, we can avoid generating
--   either the if or the else circuit.
iteM
   :: IsAIG l g
   => g s
   -> l s                -- ^ test bit
   -> IO (BV (l s))      -- ^ then circuit computation
   -> IO (BV (l s))      -- ^ else circuit computation
   -> IO (BV (l s))
iteM g c x y
  | c === trueLit g = x
  | c === falseLit g = y
  | otherwise = join $ zipWithM (mux g c) <$> x <*> y

{-# INLINE lNot #-}
-- | Lazy negation of a circuit.
lNot :: IsAIG l g => g s -> IO (l s) -> IO (l s)
lNot g = fmap (lNot' g)

{-# INLINE lNot' #-}
lNot' :: IsAIG l g => g s -> l s -> l s
lNot' g x | x === trueLit g = falseLit g
          | x === falseLit g = trueLit g
          | otherwise = not x

{-# INLINE lOr #-}
-- | Build a short-cut OR circuit.  If the left argument
--   evaluates to the constant true, the right argument
--   will not be evaluated.
lOr :: IsAIG l g => g s -> IO (l s) -> IO (l s) -> IO (l s)
lOr g x y = lNot g (lAnd g (lNot g x) (lNot g y))

{-# INLINE lOr' #-}
lOr' :: IsAIG l g => g s -> l s -> l s -> IO (l s)
lOr' g x y = lNot g (lAnd' g (lNot' g x) (lNot' g y))

{-# INLINE lEq #-}
-- | Construct a lazy equality test.  If both arguments are constants,
--   the output will also be a constant.
lEq :: IsAIG l g => g s -> IO (l s) -> IO (l s) -> IO (l s)
lEq g x y = lNot g (lXor g x y)

{-# INLINE lEq' #-}
lEq' :: IsAIG l g => g s -> l s -> l s -> IO (l s)
lEq' g x y = lNot g (lXor' g x y)

-- | Build a short-cut AND circuit.  If the left argument
--   evaluates to the constant false, the right argument
--   will not be evaluated.
lAnd :: IsAIG l g => g s -> IO (l s) -> IO (l s) -> IO (l s)
lAnd g x y = do
  x' <- x
  if      x' === trueLit g  then y
  else if x' === falseLit g then return (falseLit g)
  else do
      y' <- y
      if      y' === trueLit g  then return x'
      else if y' === falseLit g then return (falseLit g)
      else and g x' y'

lAnd'' :: IsAIG l g => g s -> l s -> IO (l s) -> IO (l s)
lAnd'' g x y =
  if      x === trueLit g  then y
  else if x === falseLit g then return (falseLit g)
  else do
      y' <- y
      if      y' === trueLit g  then return x
      else if y' === falseLit g then return (falseLit g)
      else and g x y'

lAnd' :: IsAIG l g => g s -> l s -> l s -> IO (l s)
lAnd' g x y =
  if      x === trueLit g  then return y
  else if x === falseLit g then return (falseLit g)
  else if y === trueLit g  then return x
  else if y === falseLit g then return (falseLit g)
  else and g x y

lXor' :: IsAIG l g => g s -> l s -> l s -> IO (l s)
lXor' g x y =
  if      x === trueLit g  then return (not y)
  else if x === falseLit g then return y
  else if y === trueLit g  then return (not x)
  else if y === falseLit g then return x
  else xor g x y

-- | Construct a lazy xor.  If both arguments are constants,
--   the output will also be a constant.
lXor :: IsAIG l g => g s -> IO (l s) -> IO (l s) -> IO (l s)
lXor g x y = do
  x' <- x
  y' <- y
  if      x' === trueLit g  then return (not y')
  else if x' === falseLit g then return y'
  else if y' === trueLit g  then return (not x')
  else if y' === falseLit g then return x'
  else xor g x' y'


-- | A half adder which takes two inputs and returns output and carry.
{-# INLINE halfAdder #-}
halfAdder :: IsAIG l g => g s -> l s -> l s -> IO (l s, l s)
halfAdder g b c = do
  c_out <- lAnd' g b c
  s <- lAnd'' g (not c_out) (lOr' g b c)
  return (s, c_out)


-- | A full adder which takes three inputs and returns output and carry.
{-# INLINE fullAdder #-}
fullAdder :: IsAIG l g => g s -> l s -> l s -> l s -> IO (l s, l s)
fullAdder g a b c_in = do
   ab      <- lAnd' g a b
   a'b'    <- lAnd' g (not a) (not b)
   xab     <- lAnd' g (not ab) (not a'b')
   xab_c   <- lAnd' g xab c_in
   xab'_c' <- lAnd' g (not xab) (not c_in)
   s       <- lAnd' g (not xab_c) (not xab'_c')
   c_out   <- lOr' g ab xab_c
   return (s, c_out)

-- | Implements a ripple carry adder.  Both addends are assumed to have
--   the same length.
ripple_add :: IsAIG l g
           => g s
           -> BV (l s)
           -> BV (l s)
           -> IO (BV (l s), l s) -- ^ sum and carry-out bit
ripple_add g x _ | length x == 0 = return (x, falseLit g)
ripple_add g x y = do
   let unfold i = fullAdder g (x!i) (y!i)
   generateM_scan_lsb0 (length x) unfold (falseLit g)

-- ripple_add g x y = do
--     r <- newIORef (falseLit g)
--     let unfold i = do (s,c) <- fullAdder g (x!i) (y!i) =<< readIORef r
--                       writeIORef r c
--                       return s
--     sum <- generateM_lsb0 (length x) unfold
--     c_out <- readIORef r
--     return (sum,c_out)


-- | A subtraction circuit which takes three inputs and returns output and carry.
{-# INLINE fullSub #-}
fullSub :: IsAIG l g => g s -> l s -> l s -> l s -> IO (l s, l s)
fullSub g x y b_in = do
  s <- lEq' g x =<< (lEq' g y b_in)
  b_out <- lOr g (lAnd' g y b_in) (lAnd'' g (not x) (lOr' g y b_in))
  return (s, b_out)


-- | Subtract two bit vectors, returning result and borrow bit.
ripple_sub :: IsAIG l g
         => g s
         -> BV (l s)
         -> BV (l s)
         -> IO (BV (l s), l s)
ripple_sub g x _ | length x == 0 = return (x,falseLit g)
ripple_sub g x y = do
  let unfold i = fullSub g (x ! i) (y ! i)
  generateM_scan_lsb0 (length x) unfold (falseLit g)

-- ripple_sub g x y = do
--     r <- newIORef (falseLit g)
--     let unfold i = do (s,b) <- fullSub g (x!i) (y!i) =<< readIORef r
--                       writeIORef r b
--                       return s
--     diff <- generateM_lsb0 (length x) unfold
--     b_out <- readIORef r
--     return (diff,b_out)


-- | Compute just the borrow bit of a subtraction.
{-# INLINE ripple_sub_borrow #-}
ripple_sub_borrow :: IsAIG l g
         => g s
         -> BV (l s)
         -> BV (l s)
         -> IO (l s)
ripple_sub_borrow g x y = go 0 (falseLit g)
   where n = length x
         go i b | i >= n = return b
                | otherwise = (go $! (i+1)) =<<
                                  (lOr g (lAnd' g b (y!i))
                                         (lAnd'' g (lNot' g (x!i)) (lOr' g (y!i) b))
                                  )

-- | Compute the 2's complement negation of a bitvector
neg :: IsAIG l g => g s -> BV (l s) -> IO (BV (l s))
neg g x = evalStateT (generateM_lsb0 (length x) unfold) (trueLit g)
  where unfold i = StateT $ halfAdder g (lNot' g (x ! i))

-- | Add two bitvectors with the same size.  Discard carry bit.
add :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
add g x y = fst <$> addC g x y

-- | Add two bitvectors with the same size with carry.
addC :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s), l s)
addC g x y = assert (length x == length y) $ ripple_add g x y

-- | Subtract one bitvector from another with the same size.  Discard carry bit.
sub :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
sub g x y = fst <$> subC g x y

-- | Subtract one bitvector from another with the same size with carry.
subC :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s), l s)
subC g x y = assert (length x == length y) $ ripple_sub g x y

-- | Add a constant value to a bitvector
addConst :: IsAIG l g => g s -> BV (l s) -> Integer -> IO (BV (l s))
addConst g x y = do
  let n = length x
  m <- MV.new n
  let adderStepM c i
        | i == n = return ()
        | otherwise = do
          let a = x ! i
          let b = y `testBit` i
          ac <- lAnd' g a c
          negAnegC <- lAnd' g (lNot' g a) (lNot' g c)
          aEqC <- lOr' g ac negAnegC
          if b
            then do
              MV.write m (n-i-1) aEqC
              adderStepM (lNot' g negAnegC) (i+1)
            else do
              MV.write m (n-i-1) (lNot' g aEqC)
              adderStepM ac (i+1)
  adderStepM (falseLit g) 0
  fmap BV $ V.freeze m

--addConst g x c = add g x (bvFromInteger g (length x) c)

-- | Add a constant value to a bitvector
subConst :: IsAIG l g => g s -> BV (l s) -> Integer -> IO (BV (l s))
subConst g x c = addConst g x (-c)


-- | Multiply two bitvectors with the same size, with result
--   of the same size as the arguments.
--   Overflow is silently discarded.
mul :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
mul g x y = assert (length x == length y) $ do
  -- Create mutable array to store result.
  let n = length y
  -- Function to update bits.
  let updateBits i z | i == n = return z
      updateBits i z = do
        z' <- iteM g (y ! i) (add g z (shlC g x i)) (return z)
        updateBits (i+1) z'
  updateBits 0 $ replicate (length x) (falseLit g)

-- | Unsigned multiply two bitvectors with size @m@ and size @n@,
--   resulting in a vector of size @m+n@.
--mulFull :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
--mulFull g x y =
--    let len = length x + length y
--        x' = zext g x len
--        y' = zext g y len
--     in mul g x' y'

mulFull :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
mulFull = wallaceMultiply


wallaceMultiply :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
wallaceMultiply g x y =
 do let lenx = length x
    let leny = length y
    let len = length x + length y
    t <- newAddTree len
    forM_ [0..lenx-1] $ \i ->
      forM_ [0..leny-1] $ \j ->
        do z <- lAnd' g (x!i) (y!j)
           pushBit (i+j) (0,z) t
    let fa d b0 b1 b2 =
         do (s,c) <- fullAdder g b0 b1 b2
            return (d+4, c, s)
    let ha d b0 b1 =
         do (s,c) <- halfAdder g b0 b1
            return (d+3, c, s)

    BV <$> wallaceTreeReduction (falseLit g) fa ha t


-- | Signed multiply two bitvectors with size @m@ and size @n@,
--   resulting in a vector of size @m+n@.
smulFull :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
smulFull g x y = do
    let len = length x + length y
        x' = sext g x len
        y' = sext g y len
     in mul g x' y'

-- | Compute the signed quotient of two signed bitvectors with the same size.
squot :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
squot g x y = fst <$> squotRem g x y

-- | Compute the signed division remainder of two signed bitvectors with the same size.
srem :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
srem g x y = snd <$> squotRem g x y

-- | Cons value to head of a list and shift other elements to left.
shiftL1 :: BV l -> l -> BV l
shiftL1 (BV v) e = assert (V.length v > 0) $ BV (V.tail v `V.snoc` e)

-- -- | Cons value to start of list and shift other elements right.
-- shiftR1 :: l -> BV l -> BV l
-- shiftR1 e (BV v) = assert (V.length v > 0) $ BV (e `V.cons` V.init v)

-- stepN :: Monad m => Int -> (a -> m a) -> a -> m a
-- stepN n f x
--   | n > 0 = stepN (n-1) f =<< f x
--  | otherwise = return x

splitAt :: Int -> BV l -> (BV l, BV l)
splitAt n (BV v) = (BV x, BV y)
  where (x,y) = V.splitAt n v

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
          (s,b) <- ripple_sub g r divisor
          divStep (i+1) (lNot' g b) =<< ite g b rs (s ++ q)
    divStep 0 (falseLit g) initial

-- Perform quotRem on the absolute value of the operands.  Then, negate the
-- quotient if the signs of the operands differ and make the sign of a nonzero
-- remainder to match that of the dividend.
squotRem :: IsAIG l g
         => g s
         -> BV (l s)
         -> BV (l s)
         -> IO (BV (l s), BV (l s))
squotRem g dividend divisor =
    assert (length dividend > 0 && length dividend == length divisor) $ do
    let sign1 = msb dividend
    let sign2 = msb divisor
    signXor <- xor g sign1 sign2
    dividend' <- negWhen g dividend sign1
    divisor'  <- negWhen g divisor sign2
    (q,r) <- uquotRem g dividend' divisor'
    q' <- negWhen g q signXor
    r' <- negWhen g r sign1
    return (q',r')

-- This code seems to have a bug...
-- squotRem g dividend' divisor' = do
--   let n = length dividend'
--   assert (n > 0 && n == length divisor') $ do
--     let dsign = msb dividend'
--     dividend <- sabs g dividend'
--     divisor  <- sabs g divisor'
--     -- Given an n-bit dividend and divisor, 'initial' is the starting value of
--     -- the 2n-bit "remainder register" that carries both the quotient and remainder;
--     let initial = zext g dividend (2*n)
--     let divStep rrOrig = do
--           let (r,q) = splitAt n rrOrig
--           s <- sub g r divisor
--           ite g (msb s)
--                 (rrOrig `shiftL1` falseLit g)     -- rem < 0, orig rr's quot lsl'd w/ 0
--                 ((s ++ q) `shiftL1` trueLit g) -- rem >= 0, new rr's quot lsl'd w/ 1
--     (qr,rr) <- splitAt n <$> stepN n divStep (initial `shiftL1` falseLit g)
--     q' <- negWhen g qr =<< xor g dsign (msb divisor')
--     r' <- negWhen g (falseLit g `shiftR1` rr) dsign
--     return (q', r')

-- | Compute the unsigned quotient of two unsigned bitvectors with the same size.
uquot :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
uquot g x y = fst <$> uquotRem g x y

-- | Compute the unsigned division remainder of two unsigned bitvectors with the same size.
urem :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
urem g x y = snd <$> uquotRem g x y

-- | Test syntactic equalify of two bitvectors using the `===` operation
bvSame :: IsLit l => BV (l s) -> BV (l s) -> Bool
bvSame (BV x) (BV y) = assert (V.length x == V.length y) $ V.foldr (&&) True $ V.zipWith (===) x y

-- | Test equality of two bitvectors with the same size.
bvEq :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
bvEq g x y = assert (n == length y) $ go 0 (trueLit g)
  where n = length x
        go i r | i == n = return r
        go i r = go (i+1) =<< and g r =<< eq g (x `at` i) (y `at` i)

-- | Test if a bitvector is equal to zero
isZero :: IsAIG l g => g s -> BV (l s) -> IO (l s)
isZero g (BV v) = V.foldM (\x y -> and g x (lNot' g y)) (trueLit g) v

-- | Test if a bitvector is distinct from zero
nonZero :: IsAIG l g => g s -> BV (l s) -> IO (l s)
nonZero g bv = lNot g $ isZero g bv

-- | Unsigned less-than on bitvector with the same size.
ult :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
ult g x y = assert (length x == length y) $ ripple_sub_borrow g x y

-- | Unsigned less-than-or-equal on bitvector with the same size.
ule :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
ule g x y = lNot g $ ult g y x

-- | Signed less-than on bitvector with the same size.
slt :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
slt g x y = assert (length x == length y) $ do
  let xs = x `at` 0
  let ys = y `at` 0
  -- x is negative and y is positive.
  c0 <- and g xs (lNot' g ys)
  -- x is positive and y is negative.
  c1 <- and g (lNot' g xs) ys
  c2 <- and g (lNot' g c1) =<< ult g (tail x) (tail y)
  or g c0 c2

-- | Signed less-than-or-equal on bitvector with the same size.
sle :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (l s)
sle g x y = lNot g $ slt g y x

-- | @sext v n@ sign extends @v@ to be a vector with length @n@.
-- This function requires that @n >= length v@ and @length v > 0@.
sext :: IsAIG l g => g s -> BV (l s) -> Int -> BV (l s)
sext _g v r = assert (r >= n && n > 0) $ replicate (r - n) (msb v) ++ v
  where n = length v

-- | @zext g v n@ zero extends @v@ to be a vector with length @n@.
-- This function requires that @n >= length v@.
zext :: IsAIG l g => g s -> BV (l s) -> Int -> BV (l s)
zext g v r = assert (r >= n) $ replicate (r - n) (falseLit g) ++ v
  where n = length v

-- | Truncate the given bit vector to the specified length
trunc :: Int -> BV (l s) -> BV (l s)
trunc w vx = assert (length vx >= w) $ drop (length vx - w) vx

-- | Truncate or zero-extend a bitvector to have the specified number of bits
zeroIntCoerce :: IsAIG l g => g s -> Int -> BV (l s) -> BV (l s)
zeroIntCoerce g r t
    | r > l = zext g t r
    | r < l = trunc r t
    | otherwise = t
  where l = length t

-- | Truncate or sign-extend a bitvector to have the specified number of bits
signIntCoerce :: IsAIG l g => g s -> Int -> BV (l s) -> BV (l s)
signIntCoerce g r t
    | r > l = sext g t r
    | r < l = trunc r t
    | otherwise = t
  where l = length t


-- | @muxInteger mergeFn maxValue lv valueFn@ returns a circuit
-- whose result is @valueFn v@ when @lv@ has value @v@.
muxInteger :: (Integral i, Monad m)
           => (l -> m a -> m a -> m a) -- Combining operation for muxing on individual bit values
           -> i -- ^ Maximum value input vector is allowed to take.
           -> BV l -- ^ Input vector
           -> (i -> m a)
           -> m a
muxInteger mergeFn maxValue vx valueFn = impl (length vx) 0
  where impl _ y | y >= toInteger maxValue = valueFn maxValue
        impl 0 y = valueFn (fromInteger y)
        impl i y = mergeFn (vx ! j) (impl j (y `setBit` j)) (impl j y)
          where j = i - 1

-- | Shift left.  The least significant bit becomes 0.
shl :: IsAIG l g
    => g s
    -> BV (l s)       -- ^ the value to shift
    -> BV (l s)       -- ^ how many places to shift
    -> IO (BV (l s))
shl g x y = muxInteger (iteM g) (length x) y (return . shlC g x)

-- | Shift left by a constant.
shlC :: IsAIG l g => g s -> BV (l s) -> Int -> BV (l s)
shlC g x s0 = slice x j (n-j) ++ replicate j (falseLit g)
  where n = length x
        j = min n s0

-- | Shift right by a constant.
shrC :: l s -> BV (l s) -> Int -> BV (l s)
shrC c x s0 = replicate j c ++ slice x 0 (n-j)
  where n = length x
        j = min n s0

-- | Signed right shift.  The most significant bit is copied.
sshr :: IsAIG l g
     => g s
     -> BV (l s)     -- ^ the value to shift
     -> BV (l s)     -- ^ how many places to shift
     -> IO (BV (l s))
sshr g x y = muxInteger (iteM g) (length x) y (return . shrC (msb x) x)

-- | Unsigned right shift.  The most significant bit becomes 0.
ushr :: IsAIG l g
     => g s
     -> BV (l s)     -- ^ the value to shift
     -> BV (l s)     -- ^ how many places to shift
     -> IO (BV (l s))
ushr g x y = muxInteger (iteM g) (length x) y (return . shrC (falseLit g) x)

-- | Rotate left by a constant.
rolC :: BV l -> Int -> BV l
rolC (BV x) i
  | V.null x  = BV x
  | otherwise = BV (V.drop j x V.++ V.take j x)
  where j = i `mod` V.length x

-- | Rotate right by a constant.
rorC :: BV l -> Int -> BV l
rorC x i = rolC x (- i)

-- | Rotate left.
rol :: IsAIG l g
    => g s
    -> BV (l s)    -- ^ the value to rotate
    -> BV (l s)    -- ^ how many places to rotate
    -> IO (BV (l s))
rol g x0 (BV ys) = fst <$> V.foldM f (x0, 1) (V.reverse ys)
  where
    f (x, p) y = do
      x' <- ite g y (rolC x p) x
      let p' = (2*p) `mod` length x0
      return (x', p')

-- | Rotate right.
ror :: IsAIG l g
    => g s
    -> BV (l s)    -- ^ the value to rotate
    -> BV (l s)    -- ^ how many places to rotate
    -> IO (BV (l s))
ror g x0 (BV ys) = fst <$> V.foldM f (x0, 1) (V.reverse ys)
  where
    f (x, p) y = do
      x' <- ite g y (rorC x p) x
      let p' = (2*p) `mod` length x0
      return (x', p')


-- | Compute the rounded-down base2 logarithm of the input bitvector.
--   For x > 0, this uniquely satisfies 2^(logBase2_down(x)) <= x < 2^(logBase2_down(x)+1).
--   For x = 0, we set logBase2(x) = -1.
--   The output bitvector has the same width as the input bitvector.
logBase2_down
        :: IsAIG l g
        => g s
        -> BV (l s)  -- ^ input bitvector
        -> IO (BV (l s))
logBase2_down g bv = do
   (v, c) <- priorityEncode g (length bv) bv
   iteM g v (return c)
            (return (bvFromInteger g (length bv) (-1)))

-- | Compute the rounded-up base2 logarithm of the input bitvector.
--   For x > 1, this uniquely satisfies 2^(logBase2_up(x) - 1) < x <= 2^(logBase2_up(x)).
--   For x = 1, logBase2_up 1 = 0.
--   For x = 0, we get logBase2_up 0 = <input bitvector length>; this just
--   happens to work out from the defining fomula
--   `logBase2_up x = logBase2_down (x-1) + 1`
--   when interpreted in 2's complement.
--   The output bitvector has the same width as the input bitvector.
logBase2_up
        :: IsAIG l g
        => g s
        -> BV (l s)  -- ^ input bitvector
        -> IO (BV (l s))
logBase2_up g bv = do
   bv' <- subConst g bv 1
   i <- logBase2_down g bv'
   addConst g i 1

-- | Count the number of leading zeros in the input vector; that is,
--   the number of more-significant digits set to 0 above the most
--   significant digit that is set.  If the input vector is 0, the output of
--   this function is the length of the bitvector (i.e., all digits are
--   counted as leading zeros).
--   The output bitvector has the same width as the input bitvector.
countLeadingZeros
        :: IsAIG l g
        => g s
        -> BV (l s)  -- ^ input bitvector
        -> IO (BV (l s))
countLeadingZeros g bv = do
   lg <- logBase2_down g bv
   let w'= bvFromInteger g (length bv) (fromIntegral (length bv - 1))
   sub g w' lg

-- | Count the number of trailing zeros in the input vector; that is,
--   the number of less-significant digits set to 0 below the least
--   significant digit which is set.  If the input vector is 0, the
--   output of this function is the length of the bitvector (i.e.,
--   all digits are counted as trailing zeros).
--   The output bitvector has the same width as the input bitvector.
countTrailingZeros
        :: IsAIG l g
        => g s
        -> BV (l s)  -- ^ input bitvector
        -> IO (BV (l s))
countTrailingZeros g (BV v) = do
   countLeadingZeros g (BV (V.reverse v))

-- | Given positive x, find the unique i such that: 2^i <= x < 2^(i+1)
--   This is the floor of the lg2 function.  We extend the function so
--   intLog2_down 0 = -1.
intLog2_down :: Int -> Int
#if MIN_VERSION_base(4,8,0)
intLog2_down x = (Bits.finiteBitSize x - 1) - Bits.countLeadingZeros x
#else
intLog2_down x
   | x <= 0    = -1
intLog2_down 1 =  0
intLog2_down x =  1 + intLog2_down (x `div` 2)
#endif

-- | Given positive x, find the unique i such that: 2^(i-1) < x <= 2^i
--   This is the ceiling of the lg2 function.
--   Note: intLog2_up 1 = 0
intLog2_up :: Int -> Int
intLog2_up x = intLog2_down (x - 1) + 1

-- | Priority encoder.  Given a bitvector, calculate the
--   bit position of the most-significant 1 bit, with position
--   0 corresponding to the least-significant-bit.  Return
--   the "valid" bit, which is set iff at least one bit
--   in the input is set; and the calcuated bit position.
--   If no bits are set in the input (i.e. if the valid bit is false),
--   the calculated bit position is zero.
--   The indicated bitwidth must be large enough to hold the answer;
--   in particular, we must have (length bv <= 2^w).
priorityEncode :: IsAIG l g
               => g s
               -> Int       -- ^ width of the output bitvector
               -> BV (l s)  -- ^ input bitvector
               -> IO (l s, BV (l s)) -- ^ Valid bit and position bitvector
priorityEncode g w bv
  | w < 0 = fail $ unwords ["priorityEncode: asked for negative number of output bits", show w, show $ length bv]
  | length bv == 0 = return ( falseLit g, replicate w (falseLit g) )
  | length bv == 1 = return ( bv!0, replicate w (falseLit g) )
  | otherwise = do
       let w' = intLog2_up (length bv)

       unless ( w' <= w )
              (fail $ unwords ["priorityEncode: insufficent bits to encode priority output", show w, show $ length bv])

       (v, p) <- doPriorityEncode g w' bv

       unless (length p == w')
              (fail $ unwords ["priorityEncode: length check failed", show $ length p, show w'])

       -- zero extend as necessary to fit the requested bitwidth
       let p' = replicate (w - length p) (falseLit g)
       return (v, p'++p)

-- Invariants:
--     w > 0 and 2^(w-1) < length bv <= 2^w
--      OR
--     w = 0 and length bv = 1
--
--     length <output bv> = w
doPriorityEncode
    :: IsAIG l g
    => g s
    -> Int       -- ^ width of the output bitvector
    -> BV (l s)  -- ^ input bitvector
    -> IO (l s, BV (l s))
doPriorityEncode g w bv
   | w < 0 = fail "doPriorityEncode: negative w!"

   | length bv == 1 = do                      -- w = 0
        return ( bv!0, empty )

   | length bv == 2 = do                      -- w = 1
        v <- lOr' g (bv!0) (bv!1)
        return (v, singleton (bv!1))

   | length bv == 3 = do                      -- w = 2
        vlo <- lOr' g (bv!0) (bv!1)
        let vhi = bv!2
        v  <- lOr' g vlo vhi
        e0 <- lAnd' g (not vhi) (bv!1)
        return (v, BV $ V.fromList [vhi, e0])

   | length bv == 4 = do                      -- w = 2
        vlo <- lOr' g (bv!0) (bv!1)
        vhi <- lOr' g (bv!2) (bv!3)
        v   <- lOr' g vlo vhi
        e0  <- lazyMux g vhi (return (bv!3)) (return (bv!1))
        return (v, BV $ V.fromList [vhi, e0])

   | otherwise = do                           -- w >= 3; 2^(w-1) < length b <= 2^w
       unless (w >= 3)
              (fail "doPriorityEncode: w too small!")
       unless (2^(w-1) < length bv && length bv <= 2^w)
              (fail $ unwords ["doPriorityEncode: invariant check failed"
                              , show w, show $ length bv ])

       let bitsLo = 2^(w - 1)
       let wLo = w - 1

       let bitsHi = length bv - bitsLo
       let wHi = intLog2_up bitsHi

       unless (0 < bitsHi)
              (fail "doPriorityEnode: bitsHi nonpositive")
       unless (bitsHi <= bitsLo && wHi <= wLo)
              (fail $ unwords ["doPriorityEncode: bounds check failed",
                               show bitsHi, show bitsLo, show wHi, show wLo, show w, show $ length bv])

       let bvLo = drop bitsHi bv
       let bvHi = take bitsHi bv

       (vHi, pHi) <- doPriorityEncode g wHi bvHi
       (vLo, pLo) <- doPriorityEncode g wLo bvLo

       v <- lOr' g vHi vLo
       p <- iteM g vHi
                   (return (replicate (length pLo - length pHi) (falseLit g) ++ pHi))
                   (return pLo)
       return (v, singleton vHi ++ p)


-- | Polynomial multiplication. Note that the algorithm works the same
--   no matter which endianness convention is used.  Result length is
--   @max 0 (m+n-1)@, where @m@ and @n@ are the lengths of the inputs.
pmul :: IsAIG l g
     => g s
     -> BV (l s)
     -> BV (l s)
     -> IO (BV (l s))
pmul g x y = generateM_msb0 (max 0 (m + n - 1)) coeff
  where
    m = length x
    n = length y
    coeff k = foldM (xor g) (falseLit g) =<<
      sequence [ and g (at x i) (at y j) | i <- [0 .. k], let j = k - i, i < m, j < n ]

-- | Polynomial mod with symbolic modulus. Return value has length one
-- less than the length of the modulus.
-- This implementation is optimized for the (common) case where the modulus
-- is concrete.
pmod :: forall l g s. IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
pmod g x y = findmsb (bvToList y)
  where
    findmsb :: [l s] -> IO (BV (l s))
    findmsb [] = return (replicate (length y - 1) (falseLit g)) -- division by zero
    findmsb (c : cs)
      | c === trueLit g = usemask cs
      | c === falseLit g = findmsb cs
      | otherwise = do
          t <- usemask cs
          f <- findmsb cs
          zipWithM (mux g c) t f

    usemask :: [l s] -> IO (BV (l s))
    usemask m = do
      rs <- go 0 p0 z0
      return (zext g (bvFromList rs) (length y - 1))
      where
        msize = Prelude.length m
        p0 = Prelude.replicate (msize - 1) (falseLit g) Prelude.++ [trueLit g]
        z0 = Prelude.replicate msize (falseLit g)

        next :: [l s] -> IO [l s]
        next [] = return []
        next (b : bs) = do
          m' <- Prelude.mapM (and g b) m
          let bs' = bs Prelude.++ [falseLit g]
          Control.Monad.zipWithM (xor g) m' bs'

        go :: Int -> [l s] -> [l s] -> IO [l s]
        go i p acc
          | i >= length x = return acc
          | otherwise = do
              px <- Prelude.mapM (and g (x ! i)) p
              acc' <- Control.Monad.zipWithM (xor g) px acc
              p' <- next p
              go (i+1) p' acc'


-- | Polynomial division. Return value has length
--   equal to the first argument.
pdiv :: IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s))
pdiv g x y = do
  (q,_) <- pdivmod g x y
  return q

-- Polynomial div/mod: resulting lengths are as in Cryptol.

-- TODO: probably this function should be disentangled to only compute
-- division, given that we have a separate polynomial modulus algorithm.
pdivmod :: forall l g s. IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s), BV (l s))
pdivmod g x y = findmsb (bvToList y)
  where
    findmsb :: [l s] -> IO (BV (l s), BV (l s))
    findmsb (c : cs) = lmuxPair c (usemask cs) (findmsb cs)
    findmsb [] = return (x, replicate (length y - 1) (falseLit g)) -- division by zero

    usemask :: [l s] -> IO (BV (l s), BV (l s))
    usemask mask = do
      (qs, rs) <- pdivmod_helper g (bvToList x) mask
      let z = falseLit g
      let qs' = Prelude.map (const z) rs Prelude.++ qs
      let rs' = Prelude.replicate (length y - 1 - Prelude.length rs) z Prelude.++ rs
      let q = BV $ V.fromList qs'
      let r = BV $ V.fromList rs'
      return (q, r)

    lmuxPair :: l s -> IO (BV (l s), BV (l s)) -> IO (BV (l s), BV (l s)) -> IO (BV (l s), BV (l s))
    lmuxPair c a b
      | c === trueLit g  = a
      | c === falseLit g = b
      | otherwise = join (muxPair c <$> a <*> b)

    muxPair :: l s -> (BV (l s), BV (l s)) -> (BV (l s), BV (l s)) -> IO (BV (l s), BV (l s))
    muxPair c (x1, y1) (x2, y2) = (,) <$> zipWithM (mux g c) x1 x2 <*> zipWithM (mux g c) y1 y2

-- Divide ds by (1 : mask), giving quotient and remainder. All
-- arguments and results are big-endian. Remainder has the same length
-- as mask (but limited by length ds); total length of quotient ++
-- remainder = length ds.
pdivmod_helper :: forall l g s. IsAIG l g => g s -> [l s] -> [l s] -> IO ([l s], [l s])
pdivmod_helper g ds mask = go (Prelude.length ds - Prelude.length mask) ds
  where
    go :: Int -> [l s] -> IO ([l s], [l s])
    go n cs | n <= 0 = return ([], cs)
    go _ []          = fail "Data.AIG.Operations.pdiv: impossible"
    go n (c : cs)    = do cs' <- mux_add c cs mask
                          (qs, rs) <- go (n - 1) cs'
                          return (c : qs, rs)

    mux_add :: l s -> [l s] -> [l s] -> IO [l s]
    mux_add c (x : xs) (y : ys) = do z <- lazyMux g c (xor g x y) (return x)
                                     zs <- mux_add c xs ys
                                     return (z : zs)
    mux_add _ []       (_ : _ ) = fail "Data.AIG.Operations.pdiv: impossible"
    mux_add _ xs       []       = return xs
