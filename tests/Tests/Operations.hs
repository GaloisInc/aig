{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
module Tests.Operations (op_tests) where

import Test.Tasty
import Test.Tasty.QuickCheck
--import Test.QuickCheck

import           Data.AIG.Interface (BasicGraph, BasicLit, newBasicGraph)
import qualified Data.AIG.Interface as AIG
import qualified Data.AIG.Operations as AIG
import Data.Bits
import Data.Int
import Data.Word

type BV s = AIG.BV (BasicLit s)

--------------------------------------------------------------------------
-- Some test harness stuff to make writing down unit tests easier

class Precond x where
  precond :: x -> Bool
  precond _ = True

class Arbitrary x => AIGTestableValue g x y where
  injectArg  :: g -> x -> y
  extractArg :: g -> y -> Maybe x

class PushIO y where
  pushIO  :: (a -> y) -> IO a -> y

instance PushIO (IO b) where
  pushIO f x = x >>= f

instance PushIO b => PushIO (a -> b) where
  pushIO f x a = pushIO (\x' -> f x' a) x

class (Testable p, PushIO y) => AIGTestable g x y p | g x y -> p where
  runTest :: IO g -> x -> y -> Bool -> p

newtype Denom a = Denom a
 deriving (Eq, Ord, Show)

instance Precond Bool
instance Precond Word32
instance Precond Word64
instance Precond Int32
instance Precond Int64
instance Precond Integer

instance (Integral a, Eq a) => Precond (Denom a) where
  precond (Denom x) = x /= 0
instance Precond Int where
  precond x = 0 <= x && x < 64

instance Arbitrary a => Arbitrary (Denom a) where
  arbitrary = Denom <$> arbitrary

instance (AIGTestableValue g a x, AIGTestableValue g b y) =>
    AIGTestableValue g (a,b) (x,y) where
  injectArg g (a,b) = (injectArg g a, injectArg g b)
  extractArg g (x,y) = (,) <$> extractArg g x <*> extractArg g y

instance AIGTestableValue g a b => AIGTestableValue g (Denom a) b where
  injectArg g (Denom x) = injectArg g x
  extractArg g x = Denom <$> extractArg g x

instance AIGTestableValue (BasicGraph s) Int (BV s) where
  injectArg g x  = AIG.bvFromInteger g (finiteBitSize x) (toInteger x)
  extractArg g x = fromInteger <$> AIG.asSigned g x

instance AIGTestableValue (BasicGraph s) Word32 (BV s) where
  injectArg g x  = AIG.bvFromInteger g (finiteBitSize x) (toInteger x)
  extractArg g x = fromInteger <$> AIG.asUnsigned g x

instance AIGTestableValue (BasicGraph s) Word64 (BV s) where
  injectArg g x  = AIG.bvFromInteger g (finiteBitSize x) (toInteger x)
  extractArg g x = fromInteger <$> AIG.asUnsigned g x

instance AIGTestableValue (BasicGraph s) Int32 (BV s) where
  injectArg g x  = AIG.bvFromInteger g (finiteBitSize x) (toInteger x)
  extractArg g x = fromInteger <$> AIG.asSigned g x

instance AIGTestableValue (BasicGraph s) Int64 (BV s) where
  injectArg g x  = AIG.bvFromInteger g (finiteBitSize x) (toInteger x)
  extractArg g x = fromInteger <$> AIG.asSigned g x

instance AIGTestableValue (BasicGraph s) Integer Integer where
  injectArg _g x = x
  extractArg _g x = Just x

instance AIGTestableValue (BasicGraph s) Bool (BasicLit s) where
  injectArg g x  = AIG.constant g x
  extractArg g x = AIG.asConstant g x

instance (Eq x, Show x, AIGTestableValue g x y) => AIGTestable g x (IO y) Property
 where
   runTest gph x y pre = pre ==> ioProperty $
     do gph' <- gph
        y' <- y
        case extractArg gph' y' of
          Nothing -> fail $ unwords ["Expected concrete output"]
          Just z
            | x == z    -> return True
            | otherwise -> fail $ unwords ["Expected", show x, "but got", show z]

instance
   (Precond x, Show x, AIGTestableValue g x y, AIGTestable g a b p) =>
   AIGTestable g (x -> a) (y -> b) (x -> p)
 where
   runTest gph f g pre = \x ->
     let y = (gph >>= \gph' -> return $ injectArg gph' x)
      in runTest gph (f x) (pushIO g y) (precond x && pre)


------------------------------------------------------------------------------------
-- Make a unit test from a concrete operation and an operation on AIGs

mkTest :: forall a b p
        . (Testable p, AIGTestable (BasicGraph ()) a b p)
       => String
       -> a
       -> (BasicGraph () -> b)
       -> TestTree
mkTest nm a b =
  withResource newBasicGraph (\_ -> return ()) $ \(g :: IO (BasicGraph ())) ->
    testProperty nm $ (runTest g a (pushIO b g) True :: p)


op_tests :: [TestTree]
op_tests =
  [ mkTest "ite"  (\b (x :: Word64) y -> if b then x else y) AIG.ite

  , mkTest "neg"  (negate :: Int64 -> Int64) AIG.neg
  , mkTest "add"  ((+)  :: Word64 -> Word64 -> Word64) AIG.add
  , mkTest "addC" addC AIG.addC
  , mkTest "sub"  ((-)  :: Word64 -> Word64 -> Word64) AIG.sub
  , mkTest "subC" subC AIG.subC
  , mkTest "addConst" addConst AIG.addConst
  , mkTest "subConst" subConst AIG.subConst

  , mkTest "mul"  ((*)  :: Word64 -> Word64 -> Word64) AIG.mul
  , mkTest "mulFull"  mulFull  AIG.mulFull
  , mkTest "smulFull" smulFull AIG.smulFull
  , mkTest "squot" squot AIG.squot
  , mkTest "srem"  srem  AIG.srem
  , mkTest "uquot" uquot AIG.uquot
  , mkTest "urem"  urem  AIG.urem

  , mkTest "shl"  (shiftL  :: Word64 -> Int -> Word64) AIG.shl
  , mkTest "ushr" (shiftR  :: Word64 -> Int -> Word64) AIG.ushr
  , mkTest "sshr" (shiftR  :: Int64  -> Int -> Int64)  AIG.sshr
  , mkTest "rol"  (rotateL :: Word64 -> Int -> Word64) AIG.rol
  , mkTest "ror"  (rotateR :: Word64 -> Int -> Word64) AIG.ror

  , mkTest "bvEq"    ((==) :: Word64 -> Word64 -> Bool) AIG.bvEq
  , mkTest "isZero"  (\x -> (x :: Word64) == 0) AIG.isZero
  , mkTest "nonZero" (\x -> (x :: Word64) /= 0) AIG.nonZero
  , mkTest "sle"  ((<=) :: Int64 -> Int64 -> Bool) AIG.sle
  , mkTest "slt"  ((<)  :: Int64 -> Int64 -> Bool) AIG.slt
  , mkTest "ule"  ((<=) :: Word64 -> Word64 -> Bool) AIG.ule
  , mkTest "ult"  ((<)  :: Word64 -> Word64 -> Bool) AIG.ult
  , mkTest "sabs" (abs  :: Int64 -> Int64) AIG.sabs

  , mkTest "sext" sext (\g x -> (return $ AIG.sext g x 64) :: IO _)
  , mkTest "zext" zext (\g x -> (return $ AIG.zext g x 64) :: IO _)
  , mkTest "trunc" trunc (\(_ :: BasicGraph ()) (x :: BV ()) -> (return $ AIG.trunc 64 x) :: IO _)

  , mkTest "priorityEncode" priorityEncode (\g -> AIG.priorityEncode g 32)
  , mkTest "logBase2_down" log2down AIG.logBase2_down
  , mkTest "logBase2_up"   log2up   AIG.logBase2_up
  , mkTest "clz"  clz AIG.countLeadingZeros
  , mkTest "ctz"  ctz AIG.countTrailingZeros

  , mkTest "pmul" pmul AIG.pmul
  , mkTest "pdiv" pdiv AIG.pdiv
  , mkTest "pmod" pmod AIG.pmod
  ]

addC :: Word32 -> Word32 -> (Word32, Bool)
addC x y = ( fromIntegral z, testBit z 32 )
 where z :: Word64
       z = fromIntegral x + fromIntegral y

subC :: Word32 -> Word32 -> (Word32, Bool)
subC x y = ( fromIntegral z, testBit z 32 )
 where z :: Word64
       z = fromIntegral x - fromIntegral y

addConst :: Word64 -> Integer -> Word64
addConst x y = x + fromInteger y

subConst :: Word64 -> Integer -> Word64
subConst x y = x - fromInteger y

mulFull :: Word32 -> Word32 -> Word64
mulFull x y = fromIntegral x * fromIntegral y

smulFull :: Int32 -> Int32 -> Int64
smulFull x y = fromIntegral x * fromIntegral y

uquot :: Word64 -> Denom Word64 -> Word64
uquot x (Denom y) = quot x y

urem :: Word64 -> Denom Word64 -> Word64
urem x (Denom y) = rem x y

squot :: Int64 -> Denom Int64 -> Int64
squot x (Denom y) = quot x y

srem :: Int64 -> Denom Int64 -> Int64
srem x (Denom y) = rem x y

sext :: Int32 -> Int64
sext = fromIntegral

zext :: Word32 -> Word64
zext = fromIntegral

trunc :: Word64 -> Word32
trunc = fromIntegral

log2down :: Word64 -> Int64
log2down x = fromIntegral (finiteBitSize x) - 1 - fromIntegral (countLeadingZeros x)

log2up :: Word64 -> Int64
log2up x = log2down (x - 1) + 1

clz :: Word64 -> Word64
clz = fromIntegral . countLeadingZeros

ctz :: Word64 -> Word64
ctz = fromIntegral . countTrailingZeros

pmul :: Word32 -> Word32 -> Word64
pmul x y = foldr xor zeroBits pprods
 where
  pprods = [ if testBit y i
                then shiftL (fromIntegral x) i
                else 0
           | i <- [0 .. finiteBitSize y - 1]
           ]

priorityEncode :: Word64 -> (Bool, Word32)
priorityEncode x
  | x == 0    = (False, 0)
  | otherwise = (True, fromIntegral (finiteBitSize x) - 1 - fromIntegral (countLeadingZeros x))

pdiv :: Word64 -> Denom Word32 -> Word64
pdiv x (Denom y) = fst $ pdivmod x y

pmod :: Word64 -> Denom Word32 -> Word32
pmod x (Denom y) = snd $ pdivmod x y

pdivmod :: Word64 -> Word32 -> (Word64, Word32)
pdivmod x y = go 0 x (finiteBitSize x - 1) start
  where
   start = finiteBitSize x - finiteBitSize y + countLeadingZeros y
   y'    = fromIntegral y

   go q r i j
     | j <  0      = (q,fromIntegral r)
     | testBit r i = go (setBit q j) (r `xor` (y' `shiftL` j)) (i-1) (j-1)
     | otherwise   = go q            r                         (i-1) (j-1)
