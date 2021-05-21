{- |
Module      : Data.AIG.CompactGraph
Copyright   : (c) Galois, Inc. 2021
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable

Interfaces for building, simulating and analysing And-Inverter Graphs (AIG).
-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
module Data.AIG.CompactGraph
  ( CompactGraph
  , CompactLit
  , CompactNetwork
  , compactProxy
  ) where

import Control.Monad (forM_)
import Data.Bits (shiftL, shiftR, (.&.), (.|.), xor, testBit)
import Data.IORef (IORef, newIORef, modifyIORef', readIORef)
import Data.List (elemIndex)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Word (Word32)
import System.IO (Handle, withFile, IOMode(..), hPutStrLn)

import Data.AIG.Interface hiding (xor)

newtype Var = Var Word32
  deriving (Eq, Ord, Show, Enum)

nextVar :: Var -> Var
nextVar (Var v) = Var (v + 1)

------------------------------------------------------------------
-- | A compact "Graph" datastructure similar to the AIGER format.
data CompactGraph s =
  CompactGraph {
    maxVar  :: IORef Var
  , inputs  :: IORef [Var] -- ^ Inputs, in reverse order!
  , andMap  :: IORef (Map Var (CompactLit s, CompactLit s))
  }

------------------------------------------------------------------
-- | A literal in a CompactGraph.
newtype CompactLit s = CompactLit Word32
 deriving (Eq, Ord, Show)

type CompactNetwork s = Network CompactLit CompactGraph

compactProxy :: Proxy CompactLit CompactGraph
compactProxy = Proxy (\x -> x)

varToLit :: Var -> CompactLit s
varToLit (Var v) = CompactLit (v `shiftL` 1)

litToVar :: CompactLit s -> Var
litToVar (CompactLit l) = Var (l `shiftR` 1)

litNegated :: CompactLit s -> Bool
litNegated (CompactLit l) = testBit l 0

copySign :: CompactLit s -> CompactLit s -> CompactLit s
copySign (CompactLit src) (CompactLit dst) =
  CompactLit ((dst .&. 0xFFFFFFFE) .|. (src .&. 0x00000001))

newCompactGraph :: IO (CompactGraph s)
newCompactGraph =
  do maxVar  <- newIORef (Var 0)
     inputs  <- newIORef []
     andMap  <- newIORef Map.empty
     return (CompactGraph {..})

newVar :: CompactGraph s -> IO Var
newVar g =
  do modifyIORef' (maxVar g) nextVar
     readIORef (maxVar g)

mkVarMap ::
  [Var] ->
  Map Var (CompactLit s, CompactLit s) ->
  (Map Var Var)
mkVarMap ins gateMap =
  Map.fromList (zip varList [Var 0..])
    where
      varList = [Var 0] ++ ins ++ Map.keys gateMap

lookupLit :: CompactLit s -> Map Var Var -> Maybe (CompactLit s)
lookupLit l m = (copySign l . varToLit) <$> Map.lookup (litToVar l) m

writeHeader ::
  Handle ->
  Var ->
  [Var] ->
  Int ->
  [CompactLit s] ->
  Map Var (CompactLit s, CompactLit s) ->
  IO ()
writeHeader h (Var var) ins latches outs gateMap =
  do hPutStrLn h $ unwords [ "aag"
                           , show var
                           , show (length ins)
                           , show latches
                           , show (length outs)
                           , show (Map.size gateMap)
                           ]

writeInputs :: Handle -> Int -> Map Var Var -> [Var] -> IO ()
writeInputs h latches varMap ins =
  forM_ (take inCount ins) $ \v ->
    case varToLit <$> Map.lookup v varMap of
      Just (CompactLit i) -> hPutStrLn h (show i)
      Nothing -> fail $ "Input not found: " ++ show v
  where inCount = length ins - latches

writeLatches ::
  Handle ->
  Int ->
  Map Var Var ->
  [Var] ->
  [CompactLit s] ->
  IO ()
writeLatches h latches varMap ins outs =
  forM_ latchPairs $ \(v, n) ->
    case (Map.lookup v varMap, lookupLit n varMap) of
      (Just (Var vi), Just (CompactLit ni)) ->
        hPutStrLn h $ unwords [show vi, show ni]
      _ -> fail $ "Latch not found: " ++ show v ++ " " ++ show n
  where
    inCount = length ins - latches
    outCount = length outs - latches
    latchPairs = zip (drop inCount ins) (drop outCount outs)

writeOutputs :: Handle -> Int -> Map Var Var -> [CompactLit s] -> IO ()
writeOutputs h latches varMap outs =
  forM_ (take outCount outs) $ \l ->
    case copySign l <$> lookupLit l varMap of
      Just (CompactLit i) -> hPutStrLn h (show i)
      Nothing -> fail $ "Output not found: " ++ show l
  where outCount = length outs - latches

writeAnds ::
  Handle ->
  Map Var Var ->
  Map Var (CompactLit s, CompactLit s) ->
  IO ()
writeAnds h varMap gateMap =
  forM_ (Map.assocs gateMap) $ \(v, (l, r)) ->
    case (varToLit <$> Map.lookup v varMap, lookupLit l varMap, lookupLit r varMap) of
      (Just (CompactLit v'), Just (CompactLit li), Just (CompactLit ri)) ->
        hPutStrLn h $ unwords [show v', show li, show ri]
      _ -> fail $ "And not found: " ++ show (l, r)

instance IsLit CompactLit where
  not (CompactLit x) = CompactLit (x `xor` 1)
  (===) = (==)

instance IsAIG CompactLit CompactGraph where
  withNewGraph _proxy k = k =<< newCompactGraph

  aigerNetwork _proxy _fp =
    fail "Cannot read AIGER files from the CompactGraph implementation"

  trueLit  _g = CompactLit 1
  falseLit _g = CompactLit 0

  newInput g =
    do v <- newVar g
       modifyIORef' (inputs g) (v :)
       return (varToLit v)

  and g x y =
    do v <- newVar g
       let l = max x y
           r = min x y
       modifyIORef' (andMap g) $ Map.insert v (l, r)
       return (varToLit v)

  inputCount g = length <$> readIORef (inputs g)

  -- | Get input at given index in the graph.
  getInput _g _i =
    fail "Function getInput not implemented for CompactGraph"

  writeAiger fp ntk = writeAigerWithLatches fp ntk 0

  writeAigerWithLatches fp (Network g outs) latches =
    withFile fp WriteMode $ \h ->
    do var <- readIORef (maxVar g)
       ins <- reverse <$> readIORef (inputs g)
       gateMap <- readIORef (andMap g)
       let vm = mkVarMap ins gateMap
       {-
       print vm
       print ins
       print outs
       print gateMap
       -}
       writeHeader h var ins latches outs gateMap
       writeInputs h latches vm ins
       writeLatches h latches vm ins outs
       writeOutputs h latches vm outs
       writeAnds h vm gateMap

  writeCNF _g _l _fp =
    fail "Cannot write CNF files from the CompactGraph implementation"

  checkSat _g _l =
    fail "Cannot SAT check graphs in the CompactGraph implementation"

  cec _g1 _g2 =
    fail "Cannot CEC graphs in the CompactGraph implementation"

  -- | Evaluate the network on a set of concrete inputs.
  evaluator _g _xs =
    fail "evaluator not implemented (TODO)"

  -- | Examine the outermost structure of a literal to see how it was constructed
  litView g l =
    do ins <- reverse <$> readIORef (inputs g) -- TODO: this will be slow
       gateMap <- readIORef (andMap g)
       let v = litToVar l
       case (elemIndex v ins, Map.lookup v gateMap) of
         (Just i, _) -> return (f i)
           where f = if litNegated l then NotInput else Input
         (_, Just (l1, l2)) -> return (f l1 l2)
           where f = if litNegated l then NotAnd else And
         _ | l == falseLit g -> return FalseLit
         _ | l == trueLit g -> return TrueLit
         _ -> fail $ "Invalid literal: " ++ show l

  -- | Build an evaluation function over an AIG using the provided view function
  abstractEvaluateAIG _g _f =
    fail "Function abstractEvaluateAIG not implemented for CompactGraph (TODO)"
