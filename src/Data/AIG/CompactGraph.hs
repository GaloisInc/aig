{- |
Module      : Data.AIG.CompactGraph
Copyright   : (c) Galois, Inc. 2021
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable

A pure Haskell implementation of the IsAIG class with support for AIGER
and CNF file creation.
-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Data.AIG.CompactGraph
  ( CompactGraph
  , CompactLit
  , CompactNetwork
  , compactProxy
  ) where

import Control.Monad (forM_)
import Data.Bits (shiftL, shiftR, (.&.), (.|.), xor, testBit)
import Data.IORef (IORef, newIORef, modifyIORef', readIORef)
import Data.List (elemIndex, intersperse)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import Data.Word (Word32)
import System.IO (Handle, withFile, IOMode(..))

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
    -- ^ The largest variable ID used so far.
  , inputs  :: IORef [Var]
    -- ^ Inputs, in reverse order!
  , andMap  :: IORef (Map Var (CompactLit s, CompactLit s))
    -- ^ A map from and gate variables to their input literals.
  }

------------------------------------------------------------------
-- | A literal in a CompactGraph.
newtype CompactLit s = CompactLit Word32
 deriving (Eq, Ord, Show)

type CompactNetwork s = Network CompactLit CompactGraph

-- | The type of AIGER file to create. We don't currently support user
-- specification of this. The distinction primarily exists to ease
-- debugging.
data AIGFileMode
  = ASCII
  | Binary

modeString :: AIGFileMode -> BS.ByteString
modeString ASCII = "aag"
modeString Binary = "aig"

bsUnwords :: [BS.Builder] -> BS.Builder
bsUnwords = mconcat . intersperse (BS.charUtf8 ' ')

compactProxy :: Proxy CompactLit CompactGraph
compactProxy = Proxy (\x -> x)

-- | Turn a variable into its positive literal.
varToLit :: Var -> CompactLit s
varToLit (Var v) = CompactLit (v `shiftL` 1)

-- | Extract the variable a literal refers to.
litToVar :: CompactLit s -> Var
litToVar (CompactLit l) = Var (l `shiftR` 1)

-- | Determine whether the given literal is negated.
litNegated :: CompactLit s -> Bool
litNegated (CompactLit l) = testBit l 0

-- | Return the second literal with its polarity altered to match the
-- first.
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

-- | Create a map associating a new destination variable with each
-- existing variable. Used to ensure the ordering invariants of the
-- binary AIGER file format.
mkVarMap ::
  [Var] ->
  Map Var (CompactLit s, CompactLit s) ->
  (Map Var Var)
mkVarMap ins gateMap =
  Map.fromList (zip varList [Var 0..])
    where
      varList = [Var 0] ++ ins ++ Map.keys gateMap

-- | Adjust a literal according to the given variable mapping.
lookupLit :: CompactLit s -> Map Var Var -> Maybe (CompactLit s)
lookupLit l m = (copySign l . varToLit) <$> Map.lookup (litToVar l) m

hPutBBLn :: Handle -> BS.Builder -> IO ()
hPutBBLn h b = BS.hPutBuilder h (b <> BS.charUtf8 '\n')

-- | Write an AIGER header line to the given handle.
writeHeader ::
  Handle ->
  AIGFileMode ->
  Var ->
  [Var] ->
  Int ->
  [CompactLit s] ->
  Map Var (CompactLit s, CompactLit s) ->
  IO ()
writeHeader h format (Var var) ins latches outs gateMap =
  do hPutBBLn h $ bsUnwords [ BS.byteString (modeString format)
                            , BS.word32Dec var
                            , BS.intDec (length ins)
                            , BS.intDec latches
                            , BS.intDec (length outs)
                            , BS.intDec (Map.size gateMap)
                            ]

-- | Write AIGER input lines to the given handle.
writeInputs :: Handle -> AIGFileMode -> Int -> Map Var Var -> [Var] -> IO ()
writeInputs _ Binary _ _ _ = return ()
writeInputs h ASCII latches varMap ins =
  forM_ (take inCount ins) $ \v ->
    case varToLit <$> Map.lookup v varMap of
      Just (CompactLit i) -> hPutBBLn h $ BS.word32Dec i
      Nothing -> fail $ "Input not found: " ++ show v
  where inCount = length ins - latches

-- | Write AIGER latch lines to the given handle.
writeLatches ::
  Handle ->
  AIGFileMode ->
  Int ->
  Map Var Var ->
  [Var] ->
  [CompactLit s] ->
  IO ()
writeLatches h format latches varMap ins outs =
  forM_ latchPairs $ \(v, n) ->
    case (Map.lookup v varMap, lookupLit n varMap) of
      (Just (Var vi), Just (CompactLit ni)) ->
        case format of
          ASCII -> hPutBBLn h $ bsUnwords [ BS.word32Dec vi
                                          , BS.word32Dec ni
                                          ]
          Binary -> hPutBBLn h $ BS.word32Dec ni
      _ -> fail $ "Latch not found: " ++ show v ++ " " ++ show n
  where
    inCount = length ins - latches
    outCount = length outs - latches
    latchPairs = zip (drop inCount ins) (drop outCount outs)

-- | Write AIGER output lines to the given handle.
writeOutputs :: Handle -> Int -> Map Var Var -> [CompactLit s] -> IO ()
writeOutputs h latches varMap outs =
  forM_ (take outCount outs) $ \l ->
    case copySign l <$> lookupLit l varMap of
      Just (CompactLit i) -> hPutBBLn h $ BS.word32Dec i
      Nothing -> fail $ "Output not found: " ++ show l
  where outCount = length outs - latches

-- | Write AIGER and gate lines or bytes to the given handle.
writeAnds ::
  Handle ->
  AIGFileMode ->
  Map Var Var ->
  Map Var (CompactLit s, CompactLit s) ->
  IO ()
writeAnds h format varMap gateMap =
  forM_ (Map.assocs gateMap) $ \(v, (l, r)) ->
    case (varToLit <$> Map.lookup v varMap
         , lookupLit l varMap
         , lookupLit r varMap) of
      (Just vi, Just li, Just ri) ->
        writeAnd h format vi li ri
      _ -> fail $ "And not found: " ++ show (l, r)

-- | Helper for @writeAnds@ to write the actual content of the gate.
writeAnd ::
  Handle ->
  AIGFileMode ->
  CompactLit s ->
  CompactLit s ->
  CompactLit s ->
  IO ()
writeAnd h format (CompactLit v) (CompactLit l) (CompactLit r) =
  case format of
    ASCII ->
      hPutBBLn h $ bsUnwords [ BS.word32Dec v
                             , BS.word32Dec l
                             , BS.word32Dec r
                             ]
    Binary ->
      do BS.hPutBuilder h (encodeDifference (v - l))
         BS.hPutBuilder h (encodeDifference (l - r))

-- | Encode a 32-bit value, representing a difference, in a variable
-- number of bytes.
encodeDifference :: Word32 -> BS.Builder
encodeDifference w@(fromIntegral -> b)
  | w < 0x80 = BS.word8 b
  | otherwise = BS.word8 ((b .&. 0x7f) .|. 0x80) <>
                encodeDifference (w `shiftR` 7)

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
           format = Binary
       writeHeader h format var ins latches outs gateMap
       writeInputs h format latches vm ins
       writeLatches h format latches vm ins outs
       writeOutputs h latches vm outs
       writeAnds h format vm gateMap

  writeCNF g out fp =
    withFile fp WriteMode $ \h ->
    do Var var <- readIORef (maxVar g)
       ins <- reverse <$> readIORef (inputs g)
       gateMap <- readIORef (andMap g)
       let vm = mkVarMap ins gateMap
           nvars = fromIntegral var + 1
           nclauses = (3 * Map.size gateMap) + 2
           litToCNF lit =
             case Map.lookup (litToVar lit) vm of
               Just (Var v) ->
                 do let n = fromIntegral v + 1
                    return $ if litNegated lit then (-n) else n
               Nothing -> fail $ "Literal not found: " ++ show lit
           putClause lits =
             hPutBBLn h $ (bsUnwords . map BS.intDec) lits <> " 0"
       hPutBBLn h $ bsUnwords [ "p", "cnf"
                              , BS.intDec nvars
                              , BS.intDec nclauses
                              ]
       forM_ (Map.assocs gateMap) $ \(v, (ll, rl)) ->
         do n <- litToCNF (varToLit v)
            li <- litToCNF ll
            ri <- litToCNF rl
            -- 3 clauses for each gate
            putClause [-n, li]
            putClause [-n, ri]
            putClause [n, -li, -ri]
       ovar <- litToCNF out
       -- 2 more clauses
       putClause [ovar]
       putClause [-1]
       return [2 .. length ins + 1]

  checkSat _g _l =
    fail "Cannot SAT check graphs in the CompactGraph implementation"

  cec _g1 _g2 =
    fail "Cannot CEC graphs in the CompactGraph implementation"

  -- | Evaluate the network on a set of concrete inputs.
  evaluator _g _xs =
    fail "evaluator not implemented (TODO)"

  -- | Examine the outermost structure of a literal to see how it was
  -- constructed. This could certainly be made more efficient if
  -- necessary.
  litView g l =
    do ins <- reverse <$> readIORef (inputs g)
       gateMap <- readIORef (andMap g)
       let v = litToVar l
       case (elemIndex v ins, Map.lookup v gateMap, litNegated l) of
         (Just i, _, False)        -> return (Input i)
         (Just i, _, True)         -> return (NotInput i)
         (_, Just (l1, l2), False) -> return (And l1 l2)
         (_, Just (l1, l2), True)  -> return (NotAnd l1 l2)
         _ | l == falseLit g       -> return FalseLit
         _ | l == trueLit g        -> return TrueLit
         _ -> fail $ "Invalid literal: " ++ show l

  -- | Build an evaluation function over an AIG using the provided view
  -- function
  abstractEvaluateAIG _g _f =
    fail "Function abstractEvaluateAIG not implemented for CompactGraph (TODO)"
