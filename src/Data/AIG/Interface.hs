{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}

{- |
Module      : Data.AIG.Interface
Copyright   : (c) Galois, Inc. 2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : portable

Interfaces for building, simulating and analysing And-Inverter Graphs (AIG).
-}

module Data.AIG.Interface
  ( -- * Main interface classes
    IsLit(..)
  , IsAIG(..)

    -- * Helper datatypes
  , Proxy(..)
  , SomeGraph(..)
  , Network(..)
  , networkInputCount

    -- * Representations of prover results
  , SatResult(..)
  , VerifyResult(..)
  , toSatResult
  , toVerifyResult
  ) where

import Control.Applicative ((<$>))
import Control.Monad
import Prelude hiding (not, and, or)

class IsLit l where
  -- | Negate a literal.
  not :: l s -> l s

  -- | Tests whether two lits are identical.
  -- This is only a syntactic check, and may return false
  -- even if the two literals represent the same predicate.
  (===) :: l s -> l s -> Bool

-- | A proxy is used to identify a specific AIG instance when
-- calling methods that create new AIGs.
data Proxy l g where
  Proxy :: IsAIG l g => (forall a . a -> a) -> Proxy l g

-- | An And-Inverter-Graph is a data structure storing bit-level
-- nodes.
--
-- Graphs are and-inverter graphs, which contain a number of input
-- literals and Boolean operations for creating new literals.
-- Every literal is part of a specific graph, and literals from
-- different networks may not be mixed.
--
-- Both the types for literals and graphs must take a single
-- phantom type for an arugment that is used to ensure that literals
-- from different networks cannot be used in the same operation.
class IsLit l => IsAIG l g | g -> l where
  -- | Create a temporary graph, and use it to compute a result value.
  withNewGraph :: Proxy l g -- ^ A 'Proxy' value, used for selecting the concrete
                            --   implementation typeclass
               -> (forall s . g s -> IO a)
                            -- ^ The AIG graph computation to run
               -> IO a
  withNewGraph p f = newGraph p >>= (`withSomeGraph` f)

  -- | Build a new graph instance, and packge it into the
  --   'SomeGraph' type that remembers the IsAIG implementation.
  newGraph :: Proxy l g
           -> IO (SomeGraph g)
  newGraph p = withNewGraph p (return . SomeGraph)

  -- | Read an AIG from a file, assumed to be in Aiger format
  aigerNetwork :: Proxy l g
               -> FilePath
               -> IO (Network l g)

  -- | Get unique literal in graph representing constant true.
  trueLit :: g s -> l s

  -- | Get unique literal in graph representing constant false.
  falseLit :: g s -> l s

  -- | Generate a constant literal value
  constant :: g s -> Bool -> l s
  constant g True  = trueLit  g
  constant g False = falseLit g

  -- | Return if the literal is a fixed constant.  If the literal
  --   is symbolic, return @Nothing@.
  asConstant :: g s -> l s -> Maybe Bool
  asConstant g l | l === trueLit g = Just True
                 | l === falseLit g = Just False
                 | otherwise = Nothing

  -- | Generate a fresh input literal
  newInput :: g s -> IO (l s)

  -- | Compute the logical and of two literals
  and :: g s -> l s -> l s -> IO (l s)

  -- | Build the conjunction of a list of literals
  ands :: g s -> [l s] -> IO (l s)
  ands g [] = return (trueLit g)
  ands g (x:r) = foldM (and g) x r

  -- | Compute the logical or of two literals
  or :: g s -> l s -> l s -> IO (l s)
  or g x y = not <$> and g (not x) (not y)

  -- | Compute the logical equality of two literals
  eq :: g s -> l s -> l s -> IO (l s)
  eq g x y = not <$> xor g x y

  -- | Compute the logical implication of two literals
  implies :: g s -> l s -> l s -> IO (l s)
  implies g x y = or g (not x) y

  -- | Compute the exclusive or of two literals
  xor :: g s -> l s -> l s -> IO (l s)
  xor g x y = do
    o <- or g x y
    a <- and g x y
    and g o (not a)

  -- | Perform a mux (if-then-else on the bits).
  mux :: g s -> l s -> l s -> l s -> IO (l s)
  mux g c x y = do
   x' <- and g c x
   y' <- and g (not c) y
   or g x' y'

  -- | Return number of inputs in the graph.
  inputCount :: g s -> IO Int

  -- | Get input at given index in the graph.
  getInput :: g s -> Int -> IO (l s)

  -- | Write network out to AIGER file.
  writeAiger :: FilePath -> Network l g -> IO ()

  -- | Check if literal is satisfiable in network.
  checkSat :: g s -> l s -> IO SatResult

  -- | Perform combinational equivalence checking.
  cec :: Network l g -> Network l g -> IO VerifyResult

  -- | Evaluate the network on a set of concrete inputs.
  evaluator :: g s
            -> [Bool]
            -> IO (l s -> Bool)

  -- | Evaluate the network on a set of concrete inputs.
  evaluate :: Network l g
           -> [Bool]
           -> IO [Bool]
  evaluate (Network g outputs) inputs = do
    f <- evaluator g inputs
    return (f <$> outputs)

-- | A network is an and-inverstor graph paired with it's outputs,
--   thus representing a complete combinational circuit.
data Network l g where
   Network :: IsAIG l g => g s -> [l s] -> Network l g

networkInputCount :: Network l g -> IO Int
networkInputCount (Network g _) = inputCount g

-- | Some graph quantifies over the state phantom variable for a graph.
data SomeGraph g where
  SomeGraph :: g s -> SomeGraph g

-- | Unpack @SomeGraph@ in a local scope so it can be used to compute a result
withSomeGraph :: SomeGraph g
              -> (forall s . g s -> IO a)
              -> IO a
withSomeGraph (SomeGraph g) f = f g

-- | Satisfiability check result.
data SatResult
   = Unsat
   | Sat !([Bool])
  deriving (Eq,Show)

-- | Result of a verification check.
data VerifyResult
   = Valid
   | Invalid [Bool]
  deriving (Eq, Show)

-- | Convert a sat result to a verify result by negating it.
toVerifyResult :: SatResult -> VerifyResult
toVerifyResult Unsat = Valid
toVerifyResult (Sat l) = Invalid l

-- | Convert a verify result to a sat result by negating it.
toSatResult :: VerifyResult -> SatResult
toSatResult Valid = Unsat
toSatResult (Invalid l) = Sat l
