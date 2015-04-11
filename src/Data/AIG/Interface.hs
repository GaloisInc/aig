{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveFunctor #-}

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
  , lazyMux

    -- * Helper datatypes
  , Proxy(..)
  , SomeGraph(..)
  , Network(..)
  , networkInputCount
  , networkOutputCount
  -- * Literal representations
  , LitView(..)
  , LitTree(..)
  , toLitTree
  , fromLitTree
  , toLitForest
  , fromLitForest
  , foldAIG
  , foldAIGs
  , unfoldAIG
  , unfoldAIGs

    -- * Representations of prover results
  , SatResult(..)
  , VerifyResult(..)
  , toSatResult
  , toVerifyResult

    -- * QuickCheck generators and testing
  , genLitView
  , genLitTree
  , getMaxInput
  , buildNetwork
  , randomNetwork
  ) where

import Control.Applicative
import Control.Monad
import Prelude hiding (not, and, or)
import Test.QuickCheck (Gen, Arbitrary(..), generate, oneof, sized, choose)

-- | Concrete datatype representing the ways
--   an AIG can be constructed.
data LitView a
  = And !a !a
  | NotAnd !a !a
  | Input !Int
  | NotInput !Int
  | TrueLit
  | FalseLit
 deriving (Eq,Show,Ord,Functor)

newtype LitTree = LitTree { unLitTree :: LitView LitTree }
 deriving (Eq,Show,Ord)

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

-- | An And-Inverter-Graph is a data structure storing bit-level nodes.
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

  -- | Build an evaluation function over an AIG using the provided view function
  abstractEvaluateAIG
          :: g s
          -> (LitView a -> IO a)
          -> IO (l s -> IO a)

-- | Evaluate the given literal using the provided view function
foldAIG :: IsAIG l g
        => g s
        -> (LitView a -> IO a)
        -> l s
        -> IO a
foldAIG n view l = do
   eval <- abstractEvaluateAIG n view
   eval l

-- | Evaluate the given list of literals using the provided view function
foldAIGs :: IsAIG l g
        => g s
        -> (LitView a -> IO a)
        -> [l s]
        -> IO [a]
foldAIGs n view ls = do
   eval <- abstractEvaluateAIG n view
   mapM eval ls


-- | Build an AIG literal by unfolding a constructor function
unfoldAIG :: IsAIG l g
          => g s
          -> (a -> IO (LitView a))
          -> a -> IO (l s)
unfoldAIG n unfold = f
 where f = unfold >=> g
       g (And x y)    = and' (f x) (f y)
       g (NotAnd x y) = fmap not $ and' (f x) (f y)
       g (Input i)    = getInput n i
       g (NotInput i) = fmap not $ getInput n i
       g TrueLit      = return $ trueLit n
       g FalseLit     = return $ falseLit n
       and' mx my = do
          x <- mx
          y <- my
          and n x y

-- | Build a list of AIG literals by unfolding a constructor function
unfoldAIGs :: IsAIG l g
          => g s
          -> (a -> IO (LitView a))
          -> [a] -> IO [l s]
unfoldAIGs n unfold = mapM (unfoldAIG n unfold)

-- | Extract a tree representation of the given literal
toLitTree :: IsAIG l g => g s -> l s -> IO LitTree
toLitTree g = foldAIG g (return . LitTree)

-- | Construct an AIG literal from a tree representation
fromLitTree :: IsAIG l g => g s -> LitTree -> IO (l s)
fromLitTree g = unfoldAIG g (return . unLitTree)

-- | Extract a forest representation of the given list of literal s
toLitForest :: IsAIG l g => g s -> [l s] -> IO [LitTree]
toLitForest g = foldAIGs g (return . LitTree)

-- | Construct a list of AIG literals from a forest representation
fromLitForest :: IsAIG l g => g s -> [LitTree] -> IO [l s]
fromLitForest g = unfoldAIGs g (return . unLitTree)

-- | Short-cutting mux operator that optimizes the case
--   where the test bit is a concrete literal
lazyMux :: IsAIG l g => g s -> l s -> IO (l s) -> IO (l s) -> IO (l s)
lazyMux g c
  | c === (trueLit g)  = \x _y -> x
  | c === (falseLit g) = \_x y -> y
  | otherwise = \x y -> join $ pure (mux g c) <*> x <*> y

-- | A network is an and-invertor graph paired with it's outputs,
-- thus representing a complete combinational circuit.
data Network l g where
   Network :: IsAIG l g => g s -> [l s] -> Network l g

-- | Get number of inputs associated with current network.
networkInputCount :: Network l g -> IO Int
networkInputCount (Network g _) = inputCount g

-- | Number of outputs associated with a network.
networkOutputCount :: Network l g -> Int
networkOutputCount (Network _ o) = length o

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
   | SatUnknown
  deriving (Eq,Show)

-- | Result of a verification check.
data VerifyResult
   = Valid
   | Invalid [Bool]
   | VerifyUnknown
  deriving (Eq, Show)

-- | Convert a sat result to a verify result by negating it.
toVerifyResult :: SatResult -> VerifyResult
toVerifyResult Unsat = Valid
toVerifyResult (Sat l) = Invalid l
toVerifyResult SatUnknown = VerifyUnknown

-- | Convert a verify result to a sat result by negating it.
toSatResult :: VerifyResult -> SatResult
toSatResult Valid = Unsat
toSatResult (Invalid l) = Sat l
toSatResult VerifyUnknown = SatUnknown

-- | Generate an arbitrary `LitView` given a generator for `a`
genLitView :: Gen a -> Gen (LitView a)
genLitView gen = oneof
     [ return TrueLit
     , return FalseLit
     , sized $ \n -> choose (0,n-1) >>= \i -> return (Input i)
     , sized $ \n -> choose (0,n-1) >>= \i -> return (NotInput i)
     , do x <- gen
          y <- gen
          return (And x y)
     , do x <- gen
          y <- gen
          return (NotAnd x y)
     ]

-- | Generate an arbitrary `LitTree`
genLitTree :: Gen LitTree
genLitTree = fmap LitTree $ genLitView genLitTree

-- | Given a LitTree, calculate the maximum input number in the tree.
--   Returns 0 if no inputs are referenced.
getMaxInput :: LitTree -> Int
getMaxInput (LitTree x) =
  case x of
     TrueLit -> 0
     FalseLit -> 0
     Input i -> i
     NotInput i -> i
     And a b -> max (getMaxInput a) (getMaxInput b)
     NotAnd a b -> max (getMaxInput a) (getMaxInput b)

instance Arbitrary LitTree where
  arbitrary = genLitTree
  shrink (LitTree TrueLit)      = []
  shrink (LitTree FalseLit)     = []
  shrink (LitTree (Input _))    = [LitTree TrueLit, LitTree FalseLit]
  shrink (LitTree (NotInput _)) = [LitTree TrueLit, LitTree FalseLit]
  shrink (LitTree (And x y)) =
      [ LitTree TrueLit, LitTree FalseLit, x, y ] ++
      [ LitTree (And x' y') | (x',y') <- shrink (x,y) ]
  shrink (LitTree (NotAnd x y)) =
      [ LitTree TrueLit, LitTree FalseLit, x, y ] ++
      [ LitTree (NotAnd x' y') | (x',y') <- shrink (x,y) ]


-- | Given a list of LitTree, construct a corresponding AIG network
buildNetwork :: IsAIG l g => Proxy l g -> [LitTree] -> IO (Network l g)
buildNetwork proxy litForrest = do
   let maxInput = foldr max 0 $ map getMaxInput litForrest
   (SomeGraph g) <- newGraph proxy
   forM_ [0..maxInput] (\_ -> newInput g)
   ls <- fromLitForest g litForrest
   return (Network g ls)

-- | Generate a random network by building a random `LitTree`
--   and using that to construct a network.
randomNetwork :: IsAIG l g => Proxy l g -> IO (Network l g)
randomNetwork proxy = generate arbitrary >>= buildNetwork proxy
