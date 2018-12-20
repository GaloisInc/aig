{- |
Module      : Data.AIG.AddTree
Copyright   : (c) Galois, Inc. 2018
License     : BSD3
Maintainer  : rdockins@galois.com
Stability   : experimental
Portability : portable

A data structure for building 3:2 and 2:2 addition reduction
trees.  In particular, we can use the same basic structure for
performing both Wallace tree reduction (Wallace, 1964 "A suggestion for a fast multiplier"),
and Dadda tree reduction (Dadda, 1965 "Some schemes for parallel multipliers") for
multiplication circuits.  We can also use these data structures for performing intermediate
reduction for popcount circuits.
-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
module Data.AIG.AddTree
  ( AddTree
  , newAddTree
  , pushBit
  , wallaceTreeReduction
  , daddaTreeReduction
  ) where

import           Control.Monad
import           Data.Bits
import           Data.Monoid

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap.Strict as IMap
import qualified Data.Sequence as Seq

type Column b = IMap.IntMap (Seq.Seq b)

newtype AddTree b = AddTree { addTree :: MV.IOVector (Column b) }

-- | Create a new addition reduction tree with the given number of columns.
newAddTree ::
  Int {- ^ Maximum number of columns in the reduction tree -} ->
  IO (AddTree b)
newAddTree n = AddTree <$> MV.replicate n IMap.empty


-- | Push a new bit into the addition tree.  If the bit's position
--   doesn't fit, it is silently discarded!  The column numbers
--   correspond to the positional value of the resulting number;
--   i.e., column 0 is the least significant bit.
--
--   Bits are later pulled out of each column prefering bits with
--   the lowest value for the delay heuristic first.
pushBit ::
  Int     {- ^ Output column -} ->
  (Int,b) {- ^ Delay heuristic, bit pair -} ->
  AddTree b ->
  IO ()
pushBit x db (AddTree mv) | 0 <= x && x < MV.length mv = MV.modify mv (pushColumn db) x
pushBit _ _ _ = return () -- out-of-bounds bits are just silently thrown away!


pushColumn ::
  (Int,b) ->
  Column b ->
  Column b
pushColumn (d,b) = IMap.alter f d
  where f Nothing  = Just (Seq.singleton b)
        f (Just s) = Just (s Seq.|> b)


popColumn ::
  Column b ->
  (Int, b, Column b)
popColumn col =
  let ((d, bs), col') = IMap.deleteFindMin col in
  case Seq.viewl bs of
     b Seq.:< bs' ->
       let col'' = if null bs'
                        then col'
                        else IMap.insert d bs' col'
        in (d, b, col'')
     Seq.EmptyL -> popColumn col'

popColumn2 ::
  Column b ->
  (Int, b, b, Column b)
popColumn2 col =
  let ((d, bs), col') = IMap.deleteFindMin col in
  case Seq.viewl bs of
     b0 Seq.:< bs' ->
       case Seq.viewl bs' of
         b1 Seq.:< bs'' ->
           let col'' = if null bs''
                         then col'
                         else IMap.insert d bs'' col'
            in (d, b0, b1, col'')
         Seq.EmptyL ->
           let (d', b1, col'') = popColumn col'
            in (d', b0, b1, col'')
     Seq.EmptyL -> popColumn2 col'

popColumn3 ::
  Column b ->
  (Int, b, b, b, Column b)
popColumn3 col =
  let ((d, bs), col') = IMap.deleteFindMin col in
  case Seq.viewl bs of
     b0 Seq.:< bs' ->
       case Seq.viewl bs' of
         b1 Seq.:< bs'' ->
           case Seq.viewl bs'' of
             b2 Seq.:< bs''' ->
               let col'' = if null bs'''
                             then col'
                             else IMap.insert d bs''' col'
                 in (d, b0, b1, b2, col'')
             Seq.EmptyL ->
               let (d', b2, col'') = popColumn col'
                in (d', b0, b1, b2, col'')
         Seq.EmptyL ->
           let (d', b1, b2, col'') = popColumn2 col'
            in (d', b0, b1, b2, col'')
     Seq.EmptyL -> popColumn3 col'


colHeight :: Column b -> Int
colHeight = getSum . foldMap (Sum . Seq.length)

maxColumnHeight :: AddTree b -> IO Int
maxColumnHeight (AddTree mv) =
  maximum <$> (forM [0 .. MV.length mv-1] (\i -> colHeight <$> MV.read mv i))


-- | Having reduced the tree to a maximum column height of 2, compute the final
--   sum using a standard ripple-carry adder.
finishReduction :: forall b.
  b ->
  (Int -> b -> b -> b -> IO (Int,b,b)) {- ^ full adder, returns (delay,carry,sum) -} ->
  (Int -> b -> b -> IO (Int,b,b))      {- ^ half adder, returns (delay,carry,sum) -} ->
  AddTree b                            {- ^ addition tree to reduce -} ->
  IO (V.Vector b)
finishReduction z fa ha ys = V.generateM (MV.length (addTree ys)) $ \i ->
   do col <- MV.read (addTree ys) i
      if | colHeight col == 0 ->
            do return z

         | colHeight col == 1 ->
            do let (_,b0,_) = popColumn col
               return b0

         | colHeight col == 2 ->
            do let (d,b0,b1,_) = popColumn2 col
               (d',c,s) <- ha d b0 b1
               pushBit (i+1) (d',c) ys
               return s

         | colHeight col == 3 ->
            do let (d,b0,b1,b2,_) = popColumn3 col
               (d',c,s) <- fa d b0 b1 b2
               pushBit (i+1) (d',c) ys
               return s

         | otherwise ->
            fail ("finishReduction: too many remaining bits! " ++ show (colHeight col))

-- | Sequence of maximum column heights for Dadda tree reduction.
--
--     j(0)   = 2
--
--     j(n+1) = floor( 1.5 * j(n) )
daddaSequence :: [Int]
daddaSequence = 2 : [ x + (x `shiftR` 1)  | x <- daddaSequence ]

-- | Find the initial segment of the Dadda sequence that is
--   less than the given value, and return it, in reversed order.
--
--   These values determine how much reduction is done in each round
--   of Dadda tree reduction.
daddaReductionSequence :: Int -> [Int]
daddaReductionSequence n = go daddaSequence []
 where
 go (x:xs) output
   | x >= n    = output
   | otherwise = go xs (x:output)
 go _ _ = error "daddaSequenceReduction: impossible!"


-- | Given a collection of bits in a reduction tree, compute the
--   final sum using the Dadda reduction tree strategy.  This strategy
--   reduces as few bits as possible in each round (while still maintaining
--   optimal number of reduction rounds for a given bit width) and
--   is willing to spills carry bits one column over in a single round.
daddaTreeReduction :: forall b.
  b ->
  (Int -> b -> b -> b -> IO (Int,b,b)) {- ^ full adder, returns (delay,carry,sum) -} ->
  (Int -> b -> b -> IO (Int,b,b))      {- ^ half adder, returns (delay,carry,sum) -} ->
  AddTree b                 {- ^ addition tree to reduce -} ->
  IO (V.Vector b)
daddaTreeReduction z fa ha input =
  do hs <- daddaReductionSequence <$> maxColumnHeight input
     V.reverse <$> go input hs

 where
 n = MV.length (addTree input)

 go xs [] =
    do mh <- maxColumnHeight xs
       unless (mh <= 2) (fail $ "dadda reduction failed with too many remaining bits " ++ show mh)
       finishReduction z fa ha xs

 go xs (h:hs) =
    do forM_ [0..n-1] $ \i ->
         do col <- MV.read (addTree xs) i
            reduceCol h xs i col
       mh <- maxColumnHeight xs
       unless (mh <= h) (fail $ unwords ["dadda reduction failed with too many remaining bits", show mh, show (h:hs)])
       go xs hs

 reduceCol h ys i col
   | colh <= h = MV.write (addTree ys) i col

   | colh == h+1 =
       do let (d,b0,b1,col') = popColumn2 col
          (d',c,s) <- ha d b0 b1
          let col'' = pushColumn (d',s) col'
          pushBit (i+1) (d',c) ys
          MV.write (addTree ys) i col''

   | otherwise =
       do let (d,b0,b1,b2,col') = popColumn3 col
          (d',c,s) <- fa d b0 b1 b2
          let col'' = pushColumn (d',s) col'
          pushBit (i+1) (d',c) ys
          reduceCol h ys i col''

  where colh = colHeight col


-- | Given a collection of bits in a reduction tree, compute the
--   final sum using the Wallace reduction tree strategy.  This strategy
--   greedly reduces as many bits as possible in each round without spilling
--   and carry bits until the next round.
wallaceTreeReduction :: forall b.
  b ->
  (Int -> b -> b -> b -> IO (Int,b,b)) {- ^ full adder, returns (delay,carry,sum) -} ->
  (Int -> b -> b -> IO (Int,b,b))      {- ^ half adder, returns (delay,carry,sum) -} ->
  AddTree b                 {- ^ addition tree to reduce -} ->
  IO (V.Vector b)
wallaceTreeReduction z fa ha input =
  do tmp <- AddTree <$> MV.replicate n mempty
     V.reverse <$> go input tmp 0

 where

 n = MV.length (addTree input)

 go xs ys i
   | i >= n =
       do mh <- maxColumnHeight ys
          if mh > 2
            then do tmp <- MV.replicate n mempty
                    go ys (AddTree tmp) 0
            else finishReduction z fa ha ys

   | otherwise    =
       do col <- MV.read (addTree xs) i
          reduceCol ys i col
          go xs ys (i+1)

 reduceCol ys i col
   | h == 0 = return ()
   | h == 1 = do let (d,b,_) = popColumn col
                 pushBit i (d, b) ys
   | h == 2 = do let (d,b0,b1,_) = popColumn2 col
                 (d',c,s) <- ha d b0 b1
                 pushBit i     (d',s) ys
                 pushBit (i+1) (d',c) ys
   | otherwise = do let (d,b0,b1,b2,col') = popColumn3 col
                    (d',c,s) <- fa d b0 b1 b2
                    pushBit i     (d',s) ys
                    pushBit (i+1) (d',c) ys
                    reduceCol ys i col'

   where h = colHeight col
