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
  , columnHeight
  , pushBit
  , wallaceTreeReduction
  ) where

import           Data.Monoid

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap.Strict as IMap
import qualified Data.Sequence as Seq

type Column b = IMap.IntMap (Seq.Seq b)
newtype AddTree b = AddTree { addTree :: MV.IOVector (Column b) }

newAddTree ::
  Int ->
  IO (AddTree b)
newAddTree n = AddTree <$> MV.replicate n IMap.empty

pushBit ::
  Int     {- ^ Output column -} ->
  (Int,b) {- ^ Delay heuristic, bit pair -} ->
  AddTree b ->
  IO ()
pushBit x (d,b) (AddTree mv) = MV.modify mv (IMap.alter f d) x
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

{-
popBit ::
  Int   {- ^ Column number -} ->
  AddTree b ->
  IO b
popBit x (AddTree mv) =
  do col <- MV.read mv x
     let (_d,b,col') = popColumn col
     MV.write mv x col'
     return b

popBit2 ::
  Int   {- ^ Column number -} ->
  AddTree b ->
  IO (b, b)
popBit2 x (AddTree mv) =
  do col <- MV.read mv x
     let (_d,b0,b1,col') = popColumn2 col
     MV.write mv x col'
     return (b0,b1)

popBit3 ::
  Int   {- ^ Column number -} ->
  AddTree b ->
  IO (b, b, b)
popBit3 x (AddTree mv) =
  do col <- MV.read mv x
     let (_d,b0,b1,b2,col') = popColumn3 col
     MV.write mv x col'
     return (b0,b1,b2)
-}

colHeight :: Column b -> Int
colHeight = getSum . foldMap (Sum . Seq.length)

columnHeight ::
  Int    {- ^ Column -} ->
  AddTree b ->
  IO Int
columnHeight x (AddTree mv) =
  getSum . foldMap (Sum . Seq.length) <$> MV.read mv x

wallaceTreeReduction :: forall b.
  b ->
  (Int -> b -> b -> b -> IO (Int,b,b)) {- ^ full adder, returns (delay,carry,sum) -} ->
  (Int -> b -> b -> IO (Int,b,b))      {- ^ half adder, returns (delay,carry,sum) -} ->
  AddTree b                 {- ^ addition tree to reduce -} ->
  IO (V.Vector b)
wallaceTreeReduction z fa ha input =
  do tmp <- MV.replicate n mempty
     final <- go input (AddTree tmp) 0 True
     V.generateM n (getBit final)

 where
 getBit :: AddTree b -> Int -> IO b
 getBit final i =
    do col <- MV.read (addTree final) (n-1-i)
       let h = colHeight col
       if | h == 0 -> return z
          | h == 1 -> let (_,b,_) = popColumn col
                       in return b
          | otherwise -> fail $ "Final tree has hight " ++ show h ++ " in column " ++ show i

 n = MV.length (addTree input)
 go xs ys i done
   | i+1 >= n, done = return ys
   | i+1 >= n =
       do tmp <- MV.replicate n mempty
          go ys (AddTree tmp) 0 True
   | otherwise    =
       do col <- MV.read (addTree xs) i
          done' <- reduceCol ys i col done
          go xs ys (i+1) done'

 reduceCol ys i col done
   | h == 0 = return done
   | h == 1 = do let (d,b,_) = popColumn col
                 pushBit i (d, b) ys
                 return done
   | h == 2 = do let (d,b0,b1,_) = popColumn2 col
                 (d',c,s) <- ha d b0 b1
                 pushBit i     (d',s) ys
                 pushBit (i+1) (d',c) ys
                 return False
   | otherwise = do let (d,b0,b1,b2,col') = popColumn3 col
                    (d',c,s) <- fa d b0 b1 b2
                    pushBit i     (d',s) ys
                    pushBit (i+1) (d',c) ys
                    reduceCol ys i col' False

   where h = colHeight col
