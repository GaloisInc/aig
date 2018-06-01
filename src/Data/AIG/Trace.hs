{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}


{- |
Module      : Data.AIG.Interface
Copyright   : (c) Galois, Inc. 2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : portable

A tracing wrapper AIG interface.  Given an underlying AIG interface, this
wrapper intercepts all interface calls and logs them to a file for debugging
purposes.
-}

module Data.AIG.Trace where

import Prelude hiding (not, and, or)
import Data.IORef
import Data.List (intersperse)
import System.IO
import Control.Exception
import System.IO.Unsafe

import Data.AIG.Interface


class Traceable l where
  compareLit :: l s -> l s -> Ordering
  showLit :: l s -> String

newtype TraceLit l s = TraceLit { unTraceLit :: l s }

data TraceGraph (l :: * -> * ) g s
   = TraceGraph
   { tGraph :: g s
   , tActive :: IORef (Maybe Handle)
   }

proxy :: Traceable l => Proxy l g -> Proxy (TraceLit l) (TraceGraph l g)
proxy (Proxy _) = Proxy (\x -> x)

activateTracing :: TraceGraph l g s -> FilePath -> IO ()
activateTracing g fp = do
    maybe (return ()) hClose =<< readIORef (tActive g)
    h <- openFile fp WriteMode
    writeIORef (tActive g) (Just h)

deactiveTracing :: TraceGraph l g s -> IO ()
deactiveTracing g = do
    maybe (return ()) hClose =<< readIORef (tActive g)
    writeIORef (tActive g) Nothing

withTracing :: TraceGraph l g s -> FilePath -> IO a -> IO a
withTracing g fp m =
   bracket (do old <- readIORef (tActive g)
               h <- openFile fp WriteMode
               writeIORef (tActive g) (Just h)
               return (h,old))
           (\(h,old) -> hClose h >> writeIORef (tActive g) old)
           (\_ -> m)

instance IsLit l => IsLit (TraceLit l) where
  not (TraceLit l) = TraceLit (not l)
  (TraceLit x) === (TraceLit y) = x === y

instance Traceable l => Eq (TraceLit l s) where
  (TraceLit x) == (TraceLit y) = compareLit x y == EQ

instance Traceable l => Ord (TraceLit l s) where
  compare (TraceLit x) (TraceLit y) = compareLit x y


class TraceOp l g a where
  traceOp :: (Traceable l, IsAIG l g) => TraceGraph l g s -> String -> a -> a

class TraceOutput l g x where
  traceOutput :: (Traceable l, IsAIG l g) => TraceGraph l g s -> x -> String

instance TraceOp l g b => TraceOp l g (Int -> b) where
  traceOp g msg f i = traceOp g (msg++" "++show i) (f i)

instance TraceOp l g b => TraceOp l g (TraceLit l s -> b) where
  traceOp g msg f i = traceOp g (msg++" "++showLit (unTraceLit i)) (f i)

instance TraceOp l g b => TraceOp l g ([TraceLit l s] -> b) where
  traceOp g msg f is = traceOp g (msg++" ["++unwords (map (showLit . unTraceLit) is)++"]") (f is)

instance TraceOp l g b => TraceOp l g (FilePath -> b) where
  traceOp g msg f i = traceOp g (msg++" "++i) (f i)

instance TraceOutput l g x => TraceOp l g (IO x) where
  traceOp g msg f = do
      mh <- readIORef (tActive g)
      case mh of
        Nothing -> f
        Just h -> do
            hPutStr h msg
            hFlush h
            x <- f
            hPutStrLn h $ " result "++traceOutput g x
            hFlush h
            return x

instance TraceOutput l g a => TraceOutput l g [a] where
  traceOutput g xs =
     "[" ++ concat (intersperse ", " (map (traceOutput g) xs)) ++ "]"

instance TraceOutput l g (TraceLit l s) where
  traceOutput _g (TraceLit l) = showLit l

instance TraceOutput l g Int where
  traceOutput _g i = show i

instance TraceOutput l g () where
  traceOutput _g () = "()"

instance TraceOutput l g SatResult where
  traceOutput _g r = show r

instance TraceOutput l g VerifyResult where
  traceOutput _g r = show r

instance TraceOutput l g x => TraceOutput l g (LitView x) where
  traceOutput g (And x y)    = "And ("++traceOutput g x++") ("++traceOutput g y++")"
  traceOutput g (NotAnd x y) = "NotAnd ("++traceOutput g x++") ("++traceOutput g y++")"
  traceOutput _ (Input i)    = "Input "++show i
  traceOutput _ (NotInput i) = "NotInput "++show i
  traceOutput _ TrueLit      = "TrueLit"
  traceOutput _ FalseLit     = "FalseLit"

withNewGraphTracing :: (IsAIG l g, Traceable l)
                    => Proxy l g
                    -> FilePath
                    -> (forall s. TraceGraph l g s -> IO a)
                    -> IO a
withNewGraphTracing _ fp f = withNewGraph undefined $ \g -> withTracing g fp (f g)

instance (IsAIG l g, Traceable l) => IsAIG (TraceLit l) (TraceGraph l g) where
  withNewGraph _ f = withNewGraph undefined $ \g -> do
                         r <- newIORef Nothing
                         f (TraceGraph g r)

  aigerNetwork _ fp = do
          (Network g outs) <- aigerNetwork undefined fp
          r <- newIORef Nothing
          return (Network (TraceGraph g r) (map TraceLit outs))

  trueLit g = TraceLit $ trueLit (tGraph g)
  falseLit g = TraceLit $ falseLit (tGraph g)

  newInput g = traceOp g "NewInput" $ fmap TraceLit $ newInput (tGraph g)

  and g = traceOp g "and" $ \(TraceLit x) (TraceLit y) -> fmap TraceLit $ and (tGraph g) x y
  or g = traceOp g "or" $ \(TraceLit x) (TraceLit y) -> fmap TraceLit $ or (tGraph g) x y
  implies g = traceOp g "implies" $ \(TraceLit x) (TraceLit y) -> fmap TraceLit $ implies (tGraph g) x y
  eq g = traceOp g "eq" $ \(TraceLit x) (TraceLit y) -> fmap TraceLit $ eq (tGraph g) x y
  xor g = traceOp g "xor" $ \(TraceLit x) (TraceLit y) -> fmap TraceLit $  xor (tGraph g) x y
  mux g = traceOp g "mux" $ \(TraceLit x) (TraceLit y) (TraceLit z) -> fmap TraceLit $ mux (tGraph g) x y z

  inputCount g = traceOp g "inputCount" $ inputCount (tGraph g)

  getInput g = traceOp g "getInput" $ \i -> fmap TraceLit $ getInput (tGraph g) i

  writeAiger fp0 (Network g outs0) =
       (traceOp g "writeAiger" $ \fp outs -> writeAiger fp (Network (tGraph g) (map unTraceLit outs))) fp0 outs0

  writeAigerWithLatches fp0 (Network g outs0) nl0 =
       (traceOp g "writeAigerWithLatches" $ \fp outs nl -> writeAigerWithLatches fp (Network (tGraph g) (map unTraceLit outs)) nl) fp0 outs0 nl0

  writeCNF g =
       traceOp g "writeCNF" $ \out fp -> writeCNF (tGraph g) (unTraceLit out) fp

  checkSat g = traceOp g "checkSat" $ \(TraceLit x) -> checkSat (tGraph g) x

  cec (Network g1 outs1') (Network g2 outs2') =
      (traceOp g1 "cec" $ \outs1 outs2 ->
        cec (Network (tGraph g1) (map unTraceLit outs1))
            (Network (tGraph g2) (map unTraceLit outs2)))
            outs1' outs2'

  evaluator g ins =
        do mh <- readIORef (tActive g)
           maybe (return ()) (\h -> (hPutStrLn h $ unwords ["building evaluator",show ins]) >> hFlush h) mh
           let traceIO l x h = (hPutStrLn h $ unwords ["evaluator call",show ins,showLit l,show x]) >> hFlush h
           let trace l x =
                  case mh of
                     Nothing -> x
                     Just h  -> seq (unsafePerformIO (traceIO l x h)) x
           ev <- evaluator (tGraph g) ins
           return (\(TraceLit l) -> trace l $ ev l)

  litView g = traceOp g "litView" $ \(TraceLit l) -> fmap (fmap TraceLit) (litView (tGraph g) l)

  abstractEvaluateAIG g f =
        do mh <- readIORef (tActive g)
           maybe (return ()) (\h -> (hPutStrLn h $ unwords ["building abstract evaluator"]) >> hFlush h) mh
           let traceIO l h = (hPutStrLn h $ unwords ["abstract evaluator call",showLit l]) >> hFlush h
           let trace l x =
                  case mh of
                     Nothing -> return x
                     Just h  -> traceIO l h >> return x
           ev <- abstractEvaluateAIG (tGraph g) f
           return (\(TraceLit l) -> trace l =<< ev l)
