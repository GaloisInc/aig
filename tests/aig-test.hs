module Main (main) where

import Test.Tasty
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML

import Tests.FileIO
import Tests.Operations

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

main :: IO ()
main = do
  defaultMainWithIngredients ingrs tests

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   ]
   ++
   defaultIngredients


tests :: TestTree
tests =
    testGroup "AIG"
    [ testGroup "Bitvector operations" $ op_tests
    , testGroup "File I/O" $ io_tests
    ]
