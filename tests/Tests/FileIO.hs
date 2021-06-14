module Tests.FileIO (io_tests) where

import qualified Data.ByteString as BS
import System.Directory
import Test.Tasty
import Test.Tasty.HUnit

import Data.AIG.CompactGraph
import Data.AIG.Interface
import Data.AIG.Operations

io_tests :: [TestTree]
io_tests =
  [ testCase "read_write" $
      do g <- newCompactGraph
         x <- newBV g 8
         o <- mul g x x
         let file1 = "mul1.aig"
             file2 = "mul2.aig"
         writeAiger file1 (Network g (bvToList o))
         n <- aigerNetwork compactProxy file1
         writeAiger file2 n
         bs1 <- BS.readFile file1
         bs2 <- BS.readFile file2
         removeFile file1
         removeFile file2
         bs1 @?= bs2
  ]
