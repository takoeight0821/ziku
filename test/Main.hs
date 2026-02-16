module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import Ziku.Stub (version)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Ziku"
    [ testCase "version" $
        version @?= "0.1.0.0"
    ]
