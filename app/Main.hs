module Main (main) where

import Ziku.Stub (version)

import Data.Text.IO qualified as T

main :: IO ()
main = T.putStrLn ("ziku " <> version)
