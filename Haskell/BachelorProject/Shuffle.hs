module Shuffle where
    
import System.Random
import Data.Array.IO
import Control.Monad

import Data.Array.ST
import Control.Monad.ST
import Data.STRef

-- | Randomly shuffle a list
--   /O(N)/
-- code gehaald van https://wiki.haskell.org/Random_shuffle

-- shuffles the list so that every element is in a random order
shuffle :: [a] -> IO [a]
shuffle xs = do
        ar <- newArray n xs
        forM [1..n] $ \i -> do
            j <- randomRIO (i,n)
            vi <- readArray ar i
            vj <- readArray ar j
            writeArray ar j vi
            return vj
  where
    n = length xs
    newArray :: Int -> [a] -> IO (IOArray Int a)
    newArray n xs =  newListArray (1,n) xs
 
-- randomly divide an integer over n elements 
splitNumber :: Int -> Int -> IO [Int]

splitNumber n 0 = do
    return []
    
splitNumber n 1 = do 
    return [n]

splitNumber n size = do
    n1 <- randomRIO (0,n)
    rest <- splitNumber (n-n1) (size-1)
    return (n1 : rest)
    


