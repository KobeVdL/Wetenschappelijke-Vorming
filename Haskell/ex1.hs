--import Data.List

elemt :: (Eq a) => a -> [a] -> Bool 

elemt a [] = False

elemt a list 
    | (a == (head list)) = True
    | otherwise = elemt a (tail list)
    
nub :: (Eq a) => [a] -> [a]

nub [] = []

nub (x:xs) 
    | elemt x xs = nub xs
    | otherwise = x : nub xs
    
isAsc :: [Int] -> Bool

isAsc (x:xs)
    | xs == [] = True
    | (x <= head xs) = isAsc xs
    | otherwise = False
    
main = let 
    k = isAsc [1,2,3,4,3]
    in
    putStrLn (show k)