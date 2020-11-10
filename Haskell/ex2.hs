rev :: [a] -> [a]

rev = foldr (@@) []

(@@) :: a -> [a] -> [a]

(@@) x y =  y ++ [x]

prefixes :: [a] -> [[a]]

prefixes = foldr (\x acc  -> [x] : (map((:) x) acc)) []

lagrange ::  [(Float,Float)] -> Float -> Float

lagrange list value = (foldr (\(x,y) acc -> acc + y * (lagrangeterm((map (\(x,y) -> x) list)) x value)) 0) list 

lagrangeterm :: [Float] -> Float -> Float -> Float

lagrangeterm list xj value = foldl (
    \acc arg -> 
    if xj == arg then
        acc 
    else 
        acc * ((value - arg) / (xj - arg))
    ) 1 list

randomfunction ::Floating a=> [a]-> a

randomfunction = foldr (+) 0.0

data Trie = Leaf a | Node a [Trie a]

foldtrie :: (b -> a -> b) -> b -> Trie a -> b

foldtrie func acc (Leaf x) = func acc x

foldtrie func acc (Node a listOfTrees) = foldl f' (func acc a) listOfTrees -- func acc a is de nieuwe acc
    where 
    f' acc t = foldtree f acc t

main = let  
    k =  randomfunction [1,2,3,4]
    --k = lagrangeterm (map (\(x,y) -> x) [(1,2),(3,2),(4,5)]) 3 2 
    in
    putStrLn (show k)
    