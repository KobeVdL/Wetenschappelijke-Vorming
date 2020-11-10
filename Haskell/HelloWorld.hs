fac :: Integer -> Integer 

main :: IO ()

fac n 
    | n <= 1 = 1
    | otherwise = n * fac(n-1)

main = let 
    a = fac 8
    in
    putStrLn (show a)