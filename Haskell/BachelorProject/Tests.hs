module Tests where
    
import Project
import BasicProlog
import Shuffle
import TopDown
import Constructors
import PropertyChecking
import System.Environment
import NaiveGenerator
import TopDownBackTrack
import Shrinking
import BottomUp
import BasicStep

import Data.Time
import System.TimeIt
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import Control.Monad.Trans.Maybe
import Data.Time.Clock.POSIX
import Distribution.Simple.SrcDist




import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


-- TODO i think timing function is not optimal



--Test de tijd met :set +s in ghci

-- Tests the bottomUp program with the parentProgram
test7 = print (semiNaiveBottomUp parentProgram 3 Map.empty Map.empty) 
    

-- Tests the bottomUp program with the evenProgram
test8 = print (semiNaiveBottomUp evenProgram 8 Map.empty Map.empty)
    
 
-- Tests if the add to correct Scheme works correctly
test4 = print (addToCorrectScheme p3 m3)
        where
        t1 = MkTerm "a" 0 []
        t2 = MkTerm "c" 0 []
        t3 = MkTerm "b" 1 [t1] 
        p1 = MkPredicate "a" 1 [t1]
        p2 = MkPredicate "b" 1 [t2]
        p3 = MkPredicate "c" 1 [t3]
        m =  Map.empty
        m1 = Map.insert "a" Set.empty m 
        m2 = Map.insert "b" Set.empty m1
        m3 = Map.insert "c" Set.empty m2

-- Tests if the findNewPred works correctly   
test6 = print (show (findNewPred r Map.empty m1))
    where 
    t1 = MkTerm "a" 0 []
    t2 = MkPredicate "b" 1 [Variable "x"]
    t3 = MkPredicate "c" 1 [Variable "x"] 
    r = Rule t3 [t2]
    m = Map.empty
    m1 = Map.insert "b" (Set.fromList [[t1]]) m 
   
   
-- Tests if the find binder works correctly   
findBinderTest = findBinder (valuesOfPred (hasType [x,nat])) [zero,nat]
    where 
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2
   
-- Tests if the bindValue works correctly
binderPredTest = bindValue (Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]) binder  
    where 
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2
    Just binder= findBinder (hasType [y]) (hasType [leq [x,y]]) 


-- Tests the topDownAlgorithm    
topDownAlgorithmTest :: IO ()

topDownAlgorithmTest = do
        d <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 100 (serperateConstant aritProgramUpgraded) depthFirst 0
        putStrLn (show d )
        return ()
        
   

-- Tests the evaluation of a term   
evalTest :: IO() 

evalTest = do 
    d <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 5 (serperateConstant aritProgramUpgraded) depthFirst 0
    case d of
        Just ([MkPredicate "hasType" 2 [val,typeOfVal]])-> do
            putStrLn (show (MkPredicate "hasType" 2 [val,typeOfVal]))
            putStrLn ""
            putStrLn (show (eval val normalStep))
        Nothing -> return ()
        


-- Tests if the changeVariable works correctly        
changeVariableTest :: IO ()

changeVariableTest = do 
    putStrLn (show (changeVariable z replacingTerm pred))
    where
    emptyArray = MkTerm "[]" 0 [] 
    array = MkTerm "array" 1 
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    addArray = MkTerm ":" 2
    append = MkTerm "++" 2
    hasType = MkPredicate "hasType" 2 
    pred = hasType [y,array [z]]
    replacingTerm = array [z]


-- Tests the backtrack algorithm
topDownBacktrackAlgorithmTest :: IO ()

topDownBacktrackAlgorithmTest = do
        d <- topDownBacktrackAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 2000 (serperateConstant aritProgram) depthFirst 0 0
        putStrLn (show d )
        return ()
        

-- Tests the shrinking algorithm
shrinkingTest:: IO() 

shrinkingTest = do -- FOUT mss in property Just hasType(succ(succ(succ(succ(Zero)))),nat) is niet aan property voldaan
        maybeTerm <- topDownPropertyChecking 10 100 (checkProperty step3) aritProgram
        putStrLn (show maybeTerm)
        let shrinkedTerm = do
            term <- maybeTerm
            Just (shrinkAlgorithm term (checkProperty step3) aritProgram)
        putStrLn (show shrinkedTerm)
            
            
-- tests the checkProperty method        
checkPropertyTest:: IO()

checkPropertyTest = do
        putStrLn (show (checkProperty step3 (hasType [zero,nat])))
        
        where
        zero = MkTerm "Zero" 0 []
        nat = MkTerm "nat" 0 []
        hasType = MkPredicate "hasType" 2 
        
        
 
{- 
Calculates the time needed to check the property of the program for a TopDown algorithm
-}
timeUsedPropertyTopDown ::Int -> Int -> Program -> (Predicate -> Bool) -> IO Double
    
timeUsedPropertyTopDown times size program propCheck = do 
    timeUsedProperty method
    where
    method = topDownPropertyChecking size times propCheck program

    
--Calculates the time needed to check the property of the program for a BottomUp algorithm
timeUsedPropertyBottomUp :: Int -> Program -> (Predicate -> Bool) -> IO Double
    
timeUsedPropertyBottomUp size program propCheck  = do
    --if (size > 2) then 
     --   timeUsedProperty method2 -- BottomUp kan niet groter dan 3 worden want is dan te groot
   -- else
        timeUsedProperty method
    where
    method = fastBottomUpProperty program propCheck size Map.empty Map.empty
    method2 = fastBottomUpProperty program propCheck 2 Map.empty Map.empty

-- Calculates the time needed to check the property of the program for a Naïve algorithm
timeUsedPropertyNaive :: Int -> Int -> Program ->(Predicate -> Bool) -> IO Double   
    
timeUsedPropertyNaive times size program propCheck  = do 
    timeUsedProperty method
    where
    method = naiveTryUntillPropertyFalse times size propCheck program
    
    
--Calculates the time needed to check the property of the program for a TopDownBackTrack algorithm
timeUsedPropertyTopDownBacktrack :: Int -> Int-> Int -> Program -> (Predicate -> Bool)-> IO Double 
 
timeUsedPropertyTopDownBacktrack  times size forget program propCheck  = do 
    timeUsedProperty method
    where
    method = topDownBacktrackPropertyChecking size times forget propCheck program  
 
    
-- calculates the time needed to find that the property is false    
timeUsedProperty :: (IO (Maybe Predicate)) -> IO Double
    
timeUsedProperty method =
    do 
    (time,maybeTerm) <- timeItT method
    --time1 <- getCurrentTime -- getPOSIXTime uncomment this if you are using windows
    --maybeTerm <- method
    --time2 <- getCurrentTime  -- getPOSIXTime uncomment this if you are using windows
    case maybeTerm of
        Just term -> return time --return (posixToInt (time2-time1)) -- heeft het juiste resultaat gevonden
        Nothing -> return (1/0) -- returns infinity Denkt dat de property juist is dus zet tijd op oneindig
    

    
    
-- returns the result into a csvString where n is the number of times you try the test
resultsToString :: (Show a) => Int -> [IO a] -> IO String

resultsToString 0 _ = return ""

resultsToString n methodsToPerform =do
    result <- methodsToCsv (methodsToPerform)
    resStr <- resultsToString (n-1) methodsToPerform
    return (result ++ resStr)
    
    
--  turn the results of the methods into a Csv (one array)
methodsToCsv :: (Show a) =>  [IO a] -> IO String

methodsToCsv [] = return "\n"

methodsToCsv [x] = do
    result <- x
    return (show result ++ "\n")

methodsToCsv (x:xs)= do
    result <- x
    restResult <- methodsToCsv xs
    return (show result ++ ";" ++ restResult)
    
    
-- Write the output of the methods to a file, n is the times you try the method, the next is the list of methods
-- that have to performed , lastly is the fileName where the result needs to be written to.
timeResults ::(Show a) => Int -> [IO a] -> String -> IO()

timeResults n methodsToPerform output= do
    s <- resultsToString n methodsToPerform
    writeFile output s

-- Test the timing method for the top Down Algorithm
calResults1 :: IO()

calResults1 = timeResults 20 methodsToPerform "Output/output.csv"
    where
    ts = (\x y -> timeUsedPropertyTopDown x y aritProgram (checkProperty normalStep))
    methodsToPerform = [ts 5 20 , ts 10 20 ,ts 20 20, ts 50 20,ts 100 20 , ts 500 20 ,ts 1000 20]

-- Test the timing method for the top Down Algorithm where the simplification algorithm differ
calResults2 :: IO()

calResults2 = timeResults 20 methodsToPerform "Output/output2.csv"
    where
    ts = (\x y -> timeUsedPropertyTopDown 20 20 x y)
    methodsToPerform = [ts aritProgram (checkProperty normalStep) , ts aritProgram2 (checkProperty normalStep) ,ts aritProgram3 (checkProperty normalStep), ts aritProgram (checkProperty step1), ts aritProgram (checkProperty step2),  ts aritProgram (checkProperty step3) ]


-- Test the timing method for the BottomUp Algorithm
calResults3 :: Int -> (Predicate -> Bool) -> IO()

calResults3 size propCheck = timeResults 1 methodsToPerform ("Output2/BottomUp/Step4/output.4."++ show size ++".csv")
    where
    ts = (\x y -> timeUsedPropertyBottomUp size x y)
    methodsToPerform = [ts aritProgramUpgraded (propCheck) ]
            
   
--  Loops over the sizes for calculating the results
calResultLoopSize3:: Int -> (Predicate -> Bool) -> IO()

calResultLoopSize3  (0) propCheck = return () -- terms of size 0 always fails 

calResultLoopSize3  max propCheck = do
    calResultLoopSize3 (max-1) propCheck
    calResults3 max propCheck
   

 
-- The correct Method to calculate  the timing for the 4 used algorithms 
calResultsFinal :: Int -> (Predicate -> Bool) -> IO()

calResultsFinal size propCheck = timeResults 20 methodsToPerform ("Output2/Step1/outputFinal.1."++ (show size) ++ ".csv")
    where  
    tsNaive = (\x -> timeUsedPropertyNaive 10000 size x)
    tsBottom = (\x y -> timeUsedPropertyBottomUp size x y)
    tsTop = (\x y -> timeUsedPropertyTopDown 10000 size x y)
    tsTopBacktrack = (\x y ->  timeUsedPropertyTopDownBacktrack  10000 size 0 x y)
    program = aritProgramUpgraded
    methodsToPerform = [tsNaive program propCheck, tsBottom program propCheck, tsTop program propCheck ,tsTopBacktrack program propCheck]
    


--  Loops over the sizes for calculating the results
calResultLoopSize:: Int -> (Predicate -> Bool) -> IO()

calResultLoopSize  (0) propCheck = return () -- terms of size 0 always fails 

calResultLoopSize  max propCheck = do
    calResultLoopSize (max-1) propCheck
    calResultsFinal max propCheck
 

-- Calculates the percentage of the the number of naive algorithm tries that failed to find the 
--   error on the total number of tries
naivePercentage:: Int -> Int -> Program-> IO Float 

naivePercentage size amount program= do
    numberOfTrue <- naivePercentageHelper size amount program
    return (fromIntegral numberOfTrue/ fromIntegral amount)
            
            
-- helper of naivePercentage
naivePercentageHelper:: Int -> Int -> Program-> IO Int 

naivePercentageHelper size 0 program = return 0

naivePercentageHelper size amount program= do
    gen <- naiveGenerateElem size program
    let precond1 = precond gen program
    if precond1 then do
        number<-naivePercentageHelper size (amount-1) program
        return (1 + number)
    else
        naivePercentageHelper size (amount-1) program
   

-- Write the percentage to the file   
percentageWrite :: Int-> Program-> IO()

percentageWrite max program= do 
    result <-percentageWriteHelper max 0 program
    writeFile "Output2/percentage.csv" result
    
-- helper of percentageWrite
percentageWriteHelper :: Int -> Int -> Program -> IO String

percentageWriteHelper max current program
    | current <= max =do
        per <-naivePercentage current 10000 program
        other <-  percentageWriteHelper max (current + 1) program
        return (show current ++ ";" ++ show per ++ "\n" ++ other)
    |otherwise = return ""

            
-- test for bottomUp Algorithm 
ariTest :: Scheme

ariTest = semiNaiveBottomUp aritProgramUpgraded 2 Map.empty Map.empty

-- test for bottomUp Algorithm
ariTest2 :: Scheme

ariTest2 = semiNaiveBottomUp aritProgram2 3 Map.empty Map.empty

-- test for bottomUp Algorithm
ariTest3 :: Scheme

ariTest3 = semiNaiveBottomUp aritProgram3 3 Map.empty Map.empty -- Bij maar 2 keer geeft wel true terug omdat de formule nergens in gebruikt wordt
