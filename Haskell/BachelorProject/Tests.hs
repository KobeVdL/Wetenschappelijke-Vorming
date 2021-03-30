module Tests where
    
import Project
import BasicProlog
import Shuffle
import TopDown
import Constructors
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import Control.Monad.Trans.Maybe
import Data.Time.Clock.POSIX
import PropertyChecking
import System.Environment
import NaiveGenerator
import TopDownBackTrack
import Shrinking



import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

--Test de tijd met :set +s in ghci


test7 = print (semiNaiveBottomUp parentProgram 3 Map.empty Map.empty) --test met even getallen implementeren
    

    
test8 = print (semiNaiveBottomUp evenProgram 8 Map.empty Map.empty)
    
 

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

         
test6 = print (show (findNewPred r Map.empty m1))
    where 
    t1 = MkTerm "a" 0 []
    t2 = MkPredicate "b" 1 [Variable "x"]
    t3 = MkPredicate "c" 1 [Variable "x"] 
    r = Rule t3 [t2]
    m = Map.empty
    m1 = Map.insert "b" (Set.fromList [[t1]]) m 
   
findBinderTest = findBinderArguments (valuesOfPred (hasType [x,nat])) [zero,nat]
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
    --Just binder= findBinderPred (hasType [y]) (hasType [leq [x,y]]) 
   

binderPredTest = bindRule (Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]) binder  
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
    Just binder= findBinderPred (hasType [y]) (hasType [leq [x,y]]) 

-- geeft steeds hetzelfde resultaat terug
--bottomUpTest =  topDownPred (MkPredicate "hasType" 2 [Variable "X",Variable "Z2"])  aritProgram 8
    
    
topDownAlgorithmTest :: IO ()

topDownAlgorithmTest = do
        d <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 100 (serperateConstant aritProgramUpgraded) depthFirst 0
        putStrLn (show d )
        return ()
        
        
evalTest :: IO() 

evalTest = do 
    d <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 100 (serperateConstant aritProgramUpgraded) depthFirst 0
    case d of
        Just ([MkPredicate "hasType" 2 [val,typeOfVal]])-> do
            putStrLn (show val)
            putStrLn ""
            putStrLn (show (eval val step))
        Nothing -> return ()
        
        
changeVariableTest :: IO ()

changeVariableTest = do 
    putStrLn (show (changeVariableInPredicate pred z replacingTerm))
    where
    emptyArray = MkTerm "[]" 0 [] --[hasType(:(ifThenElse(True,[],[]),ifThenElse(ifThenElse(False,False,False),[],[])),array(array(array(array(array(X))))))]
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


topDownBacktrackAlgorithmTest :: IO ()

topDownBacktrackAlgorithmTest = do
        d <- topDownBacktrackAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 2000 (serperateConstant aritProgram) depthFirst 0 0
        putStrLn (show d )
        return ()
        
        
shrinkingTest:: IO() 

shrinkingTest = do -- FOUT mss in property Just hasType(succ(succ(succ(succ(Zero)))),nat) is niet aan property voldaan
        maybeTerm <- topDownPropertyChecking 10 100 (checkProperty step1) aritProgram
        putStrLn (show maybeTerm)
        let shrinkedTerm = do
            term <- maybeTerm
            Just (shrinkAlgorithm term (checkProperty step1) aritProgram)
        putStrLn (show shrinkedTerm)
            
randomTest:: IO()

randomTest = do
        putStrLn (show (checkProperty step2 (hasType [zero,nat])))
        
        where
        zero = MkTerm "Zero" 0 []
        nat = MkTerm "nat" 0 []
        hasType = MkPredicate "hasType" 2 
        
        
 
{- 
Calculates the time needed to check the property of the program
-}
timeUsedPropertyTopDown ::Int -> Int -> Program -> (Predicate -> Bool) -> IO Int
    
timeUsedPropertyTopDown times size program propCheck = do 
    timeUsedProperty method
    where
    method = topDownPropertyChecking size times propCheck program

    
--Calculates the time needed to check the property of the program
timeUsedPropertyBottomUp :: Int -> Program -> (Predicate -> Bool) -> IO Int
    
timeUsedPropertyBottomUp size program propCheck  = do
    --if (size > 2) then 
     --   timeUsedProperty method2 -- BottomUp kan niet groter dan 3 worden want is dan te groot
   -- else
        timeUsedProperty method
    where
    method = fastBottomUpProperty program propCheck size Map.empty Map.empty
    method2 = fastBottomUpProperty program propCheck 2 Map.empty Map.empty

    
timeUsedPropertyNaive :: Int -> Int -> (Predicate -> Bool) -> IO Int    
    
timeUsedPropertyNaive times size propCheck  = do 
    timeUsedProperty method
    where
    method = naiveTryUntillPropertyFalse times size propCheck
    
timeUsedPropertyTopDownBacktrack :: Int -> Int-> Int -> Program -> (Predicate -> Bool)-> IO Int 
 
timeUsedPropertyTopDownBacktrack  times size forget program propCheck  = do 
    timeUsedProperty method
    where
    method = topDownBacktrackPropertyChecking size times forget propCheck program  
 
    
-- calculates the time needed to find that the property is false    
timeUsedProperty :: (IO (Maybe Predicate)) -> IO Int
    
timeUsedProperty method =
    do 
    time1 <- getPOSIXTime
    maybeTerm <- method
    time2 <- getPOSIXTime
    case maybeTerm of
        Just term -> return (posixToInt (time2-time1)) -- heeft het juiste resultaat gevonden
        Nothing -> return (maxBound) -- Denkt dat de property juist is dus zet tijd op oneindig
    




-- change the  posix value to an integer value
-- time in 10-e5 seconds
posixToInt :: POSIXTime ->Int

posixToInt time = floor(toRational(time * 10000)) 
    
resultsToString :: (Show a) => Int -> [IO a] -> IO String

resultsToString 0 _ = return ""

resultsToString n methodsToPerform =do
    result <- methodsToCsv (methodsToPerform)
    resStr <- resultsToString (n-1) methodsToPerform
    return (result ++ resStr)
    
    

methodsToCsv :: (Show a) =>  [IO a] -> IO String

methodsToCsv [] = return "\n"

methodsToCsv [x] = do
    result <- x
    return (show result ++ "\n")

methodsToCsv (x:xs)= do
    result <- x
    restResult <- methodsToCsv xs
    return (show result ++ ";" ++ restResult)
    
    

timeResults ::(Show a) => Int -> [IO a] -> String -> IO()

timeResults n methodsToPerform output= do
    s <- resultsToString n methodsToPerform
    writeFile output s

calResults1 :: IO()

calResults1 = timeResults 20 methodsToPerform "Output/output.csv"
    where
    ts = (\x y -> timeUsedPropertyTopDown x y aritProgram (checkProperty step))
    methodsToPerform = [ts 5 20 , ts 10 20 ,ts 20 20, ts 50 20,ts 100 20 , ts 500 20 ,ts 1000 20]

calResults2 :: IO()

calResults2 = timeResults 20 methodsToPerform "Output/output2.csv"
    where
    ts = (\x y -> timeUsedPropertyTopDown 20 20 x y)
    methodsToPerform = [ts aritProgram (checkProperty step) , ts aritProgram2 (checkProperty step) ,ts aritProgram3 (checkProperty step), ts aritProgram (checkProperty step1), ts aritProgram (checkProperty step2),  ts aritProgram (checkProperty step3) ]

calResults3 :: IO()

calResults3 = timeResults 20 methodsToPerform "Output/output3.csv"
    where
    ts = (\x y -> timeUsedPropertyBottomUp 3 x y)
    methodsToPerform = [ts aritProgram (checkProperty step) , ts aritProgram2 (checkProperty step) ,ts aritProgram3 (checkProperty step), ts aritProgram (checkProperty step1), ts aritProgram (checkProperty step2),  ts aritProgram (checkProperty step3) ]
            
 
calResultsFinal :: Int -> (Predicate -> Bool) -> IO()

calResultsFinal size propCheck = timeResults 20 methodsToPerform ("Output/outputFinal.6."++ (show size) ++ ".csv")
    where  
    tsNaive = (\x -> timeUsedPropertyNaive 10000 size x)
    tsBottom = (\x y -> timeUsedPropertyBottomUp size x y)
    tsTop = (\x y -> timeUsedPropertyTopDown 1000 size x y)
    tsTopBacktrack = (\x y ->  timeUsedPropertyTopDownBacktrack  1000 size 0 x y)
    methodsToPerform = [tsNaive propCheck ,tsBottom aritProgram propCheck , tsTop aritProgram propCheck ,tsTopBacktrack aritProgram propCheck]

calResultLoopSize:: Int->(Predicate -> Bool) -> IO()

calResultLoopSize  (-1) propCheck = return ()

calResultLoopSize  max propCheck = do
    calResultLoopSize (max-1) propCheck
    calResultsFinal max propCheck
 
            
naivePercentage:: Int -> Int -> IO Float 

naivePercentage size amount = do
    numberOfTrue <- naivePercentageHelper size amount
    return (fromIntegral numberOfTrue/ fromIntegral amount)
            
            
            
naivePercentageHelper:: Int -> Int -> IO Int 

naivePercentageHelper size 0 = return 0

naivePercentageHelper size amount= do
    gen <- naiveGenerateElem size
    let precond1 = precond gen
    if precond1 then do
        number<-naivePercentageHelper size (amount-1)
        return (1 + number)
    else
        naivePercentageHelper size (amount-1)
        
percentageWrite :: Int-> IO()

percentageWrite max = do 
    result <-percentageWriteHelper max 0
    writeFile "Output/percentage.csv" result
    

percentageWriteHelper :: Int -> Int -> IO String

percentageWriteHelper max current 
    | current <= max =do
        per <-naivePercentage current 10000
        other <-  percentageWriteHelper max (current + 1)
        return (show current ++ ";" ++ show per ++ "\n" ++ other)
    |otherwise = return ""

            
    
ariTest :: Scheme

ariTest = semiNaiveBottomUp aritProgramUpgraded 2 Map.empty Map.empty


ariTest2 :: Scheme

ariTest2 = semiNaiveBottomUp aritProgram2 3 Map.empty Map.empty


ariTest3 :: Scheme

ariTest3 = semiNaiveBottomUp aritProgram3 3 Map.empty Map.empty -- Bij maar 2 keer geeft wel true terug omdat de formule nergens in gebruikt wordt
