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
        d <- topDownPred (MkPredicate "hasType" 2 [Variable "X",Variable "Z2"])  (serperateConstant aritProgram) 120
        -- topDownPred (MkPredicate "hasType" 2 [ifThenElse [Variable "X",Variable "Y",Variable "Z"],Variable "Z2"])  (serperateConstant aritProgram) 0
        putStrLn (show d )
        return ()
    
    
topDownAlgorithmTest' :: IO ()

topDownAlgorithmTest' = do
        d <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 10 (serperateConstant aritProgram) depthFirst 0
        -- topDownPred (MkPredicate "hasType" 2 [ifThenElse [Variable "X",Variable "Y",Variable "Z"],Variable "Z2"])  (serperateConstant aritProgram) 0
        putStrLn (show d )
        return ()
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

 
topDownPropertyChecking :: Int -> Program -> IO ()

topDownPropertyChecking 0 program = do
    putStrLn "property is wrsch waar"


topDownPropertyChecking n program = do
    maybePred <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) 5 (serperateConstant program) depthFirst 0
    case maybePred of
        Just pred-> do
            let test = checkProperty (head pred) step
            if test == False then do
                putStrLn ("Test is " ++ (show test) ++ " with value " ++ (show pred))
            else do
                topDownPropertyChecking (n-1) program
        Nothing -> do 
            putStrLn "Geen regels toepasbaar"
 

timeUsedPropertyTopDown :: IO POSIXTime
    
timeUsedPropertyTopDown = do 
    time1 <- getPOSIXTime
    topDownPropertyChecking 100 aritProgram-- checkPropertyScheme (semiNaiveBottomUp aritProgram 100 Map.empty Map.empty)
    time2 <- getPOSIXTime
    return (time2-time1)

timeUsedPropertyBottomUp :: IO POSIXTime
    
timeUsedPropertyBottomUp = do 
    time1 <- getPOSIXTime
    putStrLn (show (fastBottomUpProperty aritProgram 3 Map.empty Map.empty))-- checkPropertyScheme (semiNaiveBottomUp aritProgram 100 Map.empty Map.empty)
    time2 <- getPOSIXTime
    return (time2-time1)

            
    
ariTest :: Scheme

ariTest = semiNaiveBottomUp aritProgram 3 Map.empty Map.empty


ariTest2 :: Scheme

ariTest2 = semiNaiveBottomUp aritProgram2 3 Map.empty Map.empty


ariTest3 :: Scheme

ariTest3 = semiNaiveBottomUp aritProgram3 3 Map.empty Map.empty -- Bij maar 2 keer geeft wel true terug omdat de formule nergens in gebruikt wordt
