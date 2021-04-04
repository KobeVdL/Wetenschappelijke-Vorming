module TopDownBackTrack where

import BasicProlog
import TopDown
import Shuffle

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import System.Random
import Control.Monad.Trans.Maybe


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- creates a predicate with a top-down backtrack approuch, it makes random choices in the syntax tree to generate a program
-- Returns Nothing if no programs of size n are possible
-- The top-down approuch work with a worklist that has to be empty to stop
-- on top of that in the n'th node it instead choose every possible clause it can and gives back all predicates
-- it found this way   
topDownBacktrackAlgorithm:: [Predicate] -> Int -> ([Clause],[Clause]) -> ([a] -> [a] -> [a]) -> Int -> Int -> IO ([[Predicate]])

topDownBacktrackAlgorithm startPred n rules func bStep index =do
    allBinders <- topDownLoopBacktrack (zip startPred (repeat n)) rules func bStep index
    case allBinders of
        [] -> return []
        listOfListBinders->do
            return (foldr (\x acc -> (applyBinderList x):acc) [] listOfListBinders) -- give binded result back
    where
        applyBinderList = foldl (\acc x -> bindValue acc x) startPred -- apply the binders to the given predicate



-- similar to the goTopDown but instead go over all clauses and returns a list of list of binders
allGoTopDown:: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a])->([Clause],[Clause]) ->Int-> IO ([[Binder]])

-- If all facts are evaluated give empty list back (only if size is 0
allGoTopDown (w,n) ws (_,[]) funct totalProgram index = do 
    return ([])
    
-- If all rules are evaluated give empty list back
allGoTopDown (w,n) ws ([],_) funct totalProgram index = do 
    return ([] )   

-- Call a goTopDown for each rule to achieve all possible combinations with that step
allGoTopDown (w,n) ws rs funct totalProgram index = do
    maybeResult<-goTopDownR (w,n) ws rs funct totalProgram index --(binders,rulesRemaining)
    case maybeResult of
        Just (binders,rulesRemaining) ->do
            listBinders <- allGoTopDown (w,n) ws rulesRemaining funct totalProgram index
            return (binders:listBinders)
        Nothing -> return [] -- Case it is nothing return empty List bec no other bindings are found
    


-- Do a topDown algorithm but if found an answer also returns the rules evaluated
goTopDownR:: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a])->([Clause],[Clause]) ->Int-> IO (Maybe ([Binder],([Clause],[Clause])))

goTopDownR (w,n) ws rs funct totalProgram index =do 
    r <- stepRule (w,n) ws rs index
    case r of 
        Nothing->  return Nothing
        Just(ws',binder,rs',newIndex)-> 
            do 
            --putStrLn (show ws')
            dividedPred' <- splitNumber (n-1) (length(ws'))
            dividedPred <- shuffle dividedPred'
            p <- topDownLoop ((depthFirst) (zip ws' dividedPred) (applyBinderSizeList ws binder)) totalProgram funct newIndex  -- diepte eerst
            case p of 
                Just l -> return (Just ( (binder : l),rs')) -- If found answer retrieve binder and the rest of the rules
                Nothing -> goTopDownR (w,n) ws rs' funct totalProgram newIndex-- indien het niet gaat kijk dan naar andere regels




-- For each predicate in the list search a valid binder for it
topDownLoopBacktrack:: [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a]) ->Int-> Int -> IO ([[Binder]])

topDownLoopBacktrack [] program _ _ _= return ([])

topDownLoopBacktrack (w:ws) program func 0 index = allGoTopDown w ws program func program index -- gaat een lijst van binders geven, moet de vorige gevonden binders hieraanplakken
    

topDownLoopBacktrack (w:ws) program func bStep index = 
    (goTopDownBacktrack w ws program func program (bStep-1) index) -- geef program mee dat mogelijk verandert en totale programma


-- exactly the same as goTopDown except holds an bStep variable who is used to check for the given backtrackNode
goTopDownBacktrack:: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a])->([Clause],[Clause]) -> Int -> Int-> IO ([[Binder]])

goTopDownBacktrack (w,n) ws rs funct totalProgram bStep index =do 
    r <- stepRule (w,n) ws rs index
    case r of 
        Nothing->  return []
        Just(ws',binder,rs',newIndex)-> 
            do 
            dividedPred' <- splitNumber (n-1) (length(ws'))
            dividedPred <- shuffle dividedPred'
            p <- topDownLoopBacktrack ((depthFirst) (zip ws' dividedPred) (applyBinderSizeList ws binder)) totalProgram funct bStep newIndex  -- diepte eerst
            case p of 
                [] -> goTopDownBacktrack (w,n) ws rs' funct totalProgram bStep newIndex-- indien het niet gaat kijk dan naar andere regels
                x -> return (map (binder:) p) -- gaat binder aan elke binder in de lijst plakken
    
    