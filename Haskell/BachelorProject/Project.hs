
-- Project laden met random gebruik stack ghci
module Project where

import BasicProlog
import Shuffle
import TopDown
import TopDownBackTrack
import PropertyChecking
import BottomUp
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.List
import Debug.Trace



import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe



--  Executes the bottom-up algorithm to generate predicates, returns Nothing if every generated predicate is valid to the given property
--  Returns a counterexample if he generated a predicate that does not fulfill the property 
fastBottomUpProperty :: Program ->  (Predicate -> Bool) -> Int -> Scheme -> Scheme -> IO (Maybe Predicate)  
    
fastBottomUpProperty _ propCheck (-1) oldScheme differenceScheme = return Nothing  
    
fastBottomUpProperty program propCheck n oldScheme differenceScheme = 
    case prop of
        Nothing -> do
            fastBottomUpProperty program propCheck (n-1) newScheme newFoundElements
            where
            foundElements =  addListToCorrectScheme newPreds Map.empty
            newScheme =    unionScheme oldScheme differenceScheme
            allElements =  unionScheme newScheme foundElements
            newFoundElements =  Map.differenceWith (maybeSetDif) allElements newScheme  
        Just pred -> return (Just pred)
    where
    (prop,newPreds) = fireAllRulesProperty program propCheck oldScheme differenceScheme





-- fire all the rules in the given program, this uses the program the other way around, it tries to 
-- generate all possible combinations that can bind with the body of a clause
-- Then he is going to seach for the first predicate that doesn't fulfill the property

fireAllRulesProperty :: Program -> (Predicate -> Bool) -> Scheme -> Scheme -> (Maybe Predicate,[Predicate])

fireAllRulesProperty (MkProgram []) propCheck oldScheme differenceScheme = (Nothing,[])

fireAllRulesProperty (MkProgram (firstClause:restOfClauses)) propCheck oldScheme differenceScheme = 
    case prop of
        Just pred -> (Just pred,[]) -- Als tegenvoorbeeld gevonden is mogen we stoppen
        Nothing -> case propNext of
            Just predNext -> (Just predNext,[])
            Nothing -> (Nothing,clausePred ++ list) -- add the Next found predicates to a list to use them later
            where 
            (propNext,list) =fireAllRulesProperty (MkProgram restOfClauses) propCheck oldScheme differenceScheme
    where
    clausePred = findNewPred firstClause oldScheme differenceScheme
    prop =find (propCheck) clausePred






--  Executes the top-down algorithm to generate predicates, returns Nothing if every generated predicate is valid to the given property
--  Returns a counterexample if he generated a predicate that does not fulfill the property 
topDownPropertyChecking :: Int-> Int -> (Predicate -> Bool) -> Program -> IO (Maybe Predicate)

topDownPropertyChecking _ 0 propCheck program = return Nothing

topDownPropertyChecking size n propCheck program = do
    maybePred <- topDownAlgorithm ([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) size (serperateConstant program) depthFirst 0
    case maybePred of
        Just pred-> do
            let test = propCheck (head pred)
            if test == False then 
                return (Just (head pred))
            else do
                topDownPropertyChecking size (n-1) propCheck program
        Nothing -> do 
            putStrLn "No rules applicable"
            return Nothing





--  Executes the top-down backTrack algorithm to generate predicates, returns Nothing if every generated predicate is valid to the given property
--  Returns a counterexample if he generated a predicate that does not fulfill the property 
topDownBacktrackPropertyChecking :: Int-> Int -> Int->(Predicate -> Bool) -> Program -> IO (Maybe Predicate)

topDownBacktrackPropertyChecking _ 0 bStep propCheck program = return Nothing

topDownBacktrackPropertyChecking size n bStep propCheck program = do
    maybePred <- topDownBacktrackAlgorithm([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) size (serperateConstant program) depthFirst 0 0
    let prop = find (\x->not (propCheck (head x))) maybePred 
    case prop of
        Just prop -> return (Just (head prop))
        Nothing -> topDownBacktrackPropertyChecking size (n-1) bStep propCheck program

   
   





    
    