
-- Project laden met random gebruik stack ghci
module Project where

import BasicProlog
import Shuffle
import TopDown
import TopDownBackTrack
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.List
import Debug.Trace
import System.IO.Unsafe
import PropertyChecking

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- FOUT ontdekt leq staat er niet tussen
semiNaiveBottomUp :: Program -> Int -> Scheme -> Scheme -> Scheme

semiNaiveBottomUp _ (-1) oldScheme differenceScheme = unionScheme oldScheme differenceScheme

semiNaiveBottomUp program n oldScheme differenceScheme = semiNaiveBottomUp program (n-1) newScheme newFoundElements
    where
    newPreds = fireAllRules program oldScheme differenceScheme
    foundElements =  addListToCorrectScheme newPreds Map.empty
    newScheme =    unionScheme oldScheme differenceScheme
    allElements =  unionScheme newScheme foundElements
    newFoundElements =  Map.differenceWith (maybeSetDif) allElements newScheme 
    
-- Gaat steeds property checken na toepassen regel, Return True als het algoritme stopt met dat de property false is, (anders geef foutief resultaat)
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




fireAllRulesProperty :: Program -> (Predicate -> Bool) -> Scheme -> Scheme -> (Maybe Predicate,[Predicate])

fireAllRulesProperty (MkProgram []) propCheck oldScheme differenceScheme = (Nothing,[])

fireAllRulesProperty (MkProgram (firstClause:restOfClauses)) propCheck oldScheme differenceScheme = 
    case prop of
        Just pred -> (Just pred,[]) -- Als tegenvoorbeeld gevonden is mogen we stoppen
        Nothing -> case propNext of
            Just predNext -> (Just predNext,[])--(True, clausePred ++ list)
            Nothing -> (Nothing,clausePred ++ list)--(False ,[]) -- add the Next found predicates to a list to use them later
            where 
            (propNext,list) =fireAllRulesProperty (MkProgram restOfClauses) propCheck oldScheme differenceScheme
    where
    clausePred = findNewPred firstClause oldScheme differenceScheme
    prop =find (propCheck) clausePred--and (map (\x -> checkProperty x func) clausePred) 


 
    
    
checkPropertyScheme :: Scheme -> (Predicate -> Bool) -> Bool
    
checkPropertyScheme scheme propCheck = listPred
    where
    listKeys = Map.toList scheme
    listPred = foldr (\(x,y) acc -> (Set.foldr (\z acc2-> (propCheck (MkPredicate x (length z) z)) 
        && acc2 ) True y ) && acc) True  listKeys
    -- predList = Map.mapWithKey (\name x -> (Set.map MkPredicate name (length x) x )) scheme



--Return True als het algoritme stopt met dat de property false is, (anders geef foutief resultaat)
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
            putStrLn "Geen regels toepasbaar"
            return Nothing

--Return True als het algoritme stopt met dat de property false is, (anders geef foutief resultaat)
topDownBacktrackPropertyChecking :: Int-> Int -> Int->(Predicate -> Bool) -> Program -> IO (Maybe Predicate)

topDownBacktrackPropertyChecking _ 0 bStep propCheck program = return Nothing

topDownBacktrackPropertyChecking size n bStep propCheck program = do
    maybePred <- topDownBacktrackAlgorithm([MkPredicate "hasType" 2 [Variable "X1",Variable "Z2"]]) size (serperateConstant program) depthFirst 0 0
    let prop = find (\x-> propCheck (head x)) maybePred --foldr (\x acc -> ((checkProperty (head x) func) && acc)) True maybePred 
    case prop of
        Just prop -> return (Just (head prop))
        Nothing -> topDownBacktrackPropertyChecking size (n-1) bStep propCheck program




    
checkProperty :: (String-> Term-> Maybe Term) -> Predicate -> Bool    
   
checkProperty func pred= property1 term func && property2 term func && property3 pred func
    where
    term = head (valuesOfPred pred)
   

andSet :: Set Bool -> Bool

andSet= foldr (&&) True





    
    