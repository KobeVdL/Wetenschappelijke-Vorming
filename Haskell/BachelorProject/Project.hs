
-- Project laden met random gebruik stack ghci
module Project where

import BasicProlog
import Shuffle
import TopDown
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import System.IO.Unsafe
import PropertyChecking

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


semiNaiveBottomUp :: Program -> Integer -> Scheme -> Scheme -> Scheme

semiNaiveBottomUp _ 0 oldScheme differenceScheme = unionScheme oldScheme differenceScheme

semiNaiveBottomUp program n oldScheme differenceScheme = semiNaiveBottomUp program (n-1) newScheme newFoundElements
    where
    newPreds = fireAllRules program oldScheme differenceScheme
    foundElements =  addListToCorrectScheme newPreds Map.empty
    newScheme =    unionScheme oldScheme differenceScheme
    allElements =  unionScheme newScheme foundElements
    newFoundElements =  Map.differenceWith (maybeSetDif) allElements newScheme 
    
-- Gaat steeds property checken na toepassen regel
fastBottomUpProperty :: Program -> Integer -> Scheme -> Scheme -> Bool    
    
fastBottomUpProperty _ 0 oldScheme differenceScheme = True   
    
fastBottomUpProperty program n oldScheme differenceScheme = 
    case prop of
        True -> fastBottomUpProperty program (n-1) newScheme newFoundElements
            where
            foundElements =  addListToCorrectScheme newPreds Map.empty
            newScheme =    unionScheme oldScheme differenceScheme
            allElements =  unionScheme newScheme foundElements
            newFoundElements =  Map.differenceWith (maybeSetDif) allElements newScheme  
        False -> False
    where
    (prop,newPreds) = fireAllRulesProperty program oldScheme differenceScheme




fireAllRulesProperty :: Program -> Scheme -> Scheme -> (Bool,[Predicate])

fireAllRulesProperty (MkProgram []) oldScheme differenceScheme = (True,[])

fireAllRulesProperty (MkProgram (firstClause:restOfClauses)) oldScheme differenceScheme = 
    case prop of
        False -> (False ,[]) -- Als property false is mogen we stoppen
        True -> case propNext of
            True -> (True, clausePred ++ list)
            False -> (False ,[])
            where 
            (propNext,list) =fireAllRulesProperty (MkProgram restOfClauses) oldScheme differenceScheme
    where
    clausePred = findNewPred firstClause oldScheme differenceScheme
    prop = and (map (\x -> checkProperty x step) clausePred) 


 
    
    
checkPropertyScheme :: Scheme -> (String-> Term-> Maybe Term) -> Bool
    
checkPropertyScheme scheme func = listPred
    where
    listKeys = Map.toList scheme
    listPred = foldr (\(x,y) acc -> (Set.foldr (\z acc2-> (checkProperty (MkPredicate x (length z) z) func) 
        && acc2 ) True y ) && acc) True  listKeys
    -- predList = Map.mapWithKey (\name x -> (Set.map MkPredicate name (length x) x )) scheme


    
checkProperty :: Predicate  -> (String-> Term-> Maybe Term) -> Bool    
   
checkProperty pred  func = property1 term func && property2 term func && property3 pred func
    where
    term = head (valuesOfPred pred)
   

andSet :: Set Bool -> Bool

andSet= foldr (&&) True





    
    