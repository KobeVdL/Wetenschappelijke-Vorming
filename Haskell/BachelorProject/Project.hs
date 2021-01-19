
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
    

    
    
checkProperty :: Scheme ->Bool
    
checkProperty scheme = case posP of
        Just set ->  andSet (Set.map (property1 . head) set)  && andSet (Set.map (property2 . head) set) 
              && andSet (Set.map (\x -> property3 (mkPred x) set ) set)
        Nothing -> True
    where
    posP = getSchemeValues "hasType" (scheme)
    mkPred = MkPredicate "hasType" 2 
    

andSet :: Set Bool -> Bool

andSet= foldr (&&) True





    
    