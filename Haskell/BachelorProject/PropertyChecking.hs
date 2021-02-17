
module PropertyChecking where 

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import BasicProlog


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


--Step gaat een vereenvoudigingstap uitvoeren op de term, indien dit niet gaat geeft hij Nothing terug
step :: String-> Term-> Maybe Term

step "True" _ = Nothing

step "False" _ = Nothing

step "Zero" _ = Nothing

step "ifThenElse" term  
    | condition == "True" = Just t2
    | condition == "False" = Just t3
    | otherwise =do
        t1'<- step (name t1) t1
        return (MkTerm "ifThenElse" 3 (t1' : rest))
    where
    (t1:t2:t3:[]) = values term
    rest =[t2,t3]
    condition= name t1
    
step "succ" term = do
    t' <- step (name t) t
    return (MkTerm "succ" 1 [t'])
    where
    t = head (values term)
    
step "leq" term 
    | not (normalForm t1) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "leq" 3 (t1': [t2]))
    | not (normalForm t2) =do
        t2'<-(step (name t2) t2)
        return (MkTerm "leq" 3 (t1:t2': []))
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | (name t1 == "Zero") = Just (MkTerm "True" 0 [])
    | (name t2 == "Zero") = Just (MkTerm "False" 0 [])
    | (name t1 == "succ") && (name t2 == "succ") = step "leq" (MkTerm "leq" 2 [head (values t1),head (values t2)])
    | otherwise = Nothing
     where
    (t1:t2:[]) = values term
    
step _ _ = Nothing
    
normalForm :: Term -> Bool
   
normalForm term = (Nothing == (step (name term) term))



value :: String -> Term -> Bool

value "True" _ = True

value "False" _ = True

value "Zero" _ = True

value "succ" term = nv (name t) t
    where
    t = head (values term)

value _ _ = False

nv :: String -> Term -> Bool

nv "Zero" _ = True

nv "succ" term = nv (name t) t
    where
    t = head (values term)
    
nv _ _ = False


eval :: Term -> (String-> Term-> Maybe Term) -> Term

eval t func = case t' of
        Just t'-> eval t' func
        Nothing -> t
    where
    t'=func (name t) t

-- Eerste property eval term => value
property1 :: Term -> (String-> Term-> Maybe Term) -> Bool

property1 term func = value (name t) t
    where
    t = eval term func

--tweede property ofwel vereenvoudiging mogelijk ofwel value
property2 :: Term -> (String-> Term-> Maybe Term) -> Bool

property2 term func = case t of
        Just t' -> True
        Nothing -> value (name term) term
    where
    t= func (name term) term
    
--De 3de property zegt dat na de vereenvoudigen moet de term nog steeds aan hastype voldoen    
{-property3 :: Predicate -> Set [Term] -> Bool

property3 (MkPredicate "hasType" 2 [term,typeOfTerm]) scheme = Set.member [t,typeOfTerm] scheme 
    where
    t = eval term-}
    

property3 :: Predicate  -> (String-> Term-> Maybe Term) -> Bool

property3 (MkPredicate "hasType" 2 [term,typeOfTerm]) func = checkHasType t typeOfTerm
    where
    t = eval term func

checkHasType:: Term -> Term-> Bool

checkHasType (MkTerm "True" 0 [] ) (MkTerm "bool" 0 [] ) =True

checkHasType (MkTerm "False" 0 [] ) (MkTerm "bool" 0 [] ) =True

checkHasType term (MkTerm "nat" 0 []) = nv (name term) term

checkHasType _ _ = False