
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

step "A" _ = Nothing

step "[]" _ = Nothing

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
    
step "add" (MkTerm "add" 2 [t1,t2]) 
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "add" 2 [t1',t2])
    | not (normalForm t2 step) = do
        t2'<-(step (name t2) t2)
        return (MkTerm "add" 2 [t1,t2'])
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | otherwise = Just (addTerms t1 t2)


step "subtract" (MkTerm "subtract" 2 [t1,t2])  
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "subtract" 2 [t1',t2])
    | not (normalForm t2 step) = do
        t2'<-(step (name t2) t2)
        return (MkTerm "subtract" 2 [t1,t2'])
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | otherwise = Just (subtractTerms t1 t2)
    
step "multiply" (MkTerm "multiply" 2 [t1,t2]) 
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "multiply" 2 [t1',t2])
    | not (normalForm t2 step) = do
        t2'<-(step (name t2) t2)
        return (MkTerm "multiply" 2 [t1,t2'])
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | otherwise = Just (multiplyTerms t1 t2)    
    
    
step "leq" (MkTerm "leq" 2 [t1,t2])
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "leq" 2 [t1',t2])
    | not (normalForm t2 step) =do
        t2'<-(step (name t2) t2)
        return (MkTerm "leq" 2 [t1,t2'])
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | (name t1 == "Zero") = Just (MkTerm "True" 0 [])
    | (name t2 == "Zero") = Just (MkTerm "False" 0 [])
    | (name t1 == "succ") && (name t2 == "succ") = step "leq" (MkTerm "leq" 2 [head (values t1),head (values t2)])
    | otherwise = Nothing

step ":" (MkTerm ":" 2 [t1,t2]) 
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm ":" 2 [t1',t2])
    | not (normalForm t2 step) =do
        t2'<-(step (name t2) t2)
        return (MkTerm ":" 2 [t1,t2'])
    | otherwise = Nothing

step "++" (MkTerm "++" 2 [t1,t2]) 
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "++" 2 [t1',t2])
    | not (normalForm t2 step) =do
        t2'<-(step (name t2) t2)
        return (MkTerm "++" 2 [t1,t2'])
    | otherwise = Just (appendArrays t1 t2)

    
step _ _ = Nothing
    

--PRECONDITION both terms are simplified
-- adds two terms to each other on a declarative way
addTerms :: Term -> Term ->  Term

addTerms (MkTerm "Zero" 0 []) otherTerm = otherTerm

addTerms (MkTerm "succ" 1 [rest]) otherTerm = addTerms rest (succ [otherTerm]) 
    where
    succ = MkTerm "succ" 1 
    


--PRECONDITION both terms are simplified
-- subtract two terms, returns zero if the second term is larger then the first
subtractTerms :: Term -> Term -> Term

subtractTerms (MkTerm "Zero" 0 []) otherTerm =  (MkTerm "Zero" 0 [])

subtractTerms firstTerm (MkTerm "Zero" 0 []) =  firstTerm

subtractTerms (MkTerm "succ" 1 [rest]) (MkTerm "succ" 1 [rest2]) = subtractTerms rest rest2 

    
    
--PRECONDITION both terms are simplified
-- multiply 2 terms by adding them n times the second term n is the number of the first term
multiplyTerms :: Term -> Term -> Term

multiplyTerms t1 t2 = multiplyTermsHelper t1 t2 (MkTerm "Zero" 0 [])

multiplyTermsHelper :: Term -> Term ->Term -> Term


multiplyTermsHelper (MkTerm "Zero" 0 []) startTerm resultTerm  = resultTerm

multiplyTermsHelper firstTerm (MkTerm "Zero" 0 []) resultTerm =  resultTerm

multiplyTermsHelper (MkTerm "succ" 1 [rest]) otherTerm resultTerm= multiplyTermsHelper rest otherTerm (addTerms otherTerm resultTerm)
 
  


--PRECONDITION both terms are simplified
-- append two arrays to each other
appendArrays :: Term -> Term -> Term

appendArrays (MkTerm "[]" 0 []) otherTerm = otherTerm

appendArrays (MkTerm ":" 2 [x,xs]) otherTerm = (MkTerm ":" 2 [x , appendArrays xs otherTerm])

    
    
    
--Step gaat een vereenvoudigingstap uitvoeren op de term, indien dit niet gaat geeft hij Nothing terug
-- step1 bevat een fout
-- step1 voldoet niet aan de eerste property
step1 :: String-> Term-> Maybe Term

step1 "True" _ = Nothing

step1 "False" _ = Nothing

step1 "Zero" _ = Nothing

step1 "ifThenElse" term  
    | condition == "True" = Just t2
    | condition == "False" = Just t3
    | otherwise =do
        t1'<- step (name t1) t1
        return (MkTerm "ifThenElse" 3 (t1' : rest))
    where
    (t1:t2:t3:[]) = values term
    rest =[t2,t3]
    condition= name t1
    
step1 "succ" term = do
    t' <- step (name t) t
    return (MkTerm "succ" 1 [t'])
    where
    t = head (values term)
    
step1 "leq" term 
    | not (normalForm t1 step2) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "leq" 3 (t1': [t2]))
    | not (normalForm t2 step2) =do
        t2'<-(step (name t2) t2)
        return (MkTerm "leq" 3 (t1:t2': []))
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | (name t1 == "Zero") = Just (Variable "X" ) -- Verandering t.o.v. normale step functie
    | (name t2 == "Zero") = Just (MkTerm "False" 0 [])
    | (name t1 == "succ") && (name t2 == "succ") = step "leq" (MkTerm "leq" 2 [head (values t1),head (values t2)])
    | otherwise = Nothing
     where
    (t1:t2:[]) = values term
    
step1 _ _ = Nothing    
    
   

--Step gaat een vereenvoudigingstap uitvoeren op de term, indien dit niet gaat geeft hij Nothing terug
-- step2 bevat een fout
-- step2 voldoet niet aan property2

step2 :: String-> Term-> Maybe Term

step2 "True" _ = Nothing

step2 "False" _ = Nothing

step2 "Zero" _ = Nothing

step2 "ifThenElse" term  
    | condition == "True" = Just t2
    | condition == "False" = Just t3
    | otherwise =do
        t1'<- step (name t1) t1
        return (MkTerm "ifThenElse" 3 (t1' : rest))
    where
    (t1:t2:t3:[]) = values term
    rest =[t2,t3]
    condition= name t1
    
step2 "succ" term = do
    t' <- step (name t) t
    return (MkTerm "succ" 1 [t'])
    where
    t = head (values term)
    
step2 "leq" term 
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "leq" 3 (t1': [t2]))
    | not (normalForm t2 step) =do
        t2'<-(step (name t2) t2)
        return (MkTerm "leq" 3 (t1:t2': []))
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | (name t1 == "Zero") = Nothing -- Hier zit de fout 
    | (name t2 == "Zero") = Just (MkTerm "False" 0 [])
    | (name t1 == "succ") && (name t2 == "succ") = step "leq" (MkTerm "leq" 2 [head (values t1),head (values t2)])
    | otherwise = Nothing
     where
    (t1:t2:[]) = values term
    
step2 _ _ = Nothing



--Step gaat een vereenvoudigingstap uitvoeren op de term, indien dit niet gaat geeft hij Nothing terug
-- step3 bevat een fout
-- step3 voldoet niet aan property3

step3 :: String-> Term-> Maybe Term

step3 "True" _ = Nothing

step3 "False" _ = Nothing

step3 "Zero" _ = Nothing

step3 "ifThenElse" term  
    | condition == "True" = Just t2
    | condition == "False" = Just t3
    | otherwise =do
        t1'<- step (name t1) t1
        return (MkTerm "ifThenElse" 3 (t1' : rest))
    where
    (t1:t2:t3:[]) = values term
    rest =[t2,t3]
    condition= name t1
    
step3 "succ" term = Just (MkTerm "ifThenElse" 3 [true, true ,true])  -- hier zit de fout 
    where
    true = MkTerm "true" 0 []
    
step3 "leq" term 
    | not (normalForm t1 step) = do
        t1'<-(step (name t1) t1)
        return (MkTerm "leq" 3 (t1': [t2]))
    | not (normalForm t2 step) =do
        t2'<-(step (name t2) t2)
        return (MkTerm "leq" 3 (t1:t2': []))
    | not (nv (name t1) t1) && not (nv (name t1) t1) = Nothing
    | (name t1 == "Zero") = Just (MkTerm "True" 0 [])
    | (name t2 == "Zero") = Just (MkTerm "False" 0 [])
    | (name t1 == "succ") && (name t2 == "succ") = step "leq" (MkTerm "leq" 2 [head (values t1),head (values t2)])
    | otherwise = Nothing
     where
    (t1:t2:[]) = values term
    
step3 _ _ = Nothing

   
    
normalForm :: Term -> (String-> Term-> Maybe Term) -> Bool
   
normalForm term func = (Nothing == (func (name term) term))



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

property3 :: Predicate  -> (String-> Term-> Maybe Term) -> Bool

property3 (MkPredicate "hasType" 2 [term,typeOfTerm]) func = checkHasType t typeOfTerm
    where
    t = eval term func


-- Checks if the value of the given type is correct
checkHasType:: Term -> Term-> Bool

checkHasType (MkTerm "True" 0 [] ) (MkTerm "bool" 0 [] ) =True

checkHasType (MkTerm "False" 0 [] ) (MkTerm "bool" 0 [] ) =True

checkHasType term (MkTerm "nat" 0 []) = nv (name term) term

checkHasType _ _ = False