module BasicStep where
 

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import BasicProlog


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


-- The simplification algorithm which is unique for each programming language
-- This step is tested in property checking to see if the simplification is correct.
step ::  Term-> (Term-> Maybe Term)-> Maybe Term

step (MkTerm "True" 0 []) _ = Nothing

step (MkTerm "False" 0 []) _= Nothing

step (MkTerm "Zero" 0 []) _= Nothing

step (MkTerm "'A'" 0 []) _= Nothing

step (MkTerm "[]" 0 []) _= Nothing

step (MkTerm "ifThenElse" 3 [t1,t2,t3]) stepMethod 
    | not (normalForm t1 stepMethod) =do
        t1'<- stepMethod t1
        return (MkTerm "ifThenElse" 3 (t1' : rest))
    | t1 == (MkTerm "True" 0 []) = Just t2
    | t1 == (MkTerm "False" 0 []) = Just t3
    | otherwise = Nothing
    where
    rest =[t2,t3]
    
step (MkTerm "succ" 1 [t]) stepMethod = do
    t' <- stepMethod t
    return (MkTerm "succ" 1 [t'])

    
step (MkTerm "add" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "add" 2 [t1',t2])
    | not (normalForm t2 stepMethod) = do
        t2'<-(stepMethod t2)
        return (MkTerm "add" 2 [t1,t2'])
    | not (nv t1) || not (nv t2) = Nothing-- error "not a number value for reducing"
    | otherwise = Just (addTerms t1 t2)


step (MkTerm "subtract" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "subtract" 2 [t1',t2])
    | not (normalForm t2 stepMethod) = do
        t2'<-(stepMethod t2)
        return (MkTerm "subtract" 2 [t1,t2'])
    | not (nv t1) || not (nv t2) = Nothing--error "not a number value for reducing"
    | otherwise = Just (subtractTerms t1 t2)
    
step (MkTerm "multiply" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod  t1)
        return (MkTerm "multiply" 2 [t1',t2])
    | not (normalForm t2 stepMethod) = do
        t2'<-(stepMethod  t2)
        return (MkTerm "multiply" 2 [t1,t2'])
    | not (nv t1) || not (nv t2) = Nothing--error "not a number value for reducing"
    | otherwise = Just (multiplyTerms t1 t2)    
    
    
step (MkTerm "leq" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "leq" 2 [t1',t2])
    | not (normalForm t2 stepMethod) =do
        t2'<-(stepMethod t2)
        return (MkTerm "leq" 2 [t1,t2'])
    | not (nv t1) || not (nv t2) = Nothing--error "not a number value for reducing"
    | (name t1 == "Zero") = Just (MkTerm "True" 0 [])
    | (name t2 == "Zero") = Just (MkTerm "False" 0 [])
    | (name t1 == "succ") && (name t2 == "succ") = stepMethod  (MkTerm "leq" 2 [head (values t1),head (values t2)])
    | otherwise = error "Can't reduce term"

step (MkTerm ":" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm ":" 2 [t1',t2])
    | not (normalForm t2 stepMethod) =do
        t2'<-(stepMethod t2)
        return (MkTerm ":" 2 [t1,t2'])
    | not (arrayValue t2) = Nothing
    | otherwise = Nothing

step (MkTerm "++" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "++" 2 [t1',t2])
    | not (normalForm t2 stepMethod) =do
        t2'<-(stepMethod t2)
        return (MkTerm "++" 2 [t1,t2'])
    | not (arrayValue t1) || not (arrayValue t2) = Nothing
    | otherwise = Just (appendArrays t1 t2)
    
step (MkTerm "and" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "and" 2 [t1',t2])
    | not (normalForm t2 stepMethod) =do
        t2'<-(stepMethod t2)
        return (MkTerm "and" 2 [t1,t2'])
    | not (bv t1) || not (bv t2) = Nothing--error "not a boolean value for reducing"
    | otherwise = Just (booleanOperation (&&) t1 t2)
    
step (MkTerm "or" 2 [t1,t2]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "or" 2 [t1',t2])
    | not (normalForm t2 stepMethod) =do
        t2'<-(stepMethod t2)
        return (MkTerm "or" 2 [t1,t2'])
    | not (bv t1) || not (bv t2) = Nothing--error "not a boolean value for reducing"
    | otherwise = Just (booleanOperation (||) t1 t2)

step (MkTerm "not" 1 [t1]) stepMethod
    | not (normalForm t1 stepMethod) = do
        t1'<-(stepMethod t1)
        return (MkTerm "not" 1 [t1'])
    | not (bv t1) = Nothing--error "not a boolean value for reducing"
    | otherwise = Just ( boolToTerm(not(termToBool t1)))    

    
    
step term _ = trace ("term is " ++ show term) error "Term not included in current step method"
    

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

-- a helper function for multiply
multiplyTermsHelper (MkTerm "Zero" 0 []) startTerm resultTerm  = resultTerm

multiplyTermsHelper firstTerm (MkTerm "Zero" 0 []) resultTerm =  resultTerm

multiplyTermsHelper (MkTerm "succ" 1 [rest]) otherTerm resultTerm= multiplyTermsHelper rest otherTerm (addTerms otherTerm resultTerm)
 
  


--PRECONDITION both terms are simplified
-- append two arrays to each other
appendArrays :: Term -> Term -> Term

appendArrays (MkTerm "[]" 0 []) otherTerm = otherTerm

appendArrays (MkTerm ":" 2 [x,xs]) otherTerm = (MkTerm ":" 2 [x , appendArrays xs otherTerm])

appendArrays t1 t2 = trace ("t1 is " ++ (show t1) ++ " t2 is " ++ (show t2)) (error "Not valid argument appendArray")   
   
--PRECONDITION both terms are simplified
-- simplify with the booleanOperation
booleanOperation :: (Bool->Bool->Bool) -> Term -> Term -> Term

booleanOperation (operat) b1 b2 =boolToTerm (operat (termToBool b1) (termToBool b2))




--change the term to a boolean
termToBool:: Term -> Bool

termToBool (MkTerm "True" 0 []) = True

termToBool (MkTerm "False" 0 []) = False



-- change the boolean to a term
boolToTerm :: Bool -> Term
   
boolToTerm True = MkTerm "True" 0 []

boolToTerm False = MkTerm "False" 0 []



-- Checks if given term is in normal form with the given simplification algorithm
normalForm :: Term -> ( Term-> Maybe Term) -> Bool
   
normalForm term func = (Nothing == (func term))


-- Returns True if the given Term is a value as that it cannot be simplified anymore
value :: Term -> Bool

value (MkTerm "True" 0 []) = True

value (MkTerm "False" 0 []) = True

value (MkTerm "Zero" 0 []) = True

value (MkTerm "[]" 0 []) = True

value (MkTerm "'A'" 0 []) = True

value (MkTerm "succ" 1 [x]) = nv x

value (MkTerm ":" 2 [x,y]) = value x && arrayValue y

value _ = False


-- Returns True if the given Term is a number value
nv ::  Term -> Bool

nv (MkTerm "Zero" 0 [] )= True

nv (MkTerm "succ" 1 [t] ) = nv t
     
nv _ = False


-- Returns True if the given Term is a basic boolean value
bv:: Term -> Bool

bv (MkTerm "True" 0 [] ) = True

bv (MkTerm "False" 0 [] ) = True

bv _ = False


-- Returns True if the given Term is a basic array (only : or [])

arrayValue:: Term-> Bool

arrayValue (MkTerm "[]" 0 []) = True

arrayValue (MkTerm ":" 2 [x,y]) = arrayValue y

arrayValue _ =False


-- evaluate the term with the given simplification algorithm
-- evaluate shall call the given simplification untill it can't be simplified anymore
eval :: Term -> (Term-> Maybe Term) -> Term

eval t func = case t' of
        Just t'-> eval t' func
        Nothing -> t
    where
    t'=func t


-- The first property states that when a term is fully evaluated that it should have a value as a result
-- First property eval term => value
property1 :: Term -> ( Term-> Maybe Term) -> Bool

property1 term func = value t
    where
    t = eval term func

-- The second property states that a simplification step should be possible or otherwise it should be a value
-- second property or simplification possible or value
property2 :: Term -> ( Term-> Maybe Term) -> Bool

property2 term func = case t of
        Just t' -> True
        Nothing -> value term
    where
    t= func term
    
    
    
  
-- The third property states that after an evaluation the type of the term should be the same
property3 :: Predicate  -> (Term-> Maybe Term) -> Bool

property3 (MkPredicate "hasType" 2 [term,typeOfTerm]) func = checkHasType t typeOfTerm
    where
    t = eval term func


-- Checks if the value of the given type is correct
checkHasType:: Term -> Term-> Bool

checkHasType (MkTerm "True" 0 [] ) (MkTerm "bool" 0 [] ) =True

checkHasType (MkTerm "False" 0 [] ) (MkTerm "bool" 0 [] ) =True

checkHasType (MkTerm "'A'" 0 []) (MkTerm "char" 0 []) = True

checkHasType (MkTerm "[]" 0 [] ) (MkTerm "array" 1 [x]) = True

checkHasType (MkTerm ":" 2 [x,y]) (MkTerm "array" 1 [z]) = checkHasType x z && checkHasType y (MkTerm "array" 1 [z])

checkHasType term (MkTerm "nat" 0 []) = nv term

checkHasType _ _ = False




-- Checks all the 3 properties with the given simplification algorithm and predicate
checkProperty :: (Term-> Maybe Term) -> Predicate -> Bool    
   
checkProperty func pred= property1 term func && property2 term func && property3 pred func
    where
    term = head (valuesOfPred pred)

 