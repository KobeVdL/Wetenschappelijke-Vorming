module TopDown where

import BasicProlog
import Shuffle
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import System.IO.Unsafe

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

{-
Hieronder volgt een topdown nadering. De manier werkt als volgt met behulp van een stapel (dit doen we door middel van een array):
    1. kies een willekeurig predicaat
    2. Zet predicaat op de stapel
    3. Vereenvoudig met behulp van regel en zet deze op de stapel
    4. Voor elke variabele herhaal stap 1 tot 3
    
We voorzien nu nog een restrictie op de grootte zodat het predicaat steeds eindig blijft
dit doen we doormiddel van constante te nemen bij de laatste stap.
We moeten ook nog zorgen dat variabele steeds uniek blijven om verkeerde oplossingen te vermijden

Andere manier , ga depth first oplossing zoeken, update dan alle variabele die dezelfde waarde hebben,
Hou steeds de term bij om zo de uiteindelijke term te bepalen.

applyRule:: [Term] -> Clause -> Term -> [Term]

applyRule stack rule term = error "not implemented"

-}
-- input:
--      1. predikaten die vereenvoudigd moeten worden
--      2. programme die regels geeft
--      3. De grootte van de maximale lengte van de parse tree
 
findBinderStep :: [Predicate] -> Program -> Integer->  Binder

findBinderStep [] _ size= Map.empty--trace ("body leeg, grootte is " ++ show size) (Map.empty)

findBinderStep (x:xs) program size = Map.union (firstBinder) (findBinderStep newPredicates program size)
    where
    firstBinder= topDownPred x program size--trace "binderStep geweest" (topDownPred x program size)
    newPredicates = Map.foldrWithKey (\t1 t2 predList -> changeVariableInPredicateList predList t1 t2) xs firstBinder
    -- trace ("Binder is " ++ show firstBinder) (Map.foldrWithKey (\t1 t2 predList -> changeVariableInPredicateList predList t1 t2) xs firstBinder)

{-
Predicaat en/of term moet de volgende omringen 

1. voeg regel toe en doe dan recursief verder
2. unificatie op de rest van de regels (zodat regel hetzelfde blijft
3. toepassen op overige termen


-}

-- Gaat de uiteindelijke binder voor predikaat teruggeven
-- doe dit door middel van regel te zoeken die je kan toepassen 
-- Hiervan binder zoeken en toepassen zodat je uiteindelijke predikaat terugkrijgt en daarvan binders gaat zoeken

--werkt ongeveer maar bij if then else geeft hij bij W soms 2 verschillende waardes
-- probleem ligt bij unificatie kijkt hij niet naar wat er voor is gevonden
topDownPred :: Predicate -> Program -> Integer -> Binder

topDownPred pred program 0 = binder -- findBinder pred (headTerm a)
    where
    (const,rules) = serperateConstant program
    x = randomPermutation const
    r = findBindingRule pred x
    Just binder = findBinderPred pred (headTerm r)
    -- z = findBinderStep body r 
    -- a = bindRule r z

topDownPred pred program n = binder -- findBinder pred (headTerm a)
    where
    x = randomPermutation (releaseProgram program)
    newPred= renameVariablePred pred 
    r = (findBindingRule newPred x)
    Just bind =findBinderPred newPred (headTerm r)
    newRule= bindRule r bind 
    z = findBinderStep (body newRule) program (n-1)-- trace ("Rule is " ++ show newRule )(findBinderStep (body newRule) program (n-1))
    a =  bindRule newRule z --trace ("Binder is " ++ show z) (bindRule newRule z)  
    Just binder = findBinderPred (headTerm a) pred  --trace ("gebonden regel is " ++ show a++ "\n predikaat is " ++ show pred) (findBinderPred (headTerm a) pred )


--Rename variable gaat eerst alle variabele zoeken die er in voorkomen en dan hernoemen naar _n
-- met n een nummer, we verwachten dat de gebruiker geen variabele ingeeft van deze vorm 
findVariablesList :: [Term] -> Set Term

findVariablesList  = foldr (\x acc-> Set.union (findVariable x) acc ) Set.empty

findVariable :: Term -> Set Term

findVariable (MkTerm _ _ []) =Set.empty

findVariable (Variable name) =  Set.singleton (Variable name)

findVariable (MkTerm _ _ list) = findVariablesList list



renameVariablePred :: Predicate -> Predicate

renameVariablePred pred = newPred
    where
    set = findVariablesList (valuesOfPred pred)
    binder  = renameBinder (Set.toList set) 0
    newPred = Map.foldrWithKey (\t1 t2 predList -> changeVariableInPredicate predList t1 t2) pred binder 

renameBinder :: [Term] -> Integer -> Binder
  
renameBinder [] _ = Map.empty
  
renameBinder (x:xs) n = Map.union (Map.singleton x (Variable ("_" ++ show n))) (renameBinder xs (n+1))

 

        
--TODO veranderen naar maybe
findBindingRule :: Predicate -> [Clause] ->Clause

findBindingRule pred (x:xs) = case binder of
    Nothing -> findBindingRule pred xs
    Just bind -> x
    where
    binder = findBinderPred (headTerm x) pred
    

{-
--Zoekt waarbij de head kan binden met de gegeven predikaat
applyRule :: Predicate -> [Clause] -> Maybe (Binder,[Predicate])


applyRule pred [] = Nothing

applyRule pred (x:xs) = case binder of
    Nothing -> applyRule pred xs
    Just bind -> Just (body (bindRule x bind))
    where
    termsOfRule = headTerm x
    binder = findBinderPred (headTerm x) pred
-}

-- generates elements to test in a top down matter  bec bottom up has to many cases
topDownPredicate :: ([Clause],[Clause]) -> Integer  -> Predicate

topDownPredicate (const,_) 0 = headTerm (head const)--TODO

topDownPredicate (const,rules) size = MkPredicate "" 0 [] -- TODO


{-
getConstants :: Program -> [Clause]

getConstants (MkProgram clauseList) = map (filter (\x -> body x == []) clauseList)

-}

--Gaat nog een probleem hebben met variabele die hernoemd moeten worden

pop :: [a] -> (a, [a])

pop [] = error "stack is empty"

pop (x:xs) = (x,xs)

put:: [a] -> a -> [a]

put list a = a:list


topDownAlgorithm :: Program -> Integer-> Predicate

topDownAlgorithm p 0 = headTerm (head x)
    where 
    (const,rules) = serperateConstant p
    x = randomPermutation const

topDownAlgorithm p n = headTerm (head x) --topDownAlgorithmHelper rules [headTerm (head x)] (n-1)
    where
    rules = releaseProgram p
    x = randomPermutation (rules)
    
topDownAlgorithmHelper:: Program -> [Predicate]-> [Term]

topDownAlgorithmHelper _ _= [MkTerm "" 0 []] --TODO



-- Geeft tuppel terug waarbij het eerste deel constanten zijn en het 2de deel regels
serperateConstant :: Program -> ([Clause],[Clause])

serperateConstant (MkProgram xs) = serperateConstantHelper xs


    
serperateConstantHelper :: [Clause] -> ([Clause],[Clause])

serperateConstantHelper [] =([],[])

serperateConstantHelper (x:xs)
    | body x == [] = let (cons,rules) = serperateConstantHelper xs in
                        (x:cons,rules)
    | otherwise = let (cons,rules) = serperateConstantHelper xs in
                        (cons,x:rules)
    
{-
De volgend functie krijgt een lijst als input en berekent een random permutatie hiervan,
We maken hier gebruik van het Fisher–Yates gelijkaardig shuffle algoritme dat in O(n*logn) tijd werkt.
We kunnen niet in O(n) omdat haskell niet in lineare tijd aan de elementen in de array kan
-}

--VRAAG: mag dit wel gebruikt worden of is het beter om steeds IO lijst door te geven
randomPermutation :: [a] -> [a]

randomPermutation = unsafePerformIO . shuffle
