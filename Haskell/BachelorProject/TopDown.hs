module TopDown where

import BasicProlog
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



{-
    Hieronder volgt een topdown nadering. De manier werkt als volgt met behulp van een stapel (dit doen we door middel van een array):
    1. kies een willekeurig predicaat
    2. Zet predicaat op de stapel
    3. Vereenvoudig met behulp van regel en zet deze op de stapel
    4. Voor elke variabele herhaal stap 3 tot stapel leeg is
    
    We voorzien nu nog een restrictie op de grootte zodat het predicaat steeds eindig blijft
    dit doen we doormiddel van constante te nemen bij de laatste stap.
    We moeten ook nog zorgen dat variabele steeds uniek blijven om verkeerde oplossingen te vermijden

-}



{-
    Predicaat en/of term moet de volgende omringen 

    1. voeg regel toe en doe dan recursief verder
    2. unificatie op de rest van de regels (zodat regel hetzelfde blijft
    3. toepassen op overige termen

-}

-- generates elements to test in a top down matter  bec bottom up has to many cases



-- Gives tuple where the first part are facts and the second are the other rules
serperateConstant :: Program -> ([Clause],[Clause])

serperateConstant (MkProgram xs) = serperateConstantHelper xs

-- Helper for the serperateConstant function
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

-- shuffles the elements in an array in a random order
randomPermutation ::  [a] -> IO [a]

randomPermutation = shuffle


-- evaluates the elements in a depth first manner (by appending the new element at the head of the list)
depthFirst:: [a]-> [a] -> [a]

depthFirst = (++)
   
-- evaluates the elements in a breadth first manner (by appending the new element at the back of the list)
breadthFirst:: [a] -> [a] -> [a]

breadthFirst list1 list2 = list2 ++ list1    




-- creates a predicate with a top-down approuch, it makes random choices in the syntax tree to generate a program
-- Returns Nothing if no programs of size n are possible
-- The top-down approuch work with a worklist that has to be empty to stop    
topDownAlgorithm:: [Predicate] -> Int -> ([Clause],[Clause]) -> ([a] -> [a] -> [a]) ->Int -> IO (Maybe [Predicate])

topDownAlgorithm startPred n rules func index =do
    allBinders <- topDownLoop (zip startPred (repeat n)) rules func index
    case allBinders of
        Nothing -> return Nothing
        Just listBinders->do
            return (Just (foldl (\acc x -> bindValue acc x) startPred listBinders)) -- give binded result back
  
  
-- For each predicate in the list search a valid binder for it
topDownLoop:: [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a]) -> Int -> IO (Maybe [Binder])

topDownLoop [] program _ _= return (Just [])

topDownLoop (w:ws) program func index = 
    (goTopDown w ws program func program index) -- geef program mee dat mogelijk verandert en totale programma


-- In this step the real works happens, first it selects a rule where the first value in the list can bind with
-- From there it divides the size in random subsizes to its replaced elements
-- Then start back again with the old elements added to the new (change manner in code if you want to do it depth order
-- breadth first.
goTopDown:: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a])->([Clause],[Clause]) ->Int-> IO (Maybe [Binder])

goTopDown (w,n) ws rs funct totalProgram index =do 
    r <- stepRule (w,n) ws rs index
    case r of 
        Nothing->  return Nothing
        Just(ws',binder,rs',newIndex)-> 
            do 
            dividedPred' <- splitNumber (n-1) (length(ws'))
            dividedPred <- shuffle dividedPred'
            p <- topDownLoop ((depthFirst) (zip ws' dividedPred) (applyBinderSizeList ws binder)) totalProgram funct newIndex  -- diepte eerst
            case p of 
                Just l -> return (Just ( binder : l))
                Nothing -> goTopDown (w,n) ws rs' funct totalProgram newIndex-- indien het niet gaat kijk dan naar andere regels


-- searches for a rule which can bind with given predicate and reurns it back togheter with a newIndex
-- for renaming the terms and the binder such that every element in the list is correctly replaced
stepRule :: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause]) ->Int-> IO (Maybe ([(Predicate)],Binder,([Clause],[Clause]),Int))

stepRule (pred,0) rest (const,rules) index = do
    x <- randomPermutation (const)
    let foundBindRule= do findBindingRule pred x 
    case foundBindRule of 
        Nothing -> return Nothing
        Just (rule,rest) ->
            do --Moet variabele nog hernoemen
               let (editedRule,newIndex) = rename rule index
               let  Just bind = findBinder pred (headTerm editedRule) --altijd voldaan door findBindingRule
               return (Just (((bindValue (body editedRule) bind)),bind,
                (rest,rules),newIndex))
                
stepRule (pred,n) rest (const,rules) index = do
    x <- randomPermutation (rules)
    let foundBindRule= do findBindingRule pred x 
    case foundBindRule of 
        Nothing -> return Nothing
        Just (rule,rest) ->
            do 
               let (editedRule,newIndex) = rename rule index
               let  Just bind = findBinder pred (headTerm editedRule) --altijd voldaan door findBindingRule
               return (Just (((bindValue (body editedRule) bind)),bind,
                (const,rest),newIndex))





applyBinderSizeList :: [(Predicate,Int)] -> Binder -> [(Predicate,Int)]

applyBinderSizeList list binder  = zip (bindValue predList binder) sizeList
    where
    (predList,sizeList) = unzip list
    
    
maybeAppend :: Maybe a -> Maybe b -> (a->b->b) ->Maybe b

maybeAppend (Just a) (Just b) f = Just (f a b )

maybeAppend _ _ _= Nothing
    
   
   
   
   