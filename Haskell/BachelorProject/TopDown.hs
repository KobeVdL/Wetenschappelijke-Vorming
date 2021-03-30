module TopDown where

import BasicProlog
import Shuffle
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import System.IO.Unsafe
import System.Random
import Control.Monad.Trans.Maybe

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


-- TODO zorg dat je enkel variabele kan kiezen bij n =0


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



-}
-- input:
--      1. predikaten die vereenvoudigd moeten worden
--      2. programme die regels geeft
--      3. De grootte van de maximale lengte van de parse tree
 


maybeUnion:: Ord k => Maybe (Map k a) -> Maybe (Map k a) -> Maybe (Map k a) 

maybeUnion Nothing  _ = Nothing

maybeUnion _ Nothing = Nothing

maybeUnion (Just x) ( Just y ) = Just (Map.union x y) 



{-
Predicaat en/of term moet de volgende omringen 

1. voeg regel toe en doe dan recursief verder
2. unificatie op de rest van de regels (zodat regel hetzelfde blijft
3. toepassen op overige termen


-}





-- generates elements to test in a top down matter  bec bottom up has to many cases




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

--Slechte implementatie ziet dit als een inpure functie en geeft steeds hetzelfde resultaat terug
--randomPermutation :: [a] -> [a]

--randomPermutation = unsafePerformIO . shuffle



randomPermutation ::  [a] -> IO [a]

randomPermutation = shuffle


   
depthFirst:: [a]-> [a] -> [a]

depthFirst = (++)
   
breadthFirst:: [a] -> [a] -> [a]

breadthFirst list1 list2 = list2 ++ list1    

   
topDownAlgorithm:: [Predicate] -> Int -> ([Clause],[Clause]) -> ([a] -> [a] -> [a]) ->Int -> IO (Maybe [Predicate])

topDownAlgorithm startPred n rules func index =do
    allBinders <- topDownLoop (zip startPred (repeat n)) rules func index
    case allBinders of
        Nothing -> return Nothing
        Just listBinders->do
            return (Just (foldl (\acc x -> applyBinder acc x) startPred listBinders)) -- give binded result back
  
-- For each predicate in the list search a valid binder for it
topDownLoop:: [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a]) -> Int -> IO (Maybe [Binder])

topDownLoop [] program _ _= return (Just [])

topDownLoop (w:ws) program func index = 
    (goTopDown w ws program func program index) -- geef program mee dat mogelijk verandert en totale programma



goTopDown:: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause])-> ([a] -> [a] -> [a])->([Clause],[Clause]) ->Int-> IO (Maybe [Binder])

goTopDown (w,n) ws rs funct totalProgram index =do 
    r <- stepRule (w,n) ws rs index
    case r of 
        Nothing->  return Nothing
        Just(ws',binder,rs',newIndex)-> 
            do 
            --putStrLn (show ws')
            dividedPred' <- splitNumber (n-1) (length(ws'))
            dividedPred <- shuffle dividedPred'
            --putStrLn ("Old List of preds are "++ show ws)
            --putStrLn ("Binders are "++ show (binder))
            --putStrLn ("Added rules are "++ show (ws'))
            --putStrLn ("New List of preds are "++ show (applyBinderSizeList ws binder))
            p <- topDownLoop ((depthFirst) (zip ws' dividedPred) (applyBinderSizeList ws binder)) totalProgram funct newIndex  -- diepte eerst
            case p of 
                Just l -> return (Just ( binder : l))
                Nothing -> goTopDown (w,n) ws rs' funct totalProgram newIndex-- indien het niet gaat kijk dan naar andere regels


        
stepRule :: (Predicate,Int) -> [(Predicate,Int)] -> ([Clause],[Clause]) ->Int-> IO (Maybe ([(Predicate)],Binder,([Clause],[Clause]),Int))

stepRule (pred,0) rest (const,rules) index = do
    x <- randomPermutation (const)
    let foundBindRule= do findBindingRule pred x 
    case foundBindRule of 
        Nothing -> return Nothing
        Just (rule,rest) ->
            do --Moet variabele nog hernoemen
               let (editedRule,newIndex) = renameVariableClause rule index
               --putStrLn ("rule is " ++ show editedRule)
               --putStrLn ("pred is " ++ show pred)
               let  Just bind = findBinderPred pred (headTerm editedRule) --altijd voldaan door findBindingRule
               return (Just (((applyBinder (body editedRule) bind)),bind,
                (rest,rules),newIndex))
                
stepRule (pred,n) rest (const,rules) index = do
    x <- randomPermutation (rules)
    let foundBindRule= do findBindingRule pred x 
    case foundBindRule of 
        Nothing -> return Nothing
        Just (rule,rest) ->
            do 
               let (editedRule,newIndex) = renameVariableClause rule index
               let  Just bind = findBinderPred pred (headTerm editedRule) --altijd voldaan door findBindingRule
               return (Just (((applyBinder (body editedRule) bind)),bind,
                (const,rest),newIndex))





applyBinderSizeList :: [(Predicate,Int)] -> Binder -> [(Predicate,Int)]

applyBinderSizeList list binder  = zip (applyBinder predList binder) sizeList
    where
    (predList,sizeList) = unzip list
    
    
maybeAppend :: Maybe a -> Maybe b -> (a->b->b) ->Maybe b

maybeAppend (Just a) (Just b) f = Just (f a b )

maybeAppend _ _ _= Nothing
    
   
   
   
   