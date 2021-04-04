module BottomUp where



import BasicProlog
      
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


type Scheme = Map String (Set [Term])

-- creates a scheme with a bottom-up approuch, 
-- A scheme holds for each type of Predicate written in the rules all possible values for it
-- Bottom-up first start by all facts into the scheme, in the next step its going to use these facts for binding
-- with the body of rules if possible, if so adds the head to the scheme
-- bottom-up stops after n iterations (grows very fast)
semiNaiveBottomUp :: Program -> Int -> Scheme -> Scheme -> Scheme

semiNaiveBottomUp _ (-1) oldScheme differenceScheme = unionScheme oldScheme differenceScheme

semiNaiveBottomUp program n oldScheme differenceScheme = semiNaiveBottomUp program (n-1) newScheme newFoundElements
    where
    newPreds = fireAllRules program oldScheme differenceScheme
    foundElements =  addListToCorrectScheme newPreds Map.empty
    newScheme =    unionScheme oldScheme differenceScheme
    allElements =  unionScheme newScheme foundElements
    newFoundElements =  Map.differenceWith (maybeSetDif) allElements newScheme 



-- search in scheme for predicate with given name
getSchemeValues ::  String -> Scheme -> Maybe (Set [Term])

getSchemeValues = Map.lookup 


-- find new preds for given rule and given schemes, if the new elements are empty
-- returns the facts, otherwise find all possible combinations of binding with a values in the scheme
-- in the semi-naïve approuch there is one chosen from the new generated preds , the rest doesn't matter 
findNewPred :: Clause -> Scheme -> Scheme -> [Predicate]

--Feiten worden toegevoegd als er geen nieuwe elementen zijn
findNewPred (Rule x []) _ differenceScheme 
    | Map.null differenceScheme = [x]
    | otherwise = []


-- In het geval van een regel gebruik steeds minstens 1 van de nieuwe elementen
-- Hierdoor ga je geen elementen overlopen die je daarvoor ook al een keer hebt gevonden

--Bij de laatste predikaat ga je altijd een nieuw element gebruiken als daarvoor nog niet is gebeurd 
findNewPred (Rule x [y]) oldScheme differenceScheme =  case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
         binder = findBinder (valuesOfPred y) a in
        (case binder of
            Just bind -> pred : acc
                where
                (Rule pred _) = bindValue (Rule x []) bind
            Nothing ->  acc)) [] posValueOfy
    Nothing -> []
    where
    z = getSchemeValues (nameOfPred y) differenceScheme

-- We use the principle of a binonium of Newton, we give a list of [0,1]
-- If 0 then you take an element from your old list and continue recursively
-- If a 1 then you take an element from your new list and then you take the rest of your elements from the total list-- We gebruiken het principe van een binonium van Newton we geven een lijst van [0,1] mee
findNewPred rule@(Rule x (y:ys)) oldScheme differenceScheme = 
    (foldl (\acc f -> ( f rule oldScheme differenceScheme) ++   acc) [] [newPredChoosingOld,newPredChoosingNew])

-- Take the terms of an old scheme
newPredChoosingOld :: Clause -> Scheme -> Scheme -> [Predicate]

newPredChoosingOld (Rule x (y:ys)) oldScheme differenceScheme = 
    case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder = findBinder (valuesOfPred y) a in
        (case binder of
        Just bind -> findNewPred newRule oldScheme differenceScheme ++ acc
            where
            newRule =  bindValue (Rule x ys) bind 
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) oldScheme
    
-- Take the terms of a predicate from a new scheme. After this there are no restrictions that at least 1 must be newnewPredChoosingNew :: Clause -> Scheme -> Scheme -> [Predicate]
newPredChoosingNew (Rule x (y:ys)) oldScheme differenceScheme = 
    case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
         binder = findBinder (valuesOfPred y) a in
        (case binder of
        Just bind -> findNewPredUseAll newRule (unionScheme oldScheme differenceScheme) ++ acc
            where
            newRule =  bindValue (Rule x ys) bind 
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z = getSchemeValues (nameOfPred y) differenceScheme
  
--Take terms either of an old or an new scheme    
findNewPredUseAll :: Clause -> Scheme -> [Predicate]

findNewPredUseAll (Rule x []) _ = [x]

findNewPredUseAll (Rule x (y:ys)) scheme =  case z of
    Just posValueOfy -> Set.foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder = findBinder (valuesOfPred y) a in
        (case binder of
        Just bind -> findNewPredUseAll newRule scheme ++ acc
            where
            newRule =  bindValue (Rule x ys) bind 
        Nothing ->  acc)) [] posValueOfy
    Nothing -> []
    where
    z = getSchemeValues (nameOfPred y) scheme
    

    
    
-- searches for the correct scheme where the element needs to be added and add the element to it
addToCorrectScheme :: Predicate -> Scheme -> Scheme 

addToCorrectScheme pred = Map.insertWith Set.union (nameOfPred pred) (Set.insert (valuesOfPred pred) Set.empty)

 
addListToCorrectScheme :: [Predicate] -> Scheme -> Scheme

addListToCorrectScheme [] scheme = scheme

addListToCorrectScheme (x:xs) scheme = addListToCorrectScheme xs z
    where 
    z =addToCorrectScheme x scheme


-- searches for each rule all possible bindings with the given scheme of which
-- one element needs to be from a new scheme
fireAllRules :: Program -> Scheme -> Scheme -> [Predicate]

fireAllRules (MkProgram []) oldScheme differenceScheme = []


fireAllRules (MkProgram (firstClause:restOfClauses)) oldScheme differenceScheme =  
     (newPreds ++ fireAllRules (MkProgram restOfClauses) oldScheme differenceScheme)
     where 
     newPreds= findNewPred firstClause oldScheme differenceScheme
     predsEdited = (foldr (\x acc ->fst (rename x 0) : acc) [] newPreds)    
    

-- take the union of two schemes
unionScheme :: Scheme -> Scheme -> Scheme

unionScheme = Map.unionWith Set.union

-- take the difference of two sets and turn it into a maybe
maybeSetDif :: Set[Term] -> Set [Term] -> Maybe (Set [Term]) 

maybeSetDif x y = Just $ Set.difference x y
    

    