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


-- search in scheme for predicate with given name
getSchemeValues ::  String -> Scheme -> Maybe (Set [Term])

getSchemeValues = Map.lookup 



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

-- We gebruiken het principe van een binonium van Newton we geven een lijst van [0,1] mee
-- Indien een 0 dan neem je een element uit je oude lijst en ga je recursief verder
-- Indien een 1 dan neem je een element uit je nieuwe lijst  en dan ga je de rest van je elementen uit de totale lijst halen
findNewPred rule@(Rule x (y:ys)) oldScheme differenceScheme = 
    (foldl (\acc f -> ( f rule oldScheme differenceScheme) ++   acc) [] [newPredChoosingOld,newPredChoosingNew])

-- Neem de termen van een predikaat uit een oude scheme
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
    
--Neem de termen van een predikaat uit een nieuwe scheme hierna zijn er geen restricties dat er minstens 1 nieuw moet zijn
newPredChoosingNew :: Clause -> Scheme -> Scheme -> [Predicate]
    
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
  
--Neem de termen van een predikaat uit een oude of een nieuwe scheme    
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
    
    
chooseAllOrNewScheme :: Integer ->(Clause -> Scheme -> Scheme -> [Predicate])

chooseAllOrNewScheme 0  = newPredChoosingOld 

chooseAllOrNewScheme 1 = newPredChoosingNew 
    
    
-- zoek de scheme waar waarde moet toegevoegd worden
addToCorrectScheme :: Predicate -> Scheme -> Scheme 

addToCorrectScheme pred = Map.insertWith Set.union (nameOfPred pred) (Set.insert (valuesOfPred pred) Set.empty)

 
addListToCorrectScheme :: [Predicate] -> Scheme -> Scheme

addListToCorrectScheme [] scheme = scheme

addListToCorrectScheme (x:xs) scheme = addListToCorrectScheme xs z
    where 
    z =addToCorrectScheme x scheme



fireAllRules :: Program -> Scheme -> Scheme -> [Predicate]

fireAllRules (MkProgram []) oldScheme differenceScheme = []


fireAllRules (MkProgram (firstClause:restOfClauses)) oldScheme differenceScheme =  
     (newPreds ++ fireAllRules (MkProgram restOfClauses) oldScheme differenceScheme)
     where 
     newPreds= findNewPred firstClause oldScheme differenceScheme
     predsEdited = (foldr (\x acc ->fst (rename x 0) : acc) [] newPreds)    
    

 
unionScheme :: Scheme -> Scheme -> Scheme

unionScheme = Map.unionWith Set.union


maybeSetDif :: Set[Term] -> Set [Term] -> Maybe (Set [Term]) 

maybeSetDif x y = Just $ Set.difference x y
    

    