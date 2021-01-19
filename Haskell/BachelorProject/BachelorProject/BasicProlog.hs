
module BasicProlog where
      
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

data Kardinaliteit = Integer deriving (Eq, Show)



data Term = MkTerm { 
            name :: String ,
            kardinaliteit :: Integer ,
            values :: [Term]
            }
            | 
            Variable {
            name :: String}
            deriving (Ord)


instance Eq Term  where 
   (==) (Variable x) (Variable y) = (x == y)
   x == y = ((name x)==(name y)) && termValuesEqual (values x) (values y)


instance Show Term  where
    show (Variable x) = x
    show (MkTerm nameT 0 _) = nameT
    show (MkTerm nameT n list) = nameT ++ "(" ++ showTermList list ++ ")"
    
    

showTermList :: [Term] -> String

showTermList [x] = show x

showTermList (x:xs) = show x ++ "," ++ showTermList xs 



termValuesEqual :: [Term] -> [Term] -> Bool

termValuesEqual [] [] = True

termValuesEqual (x:xs) (y:ys) = (x == y) && termValuesEqual xs ys



--Elke buitenste is een predikaat deze bevat termen als argumenten
data Predicate = MkPredicate {
                    nameOfPred :: String ,
                    kardinaliteitOfPred :: Integer ,
                    valuesOfPred :: [Term] }
    
instance Eq Predicate  where 
   x == y = ((nameOfPred x)==(nameOfPred y)) && termValuesEqual (valuesOfPred x) (valuesOfPred y)   
    
    
instance Show Predicate  where
    show (MkPredicate nameP 0 _) = nameP
    show (MkPredicate nameP n list) = nameP ++ "(" ++ showTermList list ++ ")"
            {- Een term bevat een 
naam de kardinaliteit (of het aantal termen het bezit) en de bijhorende termen 
Empty geeft een fout aan, of een valse staat.
-}

type Binder = Map Term Term


--data Value a = MkValue a deriving (Eq, Show)

data Clause = Rule
              {headTerm :: Predicate ,
              body :: [Predicate] }    
              deriving (Eq, Show)

type Scheme = Map String (Set [Term])

newtype Program = MkProgram [Clause]

releaseProgram :: Program -> [Clause]

releaseProgram (MkProgram list) = list
    

    

{-Manier om juiste variabele te zoeken: 1 check of alle elementen in regel ook in bottom-up set zitten
    2. Ga alle mogelijke manieren bekijken om body van regel te voldoen (mss aparte lijst per term naam bijhouden)
    3. Voer een unificatie uit op de term en de body => gefaald probeer andere variabele
    4. Werkt wel voeg Head toe aan nieuwe elementen die aan het einde van de iteratie wordt toegevoegd aan de totale lijst
    
 
 -}   

-- Append a program to another program
appendProgram :: Program -> Program -> Program

appendProgram (MkProgram p1) (MkProgram p2) = MkProgram (p1 ++ p2)


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
         binder = findBinderArguments (valuesOfPred y) a in
        (case binder of
            Just bind -> pred : acc
                where
                (Rule pred _) = bindRule (Rule x []) bind
            Nothing ->  acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) differenceScheme

-- We gebruiken het principe van een binonium van Newton we geven een lijst van [0,1] mee
-- Indien een 0 dan neem je een element uit je oude lijst en ga je recursief verder
-- Indien een 1 dan neem je een element uit je nieuwe lijst  en dan ga je de rest van je elementen uit de totale lijst halen
findNewPred (Rule x (y:ys)) oldScheme differenceScheme =
    (foldl (\acc f -> ( f (Rule x (y:ys)) oldScheme differenceScheme) ++   acc) [] [newPredChoosingOld,newPredChoosingNew])

-- Neem de termen van een predikaat uit een oude scheme
newPredChoosingOld :: Clause -> Scheme -> Scheme -> [Predicate]

newPredChoosingOld (Rule x (y:ys)) oldScheme differenceScheme = 
    case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder = findBinderArguments (valuesOfPred y) a in
        (case binder of
        Just bind -> findNewPred newRule oldScheme differenceScheme ++ acc
            where
            newRule =  bindRule (Rule x ys) bind 
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) oldScheme
    
--Neem de termen van een predikaat uit een nieuwe scheme hierna zijn er geen restricties dat er minstens 1 nieuw moet zijn
newPredChoosingNew :: Clause -> Scheme -> Scheme -> [Predicate]
    
newPredChoosingNew (Rule x (y:ys)) oldScheme differenceScheme = 
    case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
         binder = findBinderArguments (valuesOfPred y) a in
        (case binder of
        Just bind -> findNewPredUseAll newRule (unionScheme oldScheme differenceScheme) ++ acc
            where
            newRule =  bindRule (Rule x ys) bind 
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z = getSchemeValues (nameOfPred y) differenceScheme
  
--Neem de termen van een predikaat uit een oude of een nieuwe scheme    
findNewPredUseAll :: Clause -> Scheme -> [Predicate]

findNewPredUseAll (Rule x []) _ = [x]

findNewPredUseAll (Rule x (y:ys)) scheme =  case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder = findBinderArguments (valuesOfPred y) a in
        (case binder of
        Just bind -> findNewPredUseAll newRule scheme ++ acc
            where
            newRule =  bindRule (Rule x ys) bind 
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) scheme
    
    
chooseAllOrNewScheme :: Integer ->(Clause -> Scheme -> Scheme -> [Predicate])

chooseAllOrNewScheme 0  = newPredChoosingOld 

chooseAllOrNewScheme 1 = newPredChoosingNew 
    
    

    
--Gegeven een binder pas deze toe op de regel.     

bindRule :: Clause -> Binder  -> Clause

bindRule  = Map.foldrWithKey changeVariableOfRule 


bindRuleList :: Binder -> [Clause] ->  [Clause]

bindRuleList binder  = foldr (\x acc-> (bindRule x binder ):acc) [] 

 
 
--Zoek een binder voor de term indien ze verschillend zijn geef nothing terug
findBinders :: Term -> Term -> Maybe Binder 

-- Hier gaat het fout omdat variabele niet worden hernoemd
findBinders (Variable x) bindingTerm = Just (Map.singleton (Variable x) bindingTerm )

findBinders term (Variable y) = Just (Map.singleton (Variable y) term )

findBinders term bindingTerm 
    | name term == name bindingTerm = findBinderArguments (values term) (values bindingTerm)
    | otherwise = Nothing
    
    
    
findBinderArguments :: [Term] -> [Term] -> Maybe Binder 

findBinderArguments [] [] = Just Map.empty

findBinderArguments _ [] = Nothing

findBinderArguments [] _ = Nothing

findBinderArguments (x:xs) (y:ys) = appendBinder z k
    where
    z = findBinders x y 
    k = findBinderArguments xs ys
    

findBinderPred :: Predicate -> Predicate -> Maybe Binder

findBinderPred pred1 pred2 
    | nameOfPred pred1 == nameOfPred pred2 = findBinderArguments (valuesOfPred pred1) (valuesOfPred pred2)
    | otherwise = Nothing
        

    
appendBinder :: Maybe Binder -> Maybe Binder -> Maybe Binder

appendBinder binder1 binder2 = do 
    x <- binder1
    y <- binder2
    Just (Map.union x y)


addToBinder :: (Term,Term) -> Binder -> Binder

addToBinder (Variable v,term) = Map.insert (Variable v) term
 
    

-- zoek de scheme waar waarde moet toegevoegd worden
addToCorrectScheme :: Predicate -> Scheme -> Scheme 

addToCorrectScheme pred = Map.insertWith Set.union (nameOfPred pred) (Set.insert (valuesOfPred pred) Set.empty)

 
addListToCorrectScheme :: [Predicate] -> Scheme -> Scheme

addListToCorrectScheme [] scheme = scheme

addListToCorrectScheme (x:xs) scheme = addListToCorrectScheme xs z
    where 
    z =addToCorrectScheme x scheme



changeVariableOfRule ::   Term -> Term -> Clause  -> Clause

changeVariableOfRule (Variable x) bindingTerm  r  = Rule (changeVariableInPredicate (headTerm r) (Variable x) bindingTerm) (changeVariableInPredicateList (body r) (Variable x) bindingTerm)

changeVariableOfRule _ bindingTerm r = error "Verwacht een Variabele geen term"



changeVariableInPredicate :: Predicate -> Term -> Term -> Predicate

changeVariableInPredicate (MkPredicate name kard termList) var replacingTerm = MkPredicate name kard (changeVariableTermList termList var replacingTerm)


changeVariableInPredicateList :: [Predicate] -> Term -> Term -> [Predicate]

changeVariableInPredicateList [] var bindingTerm = []

changeVariableInPredicateList list var bindingTerm = map (\y -> changeVariableInPredicate y var bindingTerm) list--changeVariableInPredicate y var bindingTerm : changeVariableInPredicateList ys var bindingTerm


changeVariable :: Term ->  Term -> Term -> Term

changeVariable (Variable y) (Variable x) bindingTerm = 
                if Variable x == Variable y then
                     bindingTerm -- bij variabele vervang je deze
                else
                     Variable y

changeVariable (MkTerm nameTerm kard valueOfTerm) (Variable x) bindingTerm = MkTerm nameTerm kard (changeVariableTermList valueOfTerm (Variable x) bindingTerm)
    
changeVariable termToChange _ bindingTerm = error "Verwacht een Variabele geen term"



changeVariableTermList :: [Term] -> Term -> Term -> [Term]

changeVariableTermList (y:ys) (Variable x) bindingTerm = changeVariable y (Variable x) bindingTerm : changeVariableTermList ys (Variable x) bindingTerm

changeVariableTermList [] (Variable x) bindingTerm = []

changeVariableTermList _ _ _ = error "Verwacht een Variabele geen term"



fireAllRules :: Program -> Scheme -> Scheme -> [Predicate]

fireAllRules (MkProgram []) oldScheme differenceScheme = []

fireAllRules (MkProgram (firstClause:restOfClauses)) oldScheme differenceScheme = 
     findNewPred firstClause oldScheme differenceScheme ++ fireAllRules (MkProgram restOfClauses) oldScheme differenceScheme

 
unionScheme :: Scheme -> Scheme -> Scheme

unionScheme = Map.unionWith Set.union


maybeSetDif :: Set[Term] -> Set [Term] -> Maybe (Set [Term]) 

maybeSetDif x y = Just $ Set.difference x y



createFacts :: [Predicate] -> [Clause]

createFacts [] = []

createFacts (x:xs) = (Rule x []) : createFacts xs




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


eval :: Term -> Term

eval t = case t' of
        Just t'-> eval t'
        Nothing -> t
    where
    t'=step (name t) t

-- Eerste property eval term => value
property1 :: Term -> Bool

property1 term = value (name t) t
    where
    t = eval term

--tweede property ofwel vereenvoudiging mogelijk ofwel value
property2 :: Term -> Bool

property2 term = case t of
        Just t' -> True
        Nothing -> value (name term) term
    where
    t= step (name term) term
    
--De 3de property zegt dat na de vereenvoudigen moet de term nog steeds aan hastype voldoen    
property3 :: Predicate -> Set [Term] -> Bool

property3 (MkPredicate "hasType" 2 [term,typeOfTerm]) scheme = Set.member [t,typeOfTerm] scheme 
    where
    t = eval term
    





