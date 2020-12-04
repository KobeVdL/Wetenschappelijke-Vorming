import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

data Kardinaliteit = Integer deriving (Eq, Show)

data Name = String deriving (Eq, Show)

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
{-instance Ord Term where -- verwacht namen zijn uniek
    term1 `compare` term2  = 
    where
        x = name term1 `compare` name term2
    
compareTerms :: [Term] -> [Term] -> Ord

compareTerms [] [] = EQ

CompareTerm :: Term -> Term ->Ord
-}



type Binder = Map Term Term


--data Value a = MkValue a deriving (Eq, Show)

data Clause = Rule
              {headTerm :: Predicate ,
              body :: [Predicate] }    
              deriving (Eq, Show)

type Scheme = Map String (Set [Term])

newtype Program = MkProgram [Clause]
    

test4 = print (addToCorrectScheme p3 m3)
        where
        t1 = MkTerm "a" 0 []
        t2 = MkTerm "c" 0 []
        t3 = MkTerm "b" 1 [t1] 
        p1 = MkPredicate "a" 1 [t1]
        p2 = MkPredicate "b" 1 [t2]
        p3 = MkPredicate "c" 1 [t3]
        m =  Map.empty
        m1 = Map.insert "a" Set.empty m 
        m2 = Map.insert "b" Set.empty m1
        m3 = Map.insert "c" Set.empty m2

        
{-test5 = print (show (unification t1 t2 r))
    where
    t1 = Variable "a"  
    t2 = Constant "b" 0 
    --t1 = MkPredicate "elder" 1 [b]
    --t2 = MkPredicate "elder" 1 [a]
    --t3 = MkPredicate "c" 1 [b] 
    r = Rule t2 [t3,t2] 
  -}  
test6 = print (show (findNewPred r Map.empty m1))
    where 
    t1 = MkTerm "a" 0 []
    t2 = MkPredicate "b" 1 [Variable "x"]
    t3 = MkPredicate "c" 1 [Variable "x"] 
    r = Rule t3 [t2]
    m = Map.empty
    m1 = Map.insert "b" (Set.fromList [[t1]]) m 
    
test7 = print (semiNaiveBottomUp program 1 Map.empty Map.empty) --test met even getallen implementeren
    where
    p1 = MkPredicate "Person" 1 [MkTerm "ann" 0 []]
    p2 = MkPredicate "Person" 1 [MkTerm "betrand" 0 []]
    p3 = MkPredicate "Person" 1 [MkTerm "charles" 0 []]
    p4 = MkPredicate "Person" 1 [MkTerm "dorothy" 0 []]
    p5 = MkPredicate "Person" 1 [MkTerm "evelyn" 0 []]
    p6 = MkPredicate "Person" 1 [MkTerm "fred" 0 []]
    p7 = MkPredicate "Person" 1 [MkTerm "george" 0 []]
    p8 = MkPredicate "Person" 1 [MkTerm "hilary" 0 []]
    pa1 = MkPredicate "Parent" 2 [MkTerm "dorothy" 0 [],MkTerm "george" 0 []]
    pa2 = MkPredicate "Parent" 2 [MkTerm "evelyn" 0 [],MkTerm "george" 0 []]
    pa3 = MkPredicate "Parent" 2 [MkTerm "betrand" 0 [],MkTerm "dorothy" 0 []]
    pa4 = MkPredicate "Parent" 2 [MkTerm "ann" 0 [],MkTerm "dorothy" 0 []]
    pa5 = MkPredicate "Parent" 2 [MkTerm "ann" 0 [],MkTerm"hilary" 0 []]
    pa6 = MkPredicate "Parent" 2 [MkTerm "charles" 0 [],MkTerm "evelyn" 0 []]
    f1 = Rule p1 []
    f2 = Rule p2 []
    f3 = Rule p3 []
    f4 = Rule p4 []
    f5 = Rule p5 []
    f6 = Rule p6 []
    f7 = Rule p7 []
    f14 = Rule p8 []
    f8 = Rule pa1 []
    f9 = Rule pa2 []
    f10 = Rule pa3 []
    f11 = Rule pa4 []
    f12 = Rule pa5 []
    f13 = Rule pa6 []
    r1 = Rule (MkPredicate "sgc" 2 [Variable "X",Variable "X"]) [MkPredicate "Person" 1 [Variable "X"] ]
    r2 = Rule (MkPredicate "sgc" 2 [Variable "X",Variable "Y"]) [MkPredicate "Parent" 2 [Variable "X",Variable "X1"],
        MkPredicate "sgc" 2 [Variable "X1",Variable "Y1"],
        MkPredicate "Parent" 2 [Variable "Y",Variable "Y1"]]
    program = MkProgram [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,r1,r2]
    



    
    
test8 = print (semiNaiveBottomUp program 8 Map.empty Map.empty)
    where
    zero = MkTerm "zero" 0 []
    evenBasic = Rule(MkPredicate "even" 1 [zero]) []
    evenRecursive = Rule (MkPredicate "even" 1 [MkTerm "succ" 1 [MkTerm "succ" 1 [Variable "X"]]]) [MkPredicate "even" 1 [Variable "X"]]
    program = MkProgram [evenBasic, evenRecursive]
    
{-Manier om juiste variabele te zoeken: 1 check of alle elementen in regel ook in bottom-up set zitten
    2. Ga alle mogelijke manieren bekijken om body van regel te voldoen (mss aparte lijst per term naam bijhouden)
    3. Voer een unificatie uit op de term en de body => gefaald probeer andere variabele
    4. Werkt wel voeg Head toe aan nieuwe elementen die aan het einde van de iteratie wordt toegevoegd aan de totale lijst
    
 
 -}   

--Unificatie denk let Martelli - montenari algoritme



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
        binder = findBinderArguments (valuesOfPred y) a
        newRule =  bindRule binder (Rule x []) in
        (case  newRule of 
        Just (Rule pred _) ->  pred : acc
        Nothing ->  acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) differenceScheme

-- We gebruiken het principe van een binonium van Newton we geven een lijst van [0,1] mee
-- Indien een 0 dan neem je een element uit je oude lijst en ga je recursief verder
-- Indien een 1 dan neem je een element uit je nieuwe lijst  en dan ga je de rest van je elementen uit de totale lijst halen
findNewPred (Rule x (y:ys)) oldScheme differenceScheme =
    foldl (\acc f -> ( f (Rule x (y:ys)) oldScheme differenceScheme) ++   acc) [] [newPredChoosingOld,newPredChoosingNew]


newPredChoosingOld :: Clause -> Scheme -> Scheme -> [Predicate]

newPredChoosingOld (Rule x (y:ys)) oldScheme differenceScheme = 
    case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder =  findBinderArguments (valuesOfPred y) a
        newRule =  bindRule binder (Rule x ys)    in
        (case newRule of 
        Just rule -> findNewPred rule oldScheme differenceScheme ++ acc
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) oldScheme
    
newPredChoosingNew :: Clause -> Scheme -> Scheme -> [Predicate]
    
newPredChoosingNew (Rule x (y:ys)) oldScheme differenceScheme = 
    case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder = findBinderArguments (valuesOfPred y) a
        newRule = bindRule binder (Rule x ys)    in
        (case newRule of 
        Just rule -> findNewPredUseAll rule (unionScheme oldScheme differenceScheme) ++ acc
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) oldScheme
  
    
findNewPredUseAll :: Clause -> Scheme -> [Predicate]

findNewPredUseAll (Rule x []) _ = [x]

findNewPredUseAll (Rule x (y:ys)) scheme =  case z of
    Just posValueOfy -> foldl (\acc a -> let --concatmap acc niet meer doorgeven
        binder = findBinderArguments (valuesOfPred y) a
        newRule = bindRule binder (Rule x ys)    in
        (case newRule of 
        Just rule -> findNewPredUseAll rule scheme ++ acc
        Nothing -> acc)) [] posValueOfy
    Nothing -> []
    where
    z =  getSchemeValues (nameOfPred y) scheme
    
    
chooseAllOrNewScheme :: Integer ->(Clause -> Scheme -> Scheme -> [Predicate])

chooseAllOrNewScheme 0  = newPredChoosingOld 

chooseAllOrNewScheme 1 = newPredChoosingNew 
  

{-
unification :: Term -> Term -> Clause ->  Maybe Clause --(moet variabele allemaal vervangen zodat 2 gekozen termen gelijk zijn)

unification term1 term2 rule = bindRule z rule
    where 
    z= findBinders term1 term2
    
 -}   
    
bindRule :: Maybe Binder -> Clause -> Maybe Clause --fmap gebruiken Aanpassen naar binder->clause->clause

bindRule Nothing rule = Nothing


--TODO hier zit fout
bindRule (Just binder) rule = Just  (Map.foldrWithKey changeVariableOfRule rule binder)


    
    
    
findBinders :: Term -> Term -> Maybe Binder 

findBinders (Variable x) bindingTerm = Just (Map.singleton (Variable x) bindingTerm )

findBinders term bindingTerm 
    | name term == name bindingTerm = findBinderArguments (values term) (values bindingTerm)
    | otherwise = Nothing
    
    
    
findBinderArguments :: [Term] -> [Term] -> Maybe Binder 

findBinderArguments [] [] = Just Map.empty

findBinderArguments (x:xs) (y:ys) = appendBinder z k
    where
    z = findBinders x y 
    k = findBinderArguments xs ys
    
    
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

{-
bottomUpAlgorithm :: Program -> Integer ->  Scheme -- aanpassen naar semi-naive

bottomUpAlgorithm _ 0  = Map.empty 

bottomUpAlgorithm program integer = bottomUpHelper program integer Map.empty 



bottomUpHelper:: Program -> Integer ->  Scheme -> Scheme

bottomUpHelper _ 0 scheme = scheme

bottomUpHelper program n scheme = bottomUpHelper program (n-1) newScheme
    where
    newPreds = fireAllRules program scheme
    newScheme = addListToCorrectScheme newPreds scheme
 -} 
 
unionScheme :: Scheme -> Scheme -> Scheme

unionScheme = Map.unionWith Set.union


maybeSetDif :: Set[Term] -> Set [Term] -> Maybe (Set [Term]) 

maybeSetDif x y = Just $ Set.difference x y

semiNaiveBottomUp :: Program -> Integer -> Scheme -> Scheme -> Scheme

semiNaiveBottomUp _ 0 oldScheme differenceScheme = unionScheme oldScheme differenceScheme

semiNaiveBottomUp program n oldScheme differenceScheme = semiNaiveBottomUp program (n-1) newScheme newFoundElements
    where
    newPreds = fireAllRules program oldScheme differenceScheme
    foundElements =  addListToCorrectScheme newPreds Map.empty
    newScheme =    unionScheme oldScheme differenceScheme
    allElements =  unionScheme newScheme foundElements
    newFoundElements =  Map.differenceWith (maybeSetDif) allElements newScheme --Map.insertWith Set.union (nameOfPred pred) (Set.insert (valuesOfPred pred) Set.empty)
    
  