import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

data Kardinaliteit = Integer deriving (Eq, Show)

data Name = String deriving (Eq, Show)

data Term = Empty | 
            MkTerm { 
            name :: String ,
            kardinaliteit :: Integer ,
            values :: [Term]
            }
            | 
            Constant {
            name :: String,
            kardinaliteit :: Integer}  |
            Variable {
            name :: String}
            deriving (Eq, Show)


--Elke buitenste is een predikaat deze bevat termen als argumenten
data Predicate = MkPredicate {
    nameOfPred :: String ,
    kardinaliteitOfPred :: Integer ,
    valuesOfPred :: [Term] }
    deriving (Eq, Show)
            {- Een term bevat een 
naam de kardinaliteit (of het aantal termen het bezit) en de bijhorende termen 
Empty geeft een fout aan, of een valse staat.
-}
instance Ord Term where -- verwacht namen zijn uniek
    term1 `compare` term2  = (name term1) `compare` (name term2)


type Binder = Map Term Term


--data Value a = MkValue a deriving (Eq, Show)

data Clause = Rule
              {headTerm :: Predicate ,
              body :: [Predicate] }
              | Fact 
              {headTerm :: Predicate}    
              deriving (Eq, Show)

type Scheme = Map String (Set [Term])

data Program = MkProgram [Clause]
    

test4 = print (addToCorrectScheme p3 m3)
        where
        t1 = Constant "a" 0 
        t2 = Constant "c" 0
        t3 = MkTerm "b" 1 [t1] 
        p1 = MkPredicate "a" 1 [t1]
        p2 = MkPredicate "b" 1 [t2]
        p3 = MkPredicate "c" 1 [t3]
        m =  Map.empty
        m1 = Map.insert "a" (Set.empty) m 
        m2 = Map.insert "b" (Set.empty) m1
        m3 = Map.insert "c" (Set.empty) m2

        
{-test5 = print (show (unification t1 t2 r))
    where
    t1 = Variable "a"  
    t2 = Constant "b" 0 
    --t1 = MkPredicate "elder" 1 [b]
    --t2 = MkPredicate "elder" 1 [a]
    --t3 = MkPredicate "c" 1 [b] 
    r = Rule t2 [t3,t2] 
  -}  
test6 = print (show (findNewPred r m1))
    where 
    t1 = Constant "a" 0 
    t2 = MkPredicate "b" 1 [Variable "x"]
    t3 = MkPredicate "c" 1 [Variable "x"] 
    r = Rule t3 [t2]
    m = Map.empty
    m1 = Map.insert "b" (Set.fromList [[t1]]) m 
    
test7 = print (bottom_upAlgorithm program 10)
    where
    p1 = MkPredicate "Person" 1 [(Constant "ann" 0)]
    p2 = MkPredicate "Person" 1 [(Constant "betrand" 0)]
    p3 = MkPredicate "Person" 1 [(Constant "charles" 0)]
    p4 = MkPredicate "Person" 1 [(Constant "dorothy" 0)]
    p5 = MkPredicate "Person" 1 [(Constant "evelyn" 0)]
    p6 = MkPredicate "Person" 1 [(Constant "fred" 0)]
    p7 = MkPredicate "Person" 1 [(Constant "george" 0)]
    p8 = MkPredicate "Person" 1 [(Constant "hilary" 0)]
    pa1 = MkPredicate "Parent" 2 [(Constant "dorothy" 0),(Constant "george" 0)]
    pa2 = MkPredicate "Parent" 2 [(Constant "evelyn" 0),(Constant "george" 0)]
    pa3 = MkPredicate "Parent" 2 [(Constant "betrand" 0),(Constant "dorothy" 0)]
    pa4 = MkPredicate "Parent" 2 [(Constant "ann" 0),(Constant "dorothy" 0)]
    pa5 = MkPredicate "Parent" 2 [(Constant "ann" 0),(Constant "hilary" 0)]
    pa6 = MkPredicate "Parent" 2 [(Constant "charles" 0),(Constant "evelyn" 0)]
    f1 = Fact p1
    f2 = Fact p2
    f3 = Fact p3
    f4 = Fact p4
    f5 = Fact p5
    f6 = Fact p6
    f7 = Fact p7
    f14 = Fact p8
    f8 = Fact pa1
    f9 = Fact pa2
    f10 = Fact pa3
    f11 = Fact pa4
    f12 = Fact pa5
    f13 = Fact pa6
    r1 = Rule (MkPredicate "sgc" 2 [(Variable "X"),(Variable "X")]) [(MkPredicate "Person" 1 [(Variable "X")] )]
    r2 = Rule (MkPredicate "sgc" 2 [(Variable "X"),(Variable "Y")]) [(MkPredicate "Parent" 2 [(Variable "X"),(Variable "X1")] ),
        (MkPredicate "sgc" 2 [(Variable "X1"),(Variable "Y1")]),
        (MkPredicate "Parent" 2 [(Variable "Y"),(Variable "Y1")] )]
    program = MkProgram [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,r1,r2]
    
{-Manier om juiste variabele te zoeken: 1 check of alle elementen in regel ook in bottom-up set zitten
    2. Ga alle mogelijke manieren bekijken om body van regel te voldoen (mss aparte lijst per term naam bijhouden)
    3. Voer een unificatie uit op de term en de body => gefaald probeer andere variabele
    4. Werkt wel voeg Head toe aan nieuwe elementen die aan het einde van de iteratie wordt toegevoegd aan de totale lijst
    
 
 -}   

--Unificatie denk let Martelli - montenari algoritme



getSchemeValues ::  String -> Scheme -> Maybe (Set [Term])

getSchemeValues relation scheme = Map.lookup relation scheme 


findNewPred :: Clause -> Scheme -> [Predicate]

findNewPred (Fact x) _ = [x]

findNewPred (Rule x []) scheme = [x] 


findNewPred (Rule x (y:ys)) scheme =case z of
    Just posValueOfy -> (foldl (\acc a -> let
        binder = findBinderArguments (valuesOfPred y) a
        newRule = bindRule binder (Rule x ys)    in
        (case newRule of 
        Just rule -> (findNewPred rule scheme )++ acc
        Nothing -> acc)) [] posValueOfy)
    Nothing -> []
    where
    z = getSchemeValues (nameOfPred y) scheme
    
  

{-
unification :: Term -> Term -> Clause ->  Maybe Clause --(moet variabele allemaal vervangen zodat 2 gekozen termen gelijk zijn)

unification term1 term2 rule = bindRule z rule
    where 
    z= findBinders term1 term2
    
 -}   
    
bindRule :: Maybe Binder -> Clause -> Maybe Clause

bindRule Nothing rule = Nothing

bindRule (Just binder) rule = Just (Map.foldrWithKey (changeVariableOfRule) rule binder) 


    
    
    
findBinders :: Term -> Term -> Maybe Binder 

findBinders (Variable x) bindingTerm = Just (Map.singleton (Variable x) bindingTerm )

findBinders (Constant x 0) bindingTerm 
    | (name bindingTerm) == x = Just Map.empty
    | otherwise = Nothing 

findBinders term bindingTerm 
    | (name term) == (name bindingTerm) = findBinderArguments (values term) (values bindingTerm)
    | otherwise = Nothing
    
    
    
findBinderArguments :: [Term] -> [Term] -> Maybe Binder --Pre unificatie is mogelijk

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

addToBinder ((Variable v),term) binder = Map.insert (Variable v) term binder
 
    

-- zoek de scheme waar waarde moet toegevoegd worden
addToCorrectScheme :: Predicate -> Scheme -> Scheme 

--addToCorrectScheme (Constant _ _) scheme = error "Constante waarde" -- Zou error moeten geven

--addToCorrectScheme (Variable _) scheme = error "Variabele waarde"

addToCorrectScheme pred m = Map.insertWith (Set.union) (nameOfPred pred) (Set.insert (valuesOfPred pred) Set.empty) m

 
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

changeVariableInPredicateList (y:ys) var bindingTerm = (changeVariableInPredicate y var bindingTerm) : (changeVariableInPredicateList ys var bindingTerm)


changeVariable :: Term ->  Term -> Term -> Term

changeVariable (Variable y) (Variable x) bindingTerm = 
                if ((Variable x)==(Variable y)) then
                     bindingTerm -- bij variabele vervang je deze
                else
                     Variable y
changeVariable (Constant a b) (Variable x) bindingTerm = Constant a b

changeVariable (MkTerm nameTerm kard valueOfTerm) (Variable x) bindingTerm = MkTerm nameTerm kard (changeVariableTermList valueOfTerm (Variable x) bindingTerm)
    
changeVariable termToChange _ bindingTerm = error "Verwacht een Variabele geen term"



changeVariableTermList :: [Term] -> Term -> Term -> [Term]

changeVariableTermList (y:ys) (Variable x) bindingTerm = (changeVariable y (Variable x) bindingTerm) : (changeVariableTermList ys (Variable x) bindingTerm)

changeVariableTermList [] (Variable x) bindingTerm = []

changeVariableTermList _ _ _ = error "Verwacht een Variabele geen term"



fireAllRules :: Program -> Scheme -> [Predicate]

fireAllRules (MkProgram []) listOfSchemes = []

fireAllRules (MkProgram (firstClause:restOfClauses)) scheme = 
    (findNewPred firstClause scheme) ++ (fireAllRules (MkProgram restOfClauses) scheme)


bottom_upAlgorithm :: Program -> Integer ->  Scheme 

bottom_upAlgorithm _ 0  = Map.empty 

bottom_upAlgorithm program integer = bottomUpHelper program integer Map.empty 



bottomUpHelper:: Program -> Integer ->  Scheme -> Scheme

bottomUpHelper _ 0 scheme = scheme

bottomUpHelper program n scheme = bottomUpHelper program (n-1) newScheme
    where
    newPreds = fireAllRules program scheme
    newScheme = addListToCorrectScheme newPreds scheme
