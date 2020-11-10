import Data.Set (Set)
import qualified Data.Set as Set

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
            deriving (Eq, Show) {- Een term bevat een 
naam de kardinaliteit (of het aantal termen het bezit) en de bijhorende termen 
Empty geeft een fout aan, of een valse staat.
-}
instance Ord Term where -- verwacht namen zijn uniek
    term1 `compare` term2  = (name term1) `compare` (name term2)


data Binder = MkBinder {
            getBinder :: [(Term,Term)]
            } | InvalidBinder deriving (Eq, Show)


--data Value a = MkValue a deriving (Eq, Show)

data Clause = Rule
              {headTerm :: Term ,
              body :: [Term] }
              | Fact 
              {headTerm :: Term}    
              | InvalidClause
              deriving (Eq, Show)

data Scheme = MkScheme { 
                  relation :: String ,
                  getSchemeValues :: (Set [Term])
                  } 
               | InvalidScheme deriving (Eq, Show)-- zie datalog hou bij welke values een bepaald predikaat heeft.

data Program = MkProgram [Clause]

fireAllRules :: Program -> [Scheme] -> [Term]

fireAllRules (MkProgram []) listOfSchemes = []

fireAllRules (MkProgram (firstClause:restOfClauses)) listOfSchemes = 
    (findNewTerms firstClause listOfSchemes) ++ (fireAllRules (MkProgram restOfClauses) listOfSchemes)

    
test3 = print (addToScheme [t4] m )
        where
        t1 = Constant "a" 0 
        t2 = Constant "b" 0
        t3 = Constant "c" 0
        t4 = MkTerm "l" 1 [t3]         
        m = MkScheme "a" (Set.fromList [[t1],[t2]])

test4 = print (addToCorrectScheme t3 [m1,m2,m3])
        where
        t1 = Constant "a" 0 
        t2 = Constant "c" 0
        t3 = MkTerm "b" 1 [t1] 
        m1 = MkScheme "a" (Set.fromList [])
        m2 = MkScheme "b" (Set.fromList [])
        m3 = MkScheme "c" (Set.fromList [])
        
test5 = print (show (unification t1 t2 r))
    where
    t1 = Variable "a"  
    t2 = Constant "b" 0 
    t3 = MkTerm "b" 1 [t1] 
    r = Rule t2 [t3,t2] 
    
test6 = print (show (findNewTerms r [scheme]))
    where 
    t1 = Constant "a" 0 
    t2 = MkTerm "b" 1 [Variable "x"]
    t3 = MkTerm "c" 1 [Variable "x"] 
    r = Rule t3 [t2]
    scheme = MkScheme "b" (Set.fromList [[t1]])
    
test7 = print (bottom_upAlgorithm program 1)
    where
    p1 = MkTerm "Person" 1 [(Constant "ann" 0)]
    p2 = MkTerm "Person" 1 [(Constant "betrand" 0)]
    p3 = MkTerm "Person" 1 [(Constant "charles" 0)]
    p4 = MkTerm "Person" 1 [(Constant "dorothy" 0)]
    p5 = MkTerm "Person" 1 [(Constant "evelyn" 0)]
    p6 = MkTerm "Person" 1 [(Constant "fred" 0)]
    p7 = MkTerm "Person" 1 [(Constant "george" 0)]
    p8 = MkTerm "Person" 1 [(Constant "hilary" 0)]
    pa1 = MkTerm "Parent" 2 [(Constant "dorothy" 0),(Constant "george" 0)]
    pa2 = MkTerm "Parent" 2 [(Constant "evelyn" 0),(Constant "george" 0)]
    pa3 = MkTerm "Parent" 2 [(Constant "betrand" 0),(Constant "dorothy" 0)]
    pa4 = MkTerm "Parent" 2 [(Constant "ann" 0),(Constant "dorothy" 0)]
    pa5 = MkTerm "Parent" 2 [(Constant "ann" 0),(Constant "hilary" 0)]
    pa6 = MkTerm "Parent" 2 [(Constant "charles" 0),(Constant "evelyn" 0)]
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
    r1 = Rule (MkTerm "sgc" 2 [(Variable "X"),(Variable "X")]) [(MkTerm "Person" 1 [(Variable "X")] )]
    r2 = Rule (MkTerm "sgc" 2 [(Variable "X"),(Variable "Y")]) [(MkTerm "Parent" 2 [(Variable "X"),(Variable "X1")] ),
        (MkTerm "sgc" 2 [(Variable "X1"),(Variable "Y1")]),
        (MkTerm "Parent" 2 [(Variable "Y"),(Variable "Y1")] )]
    program = MkProgram [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,r1,r2]
    
{-Manier om juiste variabele te zoeken: 1 check of alle elementen in regel ook in bottom-up set zitten
    2. Ga alle mogelijke manieren bekijken om body van regel te voldoen (mss aparte lijst per term naam bijhouden)
    3. Voer een unificatie uit op de term en de body => gefaald probeer andere variabele
    4. Werkt wel voeg Head toe aan nieuwe elementen die aan het einde van de iteratie wordt toegevoegd aan de totale lijst
    
 
 -}   

--Unificatie denk let Martelli - montenari algoritme

findNewTerms :: Clause -> [Scheme] -> [Term]

findNewTerms (Fact x) _ = [x]

findNewTerms InvalidClause schemeList =[]

findNewTerms (Rule x []) schemeList = [x] 

findNewTerms (Rule x (y:ys)) schemeList 
    | (z /= InvalidScheme) =(foldl (\acc a -> let
        binder = findBinderArguments (values y) (a)
        newRule = bindRule binder (Rule x ys)
        in
        (findNewTerms newRule schemeList )++ acc) []) (getSchemeValues z)
    | otherwise = []
    where 
    z = findCorrectScheme y schemeList  
    
findCorrectScheme :: Term -> [Scheme] -> Scheme

findCorrectScheme term [] = InvalidScheme

findCorrectScheme term (x:xs) 
    | (name term) == (relation x) = x
    | otherwise = findCorrectScheme term xs

unification :: Term -> Term -> Clause ->  Clause --(moet variabele allemaal vervangen zodat 2 gekozen termen gelijk zijn)

unification term1 term2 rule
    --  | (unificationPossible term1 term2) =  rule --TODO gebruik binder om alle variabele te veranderen + check of bij find binder dat hij nog niet in de lijst zit
    -- | otherwise = rule
    | z /= InvalidBinder  = bindRule z rule
    | otherwise = InvalidClause -- geef onmogelijk resultaat terug als er niet kan gebindt worden
    where 
    z= (findBinders term1 term2)
    
bindRule :: Binder -> Clause -> Clause

bindRule InvalidBinder _ =InvalidClause

bindRule (MkBinder []) rule = rule --binder overlopen

bindRule (MkBinder ((x,y): xs)) rule = bindRule (MkBinder xs) z
    where
    z = changeVariableOfRule rule x y 
    
findBinders :: Term -> Term -> Binder 

findBinders (Variable x) bindingTerm = MkBinder [((Variable x) ,bindingTerm)]

findBinders (Constant x 0) bindingTerm 
    | (name bindingTerm) == x = MkBinder []
    | otherwise = InvalidBinder

findBinders term bindingTerm 
    | (name term) == (name bindingTerm) = findBinderArguments (values term) (values bindingTerm)
    | otherwise = InvalidBinder
    
findBinderArguments :: [Term] -> [Term] -> Binder --Pre unificatie is mogelijk

findBinderArguments [] [] = MkBinder []

findBinderArguments (x:xs) (y:ys) 
    | (z /= InvalidBinder) && (k/= InvalidBinder) = appendBinder z k --Binder ((getVar z): (getVar k)) ((getActualValue z): (getActualValue k))
    | otherwise = InvalidBinder
    where
    z = findBinders x y 
    k = findBinderArguments xs ys
    
appendBinder :: Binder -> Binder -> Binder

appendBinder (MkBinder []) binder =binder

appendBinder (MkBinder ((var,val):xs)) binder 
    | (z == InvalidBinder) = InvalidBinder
    | otherwise = appendBinder (MkBinder xs) z
    where
    z = addToBinder (var,val) binder


addToBinder :: (Term,Term) -> Binder -> Binder

addToBinder (var1,val1) (MkBinder []) = MkBinder [(var1,val1)]

addToBinder (var1,val1) (MkBinder ((var2,val2):xs))
    | (var1 == var2) && (val1 == val2) = MkBinder ((var2,val2):xs)
    | (var1 == var2) = InvalidBinder
    | (z == InvalidBinder) = InvalidBinder
    | otherwise =MkBinder ((var1,val1):(var2,val2):xs)
    where
    z = addToBinder  (var1,val1) (MkBinder (xs))


addToScheme :: [Term] -> Scheme -> Scheme

addToScheme termList s = x
    where 
    x = MkScheme (relation s) (Set.insert termList (getSchemeValues s) )

-- zoek de scheme waar waarde moet toegevoegd worden
addToCorrectScheme :: Term -> [Scheme] -> [Scheme] 

addToCorrectScheme (Constant _ _) (x:xs) = error "Constante waarde" -- Zou error moeten geven

addToCorrectScheme (Variable _) (x:xs) = error "Variabele waarde"

addToCorrectScheme term [] = (MkScheme (name term) (Set.fromList [(values term)])):[]



addToCorrectScheme term (x:xs)
    |(name term) == (relation x) = (addToScheme (values term) x) : xs
    | otherwise = x : addToCorrectScheme term xs
 
addListToCorrectScheme :: [Term] -> [Scheme] -> [Scheme]

addListToCorrectScheme [] schemeList = schemeList

addListToCorrectScheme (x:xs) schemeList = addListToCorrectScheme xs z
    where 
    z =addToCorrectScheme x schemeList


changeVariableOfRule :: Clause -> Term -> Term -> Clause

changeVariableOfRule r (Variable x) bindingTerm = Rule (changeVariable (headTerm r) (Variable x) bindingTerm) (changeVariableTermList (body r) (Variable x) bindingTerm)

changeVariableOfRule r _ bindingTerm = error "Verwacht een Variabele geen term"

changeVariable :: Term ->  Term -> Term ->Term

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

bottom_upAlgorithm :: Program -> Integer ->  [Scheme]     

bottom_upAlgorithm _ 0  = []

bottom_upAlgorithm program integer = bottom_upHelper program integer [] 

bottom_upHelper:: Program -> Integer ->  [Scheme] -> [Scheme]

bottom_upHelper _ 0 schemeList = schemeList

bottom_upHelper program n schemeList = bottom_upHelper program (n-1) newSchemeList
    where
    newTerms = fireAllRules program schemeList
    newSchemeList = addListToCorrectScheme newTerms schemeList
