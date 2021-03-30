
module BasicProlog where
      
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

class (Bindable a) where
    bindValue :: a -> Binder -> a
    changeVariable ::  Term -> Term -> a -> a
    findBinder :: a -> a -> Maybe Binder
    rename :: a -> Int -> (a,Int)
    findVariables :: a -> Set Term

data Term = MkTerm { 
            name :: String ,
            kardinaliteit :: Int ,
            values :: [Term]
            }
            | 
            Variable {
            name :: String}
            deriving (Ord)
            
--Elke buitenste is een predikaat deze bevat termen als argumenten
data Predicate = MkPredicate {
                    nameOfPred :: String ,
                    kardinaliteitOfPred :: Int ,
                    valuesOfPred :: [Term] }deriving Ord
                    

data Clause = Rule
              {headTerm :: Predicate ,
              body :: [Predicate] }    
              deriving (Eq, Show)


instance Eq Term  where 
    (==) (Variable x) (Variable y) = (x == y)
    x == y = ((name x)==(name y)) && termValuesEqual (values x) (values y)
    
instance Show Term where
    show (Variable x) = x
    show (MkTerm nameT 0 _) = nameT
    show (MkTerm nameT n list) = nameT ++ "(" ++ showTermList list ++ ")"
    
instance Bindable Term where
    bindValue term binder = Map.foldrWithKey changeVariable term binder --changeVariable term (Variable x) bindingTerm 
    
    changeVariable  (Variable x) bindingTerm (MkTerm nameTerm kard argumentTerms) = MkTerm nameTerm kard (changeVariable (Variable x) bindingTerm argumentTerms)
    changeVariable (Variable x) bindingTerm (Variable y) = 
                if Variable x == Variable y then
                     bindingTerm -- bij variabele vervang je deze
                else
                     Variable y
    changeVariable _ bindingTerm termToChange = error "Expects a variable, not a term"
                     
    findBinder (Variable x) bindingTerm = Just (Map.singleton (Variable x) bindingTerm )
    findBinder term (Variable y) = Just (Map.singleton (Variable y) term ) 
    findBinder term bindingTerm 
        | name term == name bindingTerm = findBinder (values term) (values bindingTerm)
        | otherwise = Nothing
        

    rename term n = (newTerm, (Set.size set+n))
        where
        set = findVariables (term)
        binder = renameBinder (Set.toList set) n
        newTerm = bindValue term binder 
        
    findVariables (Variable x) = Set.singleton (Variable x)
    findVariables (MkTerm nameTerm kard valueOfTerm) = findVariables valueOfTerm
    
    
    
instance Eq Predicate  where 
   x == y = ((nameOfPred x)==(nameOfPred y)) && termValuesEqual (valuesOfPred x) (valuesOfPred y)   
    
    
instance Show Predicate  where
    show (MkPredicate nameP 0 _) = nameP
    show (MkPredicate nameP n list) = nameP ++ "(" ++ showTermList list ++ ")"
            {- 
                A predicate has a name, a kardinality and a list of terms as arguments
            -}
            
            
    
instance Bindable Predicate where    
    
    bindValue (MkPredicate name kard termList) binder = MkPredicate name kard (bindValue termList binder)

    changeVariable var replacingTerm (MkPredicate name kard termList) = MkPredicate name kard (changeVariable var replacingTerm termList)

    findBinder pred1 pred2 
        | nameOfPred pred1 == nameOfPred pred2 = findBinder (valuesOfPred pred1) (valuesOfPred pred2)
        | otherwise = Nothing
        
    rename (MkPredicate name kard termList) n = ((MkPredicate name kard renamedTerms),index + n)
        where
        (renamedTerms,index) = rename termList n
        
    findVariables (MkPredicate name kard termList) = findVariables termList
  
  
  
  
instance Bindable Clause where
    
    bindValue rule binder = fst $ rename bindedRule  0 -- TODO 
        where 
        bindedRule = Map.foldrWithKey (changeVariable) rule binder
    
    changeVariable  var replacingTerm (Rule headRule body)= Rule (changeVariable var replacingTerm headRule) (changeVariable var replacingTerm body)

    findBinder rule1 rule2 = Nothing -- Do not use findBinders on 2 rules


    rename clause n = ((Rule x xs),newIndex)
        where
        ((x:xs),newIndex) = rename ((headTerm clause):body clause) n --add head of rule to body

    
    findVariables (Rule headRule body) = Set.union (findVariables headRule) (findVariables body)
  
    

instance Bindable a => Bindable [a] where
    
    bindValue array binder = map (\x -> bindValue x binder) array
    
    changeVariable var replacingTerm array = map (changeVariable var replacingTerm) array

    findBinder [] [] = Just Map.empty

    findBinder _ [] = Nothing

    findBinder [] _ = Nothing

    findBinder(x:xs) (y:ys) = appendBinder z k
        where
        z = findBinder x y 
        k = findBinder xs ys
       
    rename array n = (bindValue array binder,(Set.size varSet +n))
        where
        varSet = foldr (Set.union . findVariables) (Set.empty) (array)
        binder  = renameBinder (Set.toList varSet) n
        
    findVariables = foldr (\x acc-> Set.union (findVariables x) acc ) Set.empty

    

showTermList :: [Term] -> String

showTermList [] = ""

showTermList [x] = show x

showTermList (x:xs) = show x ++ "," ++ showTermList xs 



termValuesEqual :: [Term] -> [Term] -> Bool

termValuesEqual [] [] = True

termValuesEqual (x:xs) (y:ys) = (x == y) && termValuesEqual xs ys

    


type Binder = Map Term Term


--data Value a = MkValue a deriving (Eq, Show)


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




    
--Gegeven een binder pas deze toe op de regel.     
    

appendBinder :: Maybe Binder -> Maybe Binder -> Maybe Binder

appendBinder binder1 binder2 = do 
    x <- binder1
    y <- binder2
    Just (Map.union x y)


addToBinder :: (Term,Term) -> Binder -> Binder

addToBinder (Variable v,term) = Map.insert (Variable v) term
 



renameBinder :: [Term] -> Int -> Binder
  
renameBinder [] _ = Map.empty
  
renameBinder (x:xs) n = Map.union (Map.singleton x (Variable ("_" ++ show n))) (renameBinder xs (n+1))




findBindingRule :: Predicate -> [Clause] -> Maybe (Clause,[Clause])

findBindingRule pred [] = Nothing

findBindingRule pred (x:xs) = case binder of
    Nothing -> findBindingRule pred xs
    Just bind ->Just (x,xs)
    where
    binder = findBinder (headTerm x) pred
    

