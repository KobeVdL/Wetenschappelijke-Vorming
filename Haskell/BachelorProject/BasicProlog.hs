{-# LANGUAGE FlexibleInstances #-}
module BasicProlog where
      
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- This class states that given object can be binded with a binder with another object
-- Furthermore it has functions that rename the variables to "_" ++ #Number#
-- Last but not least it also a function that returns all the variables that are included in given object
class (Bindable a) where
    -- binds the object with given binder
    bindValue :: a -> Binder -> a
    
    -- first term is a variable and second is the replacingTerm, replaces all occurences of the first term
    -- with second term in given object
    changeVariable ::  Term -> Term -> a -> a
    
    -- finds the binder so that after applying it to the first object, the first and the second are equal
    findBinder :: a -> a -> Maybe Binder
    
    -- renames the variables with "_" ++ #Number# where starting number is given and is increased for each variable
    rename :: a -> Int -> (a,Int)
    
    -- returns a set of all the variables in given object
    findVariables :: a -> Set Term


-- Term consist of a name kardinality and his arguments, for constants use kardinality=0 and arguments=[]
-- Term can also be a variable that has only a name
data Term = MkTerm { 
            name :: String ,
            kardinaliteit :: Int ,
            values :: [Term]
            }
            | 
            Variable {
            name :: String}
            deriving (Ord)
            

-- Predicate class forms the outer layer in a prolog program, it has a list of terms as arguments
data Predicate = MkPredicate {
                    nameOfPred :: String ,
                    kardinaliteitOfPred :: Int ,
                    valuesOfPred :: [Term] }deriving Ord
                    


-- A clause consist of one Predicate which forms the head of the rule
-- and a list of predicates which forms the body of the rule
data Clause = Rule
              {headTerm :: Predicate ,
              body :: [Predicate] }    
              deriving (Eq, Show)

-- A program is a list of clauses (like a prolog program)
data Program = MkProgram [Clause]


-- Maps a Variable to a Term
type Binder = Map Term Term


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
    

instance Eq b => Eq ([Term] -> b) where
    f == g = f []  == g []


instance Ord b => Ord ([Term] -> b) where
    f <= g = f [] <= g []
    
    
    
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

    

-- Shows a list of terms serperated by a comma
showTermList :: [Term] -> String

showTermList [] = ""

showTermList [x] = show x

showTermList (x:xs) = show x ++ "," ++ showTermList xs 


-- Checks if two list of terms are equal to each other
termValuesEqual :: [Term] -> [Term] -> Bool

termValuesEqual [] [] = True

termValuesEqual (x:xs) (y:ys) = (x == y) && termValuesEqual xs ys

    

-- returns the list of clauses which are packed in a Program
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


    
-- append 2 maybe binders to each other, returns nothing if one of them is nothing
appendBinder :: Maybe Binder -> Maybe Binder -> Maybe Binder

appendBinder binder1 binder2 = do 
    x <- binder1
    y <- binder2
    Just (Map.union x y)


-- Creates the binder that renames all the variables to another variable
renameBinder :: [Term] -> Int -> Binder
  
renameBinder [] _ = Map.empty
  
renameBinder (x:xs) n = Map.union (Map.singleton x (Variable ("_" ++ show n))) (renameBinder xs (n+1))



-- With given predicate search for a rule where the head of the rule matches with a binding to the given pred
-- Returns Nothing if no such rule available
findBindingRule :: Predicate -> [Clause] -> Maybe (Clause,[Clause])

findBindingRule pred [] = Nothing

findBindingRule pred (x:xs) = case binder of
    Nothing -> findBindingRule pred xs
    Just bind ->Just (x,xs)
    where
    binder = findBinder (headTerm x) pred
    

