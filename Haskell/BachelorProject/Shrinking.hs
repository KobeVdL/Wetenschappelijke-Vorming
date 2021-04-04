module Shrinking where
    
import BasicProlog


import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.List
import Debug.Trace

-- TODO kan je dit niet blijven laten hollowen?


import qualified Data.Set as Set
{-
    Shrinking is a method to reduce the complexity for a generated term. Those differ for the type of term generated
    For example, an integer wants to reduce its value to 0.
    In our declaritive terms, we want to reduce the size of the term.
    
    peel and hollow algoritmes
-}

-- Removes the top layer of rules such that the property and precondition  not holds --TODO precondition cejcl
-- It 'peels' of the rules used that are not directly needed
shrinkAlgorithm:: Predicate ->(Predicate -> Bool) -> Program -> (Set Predicate)

shrinkAlgorithm startPred propCheck program= Set.fromList(result)
    where
    shrinkedPred = shrinkTermPeel startPred propCheck program
    result = concat (map (\x -> shrinkTermHollow x propCheck program) shrinkedPred)

-- perform a peel step in which the top term is removed and checked if the property  not holds
-- this is done by using a rule to simplify the predicate and the body of the rule is checked apart each time
shrinkTermPeel:: Predicate->(Predicate -> Bool) -> Program -> [Predicate]

shrinkTermPeel startPred propCheck program
    | predsNotValid==[] = [startPred]
    | otherwise = foldr (\x acc -> shrinkTermPeel x propCheck program ++ acc)[] predsNotValid -- append the reduced preds
    where
    reducedPreds = reducePred startPred (releaseProgram program)
    predsNotValid = filter (\x-> not (propCheck x)) reducedPreds
 
 
 
-- Hollow the given term by reducing the inner terms inside the outer term
-- and checking each time if the precondition holds and the property not 
shrinkTermHollow::  Predicate -> (Predicate -> Bool) -> Program -> [Predicate]

shrinkTermHollow startPred@(MkPredicate name kard [term @(MkTerm nameTerm kardTerm listTerms),typeOfTerm]) propCheck program = hollowSolution startSol startWorkList 0 toPred propCheck  -- TODO voor alle programmas maken, gaat niet
    where
    (startSol,startWorkList) = setUpHollow term
    toPred = \x -> MkPredicate name kard [MkTerm nameTerm kardTerm x,typeOfTerm]
    

    
-- construct all preds that are inside a term and that reduce the term
hollowSolution :: [Set Term] -> [[Term]] -> Int -> ([Term] -> Predicate)-> (Predicate -> Bool) -> [Predicate]

hollowSolution sol [] index toPred propCheck = map toPred (constuctValuesPred sol (-1) (Variable "this is not used"))

hollowSolution sol (y:ys) index toPred propCheck 
    | index >= length sol = map toPred (constuctValuesPred sol (-1) (Variable "this is not used"))
    | otherwise = hollowSolution totalSol ys (index + 1) toPred propCheck
    where
    (first,(replace:last)) = splitAt index sol
    newSol = maxReducedForCurrentIndex sol index toPred propCheck y  
    totalSol = first ++ (newSol:last)


    

-- for given index calculates a new [set Term] with solutions(including previous found ) that are max reduced and still invalid for precondition
maxReducedForCurrentIndex ::  [Set Term]-> Int -> ([Term] -> Predicate) -> (Predicate -> Bool) -> [Term] -> Set Term

maxReducedForCurrentIndex currentSol index toPred propCheck [] = Set.empty

maxReducedForCurrentIndex currentSol index toPred propCheck (x:xs) 
    | stepResults == [] = Set.insert x (maxReducedForCurrentIndex currentSol index toPred propCheck xs) -- add the term to the solutions
    | otherwise = maxReducedForCurrentIndex currentSol index toPred propCheck (stepResults ++ xs) -- add the terms to the list bec they can still be reduced 
    where
    stepResults = hollowStep currentSol index toPred propCheck x


--performs one step in the hollow algorithm returns an empty list if none such terms exist
hollowStep :: [Set Term] -> Int -> ([Term] -> Predicate) -> (Predicate -> Bool) -> Term -> [Term] --TODO geen idee 

hollowStep currentSol index toPred propCheck stepTerm = filter (validCounterPred currentSol index toPred propCheck) reduceTerms -- filters out the terms that still form counter examples.
    where
    reduceTerms = hollowReduction stepTerm
    
    
-- checks if given term still is a counterexample
validCounterPred:: [Set Term] -> Int -> ([Term] -> Predicate) -> (Predicate -> Bool) -> Term -> Bool

validCounterPred currentSol index toPred propCheck termToCheck = case found of
        Nothing -> True
        Just x -> False
    where
    possibleValuesPred = constuctValuesPred currentSol index termToCheck
    found = find (propCheck . toPred) possibleValuesPred
        

-- put everyTerm in the first list in front of each other element
-- index gives the index where possible solution should be replaced with given term
constuctValuesPred :: [Set Term] -> Int -> Term -> [[Term]]

constuctValuesPred [] index givenTerm = [[]] -- TODO fout als map leeg is wordt dit niet uitgevoerd

constuctValuesPred (x:xs) 0 givenTerm = map (givenTerm:) (constuctValuesPred xs (-1) givenTerm)

constuctValuesPred (x:xs) index givenTerm =  map (\z-> concat (map (z:) (constuctValuesPred xs index givenTerm))) (Set.toList x)


--sets up the terms for the hollow algorithm
setUpHollow:: Term -> ([Set Term] ,[[Term]])

setUpHollow term = ( map (\x->Set.singleton x ) (values term) , map (\x->[x]) (values term)) -- Probleem wanneer mag ik stoppen
-- oplossing als terug voldaan is aan property of reductie is leeg voeg dan vorige term toe aan oplossingen
-- en voeg niet toe aan de lijst.
    

        

-- Term->Predicate \x-> MkPredicate "" 3 [MkTerm "X" 1 [x],y,z]
-- arg (\var -> MkTerm "X" 2 [var,y])
-- arg (\var -> MkTerm "X" 2 [x,var])
-- eerst eerste variabele vereenvoudigen en deze dan als nieuwe variabele zetten, doe hetzelfde voor de volgende
-- voor gemak begin met 1 variabele

-- reduces a terms with the hollow algorithm
hollowReduction :: Term->[Term]

hollowReduction (MkTerm "Zero" 0 [])  = []

hollowReduction (MkTerm "True" 0 [])  = [] 

hollowReduction (MkTerm "False" 0 [])  = [] 

hollowReduction (MkTerm "succ" 1 subTerm)  = subTerm

hollowReduction (MkTerm "ifThenElse" 3 [x,y,z]) = [y,z]

hollowReduction (MkTerm "leq" 2 [x,y] ) 
    | hollowX /= [] = map (\z -> MkTerm "leq" 2 [z,y] ) hollowX
    | hollowY /= [] = map (\z -> MkTerm "leq" 2 [y,z] ) hollowY
    |otherwise = [] --No valid reductions
    --(MkTerm "leq" 2 [x,y] )
    where
    hollowX = hollowReduction x
    hollowY = hollowReduction y

hollowReduction _ =[]

 
{- for each term in property, check which type the term has (for each rule in program
    check for each term if property is valid for that term
    if none, previous term is minimal
    otherwise shrink the term
 
-}   

reducePred:: Predicate->[Clause]->[Predicate]
   
reducePred pred [] = []   
   
reducePred pred clauses =
    case foundRule of
        Nothing-> []
        Just(rule,otherRules)-> newPreds ++ reducePred pred otherRules
            where
            Just binder = findBinder pred (headTerm rule) -- altijd voldaan want anders zou findBindingRule falen
            newPreds = body (bindValue rule binder)
    where
    foundRule = findBindingRule pred clauses


-- create a hasType element with the correct Type
createHasType:: Term->Predicate

createHasType givenTerm = MkPredicate "hasType" 2 [givenTerm,getTypeOfTerm givenTerm]


-- gets the type of a term
getTypeOfTerm ::Term-> Term -- TODO automatisch laten aanpassen aan programma

getTypeOfTerm (MkTerm "Zero" 0 []) = (MkTerm "nat" 0 [])

getTypeOfTerm (MkTerm "True" 0 []) = (MkTerm "bool" 0 [])

getTypeOfTerm (MkTerm "False" 0 []) = (MkTerm "bool" 0 [])

getTypeOfTerm (MkTerm "succ" 1 [x]) = (MkTerm "nat" 0 [])

getTypeOfTerm (MkTerm "ifThenElse" 3 [x,y,z]) = getTypeOfTerm y

getTypeOfTerm (MkTerm "leq" 2 [x,y] ) = (MkTerm "bool" 0 [])













