module Shrinking where
    
import BasicProlog


import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.List
import Debug.Trace

-- Gebruik AC1 (arc consistency om termen blijven te verminderen tot als er geen verandering meer gebeurt


import qualified Data.Set as Set
{-
    Shrinking is a method to reduce the complexity for a generated term. Those differ for the type of term generated
    For example, an integer wants to reduce its value to 0.
    In our declaritive terms, we want to reduce the size of the term.
    
    peel and hollow algoritmes
-}

data ShrinkInfo = MkShrinkInfo{
                solutionTermsShrink :: [Set Term],
                indexShrink :: Int,
                getToPred :: (ShrinkInfo -> Term -> [Predicate])
                }
                
data PredValidator = MkPredValidator{
                        getPropertyCheck :: (Predicate -> Bool),
                        getPrecond :: (Predicate -> Program -> Bool),
                        getProgram :: Program
                    }



-- Removes the top layer of rules such that the property and precondition  not holds --TODO precondition cejcl
-- It 'peels' of the rules used that are not directly needed
shrinkAlgorithm:: Predicate ->(Predicate -> Bool) ->(Predicate -> Program -> Bool) -> Program -> (Set Predicate)

shrinkAlgorithm startPred@(MkPredicate name kardi arg) propCheck precond program= Set.fromList(map (MkPredicate name kardi) result) -- creates all tje preds
    where
    predValid = MkPredValidator propCheck precond program
    shrinkedPred = shrinkTermPeel startPred propCheck precond program
    toPred = (\x y ->(map (MkPredicate name kardi) (constructTerms x y)))
    result = concat (map (\x -> shrinkTermHollowStart x toPred predValid) shrinkedPred)

-- perform a peel step in which the top term is removed and checked if the property  not holds
-- this is done by using a rule to simplify the predicate and the body of the rule is checked apart each time
shrinkTermPeel:: Predicate->(Predicate -> Bool) -> (Predicate -> Program -> Bool) -> Program -> [Predicate]

shrinkTermPeel startPred propCheck precond program
    | predsNotValid==[] = [startPred]
    | otherwise = foldr (\x acc -> shrinkTermPeel x propCheck precond program ++ acc)[] predsNotValid -- append the reduced preds
    where
    reducedPreds = reducePred startPred (releaseProgram program)
    predsNotValid = filter (\x-> precond x program && not(propCheck x)) reducedPreds
 
 

-- Term->Predicate \x-> MkPredicate "" 3 [MkTerm "X" 1 [x],y,z]
-- arg (\var -> MkTerm "X" 2 [var,y])
-- arg (\var -> MkTerm "X" 2 [x,var])
-- eerst eerste variabele vereenvoudigen en deze dan als nieuwe variabele zetten, doe hetzelfde voor de volgende
-- voor gemak begin met 1 variabele

-- reduces a terms with the hollow algorithm




filterCounterEx :: ShrinkInfo -> PredValidator -> [Term] -> [Term]

filterCounterEx shrinkInfo predValid = filter (validCounterPred shrinkInfo predValid)





hollowReduction :: ShrinkInfo -> PredValidator->  Term -> [Term]

hollowReduction shrinkInfo  predValid termToReduce@(MkTerm name kardi arg)
    | kardi == 0 = [termToReduce] -- if constant then not reducable anymore
    | reducable /= [] = concat (map (hollowReduction shrinkInfo predValid) reducable) -- term is reducable, replace parent with one or more of its childs
    | otherwise =  map (MkTerm name kardi) (shrinkTermHollow termToReduce newToPred predValid) -- term is not reducable
    -- construct all possible maxReducedTerms of given term thats not reducable
    where
    reducable =filterCounterEx shrinkInfo predValid (values termToReduce)
    toPred = getToPred shrinkInfo 
    newToPred = expandToPred shrinkInfo termToReduce





-- Hollow the given term by reducing the inner terms inside the outer term
-- and checking each time if the precondition holds and the property not 
shrinkTermHollow::  Term -> (ShrinkInfo ->Term -> [Predicate]) -> PredValidator -> [[Term]]

shrinkTermHollow term toPred predValid = hollowSolution shrinkInfo predValid startWorkList  -- TODO voor alle programmas maken, gaat niet
    where
    (startSol,startWorkList) = setUpHollow term
    shrinkInfo = MkShrinkInfo startSol 0 toPred 
    
-- Similar to shrinkTermHollow, only this time starts with a predicate and gives a list of predicates back    
shrinkTermHollowStart :: Predicate -> (ShrinkInfo ->Term -> [Predicate]) -> PredValidator -> [[Term]]
  
shrinkTermHollowStart pred toPred predValid = (hollowSolution shrinkInfo predValid startWorkList)
    where
    (startSol,startWorkList) = setUpHollowPred pred
    shrinkInfo = MkShrinkInfo startSol 0 toPred 


    
-- construct all preds that are inside a term and that reduce the term
hollowSolution :: ShrinkInfo -> PredValidator ->  [[Term]] -> [[Term]]

-- all the work is done
hollowSolution shrinkInfo predValid [] = (constuctValuesPredWithoutReplace sol )
    where
    sol = solutionTermsShrink shrinkInfo

hollowSolution shrinkInfo predValid (y:ys)
    | index >= length sol = (constuctValuesPredWithoutReplace sol ) -- index should never be higher as the kardinality
    | otherwise = hollowSolution (newShrinkInfo) predValid ys --if (replace != newSol) then -- solution changed so not possible to stop
                   -- each
                  --else
                  --  ddd
    --hollowSolution (newShrinkInfo) predValid ys
    where
    sol = solutionTermsShrink shrinkInfo
    toPred = getToPred shrinkInfo
    index = indexShrink shrinkInfo
    (first,(replace:last)) = splitAt index sol
    newSol = maxReducedForCurrentIndex shrinkInfo predValid y  
    totalSol = first ++ (newSol:last)
    newShrinkInfo = MkShrinkInfo totalSol (index+1) toPred 



-- for given index calculates a new [set Term] with solutions(including previous found ) that are max reduced and still valid for precondition and invalid for property
-- TODO deze functie is nog verkeerd
maxReducedForCurrentIndex ::  ShrinkInfo-> PredValidator -> [Term] -> Set Term

maxReducedForCurrentIndex shrinkInfo predValid [] = Set.empty

maxReducedForCurrentIndex shrinkInfo predValid (x:xs)= -- go over each term of valid solutions and add them to the set
    Set.union (Set.fromList stepResults) (maxReducedForCurrentIndex shrinkInfo predValid xs)
    where
    stepResults = hollowReduction shrinkInfo predValid x --trace ("results shrinking are" ++ (show (hollowStep currentSol index toPred propCheck precond program x))) (hollowStep currentSol index toPred propCheck precond program x)



-- checks if given term still is a counterexample
validCounterPred:: ShrinkInfo -> PredValidator -> Term -> Bool

validCounterPred shrinkInfo predValid termToCheck = case found of
        Nothing -> True
        Just x -> False
    where
    toPred = getToPred shrinkInfo
    propCheck = getPropertyCheck predValid
    precond = getPrecond predValid
    program = getProgram predValid
    possibleValuesPred = toPred shrinkInfo termToCheck -- construct all possible predicates with given term
    found = find ((\x-> not (precond x program) ||(propCheck x))) possibleValuesPred



-- same as construct valuesPred, only do not replace a term at index n
constuctValuesPredWithoutReplace :: [Set Term] -> [[Term]]

constuctValuesPredWithoutReplace [] = [[]]

constuctValuesPredWithoutReplace (x:xs) = map (\z-> concat (map (z:) (constuctValuesPredWithoutReplace xs))) (Set.toList x)



--sets up the terms for the hollow algorithm
setUpHollow:: Term -> ([Set Term] ,[[Term]])

setUpHollow term = ( map (\x->Set.singleton x ) (values term) , map (\x->[x]) (values term)) -- Probleem wanneer mag ik stoppen
-- oplossing als terug voldaan is aan property of reductie is leeg voeg dan vorige term toe aan oplossingen
-- en voeg niet toe aan de lijst.
    
-- similar with setUpHollow, only starts with a pred instead    
setUpHollowPred :: Predicate -> ([Set Term] ,[[Term]])
    
setUpHollowPred pred = ( map (\x->Set.singleton x ) (valuesOfPred pred) , map (\x->[x]) (valuesOfPred pred))     

-- Function used to create the function toPred, needs shrinkInfo and a list of possible to use terms
-- returns a list of all predicates that can be made with it
-- increases everytime you call this function
expandToPred :: ShrinkInfo -> Term -> (ShrinkInfo -> Term -> [Predicate])

expandToPred shrinkInfo term@(MkTerm name kardi arg) = (\x y -> concat (map (toPred shrinkInfo) (map (MkTerm name kardi) (constructTerms x y))))-- toPred possibleValuesPred
    where
    currentSol = solutionTermsShrink shrinkInfo
    index = indexShrink shrinkInfo
    toPred = getToPred shrinkInfo



constructTerms :: ShrinkInfo -> Term -> [[Term]]

constructTerms shrinkInfo = constuctValuesPred sol index
    where
    sol = solutionTermsShrink shrinkInfo
    index = indexShrink shrinkInfo



-- put everyTerm in the first list in front of each other element
-- index gives the index where possible solution should be replaced with given term
constuctValuesPred :: [Set Term] -> Int -> Term -> [[Term]]

constuctValuesPred [] index givenTerm = [[]] -- TODO fout als map leeg is wordt dit niet uitgevoerd

constuctValuesPred (x:xs) 0 givenTerm =   map (givenTerm:) (constuctValuesPred xs (-1) givenTerm)

constuctValuesPred (x:xs) index givenTerm =  map (\z-> concat (map (z:) (constuctValuesPred xs (index-1) givenTerm))) (Set.toList x)


 
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













