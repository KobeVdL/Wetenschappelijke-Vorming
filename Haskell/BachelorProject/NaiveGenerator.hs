module NaiveGenerator where 


import BasicProlog
import Shuffle
import PropertyChecking
import Constructors

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import Control.Monad.Trans.Maybe
import Data.Time.Clock.POSIX
import System.Environment
import System.Random
import Data.List


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

type TermContainer = (Set Term, Set ([Term] -> Term))

-- container that holds for each predicate all possible terms
type PredContainer = Map String (Set Term, Set ([Term] -> Term)) 


-- generates a random Predicate with the given possible terms
naiveGenerateElem :: Int -> Program -> IO Predicate

naiveGenerateElem n program = do
    typeOfTerm <- generateType n typeConst typeLitterals 
    z <-generateHasTypeTerm n const terms 
    return (hasType [z,typeOfTerm])
    where
    (((const),(terms)),((typeConst),(typeLitterals)))= aritProgramUpgradedUsedTerm 
    hasType = MkPredicate "hasType" 2
    
    

generateType:: Int -> [Term] -> [([Term]->Term)] -> IO Term

generateType 0 const _ = takeRandom const

generateType n const literals = 
    do
        roll <- randomRIO (0 :: Int, totalLength-1)
        if (roll < lengthConst) then 
            do
            return (const!!roll)
        else
            do
            arguments <- generateTypeHelper (n-1) (nub (MkTerm "_Empty" 0 [] :const)) literals kard -- adds the case where array is empty
            return (chosenLit arguments)
        where
        lengthConst = length const
        litteralLength = length literals
        totalLength = lengthConst + litteralLength
        chosenLit = literals!!((totalLength-lengthConst)-1)
        kard = (kardinaliteit (chosenLit []))
        
        generateTypeHelper :: Int -> [Term] -> [([Term]->Term)] -> Int -> IO [Term]
        
        generateTypeHelper _ _ _ 0 =(return [])
        
        generateTypeHelper size const literals times = do
            semiResult <- generateTypeHelper size const literals (times-1)
            lastTerm <- generateType size const literals
            return (lastTerm : semiResult)
   






    
  
-- Take a random element out of the list  
takeRandom :: [a] -> IO a 

takeRandom x = do
    list <-shuffle x
    return (head list)
    
    
-- generate a hasTypeTerm with given size    
generateHasTypeTerm :: Int -> [Term] -> [([Term] -> Term)] -> IO Term   

generateHasTypeTerm 0 const _ = do
   value <- takeRandom const
   return value
 
generateHasTypeTerm n const terms = do
    pickedTerm <-  takeRandom terms
    let z = kardinaliteit (pickedTerm [])
    dividedPred' <- splitNumber (n-1) (z)
    dividedPred <- shuffle dividedPred'
    interiorTerms <- generateHasTypeTermHelper dividedPred const terms
    return (pickedTerm interiorTerms)
    where
    generateHasTypeTermHelper :: [Int] -> [Term] -> [([Term] -> Term)] -> IO [Term] 
    
    generateHasTypeTermHelper [] _ _ = return []
    
    generateHasTypeTermHelper (x:xs) const terms= do
        restTerms <-  generateHasTypeTermHelper xs const terms
        current <- generateHasTypeTerm x const terms
        return (current:restTerms)
        
        
-- generates a term untill you get one that is valid to the precondition and 
-- not the property and gives the result back        
naiveTryUntillPropertyFalse :: Int -> Int -> (Predicate -> Bool) -> Program -> IO (Maybe Predicate)

naiveTryUntillPropertyFalse 0 size propCheck program = return Nothing -- geëindigt door maxTimes

naiveTryUntillPropertyFalse maxTimes size propCheck program = do
        pred <- naiveGenerateElem size program
        if not( precond pred program) || propCheck pred then
            naiveTryUntillPropertyFalse (maxTimes-1) size propCheck program
        else
            return (Just pred) -- geeft aan of geëindigt voor maxTimes
        where
        
       
        
        
        
        
-- Check if the given precondition is valid to the given predicate        
precond :: Predicate -> Program -> Bool

precond pred  program=
    checkTerm [pred] clauses clauses 0
    where
    clauses = releaseProgram program
 
    
-- Returns True if term has the correct Type
checkTerm :: [Predicate] -> [Clause] -> [Clause]-> Int -> Bool    
    
checkTerm [] _ _ _ = True    
    
checkTerm  (x:xs) allClauses clauses index = do
    let foundBindRule = findBindingRule x clauses 
    case foundBindRule of 
        Nothing -> False
        Just (rule,rest) -> 
                case result of
                        False -> checkTerm (x:xs) allClauses rest index -- no result found, check the other clauses
                        True -> True
            where
                (editedRule,newIndex) = rename rule index
                Just bind = findBinder x (headTerm editedRule) --altijd voldaan door findBindingRule
                newRule = (bindValue editedRule bind)
                result = checkTerm ((body newRule) ++ xs) allClauses allClauses newIndex
    
    
    
    {-
-- adds a constant to the given predContainer
addConstant :: String -> Term -> PredContainer -> PredContainer   

addConstant name const cont = do
    case maybePredContainer of
        Nothing -> Map.insert name newPredContainer cont
            where
            newPredContainer = (Set.singleton const,Set.empty)
        Just z ->
            Map.adjust (\x->((Set.insert const (fst x)),(snd x))) name cont
    where
    maybePredContainer = Map.lookup name cont
    
-- add a literal to the given predContainer
addLiteral :: String -> ([Term]->Term) -> PredContainer -> PredContainer    
    
addLiteral name lit cont = do
    case maybePredContainer of
        Nothing -> Map.insert name newPredContainer cont
            where
            newPredContainer = (Set.empty,Set.singleton lit)
        Just z ->
            Map.adjust (\x->((fst x),Set.insert lit (snd x))) name cont
    where
    maybePredContainer = Map.lookup name cont
    
    -}

    