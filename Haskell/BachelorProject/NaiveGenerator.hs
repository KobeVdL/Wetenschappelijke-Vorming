module NaiveGenerator where 


import BasicProlog
import Shuffle
import PropertyChecking


import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import Control.Monad.Trans.Maybe
import Data.Time.Clock.POSIX
import System.Environment



import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- generates a random Predicate with the given possible terms
naiveGenerateElem :: Int -> IO Predicate

naiveGenerateElem n = do
    typeOfTerm <- takeRandom types 
    z <-generateHasTypeTerm n const terms 
    return (hasType [z,typeOfTerm])
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    const = [zero , true, false]
    succ = MkTerm "succ" 1 
    leq = MkTerm "leq" 2 
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2 
    terms = [succ,leq,ifThenElse]
    types = [nat,bool]
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
  
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
naiveTryUntillPropertyFalse :: Int -> Int -> (Predicate -> Bool) -> IO (Maybe Predicate)

naiveTryUntillPropertyFalse 0 size propCheck = return Nothing -- geëindigt door maxTimes

naiveTryUntillPropertyFalse maxTimes size propCheck = do
        pred <- naiveGenerateElem size
        if not( precond pred) || propCheck pred then
            naiveTryUntillPropertyFalse (maxTimes-1) size propCheck
        else
            return (Just pred) -- geeft aan of geëindigt voor maxTimes
        
        
        
        
        
-- Check if the given precondition is valid to the given predicate        
precond :: Predicate -> Bool

precond (MkPredicate "hasType" 2 [term,typeOfTerm]) =
    checkTerm term typeOfTerm

precond _ = True    
    
-- Returns True if term has the correct Type
checkTerm :: Term -> Term -> Bool

checkTerm (MkTerm "Zero" 0 []) (MkTerm "nat" 0 []) = True

checkTerm  (MkTerm "True" 0 []) (MkTerm "bool" 0 []) = True

checkTerm  (MkTerm "False" 0 []) (MkTerm "bool" 0 []) = True

checkTerm  (MkTerm "succ" 1 [x]) (MkTerm "nat" 0 []) = precond (MkPredicate "hasType" 2 [x,(MkTerm "nat" 0 [])])

checkTerm  (MkTerm "ifThenElse" 1 [x,y,z]) typeTerm = 
    precond (MkPredicate "hasType" 2 [x,MkTerm "bool" 0 []] ) && precond (MkPredicate "hasType" 2 [y,typeTerm]) && precond (MkPredicate "hasType" 2 [z,typeTerm] )

checkTerm (MkTerm "leq" 2 [x,y] ) (MkTerm "bool" 0 []) =  precond (MkPredicate "hasType" 2 [x,(MkTerm "bool" 0 [])]) && precond (MkPredicate "hasType" 2 [y,(MkTerm "bool" 0 [])])
    
checkTerm _ _ = False    
    
    
    