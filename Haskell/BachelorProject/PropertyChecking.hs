
module PropertyChecking where 

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import BasicProlog
import BasicStep


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


-- The simplification algorithm which is unique for each programming language
-- This step is tested in property checking to see if the simplification is correct.
normalStep ::  Term-> Maybe Term

normalStep term = step term normalStep
    

 
    
-- A similar simplification procedure, except a small mistake  concerning the first property is included
-- This is used to test if our algorithms can detect the test    

step1 :: Term-> Maybe Term

step1 (MkTerm "leq" 2 [t1,t2]) = Nothing -- don't reduce and is an error
    
step1 term  = step term step1

    
   

-- A similar simplification procedure, except a small mistake  concerning the second property is included
-- This is used to test if our algorithms can detect the test    

step2 :: Term-> Maybe Term

step2 (MkTerm "leq" 2 [MkTerm "Zero" 0 [],t2]) = Nothing -- don't reduce and is an error
    
step2 term  = step term step2


-- A similar simplification procedure, except a small mistake  concerning the third property is included
-- This is used to test if our algorithms can detect the test    

step3 :: Term-> Maybe Term

step3 (MkTerm "succ" 1 [x]) = Just (MkTerm "ifThenElse" 3 [true, true ,true]) -- don't reduce and is an error
    where 
    true = MkTerm "True" 0 []
    
step3 term  = step term step3

-- The last step method handles a very specific and difficult to find error
-- This is used to test the algorithm

step4 :: Term -> Maybe Term

step4 (MkTerm ":" 2 [MkTerm "succ" 1 [MkTerm "Zero" 0 []],MkTerm "ifThenElse" 3 [MkTerm "True" 0 [],x,y]]) = Just (MkTerm "'A'" 0 []) -- changes array[nat] into number and is incorrect

step4 term  = step term step4


--This looks very simular as  step4 only has this method no variables in its test

step5 :: Term -> Maybe Term

step5 (MkTerm ":" 2 [MkTerm "succ" 1 [MkTerm "Zero" 0 []],MkTerm "ifThenElse" 3 [MkTerm "True" 0 [],MkTerm "[]" 0 [],MkTerm "[]" 0 []]]) = Just (MkTerm "'A'" 0 []) -- changes array[nat] into number and is incorrect


step5 term  = step term step5
