module Constructors where
    

import BasicProlog



import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


-- Creates a program that gives back even numbers (only positive)
evenProgram :: Program

evenProgram = MkProgram [evenBasic, evenRecursive]
    where
    zero = MkTerm "zero" 0 []
    evenBasic = Rule(MkPredicate "even" 1 [zero]) []
    evenRecursive = Rule (MkPredicate "even" 1 [MkTerm "succ" 1 [MkTerm "succ" 1 [Variable "X"]]]) [MkPredicate "even" 1 [Variable "X"]]
    

-- create the basic buildingBlocks for a weltyped program
aritProgram :: Program

aritProgram = MkProgram (r1:r2:r3:facts)
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2 
    facts = createFacts [hasType [true,bool], hasType [false,bool],hasType [zero,nat] ]
    r1 = Rule (hasType [succ [x],nat]) [hasType [x,nat]]
    r2 = Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]
    r3 =  Rule (hasType [ifThenElse [x,y,z],w]) [hasType [x,bool],hasType [y,w],hasType [z,w]]
    
    
-- returns a tuple where the first part gives back all constants and literals for the first part of hasType
--  the second part gives the constants and literals used for the types
-- this only used for naive generation
aritProgramUpgradedUsedTerm :: (([Term],[[Term]->Term]),([Term],[[Term]->Term]))

aritProgramUpgradedUsedTerm = ((constantsProgram,litteralsProgram),(constantsTypes,literalsType))
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    emptyArray = MkTerm "[]" 0 []
    letterA = MkTerm "'A'" 0 []
    constantsProgram= [zero,true,false,emptyArray,letterA]
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    ifThenElse = MkTerm "ifThenElse" 3
    add = MkTerm "add" 2
    subtract = MkTerm "subtract" 2
    multiply = MkTerm "multiply" 2
    addToArray = MkTerm ":" 2
    append = MkTerm "++" 2
    and = MkTerm "and" 2
    or = MkTerm "or" 2
    not = MkTerm "not" 1
    litteralsProgram = [succ,leq,ifThenElse,add,subtract,multiply,addToArray,append,and,or,not]
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    char = MkTerm "char" 0 []
    constantsTypes = [nat,bool,char]
    array = MkTerm "array" 1 
    literalsType = [array]

    
    
-- more rules and actions included then in arit program (for example has now arrays, char , add, subtract,...
aritProgramUpgraded :: Program

aritProgramUpgraded = MkProgram (booleanRules ++ arrayRules ++ numRules ++ facts)
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    emptyArray = MkTerm "[]" 0 []
    letterA = MkTerm "'A'" 0 []
    array = MkTerm "array" 1 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    char = MkTerm "char" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    hasType = MkPredicate "hasType" 2 
    facts = createFacts [hasType [true,bool], hasType [false,bool],hasType [zero,nat], hasType [letterA,char], hasType [emptyArray,array [x]] ]
    numRules = createNumberRules 
    arrayRules = createArrayRules
    booleanRules = createBooleanRules
    
-- create the basic rules that have to do with numbers
createNumberRules :: [Clause]

createNumberRules = [r1,r2,r3,r4,r5]
    where
    zero = MkTerm "Zero" 0 []
    succ = MkTerm "succ" 1 
    leq = MkTerm "leq" 2 
    bool = MkTerm "bool" 0 []
    nat = MkTerm "nat" 0 []
    x = Variable "X"
    y = Variable "Y"
    add = MkTerm "add" 2
    subtract = MkTerm "subtract" 2
    multiply = MkTerm "multiply" 2
    hasType = MkPredicate "hasType" 2 
    r1 = Rule (hasType [succ [x],nat]) [hasType [x,nat]]
    r2 = Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]
    r3 = Rule (hasType [add [x,y],nat]) [hasType [x,nat],hasType [y,nat]]
    r4 = Rule (hasType [subtract [x,y],nat]) [hasType [x,nat],hasType [y,nat]]
    r5 = Rule (hasType [multiply [x,y],nat]) [hasType [x,nat],hasType [y,nat]]
    
    
-- create rules for constructing an array 
createArrayRules :: [Clause]
   
createArrayRules = [r1,r2]
    where -- :([],[]) => array(array(X)))
    array = MkTerm "array" 1 
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    addToArray = MkTerm ":" 2
    append = MkTerm "++" 2
    hasType = MkPredicate "hasType" 2 
    r1 = Rule (hasType [addToArray [x,y],array [z]]) [hasType [x,z],hasType [y,array [z]]] 
    r2 = Rule (hasType [append [x,y],array [z]]) [hasType [x,array [z]],hasType [y,array [z]]] 
    
 
createBooleanRules:: [Clause]

createBooleanRules = [r1,r2,r3,r4]
    where
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    and = MkTerm "and" 2
    or = MkTerm "or" 2
    not = MkTerm "not" 1
    hasType = MkPredicate "hasType" 2 
    r1 =  Rule (hasType [ifThenElse [x,y,z],w]) [hasType [x,bool],hasType [y,w],hasType [z,w]]
    r2 = Rule (hasType [and [x,y], bool]) [hasType [x,bool],hasType [y,bool]]
    r3 = Rule (hasType [or [x,y], bool]) [hasType [x,bool],hasType [y,bool]]
    r4 = Rule (hasType [not [x], bool]) [hasType [x,bool]]


    
    
-- aritProgram which includes a small mistake in the rules
aritProgram2 :: Program

aritProgram2 = MkProgram (r1:r2:r3:facts)
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2 
    facts = createFacts [hasType [true,bool], hasType [false,bool],hasType [zero,nat] ]
    r1 = Rule (hasType [succ [x],nat]) [hasType [x,nat]]
    r2 = Rule (hasType [leq [x,y],bool]) [hasType [x,bool],hasType [y,nat]]  -- Verandering tov vorige
    r3 =  Rule (hasType [ifThenElse [x,y,z],w]) [hasType [x,bool],hasType [y,w],hasType [z,w]]
   

-- aritProgram which includes a small mistake in the rules   
aritProgram3 = MkProgram (r1:r2:r3:facts)
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2 
    facts = createFacts [hasType [true,bool], hasType [false,bool],hasType [zero,nat] ]
    r1 = Rule (hasType [succ [x],bool]) [hasType [x,nat]] -- verandering
    r2 = Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]
    r3 =  Rule (hasType [ifThenElse [x,y,z],w]) [hasType [x,bool],hasType [y,w],hasType [z,w]]


-- aritProgram which includes a small mistake in the rules
aritProgram4 = MkProgram (r1:r2:r3:facts)
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2 
    facts = createFacts [hasType [true,bool], hasType [false,bool],hasType [zero,nat] ]
    r1 = Rule (hasType [succ [x],nat]) [hasType [x,nat]] -- verandering
    r2 = Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]
    r3 =  Rule (hasType [ifThenElse [x,y,z],w]) [hasType [x,bool],hasType [y,w],hasType [z,w]]
    r4 = Rule (hasType [z,w]) [hasType [z,MkTerm "Error" 0 []]]
  

-- Generates a program  with parents and such ...  
parentProgram :: Program

parentProgram = MkProgram [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,r1,r2]
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
        
        

-- Create a fact of each Predicate given in a list
createFacts :: [Predicate] -> [Clause]

createFacts [] = []

createFacts (x:xs) = (Rule x []) : createFacts xs



 
    