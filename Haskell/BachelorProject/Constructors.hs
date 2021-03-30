module Constructors where
    
import Project
import BasicProlog
import Shuffle
import TopDown
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace
import Control.Monad.Trans.Maybe
import Data.Time.Clock.POSIX


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe



evenProgram :: Program

evenProgram = MkProgram [evenBasic, evenRecursive]
    where
    zero = MkTerm "zero" 0 []
    evenBasic = Rule(MkPredicate "even" 1 [zero]) []
    evenRecursive = Rule (MkPredicate "even" 1 [MkTerm "succ" 1 [MkTerm "succ" 1 [Variable "X"]]]) [MkPredicate "even" 1 [Variable "X"]]
    

    
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
    
    
aritProgramUpgraded :: Program

aritProgramUpgraded = MkProgram (r1 :(arrayRules ++ numRules ++ facts))
    where
    zero = MkTerm "Zero" 0 []
    true = MkTerm "True" 0 []
    false = MkTerm "False" 0 []
    emptyArray = MkTerm "[]" 0 []
    letterA = MkTerm "'A'" 0 []
    succ = MkTerm "succ" 1 --lijst geef je zelf mee
    leq = MkTerm "leq" 2 
    array = MkTerm "array" 1 
    nat = MkTerm "nat" 0 []
    bool = MkTerm "bool" 0 []
    char = MkTerm "Char" 0 []
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    hasType = MkPredicate "hasType" 2 
    facts = createFacts [hasType [true,bool], hasType [false,bool],hasType [zero,nat], hasType [letterA,char], hasType [emptyArray,array [x]] ]
    numRules = createNumberRules 
    arrayRules = createArrayRules
    r1 =  Rule (hasType [ifThenElse [x,y,z],w]) [hasType [x,bool],hasType [y,w],hasType [z,w]]
    

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
    
createArrayRules = r2:r1:[]
    where -- :([],[]) => array(array(X)))
    emptyArray = MkTerm "[]" 0 [] --[hasType(:(ifThenElse(True,[],[]),ifThenElse(ifThenElse(False,False,False),[],[])),array(array(array(array(array(X))))))]
    array = MkTerm "array" 1 
    x = Variable "X"
    y = Variable "Y"
    z = Variable "Z"
    w = Variable "W"
    ifThenElse = MkTerm "ifThenElse" 3
    addArray = MkTerm ":" 2
    append = MkTerm "++" 2
    hasType = MkPredicate "hasType" 2 
    r1 = Rule (hasType [addArray [x,y],array [z]]) [hasType [x,z],hasType [y,array [z]]] -- TODO er is nog iets mis met arrays
    r2 = Rule (hasType [append [x,y],array [z]]) [hasType [x,array [z]],hasType [y,array [z]]] -- [hasType(ifThenElse(True,ifThenElse(True,++([],++([],:([],[]))),[]),++(:(++([],ifThenElse(False,[],[])),[]),++([],[]))),array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(array(X))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))]
    

    
    
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
 
    