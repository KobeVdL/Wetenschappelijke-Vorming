module Tests where
    
import Project
import BasicProlog
import Shuffle
import TopDown
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Debug.Trace

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe


test7 = print (semiNaiveBottomUp program 3 Map.empty Map.empty) --test met even getallen implementeren
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
    program = MkProgram [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,r1,r2]
    



    
    
test8 = print (semiNaiveBottomUp evenProgram 8 Map.empty Map.empty)
    
    
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


test4 = print (addToCorrectScheme p3 m3)
        where
        t1 = MkTerm "a" 0 []
        t2 = MkTerm "c" 0 []
        t3 = MkTerm "b" 1 [t1] 
        p1 = MkPredicate "a" 1 [t1]
        p2 = MkPredicate "b" 1 [t2]
        p3 = MkPredicate "c" 1 [t3]
        m =  Map.empty
        m1 = Map.insert "a" Set.empty m 
        m2 = Map.insert "b" Set.empty m1
        m3 = Map.insert "c" Set.empty m2

         
test6 = print (show (findNewPred r Map.empty m1))
    where 
    t1 = MkTerm "a" 0 []
    t2 = MkPredicate "b" 1 [Variable "x"]
    t3 = MkPredicate "c" 1 [Variable "x"] 
    r = Rule t3 [t2]
    m = Map.empty
    m1 = Map.insert "b" (Set.fromList [[t1]]) m 
    

binderPredTest = bindRule (Rule (hasType [leq [x,y],bool]) [hasType [x,nat],hasType [y,nat]]) binder  
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
    Just binder= findBinderPred (hasType [y]) (hasType [leq [x,y]]) 

    
ariTest :: Scheme

ariTest = semiNaiveBottomUp aritProgram 3 Map.empty Map.empty


ariTest2 :: Scheme

ariTest2 = semiNaiveBottomUp aritProgram2 3 Map.empty Map.empty


ariTest3 :: Scheme

ariTest3 = semiNaiveBottomUp aritProgram3 3 Map.empty Map.empty -- Bij maar 2 keer geeft wel true terug omdat de formule nergens in gebruikt wordt
