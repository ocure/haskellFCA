>module LatticeIPred where

>import Data.List

----------------------------------------------------------
Implementation of the LATTICE algo of Christian Lindig (Fast Concept Analysis)

>groupObj [] is rs = rs
>groupObj (o:os) is rs = groupObj os is ([(o, [snd i|i<-is, (fst i) ==o])] ++ rs) 

>groupAtt [] is rs = rs
>groupAtt (a:as) is rs = groupAtt as is ([(a, [fst i|i<-is, (snd i) ==a])] ++ rs) 

>setIntersect [] = []
>setIntersect (x:[]) = x
>setIntersect (x:xs) = intersect x (setIntersect xs)

>prime os gs = setIntersect tmp
> 	where tmp = [ snd g | g <- gs, o<-os, (fst g)==o] 

neighbors objectsMap attritubesMap ConceptToComputNeighborsFor 

>neighbors gos aos igs min ns [] = ns  
>neighbors gos aos igs min ns (gg:ggs) 
>	| intersect min (tmpG1 \\ (nub (igs ++ [gg]))) == [] = neighbors gos aos igs min (ns ++ [(tmpG1,tmpM1)]) ggs
>	| otherwise = neighbors gos aos igs (min \\ [gg]) ns ggs 
>	where tmpM1 = prime (igs ++ [gg]) gos
>	      tmpG1 = prime tmpM1 aos	

>lattice gos aos gs = loopLattice gos aos gs (neighbors gos aos [] gs [] gs) []


>loopLattice gos aos gs [] rs = rs
>loopLattice gos aos gs (n:ns) rs = loopLattice gos aos gs ((nub (ns ++ (neighbors gos aos (fst n) (gs \\ (fst n)) [] (gs \\ (fst n)) ))) \\[([],[])])  (rs ++ [n])

To run Lattice only, compute: lattice (groupObj g1 i1 []) (groupAtt m1 i1 []) g1
or the following main function

>main = print (lattice (groupObj g1 i1 []) (groupAtt m1 i1 []) g1 )


Examples for Lattice

>g1 = ["1","2","3","4","5"]
>m1 = ["a","b","c","d","e"]
>i1 = [("1","a"),("1","b"),("1","c"),("2","a"),("2","c"),("3","a"),("3","c"),("3","d"),("4","a"),("4","b"),("4","c"),("5","b"),("5","d")]


>g1' = ["1","2","3","4"]
>m1' = ["a","b","c","d","e"]
>i1' = [("1","a"),("1","b"),("1","d"),("2","b"),("2","c"),("3","a"),("3","c"),("3","d"),("3","e"),("4","b"),("4","d")]

>iPredO = ["1","2","3","4","5","6"]
>iPredA = ["a","b","c","d","e"]
>iPredI = [("1","a"),("1","b"),("1","c"),("2","b"),("2","c"),("2","d"),("3","a"),("3","d"),("3","e"),("4","c"),("4","d"),("4","e"),("5","a"),("6","c")]

>medI = ["331","332","333"]
>medA = ["R5DA","R6DA","R7DB"]
>med = [("331","R5DA"),("331","R5DB"),("332","R6DA"),("333","R7DB")]

>di = ["1","2","3","4","5"]
>da = ["a","b","c","d","e"]
>dd = [("1","a"),("1","c"),("2","b"),("2","d"),("3","a"),("3","e"),("4","a"),("4","e"),("5","b"),("5","d")]

Test for a>=0.5

>myTi = ["1","2","3","4","5","6","7"]
>myTa = ["a","b","c","d","e","f"]
>myTd = [("5","a"),("6","a"),("7","a"),("4","b"),("5","b"),("6","b"),("7","b"),("4","c"),("5","c"),("6","c"),("7","c"),("4","d"),("5","d"),("1","e"),("2","e"),("4","e"),("5","e"),("1","f"),("2","f")]

Test for a>0.8

>myTd2 = [("5","a"),("7","a"),("5","b"),("6","b"),("7","b"),("4","c"),("5","c"),("6","c"),("4","d"),("5","d"),("2","e"),("4","e"),("5","e"),("1","f")]

Test for a=0.7

>myTd3 = [("5","a"),("6","a"),("7","a"),("5","b"),("6","b"),("7","b"),("4","c"),("5","c"),("6","c"),("4","d"),("5","d"),("1","e"),("2","e"),("4","e"),("5","e"),("1","f"),("2","f")]

-----------------------------------------------------------------
Implementation of the iPred algorithm for computing the Hasse diagram of a concept lattice 
Detailed in ICFCA 2009: Yet a Faster Algorithm for Building the Hasse Diagram of a Concept Lattice

cs is the list of formal concepts
ds is the set delta
ls represents the set of elements of the lattice
bs is the border

>mySort :: (Ord a) => [[a]] -> [[a]]
>mySort [] = []
>mySort (x:xs) = mySort left ++ [x] ++ mySort right
>  where left = [ y | y <-xs, length y <= length x]
>        right =  [ y | y<-xs, length y > length x]

>start xs = 	let
>			cs = mySort (map (concat) xs)
>			ds = [("",[])] ++ [ (x,[]) | x<-cs ]
>		in mainLoop ([""]++cs) ds [] []

>mainLoop [] ds ls bs = ls
>mainLoop (c:cs) ds ls bs = processCandidate (c:cs) ds ls bs (candidate c bs)

>processCandidate (c:cs) ds ls bs [] = mainLoop cs ds ls (bs ++ [c])
>processCandidate (c:cs) ds ls bs (k:ks) 
>	| emptyIntersection ds c k  = processCandidate (c:cs) (updateDelta ds c k [])  ((k,c):ls) (bs \\ [k]) ks
>       | otherwise     = processCandidate (c:cs) ds ls bs ks

>emptyIntersection :: (Eq a) => [([a], [[a]])] -> [a] -> [a] -> Bool
>emptyIntersection ds c k 
>       | or (map (\y -> myIntersect c y) (getConceptsOfDeltaK ds k)) = False
>       | otherwise = True 

>myIntersect c [] = False
>myIntersect c ds 
>	| intersect c ds /= [] = True
>	| otherwise = False	

>getConceptsOfDeltaK :: Eq a =>  [([a], [[a]])] -> [a] -> [[a]]
>getConceptsOfDeltaK [] k = []
>getConceptsOfDeltaK (d:ds) k
>	| (fst d)==k = snd d
>	| otherwise  = getConceptsOfDeltaK  ds k

>updateDelta [] c k ds' = ds'
>updateDelta (d:ds) c k ds' 
> 	| (fst d)==k = ds' ++ [(fst d, (snd d) ++ ((c \\ k):[]) )] ++ ds
>       | otherwise = updateDelta ds c k (d : ds')

>candidate :: (Eq a) => [a] -> [[a]] -> [[a]]
>candidate c bs = nub [ intersect c b | b<-bs]

To run iPred only, compute (start ganter) or the following main function 

>main2 = print (start ganter)

To compute the Hasse diagram on the formal concepts calculater by Lattice, run:

>main3 = print (start [ snd x | x<- (lattice (groupObj g1 i1 []) (groupAtt m1 i1 []) g1 )])

>main4 = print (start [ snd x | x<- (lattice (groupObj myTi myTd []) (groupAtt myTa myTd []) myTi )])

>main5 = print (start [ snd x | x<- (lattice (groupObj myTi myTd3 []) (groupAtt myTa myTd3 []) myTi )])

Examples for iPred

>ltest = [["c","d","e"],["d","e"],["a","b","c"],["b","c","d"],["c"],["b","c"],["d"],["c","d"],["a","d","e"],["a"],["a","b","c","d","e"]]

>ganter = [["a","c","d","e"],["a","b","d"],["d"],["b","d"],["b","c"],["c"],["b"],["a","d"],["a","b","c","d","e"]]

>showGMF ls = "graph [ "++ showGMFEdges ls ++ " ]"
>showGMFEdges [] = ""
>showGMFEdges (l:ls) = "edge [ source \""++ fst l ++ "\" target \"" ++ snd l ++"\" value 1 ]" ++ showGMFEdges ls


