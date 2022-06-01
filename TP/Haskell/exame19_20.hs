data BTree a = Empty | Node a (BTree a) (BTree a) deriving (Eq, Show)

inf max =
    let fun n = if n > max then Empty else Node n (fun (n+1)) (fun (n+1))
    in fun 0

l = \n -> \step -> n : l (n + step) step

myfun = \l -> case l of
    [] -> []
    h : t -> case t of
        [] -> h : []
        h' : t' -> h : fun ((h + h') : t')

fun [] = []
fun [x] = [x]
fun (x:y:xys) = x : fun ((x+y):xys)

data RTree a = REmpty | RNode a [RTree a] deriving (Eq, Show)

sumRT :: RTree Int -> Int
sumRT = \rt -> case rt of
    REmpty -> 0
    RNode x lrt -> x + foldr h 0 lrt
  where
      h = \roseT -> \n -> (sumRT roseT) + n

rt :: RTree Int
rt = RNode 1 [RNode 1 [REmpty], RNode 6 [REmpty, RNode 1 [RNode 1 []]]]