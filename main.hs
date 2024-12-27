import Data.List

------ Numbers ex1 ------
fact 0 = 1
fact n = n * fact (n - 1)

------ Numbers ex2 ------
combination 0 _ = 0
combination _ 0 = 1
combination n 1 = n
combination n k
  | n == k = 1
  | n > k = fact n / (fact k * fact (n - k))

------ Numbers ex3 ------
combList 0 = [0]
combList n = [combination n x | x <- [0 .. n]]

-------- Lists ex1 ------
remove1 _ [] = []
remove1 x (y : ys)
  | x == y = ys
  | otherwise = y : remove1 x ys

remEvenAux [] _ = []
remEvenAux (x : xs) pos
  | even pos = remEvenAux (remove1 x xs) (pos + 1)
  | otherwise = x : remEvenAux xs (pos + 1)

removeEven xs = remEvenAux xs 1

-------- Lists ex2 ------
sumOddAux [] _ acc = acc
sumOddAux (x : xs) pos acc
  | odd pos = sumOddAux xs (pos + 1) (acc + x)
  | otherwise = sumOddAux xs (pos + 1) acc

sumOdd xs = sumOddAux xs 1 0

------ Lists ex4 ------
minOddAux [] = []
minOddAux (x : xs)
  | odd x = x : minOddAux xs
  | otherwise = minOddAux xs

minOdd xs = case sort (minOddAux xs) of
  (x : y : xs) -> (x, y)
  [x] -> (x, x)
  [] -> (0, 0)

------ Lists ex6 ------
pairListAux [] _ = []
pairListAux (x : xs) acc = (x, acc) : pairListAux xs (acc + x)

pairList [] = []
pairList xs = pairListAux xs 0

------ Matrix ex 2 ------
colsums [] = []
colsums matrix = foldl addColumn (listAcc (length (head matrix))) matrix
  where
    addColumn acc [] = acc
    addColumn (x : xs) (y : ys) = (x + y) : addColumn xs ys
    listAcc 0 = []
    listAcc n = 0 : listAcc (n - 1)

------ Matrix ex 5 ------
square xxs = foldr (\xs b -> b && (length xs == length xxs)) True xxs

triangularAux [] _ = True
triangularAux (xs : xxs) rowIndex =
  zeros xs rowIndex
    && triangularAux xxs (rowIndex + 1)
  where
    zeros [] _ = True
    zeros (x : xs) rowIndex
      | rowIndex == 0 = (x == 0) && zeros xs 0
      | otherwise = zeros xs (rowIndex - 1)

lowertriangular xxs = square xxs && triangularAux xxs 1

-- Trees

data BST a
  = Void
  | Node
      { val :: a,
        left, right :: BST a
      }
  deriving (Eq, Ord, Read, Show)

------ ex1 ------
sum Void = 0
sum (Node v l r) = v + sum l + sum r

------ ex 4 ------
bstElem Void _ = False
bstElem (Node v l r) x
  | v == x = True
  | x > v = bstElem r x
  | x < v = bstElem l x

------ ex 6 ------
bst2ListAux Void acc = acc
bst2ListAux (Node v l r) acc = bst2ListAux l (v : bst2ListAux r acc)

bst2List (Node v l r) = bst2ListAux (Node v l r) []

------ ex 9 ------
height Void = -1
height (Node v l r) = 1 + max (height l) (height r)

annotate Void = Void
annotate (Node v l r) = Node (v, height (Node v l r)) (annotate l) (annotate r)

------ ex 10 ------
almostBalanced Void = False
almostBalanced (Node v l r) = check (height l) (height r) && almostBalanced l && almostBalanced r
  where
    check a b = abs (a - b) <= 1

-- Generic trees
data Tree a = Void1 | Node1 a [Tree a]
  deriving (Eq, Show)

------ ex 1 ------
treefold :: (Eq a, Show a) => (a -> [b] -> b) -> b -> Tree a -> b
treefold f acc Void1 = acc
treefold f acc (Node1 v tree) = f v (map (treefold f acc) tree)

------ ex 2 ------
height :: (Eq a, Show a) => Tree a -> Int
height = treefold (\v hSubTree -> 1 + foldr max (-1) hSubTree) (-1)

------ ex 3 ------
simplify :: (Eq a, Show a) => Tree a -> Tree a
simplify = treefold (\v xs -> Node1 v (removeDuplicates xs)) Void1

removeDuplicates [Void1] = [Void1]
removeDuplicates [] = []
removeDuplicates (Void1 : xs) = removeDuplicates xs
removeDuplicates (x : xs) = x : removeDuplicates xs

------ Quad Trees ------

data QT a
  = C a
  | Q (QT a) (QT a) (QT a) (QT a)
  deriving (Eq, Show)

------ ex 1 ------

buildNSimplify :: (Eq a, Show a) => QT a -> QT a -> QT a -> QT a -> QT a
buildNSimplify (C a1) (C a2) (C a3) (C a4)
  | a1 == a2 && a2 == a3 && a3 == a4 = C a1
  | otherwise = Q (C a1) (C a2) (C a3) (C a4)
buildNSimplify q1 q2 q3 q4 = Q q1 q2 q3 q4

------ ex 2 ------ error if input is not QT tree
simplify2 (C a) = C a
simplify2 (Q q1 q2 q3 q4) = buildNSimplify (simplify2 q1) (simplify2 q2) (simplify2 q3) (simplify2 q4)

------ ex 3 ------
mapQT f (C a) = C (f a)
mapQT f (Q q1 q2 q3 q4) = buildNSimplify (mapQT f q1) (mapQT f q2) (mapQT f q2) (mapQT f q3)

------ Matrix using Quad Trees ------
-- are square matrixes
data Mat a = Mat
  { nexp :: Int, -- nexp = 0 -> matrix 1*1 (2^0 * 2^0)
    mat :: QT a
  }
  deriving (Eq, Show)

------ ex 1 ------
onlyZeros :: (Eq a, Num a) => QT a -> Bool
onlyZeros (C a)
  | a == 0 = True
  | otherwise = False
onlyZeros (Q q1 q2 q3 q4) = onlyZeros q1 && onlyZeros q2 && onlyZeros q3 && onlyZeros q4

lowertriangular1 :: (Eq a, Num a) => Mat a -> Bool
lowertriangular1 (Mat 0 _) = True
lowertriangular1 (Mat n (C a))
  | a == 0 = True
  | otherwise = False
lowertriangular1 (Mat n (Q q1 q2 q3 q4)) =
  onlyZeros q2 -- check if the "quadrant" at the top right has all 0s
    && lowertriangular1 (Mat (n - 1) q1)
    && lowertriangular1 (Mat (n - 1) q4) -- q3 (lower left quadrant) does not need to be checked, it can have any number

------ ex 2 ------
uppertriangular1 :: (Eq a, Num a) => Mat a -> Bool
uppertriangular1 (Mat 0 _) = True
uppertriangular1 (Mat n (C a))
  | a == 0 = True
  | otherwise = False
uppertriangular1 (Mat n (Q q1 q2 q3 q4)) =
  onlyZeros q3
    && uppertriangular1 (Mat (n - 1) q1)
    && uppertriangular1 (Mat (n - 1) q4)