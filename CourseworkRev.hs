{- DO NOT CHANGE MODULE NAME, if you do, the file will not load properly -}
module CourseworkRev where

import qualified Data.Set as HS (fromList, toList)
import Test.QuickCheck

{-
  Your task is to design a datatype that represents the mathematical concept of
  a (finite) set of elements (of the same type). We have provided you with an
  interface (do not change this!) but you will need to design the datatype and
  also support the required functions over sets. Any functions you write should
  maintain the following invariant: no duplication of set elements.

  There are lots of different ways to implement a set. The easiest is to use a
  list. Alternatively, one could use an algebraic data type, wrap a binary
  search tree, or even use a self-balancing binary search tree. Extra marks will
  be awarded for efficient implementations (a self-balancing tree will be more
  efficient than a linked list for example).

  You are **NOT** allowed to import anything from the standard library or other
  libraries. Your edit of this file should be completely self-contained.

  **DO NOT** change the type signatures of the functions below: if you do, we
  will not be able to test them and you will get 0% for that part. While sets
  are unordered collections, we have included the Ord constraint on some
  signatures: this is to make testing easier.

  You may write as many auxiliary functions as you need. Everything must be in
  this file.

  See the note **ON MARKING** at the end of the file.
-}

{-
   PART 1.
   You need to define a Set datatype.
-}

-- you **MUST** change this to your own data type. The declaration of Set a =
-- Int is just to allow you to load the file into ghci without an error, it
-- cannot be used to represent a set.
data Set a = Empty | Node (Set a) a (Set a) deriving (Show)

{-
   PART 2.
   If you do nothing else, you must get the toList, fromList and equality working. If they
   do not work properly, it is impossible to test your other functions, and you
   will fail the coursework!
-}

-- toList {2,1,4,3} => [1,2,3,4]
-- the output must be sorted.
toList :: Ord a => Set a -> [a]
toList Empty = []
toList (Node l m r) = toList l ++ [m] ++ toList r

-- fromList: do not forget to remove duplicates!
fromList :: Ord a => [a] -> Set a
fromList []   = Empty
fromList [m]  = Node Empty m Empty
fromList xs = Node (fromList (rmvDuplicates (isort l))) m (fromList (rmvDuplicates (isort r))) where 
  mindex = length (rmvDuplicates xs) `div` 2
  m = rmvDuplicates (isort xs) !! mindex
  l = take mindex (rmvDuplicates (isort xs))
  r = drop (mindex+1) (rmvDuplicates (isort xs))

-- Make sure you satisfy this property. If it fails, then all of the functions
-- on Part 3 will also fail their tests
toFromListProp :: IO ()
toFromListProp =
  quickCheck
    ((\xs -> (HS.toList . HS.fromList $ xs) == (toList . fromList $ xs)) :: [Int] -> Bool)

-- test if two sets have the same elements (pointwise equivalent).
instance (Ord a) => Eq (Set a) where
  s1 == s2 = toList s1 == toList s2

-- you should be able to satisfy this property quite easily
eqProp :: IO ()
eqProp =
  quickCheck ((\xs -> (fromList . HS.toList . HS.fromList $ xs) == fromList xs) :: [Char] -> Bool)

{-
   PART 3. Your Set should contain the following functions. DO NOT CHANGE THE
   TYPE SIGNATURES.
-}

-- the empty set
empty :: Set a
empty = Empty

-- is it the empty set?
isNull :: Set a -> Bool
isNull Empty = True
isNull (Node l m r) = False

-- build a one element Set
singleton :: a -> Set a
singleton m = Node Empty m Empty

-- insert an element *x* of type *a* into Set *s*. Make sure there are no
-- duplicates!
insert :: (Ord a) => a -> Set a -> Set a
insert x Empty = Node Empty x Empty
insert x (Node l m r) 
  | m == x  = Node l m r
  | x < m   = Node (insert x l) m r
  | otherwise = Node l m (insert x r)

-- join two Sets together be careful not to introduce duplicates.
union :: (Ord a) => Set a -> Set a -> Set a
union Empty Empty = Empty
union (Node l m r) Empty = Node l m r
union Empty (Node l m r) = Node l m r
union (Node l m r) (Node l2 m2 r2)
    | member m (Node l2 m2 r2) = (l `union` Node l2 m2 r2) `union` r
    | otherwise = (l `union` insert m (Node l2 m2 r2)) `union` r

-- return, as a Set, the common elements between two Sets
intersection :: (Ord a) => Set a -> Set a -> Set a
intersection Empty Empty = Empty
intersection Empty (Node l m r) = Empty
intersection (Node l m r) Empty = Empty
intersection (Node l m r) list2
    | member m list2 = Node (intersection l list2) m (intersection r list2)
    | otherwise = removeSet m (Node (intersection l list2) m (intersection r list2))

-- all the elements in *s1* not in *s2*
-- {1,2,3,4} `difference` {3,4} => {1,2}
-- {} `difference` {0} => {}
difference :: (Ord a) => Set a -> Set a -> Set a
difference Empty Empty = Empty
difference Empty (Node l m r) = Empty
difference (Node l m r) Empty = Node l m r
difference (Node l m r) list2
    | member m list2 = removeSet m (Node (difference l list2) m (difference r list2))
    | otherwise = Node (difference l list2) m (difference r list2) 

-- is element *x* in the Set s1?
member :: (Ord a) => a -> Set a -> Bool
member x Empty = False  
member x (Node l m r)
    | x == m = True  
    | x < m  = member x l
    | x > m  = member x r

-- how many elements are there in the Set?
cardinality :: Set a -> Int
cardinality Empty = 0
cardinality (Node l m r) = cardinality l + 1 + cardinality r 

-- apply a function to every element in the Set
setmap :: (Ord b) => (a -> b) -> Set a -> Set b
setmap f Empty = Empty
setmap f (Node l m r) = fromList(toList(Node (setmap f l) (f m) (setmap f r)))

-- right fold a Set using a function *f*
setfoldr :: (a -> b -> b) -> b -> Set a -> b
setfoldr f acc Empty = acc
setfoldr f acc (Node l m r) = setfoldr f (f m (setfoldr f acc r)) l

-- remove an element *x* from the set
-- return the set unaltered if *x* is not present
removeSet :: (Ord a) => a -> Set a -> Set a
removeSet x Empty = Empty
removeSet x xs
    | x `elem` toList xs = fromList(rmv x (toList xs))
    | otherwise = xs

-- powerset of a set
-- powerset {1,2} => { {}, {1}, {2}, {1,2} }
powerSet :: Set a -> Set a
powerSet (Node l m r) = undefined
--insert m (powerSet l `union` powerSet r)

--auxillary functions
--isort
isort :: Ord a => [a] -> [a]
isort [] = []
isort (x:xs) = insert x (isort xs)
   where insert x [] = [x]
         insert x (y : ys) = if x <= y then x : y : ys else y : insert x ys

--rmvDuplicates
rmvDuplicates :: (Eq a) => [a] -> [a]
rmvDuplicates [] = []
rmvDuplicates list = rmvDuplicate list []

--rmvDuplicate
rmvDuplicate :: (Eq a) => [a] -> [a] -> [a]
rmvDuplicate [] _ = []
rmvDuplicate (x:xs) list2
    | x `elem` list2 = rmvDuplicate xs list2
    | otherwise = x : rmvDuplicate xs (x:list2)

--rmv
rmv :: (Eq a) => a -> [a] -> [a]
rmv x [] = []
rmv x (y:ys) 
    | x == y  = rmv x ys
    | otherwise = y : rmv x ys

{-
   ON MARKING:

   Be careful! This coursework will be marked using QuickCheck, against
   Haskell's own Data.Set implementation. This testing will be conducted
   automatically via a marking script that tests for equivalence between your
   output and Data.Set's output. There is no room for discussion, a failing test
   means that your function does not work properly: you do not know better than
   QuickCheck and Data.Set! Even one failing test means 0 marks for that
   function. Changing the interface by renaming functions, deleting functions,
   or changing the type of a function will cause the script to fail to load in
   the test harness. This requires manual adjustment by a TA: each manual
   adjustment will lose 10% from your score. If you do not want to/cannot
   implement a function, leave it as it is in the file (with undefined).

   Marks will be lost for too much similarity to the Data.Set implementation.

   Pass: creating the Set type and implementing toList and fromList is enough
   for a passing mark of 40%, as long as both toList and fromList satisfy the
   toFromListProp function.

   The maximum mark for those who use Haskell lists to represent a Set is 70%.
   To achieve a higher grade than is, one must write a more efficient
   implementation. 100% is reserved for those brave few who write their own
   self-balancing binary tree.
-}
