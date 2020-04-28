> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE PatternSynonyms #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module Data.Vector where

> import Data.Nat
> import Data.Type.Nat
> import Data.Type.Equality
> import Data.Foldable
> import Data.Proxy
> import Data.Kind
> import Prelude hiding
>   (head, tail, last, init, uncons, map, filter) -- agregar nombres aca




En este caso que vamos a querer usar 'en serio' el tipo de datos poner
el índice Nat antes que el parámetro Type es una buena idea (por
ej. para implementar las instancias para la clase Functor)

> data Vec (n :: Nat) (a :: Type) :: Type where
>   VNil  :: Vec Z a
>   VCons :: a -> Vec n a -> Vec (S n) a

> infixr 2 :.
> pattern (:.) :: a -> Vec n a -> Vec (S n) a
> pattern a :. as = VCons a as

> example3 = 'a' :. 'b' :. 'c' :. VNil

> instance Show a => Show (Vec Z a) where
>   show (VNil) = "[]"
> instance Show a => Show (Vec (S Z) a) where
>   show (a :. VNil) = '[': show a ++ "]"
> instance (Show a, Show (Vec (S n) a)) => Show (Vec (S (S n)) a) where
>   show (a :. as) = let ('[':shas) = show as
>                    in '[' : show a ++ ", " ++ shas 

> data SomeVec a where
>   SomeVec :: Vec n a -> SomeVec a

> fromSomeVec :: SNat n -> SomeVec a -> Maybe (Vec n a)
> fromSomeVec n (SomeVec vs) = fromSomeVec' n vs
>
> fromSomeVec' :: SNat n -> Vec m a -> Maybe (Vec n a)
> fromSomeVec' SZ VNil = Just VNil
> fromSomeVec' SZ _    = Nothing
> fromSomeVec' (SS _) VNil         = Nothing
> fromSomeVec' (SS n) (VCons a as) = do as' <- fromSomeVec' n as
>                                       return $ VCons a as'

(++) :: [a] -> [a] -> [a]

> append :: Vec n a -> Vec m a -> Vec (n :+ m) a
> append VNil as = as
> append (VCons a as) as' = a :. append as as'

Esto en lugar del anterior no anda:

< append (a :. as) as' = a :. append as as'

Con pattern synonyms se pierder algo al hacer pattern matching?



head :: [a] -> a

> head :: Vec (S n) a -> a
> head (VCons a _) = a


last :: [a] -> a

> class Last (n :: Nat) where
>   last :: Vec (S n) a -> a

> instance Last Z where
>   last (VCons a VNil) = a

> instance Last n => Last (S n) where
>   last (VCons a as) = last as

(no me gusta que el índice no sea el largo del vector, pero solo se me
 ocurre generar una constraint)


> last' :: Vec (S n) a -> a
> last' (VCons a VNil) = a 
> last' (VCons a as@(VCons _ _))   = last' as 

tail :: [a] -> [a]

> tail :: Vec (S n) a -> Vec n a
> tail (VCons _ as) = as


init :: [a] -> [a]

> class Init (n :: Nat) where
>   init :: Vec (S n) a -> Vec n a

> instance Init Z where
>   init (a :. VNil) = VNil

> instance Init n => Init (S n) where
>   init (a :. as) = a :. init as


> init' :: Vec (S n) a -> Vec n a
> init' (VCons a VNil) = VNil 
> init' (VCons a as@(VCons _ _))   = VCons a $ init' as 

Return all the elements of a list except the last one. The list must
 be non-empty.

uncons :: [a] -> Maybe (a, [a])
Decompose a list into its head and tail. If the list is empty, returns
 Nothing. If the list is non-empty, returns Just (x, xs), where x is
 the head of the list and xs its tail.

> uncons1 :: Vec (S n) a -> (a, Vec n a)
> uncons1 (VCons a as) = (a, as)

(no creo que el uncons con Maybe sea de mucha utilidad, pero
esta puede ser una implementacion)

> uncons :: Vec n a -> Maybe (a, Vec (SafePred n) a)
> uncons VNil         = Nothing
> uncons (VCons a as) = Just (a, as)

> type family SafePred (n :: Nat) :: Nat where
>   SafePred Z     = Z
>   SafePred (S n) = n

> null :: Vec n a -> Bool
> null = foldr (\_ _ -> False) True

> null' :: Vec n a -> Maybe (n :~: Z)
> null' VNil        = Just Refl
> null' (VCons _ _) = Nothing

Test whether the structure is empty. The default implementation is
 optimized for structures that are similar to cons-lists, because
 there is no general way to do better.

> length :: Vec n a -> Int
> length = foldl' (\c _ -> c+1) 0


> length' :: Vec n a -> SNat n
> {-length' VNil = SZ
> length' (VCons _ as) = SS $ length' as-}
> length' = foldrN (const SS) SZ


Returns the size/length of a finite
 structure as an Int. The default implementation is optimized for
 structures that are similar to cons-lists, because there is no
 general way to do better.  List transformations

map :: (a -> b) -> [a] -> [b]

> map :: (a -> b) -> Vec n a -> Vec n b
> map _ VNil         = VNil
> map f (VCons a as) = VCons (f a) $ map f as

reverse :: [a] -> [a]
reverse xs returns the elements of xs in reverse order. xs must be
 finite.

> reverse :: KnownNat n => Vec n a -> Vec n a
> reverse = unFlip . foldlN (flip flipVCons) flipVNil 





intersperse :: a -> [a] -> [a]
The intersperse function takes an element and a list and
 `intersperses' that element between the elements of the list. For
 example,

intercalate :: [a] -> [[a]] -> [a]
intercalate xs xss is equivalent to (concat (intersperse xs xss)). It inserts the list xs in between the lists in xss and concatenates the result.

intercalate ", " ["Lorem", "ipsum", "dolor"]
"Lorem, ipsum, dolor"

transpose :: [[a]] -> [[a]]
The transpose function transposes the rows and columns of its argument. For example,
transpose [[1,2,3],[4,5,6]] => [[1,4],[2,5],[3,6]]

If some of the rows are shorter than the following rows, their elements are skipped:
transpose [[10,11],[20],[],[30,31,32]] => [[10,20,30],[11,31],[32]]

subsequences :: [a] -> [[a]]
The subsequences function returns the list of all subsequences of the argument.

subsequences "abc" => ["","a","b","ab","c","ac","bc","abc"]

permutations :: [a] -> [[a]]
The permutations function returns the list of all permutations of the argument.

permutations "abc" => ["abc","bac","cba","bca","cab","acb"]


> instance Foldable (Vec n) where
>   foldr _ z VNil         = z
>   foldr f z (VCons a as) = f a (foldr f z as) 

foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
Left-associative fold of a structure.


foldl' :: Foldable t => (b -> a -> b) -> b -> t a -> b
Left-associative fold of a structure but with strict application of the operator.

foldl1 :: Foldable t => (a -> a -> a) -> t a -> a
A variant of foldl that has no base case, and thus may only be applied to non-empty structures.

foldl1 f = foldl1 f . toList
foldl1' :: (a -> a -> a) -> [a] -> a
A strict version of foldl1

foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b
Right-associative fold of a structure.


foldr1 :: Foldable t => (a -> a -> a) -> t a -> a
A variant of foldr that has no base case, and thus may only be applied to non-empty structures.

foldr1 f = foldr1 f . toList
Special folds

concat :: Foldable t => t [a] -> [a]
The concatenation of all the elements of a container of lists.

concatMap :: Foldable t => (a -> [b]) -> t a -> [b]
Map a function over all the elements of a container and concatenate the resulting lists.

and :: Foldable t => t Bool -> Bool
and returns the conjunction of a container of Bools. For the result to be True, the container must be finite; False, however, results from a False value finitely far from the left end.

or :: Foldable t => t Bool -> Bool
or returns the disjunction of a container of Bools. For the result to be False, the container must be finite; True, however, results from a True value finitely far from the left end.

any :: Foldable t => (a -> Bool) -> t a -> Bool
Determines whether any element of the structure satisfies the predicate.

all :: Foldable t => (a -> Bool) -> t a -> Bool
Determines whether all elements of the structure satisfy the predicate.

sum :: (Foldable t, Num a) => t a -> a
The sum function computes the sum of the numbers of a structure.

product :: (Foldable t, Num a) => t a -> a
The product function computes the product of the numbers of a structure.

maximum :: forall a. (Foldable t, Ord a) => t a -> a
The largest element of a non-empty structure.

minimum :: forall a. (Foldable t, Ord a) => t a -> a
The least element of a non-empty structure.


folds parametricos en n

> foldrN :: (forall m. a -> b m -> b (S m)) -> b Z -> Vec n a -> b n
> foldrN f e VNil = e
> foldrN f e (VCons a as) = f a $ foldrN f e as


> foldlN :: forall m n a b . KnownNat m
>   => (forall k. b k -> a -> b (S k)) -> b m -> Vec n a -> b (m :+ n)
> foldlN f e VNil = gcastWith (mzProof $ natSing @ m) e 
> foldlN f e (VCons a as) =
>   gcastWith (msProof (natSing @ m) (Proxy @ n)) $ foldlN f (f e a) as

> newtype FlipVec a n = FlipVec { unFlip :: Vec n a }
> flipVCons a = FlipVec . VCons a . unFlip
> flipVNil  = FlipVec VNil




Building lists
Scans

scanl :: (b -> a -> b) -> b -> [a] -> [b]

scanl' :: (b -> a -> b) -> b -> [a] -> [b]
A strictly accumulating version of scanl

scanl1 :: (a -> a -> a) -> [a] -> [a]
scanl1 is a variant of scanl that has no starting value argument:

scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]

scanr :: (a -> b -> b) -> b -> [a] -> [b]

scanr1 :: (a -> a -> a) -> [a] -> [a]
scanr1 is a variant of scanr that has no starting value argument.
Accumulating maps

mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
The mapAccumL function behaves like a combination of fmap and foldl; it applies a function to each element of a structure, passing an accumulating parameter from left to right, and returning a final value of this accumulator together with the new structure.

mapAccumR :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
The mapAccumR function behaves like a combination of fmap and foldr; it applies a function to each element of a structure, passing an accumulating parameter from right to left, and returning a final value of this accumulator together with the new structure.
Infinite lists

iterate :: (a -> a) -> a -> [a]
iterate f x returns an infinite list of repeated applications of f to x:


iterate' :: (a -> a) -> a -> [a]

repeat :: a -> [a]
repeat x is an infinite list, with x the value of every element.

replicate :: Int -> a -> [a]
replicate n x is a list of length n with x the value of every element. It is an instance of the more general genericReplicate, in which n may be of any integral type.

cycle :: [a] -> [a]
cycle ties a finite list into a circular one, or equivalently, the infinite repetition of the original list. It is the identity on infinite lists.
Unfolding

unfoldr :: (b -> Maybe (a, b)) -> b -> [a]
The unfoldr function is a `dual' to foldr: while foldr reduces a list to a summary value, unfoldr builds a list from a seed value. The function takes the element and returns Nothing if it is done producing the list or returns Just (a,b), in which case, a is a prepended to the list and b is used as the next element in a recursive call. For example,

iterate f == unfoldr (\x -> Just (x, f x))


A simple use of unfoldr:

unfoldr (\b -> if b == 0 then Nothing else Just (b, b-1)) 10 => [10,9,8,7,6,5,4,3,2,1]



Sublists
Extracting sublists

take :: Int -> [a] -> [a]
take n, applied to a list xs, returns the prefix of xs of length n, or xs itself if n > length xs:

It is an instance of the more general genericTake, in which n may be of any integral type.

drop :: Int -> [a] -> [a]
drop n xs returns the suffix of xs after the first n elements, or [] if n > length xs:



splitAt :: Int -> [a] -> ([a], [a])
splitAt n xs returns a tuple where first element is xs prefix of length n and second element is the remainder of the list:

takeWhile :: (a -> Bool) -> [a] -> [a]

takeWhile, applied to a predicate p and a list xs, returns the longest prefix (possibly empty) of xs of elements that satisfy p:

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile p xs returns the suffix remaining after takeWhile p xs:

dropWhileEnd :: (a -> Bool) -> [a] -> [a]

The dropWhileEnd function drops the largest suffix of a list in which the given predicate holds for all elements. For example:
dropWhileEnd isSpace "foo\n" => "foo"

dropWhileEnd isSpace "foo bar" => "foo bar"

dropWhileEnd isSpace ("foo\n" ++ undefined) == "foo" ++ undefined


span :: (a -> Bool) -> [a] -> ([a], [a])
span, applied to a predicate p and a list xs, returns a tuple where first element is longest prefix (possibly empty) of xs of elements that satisfy p and second element is the remainder of the list:

break :: (a -> Bool) -> [a] -> ([a], [a])
break, applied to a predicate p and a list xs, returns a tuple where first element is longest prefix (possibly empty) of xs of elements that do not satisfy p and second element is the remainder of the list:


stripPrefix :: Eq a => [a] -> [a] -> Maybe [a]
The stripPrefix function drops the given prefix from a list. It returns Nothing if the list did not start with the prefix given, or Just the list after the prefix, if it does.

stripPrefix "foo" "foobar" => Just "bar"

stripPrefix "foo" "foo" => Just ""

stripPrefix "foo" "barfoo" => Nothing

group :: Eq a => [a] -> [[a]] The group function takes a list and
 returns a list of lists such that the concatenation of the result is
 equal to the argument. Moreover, each sublist in the result contains
 only equal elements. For example,

group "Mississippi" => ["M","i","ss","i","ss","i","pp","i"]

It is a special case of groupBy, which allows the programmer to supply
 their own equality test.

inits :: [a] -> [[a]]
The inits function returns all initial segments of the argument,
 shortest first. For example, inits "abc" =>["","a","ab","abc"]
Note that inits has the following strictness property: inits (xs ++
 _|_) = inits xs ++ _|_
In particular, inits _|_ = [] : _|_


tails :: [a] -> [[a]]
The tails function returns all final segments of the argument, longest
 first. For example, tails "abc" =>["abc","bc","c",""]

Note that tails has the following strictness property: tails _|_ = _|_ : _|_
Predicates

isPrefixOf :: Eq a => [a] -> [a] -> Bool
The isPrefixOf function takes two lists and returns True iff the first
 list is a prefix of the second.

isSuffixOf :: Eq a => [a] -> [a] -> Bool
The isSuffixOf function takes two lists and returns True iff the first
 list is a suffix of the second. The second list must be finite.


isInfixOf :: Eq a => [a] -> [a] -> Bool
The isInfixOf function takes
 two lists and returns True iff the first list is contained, wholly
 and intact, anywhere within the second.

isSubsequenceOf :: Eq a => [a] -> [a] -> Bool

The isSubsequenceOf function takes two lists and returns True if all
 the elements of the first list occur, in order, in the second. The
 elements do not have to occur consecutively.

elem :: (Foldable t, Eq a) => a -> t a -> Bool infix 4
Does the element occur in the structure?

notElem :: (Foldable t, Eq a) => a -> t a -> Bool infix 4
notElem is the negation of elem.

lookup :: Eq a => a -> [(a, b)] -> Maybe b

lookup key assocs looks up a key in an association list.
Searching with a predicate

find :: Foldable t => (a -> Bool) -> t a -> Maybe a

The find function
 takes a predicate and a structure and returns the leftmost element of
 the structure matching the predicate, or Nothing if there is no such
 element.


filter :: (a -> Bool) -> [a] -> [a]
No hay forma de saber estáticamente el largo del vector resultante.
En un lenguaje de tipos dependientes usaríamos Σ(n∈N,Vec n a)

> filter :: (a -> Bool) -> Vec n a -> SomeVec a
> filter _ VNil = SomeVec VNil
> filter p (VCons a as)
>   = case filter p as of
>       SomeVec as' ->
>         if p a
>         then SomeVec $ VCons a as'
>         else SomeVec as'


partition :: (a -> Bool) -> [a] -> ([a], [a])

> partition :: (a -> Bool) -> Vec n a -> (SomeVec a, SomeVec a)
> partition p as = (filter p as, filter (not . p) as) 

Acá se puede hacer algo que codifique la invariante del largo,
claramente no con SomeVec porque no hay acceso a los índices,



(!!) :: [a] -> Int -> a infixl 9
List index (subscript) operator,
 starting from 0. It is an instance of the more general genericIndex,
 which takes an index of any integral type.

elemIndex :: Eq a => a -> [a] -> Maybe Int

The elemIndex function returns the index of the first element in the
 given list which is equal (by ==) to the query element, or Nothing if
 there is no such element.

elemIndices :: Eq a => a -> [a] -> [Int]

The elemIndices function extends elemIndex, by returning the indices
 of all elements equal to the query element, in ascending order.

findIndex :: (a -> Bool) -> [a] -> Maybe Int

The findIndex function takes a predicate and a list and returns the
 index of the first element in the list satisfying the predicate, or
 Nothing if there is no such element.

findIndices :: (a -> Bool) -> [a] -> [Int]

The findIndices function extends findIndex, by returning the indices
 of all elements satisfying the predicate, in ascending order.


zip :: [a] -> [b] -> [(a, b)]
zip3 :: [a] -> [b] -> [c] -> [(a, b, c)]
zip4 :: [a] -> [b] -> [c] -> [d] -> [(a, b, c, d)]
zip5 :: [a] -> [b] -> [c] -> [d] -> [e] -> [(a, b, c, d, e)]
zip6 :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [(a, b, c, d, e, f)]
zip7 :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [g] -> [(a, b, c, d, e,f,g)]

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipWith4 :: (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]

etc..

unzip :: [(a, b)] -> ([a], [b])
unzip3 :: [(a, b, c)] -> ([a], [b], [c])
unzip4 :: [(a, b, c, d)] -> ([a], [b], [c], [d])


lines :: String -> [String]


words :: String -> [String]

words breaks a string up into a list of words, which were delimited by
 white space.


unwords :: [String] -> String
unwords is an inverse operation to words. It joins words with separating spaces.
unwords ["Lorem", "ipsum", "dolor"] => "Lorem ipsum dolor"

nub :: Eq a => [a] -> [a]

delete :: Eq a => a -> [a] -> [a]

delete x removes the first occurrence of x from its list argument. For example,
delete 'a' "banana" => "bnana"


(\\) :: Eq a => [a] -> [a] -> [a] infix 5

The \\ function is list difference (non-associative). In the result of
 xs \\ ys, the first occurrence of each element of ys in turn (if any)
 has been removed from xs. Thus


union :: Eq a => [a] -> [a] -> [a]

The union function returns the list union of the two lists. For example,

"dog" `union` "cow" => "dogcw"


intersect :: Eq a => [a] -> [a] -> [a]
The intersect function takes the list intersection of two lists. For example,
If the first list contains duplicates, so will the result.

Ordered lists
sort :: Ord a => [a] -> [a]

The sort function implements a stable sorting algorithm. It is a
 special case of sortBy, which allows the programmer to supply their
 own comparison function.

Elements are arranged from from lowest to highest, keeping duplicates
 in the order they appeared in the input.

sortOn :: Ord b => (a -> b) -> [a] -> [a]

Sort a list by comparing the results of a key function applied to each
 element. sortOn f is equivalent to sortBy (comparing f), but has the
 performance advantage of only evaluating f once for each element in
 the input list. This is called the decorate-sort-undecorate paradigm,
 or Schwartzian transform.


insert :: Ord a => a -> [a] -> [a]

The insert function takes an element and a list and inserts the
 element into the list at the first position where it is less than or
 equal to the next element. In particular, if the list is sorted
 before the call, the result will also be sorted. It is a special case
 of insertBy, which allows the programmer to supply their own
 comparison function.



Generalized functions

nubBy :: (a -> a -> Bool) -> [a] -> [a]

The nubBy function behaves just like nub, except it uses a
 user-supplied equality predicate instead of the overloaded ==
 function.
nubBy (\x y -> mod x 3 == mod y 3) [1,2,4,5,6] => [1,2,6]


deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]

The deleteBy function behaves like delete, but takes a user-supplied
 equality predicate.


deleteFirstsBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]

The deleteFirstsBy function takes a predicate and two lists and
 returns the first list with the first occurrence of each element of
 the second list removed.


unionBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
The unionBy function is the non-overloaded version of union.

intersectBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
The intersectBy function is the non-overloaded version of intersect.

groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
The groupBy function is the non-overloaded version of group.
User-supplied comparison (replacing an Ord context)
The function is assumed to define a total ordering.


sortBy :: (a -> a -> Ordering) -> [a] -> [a]
The sortBy function is the non-overloaded version of sort.


insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]

maximumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a

minimumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a

genericLength :: Num i => [a] -> i

The genericLength function is an overloaded version of length. In
 particular, instead of returning an Int, it returns any type which is
 an instance of Num. It is, however, less efficient than length.


genericTake :: Integral i => i -> [a] -> [a]

genericDrop :: Integral i => i -> [a] -> [a]

genericSplitAt :: Integral i => i -> [a] -> ([a], [a])

genericIndex :: Integral i => [a] -> i -> a

genericReplicate :: Integral i => i -> a -> [a]

