-- Colin Prelude
-- Standard functions that I need at hand.

module ColinPrelude
    ( groupAt
    , groupsOfN
    , primes
    , isPrime
    , nextPrime
    , primeFactors
    , divides
    , concatWhile
    , concatWhileVia
    , foldlWhile
    , stripHead
    , stripTail
    , isolate
    , isolateBy
    , safeHead
    , body
    , safeBody
    , indent
    , list
    , filterM
    )
    where

import Data.List (groupBy)
      
---------------
-- GENERAL MATH
---------------
tau :: Floating a => a
tau = pi * 2

infixr 5 ///
-- Super division. Reduces an Integral number by its divisor as far as it can.
(///) :: Integral a => a -> a -> a
n /// m | n == 0         = 0
        | m == 1         = n
        | otherwise      = n `sdiv` m

sdiv :: Integral a => a -> a -> a
-- Keep dividing cleanly until you can't.
n `sdiv` m | m `divides` n = n
           | otherwise     = (n `div` m) `sdiv` m

divides :: Integral a => a -> a -> Bool
n `divides` m = m `mod` n == 0

average :: Fractional a => [a] -> a
average ns = sum ns / (fromIntegral $ length ns)

mean = average

-- Are two given values sufficently close?
isClose :: (Ord a, Fractional a) => a -> a -> Bool
isClose n m = limit > abs (n - m)
    where limit = 0.000001

-- Finding the fixed point of a function.
fixedPoint :: (Ord a, Fractional a) => (a -> a) -> a -> a
fixedPoint f guess | isClose guess next = next
                   | otherwise          = fixedPoint f next
                   where next = f guess

-- Average Dampening can help fixed-point functions converge.
averageDamp :: Fractional a => (a -> a) -> a -> a
averageDamp f = \x -> average [x,(f x)]

-- Apply a function over and over. Does this already exist?
-- Rather, apply a function n times with output stringed into the next input.
repeated :: (Ord a, Num a) => (b -> b) -> a -> b -> b
repeated f n | n < 2     = \x -> f x
             | otherwise = f . (repeated f $ n - 1)

-- Calculate any root via a fixed-point function and average dampening!
root :: (Ord a, Integral b, Fractional a) => a -> b -> a
n `root` m = fixedPoint dampedFunc 1.0
    where 
      dampedFunc  = multiDamper (\y -> n / (y ^ (m - 1)))
      multiDamper = repeated averageDamp (m - 2)

-- Calculates a log with any base. Only works with Integrals.
logBaseInt :: Integral a => a -> a -> a
logBaseInt base r 
    | not $ base `divides` r = error "Result not divisible by base!"
    | otherwise              = logBase' r 1
    where 
      logBase' curr acc = if curr == base then acc else logBase' newCurr next
          where 
            newCurr = curr `div` base
            next    = acc + 1

-- Horner's Rule - Solve for any Polynomial
horner :: Num a => a -> [a] -> a
horner x = foldr (\curr acc -> (acc * x) + curr) 0

---------
-- PRIMES
---------
data Prime a = NonPrime | a `DividesBy` a | Prime deriving (Show, Eq, Ord) 

-- A list of all prime numbers.
primes :: Integral a => [a]
primes = 2 : filter isPrime [3,5..]

 -- TODO: Learn about prime sieves.

-- Originally written 05/10/2011
-- Abstracted on 10/20/2011
-- The general case.
isPrimeGen :: Integral a => b -> (a -> b) -> a -> b
isPrimeGen success failure n 
    | n < 2     = failure n
    | n == 2    = success
    | otherwise = isPrimeGen' success failure n divs
    where 
      divs = 2 : [3,5..k]
      k    = floor $ sqrt $ fromIntegral n

isPrimeGen' :: Integral a => b -> (a -> b) -> a -> [a] -> b
isPrimeGen' success failure n [] = success
isPrimeGen' success failure n (d:ds) 
    | d `divides` n = failure d
    | otherwise     = isPrimeGen' success failure n ds

isPrime :: Integral a => a -> Bool
isPrime n = isPrimeGen True (\x -> False) n

isPrimeV :: Integral a => a -> Prime a
isPrimeV n = isPrimeGen Prime failure n
    where failure = \x -> if x < 2 then NonPrime else n `DividesBy` x

nextPrime :: Integral a => a -> a
-- Made: May 11 2011  Mod: Nov 08 2011
nextPrime n | n < 2          = 2
            | n == 2         = 3
            | 2 `divides` n  = nextPrime (n - 1)
            | otherwise      = head $ filter isPrime [(n + 2),(n + 4)..]

primeFactors :: Integral a => a -> [a]
primeFactors n = primeFacts' n 10 primes

primeFacts' :: Integral a => a -> a -> [a] -> [a]
-- After every 10 failed passes, the primality of n is tested.
primeFacts' n lim (p:ps) | n `mod` p == 0 = p : primeFacts' (n /// p) 10 ps
                         | n == 1         = []
                         | lim == 0 && isPrime n = [n]
                         | otherwise      = primeFacts' n (lim - 1) ps

------------
-- LIST WORK
------------
-- Opposite of `isolate`.
groupAt :: (a -> Bool) -> [a] -> [[a]]
groupAt _ [] = []
groupAt p xs = foldr grouper [[last xs]] $ init xs
    where grouper = (\x acc -> if p x then [x] : acc else (x : head acc) : tail acc)

groupsOfN :: Int -> [a] -> [[a]]
groupsOfN _ [] = []
groupsOfN n xs = take n xs : groupsOfN n (drop n xs)

concatWhile :: ([a] -> [a] -> Bool) -> [[a]] -> ([a],[[a]])
concatWhile p = foldlWhile p (++) []

-- Allows user to specify a custom function by which to concat each element.
concatWhileVia :: ([a] -> [a] -> Bool) -> ([a] -> [a] -> [a]) -> [[a]] -> ([a],[[a]])
concatWhileVia p c = foldlWhile p c []

{- Abstraction! Folds a list via a function `c' as long as 
a given predicate `p' is true. When found to be false, a tuple 
is returned with the current accumulator and all the values 
that didn't get folded.
-}
foldlWhile :: (a -> b -> Bool) -> (a -> b -> a) -> a -> [b] -> (a,[b])
foldlWhile _ _ acc []         = (acc,[])
foldlWhile p c acc all@(x:xs) | p acc x   = foldlWhile p c (c acc x) xs
                              | otherwise = (acc,all)

{- Isolates elements in a list, like so.
isolate 'a' "My name is a name"
returns: ["My n","a","me is ","a"," n","a","me"]
-}
isolate :: Eq a => a -> [a] -> [[a]]
isolate i = isolateBy (\x -> x == i)

isolateBy :: (a -> Bool) -> [a] -> [[a]]
isolateBy p = groupBy (\a b -> not $ (p a || p b))

safeHead :: [a] -> Maybe a
safeHead (x:_) = Just x
safeHead []    = Nothing

body :: [a] -> (a,[a])
body (x:xs) = (x,xs)

safeBody :: [a] -> (Maybe a,[a])
safeBody (x:xs) = (Just x,xs)
safeBody []     = (Nothing,[])

-- Wraps an arg in a list.
list :: a -> [a]
list x = [x]

--------------
-- STRING WORK
--------------
stripHead :: String -> String
stripHead = dropWhile (== ' ')

stripTail :: String -> String
stripTail = reverse . stripHead . reverse

indent :: String -> Int
indent = length . takeWhile (== ' ')

---------
-- MONADS
---------
filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM f xs = do
  bools <- mapM f xs
  return . map fst . filter (\(x,b) -> b) . zip xs $ bools