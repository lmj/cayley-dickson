-- Copyright (c) 2015 James M. Lawrence
--
-- Permission is hereby granted, free of charge, to any person obtaining
-- a copy of this software and associated documentation files (the
-- "Software"), to deal in the Software without restriction, including
-- without limitation the rights to use, copy, modify, merge, publish,
-- distribute, sublicense, and/or sell copies of the Software, and to
-- permit persons to whom the Software is furnished to do so, subject to
-- the following conditions:
--
-- The above copyright notice and this permission notice shall be included
-- in all copies or substantial portions of the Software.
--
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
-- MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
-- IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
-- CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
-- TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
-- SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
--
-----------------------------------------------------------------------------
-- |
-- Module      :  Math.CayleyDickson
-- Copyright   :  (c) James M. Lawrence
-- License     :  MIT
--
-- Maintainer  :  James M. Lawrence <llmjjmll@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- Cayley-Dickson constructions (complex numbers, quaternions,
-- octonions, sedenions, etc.) over general scalars without limit to
-- the number of dimensions.
--
-- An element of this structure is composed of an m-dimensional
-- /scalar part/ and an m*(2^n - 1)-dimensional /pure part/ (unrelated
-- to Haskell's uses of "pure"). An element whose scalar part is zero
-- is called a /pure/. Construction with real scalars yields the
-- Cayley-Dickson algebras, in which case the scalar part is also
-- called the /real part/. Other structures may be obtained by
-- considering general scalars, for instance the quaternions over
-- complex scalars.
-----------------------------------------------------------------------------

module Math.CayleyDickson (
    -- * Types
    Nion, Complex, Quaternion, Octonion, Sedenion,

    -- * Construction
    nion, fromScalar, complex, quaternion, octonion, sedenion,

    -- * Operations
    dot, cross, sqnorm, norm, polar,
    -- ** Operations with scalars
    --
    -- | The mnemonic is that the period (".") is on the side of the
    -- scalar.
    (**.),
    (.+), (+.), (.-), (-.), (.*), (*.), (/.),

    -- * Accessors
    coord, coords, setCoord, scalarPart, purePart,

    -- * Constants
    basisElement,

    -- * Classes
    Conjugable(..),

    -- ** Tags
    Tag(tagVal),
    Tag0,  Tag1,  Tag2,  Tag3,  Tag4,  Tag5,  Tag6,  Tag7,  Tag8,  Tag9,
    Tag10, Tag11, Tag12, Tag13, Tag14, Tag15, Tag16, Tag17, Tag18, Tag19,
    Tag20, Tag21, Tag22, Tag23, Tag24, Tag25, Tag26, Tag27, Tag28, Tag29,
    Tag30,

  ) where

----------------------------------------------------------
-- import

import Data.List (genericSplitAt, genericTake, genericReplicate, genericLength)
import Data.Bits (Bits, testBit)
import Data.Proxy (Proxy(Proxy))
import qualified Data.Int as Z
import qualified Data.Ratio as Q
import qualified Data.Complex as C
import qualified Data.Fixed as F
import qualified Data.Word as W

----------------------------------------------------------
-- infix

infix 6 :@

infix 6 .+
infix 6 +.
infix 6 .-
infix 6 -.

infix 7 .*
infix 7 *.
infix 7 /.

infixr 8 **.

----------------------------------------------------------
-- Nion

-- | General Cayley-Dickson construction producing \"N-ions\". The
-- first parameter is a 'Tag' instance that determines the dimension,
-- which is 2 raised to 'tagVal'. The second parameter is the scalar
-- type.
data Nion n a = Scalar a | Nion n a :@ Nion n a

----------------------------------------------------------
-- basic operations

-- | Equivalent to @'coord' x 0@.
scalarPart :: Nion n a -> a
scalarPart (Scalar x) = x
scalarPart (x :@ _) = scalarPart x

-- | Equivalent to @'setCoord' x 0 0@.
purePart :: Num a => Nion n a -> Nion n a
purePart (Scalar _) = Scalar 0
purePart (x :@ y) = purePart x :@ y

-- | Dot product. For real scalars, @(1 \`dot\`)@ is equivalent to
-- @'scalarPart'@.
dot :: Conjugable a => Nion n a -> Nion n a -> a
-- (y * conj x + x * conj y) / 2
Scalar x `dot` Scalar y = scalarPart' $ y * conj x
x@(Scalar _) `dot` (y1 :@ _) = x `dot` y1
(x1 :@ _) `dot` y@(Scalar _) = x1 `dot` y
(x1 :@ x2) `dot` (y1 :@ y2) = (x1 `dot` y1) + (x2 `dot` y2)

-- | Cross product. The cross product of two pures yields a pure that
-- is orthogonal to both operands. For real scalars, @(1 \`cross\`)@
-- is equivalent to @'purePart'@.
cross :: Conjugable a => Nion n a -> Nion n a -> Nion n a
-- (y * conj x - x * conj y) / 2
x `cross` y = y * conj x -. x `dot` y

-- | Squared norm: the dot product of an element with itself.
sqnorm :: Conjugable a => Nion n a -> a
sqnorm x = x `dot` x

-- | Square root of @sqnorm@.
norm :: (Conjugable a, Floating a) => Nion n a -> a
norm = sqrt . sqnorm

-- | Promote a scalar, returning an element whose scalar part is the
-- argument and whose pure part is zero. The element behaves as if it
-- were padded with zeros, but no actual padding is done.
fromScalar :: a -> Nion n a
fromScalar = Scalar

----------------------------------------------------------
-- operations with scalars

leftScalarOp :: (Nion n a -> Nion n a -> Nion n a) -> a -> Nion n a -> Nion n a
leftScalarOp f x y = f (Scalar x) y

rightScalarOp :: (Nion n a -> Nion n a -> Nion n a) -> Nion n a -> a -> Nion n a
rightScalarOp f x y = f x (Scalar y)

-- | Equivalent to @'fromScalar' x + y@.
(.+) :: Conjugable a => a -> Nion n a -> Nion n a
(.+) = leftScalarOp (+)

-- | Equivalent to @'fromScalar' x - y@.
(.-) :: Conjugable a => a -> Nion n a -> Nion n a
(.-) = leftScalarOp (-)

-- | Equivalent to @'fromScalar' x * y@.
(.*) :: Conjugable a => a -> Nion n a -> Nion n a
(.*) = leftScalarOp (*)

-- | Equivalent to @x + 'fromScalar' y@.
(+.) :: Conjugable a => Nion n a -> a -> Nion n a
(+.) = rightScalarOp (+)

-- | Equivalent to @x - 'fromScalar' y@.
(-.) :: Conjugable a => Nion n a -> a -> Nion n a
(-.) = rightScalarOp (-)

-- | Equivalent to @x * 'fromScalar' y@.
(*.) :: Conjugable a => Nion n a -> a -> Nion n a
(*.) = rightScalarOp (*)

-- | Equivalent to @x / 'fromScalar' y@.
(/.) :: (Conjugable a, Fractional a) => Nion n a -> a -> Nion n a
(/.) = rightScalarOp (/)

-- | Raise to a scalar power.
(**.) :: (Tag n, Conjugable a, RealFloat a) => Nion n a -> a -> Nion n a
Scalar x **. y = Scalar $ x ** y
x **. y = exp (y .* log x)

----------------------------------------------------------
-- polar form and complex function application

realPolar :: RealFloat a => Nion n a -> a -> (a, a, Nion n a)
realPolar sqrtMinus1 r
  | r >= 0 = (r, 0, sqrtMinus1)
  | otherwise = (-r, pi, sqrtMinus1)

polarUsing :: (Conjugable a, RealFloat a) =>
              Nion n a -> Nion n a -> (a, a, Nion n a)
polarUsing sqrtMinus1 (Scalar r) = realPolar sqrtMinus1 r
polarUsing sqrtMinus1 x
  | sqnormp == 0 = realPolar sqrtMinus1 r
  | otherwise = (normx, acos (r / normx), u)
  where
    p = purePart x
    sqnormp = sqnorm p
    u = p /. sqrt sqnormp
    r = scalarPart x
    normx = sqrt $ sqnormp + r * conj r

polar' :: (Tag n, Conjugable a, RealFloat a) =>
          Proxy n -> Nion n a -> (a, a, Nion n a)
polar' n x
  | tagVal n == 0 = error "polar: no polar form in 1 dimension"
  | otherwise = polarUsing basisElement1 x

-- | Return @(s, t, u)@ such that (approximately)
--
--     @x == s .* 'exp' (t .* u)@
--
-- where @s@ and @t@ are scalars, @s >= 0@, and @u@ is a unit pure.
--
-- If @x@ has no pure part then @u@ is arbitrarily chosen to be the
-- first pure basis element.
polar :: (Tag n, Conjugable a, RealFloat a) => Nion n a -> (a, a, Nion n a)
polar = polar' Proxy

applyUsing' :: (Tag n, Conjugable a, RealFloat a) =>
               Proxy n ->
               Nion n a -> (a -> a) -> (C.Complex a -> C.Complex a) ->
               Nion n a -> Nion n a
applyUsing' n sqrtMinus1 fr f z
  | tagVal n == 0 = Scalar $ fr $ scalarPart z
  | otherwise = x .+ u *. y
  where (s, t, u) = polarUsing sqrtMinus1 z
        -- handle special cases for a little more accuracy
        x C.:+ y | t == 0 = f $ c s 0
                 | t == pi = f $ c (-s) 0
                 | otherwise = f $ c s 0 * exp (c t 0 * c 0 1)
                 where c = (C.:+)

applyUsing :: (Tag n, Conjugable a, RealFloat a) =>
              Nion n a -> (a -> a) -> (C.Complex a -> C.Complex a) ->
              Nion n a -> Nion n a
applyUsing = applyUsing' Proxy

----------------------------------------------------------
-- constants

fill' :: Tag n => Proxy n -> a -> Nion n a
fill' n s = f $ tagVal n where
  f 0 = Scalar s
  f k = f k' :@ f k' where k' = k - 1

fill :: Tag n => a -> Nion n a
fill = fill' Proxy

paddedZero :: (Tag n, Num a) => Nion n a
paddedZero = fill 0

validIndex :: (Tag n, Num b, Ord b) => Proxy n -> b -> Bool
validIndex n i = i >= 0 && i < 2 ^ tagVal n

basisElement' :: (Tag n, Conjugable a, Bits i, Integral i) =>
                 Proxy n -> i -> Nion n a
basisElement' _ 0 = Scalar 1
basisElement' n index
  | validIndex n index = setCoord paddedZero index 1
  | otherwise = error "basisElement: out of range"

-- | The nth basis element.
basisElement :: (Tag n, Conjugable a, Bits i, Integral i) => i -> Nion n a
basisElement = basisElement' Proxy

basisElement1 :: (Tag n, Conjugable a) => Nion n a
basisElement1 = basisElement (1 :: Integer)

----------------------------------------------------------
-- util

-- Proper Functor and Foldable instances would have to translate
-- top-level scalars to their equivalent representation with padded
-- zeros. The machinations needed for this indirection are rather
-- cumbersome relative to the benefits of having the instances, whose
-- use would seem uncommon.

smap :: (a -> a) -> Nion n a -> Nion n a
smap f (Scalar s) = Scalar $ f s
smap f (x :@ y) = smap f x :@ smap f y

sfoldr :: (a -> b -> b) -> b -> Nion n a -> b
sfoldr f acc (Scalar x) = f x acc
sfoldr f acc (x :@ y) = sfoldr f (sfoldr f acc y) x

----------------------------------------------------------
-- accessors

coords' :: (Tag n, Num a) => Proxy n -> Nion n a -> [a]
coords' n (Scalar x) = x : genericReplicate k 0 where
                         k = 2 ^ tagVal n - 1 :: Integer
coords' _ x = sfoldr (:) [] x

-- | List of coordinates for this element.
coords :: (Tag n, Num a) => Nion n a -> [a]
coords = coords' Proxy

coord' :: (Tag n, Num a, Integral b, Bits b) => Proxy n -> Nion n a -> b -> a
coord' _ (Scalar x) 0 = x
coord' n elt index
  | validIndex n index = case elt of
                           Scalar _ -> 0
                           _ -> f elt $ fromInteger $ tagVal n - 1
  | otherwise = error "coord: out of range"
  where
    f (Scalar x) _ = x
    f (x :@ y) k = case testBit index k of
                     False -> f x k'
                     True  -> f y k'
                   where k' = k - 1

-- | Get the nth coordinate.
coord :: (Tag n, Num a, Integral b, Bits b) => Nion n a -> b -> a
coord = coord' Proxy

setCoord' :: (Tag n, Conjugable a, Integral b, Bits b) =>
             Proxy n -> Nion n a -> b -> a -> Nion n a
setCoord' _ (Scalar _) 0 value = Scalar value
setCoord' n elt index value
  | validIndex n index = case elt of
                           Scalar x -> setCoord (x .+ paddedZero) index value
                           _ -> f elt $ fromInteger $ tagVal n - 1
  | otherwise = error "setCoord: out of range"
  where
    f (Scalar _) _ = Scalar value
    f (x :@ y) k = case testBit index k of
                     False -> f x k' :@ y
                     True  -> x :@ f y k'
                   where k' = k - 1

-- | Set the nth coordinate, returning a new element.
setCoord :: (Tag n, Conjugable a, Integral b, Bits b) =>
            Nion n a -> b -> a -> Nion n a
setCoord = setCoord' Proxy

----------------------------------------------------------
-- construction

fromList :: Integer -> [a] -> Nion n a
fromList _ (x:[]) = Scalar x
fromList k xs = fromList k' l :@ fromList k' r where
                  k' = k `div` 2
                  (l, r) = genericSplitAt k' xs

nion' :: (Tag n, Num a) => Proxy n -> [a] -> Nion n a
nion' n elems = fromList d $ taken ++ padding where
                  d = 2 ^ tagVal n
                  taken = genericTake d elems
                  padding = genericReplicate (d - genericLength taken) 0

-- | Construct an element from a list of coordinates. If the list is
-- too small then the remaining coordinates are padded with zeros. If
-- the list is too large then the extra values are ignored.
nion :: (Tag n, Num a) => [a] -> Nion n a
nion = nion' Proxy

----------------------------------------------------------
-- instances

instance (Tag n, Show a, Num a) => Show (Nion n a) where
  show x = "nion " ++ show (coords x)

instance (Conjugable a, Eq a) => Eq (Nion n a) where
  Scalar x == Scalar y = x == y
  x@(Scalar _) == y1 :@ y2 = x == y1 && y2 == 0
  x1 :@ x2 == y@(Scalar _) = x1 == y && x2 == 0
  x1 :@ x2 == y1 :@ y2 = x1 == y1 && x2 == y2

instance Conjugable a => Num (Nion n a) where
  Scalar x + Scalar y = Scalar $ x + y
  x@(Scalar _) + (y1 :@ y2) = (x + y1) :@ y2
  (x1 :@ x2) + y@(Scalar _) = (x1 + y) :@ x2
  (x1 :@ y1) + (x2 :@ y2) = (x1 + x2) :@ (y1 + y2)

  Scalar x - Scalar y = Scalar $ x - y
  x@(Scalar _) - (y1 :@ y2) = (x - y1) :@ negate y2
  (x1 :@ x2) - y@(Scalar _) = (x1 - y) :@ x2
  (x1 :@ y1) - (x2 :@ y2) = (x1 - x2) :@ (y1 - y2)

  Scalar x * Scalar y = Scalar $ x * y
  x@(Scalar _) * (y1 :@ y2) = (x * y1) :@ (x * y2)
  (x1 :@ x2) * y@(Scalar _) = (x1 * y) :@ (x2 * y)
  (x1 :@ x2) * (y1 :@ y2) = (x1 * y1 - conj y2 * x2) :@ (y2 * x1 + x2 * conj y1)

  negate = smap negate
  fromInteger = fromScalar . fromInteger
  abs = doNotUse
  signum = doNotUse

instance (Conjugable a, Fractional a) => Fractional (Nion n a) where
  Scalar x / Scalar y = Scalar $ x / y
  x@(_ :@ _) / Scalar y = smap (/ y) x
  x / y = (x * conj y) /. sqnorm y

  recip x = conj x /. sqnorm x
  fromRational = fromScalar . fromRational

-- | The first pure basis element is arbitrarily chosen as sqrt (-1).
instance (Tag n, Conjugable a, RealFloat a) => Floating (Nion n a) where
  pi    = Scalar pi
  exp   = applyUsing basisElement1 exp exp
  log   = applyUsing basisElement1 log log
  sqrt  = applyUsing basisElement1 sqrt sqrt
  sin   = applyUsing basisElement1 sin sin
  cos   = applyUsing basisElement1 cos cos
  tan   = applyUsing basisElement1 tan tan
  asin  = applyUsing basisElement1 asin asin
  acos  = applyUsing basisElement1 acos acos
  atan  = applyUsing basisElement1 atan atan
  sinh  = applyUsing basisElement1 sinh sinh
  cosh  = applyUsing basisElement1 cosh cosh
  tanh  = applyUsing basisElement1 tanh tanh
  asinh = applyUsing basisElement1 asinh asinh
  acosh = applyUsing basisElement1 acosh acosh
  atanh = applyUsing basisElement1 atanh atanh

----------------------------------------------------------
-- convenience types

-- | Complex numbers, the 2^1-dimensional construction.
type Complex a = Nion Tag1 a

-- | Quaternions, the 2^2-dimensional construction.
type Quaternion a = Nion Tag2 a

-- | Octonions, the 2^3-dimensional construction.
type Octonion a = Nion Tag3 a

-- | Sedenions, the 2^4-dimensional construction.
type Sedenion a = Nion Tag4 a

-- | Construct a complex number.
complex :: a -> a -> Complex a
complex x y = (:@) (Scalar x) (Scalar y)

-- | Construct a quaternion.
quaternion :: a -> a -> a -> a -> Quaternion a
quaternion w x y z = (:@) ((:@) (Scalar w) (Scalar x))
                          ((:@) (Scalar y) (Scalar z))

-- | Construct an octonion.
octonion :: a -> a -> a -> a ->
            a -> a -> a -> a -> Octonion a
octonion s t u v
         w x y z = (:@) ((:@) ((:@) (Scalar s) (Scalar t))
                              ((:@) (Scalar u) (Scalar v)))
                        ((:@) ((:@) (Scalar w) (Scalar x))
                              ((:@) (Scalar y) (Scalar z)))

-- | Construct a sedenion.
sedenion :: a -> a -> a -> a ->
            a -> a -> a -> a ->
            a -> a -> a -> a ->
            a -> a -> a -> a -> Sedenion a
sedenion k l m n
         o p q r
         s t u v
         w x y z = (:@) ((:@) ((:@) ((:@) (Scalar k) (Scalar l))
                                    ((:@) (Scalar m) (Scalar n)))
                              ((:@) ((:@) (Scalar o) (Scalar p))
                                    ((:@) (Scalar q) (Scalar r))))
                        ((:@) ((:@) ((:@) (Scalar s) (Scalar t))
                                    ((:@) (Scalar u) (Scalar v)))
                              ((:@) ((:@) (Scalar w) (Scalar x))
                                    ((:@) (Scalar y) (Scalar z))))

----------------------------------------------------------
-- Conjugable

-- | The /conjugate/ of an element is obtained by negating the pure
-- part and conjugating the scalar part. The conjugate of a real
-- number is the identity ('id'), which is the default implementation.
class Num a => Conjugable a where
  -- | Conjugate.
  conj :: a -> a
  conj = id

  -- | Equivalent to @(x + conj x) / 2@.
  scalarPart' :: a -> a
  scalarPart' = id

instance Conjugable a => Conjugable (Nion n a) where
  conj (Scalar x) = Scalar $ conj x
  conj (x :@ y) = conj x :@ negate y

  scalarPart' (Scalar x) = Scalar $ scalarPart' x
  scalarPart' (x :@ _) = scalarPart' x

instance (Conjugable a, RealFloat a) => Conjugable (C.Complex a) where
  conj = C.conjugate
  scalarPart' (x C.:+ _) = scalarPart' x C.:+ 0

instance Conjugable Int
instance Conjugable Integer
instance Conjugable Float
instance Conjugable Double
instance Conjugable Z.Int8
instance Conjugable Z.Int16
instance Conjugable Z.Int32
instance Conjugable Z.Int64
instance Conjugable W.Word8
instance Conjugable W.Word16
instance Conjugable W.Word32
instance Conjugable W.Word64
instance Integral a => Conjugable (Q.Ratio a)
instance F.HasResolution a => Conjugable (F.Fixed a)

-----------------------------------------------------------------------------
-- doNotUse

rant :: String
rant = unlines $
  ["",
   "The Num class is a bit messed up, having tied (+), (-), and (*) to abs",
   "and signum. Number systems that have no appropriate definition for abs",
   "or signum must either invent their own operators for addition,",
   "subtraction, and multiplication, else break the contract with Num by",
   "raising an error such as this one when someone uses abs or signum.",
   "",
   "For some time I resisted hijacking Num, but eventually the replacement",
   "operators became too cumbersome and, coupled with the lack of numeric",
   "promotion, significantly detracted from the usability of the package.",
   "So here we are. Good luck, and stay away from abs and signum, which",
   "officially have cooties."]

doNotUse :: a -> a
doNotUse _ = error rant

----------------------------------------------------------
-- Tag

-- | Tags serve to determine a type's dimension, which is 2 raised to
-- `tagVal`. Tag instances are included for convenience only, as you
-- may create your own tag.
class Tag n where
  tagVal :: Proxy n -> Integer

data     Tag0
data     Tag1
data     Tag2
data     Tag3
data     Tag4
data     Tag5
data     Tag6
data     Tag7
data     Tag8
data     Tag9
data    Tag10
data    Tag11
data    Tag12
data    Tag13
data    Tag14
data    Tag15
data    Tag16
data    Tag17
data    Tag18
data    Tag19
data    Tag20
data    Tag21
data    Tag22
data    Tag23
data    Tag24
data    Tag25
data    Tag26
data    Tag27
data    Tag28
data    Tag29
data    Tag30

instance Tag    Tag0 where tagVal _ =    0
instance Tag    Tag1 where tagVal _ =    1
instance Tag    Tag2 where tagVal _ =    2
instance Tag    Tag3 where tagVal _ =    3
instance Tag    Tag4 where tagVal _ =    4
instance Tag    Tag5 where tagVal _ =    5
instance Tag    Tag6 where tagVal _ =    6
instance Tag    Tag7 where tagVal _ =    7
instance Tag    Tag8 where tagVal _ =    8
instance Tag    Tag9 where tagVal _ =    9
instance Tag   Tag10 where tagVal _ =   10
instance Tag   Tag11 where tagVal _ =   11
instance Tag   Tag12 where tagVal _ =   12
instance Tag   Tag13 where tagVal _ =   13
instance Tag   Tag14 where tagVal _ =   14
instance Tag   Tag15 where tagVal _ =   15
instance Tag   Tag16 where tagVal _ =   16
instance Tag   Tag17 where tagVal _ =   17
instance Tag   Tag18 where tagVal _ =   18
instance Tag   Tag19 where tagVal _ =   19
instance Tag   Tag20 where tagVal _ =   20
instance Tag   Tag21 where tagVal _ =   21
instance Tag   Tag22 where tagVal _ =   22
instance Tag   Tag23 where tagVal _ =   23
instance Tag   Tag24 where tagVal _ =   24
instance Tag   Tag25 where tagVal _ =   25
instance Tag   Tag26 where tagVal _ =   26
instance Tag   Tag27 where tagVal _ =   27
instance Tag   Tag28 where tagVal _ =   28
instance Tag   Tag29 where tagVal _ =   29
instance Tag   Tag30 where tagVal _ =   30
