import Math.CayleyDickson
import Data.Proxy (Proxy(Proxy))
import Data.Ratio (Ratio, (%))
import Control.Monad (replicateM, replicateM_, forM_, liftM)
import System.Random (Random, randomRIO)

----------------------------------------------------------
-- alternate formulas

pureDir :: (Tag n, Conjugable a, Floating a) => Nion n a -> Nion n a
pureDir x = p /. (norm p) where p = purePart x

cos' :: (Tag n, Conjugable a, RealFloat a) => Nion n a -> Nion n a
cos' x = (exp (u * x) + exp (- u * x)) / 2 where u = pureDir x

sin' :: (Tag n, Conjugable a, RealFloat a) => Nion n a -> Nion n a
sin' x = ((exp (u * x) - exp (- u * x)) * recip u) / 2 where u = pureDir x

cosh' :: (Tag n, Conjugable a, RealFloat a) => Nion n a -> Nion n a
cosh' x = (exp x + exp (- x)) / 2

sinh' :: (Tag n, Conjugable a, RealFloat a) => Nion n a -> Nion n a
sinh' x = (exp x - exp (- x)) / 2

dot' :: (Tag n, Conjugable a, Fractional a) => Nion n a -> Nion n a -> a
dot' x y = scalarPart $ (y * conj x + x * conj y) / 2

cross' :: (Tag n, Conjugable a, Fractional a) =>
          Nion n a -> Nion n a -> Nion n a
cross' x y = (y * conj x - x * conj y) / 2

qmul :: Num a => a -> a -> a -> a ->
                 a -> a -> a -> a -> (a, a, a, a)
qmul aw ax ay az bw bx by bz = (aw*bw - ax*bx - ay*by - az*bz,
                                aw*bx + ax*bw + ay*bz - az*by,
                                aw*by - ax*bz + ay*bw + az*bx,
                                aw*bz + ax*by - ay*bx + az*bw)

----------------------------------------------------------
-- test utils

epsilon :: Double
epsilon = 1e-7

assert :: Bool -> IO ()
assert True = putChar '.'
assert False = error "assertion failed"

close :: Tag n => Nion n Double -> Nion n Double -> Bool
close x y = norm (x - y) < epsilon

closeReal :: Double -> Double -> Bool
closeReal x y = abs (x - y) < epsilon

assertClose :: Tag n => Nion n Double -> Nion n Double -> IO ()
assertClose x y = assert $ close x y

assertCloseReal :: Double -> Double -> IO ()
assertCloseReal x y = assert $ closeReal x y

boundsI :: (Integer, Integer)
boundsI = (-100000, 100000)

boundsD :: (Double, Double)
boundsD = (-1, 1)

randomElt' :: (Tag n, Conjugable a, Random a) =>
              Proxy n -> (a, a) -> IO (Nion n a)
randomElt' n' bounds = liftM nion $ replicateM (2^n) (randomRIO bounds) where
                         n = tagVal n'

randomElt :: (Tag n, Conjugable a, Random a) => (a, a) -> IO (Nion n a)
randomElt = randomElt' Proxy

randomEltD :: Tag n => IO (Nion n Double)
randomEltD = randomElt boundsD

randomEltI :: Tag n => IO (Nion n Integer)
randomEltI = randomElt boundsI

randomEltI' :: (Tag n1, Tag n2) => Integer -> IO (Nion n1 (Nion n2 Integer))
randomEltI' n = liftM nion $ replicateM (fromIntegral n) randomEltI

randomEltI2 :: Tag n => IO (Complex (Nion n Integer))
randomEltI2 = randomEltI' 2

randomEltI4 :: Tag n => IO (Quaternion (Nion n Integer))
randomEltI4 = randomEltI' 4

----------------------------------------------------------
-- checks

checkFloating1' :: Tag n => Proxy n -> Nion n Double -> IO ()
checkFloating1' n' x = do
  if sqnorm (purePart x) /= 0
    then do assertClose (cos x) (cos' x)
            assertClose (sin x) (sin' x)
    else return ()
  assertClose (cosh x) (cosh' x)
  assertClose (sinh x) (sinh' x)

  if sqnorm x /= 0
    then assertCloseReal 1 (scalarPart $ x * recip x)
    else return ()

  forM_ (zip (coords x) ([0..] :: [Integer])) $ \(e, i) -> do
    assert $ e == coord x i
    assert $ 999 == coord (setCoord x i 999) i

  if n /= 0
    then do let (s, t, u) = polar x
            assertClose x $ s .* exp (t .* u)
    else return ()
  where
    n = tagVal n'

checkFloating1 :: Tag n => Nion n Double -> IO ()
checkFloating1 = checkFloating1' Proxy

checkFloating2' :: Tag n => Proxy n -> Nion n Double -> Nion n Double -> IO ()
checkFloating2' _ x y = do
  assertCloseReal (x `dot` y) (x `dot'` y)
  assertCloseReal (5 `dot` y) (5 `dot'` y)
  assertCloseReal (x `dot` 5) (x `dot'` 5)
  assertClose (x `cross` y) (x `cross'` y)
  assertClose (5 `cross` y) (5 `cross'` y)
  assertClose (x `cross` 5) (x `cross'` 5)

checkFloating2 :: Tag n => Nion n Double -> Nion n Double -> IO ()
checkFloating2 = checkFloating2' Proxy

checkFloating3 :: Tag n => Nion n Double -> IO ()
checkFloating3 x' = do
  assertCloseReal (scalarPart $ exp x) (exp $ scalarPart x)
  assertClose     (purePart $ exp x) 0
  assertCloseReal (scalarPart $ cos x) (cos $ scalarPart x)
  assertClose     (purePart $ cos x) 0
  assertCloseReal (scalarPart $ sin x) (sin $ scalarPart x)
  assertClose     (purePart $ sin x) 0
  assertCloseReal (scalarPart $ cosh x) (cosh $ scalarPart x)
  assertClose     (purePart $ cosh x) 0
  assertCloseReal (scalarPart $ sinh x) (sinh $ scalarPart x)
  assertClose     (purePart $ sinh x) 0
  where
    x = scalarPart x' .+ (x' - x')

checkFloating' :: Tag n => IO (Nion n Double) -> IO (Nion n Double) -> IO ()
checkFloating' x y = do
  x' <- x
  y' <- y
  checkFloating1 x'
  checkFloating2 x' y'
  checkFloating3 x'

checkFloating :: IO ()
checkFloating = do
  checkFloating' (randomEltD :: IO (Nion Tag0 Double))
                 (randomEltD :: IO (Nion Tag0 Double))
  checkFloating' (randomEltD :: IO (Complex Double))
                 (randomEltD :: IO (Complex Double))
  checkFloating' (randomEltD :: IO (Quaternion Double))
                 (randomEltD :: IO (Quaternion Double))
  checkFloating' (randomEltD :: IO (Sedenion Double))
                 (randomEltD :: IO (Sedenion Double))

checkScalar :: IO ()
checkScalar = do
  let x = nion [3] :: Nion Tag0 Integer
      y = nion [4] :: Nion Tag0 Integer
      z = nion [12] :: Nion Tag0 Integer
  assert $ x * y == z

checkComplex :: IO ()
checkComplex = do
  let x = complex 1 0 :: Complex Integer
      y = complex 0 1 :: Complex Integer
      z = complex 1 1 :: Complex Integer
  assert $ x + y == z
  assert $ x == basisElement (0 :: Integer)
  assert $ y == basisElement (1 :: Integer)
  assert $ (complex 1 2 :: Complex Integer) == nion [1..]

checkQuaternion :: IO ()
checkQuaternion = do
  let x = quaternion 0 1 0 0 :: Quaternion Integer
      y = quaternion 0 0 1 0 :: Quaternion Integer
      z = quaternion 0 0 0 1 :: Quaternion Integer
  assert $ x == basisElement (1 :: Integer)
  assert $ y == basisElement (2 :: Integer)
  assert $ z == basisElement (3 :: Integer)
  assert $ x `cross` y == z
  assert $ (quaternion 1 2 3 4 :: Quaternion Integer) == nion [1..]

  a <- randomEltI :: IO (Quaternion Integer)
  b <- randomEltI :: IO (Quaternion Integer)
  let (a0:a1:a2:a3:[]) = coords a
      (b0:b1:b2:b3:[]) = coords b
      (cw, cx, cy, cz) = qmul a0 a1 a2 a3 b0 b1 b2 b3
  assert $ quaternion cw cx cy cz == a * b

checkOctonion :: IO ()
checkOctonion = do
  let x = octonion 0 1 0 0 0 0 0 0 :: Octonion Integer
      y = octonion 0 0 1 0 0 0 0 0 :: Octonion Integer
      z = octonion 0 0 0 1 0 0 0 0 :: Octonion Integer
  assert $ x == basisElement (1 :: Integer)
  assert $ y == basisElement (2 :: Integer)
  assert $ z == basisElement (3 :: Integer)
  assert $ x `cross` y == z
  assert $ (octonion 1 2 3 4 5 6 7 8 :: Octonion Integer) == nion [1..]

checkSedenion :: IO ()
checkSedenion = do
  let x = sedenion 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 :: Sedenion Integer
      y = sedenion 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 :: Sedenion Integer
      z = sedenion 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 :: Sedenion Integer
      e = basisElement :: Integer -> Sedenion Integer
  assert $ x == e 1
  assert $ y == e 2
  assert $ z == e 3
  assert $ x `cross` y == z
  assert $ (e 3 + e 10) * (e 6 - e 15) == 0
  assert $ (sedenion 1 2 3 4 5 6 7 8
                     9 10 11 12 13 14 15 16 :: Sedenion Integer) == nion [1..]

checkBig :: IO ()
checkBig = do
  let x = nion [0,1,0,0] :: Nion Tag6 Integer
      y = nion [0,0,1,0] :: Nion Tag6 Integer
      z = nion [0,0,0,1] :: Nion Tag6 Integer
  assert $ x `cross` y == z

checkMixed :: IO ()
checkMixed = do
  let x = quaternion 1 2 3 4 :: Quaternion Integer
  assert $ 10 .+ x == quaternion 11 2 3 4
  assert $ x +. 10 == quaternion 11 2 3 4
  assert $ 10 .- x == nion [9, -2, -3, -4]
  assert $ x -. 10 == nion [-9, 2, 3, 4]
  assert $ 10 .* x == quaternion 10 20 30 40
  assert $ x *. 10 == quaternion 10 20 30 40

  assert $ (quaternion 1 2 3 4 :: Quaternion (Ratio Integer)) /. 2 ==
           nion [1 % 2, 1, 3 % 2, 2]

  forM_ [-2, -1, -0.5, 0, 0.5, 1, 2] $ \r -> do
    let y = fromScalar r :: Quaternion Double
        (s, t, u) = polar y
    assert $ s >= 0
    assertClose (fromScalar r) $ s .* exp (t .* u)
    assertClose (sqrt y) $ (sqrt s) .* exp ((t .* u) /. 2)

checkInverses :: IO ()
checkInverses = do
  f $ (nion [0.1] :: Nion Tag0 Double)
  f $ complex 0.1 0.2
  f $ quaternion 0.1 0.2 0.3 0.4
  f $ octonion 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8
  return ()
  where
    f :: Tag n => Nion n Double -> IO ()
    f x = do
      assertClose x $ (cos . acos) x
      assertClose x $ (acos . cos) x
      assertClose x $ (sin . asin) x
      assertClose x $ (asin . sin) x
      assertClose x $ (tan . atan) x
      assertClose x $ (atan . tan) x

checkBasic :: IO ()
checkBasic = do
  let x = quaternion 3 4 5 6 :: Quaternion Integer
  assert $ negate x == quaternion (-3) (-4) (-5) (-6)
  assert $ sqnorm x == 3^(2::Integer) + 4^(2::Integer) +
                       5^(2::Integer) + 6^(2::Integer)
  assert $ x + 99 == quaternion 102 4 5 6
  assert $ 99 + x == quaternion 102 4 5 6
  assert $ x - 1 == quaternion 2 4 5 6
  assert $ 1 - x == quaternion (-2) (-4) (-5) (-6)
  assert $ x * 2 == quaternion 6 8 10 12
  assert $ 2 * x == quaternion 6 8 10 12
  assert $ x `dot` 7 == 21
  assert $ 7 `dot` x == 21
  assert $ coord (nion [5] :: Nion Tag0 Integer) (0::Integer) == 5
  assert $ coord (nion [5] :: Nion Tag4 Integer) (0::Integer) == 5
  assert $ coord (nion [5] :: Nion Tag4 Integer) (1::Integer) == 0
  assert $ setCoord (nion [5] :: Nion Tag0 Integer)
                    (0::Integer) (9::Integer) == nion [9]
  assert $ setCoord (nion [5] :: Nion Tag4 Integer) (1::Integer) (9::Integer) ==
           nion [5, 9]
  assert $ (fromScalar 5 :: Nion Tag0 Integer) == nion [5]
  assert $ (fromScalar 5 :: Nion Tag4 Integer) == nion [5]
  assert $ nion [5] == (fromScalar 5 :: Nion Tag4 Integer)

  let y = quaternion 1 2 3 4 :: Quaternion (Ratio Integer)
  assert $ y / 2 == quaternion (1 % 2) 1 (3 % 2) 2
  assert $ recip y == quaternion (1 % 30) (-1 % 15) (-1 % 10) (-2 % 15)
  assert $ y * recip y == 1

checkPower :: IO ()
checkPower = do
  let x = quaternion 1 2 3 4 :: Quaternion Integer
  assert $ x ^. (0 :: Integer) == 1
  assert $ x ^. (1 :: Integer) == x
  assert $ x ^. (2 :: Integer) == x * x
  assert $ x ^. (3 :: Integer) == x * x * x
  assert $ x ^. (4 :: Integer) == x * x * x * x

  let y = quaternion 1 2 3 4 :: Quaternion (Ratio Integer)
  assert $ y ^^. (0 :: Integer) == 1
  assert $ y ^^. (1 :: Integer) == y
  assert $ y ^^. (2 :: Integer) == y * y
  assert $ y ^^. (3 :: Integer) == y * y * y
  assert $ y ^^. (4 :: Integer) == y * y * y * y
  assert $ y ^^. (-1 :: Integer) == recip y
  assert $ y ^^. (-2 :: Integer) == recip (y * y)

checkZeroAndOne :: (Show a, Eq a, Conjugable a) => Nion n1 (Nion n2 a) -> IO ()
checkZeroAndOne x = do
  assert $ 0 + x == x
  assert $ 1 * x == x

checkDistributive :: (Show a, Eq a, Conjugable a) =>
                     Nion n1 (Nion n2 a) -> Nion n1 (Nion n2 a) ->
                     Nion n2 a -> Nion n2 a ->
                     IO ()
checkDistributive x y r s = do
  assert $ (r + s) .* x == r .* x + s .* x
  assert $ r .* (x + y) == r .* x + r .* y

checkModule :: (Show a, Eq a, Conjugable a) =>
               Nion n1 (Nion n2 a) -> Nion n1 (Nion n2 a) ->
               Nion n2 a -> Nion n2 a -> IO ()
checkModule x y r s = do
  checkDistributive x y r s
  checkZeroAndOne x
  assert $ (r * s) .* x == r .* (s .* x)

checkIsomorphism :: (Conjugable a, Show a, Eq a) =>
                    ((Nion n1 (Nion n2 a)) -> Nion n3 a) ->
                    (Nion n1 (Nion n2 a)) -> (Nion n1 (Nion n2 a)) ->
                    IO ()
checkIsomorphism f x y = do
  assert $ f 0 == 0
  assert $ f 1 == 1
  assert $ f (conj x) == conj (f x)
  assert $ f (negate x) == negate (f x)
  assert $ f (x + y) == f x + f y
  assert $ f (x - y) == f x - f y
  assert $ f (x * y) == f x * f y
  assert $ scalarPart (sqnorm x) == sqnorm (f x)

phi :: (Tag n1, Tag n2, Tag n3, Conjugable a) =>
       (Nion n1 (Nion n2 a)) -> Nion n3 a
phi = nion . concatMap coords . coords

checkProperties1 :: IO ()
checkProperties1 = do
  let f = phi :: Complex (Complex Integer) -> Quaternion Integer
  r <- randomEltI :: IO (Complex Integer)
  s <- randomEltI :: IO (Complex Integer)
  x <- randomEltI2 :: IO (Complex (Complex Integer))
  y <- randomEltI2 :: IO (Complex (Complex Integer))
  checkIsomorphism f x y
  checkModule x y r s

checkProperties2 :: IO ()
checkProperties2 = do
  let f = phi :: Complex (Quaternion Integer) -> Octonion Integer
  r <- randomEltI :: IO (Quaternion Integer)
  s <- randomEltI :: IO (Quaternion Integer)
  x <- randomEltI2 :: IO (Complex (Quaternion Integer))
  y <- randomEltI2 :: IO (Complex (Quaternion Integer))
  checkIsomorphism f x y
  checkModule x y r s

checkProperties3 :: IO ()
checkProperties3 = do
  let f = phi :: Complex (Octonion Integer) -> Sedenion Integer
  r <- randomEltI :: IO (Octonion Integer)
  s <- randomEltI :: IO (Octonion Integer)
  x <- randomEltI2 :: IO (Complex (Octonion Integer))
  y <- randomEltI2 :: IO (Complex (Octonion Integer))
  checkIsomorphism f x y
  checkDistributive x y r s
  checkZeroAndOne x

checkProperties4 :: IO ()
checkProperties4 = do
  let f = phi :: Quaternion (Complex Integer) -> Octonion Integer
  r <- randomEltI :: IO (Complex Integer)
  s <- randomEltI :: IO (Complex Integer)
  x <- randomEltI4 :: IO (Quaternion (Complex Integer))
  y <- randomEltI4 :: IO (Quaternion (Complex Integer))
  checkIsomorphism f x y
  checkModule x y r s

main :: IO ()
main = do
  checkBasic
  checkScalar
  checkComplex
  checkQuaternion
  checkOctonion
  checkSedenion
  checkBig
  checkPower
  checkInverses
  checkMixed
  replicateM_ 20 $ do
    checkFloating
    checkProperties1
    checkProperties2
    checkProperties3
    checkProperties4
  putStrLn "\nAll tests passed."
