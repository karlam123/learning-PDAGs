--{-# LANGUAGE Strict #-}
{-# LANGUAGE BangPatterns #-}
import Data.Char
--import Data.Matrix.Unboxed
import Numeric.SpecFunctions
import qualified Data.List as L
import Math.Combinat.Numbers
import qualified Data.IntMap.Strict as M
import Control.Monad.Trans.State.Strict
import Control.Parallel.Strategies
import qualified Data.Sequence as S
import Data.Foldable

type Matrix a = S.Seq (S.Seq a)

-- Read a file of ints separated by ',' and store in an [Int].
readCol :: FilePath -> IO [Int]
readCol fileP = do
  str <- readFile fileP
  let result = map digitToInt $ filter p str
  return $ map fi result
  where p x = x /= ',' && x /= '\n'
        fi :: Int -> Int
        fi = fromIntegral

-- Store multiple files in a matrix.
createX :: IO (Matrix Int)
createX = do
  let cors = mapM readCol files
  let mat = fmap L.transpose cors
  let tmp = fmap S.fromList mat
  tmp2 <- tmp
  return $ fmap S.fromList tmp2

  where files = ["col1", "col2", "col3", "col4", "col5", "col6"]

-- All possible parent configurations.
createPar :: Int -> S.Seq (S.Seq Int)
createPar !n = S.replicateM n (S.fromList [0,1])

(!) :: S.Seq a -> Int -> a
(!) = S.index

-- bijection from NxN to N
cantor :: Int -> Int -> Int
cantor !n0 !n1 = (n*(n+1) `quot` 2) + n1
  where !n = n0 + n1

invCantor :: Int -> (Int, Int)
invCantor !n = (n0, n1)
  where
        !n2 = fromIntegral n
        !tmp1 = (8*n2+1)**0.5-1
        !tmp2 =  tmp1/2
        !w = floor $ tmp2
        !t = (w*w+w) `quot` 2
        !n1 = n-t
        !n0 = w-n1

-- posterior
post :: S.Seq (S.Seq Int) -> Int -> Double -> Double -> Double
post !n !parLen !a0 !a1 = s1 - log (fd (parLen * fromIntegral (st2 parLen kv)))
  where !kv = S.length n
        lb = logBeta
        fd :: Int -> Double
        fd = fromIntegral
        tmp !c = lb (fd (n ! c ! 0)+a0) (fd (n ! c ! 1)+a1) - lb a0 a1
        !s1 = foldr' (\c acc -> tmp c + acc) 0 [0..kv-1]
        st2 = stirling2nd


toRow :: S.Seq Int -> S.Seq Int -> S.Seq Int
toRow !y !ps = foldr (\p acc -> h p `sumVec` acc) (S.fromList [0,0]) ps
  where h p' = fromTuple (invCantor (y ! (p'-1)))
        fromTuple :: (Int, Int) -> S.Seq Int
        fromTuple (x1, y1) = S.fromList $ [x1,y1]
        sumVec :: S.Seq Int -> S.Seq Int -> S.Seq Int
        sumVec !xs !ys = S.fromList $ [xs ! 0 + ys ! 0, xs ! 1 + ys ! 1]

createn :: S.Seq (S.Seq Int) -> S.Seq Int -> S.Seq (S.Seq Int)
createn !sv !y = fmap (toRow y) sv



(!#) :: S.Seq a -> S.Seq Int -> S.Seq a
(!xs) !# (!sns) = case S.length sns of
                0 -> S.empty
                1 -> S.singleton (xs ! ((S.take 1 sns) ! 0-1))
                _ -> S.singleton (xs ! ((S.take 1 sns) ! 0-1)) S.>< xs !# (S.drop 1 sns)

--(!xs) !# (S.singleton n) = S.singleton $ xs S.! (fromIntegral n-1)
--(!xs) !# (S.fromList [n:ns]) = S.singleton (xs S.! (fromIntegral n-1)) S.><  xs !# ns

-- Add two sequences of the same length
add :: Num a => S.Seq a -> S.Seq a -> S.Seq a
add xs ys = S.foldrWithIndex (\i y acc -> S.adjust (+y) i acc) xs ys

addMat :: Num a => S.Seq (S.Seq a) -> S.Seq (S.Seq a) -> S.Seq (S.Seq a)
addMat xmat ymat = S.foldrWithIndex (\i y acc -> S.adjust (add y) i acc) xmat ymat

-- Correct

suffStat :: Int -> S.Seq Int -> S.Seq (S.Seq Int) -> S.Seq (S.Seq Int) -> S.Seq Int
suffStat !v !par !pars !xdata = if n0 == 0 then f2 else f1
  where !n0 = S.length par
        !n = 2^n0
        !ns = S.replicate n (S.fromList [0,0])
        !ns0 = S.fromList [0,0] :: S.Seq Int

        -- !tmp2 = foldr (\nr acc -> elementwise (+) (test nr) acc) (zero n 2) ayy
        g !x !nsacc = foldr' (\i acc -> if xp == (pars ! (i-1)) then h (i-1) xv acc else acc) nsacc [1..n]
          where
            !xv = x ! (v-1)
            !xp = x !# par
        h !i !0 !nscomp = S.adjust (add (S.fromList [1,0])) i nscomp
        h !i !1 !nscomp = S.adjust (add (S.fromList [0,1])) i nscomp
        !tmp = foldr' (\x acc -> g x acc) ns xdata

--        tmp3 = [g2 xv | nrow <- [1..1841], let x = getRow nrow xdata, let xv = x S.! (fi v-1)]
        !tmp4 = foldr' (\x acc -> g2 x acc) ns0 xdata
        g2 !x !nsacc = h2 xv nsacc
          where !xv = x ! (v-1)
        h2 0 !nscomp = nscomp `add` S.fromList [1, 0]
        h2 1 !nscomp = nscomp `add` S.fromList [0, 1]
        -- !f2 = S.fromFunction n (\i -> cantorRow (getRow (i+1) tmp4))
        -- !f1 = S.fromFunction n (\i -> cantorRow (getRow (i+1) tmp2))
        f1 = fmap cantorRow tmp
        f2 = S.singleton $ cantorRow tmp4
        cantorRow :: S.Seq Int -> Int
        cantorRow !vi = cantor (vi ! 0) (vi ! 1)

sortNordering :: Int -> Int -> Ordering
sortNordering !y1 !y2
  | n1/(n0+n1) < n3/(n2+n3) = LT
  | n1/(n0+n1) == n3/(n2+n3) = EQ
  | otherwise = GT
  where (!n0, !n1) = t $ invCantor y1
        (!n2, !n3) = t $ invCantor y2
        fi :: Int -> Double
        fi = fromIntegral
        t (x, y) = (fi x, fi y)

sort_y :: S.Seq Int -> S.Seq Int
sort_y !y = S.unstableSortBy sortNordering y

type AlgoState = (M.IntMap (S.Seq (S.Seq Int)), S.Seq (S.Seq Int), Double)
type StateMap = State AlgoState ()

algo :: Int -> S.Seq Int -> S.Seq (S.Seq Int) -> ((), AlgoState)
algo !v !par !xData = runState (algo' v par xData) (maps, S.empty, 1)
  where !maps = M.fromList [(0, S.empty)]

algo' :: Int -> S.Seq Int -> S.Seq (S.Seq Int) -> StateMap
algo' !v !par !xData = test3 nConfi
  where !numParents = S.length par
        !pars = createPar numParents
        !y = sort_y $ suffStat v par pars xData
        !nConfi = S.length pars
        createSq :: Int -> Int -> S.Seq (S.Seq Int)
        createSq !k !n = if k < n then S.singleton (S.fromFunction ((n-k)) ((k+1)+)) else S.empty -- [[k+1...N]]
        createSv !maps !n !k !l = (maps M.! (l-1)) S.>< createSq (l-1) k S.>< createSq k n
        comparePart !pMax !sMax !maps n k l = if p >= pMax || pMax == 1 then (p, (maps M.! (l-1)) S.>< createSq (l-1) k) else (pMax, sMax)
          where !sv = createSv maps n k l
                !n0 = createn sv y
                !p = post n0 nConfi 1 1
        test :: Int -> Int -> Int -> StateMap
        test !n !k !l = do
          (!maps, !smax, !pmax) <- get
          let (!newpmax, !newsmax) = comparePart pmax smax maps n k l
          put (maps, newsmax, newpmax)
        test2 :: Int -> Int -> StateMap
        test2 !n !k = do
          (!maps, !smax, !pmax) <- get
          put (maps, smax, 1)
          mapM_ (test n k) [1..k]
          (!maps, !smax, !pmax) <- get
          put (M.insert k smax maps, smax, pmax)

        test3 :: Int -> StateMap
        test3 !n = do
          mapM_ (test2 n) [1..n]

updateMat :: Int -> Int -> a -> Matrix a -> Matrix a
updateMat i j x mat = S.update i (S.update j x row) mat
  where row = mat ! i

toMatrix :: S.Seq Int -> Matrix Int
toMatrix !b = fst $ foldl' (\(am1, ac1) j -> tmp j (am1, ac1)) (zero, 0) [0..4]
  where tmp :: Int -> (Matrix Int, Int) -> (Matrix Int, Int)
        tmp !j (!mat, !c) = foldl' (\(am, ac) i -> (updateMat i j (b ! ac) am, ac+1)) (mat, c) [(j+1)..5]
        zero = S.replicate 6 (S.fromList [0,0,0,0,0,0])

--toParents :: Matrix Int -> S.Seq (S.Seq Int)
--toParents !mat = L.foldl' (\acc1 j -> tmp j acc1) vs [0..4]
--  where tmp :: Int -> S.Seq [Int] -> S.Seq [Int]
--        tmp !j !acc = L.foldl' (\acc2 i -> if mat ! (fromIntegral i+1, fromIntegral j+1) == 1 then acc2 S.// [(i, (acc2 S.! i)  ++[j+1])] else acc2) acc [(fromIntegral j+1)..5]
--        !vs = S.fromList [[],[],[],[],[],[]]

addParent :: S.Seq (S.Seq a) -> Int -> a -> S.Seq (S.Seq a)
addParent ps i j = S.adjust (S.|>j) i ps

type ParentList = (S.Seq Int, S.Seq (S.Seq Int))
toParents' :: S.Seq Int -> Matrix Int -> ParentList
toParents' !ind !mat = (ind, foldl' (\acc1 j -> tmp j acc1) vs (S.fromFunction 5 id)) -- [0..4]
  where tmp :: Int -> S.Seq (S.Seq Int) -> S.Seq (S.Seq Int)
        tmp !j !acc = foldl' (\acc2 i -> if mat ! (i) ! (j)  == 1 then addParent acc2 i (ind ! j) else acc2) acc (S.fromFunction (5- j) (\x -> (x+j+1))) -- [j+1..5]
        !vs = S.fromList [S.empty, S.empty, S.empty, S.empty, S.empty, S.empty] :: S.Seq (S.Seq Int)


toParents2 :: S.Seq Int -> S.Seq Int -> ParentList
toParents2 !b !ind = toParents' ind (toMatrix b)

optimalDagState :: Matrix Int -> S.Seq Int -> S.Seq Int-> State ((Double, ParentList)) ()
optimalDagState !xData !ind !b = do
  (!popt, !gopt) <- get
  let !c = mapG' xData indvs vs
  if c > popt || popt == 0 then put (c, (indvs, vs)) else put (popt, gopt)
  where (!indvs, !vs) = toParents2 b ind

optimalDag :: Matrix Int -> S.Seq (S.Seq Int) -> S.Seq Int -> (Double, ParentList)
optimalDag !xData !bs !ind = execState (mapM_ (optimalDagState xData ind) bs) (0, (S.empty, S.empty))

-- map of a graph G
mapG :: Matrix Int -> S.Seq (S.Seq Int) -> Double
mapG !xData !vs = S.foldrWithIndex (\v par acc-> acc+helper (algo (v+1) par xData)) 0 vs
  where helper :: ((), AlgoState) -> Double
        helper ((), (_, _, !p)) = p

mapG' :: Matrix Int -> S.Seq Int -> S.Seq (S.Seq Int) -> Double
mapG' !xData !ind !vs = S.foldrWithIndex (\v par acc-> acc+helper (algo ((ind ! v)) par xData)) 0 vs
  where helper :: ((), AlgoState) -> Double
        helper ((), (_, _, !p)) = p

-- All permutations of [1..n]
permutations :: Int -> [S.Seq Int]
permutations !n = S.fromList <$> L.permutations [1..n]

parOptimalDag :: Strategy (Double, ParentList)
parOptimalDag (!p, !vs) = do
  (!p', !vs') <- rdeepseq (p, vs)
  return (p', vs')

-- Evaluate all optimal dag for all permutations of [1..6]
allOptimalDags :: Matrix Int -> [(Double, ParentList)]
allOptimalDags !xData = parMap parOptimalDag (optimalDag xData bs) (permutations 6)
  where !bs = createPar 15

allMaximumGraph :: [(Double, ParentList)] -> (Double, ParentList)
allMaximumGraph !xs = foldr (\(p, vs) (pacc, vsacc) -> if p > pacc || pacc == 0 then (p, vs) else (pacc, vsacc)) (0, (S.empty, S.empty)) xs

printParents :: (Double, ParentList) -> IO ()
printParents (p, (par, pars)) = do
  putStrLn $ "Parent order: " ++ show par
  putStrLn $ "Parents of each vertex: " ++ show pars
  putStrLn $ "MAP of graph: " ++ show p

main :: IO ()
main = do
  !xData <- createX
  --putStrLn (show (mapG xData vs))
  let !res = allOptimalDags xData
  let !maxGraph = allMaximumGraph res
  putStrLn $ show $ (res, maxGraph)
  printParents maxGraph
  --where vs = S.fromList (map S.fromList [[2], [], [2], [5], [2], [4]])
