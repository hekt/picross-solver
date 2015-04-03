{-# LANGUAGE BangPatterns #-}

import Data.Array (Array, listArray, elems, bounds, (!))
import Data.List (foldl', elemIndex, elemIndices, transpose, sortBy, nub)
import Data.Maybe (isNothing, isJust)
import System.Environment (getArgs)
import Debug.Trace

type Line = [Maybe Bool]
type StrictLine = [Bool]
type Hints = [Int]
type HintsArray = Array Int Hints
type HintsPair  = (HintsArray, HintsArray)

main :: IO ()
main = do
  (path:_) <- getArgs
  hints <- fmap parse $ readFile path
  let !result = solve hints
  displayWithHints hints $ result

parse :: String -> HintsPair
parse s = let s' = lines s
              (x, y) = flip splitAt s' . maybe 1 id $ elemIndex "" s'
          in (f x, f $ tail y)
    where
      f xs = let xs' = map (map read . words) xs
             in listArray (0, length xs' - 1) xs'

display :: [Line] -> IO ()
display = putStr . unlines . map displayLine

displayWithHints :: HintsPair -> [Line] -> IO ()
displayWithHints (xHints_, yHints_) lines =
    let xHints = elems xHints_
        yHints = elems yHints_

        maxLen  = maximum . map length
        show' y = if y < 10 then ' ': show y else show y

        xs   = map ((++ " ") . unwords . map show) xHints
        xLen = maxLen xs
        xs'  = map (\s -> replicate (xLen - length s) ' ' ++ s) xs
                  
        ys   = map (map show') yHints
        yLen = maxLen ys
        ys'  = map (replicate xLen ' ' ++) . map concat . transpose $
               map (\s -> replicate (yLen - length s) "  " ++ s) ys
        strs = (ys' ++) . zipWith (++) xs' $ map displayLine' lines
    in do
      putStr $ unlines strs
      putStrLn $ "Unsolved: " ++ show (nothingCount lines)

displayLine :: Line -> String
displayLine [] = []
displayLine (Just True : ls) = '█': displayLine ls
displayLine (Just False: ls) = ' ': displayLine ls
displayLine (Nothing   : ls) = '?': displayLine ls

displayLine' :: Line -> String
displayLine' = concatMap (\c -> [c, c] ) . displayLine

displayLine'' :: Line -> String
displayLine'' [] = []
displayLine'' (Just True : ls) = '█': displayLine'' ls
displayLine'' (Just False: ls) = '-': displayLine'' ls
displayLine'' (Nothing   : ls) = '?': displayLine'' ls

nothingCount :: [Line] -> Int
nothingCount = sum . map f
    where f = sum . map (\x -> if isNothing x then 1 else 0)

solve :: HintsPair -> [Line]
solve hints@(xHints, yHints) =
    let grid = initialFilling hints
        grid' = linear hints grid
    -- in grid'
    in exponential hints grid'

linear :: HintsPair -> [Line] -> [Line]
linear hints@(xHints, yHints) grid
    -- = grid'
    | isCompleted grid' = grid'
    | grid == grid'     = grid
    | otherwise         = linear hints grid'
    where xqs   = sortByHints xHints [0 .. snd (bounds xHints)]
          yqs   = sortByHints yHints [0 .. snd (bounds yHints)]
          grid' = linearOnce hints grid
          -- grid' = linearX hints grid (xqs, yqs)

linearOnce :: HintsPair -> [Line] -> [Line]
linearOnce hints@(xHints, yHints) grid =
    let xUpdated = zipWith linearSuite (elems xHints) grid
    in transpose . zipWith linearSuite (elems yHints) $ transpose xUpdated

exponential :: HintsPair -> [Line] -> [Line]
exponential hints@(xHints, yHints) grid =
    let xqs = sortByHints xHints [0 .. snd (bounds xHints)]
        yqs = sortByHints yHints [0 .. snd (bounds yHints)]
        grid' = updateXLine' hints grid (xqs, yqs)
    in grid'

isCompleted :: [Line] -> Bool
isCompleted = all (all isJust)

initialFilling :: HintsPair -> [Line]
initialFilling hints@(xHints, yHints) =
    let xLen = snd (bounds yHints) + 1
        yLen = snd (bounds xHints) + 1
        xGrid = map (fillByHints xLen) $ elems xHints
        yGrid = transpose $ map (fillByHints yLen) $ elems yHints
    in zipWith merge xGrid yGrid


fillByHints :: Int -> Hints -> Line
fillByHints len [0]   = replicate len (Just False)
fillByHints len hints = (tail $ f hints) ++ replicate m Nothing
    where m = len - hintSum hints
          f [] = []
          f (h:hs) | h > m     = replicate (m + 1) Nothing ++
                                 replicate (h - m) (Just True) ++ f hs
                   | otherwise = replicate (h + 1) Nothing ++ f hs

splitDecided :: Hints -> Line -> ((Hints, Hints, Hints), (Line, Line, Line))
splitDecided hints line =
    let ((h1, h2), (l1, l2))   = lsplitDecided hints line
        ((h3, h2'), (l3, l2')) = lsplitDecided (reverse h2) (reverse l2)
    in ((h1, reverse h2', reverse h3), (l1, reverse l2', reverse l3))

lsplitDecided :: Hints -> Line -> ((Hints, Hints), (Line, Line))
lsplitDecided hints line =
    let (hints', line') = lstripDecided hints line
        hintsPair       = splitAt (length hints - length hints') hints
        linePair        = splitAt (length line - length line') line
    in (hintsPair, linePair)

lstripDecided :: Hints -> Line -> (Hints, Line)
lstripDecided []           line = ([], line)
lstripDecided hints@(h:hs) line =
    let hl  = replicate h (Just True) ++ [Just False]
        l'  = dropWhile (== Just False) line
        l'' = drop (h+1) l'
    in if and $ zipWith (==) hl l'
       then lstripDecided hs l'' else (hints, l')

linearSuite' :: Hints -> Line -> [(Hints -> Line -> Line)] -> Line
linearSuite' hints line fs
    | all isJust line = line
    | line /= line'   = linearSuite' hints line' fs
    | otherwise       = line'
    where f l fill = let (trih, tril)   = splitDecided hints l
                         (_, h, _)    = trih
                         (l1, l2, l3) = tril
                         l2'          = bothSide h l2 fill
                     in if null l2 || all isJust l2 then l
                        else merge' hints line $ l1 ++ l2' ++ l3
          line'    = foldl' f line fs
          trace' a = trace (unlines ["suite " ++ show hints
                                    , displayLine line
                                    , displayLine a]) a

merge' :: Hints -> Line -> Line -> Line
merge' h l1 l2 =
    let line' = merge l1 l2
    in if l2 == line' then line'
       else trace (unlines [ "confricted. hints: " ++ show h
                           , displayLine'' l1
                           , displayLine'' l2
                           , "merged to", displayLine'' line']) line'

linearSuite :: Hints -> Line -> Line
linearSuite hints line = linearSuite' hints line
                         [ fillEdge
                         , fillNearEdge
                         , fillCompleted
                         , fill001
                         , fill002
                         , fill003
                         , fill004
                         , sameHints
                         , prefixOfDecided
                         , fillByHintsWrap
                         , markByMaximumHint
                         , fillByMinimumHint
                         , sweepCompletedLine
                         ]
linearSuiteMini :: Hints -> Line -> Line
linearSuiteMini hints line = linearSuite' hints line
                             [ fillEdge
                             , fillNearEdge
                             ]

bothSide :: Hints -> Line -> (Hints -> Line -> Line) -> Line
bothSide hints line f = let line' = f hints line
                        in reverse $ f (reverse hints) $ reverse line'

-- 3 ____oo   => xxx_oo
-- 3 ____oooo => oooxoooo
fill001 :: Hints -> Line -> Line
fill001 []          line = line
fill001 hints@(h:_) line
    | h + 1 /= lenn = line
    | h     == lent = tail ns ++ Just False: line'
    | h     <  lent = replicate h (Just True) ++ Just False: line'
    | otherwise     = line
    where ns    = takeWhile isNothing line
          lenn  = length ns
          line' = drop lenn line
          ts    = takeWhile (== Just True) line'
          lent  = length ts
          trace' xs  = trace (unlines [ "fill001 ", show hints
                                      , displayLine line, displayLine xs]) xs

-- 5 ___ooo  => x__ooo
-- 5 ___oooo => xx_oooo
fill002 :: Hints -> Line -> Line
fill002 []          line = line
fill002 hints@(h:_) line
    | n < 1     = line
    | h >= lenn = replicate n (Just False) ++
                  replicate (lenn - n) Nothing ++ line'
    | otherwise = line
    where ns    = takeWhile isNothing line
          lenn  = length ns
          line' = drop lenn line
          ts    = takeWhile (== Just True) line'
          lent  = length ts
          n     = lenn + lent - h
          trace' xs  = trace (unlines [ "fill002", show hints
                                      , displayLine line, displayLine xs]) xs

-- 3 __x => xxx
fill003 :: Hints -> Line -> Line
fill003 []          line    = line
fill003 hints@(h:_) line
    | null fs               = line
    | head fs /= Just False = line
    | lenn < 1              = line
    | lenn < h              = replicate lenn (Just False) ++ fs
    | otherwise             = line
    where ns   = takeWhile isNothing line
          lenn = length ns
          fs   = drop lenn line
          trace' xs = trace (unlines [ "fill003", show hints
                                     , displayLine line, displayLine xs]) xs

fill004 :: Hints -> Line -> Line
fill004 hints@(h1:h2:_) line
    | isNothing mi            = line
    | h1 + h2 + 1 > length xs = linearSuite [h1] xs ++ line'
    | otherwise               = line
    where xs = takeWhile (/= Just False) line
          mi = elemIndex (Just True) xs
          line' = drop (length xs) line
          -- suites = [fillEdge]
          -- miniSuite h l = reverse $ fillEdge [h1] $ reverse l
          trace' l = trace (unlines [ "fill004", show hints
                                     , displayLine xs
                                     , displayLine line, displayLine l]) l
fill004 _         line = line

fillByMinimumHint :: Hints -> Line -> Line
fillByMinimumHint []    line = line
fillByMinimumHint hints line = merge line . tail $ f (Just False: line')
    where
      minHint = minimum hints
      line'    = merge line $ fillNearEdge [minHint] line
      f (Just False: Just True: xs) =
          let len    = (1 + ) . length $ takeWhile (== Just True) xs
              hints' = filter (> len) hints
              minHint' = minimum hints'
          in if null hints' then Just False: Just True: f xs
             else  Just False: replicate minHint (Just True) ++
                   f (drop (minHint-1) xs)
      f []     = []
      f (x:xs) = x: f xs
      trace' l = if l == line then l
                 else trace (unlines [ "minHint " ++ show hints
                                     , displayLine line, displayLine l]) l
                         
markByMaximumHint :: Hints -> Line -> Line
markByMaximumHint []    line = line
markByMaximumHint hints line = tail $ f (filledGroups line) Nothing
    where
      maxHint = maximum hints
      f []                 temp = [temp]
      f ([Nothing]   : ls) temp = temp: f ls Nothing
      f ([Just False]: ls) temp = temp: f ls (Just False)
      f (l           : []) temp =
          if length l /= maxHint then temp: l
          else Just False: l
      f (l           : ls) temp =
          if length l /= maxHint then temp: (tail l) ++ f ls (Just True)
          else Just False: l ++ f (tail ls) (Just False)
      trace' l = if l == line then l
                 else trace (unlines [ "maximumHint " ++ show hints
                                     , displayLine line, displayLine l]) l

fillByHintsWrap :: Hints -> Line -> Line
fillByHintsWrap []    line = line
fillByHintsWrap hints line = merge line $
                             (tail $ f hints) ++ replicate m Nothing
    where len = length line
          m = len - hintSum hints
          trace' l = if l /= line
                     then trace (unlines [ "fillByHints " ++ show hints
                                         , displayLine line
                                         , displayLine l]) l
                     else l
          f [] = []
          f (h:hs) | h > m     = replicate (m + 1) Nothing ++
                                 replicate (h - m) (Just True) ++ f hs
                   | otherwise = replicate (h + 1) Nothing ++ f hs

sameHints :: Hints -> Line -> Line
sameHints hints@(h1:h2:_) line
    | h1 /= h2            = line
    | lenNs < h1          = line
    | lenNs > h1 + h2     = line
    | otherwise           = l1 ++ l: f (tail hints) l2
    where lenNs = length $ takeWhile (/= Just False) line
          (l1, l: l2) = splitAt lenNs line
          f hs = fillNearEdge hs . fillEdge hs
          trace' xs = if line == xs then xs
                      else trace (unlines [ "sameHints " ++ show hints
                                          , displayLine line
                                          , displayLine xs]) xs
sameHints _ line = line

prefixOfDecided :: Hints -> Line -> Line
prefixOfDecided []          line = line
prefixOfDecided hints@(h:_) line
    | lenTs == h   = line
    | isNothing mi = line
    | null xs      = line
    | not decided  = line
    | not (null smalls) && lenTs > h = (++ ys) . linearSuite smalls $ xs
    | not (null larges) && lenTs < h = (++ ys) . linearSuite larges $ xs
    | otherwise  = line
    where mi = elemIndex (Just True) line
          i  = maybe 0 (+ (-1)) mi
          (xs, ys) = splitAt i line
          ys' = dropWhile (/= Just True) ys
          lenTs = length $ takeWhile (== Just True) ys'
          afterTs = dropWhile (== Just True) $ dropWhile (/= Just True) ys
          decided | head ys      /= Just False = False
                  | null afterTs               = True
                  | head afterTs /= Just False = False
                  | otherwise                  = True
          smalls = takeWhile (< lenTs) hints
          larges = takeWhile (> lenTs) hints
          trace' l = if line == l then l
                        else trace (unlines [ "prefixOfDecided " ++ show hints
                                            , displayLine line
                                            , displayLine l]) l
                                 
fillCompleted :: Hints -> Line -> Line
fillCompleted [h] line =
    let l = length $ elemIndices (Just True) line
        f (Just True) = Just True
        f _           = Just False
        trace' l = trace (unlines [ "fillCompleted " ++ show h
                                  , displayLine line, displayLine l]) l
    in if l == h then map f line else line
fillCompleted _   line = line

sweepCompletedLine :: Hints -> Line -> Line
sweepCompletedLine []    line = replicate (length line) (Just False)
sweepCompletedLine hints line
    | all isJust line          = line
    | line2hints line /= hints = line
    | otherwise                = n2f line
    where n2f = map (\x -> if isNothing x then Just False else x)
          trace' l = trace (unlines [ "sweep: ", show hints
                                    , displayLine line, displayLine l]) l

line2hints :: Line -> Hints
line2hints line = filter (/= 0) $ f 0 line
    where f n [] = [n]
          f n (Just True: xs) = f (n+1) xs
          f n (_        : xs) = n: f 0 xs

fillEdge :: Hints -> Line -> Line
fillEdge [] line = line
fillEdge hints@(h:_) line@(Just True: xs)
    | h == length line = replicate h (Just True)
    | otherwise        = replicate h (Just True) ++ Just False: drop h xs
    where trace' l = flip trace l $ unlines [ "fillEdge " ++ show hints
                                            , displayLine line, displayLine l]
fillEdge _     l               = l

fillNearEdge :: Hints -> Line -> Line
fillNearEdge []          xs = xs
fillNearEdge hints@(h:_) xs =
    let f i = take i xs ++ replicate (h-i) (Just True) ++ drop h xs
        trace' ys = if xs /= ys
                    then trace (unlines [ "fillNearEdge ", show hints
                                        , displayLine xs, displayLine ys]) ys
               else ys
    in case elemIndex (Just True) xs of
         (Just i) -> if i < h then f i else xs
         _        -> xs
                     
updateLine :: HintsArray -> [Line] -> Int -> ([Line], [Int], Bool)
updateLine hints grid q = let (ls1, l: ls2) = splitAt q grid
                              (l', skipped) = update (hints ! q) l
                          in (ls1 ++ l': ls2, updatedIndices l l', skipped)

updateXLine :: HintsPair -> [Line] -> ([Int], [Int]) -> [Line]
updateXLine hints@(xHints, yHints) grid ((q:qs), yqs)
    -- | not $ null yqs_ = grid'
    | not $ null yqs' = updateYLine hints grid' (qs', yqs')
    | not $ null qs   = updateXLine hints grid' (qs', yqs')
    | otherwise       = grid'
    where (grid', yqs_, skipped) = updateLine xHints grid q
          yqs' = yqs_ ++ yqs
          qs'  = if skipped then qs ++ [q] else qs

updateXLine' :: HintsPair -> [Line] -> ([Int], [Int]) -> [Line]
updateXLine' hints@(xHints, yHints) grid (q:qs, yqs)
    | not $ null yqs' = updateYLine' hints grid' (xqs', yqs')
    | not $ null qs   = updateXLine' hints grid' (xqs', yqs')
    | otherwise       = grid'
    where (grid_, updated, skipped) = updateLine xHints grid q
          grid'        = if null updated then grid_
                         else linear hints grid_
          (xqs_, yqs_) = unzip $ updatedPoints grid grid'
          xqs'         = if skipped then nub xqs_ ++ qs ++ [q]
                         else nub xqs_ ++ qs
          yqs'         = nub yqs_ ++ yqs

updateYLine :: HintsPair -> [Line] -> ([Int], [Int]) -> [Line]
updateYLine hints@(xHints, yHints) grid (xqs, (q:qs))
    -- | not $ null xqs_ = grid'
    | not $ null xqs' = updateXLine hints grid' (xqs', qs')
    | not $ null qs   = updateYLine hints grid' (xqs', qs')
    | otherwise       = grid'
    where (grid_, xqs_, skipped) = updateLine yHints (transpose grid) q
          grid' = transpose grid_
          xqs'  = xqs_ ++ xqs
          qs'   = if skipped then qs ++ [q] else qs

updateYLine' :: HintsPair -> [Line] -> ([Int], [Int]) -> [Line]
updateYLine' hints@(xHints, yHints) grid (xqs, q:qs)
    | not $ null xqs' = updateXLine' hints grid' (xqs', yqs')
    | not $ null yqs' = updateYLine' hints grid' (xqs', yqs')
    | otherwise       = grid'
    where (grid_, updated, skipped) = updateLine yHints (transpose grid) q
          grid'        = if null updated then transpose $ grid_
                         else linear hints $ transpose grid_
          (xqs_, yqs_) = unzip $ updatedPoints grid grid'
          xqs'         = nub xqs_ ++ xqs
          yqs'         = if skipped then nub yqs_ ++ qs ++ [q]
                         else nub yqs_ ++ qs

update :: Hints -> Line -> (Line, Bool)
update hints line
    | all isNothing line = (line, False)
    | all isJust line    = (line, False)
    | null h             = ( l1 ++ replicate (length l2) (Just False) ++ l3
                           , False)
    | l2 /= l2'          = (l1 ++ l2' ++ l3, True)
    | otherwise          = (l1 ++ (decide l2 $ patterns h l2) ++ l3, False)
    where (trih, tril) = splitDecided hints line
          (_,  h,  _)  = trih
          (l1, l2, l3) = tril
          l2'          = linearSuite h l2

updatedIndices :: Line -> Line -> [Int]
updatedIndices l k = f 0 l k
    where
      f n []     _      = []
      f n (x:xs) (y:ys) = if x /= y then n: f (n+1) xs ys else f (n+1) xs ys

decide :: Line -> [StrictLine] -> Line
decide l [] = l
decide l ks = merge l $ gather ks

merge :: Line -> Line -> Line
merge xs ys = zipWith f xs ys
    where f Nothing y = y
          f x       _ = x

gather :: [StrictLine] -> Line
gather []     = repeat Nothing
gather (k:ks) = let k' = map Just k
                in foldl' g k' ks
    where f (Just x, y) = if x == y then Just x else Nothing
          f _           = Nothing
          g xs ys = map f $ zip xs ys

patterns :: Hints -> Line -> [StrictLine]
patterns hints line =
    let margin = length line - hintSum hints
        margin' = maybe margin (min margin) $ elemIndex (Just True) line
    in f [ (hints, margin - n, line') | n <- [0..margin']
         , let line' = replicate n False, isValidWithLine line line']
    where
      check xs = isValidWithLine line xs && isValidWithHints hints xs
      f :: [(Hints, Int, StrictLine)] -> [StrictLine]
      f [] = []
      -- f (([],  m, l): qs) = if check l then l: f qs else f qs
      f ((hs,  0, l): qs) = let l' = l ++ fillAll hs
                            in if check l' then l': f qs else f qs
      f (([h], m, l): qs) = let l' = l ++ fill h m
                            in if check l' then l': f qs else f qs
      f (((h:hs), m, l): qs) =
          f $ (++qs) [ (hs, m-n+1, l') | n <- [1..m+1]
                     , let l' = l ++ fill h n, isValidWithLine line l' ]

fill :: Int -> Int -> StrictLine
fill x y = replicate x True ++ replicate y False

fillAll :: [Int] -> StrictLine
fillAll []     = []
fillAll [x]    = replicate x True
fillAll (x:xs) = replicate x True ++ [False] ++ fillAll xs

isValidWithLine :: Line -> StrictLine -> Bool
isValidWithLine xs ys = and $ zipWith f xs ys
    where f (Just x) y = x == y
          f _        _ = True

isValidWithHints :: Hints -> StrictLine -> Bool
isValidWithHints h l = h == (filter (/= 0) $ f 0 l)
    where f n []         = [n]
          f n (True: xs) = f (n+1) xs
          f n (_:    xs) = n: f 0 xs

sortByHints :: HintsArray -> [Int] -> [Int]
sortByHints hints lines = reverse $ sortBy f lines
    where f x y = hintSum (hints ! x) `compare` hintSum (hints ! y)

hintSum :: [Int] -> Int
hintSum ns = sum ns + length ns - 1

updatedPoints :: Eq a => [[a]] -> [[a]] -> [(Int, Int)]
updatedPoints l k = g $ zip3 l k [0..]
    where
      f [] = []
      f ((x, y, i): zs) | x == y    = f zs
                        | otherwise = i: f zs
      g [] = []
      g ((xs, ys, i): zs) = let xys' = zip (repeat i) . f $ zip3 xs ys [0..]
                            in xys' ++ g zs

filledGroups :: Line -> [Line]
filledGroups line = f line 0
    where f []              0 = []
          f []              y = replicate y (Just True): []
          f (Just True: xs) y = f xs (y+1)
          f (x:xs)          0 = [x]: f xs 0
          f (x:xs)          y = replicate y (Just True): [x]: f xs 0
