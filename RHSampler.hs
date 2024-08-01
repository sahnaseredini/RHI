module RHSampler where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (flip)
import Data.Char (ord, toUpper, chr)
import Control.Monad 
import Numeric
import System.Random

-- Examples to run are in the main function 

-- Syntax --
data ArithE = Num Int | Var Loc | Aexp Aop ArithE ArithE deriving (Show, Eq, Ord)
data BoolE = Truth Bool | Bexp Bop BoolE BoolE | BexpA BopA ArithE ArithE | BexpN BopN BoolE deriving (Show, Eq, Ord)
data Com = Skip | Assign Loc ArithE | Seq Com Com | If BoolE Com Com | While BoolE Com deriving (Show, Eq)
data Loc = L String deriving (Show, Eq, Ord)
data Aop = Plus | Minus | Mul deriving (Show, Eq, Ord)
data Bop = And | Or deriving (Show, Eq, Ord)
data BopN = Neg deriving (Show, Eq, Ord)
data BopA = Equ | LoE deriving (Show, Eq, Ord)
-- END OF Syntax --

-- Required definitions -- 
type Mem = Map.Map Loc Int
type CountRowVars = Map.Map Loc Int
type Env = (Int, CountRowVars)
type MemSystem = (Mem, Env)
type Pr = Double 
type Prob m = [(m, Pr)]
type ProbA = [((Int, MemSystem), Pr)]
type ProbB = [((Bool, MemSystem), Pr)]
-- END OF Required definitions -- 

-- Run definitions -- 
-- main :: IO ()
main = do
  let n = 10000
  g <- newStdGen
  let rn = take (n*10) (randoms g :: [Double])
  -- print rn
  print $ tidyUp (eval (Assign (L "y") (Aexp Plus (Num 1) (Var (L "x")))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv) n n rn) 
  print $ tidyUp (eval (Assign (L "y") (Aexp Plus (Num 2) (Var (L "y")))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv) n n rn)
  print $ tidyUp (eval (Seq (Assign (L "x") (Num 0)) (Seq (Assign (L "y") (Num 0)) (While (BexpA Equ (Var (L "x"))(Num 0)) (Assign (L "y") (Num 1))))) flip (Map.fromList[(L "x", 0), (L "y", 0)], startEnv) n n rn)
-- END OF Run definitions -- 

-- Evaluation definitions -- 
eval :: Com -> (Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])) -> MemSystem -> Int -> Int -> [Pr] -> Prob MemSystem
eval c flipFunction mem n step rn = case step of
  0 -> []
  _ -> tidyUp([(es,(1/fromIntegral n))] ++ (eval c flipFunction mem n (step - 1) newrn))
  where
    (es, newrn) = evalS c flipFunction mem rn

evalS :: Com -> (Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])) -> MemSystem -> [Pr] -> (MemSystem, [Pr])
evalS Skip flipFunction mem rn = (mem, rn)
evalS (Assign x e) flipFunction mem rn = writeMS x (fst a) flipFunction (snd a) newrn
  where 
    (a, newrn) = evalA e flipFunction mem rn
evalS (Seq c0 c1) flipFunction mem rn = evalS c1 flipFunction p newrn
  where 
    (p, newrn) = evalS c0 flipFunction mem rn
evalS (If e c0 c1) flipFunction mem rn = if (fst b) then evalS c0 flipFunction (snd b) newrn else evalS c1 flipFunction (snd b) newrn
  where 
    (b, newrn) = evalB e flipFunction mem rn
evalS (While e c) flipFunction mem rn = if (fst b) then evalS (Seq c (While e c)) flipFunction (snd b) newrn else evalS Skip flipFunction (snd b) newrn
  where 
    (b, newrn) = evalB e flipFunction mem rn 

evalA :: ArithE -> (Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])) -> MemSystem -> [Pr] -> ((Int, MemSystem), [Pr])
evalA (Num n) flipFunction mem rn = ((n, mem), rn)
evalA (Var l) flipFunction mem rn = readMS l flipFunction mem rn
evalA (Aexp op a1 a2) flipFunction mem rn = case a1 of 
  Num n1 -> case a2 of 
    Num n2 -> case op of 
      Plus -> (((n1 + n2), mem), rn)
      Minus -> (((n1 - n2), mem), rn)
      Mul -> (((n1 * n2), mem), rn)
    _ -> evalA (Aexp op a1 (Num (fst a))) flipFunction (snd a) newrn
      where 
      (a, newrn) = evalA a2 flipFunction mem rn
  _ -> evalA (Aexp op (Num (fst a)) a2) flipFunction (snd a) newrn
    where 
    (a, newrn) = evalA a1 flipFunction mem rn

evalB :: BoolE -> (Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])) -> MemSystem -> [Pr] -> ((Bool, MemSystem), [Pr])
evalB (Truth t) flipFunction mem rn = ((t, mem), rn)
evalB (Bexp op b1 b2) flipFunction mem rn = case b1 of 
  Truth t1 -> case b2 of 
    Truth t2 -> case op of 
      And -> ((t1 && t2, mem), rn)
      Or -> ((t1 || t2, mem), rn)
    _ -> evalB (Bexp op b1 (Truth (fst b))) flipFunction (snd b) newrn
      where 
        (b, newrn) = evalB b2 flipFunction mem rn 
  _ -> evalB (Bexp op (Truth (fst b)) b2) flipFunction (snd b) newrn 
    where 
      (b, newrn) = evalB b1 flipFunction mem rn 
evalB (BexpA op a1 a2) flipFunction mem rn = case a1 of 
  Num n1 -> case a2 of 
    Num n2 -> case op of 
      Equ -> ((n1 == n2, mem), rn)
      LoE -> ((n1 <= n2, mem), rn)
    _ -> evalB (BexpA op a1 (Num (fst a))) flipFunction (snd a) newrn 
      where 
        (a, newrn) = evalA a2 flipFunction mem rn
  _ -> evalB (BexpA op (Num (fst a)) a2) flipFunction (snd a) newrn
    where 
      (a, newrn) = evalA a1 flipFunction mem rn
evalB (BexpN op b) flipFunction mem rn = case b of 
  Truth t -> ((not t, mem), rn)
  _ -> evalB (BexpN op (Truth (fst b1))) flipFunction (snd b1) newrn
    where 
      (b1, newrn) = evalB b flipFunction mem rn
-- END OF Evaluation definitions -- 

-- Flip function --
flip :: Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])
flip loc mem rn = flipMem loc mem rn

flipMem :: Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])
flipMem loc (mem, env) rn = if null mem then ((mem, env), rn) else ((\m1 -> \m2 -> ((Map.union (fst m1) (fst m2)), snd m2)) fl fm, newrn) 
  where 
    (fm, newrn) = flipMem loc ((tailMap mem), (snd fl)) (tail rn)
    fl = flipLoc loc ((headMap mem), env) (head rn)

flipLoc :: Loc -> ((Loc, Int), Env) -> Pr -> MemSystem
flipLoc loc ((l,v), (clocks, countRowVars)) rn =  
    if distance loc l <= blastRadius && loc /= l && counter >= rhThreshold && rn <= flipProbability
      then (Map.fromList[(l, flipCell v)], env)
    else (Map.fromList[(l,v)], env)
  where 
    countRowVarsU1 = (\v1 -> tickCounter l v1 countRowVars) (if distance loc l <= blastRadius && loc /= l then 1 else 0)
    countRowVarsUpdated = resetCounter loc 0 countRowVarsU1
    env = (clocks, countRowVarsUpdated)
    counter = fromJust (Map.lookup l countRowVarsUpdated)

flipCell :: Int -> Int
flipCell n = if mod n 2 == 0 then n + flipValue else n - flipValue
-- END OF Flip function --

-- Auxiliary functions --
readMS :: Loc -> (Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])) -> MemSystem -> [Pr] -> ((Int, MemSystem), [Pr])
readMS loc flipFunction mem rn = ((v, ck), newrn)
  where
    ck = (\(m, env) -> (m, checkClocks env)) fl 
    (fl, newrn) = flipFunction loc mem rn
    v = fromJust (Map.lookup loc (fst mem))

writeMS :: Loc -> Int -> (Loc -> MemSystem -> [Pr] -> (MemSystem, [Pr])) -> MemSystem -> [Pr] -> (MemSystem, [Pr])
writeMS loc v flipFunction mem rn = (ck, newrn)
  where
    ck = (\(m, env) -> (m, checkClocks env)) fl 
    (fl, newrn) = flipFunction loc mem' rn
    mem' = insertToMem (loc, v) startEnv mem

insertToMem :: (Loc, Int) -> Env -> MemSystem -> MemSystem
insertToMem (loc, v) env1 (mem, env) = ((Map.insert loc v mem), ((max (fst env1) (fst env)), Map.union (snd env1) (snd env)))

tidyUp l = listWith (+) l

listWith f list = Map.toList (Map.fromListWith f list)

tailMap m = Map.fromList $ tail $ Map.toList m
headMap m = head $ Map.toList m

distance :: Loc -> Loc -> Int
distance (L x) (L y) = abs (strToInt x - strToInt y)

strToInt :: String -> Int
strToInt [] = 0
strToInt [x] = (ord x) - 65
strToInt (x:xs) = (((length xs) * 26 * ((ord x) - 65 + 1))) + strToInt xs

checkClocks :: Env -> Env
checkClocks (clocks, counter) =
  if clocks >= (refreshInterval - 1) 
    then (0, resetCounters counter)
    else (clocks + 1, counter)

tickCounter :: Loc -> Int -> CountRowVars -> CountRowVars
tickCounter loc v counter = Map.insertWith (+) loc v counter

resetCounter :: Loc -> Int -> CountRowVars -> CountRowVars
resetCounter loc v counter = Map.insert loc v counter

resetCounters :: CountRowVars -> CountRowVars
resetCounters counter = Map.map (\a -> 0) counter
-- END OF Auxiliary functions --

-- Initialisations --
rhThreshold = 1
refreshInterval = 10
blastRadius = 1
flipValue = 1
flipProbability = 0.9

startEnv :: Env
startEnv = (0, Map.empty)
-- END OF Initialisations --
