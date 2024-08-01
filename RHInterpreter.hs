module RHInterpreter where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (flip)
import Data.Char (ord, toUpper, chr)
import Control.Monad 
import Numeric

-- Examples to run: 
-- tidyUp (eval (Seq Skip Skip) flip (Map.fromList[(L "x", 1)], startEnv))
-- tidyUp (eval (Assign (L "y") (Num 2)) flip (Map.fromList[(L "x", 1)], startEnv))
-- tidyUp (eval (Assign (L "y") (Aexp Plus (Num 2) (Var (L "y")))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv))
-- tidyUp (eval (Seq (Assign (L "y") (Aexp Plus (Num 2) (Var (L "y")))) (Assign (L "x") (Aexp Plus (Num 2) (Var (L "x"))))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv))
-- tidyUp (eval (Assign (L "y") (Aexp Plus (Var (L "y")) (Var (L "y")))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv)) 

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

-- Evaluation definitions -- 
eval :: Com -> (Loc -> MemSystem -> Prob MemSystem) -> MemSystem -> Prob MemSystem
eval Skip flipFunction mem = dirac mem
eval (Assign x e) flipFunction mem = listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (writeMS x (fst $ fst h) flipFunction (snd $ fst h)))) a))
  where 
    a = evalA e flipFunction mem
eval (Seq c0 c1) flipFunction mem = listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (eval c1 flipFunction (fst h)))) p))
  where 
    p = eval c0 flipFunction mem
eval (If e c0 c1) flipFunction mem = listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (if (fst $ fst h) then eval c0 flipFunction (snd $ fst h) else eval c1 flipFunction (snd $ fst h)))) b))
  where 
    b = evalB e flipFunction mem
eval (While e c) flipFunction mem = listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (if (fst $ fst h) then eval (Seq c (While e c)) flipFunction (snd $ fst h) else eval Skip flipFunction (snd $ fst h)))) b))
  where 
    b = evalB e flipFunction mem

evalA :: ArithE -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> Prob (Int, MemSystem)
evalA (Num n) flipFunction mem = dirac (n, mem)
evalA (Var l) flipFunction mem = readMS l flipFunction mem
evalA (Aexp op a1 a2) flipFunction mem = case a1 of 
  Num n1 -> case a2 of 
    Num n2 -> case op of 
      Plus -> dirac ((n1 + n2), mem)
      Minus -> dirac ((n1 - n2), mem)
      Mul -> dirac ((n1 * n2), mem)
    _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalA (Aexp op a1 (Num (fst $ fst h))) flipFunction (snd $ fst h)))) a))
      where 
      a = evalA a2 flipFunction mem
  _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalA (Aexp op (Num (fst $ fst h)) a2) flipFunction (snd $ fst h)))) a))
    where 
    a = evalA a1 flipFunction mem

evalB :: BoolE -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> Prob (Bool, MemSystem)
evalB (Truth t) flipFunction mem = dirac (t, mem)
evalB (Bexp op b1 b2) flipFunction mem = case b1 of 
  Truth t1 -> case b2 of 
    Truth t2 -> case op of 
      And -> dirac (t1 && t2, mem)
      Or -> dirac (t1 || t2, mem)
    _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalB (Bexp op b1 (Truth (fst $ fst h))) flipFunction (snd $ fst h)))) b))
      where 
        b = evalB b2 flipFunction mem
  _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalB (Bexp op (Truth (fst $ fst h)) b2) flipFunction (snd $ fst h)))) b))
    where 
      b = evalB b1 flipFunction mem
evalB (BexpA op a1 a2) flipFunction mem = case a1 of 
  Num n1 -> case a2 of 
    Num n2 -> case op of 
      Equ -> dirac (n1 == n2, mem)
      LoE -> dirac (n1 <= n2, mem)
    _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalB (BexpA op a1 (Num (fst $ fst h))) flipFunction (snd $ fst h)))) a))
      where 
        a = evalA a2 flipFunction mem
  _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalB (BexpA op (Num (fst $ fst h)) a2) flipFunction (snd $ fst h)))) a))
    where 
      a = evalA a1 flipFunction mem
evalB (BexpN op b) flipFunction mem = case b of 
  Truth t -> dirac (not t, mem)
  _ -> listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (m, pr * (snd h))) (evalB (BexpN op (Truth (fst $ fst h))) flipFunction (snd $ fst h)))) b1))
    where 
      b1 = evalB b flipFunction mem
-- END OF Evaluation definitions -- 

-- Flip function --
flip :: Loc -> MemSystem -> Prob MemSystem
flip loc mem = listWith (+) (flipMem loc mem)

flipMem :: Loc -> MemSystem -> Prob MemSystem
flipMem loc (mem, env) = if null mem then [((mem, env), 1.0)] else listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (((Map.union (fst $ fst h) (fst m)), snd m), pr * (snd h))) fm)) fl))
  where
    fm = flipMem loc ((tailMap mem), env1)
    env1 = snd $ fst (fl!!0)
    fl = flipLoc loc ((headMap mem), env)

flipLoc :: Loc -> ((Loc, Int), Env) -> Prob MemSystem
flipLoc loc ((l, v), (clocks, countRowVars)) = listUnionWith (+) [((Map.fromList[(l, v)], env), (1 - flipProbability))] (
    if distance loc l <= blastRadius && loc /= l && counter >= rhThreshold 
      then [((Map.fromList[(l, flipCell v)], env), flipProbability)] 
    else [((Map.fromList[(l, v)], env), flipProbability)]) 
  where 
    countRowVarsU1 = (\v1 -> tickCounter l v1 countRowVars) (if distance loc l <= blastRadius && loc /= l then 1 else 0)
    countRowVarsUpdated = resetCounter loc 0 countRowVarsU1
    env = (clocks, countRowVarsUpdated)
    counter = fromJust (Map.lookup l countRowVarsUpdated)

flipCell :: Int -> Int
flipCell n = if mod n 2 == 0 then n + flipValue else n - flipValue
-- END OF Flip function --

-- Auxiliary functions --
readMS :: Loc -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> Prob (Int, MemSystem)
readMS loc flipFunction mem = prob2ProbAList v ck
  where
    ck = map (\((m, env), pr) -> ((m, checkClocks env), pr)) fl 
    fl = flipFunction loc mem
    v = fromJust (Map.lookup loc (fst mem))

writeMS :: Loc -> Int -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> Prob MemSystem
writeMS loc v flipFunction mem = ck
  where
    ck = map (\((m, env), pr) -> ((m, checkClocks env), pr)) fl 
    fl = flipFunction loc mem'
    mem' = (Map.insert loc v (fst mem), snd mem)

listUnionWith f l1 l2 = Map.toList (Map.unionWith f (Map.fromListWith f l1) (Map.fromListWith f l2))

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

dirac :: m -> Prob m
dirac m = [(m, 1)]

prob2ProbAList v [] = []
prob2ProbAList v ((m, p):xs) = ((v, m), p):(prob2ProbAList v xs)
-- END OF Auxiliary functions --

-- Initialisations --
rhThreshold = 1
refreshInterval = 10
blastRadius = 1
flipValue = 1
flipProbability = 0.01

startEnv :: Env
startEnv = (0, Map.empty)
-- END OF Initialisations --
