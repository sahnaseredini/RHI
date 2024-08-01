module RHMonad where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (flip)
import Data.Char (ord, toUpper, chr)
import Control.Monad 
import Numeric

-- Examples to run: 
-- tidyUp (RH [((Map.fromList[(L "x", 1)],startEnv ), 1)] >>= eval Skip flip >>= eval Skip flip)
-- tidyUp (RH [((Map.fromList[(L "x", 1)],startEnv ), 1)] >>= eval (Assign (L "y") (Num 2)) flip)
-- tidyUp (RH [((Map.fromList[(L "x", 1),(L "y" , 2)],startEnv ), 1)] >>= eval (Assign (L "y") (Aexp Plus (Num 2) (Var (L "y")))) flip)

-- Examples to run: 
-- tidyUp (eval (Seq Skip Skip) flip (Map.fromList[(L "x", 1)], startEnv))
-- tidyUp (eval (Assign (L "y") (Num 2)) flip (Map.fromList[(L "x", 1)], startEnv))
-- tidyUp (eval (Assign (L "y") (Aexp Plus (Num 2) (Var (L "y")))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv))
-- tidyUp (eval (Seq (Assign (L "y") (Aexp Plus (Num 2) (Var (L "y")))) (Assign (L "x") (Aexp Plus (Num 2) (Var (L "x"))))) flip (Map.fromList[(L "x", 1), (L "y", 2)], startEnv))

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
type Prob = [(MemSystem, Pr)]
-- END OF Required definitions -- 

-- Monad definitions -- 
newtype RH m = RH {getRH :: [(m, Pr)]} deriving (Show, Eq, Ord)

instance Functor RH where
    fmap f (RH a) = RH [(f x, p) | (x, p) <- a]

instance Applicative RH where
    pure = return
    rf <*> rx = rf >>= \f -> rx >>= \x -> return (f x)

instance Monad RH where
    return x = RH [(x, 1)]
    (RH a) >>= f = RH (([(n, (pr1 * pr2)) | 
      (m, pr1) <- a , 
      (n, pr2) <- getRH (f m)]))
-- END OF Monad definitions -- 

-- Evaluation definitions -- 
eval :: Com -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> RH MemSystem
eval Skip flipFunction mem = return mem
eval (Assign x e) flipFunction mem = evalA e flipFunction mem >>= \(n, m) -> RH (flipFunction x ((Map.insert x n (fst m)), checkClocks $ snd m))
eval (Seq c0 c1) flipFunction mem = eval c0 flipFunction mem >>= (eval c1 flipFunction)
eval (If b c0 c1) flipFunction mem = evalB b flipFunction mem >>= \(t, m) -> if t then eval c0 flipFunction m else eval c1 flipFunction m
eval (While b c) flipFunction mem = evalB b flipFunction mem >>= \(t, m) -> if t then eval (Seq (c) (While b c)) flipFunction m else return m

evalA :: ArithE -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> RH (Int, MemSystem)
evalA (Num n) flipFunction mem = return (n, mem)
evalA (Var l) flipFunction mem = RH (map (\(m,pr) -> ((fromJust (Map.lookup l (fst m)), m), pr)) (flipFunction l (fst mem, checkClocks $ snd mem)))
evalA (Aexp opt a1 a2) flipFunction mem = case a1 of 
  Num n1 -> case a2 of 
    Num n2 -> case opt of 
      Plus -> return (n1 + n2, mem)
      Minus -> return (n1 - n2, mem)
      Mul -> return (n1 * n2, mem)
    _ -> evalA a2 flipFunction mem >>= \(n, m) -> evalA (Aexp opt a1 (Num n)) flipFunction m
  _ -> evalA a1 flipFunction mem >>= \(n, m) -> evalA (Aexp opt (Num n) a2) flipFunction m

evalB :: BoolE -> (Loc -> MemSystem -> [(MemSystem, Pr)]) -> MemSystem -> RH (Bool, MemSystem)
evalB (Truth t) flipFunction mem = return (t, mem)
evalB (Bexp opt b1 b2) flipFunction mem = case b1 of 
  Truth t1 -> case b2 of 
    Truth t2 -> case opt of 
      And -> return (t1 && t2, mem)
      Or -> return (t1 || t2, mem)
    _ -> evalB b2 flipFunction mem >>= \(t, m) -> evalB (Bexp opt b1 (Truth t)) flipFunction m
  _ -> evalB b1 flipFunction mem >>= \(t, m) -> evalB (Bexp opt (Truth t) b2) flipFunction m
evalB (BexpA opt a1 a2) flipFunction mem = case a1 of 
  Num n1 -> case a2 of 
    Num n2 -> case opt of 
      Equ -> return (n1 == n2, mem)
      LoE -> return (n1 <= n2, mem)
    _ -> evalA a2 flipFunction mem >>= \(n, m) -> evalB (BexpA opt a1 (Num n)) flipFunction m
  _ -> evalA a1 flipFunction mem >>= \(n, m) -> evalB (BexpA opt (Num n) a2) flipFunction m
evalB (BexpN opt b) flipFunction mem = case b of 
  Truth t -> return (not t, mem)
  _ -> evalB b flipFunction mem >>= \(b1, m) -> return (not b1, m)
-- END OF Evaluation definitions -- 

-- Flip function --
flip :: Loc -> MemSystem -> Prob
flip loc mem = listWith (+) (flipMem loc mem)

flipMem :: Loc -> MemSystem -> Prob
flipMem loc (mem, env) = if null mem then [((mem, env), 1.0)] else listWith (+) (foldr (++) [] (map (\h -> (map (\(m,pr) -> (((Map.union (fst $ fst h) (fst m)), snd m), pr * (snd h))) fm)) fl))
  where
    fm = flipMem loc ((tailMap mem), env1)
    env1 = snd $ fst (fl!!0)
    fl = flipLoc loc ((headMap mem), env)

flipLoc :: Loc -> ((Loc, Int), Env) -> Prob
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
listUnionWith f l1 l2 = Map.toList (Map.unionWith f (Map.fromListWith f l1) (Map.fromListWith f l2))

tidyUp (RH l) = RH (Map.toList (Map.fromListWith (+) l))

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
flipProbability = 0.01

startEnv :: Env
startEnv = (0, Map.empty)
-- END OF Initialisations --
