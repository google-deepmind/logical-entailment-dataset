{-
    Copyright 2018 Google LLC

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

        https://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
-}    

module Main where

import Control.Exception.Base
import Control.Monad
import Data.Array.IO
import qualified Data.Char as Char
import qualified Data.Logic.Propositional as Prop
import qualified Data.Logic.Propositional.NormalForms as NormalForms
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Tuple as Tuple
import MiniSat
import System.Environment
import System.IO
import System.Process
import System.Random
import Text.ParserCombinators.Parsec
import Text.Parsec.Combinator

------------------------------------ Types ------------------------------------

{-
An Entailment is a struct containing: 
   two propositions A and B
   whether A entails B (written A ⊧ B)
   three statistics (used as simple heuristic estimates):
     whether length(A) >= length(B)
     whether vars(B) ⊆ vars(A)
     whether literals(B*) ⊆ literals(A*)
       where A* is negation-normal-form version of A
-}       
type Entailment = (Prop.Expr, Prop.Expr, Int, Int, Int, Int)

{-
A FourTuple is four propositions (A, B, A*, B*) such that:
  A ⊧ B
  A* ⊧ B*
  A ⊭ B*
  A* ⊭ B
-}
type FourTuple = (Prop.Expr, Prop.Expr, Prop.Expr, Prop.Expr)

------------------------------------ main -----------------------------------

{-
Usage:
  first argument: number of pairs to generate
  second argument: max number of variables in a formula
  third argument: max complexity of a formula

NB four-tuples are extracted from generated pairs.
But many pairs are unsuitable for four-tuples.
So if you want 100 entailment lines, you need 100/4 = 25 four-tuples,
  and you might need 200 pairs to produce 25 four-tuples.
  (The ratio of pairs-to-four-tuples depends on the complexity of the formulas)
-}
main :: IO ()
main = do
    args <- getArgs
    case args of
      [] -> make_four_tuples 100 20 30
      [ns] -> do
        let n = read ns :: Int
        make_four_tuples n 20 30
      [ns, vs] -> do
        let n = read ns :: Int
        let v = read vs :: Int
        make_four_tuples n v 30
      [ns, vs, ks] -> do
        let n = read ns :: Int
        let v = read vs :: Int
        let k = read ks :: Int
        make_four_tuples n v k

------------------------------------ Generation -------------------------------

gen_formula :: RandomGen r => r -> Int -> [Char]  -> (Prop.Expr, r) 
gen_formula r complexity vs = gen_f r complexity vs

gen_f :: RandomGen r => r -> Int -> [Char] -> (Prop.Expr, r)
gen_f r 0 vs = gen_atom r vs
gen_f r n vs = f r3 where
  n1 = n - 1
  (na, r2) = pick [0 .. n1] r
  nb = n1 - na
  (f, r3) = pick [gen_unary Prop.Negation n1 vs, 
                  gen_binary Prop.Conjunction na nb vs, 
                  gen_binary Prop.Disjunction na nb vs, 
                  gen_binary Prop.Conditional na nb vs] r2

gen_atom :: RandomGen r => r -> [Char] -> (Prop.Expr, r)
gen_atom r vs = (Prop.Variable (Prop.Var v), r2) where
  (v, r2) = pick vs r

gen_unary :: RandomGen r => (Prop.Expr -> Prop.Expr) -> Int -> [Char] -> r -> (Prop.Expr, r)
gen_unary f n vs r = (f p, r') where
  (p, r') = gen_f r n vs

gen_binary :: RandomGen r => (Prop.Expr -> Prop.Expr -> Prop.Expr) -> Int -> Int -> [Char] -> r -> (Prop.Expr, r)
gen_binary f na nb vs r = (f p q, r3) where
  (p, r2) = gen_f r na vs
  (q, r3) = gen_f r2 nb vs

alphabet :: [Char]
alphabet = ['a'..'z']

make_exprs :: Int -> Int -> Int -> Int -> IO (Prop.Expr, Prop.Expr)
make_exprs c1 c2 num_vars n = do
  r <- newStdGen
  let (vs, _, r2) = take_n alphabet num_vars r
  let (p1, r3) = gen_formula r2 c1 vs
  let (p2, _) = gen_formula r3 c2 vs
  return (p1, p2)

pick :: RandomGen r => [a] -> r -> (a, r)
pick [] _ = error "pick wrongly given empty list"
pick as r =
    let indices = (0, length as-1)
        (i, r') = randomR indices r
    in  (as !! i, r')

pick_freq :: RandomGen r => [(Int, a)] -> r -> (a, r)   
pick_freq [] _ = error "pick_freq wrongly given empty list"
pick_freq as r = (pick_n n as, r') where
  (n, r') = randomR (0, tot-1) r
  tot = List.foldl' (\b -> (\(a,_) -> a + b)) 0 as

pick_n :: Int -> [(Int, a)] -> a
pick_n _ [] = error "Empty list"
pick_n x ((y,a):_) | x < y = a
pick_n x ((y,_):ps) | otherwise = pick_n (x-y) ps

pick_take :: RandomGen r => [a] -> r -> (a, [a], r)
pick_take [] _ = error "pick_take wrongly given empty list"
pick_take as r = 
    let indices = (0, length as-1)
        (i, r') = randomR indices r
    in  (as !! i, take i as ++ drop (i+1) as, r')

take_n :: RandomGen r => [a] -> Int -> r -> ([a], [a], r)
take_n as n r = take_n2 as n r []

take_n2 :: RandomGen r => [a] -> Int -> r -> [a] -> ([a], [a], r)
take_n2 as n r acc | length acc == n = (acc, as, r)
take_n2 as n r acc | otherwise = take_n2 as' n r' (a:acc) where
  (a, as', r') = pick_take as r

------------------------------------ Entails ----------------------------------

entails :: Prop.Expr -> Prop.Expr -> IO Bool
entails a b = do
  let p = Prop.Conjunction a (Prop.Negation b)
  b <- sat p
  return (not b)

equiv :: Prop.Expr -> Prop.Expr -> IO Bool
equiv a b = do
  let p = Prop.Conjunction a (Prop.Negation b)
  let q = Prop.Conjunction b (Prop.Negation a)  
  b <- sat (Prop.Disjunction p q)
  return (not b)

sat :: Prop.Expr -> IO Bool  
sat p = do
  let (n, cs) = convert_to_dimacs p
  s <- make_solver cs n
  b <- solve s []
  deleteSolver s
  return b

convert_to_dimacs :: Prop.Expr -> (Int, [[Int]])
convert_to_dimacs = expr_to_dimacs . toCNF

toCNF :: Prop.Expr -> Prop.Expr  
toCNF = fixed_point NormalForms.toCNF

fixed_point :: Eq a => (a->a) -> a -> a
fixed_point f a = 
    if f a == a then a
    else fixed_point f (f a)

expr_to_dimacs :: Prop.Expr -> (Int, [[Int]])
expr_to_dimacs e = to_dimacs e (zip (extract_vars e) [1..])

to_dimacs :: Prop.Expr -> [(Char, Int)] -> (Int, [[Int]])
to_dimacs e m = (length m, to_dimacs_c e m)

to_dimacs_c :: Prop.Expr -> [(Char, Int)] -> [[Int]]
to_dimacs_c (Prop.Variable (Prop.Var c)) m = case lookup c m of
  Just i -> [[i]]
to_dimacs_c (Prop.Negation (Prop.Variable (Prop.Var c))) m = case lookup c m of
  Just i -> [[-i]]
to_dimacs_c (Prop.Conjunction p q) m = to_dimacs_c p m ++ to_dimacs_c q m
to_dimacs_c (Prop.Disjunction p q) m = [to_dimacs_d p m ++ to_dimacs_d q m]

to_dimacs_d :: Prop.Expr -> [(Char, Int)] -> [Int]
to_dimacs_d (Prop.Variable (Prop.Var c)) m = case lookup c m of
  Just i -> [i]
to_dimacs_d (Prop.Negation (Prop.Variable (Prop.Var c))) m = case lookup c m of
  Just i -> [-i]
to_dimacs_d (Prop.Disjunction p q) m = to_dimacs_d p m ++ to_dimacs_d q m

extract_vars :: Prop.Expr -> [Char]
extract_vars e = List.sort (List.nub (f e)) where
  f (Prop.Variable (Prop.Var c)) = [c]
  f (Prop.Negation p) = f p
  f (Prop.Conjunction p q ) = f p ++ f q
  f (Prop.Disjunction p q ) = f p ++ f q
  f (Prop.Conditional p q ) = f p ++ f q

make_solver:: [[Int]] -> Int -> (IO Solver)
make_solver baseClauses vars = do 
  s <- newSolver
  literals <- sequence [newLit s | i <- [1..vars]]
  sequence_ $ map ( (addClause s).(toLits)) baseClauses
  return s

toLits :: [Int] -> [Lit] 
toLits xs = map lit' xs where
  lit' x | x > 0 = minisat_mkLit $ MkVar (fromIntegral (x-1)) 
  lit' x | x < 0 = neg $ minisat_mkLit $ MkVar (fromIntegral (abs x - 1))

------------------------------------ show -------------------------------------

showF :: Prop.Expr -> String  
showF (Prop.Variable (Prop.Var c)) = [c]
showF (Prop.Negation p) = "~(" ++ showF p ++ ")"
showF (Prop.Conjunction p q) = "(" ++ showF p ++ "&" ++ showF q ++ ")"
showF (Prop.Disjunction p q) = "(" ++ showF p ++ "|" ++ showF q ++ ")"
showF (Prop.Conditional p q) = "(" ++ showF p ++ ">" ++ showF q ++ ")"

------------------------------------ check ------------------------------------

verify_dataset :: String -> IO ()
verify_dataset f = do
  ts <- parse_file f
  forM_ ts $ \(a, b, e, _, _, _) -> do
    let not_e = e == 0
    not_entails <- sat (Prop.Conjunction a (Prop.Negation b))
    putStrLn $ "Verifying " ++ show a ++ ", " ++ show b ++ ", " ++ show e
    case not_entails == not_e of
      True -> return ()
      False -> do
        putStrLn $ "Problem with " ++ show a ++ ", " ++ show b ++ ", " ++ show e
        error "Error"
  putStrLn "Ok"

------------------------------------ Parsing ----------------------------------

parse_file :: String -> IO [Entailment]
parse_file f = do
    x <- readFile f
    case (parse file f x) of
        Left e -> do
            putStrLn $ "Parse error: " ++ show e
            return []
        Right rs -> do
            return rs

file :: Parser [Entailment]
file = spaces >> parse_triples

parse_triples :: Parser [Entailment]
parse_triples = many1 parse_triple

parse_triple :: Parser Entailment
parse_triple = do
    p <- parse_formula
    lexeme ","
    q <- parse_formula
    lexeme ","
    n <- parse_int
    lexeme ","
    h1 <- parse_int
    lexeme ","
    h2 <- parse_int
    lexeme ","
    h3 <- parse_int
    return (p, q, n, h1, h2, h3)

parse_formula :: Parser Prop.Expr
parse_formula = do
  e <-  Text.ParserCombinators.Parsec.try parse_negation <|> 
        Text.ParserCombinators.Parsec.try parse_conjunction <|> 
        Text.ParserCombinators.Parsec.try parse_disjunction <|> 
        Text.ParserCombinators.Parsec.try parse_implication <|> 
        parse_atom
  return e

comma = lexeme ","
      
parse_atom :: Parser Prop.Expr
parse_atom = do
    a <- identifierSymbol
    return $ Prop.Variable (Prop.Var a)
    
identifierSymbol :: Parser Char
identifierSymbol = alphaNum <|> (char '_')

parse_negation :: Parser Prop.Expr
parse_negation = do
  lexeme "~"
  lexeme "("
  p <- parse_formula
  lexeme ")"
  return $ Prop.Negation p

parse_conjunction :: Parser Prop.Expr
parse_conjunction = do
  lexeme "("
  p <- parse_formula
  lexeme "&"
  q <- parse_formula
  lexeme ")"
  return $ Prop.Conjunction p q

parse_disjunction :: Parser Prop.Expr
parse_disjunction = do
  lexeme "("
  p <- parse_formula
  lexeme "|"
  q <- parse_formula
  lexeme ")"
  return $ Prop.Disjunction p q

parse_implication :: Parser Prop.Expr
parse_implication = do
  lexeme "("
  p <- parse_formula
  lexeme ">"
  q <- parse_formula
  lexeme ")"
  return $ Prop.Conditional p q

parse_int :: Parser Int
parse_int = do
  e <- Text.ParserCombinators.Parsec.try parse_1 <|> parse_0
  return e

parse_1 :: Parser Int
parse_1 = do
  lexeme "1"
  return 1

parse_0 :: Parser Int
parse_0 = do
  lexeme "0"
  return 0

lexeme :: String -> Parser String
lexeme s = do
    string s
    spaces
    return s

------------------------------------ de Bruijn --------------------------------

type SymbolMap = [(Prop.Var, Int)]

deBruijn :: (Prop.Expr, SymbolMap) -> (Prop.Expr, SymbolMap)
deBruijn (Prop.Negation p, m) = (Prop.Negation p', m') where (p', m') = deBruijn (p, m)
deBruijn (Prop.Conjunction p q, m) = (Prop.Conjunction p' q', m'') where 
  (p', m') = deBruijn (p, m)
  (q', m'') = deBruijn (q, m')
deBruijn (Prop.Disjunction p q, m) = (Prop.Disjunction p' q', m'') where 
  (p', m') = deBruijn (p, m)
  (q', m'') = deBruijn (q, m')
deBruijn (Prop.Conditional p q, m) = (Prop.Conditional p' q', m'') where 
  (p', m') = deBruijn (p, m)
  (q', m'') = deBruijn (q, m')
deBruijn (Prop.Variable p, m) = case lookup p m of
  Nothing -> (Prop.Variable p', m') where
    n = length m + 1
    p' = Prop.Var (Char.chr n)
    m' = (p, n) : m
  Just n -> (Prop.Variable p', m) where
    p' = Prop.Var (Char.chr n)

------------------------------------ Alpha-Equivalence ------------------------

build_set :: String -> IO (Set.Set (Prop.Expr, Prop.Expr))
build_set f = do
  ts <- parse_file f
  let fs = List.foldl' add_triple Set.empty ts
  return fs

add_triple :: Set.Set (Prop.Expr, Prop.Expr) -> Entailment -> Set.Set (Prop.Expr, Prop.Expr)
add_triple s (p,q,_,_,_,_) = Set.insert (p',q') s where
  (p', m) = deBruijn (p, [])
  (q', _) = deBruijn (q, m)

check_triple :: Set.Set (Prop.Expr, Prop.Expr) -> String -> Entailment -> IO ()
check_triple s f (a,b,n,h1,h2,h3) = do
  let (a', m) = deBruijn (a, [])
  let (b', _) = deBruijn (b, m)
  case Set.member (a',b') s of
    True -> putStrLn $ "Redundant: " ++ showF a ++ "," ++ showF b
    False -> appendFile f $ showF a ++ "," ++ showF b ++ "," ++ show n ++ "," ++ show h1 ++ "," ++ show h2 ++ "," ++ show h3 ++ "\n"

filter_alpha_equivalences :: String -> String -> String -> IO ()  
filter_alpha_equivalences training test results = do
  s <- build_set training
  ts <- parse_file test
  forM_ ts (check_triple s results)

instance Ord Prop.Expr where
  compare (Prop.Variable p) (Prop.Variable q) = compare p q
  compare (Prop.Variable _) (Prop.Negation _) = LT
  compare (Prop.Variable _) (Prop.Conjunction _ _) = LT
  compare (Prop.Variable _) (Prop.Disjunction _ _) = LT
  compare (Prop.Variable _) (Prop.Conditional _ _) = LT

  compare (Prop.Negation _) (Prop.Variable _) = GT
  compare (Prop.Negation p) (Prop.Negation q) = compare p q
  compare (Prop.Negation _) (Prop.Conjunction _ _) = LT
  compare (Prop.Negation _) (Prop.Disjunction _ _) = LT
  compare (Prop.Negation _) (Prop.Conditional _ _) = LT

  compare (Prop.Conjunction _ _) (Prop.Variable _) = GT
  compare (Prop.Conjunction _ _) (Prop.Negation _) = GT
  compare (Prop.Conjunction p q) (Prop.Conjunction p' q') = compare (p,q) (p',q')
  compare (Prop.Conjunction _ _) (Prop.Disjunction _ _) = LT
  compare (Prop.Conjunction _ _) (Prop.Conditional _ _) = LT

  compare (Prop.Disjunction _ _) (Prop.Variable _) = GT
  compare (Prop.Disjunction _ _) (Prop.Negation _) = GT
  compare (Prop.Disjunction _ _) (Prop.Conjunction _ _) = GT
  compare (Prop.Disjunction p q) (Prop.Disjunction p' q') = compare (p,q) (p',q')
  compare (Prop.Disjunction _ _) (Prop.Conditional _ _) = LT

  compare (Prop.Conditional _ _) (Prop.Variable _) = GT
  compare (Prop.Conditional _ _) (Prop.Negation _) = GT
  compare (Prop.Conditional _ _) (Prop.Conjunction _ _) = GT
  compare (Prop.Conditional _ _) (Prop.Disjunction _ _) = GT
  compare (Prop.Conditional p q) (Prop.Conditional p' q') = compare (p,q) (p',q')

------------------------------------ Simple Baselines -------------------------

subset :: (Eq a) => [a] -> [a] -> Bool
subset a b = all (`elem` b) a

prop_length :: Prop.Expr -> Int
prop_length (Prop.Variable _) = 1
prop_length (Prop.Negation p) = prop_length p + 1
prop_length (Prop.Conjunction p q) = prop_length p + prop_length q + 1
prop_length (Prop.Disjunction p q) = prop_length p + prop_length q + 1
prop_length (Prop.Conditional p q) = prop_length p + prop_length q + 1
prop_length (Prop.Biconditional p q) = prop_length p + prop_length q + 1

heuristic_1 :: Prop.Expr -> Prop.Expr -> Int
heuristic_1 a b = case prop_length a >= prop_length b of
  True -> 1
  False -> 0

heuristic_2 :: Prop.Expr -> Prop.Expr -> Int
heuristic_2 a b = case Prop.variables b `subset` Prop.variables a of
  True -> 1
  False -> 0

heuristic_3 :: Prop.Expr -> Prop.Expr -> Int
heuristic_3 a b = case ls_b `subset` ls_a of
  True -> 1
  False -> 0
  where
  ls_a = literals (fixed_point NormalForms.toNNF a)
  ls_b = literals (fixed_point NormalForms.toNNF b)

literals :: Prop.Expr -> [(Prop.Var, Bool)]
literals (Prop.Variable p) = [(p, True)]
literals (Prop.Negation (Prop.Variable p)) = [(p, False)]
literals (Prop.Conjunction p q) = List.nub $ literals p ++ literals q
literals (Prop.Disjunction p q) = List.nub $ literals p ++ literals q
literals (Prop.Conditional p q) = List.nub $ literals p ++ literals q
literals (Prop.Biconditional p q) = List.nub $ literals p ++ literals q

------------------------------------ Baselines Stats -------------------------

get_stats :: String -> IO ()
get_stats f = do
  ts <- parse_file f
  (stat1, stat2, stat3, stat4, stat5) <- foldM accumulate_stat (0, 0, 0, 0, 0) ts
  putStrLn $ "Heuristic 1: " ++ show stat1 ++ " / " ++ show (length ts)
  putStrLn $ "Heuristic 2: " ++ show stat2 ++ " / " ++ show (length ts)
  putStrLn $ "Heuristic 3: " ++ show stat3 ++ " / " ++ show (length ts)
  putStrLn $ "Proportion of tautologies: " ++ show stat4 ++ " / " ++ show (length ts)
  putStrLn $ "Proportion of satisfiable Bs: " ++ show stat5 ++ " / " ++ show (length ts)

accumulate_stat :: (Int, Int, Int, Int, Int) -> Entailment -> IO (Int, Int, Int, Int, Int)
accumulate_stat (s1, s2, s3, s4, s5) (_, b, entails, h1, h2, h3) = do
  let s1' = if h1 == entails then s1 + 1 else s1
  let s2' = if h2 == entails then s2 + 1 else s2
  let s3' = if h3 == entails then s3 + 1 else s3
  not_is_tautology_b <- sat (Prop.Negation b)
  let s4' = if not_is_tautology_b then s4 else s4 + 1
  satisfiable_b <- sat b
  let s5' = if satisfiable_b then s5 + 1 else s5
  return (s1', s2', s3', s4', s5')

------------------------------------ Bias Stats -------------------------------

bias_stats :: String -> IO ()
bias_stats f = do
  ts <- parse_file f
  print_stats ts prop_length "length"
  print_stats ts num_vars "num vars"
  print_stats2 ts num_new_vars "new vars"
  print_stats ts num_negs "num negs"
  print_stats ts num_conjs "num conjs"
  print_stats ts num_disjs "num disjs"
  print_stats ts num_imps "num imps"
  print_stats ts count_sats "num satisfying TVAs"
  print_stats ts (num_negs_at_level 0) "negs at level 0"
  print_stats ts (num_negs_at_level 1) "negs at level 1"
  print_stats ts (num_negs_at_level 2) "negs at level 2"
  print_stats ts (num_conjs_at_level 0) "conjs at level 0"
  print_stats ts (num_conjs_at_level 1) "conjs at level 1"
  print_stats ts (num_conjs_at_level 2) "conjs at level 2"
  print_stats ts (num_disjs_at_level 0) "disjs at level 0"
  print_stats ts (num_disjs_at_level 1) "disjs at level 1"
  print_stats ts (num_disjs_at_level 2) "disjs at level 2"
  
print_stats :: [Entailment] -> (Prop.Expr -> Int) -> String -> IO ()
print_stats ts f s = do
  let (dist1, dist0) = List.foldl' (accumulate_bias_a f) (Map.empty, Map.empty) ts
  let (m1, m2) = (mean dist1, mean dist0)
  putStrLn $ "Mean " ++ s ++ " for A: " ++ show m1
  putStrLn $ "Mean " ++ s ++ " for A*: " ++ show m2
  putStrLn $ "Chi-squared for " ++ s ++ " is: " ++ show (chi_squared dist1 dist0)
  let (dist1, dist0) = List.foldl' (accumulate_bias_b f) (Map.empty, Map.empty) ts
  let (m1, m2) = (mean dist1, mean dist0)
  putStrLn $ "Mean " ++ s ++ " for B: " ++ show m1
  putStrLn $ "Mean " ++ s ++ " for B*: " ++ show m2
  putStrLn $ "Chi-squared for " ++ s ++ " is: " ++ show (chi_squared dist1 dist0)

print_stats2 :: [Entailment] -> (Prop.Expr -> Prop.Expr -> Int) -> String -> IO ()
print_stats2 ts f s = do
  let (dist1, dist0) = List.foldl' (accumulate_bias2 f) (Map.empty, Map.empty) ts
  let (m1, m2) = (mean dist1, mean dist0)
  putStrLn $ "Mean " ++ s ++ " for B: " ++ show m1
  putStrLn $ "Mean " ++ s ++ " for B*: " ++ show m2
  putStrLn $ "Chi-squared for " ++ s ++ " is: " ++ show (chi_squared dist1 dist0)

chi_squared :: Map.Map Int Int -> Map.Map Int Int -> (Float, Int)
chi_squared m1 m2 = (sum (map f all_keys), length all_keys) where
  all_keys = List.sort (List.nub (Map.keys m1 ++ Map.keys m2))
  f i = case (Map.lookup i m1, Map.lookup i m2) of
    (Nothing, Nothing) -> 0.0
    (Nothing, Just s_i) -> fromIntegral s_i 
    (Just r_i, Nothing) -> fromIntegral r_i
    (Just r_i, Just s_i) -> g (fromIntegral r_i) (fromIntegral s_i)
  g x y = (x - y)**2 / (x+y)

mean :: Map.Map Int Int -> Float  
mean m = total / count where
  m_l = Map.toList m
  count = sum (map (fromIntegral . snd) m_l) :: Float
  total = sum (map (\(a,b) -> (fromIntegral (a * b))) m_l) :: Float

accumulate_bias_a :: (Prop.Expr -> Int) -> (Map.Map Int Int, Map.Map Int Int) -> Entailment -> (Map.Map Int Int, Map.Map Int Int)
accumulate_bias_a f (pos_dist, neg_dist) (a, _, 1, _, _, _) = (update_count f pos_dist a, neg_dist)
accumulate_bias_a f (pos_dist, neg_dist) (a, _, 0, _, _, _) = (pos_dist, update_count f neg_dist a)

accumulate_bias_b :: (Prop.Expr -> Int) -> (Map.Map Int Int, Map.Map Int Int) -> Entailment -> (Map.Map Int Int, Map.Map Int Int)
accumulate_bias_b f (pos_dist, neg_dist) (_, b, 1, _, _, _) = (update_count f pos_dist b, neg_dist)
accumulate_bias_b f (pos_dist, neg_dist) (_, b, 0, _, _, _) = (pos_dist, update_count f neg_dist b)

accumulate_bias2 :: (Prop.Expr -> Prop.Expr -> Int) -> (Map.Map Int Int, Map.Map Int Int) -> Entailment -> (Map.Map Int Int, Map.Map Int Int)
accumulate_bias2 f (pos_dist, neg_dist) (a, b, 1, _, _, _) = (update_count2 f pos_dist a b, neg_dist)
accumulate_bias2 f (pos_dist, neg_dist) (a, b, 0, _, _, _) = (pos_dist, update_count2 f neg_dist a b)

update_count :: (Prop.Expr -> Int) -> Map.Map Int Int -> Prop.Expr -> Map.Map Int Int
update_count f m b = case Map.lookup l m of
  Nothing -> Map.insert l 1 m
  Just n -> Map.insert l (n+1) m
  where l =  f b

update_count2 :: (Prop.Expr -> Prop.Expr -> Int) -> Map.Map Int Int -> Prop.Expr -> Prop.Expr -> Map.Map Int Int
update_count2 f m a b = case Map.lookup l m of
  Nothing -> Map.insert l 1 m
  Just n -> Map.insert l (n+1) m
  where l =  f a b

num_vars :: Prop.Expr -> Int
num_vars = length . extract_vars

num_new_vars :: Prop.Expr -> Prop.Expr -> Int
num_new_vars a b = length (extract_vars b List.\\ extract_vars a)

num_negs :: Prop.Expr -> Int
num_negs (Prop.Variable _) = 0
num_negs (Prop.Negation p) = num_negs p + 1
num_negs (Prop.Conjunction p q) = num_negs p + num_negs q
num_negs (Prop.Disjunction p q) = num_negs p + num_negs q
num_negs (Prop.Conditional p q) = num_negs p + num_negs q
num_negs (Prop.Biconditional p q) = num_negs p + num_negs q

num_conjs :: Prop.Expr -> Int
num_conjs (Prop.Variable _) = 0
num_conjs (Prop.Negation p) = num_conjs p
num_conjs (Prop.Conjunction p q) = num_conjs p + num_conjs q + 1
num_conjs (Prop.Disjunction p q) = num_conjs p + num_conjs q
num_conjs (Prop.Conditional p q) = num_conjs p + num_conjs q
num_conjs (Prop.Biconditional p q) = num_conjs p + num_conjs q

num_disjs :: Prop.Expr -> Int
num_disjs (Prop.Variable _) = 0
num_disjs (Prop.Negation p) = num_disjs p
num_disjs (Prop.Conjunction p q) = num_disjs p + num_disjs q
num_disjs (Prop.Disjunction p q) = num_disjs p + num_disjs q + 1
num_disjs (Prop.Conditional p q) = num_disjs p + num_disjs q
num_disjs (Prop.Biconditional p q) = num_disjs p + num_disjs q

num_imps :: Prop.Expr -> Int
num_imps (Prop.Variable _) = 0
num_imps (Prop.Negation p) = num_imps p
num_imps (Prop.Conjunction p q) = num_imps p + num_imps q
num_imps (Prop.Disjunction p q) = num_imps p + num_imps q
num_imps (Prop.Conditional p q) = num_imps p + num_imps q + 1
num_imps (Prop.Biconditional p q) = num_imps p + num_imps q

num_negs_at_level :: Int -> Prop.Expr -> Int
num_negs_at_level level p = num_negs_at_level2 p level 0

num_negs_at_level2 :: Prop.Expr -> Int -> Int -> Int
num_negs_at_level2 (Prop.Variable _) _ _ = 0
num_negs_at_level2 (Prop.Negation _) level current | level == current = 1
num_negs_at_level2 (Prop.Negation _) level current | level < current = 0
num_negs_at_level2 (Prop.Negation p) level current | level > current = num_negs_at_level2 p level (current+1)
num_negs_at_level2 (Prop.Conjunction _ _) level current | level <= current = 0
num_negs_at_level2 (Prop.Conjunction p q) level current | level > current = 
  num_negs_at_level2 p level (current+1) + num_negs_at_level2 q level (current+1)
num_negs_at_level2 (Prop.Disjunction _ _) level current | level <= current = 0
num_negs_at_level2 (Prop.Disjunction p q) level current | level > current = 
  num_negs_at_level2 p level (current+1) + num_negs_at_level2 q level (current+1)
num_negs_at_level2 (Prop.Conditional _ _) level current | level <= current = 0
num_negs_at_level2 (Prop.Conditional p q) level current | level > current = 
  num_negs_at_level2 p level (current+1) + num_negs_at_level2 q level (current+1)

num_conjs_at_level :: Int -> Prop.Expr -> Int
num_conjs_at_level level p = num_conjs_at_level2 p level 0

num_conjs_at_level2 :: Prop.Expr -> Int -> Int -> Int
num_conjs_at_level2 (Prop.Variable _) _ _ = 0
num_conjs_at_level2 (Prop.Negation _) level current | level <= current = 0
num_conjs_at_level2 (Prop.Negation p) level current | level > current = num_conjs_at_level2 p level (current+1)
num_conjs_at_level2 (Prop.Conjunction _ _) level current | level == current = 1
num_conjs_at_level2 (Prop.Conjunction _ _) level current | level < current = 0
num_conjs_at_level2 (Prop.Conjunction p q) level current | level > current = 
  num_conjs_at_level2 p level (current+1) + num_conjs_at_level2 q level (current+1)
num_conjs_at_level2 (Prop.Disjunction _ _) level current | level <= current = 0
num_conjs_at_level2 (Prop.Disjunction p q) level current | level > current = 
  num_conjs_at_level2 p level (current+1) + num_conjs_at_level2 q level (current+1)
num_conjs_at_level2 (Prop.Conditional _ _) level current | level <= current = 0
num_conjs_at_level2 (Prop.Conditional p q) level current | level > current = 
  num_conjs_at_level2 p level (current+1) + num_conjs_at_level2 q level (current+1)

num_disjs_at_level :: Int -> Prop.Expr -> Int
num_disjs_at_level level p = num_disjs_at_level2 p level 0

num_disjs_at_level2 :: Prop.Expr -> Int -> Int -> Int
num_disjs_at_level2 (Prop.Variable _) _ _ = 0
num_disjs_at_level2 (Prop.Negation _) level current | level <= current = 0
num_disjs_at_level2 (Prop.Negation p) level current | level > current = num_disjs_at_level2 p level (current+1)
num_disjs_at_level2 (Prop.Disjunction _ _) level current | level == current = 1
num_disjs_at_level2 (Prop.Disjunction _ _) level current | level < current = 0
num_disjs_at_level2 (Prop.Disjunction p q) level current | level > current = 
  num_disjs_at_level2 p level (current+1) + num_disjs_at_level2 q level (current+1)
num_disjs_at_level2 (Prop.Conjunction _ _) level current | level <= current = 0
num_disjs_at_level2 (Prop.Conjunction p q) level current | level > current = 
  num_disjs_at_level2 p level (current+1) + num_disjs_at_level2 q level (current+1)
num_disjs_at_level2 (Prop.Conditional _ _) level current | level <= current = 0
num_disjs_at_level2 (Prop.Conditional p q) level current | level > current = 
  num_disjs_at_level2 p level (current+1) + num_disjs_at_level2 q level (current+1)

------------------------------------ Counting Sats ----------------------------

type TVA = [(Char, Bool)]

getTVAs :: [Char] -> [TVA]
getTVAs vars = 
    let bs = getBools (length vars)
        f b = zip vars b
    in  map f bs

getBools :: Int -> [[Bool]]
getBools 0 = [[]]
getBools n = 
    let p = getBools (n-1)
        lhs = map (False :) p
        rhs = map (True :) p
    in  lhs ++ rhs

getTable :: Prop.Expr -> [TVA]
getTable p =
    let vs = extract_vars p
    in  getTVAs vs

satProp :: TVA -> Prop.Expr -> Bool
satProp tva (Prop.Variable (Prop.Var p)) = case lookup p tva of
    Nothing -> error "Unexpected"
    Just b -> b
satProp tva (Prop.Negation p) = not (satProp tva p)
satProp tva (Prop.Conjunction p q) = (satProp tva p) && (satProp tva q)
satProp tva (Prop.Disjunction p q) = (satProp tva p) || (satProp tva q)
satProp tva (Prop.Conditional p q) = (not $ satProp tva p) || (satProp tva q)

count_sats :: Prop.Expr -> Int
count_sats p = length (filter (\tva -> satProp tva p) (getTable p))

------------------------------------ four-tuples ------------------------------

create_four_tuples :: Int -> Int -> Int -> IO [FourTuple]
create_four_tuples n v k = do
  pairs <- make_pairs n v k
  extract_four_tuples pairs []

make_pairs :: Int -> Int -> Int -> IO [(Prop.Expr, Prop.Expr)]
make_pairs n v k = do
  putStrLn $ "Creating " ++ show n ++ " pairs..."
  r <- newStdGen
  let (num_vars, r2) = randomR (1,v) r
  let (vs, _, r2) = take_n alphabet num_vars r
  make_pairs2 n k vs []

make_pairs2 :: Int -> Int -> [Char] -> [(Prop.Expr, Prop.Expr)] -> IO [(Prop.Expr, Prop.Expr)]
make_pairs2 n _ _ xs | length xs >= n = return xs
make_pairs2 n k vs acc = do
  r <- newStdGen
  let (c1, r2) = randomR (k `div` 3, k) r
  let (c2, r3) = randomR (k `div` 3, k) r2
  (e1, e2) <- make_pair c1 c2 vs
  is_entails <- e1 `entails` e2
  case is_entails of
    True -> make_pairs2 n k vs ((e1, e2) : acc)
    False -> make_pairs2 n k vs acc

extract_four_tuples :: [(Prop.Expr, Prop.Expr)] -> [FourTuple] -> IO [FourTuple]
extract_four_tuples [] acc = return acc
extract_four_tuples ((a,b) : ps) acc = do
  x <- find_other_pair (a,b) ps []
  case x of
    Just ((a',b'), ps') -> extract_four_tuples ps' ((a, b, a', b'):acc)
    Nothing -> extract_four_tuples ps acc

find_other_pair :: (Prop.Expr, Prop.Expr) -> [(Prop.Expr, Prop.Expr)] -> [(Prop.Expr, Prop.Expr)] -> IO (Maybe ((Prop.Expr, Prop.Expr), [(Prop.Expr, Prop.Expr)]))
find_other_pair _ [] acc = return Nothing
find_other_pair (a,b) ((a', b') : ps) acc = do
  x <- valid_four_tuple (a,b) (a', b')
  case x of
    True -> return $ Just ((a', b'), acc ++ ps)
    False -> find_other_pair (a, b) ps ((a', b') : acc)

valid_four_tuple :: (Prop.Expr, Prop.Expr) -> (Prop.Expr, Prop.Expr) -> IO Bool
valid_four_tuple (a, b) (a', b') = do
  let p1 = Prop.Conjunction a (Prop.Negation b')
  let p2 = Prop.Conjunction a' (Prop.Negation b)
  s1 <- sat p1
  s2 <- sat p2
  return (s1 && s2)

output_file :: String  
output_file = "four_tuples.txt"

write_four_tuples :: [FourTuple] -> IO ()
write_four_tuples fts = forM_ fts $ \(a, b, a2, b2) -> do
  let a' = showF a
  let b' = showF b
  let a2' = showF a2
  let b2' = showF b2
  --putStrLn "Four-tuple found"
  --putStrLn a'
  --putStrLn b'
  --putStrLn a2'
  --putStrLn b2'
  --putStrLn "---"  
  let file = output_file
  let baselines_ab = show (heuristic_1 a b) ++ "," ++ show (heuristic_2 a b) ++ "," ++ show (heuristic_3 a b)
  appendFile file $ a' ++ "," ++ b' ++ ",1," ++ baselines_ab ++ "\n" 
  let baselines_a2b2 = show (heuristic_1 a2 b2) ++ "," ++ show (heuristic_2 a2 b2) ++ "," ++ show (heuristic_3 a2 b2)
  appendFile file $ a2' ++ "," ++ b2' ++ ",1," ++ baselines_a2b2 ++ "\n"
  let baselines_ab2 = show (heuristic_1 a b2) ++ "," ++ show (heuristic_2 a b2) ++ "," ++ show (heuristic_3 a b2)
  appendFile file $ a' ++ "," ++ b2' ++ ",0," ++ baselines_ab2 ++ "\n" 
  let baselines_a2b = show (heuristic_1 a2 b) ++ "," ++ show (heuristic_2 a2 b) ++ "," ++ show (heuristic_3 a2 b)
  appendFile file $ a2' ++ "," ++ b' ++ ",0," ++ baselines_a2b ++ "\n" 

make_four_tuples :: Int -> Int -> Int -> IO ()
make_four_tuples n v k = do
  fts <- create_four_tuples n v k
  putStrLn $ "There were " ++ show (length fts) ++ " four-tuples found."
  putStrLn $ "They produce " ++ show (4 * length fts) ++ " lines."
  write_four_tuples fts
  putStrLn $ "Output written (appended) to " ++ output_file

make_pair :: Int -> Int -> [Char] -> IO (Prop.Expr, Prop.Expr)
make_pair c1 c2 vs = do
  r2 <- newStdGen
  let (p1, r3) = gen_formula r2 c1 vs
  let (p2, _) = gen_formula r3 c2 vs
  return (p1, p2)

average_length = average_stats length_triple
average_num_vars = average_stats num_vars_triple
average_num_ops = average_stats num_ops_triple
average_power_two_num_vars = average_stats power_two_num_vars_triple

average_stats :: (Int -> Entailment -> Int) -> String -> IO Float
average_stats g f = do
  ts <- parse_file f
  let x = List.foldl' g 0 ts
  let x' = fromIntegral x :: Float
  let l = fromIntegral (length ts) :: Float
  let y = x' / l :: Float
  return y

length_triple :: Int -> Entailment -> Int
length_triple n (a, b, _, _, _, _) = n + prop_length a + prop_length b

num_vars_triple :: Int -> Entailment -> Int
num_vars_triple n (a, b, _, _, _, _) = n + num_vars (Prop.Conditional a b)

power_two_num_vars_triple :: Int -> Entailment -> Int
power_two_num_vars_triple n (a, b, _, _, _, _) = n + 2 ^ (num_vars (Prop.Conditional a b))

num_ops_triple :: Int -> Entailment -> Int
num_ops_triple n (a, b, _, _, _, _) = n + num_ops a + num_ops b

num_ops :: Prop.Expr -> Int
num_ops (Prop.Variable _) = 0
num_ops (Prop.Negation p) = num_ops p + 1
num_ops (Prop.Conjunction p q) = num_ops p + num_ops q + 1
num_ops (Prop.Disjunction p q) = num_ops p + num_ops q + 1
num_ops (Prop.Conditional p q) = num_ops p + num_ops q + 1
num_ops (Prop.Biconditional p q) = num_ops p + num_ops q + 1

