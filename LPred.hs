{-
 - Practica 7: Lógica de Predicados (Codificación)
 - Profesor: Manuel Soto Romero
 - Ayudante: Diego Mendez Medina
 - Lab: Erick Arroyo 
-} 
module LPred where

import Data.List (nub, (\\))

-- TIPOS
type Var    = String
type Nombre = String

data Term
  = V Var
  | Fun Nombre [Term]
  deriving (Show, Eq)

data Formula
  = Top
  | Bot
  | Pred Nombre [Term]
  | Neg  Formula
  | Conj Formula Formula
  | Disy Formula Formula
  | Impl Formula Formula
  | Forall Var Formula
  | Exists Var Formula
  deriving (Show, Eq)

-- VARIABLES EN TERMINOS Y FORMULAS
varsTerm :: Term -> [Var]
varsTerm (V x)       = [x]
varsTerm (Fun _ ts)  = nub (concatMap varsTerm ts)

varsFormula :: Formula -> [Var]
varsFormula Top            = []
varsFormula Bot            = []
varsFormula (Pred _ ts)    = nub (concatMap varsTerm ts)
varsFormula (Neg f)        = varsFormula f
varsFormula (Conj a b)     = nub (varsFormula a ++ varsFormula b)
varsFormula (Disy a b)     = nub (varsFormula a ++ varsFormula b)
varsFormula (Impl a b)     = nub (varsFormula a ++ varsFormula b)
varsFormula (Forall x f)   = nub (x : varsFormula f)
varsFormula (Exists x f)   = nub (x : varsFormula f)

-- VARIABLE FRESCA
freshVar :: [Var] -> Var
freshVar usados = head ["v" ++ show n | n <- [(1 :: Int)..], ("v" ++ show n) `notElem` usados]

-- RENOMBRAMIENTO (solo ocurrencias libres)
renombra :: Var -> Var -> Formula -> Formula
renombra x y = go
  where
    go Top            = Top
    go Bot            = Bot
    go (Pred p ts)    = Pred p (map goT ts)
    go (Neg f)        = Neg (go f)
    go (Conj a b)     = Conj (go a) (go b)
    go (Disy a b)     = Disy (go a) (go b)
    go (Impl a b)     = Impl (go a) (go b)
    go (Forall v f)
      | v == x        = Forall v f
      | otherwise     = Forall v (go f)
    go (Exists v f)
      | v == x        = Exists v f
      | otherwise     = Exists v (go f)

    goT (V v)
      | v == x        = V y
      | otherwise     = V v
    goT (Fun n ts)    = Fun n (map goT ts)

-- ALCANCES
-- Devuelve pares (cuantificador, cuerpo-inmediato) para cada cuantificador en la formula.
alcances :: Formula -> [(Formula, Formula)]
alcances Top            = []
alcances Bot            = []
alcances (Pred _ _)     = []
alcances (Neg f)        = alcances f
alcances (Conj a b)     = alcances a ++ alcances b
alcances (Disy a b)     = alcances a ++ alcances b
alcances (Impl a b)     = alcances a ++ alcances b
alcances (Forall x f)   = (Forall x f, f) : alcances f
alcances (Exists x f)   = (Exists x f, f) : alcances f

-- VARIABLES LIBRES / LIGADAS
varsLibres :: Formula -> [Var]
varsLibres Top            = []
varsLibres Bot            = []
varsLibres (Pred _ ts)    = nub (concatMap varsTerm ts)
varsLibres (Neg f)        = varsLibres f
varsLibres (Conj a b)     = nub (varsLibres a ++ varsLibres b)
varsLibres (Disy a b)     = nub (varsLibres a ++ varsLibres b)
varsLibres (Impl a b)     = nub (varsLibres a ++ varsLibres b)
varsLibres (Forall x f)   = varsLibres f \\ [x]
varsLibres (Exists x f)   = varsLibres f \\ [x]

varsLigadas :: Formula -> [Var]
varsLigadas Top           = []
varsLigadas Bot           = []
varsLigadas (Pred _ _)    = []
varsLigadas (Neg f)       = varsLigadas f
varsLigadas (Conj a b)    = nub (varsLigadas a ++ varsLigadas b)
varsLigadas (Disy a b)    = nub (varsLigadas a ++ varsLigadas b)
varsLigadas (Impl a b)    = nub (varsLigadas a ++ varsLigadas b)
varsLigadas (Forall x f)  = nub (x : varsLigadas f)
varsLigadas (Exists x f)  = nub (x : varsLigadas f)

-- SUSTITUCION
sustituye :: Var -> Term -> Formula -> Formula
sustituye x t = go
  where
    go Top           = Top
    go Bot           = Bot
    go (Pred p ts)   = Pred p (map (sustTerm x t) ts)
    go (Neg f)       = Neg (go f)
    go (Conj a b)    = Conj (go a) (go b)
    go (Disy a b)    = Disy (go a) (go b)
    go (Impl a b)    = Impl (go a) (go b)
    go (Forall v f)
      | v == x       = Forall v f
      | v `elem` varsTerm t =
          let v'  = freshVar (varsFormula f ++ varsTerm t ++ [x, v])
              f'  = renombra v v' f
          in Forall v' (go f')
      | otherwise    = Forall v (go f)
    go (Exists v f)
      | v == x       = Exists v f
      | v `elem` varsTerm t =
          let v'  = freshVar (varsFormula f ++ varsTerm t ++ [x, v])
              f'  = renombra v v' f
          in Exists v' (go f')
      | otherwise    = Exists v (go f)

sustTerm :: Var -> Term -> Term -> Term
sustTerm x t (V v)
  | v == x    = t
  | otherwise = V v
sustTerm x t (Fun n ts) = Fun n (map (sustTerm x t) ts)

-- ALPHA EQUIVALENCIA
alphaEq :: Formula -> Formula -> Bool
alphaEq = alphaEqF [] []
  where
    alphaEqF env renv f g = case (f, g) of
      (Top, Top) -> True
      (Bot, Bot) -> True
      (Pred p ts, Pred q us) ->
        p == q && length ts == length us && and (zipWith (alphaEqT env renv) ts us)
      (Neg a, Neg b) -> alphaEqF env renv a b
      (Conj a b, Conj c d) -> alphaEqF env renv a c && alphaEqF env renv b d
      (Disy a b, Disy c d) -> alphaEqF env renv a c && alphaEqF env renv b d
      (Impl a b, Impl c d) -> alphaEqF env renv a c && alphaEqF env renv b d
      (Forall x a, Forall y b) -> alphaEqF ((x,y):env) ((y,x):renv) a b
      (Exists x a, Exists y b) -> alphaEqF ((x,y):env) ((y,x):renv) a b
      _ -> False

    alphaEqT env renv t1 t2 = case (t1, t2) of
      (V v, V w) ->
        case lookup v env of
          Just w' -> w == w'
          Nothing -> case lookup w renv of
            Just _  -> False
            Nothing -> v == w
      (Fun f ts, Fun g us) ->
        f == g && length ts == length us && and (zipWith (alphaEqT env renv) ts us)
      _ -> False

-- Número de pruebas
pruebas :: Int
pruebas = 200
