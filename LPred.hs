{-
 - Practica 7: Lógica de Predicados (Codificación)
 - Profesor: Manuel Soto Romero
 - Ayudante: DiesustituirEnFormula Mendez Medina
 - Lab: Erick Arroyo
 - Ramirez Mendoza Joaquin Rodrigo
 - Sanchez Loaeza Dana Ximena
-}
module LPred where

import Data.List (nub)

-- TIPOS
type Var = String

type Nombre = String

data Term
  = V Var
  | Fun Nombre [Term]
  deriving (Show, Eq)

data Formula
  = Top
  | Bot
  | Pred Nombre [Term]
  | Neg Formula
  | Conj Formula Formula
  | Disy Formula Formula
  | Impl Formula Formula
  | Forall Var Formula
  | Exists Var Formula
  deriving (Show, Eq)

-- VARIABLES EN TERMINOS Y FORMULAS
--  Devuelve una lista de las variables libres en un término.
--  Toma un término como entrada y analiza sus componentes para obtener las variables.
--
--   Ejemplo:
--   >>> varsTerm (Var "x")
-- ["x"]
varsTerm :: Term -> [Var]
varsTerm (V x) = [x]
varsTerm (Fun _ ts) = nub (concatMap varsTerm ts)

--   Devuelve una lista de las variables libres en una fórmula.
--   Analiza la fórmula proporcionada y regresa las variables libres correspondientes.
--
--   Ejemplo:
--   >>> varsFormula (ForAll "x" (Var "y"))
--   ["y"]
varsFormula :: Formula -> [Var]
varsFormula Top = []
varsFormula Bot = []
varsFormula (Pred _ ts) = nub (concatMap varsTerm ts)
varsFormula (Neg f) = varsFormula f
varsFormula (Conj a b) = nub (varsFormula a ++ varsFormula b)
varsFormula (Disy a b) = nub (varsFormula a ++ varsFormula b)
varsFormula (Impl a b) = nub (varsFormula a ++ varsFormula b)
varsFormula (Forall x f) = nub (x : varsFormula f)
varsFormula (Exists x f) = nub (x : varsFormula f)

--  Genera una nueva variable que no está en la lista dada.
--   Utiliza una convención para asegurar que la variable devuelta sea única.
--
--   Ejemplo:
--   >>> freshVar ["x", "y"]
--   "z"
freshVar :: [Var] -> Var
freshVar varsOcupadas = head [v | n <- [1 :: Int ..], let v = "v" ++ show n, v `notElem` varsOcupadas]

-- RENOMBRAMIENTO
--   renombra una variable en un término o fórmula.
--   Asegura que las instancias de la variable antigua se cambien a la nueva.
--
--   Ejemplo:
--   >>> renombra "x" "y" (ForAll "x" (Var "x"))
--   (ForAll "y" (Var "y"))
renombra :: Var -> Var -> Formula -> Formula
renombra x y = renombrarF
  where
    renombrarF Top = Top
    renombrarF Bot = Bot
    renombrarF (Pred p ts) = Pred p (map renombrarT ts)
    renombrarF (Neg f) = Neg (renombrarF f)
    renombrarF (Conj a b) = Conj (renombrarF a) (renombrarF b)
    renombrarF (Disy a b) = Disy (renombrarF a) (renombrarF b)
    renombrarF (Impl a b) = Impl (renombrarF a) (renombrarF b)
    renombrarF (Forall v f)
      | v == x = Forall v f
      | otherwise = Forall v (renombrarF f)
    renombrarF (Exists v f)
      | v == x = Exists v f
      | otherwise = Exists v (renombrarF f)

    renombrarT (V v)
      | v == x = V y
      | otherwise = V v
    renombrarT (Fun n ts) = Fun n (map renombrarT ts)

-- ALCANCES

--   Estudia el alcance de las variables en una fórmula.
--   Devuelve las variables vinculadas y sus respectivos ámbitos.
--
--   Ejemplo:
--   >>> alcances (ForAll "x" (Var "y"))
--   ["x"]
alcances :: Formula -> [(Formula, Formula)]
alcances Top = []
alcances Bot = []
alcances (Pred _ _) = []
alcances (Neg f) = alcances f
alcances (Conj a b) = alcances a ++ alcances b
alcances (Disy a b) = alcances a ++ alcances b
alcances (Impl a b) = alcances a ++ alcances b
alcances (Forall x f) = (Forall x f, f) : alcances f
alcances (Exists x f) = (Exists x f, f) : alcances f

-- VARIABLES LIBRES / LIGADAS
--   Determina las variables libres en una expresión dada.
--
--   Ejemplo:
--   >>> varsLibres (ForAll "x" (Var "y"))
--   ["y"]
varsLibres :: Formula -> [Var]
varsLibres Top = []
varsLibres Bot = []
varsLibres (Pred _ ts) = nub (concatMap varsTerm ts)
varsLibres (Neg f) = varsLibres f
varsLibres (Conj a b) = nub (varsLibres a ++ varsLibres b)
varsLibres (Disy a b) = nub (varsLibres a ++ varsLibres b)
varsLibres (Impl a b) = nub (varsLibres a ++ varsLibres b)
varsLibres (Forall x f) = diff (varsLibres f) [x]
varsLibres (Exists x f) = diff (varsLibres f) [x]

diff :: (Eq a) => [a] -> [a] -> [a]
diff xs ys = filter (`notElem` ys) xs

--   identifica las variables ligadas en una expresión.
--   Estas son las variables que están dentro del ámbito de un cuantificador.
--
--   Ejemplo:
--   >>> varsLigadas (ForAll "x" (Var "y"))
varsLigadas :: Formula -> [Var]
varsLigadas Top = []
varsLigadas Bot = []
varsLigadas (Pred _ _) = []
varsLigadas (Neg f) = varsLigadas f
varsLigadas (Conj a b) = nub (varsLigadas a ++ varsLigadas b)
varsLigadas (Disy a b) = nub (varsLigadas a ++ varsLigadas b)
varsLigadas (Impl a b) = nub (varsLigadas a ++ varsLigadas b)
varsLigadas (Forall x f) = nub (x : varsLigadas f)
varsLigadas (Exists x f) = nub (x : varsLigadas f)

-- SUSTITUCION
--   Realiza la sustitución de una variable por un término en una expresión.
--
--   Ejemplo:
--   >>> sustituye "x" (Var "y") (ForAll "x" (Var "x"))
--   (ForAll "x" (Var "y"))
sustituye :: Var -> Term -> Formula -> Formula
sustituye x t = sustituirEnFormula
  where
    sustituirEnFormula Top = Top
    sustituirEnFormula Bot = Bot
    sustituirEnFormula (Pred p ts) = Pred p (map (sustTerm x t) ts)
    sustituirEnFormula (Neg f) = Neg (sustituirEnFormula f)
    sustituirEnFormula (Conj a b) = Conj (sustituirEnFormula a) (sustituirEnFormula b)
    sustituirEnFormula (Disy a b) = Disy (sustituirEnFormula a) (sustituirEnFormula b)
    sustituirEnFormula (Impl a b) = Impl (sustituirEnFormula a) (sustituirEnFormula b)
    sustituirEnFormula (Forall v f)
      | v == x = Forall v f
      | v `elem` varsTerm t && x `elem` varsLibres f =
          let v' = freshVar (varsFormula f ++ varsTerm t ++ [x, v])
              f' = renombra v v' f
           in Forall v' (sustituirEnFormula f')
      | otherwise = Forall v (sustituirEnFormula f)
    sustituirEnFormula (Exists v f)
      | v == x = Exists v f
      | v `elem` varsTerm t && x `elem` varsLibres f =
          let v' = freshVar (varsFormula f ++ varsTerm t ++ [x, v])
              f' = renombra v v' f
           in Exists v' (sustituirEnFormula f')
      | otherwise = Exists v (sustituirEnFormula f)

--   sustituye un término por otro en una expresión.
--
--   Ejemplo:
--   >>> sustTerm (Var "x") (Var "y") (ForAll "x" (Var "x"))
--   (ForAll "x" (Var "y"))
sustTerm :: Var -> Term -> Term -> Term
sustTerm x t (V v)
  | v == x = t
  | otherwise = V v
sustTerm x t (Fun n ts) = Fun n (map (sustTerm x t) ts)

-- ALPHA EQUIVALENCIA
-- ============================================================
-- Determina si dos fórmulas de lógica de predicados son equivalentes alfa.
-- Dos fórmulas son equivalentes alfa si tienen la misma estructura lógica
-- y difieren únicamente en los nombres de las variables ligadas.
-- Para determinar la equivalencia alfa, se siguen estos pasos:
--   1. Convertir ambas fórmulas a una forma canónica (canon).
--   2. En la forma canónica, todas las variables ligadas se renombran
--      sistemáticamente como v1, v2, v3, ... según el orden en que aparecen.
--   3. Comparar las dos formas canónicas con igualdad estructural (==).
--
-- Ejemplo:
--   >>> alphaEq (Forall "x" (Pred "P" [V "x"]))
--               (Forall "z" (Pred "P" [V "z"]))
--   True
--
--   >>> alphaEq (Forall "x" (Pred "P" [V "y"]))
--               (Forall "z" (Pred "P" [V "y"]))
--   True
--
--   >>> alphaEq (Forall "x" (Pred "P" [V "x"]))
--               (Forall "z" (Pred "P" [V "y"]))
--   False
-- ============================================================

alphaEq :: Formula -> Formula -> Bool
alphaEq f g = canon f == canon g

-- Convierte una fórmula en su forma canónica.
-- Devuelve la fórmula con todas las variables ligadas renombradas
-- a nombres estándar (v1, v2, v3, ...).
canon :: Formula -> Formula
canon formula = fst (renombraVarsLigadas 1 [] formula)

-- RENOMBRA VARIABLES LIGADAS
-- Recorre la fórmula y renombra sistemáticamente las variables ligadas.
-- Parámetros:
--   counter : contador para generar nombres frescos (v1, v2, ...)
--   env     : entorno de sustitución [(VarOriginal, VarCanonica)]
--   formula : fórmula a renombrar
--
-- Devuelve:
--   (fórmula renombrada, contador actualizado)
-- ============================================================

renombraVarsLigadas :: Int -> [(Var, Var)] -> Formula -> (Formula, Int)
renombraVarsLigadas counter env formula = case formula of
  Top -> (Top, counter)
  Bot -> (Bot, counter)
  Pred predName terms ->
    (Pred predName [renombraTerms env t | t <- terms], counter)
  Neg subformula ->
    let (subRenom, nextCounter) = renombraVarsLigadas counter env subformula
     in (Neg subRenom, nextCounter)
  Conj left right ->
    let (renamedLeft, counter1) = renombraVarsLigadas counter env left
        (renamedRight, counter2) = renombraVarsLigadas counter1 env right
     in (Conj renamedLeft renamedRight, counter2)
  Disy left right ->
    let (renamedLeft, counter1) = renombraVarsLigadas counter env left
        (renamedRight, counter2) = renombraVarsLigadas counter1 env right
     in (Disy renamedLeft renamedRight, counter2)
  Impl left right ->
    let (renamedLeft, counter1) = renombraVarsLigadas counter env left
        (renamedRight, counter2) = renombraVarsLigadas counter1 env right
     in (Impl renamedLeft renamedRight, counter2)
  Forall var subformula ->
    let vCanon = "v" ++ show counter
        extEnv = (var, vCanon) : env
        (subRenom, nextCounter) = renombraVarsLigadas (counter + 1) extEnv subformula
     in (Forall vCanon subRenom, nextCounter)
  Exists var subformula ->
    let vCanon = "v" ++ show counter
        extEnv = (var, vCanon) : env
        (subRenom, nextCounter) = renombraVarsLigadas (counter + 1) extEnv subformula
     in (Exists vCanon subRenom, nextCounter)

-- RENOMBRA TERMS
-- Aplica el entorno de sustitución a los términos.
-- Si la variable aparece en el entorno, se sustituye por su nombre canónico.
-- Si no aparece, se deja igual (es libre).
-- ============================================================

renombraTerms :: [(Var, Var)] -> Term -> Term
renombraTerms env term = case term of
  V varName ->
    case lookup varName env of
      Just vCanon -> V vCanon
      Nothing -> V varName
  Fun funName args ->
    Fun funName [renombraTerms env arg | arg <- args]

-- Número de pruebas

pruebas :: Int
pruebas = 1000
