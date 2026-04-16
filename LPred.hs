{-
 - Practica 7: Lógica de Predicados (Codificación)
 - Profesor: Manuel Soto Romero
 - Ayudante: Diego Mendez Medina
 - Lab: Erick Arroyo 
-}
module LPred where

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

-- ALCANCES
-- Devuelve pares (cuantificador, cuerpo-inmediato) para cada cuantificador en la formula.
alcances :: Formula -> [(Formula, Formula)]
alcances = undefined

-- VARIABLES LIBRES / LIGADAS
varsLibres :: Formula -> [Var]
varsLibres  = undefined

varsLigadas :: Formula -> [Var]
varsLigadas  = undefined

-- SUSTITUCION
sustituye :: Var -> Term -> Formula -> Formula
sustituye = undefined

-- ALPHA EQUIVALENCIA
alphaEq :: Formula -> Formula -> Bool
alphaEq = undefined

-- Número de pruebas
pruebas :: Int
pruebas = 200