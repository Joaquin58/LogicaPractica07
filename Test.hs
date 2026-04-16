module Test where

import Test.QuickCheck      hiding (Fun)
import Data.List            (nub, (\\))
import Data.Char            (isDigit)
import Data.Monoid          (All(..), Any(..))
import Control.Monad        (liftM2)
import Control.Applicative  (liftA2)
import qualified LPred as LP

-- GENERADORES

vars :: [String]
vars = ["x", "y", "z", "u", "v"]

funs :: [String]
funs = ["f", "g", "h"]

preds :: [String]
preds = ["P", "Q", "R", "S"]

genTerm :: Int -> Gen LP.Term
genTerm 0 = LP.V <$> elements vars
genTerm n =
  frequency
    [ (4, LP.V   <$> elements vars)
    , (2, LP.Fun <$> elements funs <*> vectorOf 1 (genTerm (n `div` 2)))
    , (1, LP.Fun <$> elements funs <*> vectorOf 2 (genTerm (n `div` 2)))
    ]

genFormula :: Int -> Gen LP.Formula
genFormula 0 = LP.Pred <$> elements preds <*> vectorOf 1 (genTerm 1)
genFormula n =
  frequency
    [ (4, LP.Pred   <$> elements preds <*> vectorOf 1 (genTerm 2))
    , (2, LP.Neg    <$> sub)
    , (2, LP.Conj   <$> sub <*> sub)
    , (2, LP.Disy   <$> sub <*> sub)
    , (1, LP.Impl   <$> sub <*> sub)
    , (2, LP.Forall <$> elements vars <*> sub)
    , (2, LP.Exists <$> elements vars <*> sub)
    ]
  where sub = genFormula (n `div` 2)

-- | Formula con cuantificador en la raiz.
genQuantified :: Gen LP.Formula
genQuantified = do
  x    <- elements vars
  body <- genFormula 3
  elements [LP.Forall x body, LP.Exists x body]

-- | Variable que no aparece en la formula dada.
genFreshVar :: LP.Formula -> Gen LP.Var
genFreshVar f =
  let usados     = LP.varsFormula f
      candidatos = filter (`notElem` usados)
                     ["w","a","b","c","d","e","m","n","p","q"]
  in case candidatos of
       (c:_) -> return c
       []    -> return (LP.freshVar usados)

instance Arbitrary LP.Formula where
  arbitrary = sized (\n -> genFormula (min 6 n))
  shrink (LP.Neg f)      = [f]
  shrink (LP.Conj a b)   = [a, b]
  shrink (LP.Disy a b)   = [a, b]
  shrink (LP.Impl a b)   = [a, b]
  shrink (LP.Forall _ f) = [f]
  shrink (LP.Exists _ f) = [f]
  shrink _               = []

instance Arbitrary LP.Term where
  arbitrary = sized genTerm

-- all via foldMap sobre el monoide All.
todosEn :: (a -> Bool) -> [a] -> Bool
todosEn p = getAll . foldMap (All . p)

-- Conjuncion de dos predicados mediante el aplicativo de funciones.
ambos :: (a -> Bool) -> (a -> Bool) -> a -> Bool
ambos p q = (&&) <$> p <*> q

-- Levanta un predicado binario a Property sobre pares generados.
liftPred2 :: (Show a, Show b)
          => (a -> b -> Bool) -> Gen a -> Gen b -> Property
liftPred2 p ga gb = forAll ((,) <$> ga <*> gb) (uncurry p)

-- Verifica que una medida sobre formulas se preserve bajo un operador binario.
preservadoPor :: Show a
              => (a -> [LP.Var]) -> (a -> a -> a) -> Gen a -> Property
preservadoPor medida op gen =
  forAll (liftM2 (,) gen gen) $ \(a, b) ->
    todosEn (`elem` (medida a ++ medida b)) (medida (op a b))

-- PROPIEDADES

-- 1. ALCANCES: el primer componente de cada par es siempre un cuantificador
prop_alcances_cuantificadores :: LP.Formula -> Bool
prop_alcances_cuantificadores =
  getAll . foldMap (All . esCuantificador . fst) . LP.alcances
  where
    esCuantificador =
      getAny . ((Any . esForall) <> (Any . esExists))
    esForall (LP.Forall _ _) = True
    esForall _               = False
    esExists (LP.Exists _ _) = True
    esExists _               = False

-- 2. ALCANCES: el segundo componente es exactamente el cuerpo del cuantificador
prop_alcances_cuerpo_correcto :: LP.Formula -> Bool
prop_alcances_cuerpo_correcto =
  getAll . foldMap (\(q,c) -> All (cuerpoCorrecto q c)) . LP.alcances
  where
    cuerpoCorrecto (LP.Forall _ c) c' = c == c'
    cuerpoCorrecto (LP.Exists _ c) c' = c == c'
    cuerpoCorrecto _               _  = False

-- 3. varsLibres es subconjunto de varsFormula
--    Construida aplicativamente: la formula es el argumento implicito
prop_varsLibres_subset :: LP.Formula -> Bool
prop_varsLibres_subset f =
  todosEn (\v -> v `elem` LP.varsFormula f) (LP.varsLibres f)

-- 4. varsLigadas es subconjunto de varsFormula  (idem, aplicativo)
prop_varsLigadas_subset :: LP.Formula -> Bool
prop_varsLigadas_subset f =
  todosEn (\v -> v `elem` LP.varsFormula f) (LP.varsLigadas f)

-- 5. varsFormula esta contenido en varsLibres union varsLigadas
prop_particion_vars :: LP.Formula -> Bool
prop_particion_vars f =
  todosEn (`elem` (LP.varsLibres f ++ LP.varsLigadas f)) (LP.varsFormula f)

-- 6. sustituye no introduce variables ajenas a f o a t,
prop_sust_sin_basura :: Property
prop_sust_sin_basura =
  forAll triple $ \(x, t, f) ->
    let resultado  = LP.varsFormula (LP.sustituye x t f)
        permitidas = nub (LP.varsFormula f ++ LP.varsTerm t)
        esFresca v = take 1 v == "v"
                  && not (null (drop 1 v))
                  && all isDigit (drop 1 v)
    in todosEn (\v -> v `elem` permitidas || esFresca v) resultado
  where
    triple = (,,) <$> elements vars <*> arbitrary <*> arbitrary

-- 7. sustituye elimina x de las variables libres
prop_sust_elimina_libre :: Property
prop_sust_elimina_libre =
  forAll casoValido $ \(x, t, f) ->
    x `notElem` LP.varsLibres (LP.sustituye x t f)
  where
    casoValido = do
      x <- elements vars
      f <- arbitrary `suchThat` (elem    x . LP.varsLibres)
      t <- arbitrary `suchThat` (notElem x . LP.varsTerm)
      return (x, t, f)

-- 8. sustituye es identidad cuando x no es libre en f
prop_sust_identidad :: Property
prop_sust_identidad =
  forAll casoValido $ \(x, t, f) ->
    LP.sustituye x t f == f
  where
    casoValido = do
      x <- elements vars
      f <- arbitrary `suchThat` (notElem x . LP.varsLibres)
      t <- arbitrary
      return (x, t, f)

-- 9. alphaEq es reflexiva  (aplicativo de funciones)
prop_alpha_reflexiva :: LP.Formula -> Bool
prop_alpha_reflexiva = LP.alphaEq <$> id <*> id

-- 10. alphaEq es simetrica: eq(f,f') iff eq(f',f)
prop_alpha_simetrica :: Property
prop_alpha_simetrica =
  forAll parAlpha $ \(f, f') ->
    LP.alphaEq f f' == LP.alphaEq f' f
  where
    parAlpha = do
      f <- arbitrary
      x <- elements vars
      let y = LP.freshVar (LP.varsFormula f)
      return (f, renombraCuant x y f)

    renombraCuant x y (LP.Forall v b)
      | v == x    = LP.Forall y (LP.renombra x y b)
      | otherwise = LP.Forall v (renombraCuant x y b)
    renombraCuant x y (LP.Exists v b)
      | v == x    = LP.Exists y (LP.renombra x y b)
      | otherwise = LP.Exists v (renombraCuant x y b)
    renombraCuant x y (LP.Neg f)    = LP.Neg  (renombraCuant x y f)
    renombraCuant x y (LP.Conj a b) = LP.Conj (renombraCuant x y a) (renombraCuant x y b)
    renombraCuant x y (LP.Disy a b) = LP.Disy (renombraCuant x y a) (renombraCuant x y b)
    renombraCuant x y (LP.Impl a b) = LP.Impl (renombraCuant x y a) (renombraCuant x y b)
    renombraCuant _ _ f = f

-- 11. Renombrar la variable ligada de la raiz produce formula alfa-equivalente
prop_alpha_renombre :: Property
prop_alpha_renombre =
  forAll genQuantified $ \f ->
    forAll (genFreshVar f) $ \y ->
      LP.alphaEq f (renombraRaiz y f)
  where
    renombraRaiz y (LP.Forall x b) = LP.Forall y (LP.sustituye x (LP.V y) b)
    renombraRaiz y (LP.Exists x b) = LP.Exists y (LP.sustituye x (LP.V y) b)
    renombraRaiz _ f               = f

-- 12. alphaEq distingue Forall de Exists (propiedad negativa)
prop_alpha_distingue :: Property
prop_alpha_distingue =
  forAll par $ \(f1, f2) -> not (LP.alphaEq f1 f2)
  where
    par = do
      x    <- elements vars
      body <- genFormula 2
      return (LP.Forall x body, LP.Exists x body)

-- RUNNER

run :: Testable prop => String -> prop -> IO Bool
run lbl prop = do
  putStrLn $ "\n> " ++ lbl
  r <- quickCheckWithResult stdArgs { maxSuccess = LP.pruebas, chatty = False } prop
  case r of
    Success { numTests = n } ->
      putStrLn ("  OK  " ++ show n ++ " casos") >> return True
    GaveUp { numTests = n } ->
      putStrLn ("  WARN demasiados descartados (" ++ show n ++ " validos)") >> return False
    Failure { output = o } ->
      putStrLn ("  FAIL\n" ++ o) >> return False
    _ ->
      putStrLn "  FAIL" >> return False

main :: IO ()
main = do
  putStrLn "  Tests - Logica de Predicados  "

  rs <- sequence
    [ run "Alcances: solo cuantificadores"        prop_alcances_cuantificadores
    , run "Alcances: cuerpo inmediato correcto"    prop_alcances_cuerpo_correcto
    , run "varsLibres subset varsFormula"          prop_varsLibres_subset
    , run "varsLigadas subset varsFormula"         prop_varsLigadas_subset
    , run "varsFormula subset libres+ligadas"      prop_particion_vars
    , run "sustituye: sin variables extra"         prop_sust_sin_basura
    , run "sustituye: elimina variable libre"      prop_sust_elimina_libre
    , run "sustituye: identidad si no es libre"    prop_sust_identidad
    , run "alphaEq reflexiva"                      prop_alpha_reflexiva
    , run "alphaEq simetrica"                      prop_alpha_simetrica
    , run "alphaEq por renombramiento ligado"      prop_alpha_renombre
    , run "alphaEq distingue Forall de Exists"     prop_alpha_distingue
    ]

  let ok    = length (filter id rs)
      total = length rs
      calif = (fromIntegral ok / fromIntegral total :: Double) * 10
      entera  = floor calif :: Int
      decimal = round (calif * 10) `mod` 10 :: Int

  putStrLn "\n============================================"
  putStrLn $ "Pruebas exitosas : " ++ show ok ++ "/" ++ show total
  putStrLn $ "Calificacion     : " ++ show entera ++ "." ++ show decimal ++ "/10"
  putStrLn "============================================"