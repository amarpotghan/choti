module Core where

import Control.Applicative
import Data.Monoid
import Control.Monad

type Index = Int

data Name
  = Const String
  | Bounded Index
  | Unquoted Index
  deriving (Show, Eq)

-- N.B. in STLC there are no type variables
data Type
   = TypeIdentifier Name
   | FunctionArrow Type Type
   deriving (Show, Eq)

data InferableTerm
  = Annote CheckableTerm Type
  | Variable Index
  | Free Name
  | Application InferableTerm CheckableTerm
  deriving (Show, Eq)

data CheckableTerm
  = I InferableTerm
  | Lambda CheckableTerm -- N.B No variable because de brujin indices
  deriving (Show, Eq)

data Neutral
  = FreeValue Name
  | App Neutral Value

data Value
  = Fun (Value -> Value)
  | Neutral Neutral

type Compute =
  [Value] -- Env
  -> Value

apply (Fun f) v = f v
apply (Neutral n) v = Neutral (App n v)

-- evaluator

evalInferrable :: InferableTerm -> Compute
evalInferrable (Annote expr _) = evalCheckable expr
evalInferrable (Variable ix) = (!! ix)
evalInferrable (Free name) = const (Neutral (FreeValue name))
evalInferrable (Application i c) = liftA2 apply (evalInferrable i) (evalCheckable c)

evalCheckable :: CheckableTerm -> Compute
evalCheckable (Lambda c) = \e -> Fun $ \x -> evalCheckable c (x:e)
evalCheckable (I i) = evalInferrable i

-- type checker
data K = K deriving (Show, Eq)
data Constant = Type Type | Kind K deriving (Show, Eq)
type Context = [(Name, Constant)]

substitutionInferrable :: Index -> InferableTerm -> InferableTerm -> InferableTerm
substitutionInferrable i with (Annote e t) = Annote (substitutionCheckable i with e) t
substitutionInferrable i with v@(Variable j) = if i == j then with else v
substitutionInferrable i with f@(Free name) = f
substitutionInferrable i with (Application e1 e2) = Application (substitutionInferrable i with e1) (substitutionCheckable i with e2)

substitutionCheckable :: Index -> InferableTerm -> CheckableTerm -> CheckableTerm
substitutionCheckable i with (I e) = I (substitutionInferrable i with e)
substitutionCheckable i with (Lambda f) = Lambda (substitutionCheckable (i + 1) with f)

quote :: Value -> CheckableTerm
quote = quote' 0
  where
    quote' i (Fun f) = Lambda (quote' (i + 1) (f (Neutral (FreeValue (Unquoted i)))))
    quote' i (Neutral n) = I (neutralQuote i n)
    neutralQuote i (FreeValue (Unquoted x)) = Variable (i - x - 1)
    neutralQuote i (FreeValue x) = Free x


data TypeError
  = UnknownIdentifier
  | IllegalApplication
  | BugInTypeChecker
  | TypeMismatch Type Type
  | NoConform CheckableTerm Type
  deriving (Show, Eq)

axioms :: Context -> Type -> K -> Either TypeError ()
axioms c (TypeIdentifier n) K = maybe (Left UnknownIdentifier) (\(Kind K) -> pure ()) (lookup n c)
axioms c (FunctionArrow from to) k = axioms c from k *> axioms c to k

checkType :: Index -> Context -> CheckableTerm -> Type -> Either TypeError ()
checkType i c (Lambda f) (FunctionArrow t1 t2) =
  checkType (i + 1) ((Bounded i, Type t1):c) (substitutionCheckable 0 (Free (Bounded i)) f) t2
checkType i c (I e) t2 = do
  t1 <- inferTypeWith i c e
  unless (t1 == t2) $
    Left (TypeMismatch t1 t2)
checkType _ _ e t1 = Left $ NoConform e t1

inferType :: Context -> InferableTerm -> Either TypeError Type
inferType = inferTypeWith 0

inferTypeWith :: Index -> Context -> InferableTerm -> Either TypeError Type
inferTypeWith i c (Annote term typ) = do
  axioms c typ K
  checkType i c term typ
  pure typ
inferTypeWith i c (Free name) =
  maybe (Left UnknownIdentifier)
  (\(Type t) -> Right t) $
  lookup name c
inferTypeWith i c (Application e1 e2) = do
  function <- inferTypeWith i c e1
  case function of
    FunctionArrow from to -> do
      checkType i c e2 to
      pure to
    _ -> Left IllegalApplication
inferTypeWith _ _ (Variable _) = Left BugInTypeChecker -- we covert all (Variable i) to Free (Bound i)
