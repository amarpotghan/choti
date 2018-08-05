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

type Type = Value

data InferableTerm
  = Annote CheckableTerm CheckableTerm
  | Star
  | Pi CheckableTerm CheckableTerm
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
  | StarValue
  | PiValue Value (Value -> Value)

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
evalInferrable Star = const StarValue
evalInferrable (Pi d c) = \e -> PiValue (evalCheckable d e) (\x -> evalCheckable c (x:e))
evalInferrable (Application i c) = liftA2 apply (evalInferrable i) (evalCheckable c)

evalCheckable :: CheckableTerm -> Compute
evalCheckable (Lambda c) = \e -> Fun $ \x -> evalCheckable c (x:e)
evalCheckable (I i) = evalInferrable i

-- type checker
type Context = [(Name, Type)]

substitutionInferrable :: Index -> InferableTerm -> InferableTerm -> InferableTerm
substitutionInferrable i with (Annote e t) = Annote (substitutionCheckable i with e) t
substitutionInferrable i with v@(Variable j) = if i == j then with else v
substitutionInferrable i with f@(Free name) = f
substitutionInferrable i with Star = Star
substitutionInferrable i with (Pi d c) = Pi (substitutionCheckable i with d) (substitutionCheckable (i+1) with c)
substitutionInferrable i with (Application e1 e2) = Application (substitutionInferrable i with e1) (substitutionCheckable i with e2)

substitutionCheckable :: Index -> InferableTerm -> CheckableTerm -> CheckableTerm
substitutionCheckable i with (I e) = I (substitutionInferrable i with e)
substitutionCheckable i with (Lambda f) = Lambda (substitutionCheckable (i + 1) with f)

quote :: Value -> CheckableTerm
quote = quote' 0
  where
    quote' i (Fun f) = Lambda (quote' (i + 1) (f (Neutral $ FreeValue $ Unquoted i)))
    quote' i (Neutral n) = I (neutralQuote i n)
    quote' i StarValue = I Star
    quote' i (PiValue d c) = I (Pi (quote' i d) (quote' (i+1) (c (Neutral $ FreeValue $ Unquoted i))))
    neutralQuote i (FreeValue (Unquoted x)) = Variable (i - x - 1)
    neutralQuote i (FreeValue x) = Free x

data TypeError
  = UnknownIdentifier
  | IllegalApplication
  | BugInTypeChecker
  | TypeMismatch Type Type
  | NoConform CheckableTerm Type

checkType :: Index -> Context -> CheckableTerm -> Type -> Either TypeError ()
checkType i c (Lambda f) (PiValue dom codfun) =
  -- add variable to the context
  checkType (i + 1) ((Bounded i, dom):c)
  -- substitute on f and result of Pi's codfun
  (substitutionCheckable 0 (Free (Bounded i)) f) (codfun (Neutral $ FreeValue $ Bounded i))
checkType i c (I f) v = do
  typeOfLambda <- inferTypeWith i c f
  -- syntactic check, thus we need to quote the values
  when (quote typeOfLambda == quote v) $
    Left $ TypeMismatch typeOfLambda v
checkType _ _ e t1 = Left $ NoConform e t1

inferType :: Context -> InferableTerm -> Either TypeError Type
inferType = inferTypeWith 0

inferTypeWith :: Index -> Context -> InferableTerm -> Either TypeError Type
inferTypeWith i c (Annote term typ) = do
  checkType i c typ StarValue
  -- the interesting bit here
  let evaluated = evalCheckable typ mempty
  -- check term against evaulated type v
  checkType i c term evaluated
  pure evaluated
inferTypeWith i c Star = pure StarValue
inferTypeWith i c (Pi d co) = do
  checkType i c d StarValue
  -- the interesting bit here

  let evaluated = evalCheckable d mempty
  checkType (i+1) ((Bounded i, evaluated):c) (substitutionCheckable 0 (Free $ Bounded i) co) StarValue
  pure StarValue

inferTypeWith i c (Free name) =
  maybe (Left UnknownIdentifier)
  pure $
  lookup name c
inferTypeWith i c (Application e1 e2) = do
  function <- inferTypeWith i c e1
  case function of
    PiValue d codfun -> do
      checkType i c e2 d
      pure (codfun $ evalCheckable e2 mempty)
    _ -> Left IllegalApplication
inferTypeWith _ _ (Variable _) = Left BugInTypeChecker -- we covert all (Variable i) to Free (Bound i)
