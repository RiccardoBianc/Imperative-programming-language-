module Exp

where


data TypeVariable = VarT Int | Type Types | FunType TypeVariable TypeVariable | RefType TypeVariable deriving(Eq,Show,Ord)
data Costraint = Costraint TypeVariable TypeVariable deriving(Eq,Show,Ord)
data ContextInference = ContextInference [(Int,TypeVariable)] deriving(Show,Eq,Ord)
data Loc = Loc Int deriving (Show,Eq,Ord)
data Var = Var Int deriving (Show,Eq,Ord)
data Exp =  Fls
          | Tru
          | Unit
          | Succ Exp
          | IsZero Exp
          | Pred Exp
          | IfThenElse Exp Exp Exp
          | Variable Var
          | LambdaUntyped Var Exp
          | Lambda Var TypeVariable Exp
          | App Exp Exp
          | Seq Exp Exp
          | Let Var Exp Exp
          | Assign Exp Exp
          | Ref Exp
          | Deref Exp
          | Equal Exp Exp
          | Fix Exp
          | While Exp Exp
          | Plus Exp Exp
          | Num Int
          | Minus Exp Exp
          | Location Loc deriving(Show,Eq,Ord)

data Types = Unita | Boolean | Integer | Fun Types Types | TypeRef Types deriving (Show,Eq,Ord)
data Context = Context [(Int,Types)]
data Memory = Memory [(Int,Exp)] deriving (Show)
data AssignType = AssignType [(Int,Types)]

sumv (Var x) y = Var (x+y)
modulo (Var x) = if x>=0 then (Var x) else (Var (-1))
