module Exp

where
import           Data.Char

instance Show Types where
    show (Integer)         = "Int"
    show (Boolean)         = "Bool"
    show (Unita)           = "Unit"
    show (Fun (Fun a b) c) =  "("++show (Fun a b)++") -> "++show c
    show (Fun a b)         = show a++" -> "++show b
    show (TypeRef x)       = "Ref "++show x

instance Show TypeVariable where
  show (VarT x)                  = show (chr (x+97))
  show (Type x)                  =  show x
  show (FunType (FunType a b) c) =  "("++show (FunType a b)++") -> "++show c
  show (FunType a b)             = show a++" -> "++show b
  show (RefType x)               = "Ref "++show x

data Parser a = Parser (String -> [(String,Int)] -> [(a,String,[(String,Int)])])
data TypeVariable = VarT Int | Type Types | FunType TypeVariable TypeVariable | RefType TypeVariable deriving(Eq,Ord)
data Costraint = Costraint TypeVariable TypeVariable deriving(Eq,Show,Ord)
data ContextInference = ContextScheme [(Int,TypeScheme)] | ContextInference  [(Int,TypeVariable)] deriving(Show,Eq,Ord)
data TypeScheme = Scheme [TypeVariable] TypeVariable deriving(Show,Eq,Ord)
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
          | Fix Exp
          | While Exp Exp
          | Plus Exp Exp
          | Num Int
          | Minus Exp Exp
          | Location Loc deriving(Show,Eq,Ord)

data Types = Unita | Boolean | Integer | Fun Types Types | TypeRef Types deriving (Eq,Ord)
data Context = Context [(Int,Types)]
data Memory = Memory [(Int,Exp)] deriving (Show)
data AssignType = AssignType [(Int,Types)]

sumv (Var x) y = Var (x+y)
modulo (Var x) = if x>=0 then (Var x) else (Var (-1))
