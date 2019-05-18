module Exp

where

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
          | Lambda Var Types Exp
          | App Exp Exp
          | Seq Exp Exp
          | Let Var Exp Exp
          | Assign Exp Exp
          | Ref Exp
          | Deref Exp
          | EqualsInt Exp Exp
          | Fix Exp
          | While Exp Exp
          | Plus Exp Exp
          | Num Int
          | Location Loc deriving(Show,Eq,Ord)

data Types = Unita | Boolean | Integer | Fun Types Types | TypeRef Types deriving (Show,Eq,Ord)
data Context = Context [(Int,Types)]
data Memory = Memory [(Int,Exp)] deriving (Show)
data AssignType = AssignType [(Int,Types)]

sumv (Var x) y = Var (x+y)
modulo (Var x) = if x>=0 then (Var x) else (Var (-1))
