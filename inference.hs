module Inference

where
import Exp
import Data.Char
import Data.List
import Data.Ord

costraint :: ContextInference -> Exp -> ([Costraint],TypeVariable)
-- costraint context (Lambda (Var x)  )
costraint context (Variable (Var x)) = case lookup x context of
                                                    (Just t) -> ([],t)
                                                    _ -> ([Costraint (Type Boolean) (Type Integer)],Type Integer)
costraint context (IsZero t)  = case costraint context t of
                                (c,tipo) -> (c `union`[Costraint tipo (Type Integer)],Type Boolean)
costraint context (Pred t)  = case costraint context t of
                                (c,tipo) -> (c `union`[Costraint tipo (Type Integer)],Type Integer)
costraint context (Succ t)  = case costraint context t of
                                (c,tipo) -> (c `union`[Costraint tipo (Type Integer)],Type Integer)
costraint context (Num a)  = ([],Type Integer)
costraint context Tru  = ([],Type Boolean)
costraint context Fls  = ([],Type Boolean)
costraint context (IfThenElse t t1 t2) =
    case (costraint context t,costraint context t1,costraint context t2)  of
        ((c,tipot),(c1,tipot1),(c2,tipot2)) -> (c `union` c1 `union` c2 `union` [Costraint tipot (Type Boolean),Costraint tipot1 tipot2],tipot1 )
