module Inference

where
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp

generateFresh :: ContextInference -> Int -> Int
generateFresh (ContextInference []) acc = acc
generateFresh (ContextInference ((var,_):context) ) acc =
                                         if acc < var
                                         then generateFresh (ContextInference context) (var+1)
                                         else
                                             if acc == var then generateFresh (ContextInference context) (acc+1)
                                                 else generateFresh (ContextInference context) (acc)

replaceVariable :: Int -> TypeVariable -> ContextInference -> ContextInference
replaceVariable variable new_type (ContextInference context) = if (lookup variable context)== Nothing then ContextInference (union [(variable,new_type)] context) else ContextInference (map (\(x,tipo) -> if x == variable then (x,new_type) else (x,tipo)) context)


costraint :: Int -> ContextInference -> Exp -> (Int,[Costraint],TypeVariable)

costraint typevariables context ()

costraint typevariables context (Let (Var x) t1 t2) = case (costraint typevariables context t1) of
                                                        (fresht1,c1,tipot1) ->
                                                            let context' = replaceVariable x tipot1 context in
                                                            case (costraint fresht1 context' t2) of
                                                            (fresht2,c2,tipot2) ->
                                                                (fresht2,c1++c2,tipot2)

costraint typevariables context (Seq t1 t2) = case (costraint typevariables context t1) of
                                                (fresht1,c1,tipot1) ->
                                                    case (costraint fresht1 context t2) of
                                                        (fresht2,c2,tipot2) -> (typevariables,c1++c2++[Costraint tipot1 (Type Unita)],tipot2)

costraint typevariables context (App t1 t2) = case (costraint typevariables context t1) of
                                                (fresht1,c1,tipot1) ->
                                                    case (costraint fresht1 context t2) of
                                                    (fresht2,c2,tipot2) ->
                                                        ((fresht2+2),c1++c2++[Costraint tipot1 (FunType tipot2 (VarT (fresht2+1)))],VarT (fresht2+1))
costraint typevariables context (Lambda2 (Var x) type1 esp) = let t1 = case type1 of
                                                                            VarT x -> VarT (-x-1)
                                                                            x -> x in
                                                let context' = replaceVariable x t1 context in
                                                case costraint typevariables context' esp of
                                                    (fresh,costraint',t2) -> (fresh,costraint',FunType t1 t2)

costraint typevariables context (LambdaUntyped (Var x) esp) = let t1 = VarT typevariables in
                                                let context' = replaceVariable x t1 context in
                                                    case costraint (typevariables+1) context' esp of
                                                        (fresh,costraint',t2) -> (fresh,costraint',FunType t1 t2)

costraint typevariables (ContextInference context) (Variable (Var x)) = case lookup x context of
                                                    (Just t) -> (typevariables,[],t)
                                                    _ -> (typevariables,[Costraint (Type Boolean) (Type Integer)],Type Integer)
costraint typevariables context (IsZero t)  = case costraint typevariables context t of
                                (fresh,c,tipo) -> (fresh,c ++ [Costraint tipo (Type Integer)],Type Boolean)
costraint typevariables context (Pred t)  = case costraint typevariables context t of
                                (fresh,c,tipo) -> (fresh,c ++ [Costraint tipo (Type Integer)],Type Integer)
costraint typevariables context (Succ t)  = case costraint typevariables context t of
                                (fresh,c,tipo) -> (fresh,c ++ [Costraint tipo (Type Integer)],Type Integer)
costraint typevariables _ (Num _)  = (typevariables,[],Type Integer)
costraint typevariables _ Tru  = (typevariables,[],Type Boolean)
costraint typevariables _ Fls  = (typevariables,[],Type Boolean)
costraint typevariables context (IfThenElse t t1 t2) =
    case (costraint typevariables context t) of
        (fresht,c,tipot) -> case (costraint fresht context t1) of
            (fresht1,c1,tipot1) ->
                case (costraint fresht1 context t2) of
                    (fresht2,c2,tipot2) -> (fresht2,c ++ c1 ++ c2 ++ [Costraint tipot (Type Boolean),Costraint tipot1 tipot2],tipot1 )

belongs :: TypeVariable -> TypeVariable -> Bool
belongs (VarT x) (VarT t)    = x==t
belongs (VarT x) (Type s)    = False
belongs (VarT x) (FunType t1 t2) = (belongs (VarT x) t1) || (belongs (VarT x) t2)


sigma :: Unificator -> TypeVariable -> TypeVariable
sigma (Un subst) (VarT x) = case lookup (VarT x) subst of
                        Just t  -> t
                        Nothing -> (VarT x)
sigma u (Type Integer) = Type Integer
sigma u (Type Boolean) = Type Boolean
sigma u (FunType t1 t2) = FunType (sigma u t1) (sigma u t2)

data Unificator = Un [(TypeVariable,TypeVariable)]

applied :: Unificator -> [Costraint] -> [Costraint]
applied _ [] = []
applied u ((Costraint a b):ctail) = [Costraint (sigma u a) (sigma u b)]++(applied u ctail)

-- compose :: Unificator -> Unificator -> Unificator
-- compose (Un []) (Un []) = Un []
-- compose (Un (sigma:s')) (Un (gamma:g')) =

unify :: [Costraint] -> Bool
unify [] = True
unify ((Costraint s' t):c) = case (s',t) of
                           (s,x) | s==x                            -> unify(c)
                           (VarT s,t') | not (belongs (VarT s) t') -> let xtc = applied (Un [((VarT s),t')]) c in
                                                                      let new_sigma = unify xtc in
                                                                      new_sigma
                           (s,VarT x) | not  (belongs (VarT x) s) -> let xtc = applied (Un [((VarT x),s)]) c in
                                                                      let new_sigma = unify xtc in
                                                                      new_sigma
                           (FunType s1 s2,FunType t1 t2) -> unify (c++[Costraint s2 t2]++[Costraint s1 t1])
                           (RefType s,RefType t') -> unify(c++[Costraint s t'])
                           _ -> False
