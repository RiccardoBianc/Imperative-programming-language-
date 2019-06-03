module Inference

where
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp
import           Reducer

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


costraint :: Int -> ContextInference -> Exp -> Either String (Int,[Costraint],TypeVariable)
costraint typevariables context (While guard body) = case (costraint typevariables context guard) of
                                                    Right (freshguard,cguard,tipoguard) ->
                                                        case (costraint freshguard context body) of
                                                            Right (freshbody,cbody,tipobody) -> Right ((freshbody,cguard++cbody++[Costraint tipoguard (Type Boolean),Costraint tipobody (Type Unita)],Type Unita))
                                                            Left e -> Left e
                                                    Left e -> Left e

costraint typevariables context (Deref t) = case (costraint typevariables context t) of
                                                        Right (fresht,c,tipot) ->
                                                            Right ((fresht+1),c++[Costraint (RefType (VarT fresht)) tipot],VarT fresht)
                                                        Left e -> Left e
costraint typevariables context (Assign t1 t2) = case (costraint typevariables context t1) of
                                                    Right (fresht1,c1,tipot1) ->
                                                        case (costraint fresht1 context t2) of
                                                            Right (fresht2,c2,tipot2) -> Right ((fresht2,c1++c2++[Costraint tipot1 (RefType tipot2)],Type Unita))
                                                            Left e -> Left e
                                                    Left e -> Left e

costraint typevariables context (Ref t) = case (costraint typevariables context t) of
                                                        Right (fresht,c,tipot) ->
                                                            Right (fresht,c,RefType tipot)
                                                        Left e -> Left e
costraint typevariables _ (Unit) = Right (typevariables,[],Type Unita)
costraint typevariables context (Minus a b) = case (costraint typevariables context a) of
                                                                            Right (fresha,ca,tipoa) ->
                                                                                case (costraint fresha context b) of
                                                                                    Right (freshb,cb,tipob) -> Right ((freshb,ca++cb++[Costraint tipob (Type Integer),Costraint tipoa (Type Integer)],Type Integer))
                                                                                    Left e -> Left e
                                                                            Left e -> Left e
costraint typevariables context (Plus a b) = case (costraint typevariables context a) of
                                                Right (fresha,ca,tipoa) ->
                                                    case (costraint fresha context b) of
                                                        Right (freshb,cb,tipob) -> Right ((freshb,ca++cb++[Costraint tipob (Type Integer),Costraint tipoa (Type Integer)],Type Integer))
                                                        Left e -> Left e
                                                Left e -> Left e
costraint typevariables context (Fix t) = case (costraint typevariables context t) of
                                                        Right (fresht,c,tipot) ->  let x = VarT fresht in
                                                            Right ((fresht+1),c++[Costraint tipot (FunType x x) ],x)
                                                        Left e -> Left e

-- -- Let polymorphism, solo con valori per avere soundness dei reference
-- costraint typevariables context (Let (Var x) t1 t2) | isVal t1 = case (costraint typevariables context t1) of
--                                                         Right (fresht1,c1,tipot1) -> let sigma = unify c1 in
--                                                             let (t1_principal_type,context_applied) = (foundPrincipalType sigma tipot1,ContextInference (change_context context sigma)) in
--                                                             let variables_to_generalize = freev context_applied t1_principal_type in
--                                                             let scheme = Scheme variables_to_generalize t1_principal_type in
--                                                             case context_applied of
--                                                                 ContextInference a -> case (costraint fresht1 (ContextInference [((Var x),scheme)]++a)  t2) of
--                                                                     Right (fresht2,c2,tipot2) -> Right ((fresht2,c1++c2,tipot2))
--                                                                     Left e -> Left e
--
--                                                         Left e -> Left e

-- Let polymorphism, solo con valori per avere soundness dei reference
costraint typevariables context (Let (Var x) t1 t2) | isVal t1 = case (costraint typevariables context t1) of
                                                        Right (fresht1,c1,tipot1) -> let sigma = unify c1 in
                                                            case (costraint fresht1 context (subst t2 t1 (Var x)) ) of
                                                            Right (fresht2,c2,tipot2) -> Right ((fresht2,c1++c2,tipot2))
                                                            Left e -> Left e
                                                        Left e -> Left e
--Let "normale"
costraint typevariables context (Let (Var x) t1 t2) = case (costraint typevariables context t1) of
                                                    Right (fresht1,c1,tipot1) ->
                                                        let context' = replaceVariable x tipot1 context in
                                                        case (costraint fresht1 context' t2) of
                                                        Right (fresht2,c2,tipot2) -> Right ((fresht2,c1++c2,tipot2))
                                                        Left e -> Left (e++" in normal")
                                                    Left e -> Left (e++" out normal")

costraint typevariables context (Seq t1 t2) = case (costraint typevariables context t1) of
                                                                            Right (fresht1,c1,tipot1) ->
                                                                                case (costraint fresht1 context t2) of
                                                                                    Right (fresht2,c2,tipot2) -> Right ((fresht2,c1++c2++[Costraint tipot1 (Type Unita)],tipot2))
                                                                                    Left e -> Left (e++" SEQ FUORI---"++show t1)
                                                                            Left e -> Left (e++"SEQ DENTRO")

costraint typevariables context (App t1 t2) = case (costraint typevariables context t1) of
                                               Right(fresht1,c1,tipot1) ->
                                                    case (costraint fresht1 context t2) of
                                                        Right(fresht2,c2,tipot2) -> Right ((fresht2+1),c1++c2++[Costraint tipot1 (FunType tipot2 (VarT (fresht2))  )],VarT (fresht2))
                                                        Left e -> Left e
                                               Left e -> Left e
costraint typevariables context (Lambda (Var x) type1 esp) = let t1 = case type1 of
                                                                            VarT x -> VarT (-x-1)
                                                                            x -> x in
                                                let context' = replaceVariable x t1 context in
                                                case costraint typevariables context' esp of
                                                    Right (fresh,costraint',t2) -> Right ((fresh,costraint',FunType t1 t2))
                                                    Left e -> Left e

costraint typevariables context (LambdaUntyped (Var x) esp) = let t1 = VarT typevariables in
                                                let context' = replaceVariable x t1 context in
                                                    case costraint (typevariables+1) context' esp of
                                                        Right (fresh,costraint',t2) -> Right ((fresh,costraint',FunType t1 t2))
                                                        Left e -> Left e

costraint typevariables (ContextInference context) (Variable (Var x)) = case lookup x context of
                                                    (Just t) -> Right ((typevariables,[],t))
                                                    Nothing -> Left "Variabile"
costraint typevariables context (IsZero t)  = case costraint typevariables context t of
                                Right(fresh,c,tipo) -> Right ((fresh,c ++ [Costraint tipo (Type Integer)],Type Boolean))
                                Left e -> Left e
costraint typevariables context (Pred t)  = case costraint typevariables context t of
                                Right (fresh,c,tipo) -> Right ((fresh,c ++ [Costraint tipo (Type Integer)],Type Integer))
                                Left e -> Left e
costraint typevariables context (Succ t)  = case costraint typevariables context t of
                                Right (fresh,c,tipo) -> Right ((fresh,c ++ [Costraint tipo (Type Integer)],Type Integer))
                                Left e -> Left e
costraint typevariables _ (Num _)  = Right ((typevariables,[],Type Integer))
costraint typevariables _ Tru  =  Right ((typevariables,[],Type Boolean))
costraint typevariables _ Fls  = Right ((typevariables,[],Type Boolean))
costraint typevariables context (IfThenElse t t1 t2) =
    case (costraint typevariables context t) of
        Right (fresht,c,tipot) -> case (costraint fresht context t1) of
            Right (fresht1,c1,tipot1) ->
                case (costraint fresht1 context t2) of
                    Right (fresht2,c2,tipot2) -> Right((fresht2,c ++ c1 ++ c2 ++ [Costraint tipot (Type Boolean),Costraint tipot1 tipot2],tipot1 ))
                    Left e -> Left e
            Left e -> Left e
        Left e -> Left e

type Unificator = [(TypeVariable,TypeVariable)]
-- data ContextInference = ContextInference [(Int,TypeVariable)] deriving(Show,Eq,Ord)


principal (VarT x)      = [(VarT x)]
principal (FunType a b) = (principal a) ++ (principal b)
principal (RefType x)   = principal x
principal (Type _)      = []

vcontext context_applied = case unzip context_applied of
                            ([a],[b]) -> [b]


freev :: ContextInference -> TypeVariable -> [TypeVariable]
freev (ContextInference context_applied) t1_principal_type = let variablestype = principal t1_principal_type in
                                                             let context_variables = vcontext context_applied in (variablestype \\ context_variables)

change_context :: ContextInference -> Maybe Unificator -> [(Int,TypeVariable)]
change_context (ContextInference []) _ = ([])
change_context (ContextInference ((var,t):l)) (Just un) = case lookup t un of
                                                     Just x ->  ((var,x):(change_context (ContextInference l) (Just un)))
                                                     Nothing -> ((var,t):(change_context (ContextInference l) (Just un)))

foundPrincipalType :: Maybe Unificator -> TypeVariable -> TypeVariable
foundPrincipalType (Just u) (VarT x) = case lookup (VarT x) u of
                                            Just t -> foundPrincipalType (Just u) t
                                            Nothing -> (VarT x)
foundPrincipalType u (RefType x) = RefType (foundPrincipalType u x)
foundPrincipalType _ (Type x) = Type x
foundPrincipalType u (FunType a b) = FunType (foundPrincipalType u a ) (foundPrincipalType u b )


belongs :: TypeVariable -> TypeVariable -> Bool
belongs (VarT x) (VarT t)    = x==t
belongs (VarT x) (Type s)    = False
belongs (VarT x) (FunType t1 t2) = (belongs (VarT x) t1) || (belongs (VarT x) t2)
belongs (VarT x) (RefType t) = belongs (VarT x) t


composition :: Maybe Unificator ->  Maybe Unificator -> Unificator -> Maybe Unificator
composition e (Just u) [(x,s)] = case lookup s u of
                                    Just b  -> case (composition e (Just (u\\[(s,b)])) [(x,s)]) of
                                                    Just res -> Just (union res (union u [(x,b)]))
                                                    Nothing -> Just (union u [(x,b)])
                                    Nothing -> Just (union u [(x,s)])
composition _ Nothing _ =  Nothing

-- composition :: Maybe Unificator ->  Maybe Unificator -> Unificator -> Maybe Unificator
-- composition (Just u) (Just []) [(x,s)] = Just ([(x,s)])
-- composition (Just u) (Just ((a,b):t)) [(x,s)] | s==a = Just (union (u) [(x,b)])
-- composition (Just u) (Just ((a,b):t)) [(x,s)] = case composition (Just u) (Just t) [(x,s)] of
--                                         Just res -> Just (union u (union res [(a,b)]))
--                                         _        -> Nothing
-- composition _ Nothing _ =  Nothing


sigma :: Unificator -> TypeVariable -> TypeVariable
sigma (subst) (VarT x) = case lookup (VarT x) subst of
                        Just t  -> t
                        Nothing -> (VarT x)

sigma u (Type t) = Type t
sigma u (FunType t1 t2) = FunType (sigma u t1) (sigma u t2)
sigma u (RefType t) = RefType (sigma u t)


applied :: Unificator -> [Costraint] -> [Costraint]
applied _ [] = []
applied u ((Costraint a b):ctail) = [Costraint (sigma u a) (sigma u b)]++(applied u ctail)

-- compose :: Unificator -> Unificator -> Unificator
-- compose (Un []) (Un []) = Un []
-- compose (Un (sigma:s')) (Un (gamma:g')) =

unify :: [Costraint] -> Maybe Unificator
unify [] = Just []
unify ((Costraint s' t):c) = case (s',t) of
                           (Type s,Type x) | s==x  -> unify(c)
                           (VarT s,t') |  (VarT s)==t'-> unify(c)
                           (s,VarT t') | s==VarT t'-> unify(c)
                           (VarT s,t') | not (belongs (VarT s) t') -> let xtc = applied [(VarT s,t')] c in
                                                                      let new_sigma = unify xtc in
                                                                      composition new_sigma new_sigma [(VarT s,t')]
                           (s,VarT x) | not (belongs (VarT x) s) -> let xtc = applied [((VarT x),s)] c in
                                                                      let new_sigma = unify xtc in
                                                                      composition new_sigma new_sigma [((VarT x),s)]
                           (FunType s1 s2,FunType t1 t2) -> unify (c++[Costraint s2 t2]++[Costraint s1 t1])
                           (RefType s,RefType t') -> unify(c++[Costraint s t'])
                           _ -> Nothing
