module Inference

where
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp
import           Reducer


generateFresh :: ContextInference -> Int -> Int
generateFresh (ContextScheme []) acc = acc
generateFresh (ContextScheme ((var,_):context) ) acc =
                                         if acc < var
                                         then generateFresh (ContextScheme context) (var+1)
                                         else
                                             if acc == var then generateFresh (ContextScheme context) (acc+1)
                                                 else generateFresh (ContextScheme context) (acc)

replaceVariable :: Int -> TypeScheme -> ContextInference -> ContextInference
replaceVariable variable new_scheme (ContextScheme context) = if (lookup variable context) == Nothing then
     ContextScheme (union [(variable,new_scheme )] context) else
         ContextScheme (map (\(x,(Scheme foreach tipo)) -> if x == variable then
             (x,new_scheme) else (x,(Scheme foreach tipo))) context)


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
                                                            Right (fresht2,c2,tipot2) -> Right (fresht2,c1++c2++[Costraint tipot1 (RefType tipot2)],Type Unita)
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
                                                    Right ((fresht+1),c++[Costraint tipot (FunType x x)],x)
                                                Left e -> Left e

-- Let polymorphism con value restriction per avere soundness
costraint typevariables (ContextScheme context) (Let (Var x) t1 t2) | isVal t1 =
        case (costraint typevariables (ContextScheme context) t1) of
            Right (fresht1,c1,tipot1) -> let sigma = unify c1 in
                let t1_principal_type = foundPrincipalType sigma tipot1 in
                case t1_principal_type of
                    Nothing -> Left "Errore nel tipo principale t1"
                    (Just t1_principal_type) ->    let scheme = generalize (ContextScheme context) t1_principal_type in
                                                    let new_context = replaceVariable x scheme (ContextScheme context) in
                                                    case costraint fresht1 new_context t2 of
                                                        Right (a,b,c) ->  Right (a,b,c)
                                                        Left e -> Left e
            Left e -> Left e

-- -- Let polymorphism, solo con valori per avere soundness dei reference
-- costraint typevariables context (Let (Var x) t1 t2) | isVal t1 = case (costraint typevariables context t1) of
--                                                         Right (fresht1,c1,tipot1) -> case (costraint fresht1 context (subst t2 t1 (Var x)) ) of
--                                                                                         Right (fresht2,c2,tipot2) -> Right (fresht2,c1++c2,tipot2)
--                                                                                         Left e -> Left e
--                                                         Left e -> Left e

--Let "normale"
costraint typevariables context (Let (Var x) t1 t2) = case (costraint typevariables context t1) of
                                                            Right (fresht1,c1,tipot1) ->
                                                                let context' = replaceVariable x (Scheme [] tipot1) context in
                                                                case (costraint fresht1 context' t2) of
                                                                Right (fresht2,c2,tipot2) -> Right (fresht2,c1++c2,tipot2)
                                                                Left e -> Left e
                                                            Left e -> Left e

costraint typevariables context (Seq t1 t2) = case (costraint typevariables context t1) of
                                            Right (fresht1,c1,tipot1) ->
                                                case (costraint fresht1 context t2) of
                                                    Right (fresht2,c2,tipot2) -> Right ((fresht2,c1++c2++[Costraint tipot1 (Type Unita)],tipot2))
                                                    Left e -> Left e
                                            Left e -> Left e

costraint typevariables context (App t1 t2) = case (costraint typevariables context t1) of
                                               Right(fresht1,c1,tipot1) ->
                                                    case (costraint fresht1 context t2) of
                                                        Right(fresht2,c2,tipot2) -> Right ((fresht2+1),c1++c2++[Costraint tipot1 (FunType tipot2 (VarT (fresht2))  )],VarT (fresht2))
                                                        Left e -> Left e
                                               Left e -> Left e

costraint typevariables context (Lambda (Var x) type1 esp) = let t1 = sub_var type1 in
                                                let context' = replaceVariable x (Scheme [] t1) context in
                                                case costraint typevariables context' esp of
                                                    Right (fresh,costraint',t2) -> Right ((fresh,costraint',FunType t1 t2))
                                                    Left e -> Left e

costraint typevariables context (LambdaUntyped (Var x) esp) = let t1 = VarT typevariables in
                                                let context' = replaceVariable x (Scheme [] t1) context in
                                                    case costraint (typevariables+1) context' esp of
                                                        Right (fresh,costraint',t2) -> Right ((fresh,costraint',FunType t1 t2))
                                                        Left e -> Left e

costraint typevariables (ContextScheme context) (Variable (Var x)) = case lookup x context of
                                                    (Just (Scheme forall tipo)) -> let (new_type,new_var) = instantiate typevariables forall tipo in Right (new_var,[],new_type)
                                                    Nothing -> Left "Variabile libera, impossibile trovare vincoli"
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

sub_var :: TypeVariable -> TypeVariable
sub_var (VarT x)      = VarT (-x-1)
sub_var (FunType a b) = FunType (sub_var a) (sub_var b)
sub_var (RefType x)   = RefType (sub_var x)
sub_var (Type x)      = Type x

principal :: TypeVariable -> [TypeVariable]
principal (VarT x)      = [(VarT x)]
principal (FunType a b) = (principal a) ++ (principal b)
principal (RefType x)   = principal x
principal (Type _)      = []

vcontext :: ContextInference -> [TypeVariable]
vcontext (ContextInference context_applied) = case unzip context_applied of
                            ([a],b) -> b

instantiate :: Int -> [TypeVariable] -> TypeVariable -> (TypeVariable,Int)
instantiate new [] t = (t,new)
instantiate new (x:l) t = let (t',new') = aux_instantiate new x t in instantiate new' l t'

aux_instantiate :: Int -> TypeVariable -> TypeVariable -> (TypeVariable,Int)
aux_instantiate new (VarT x) (VarT v) | v==x = (VarT new,new+1)
aux_instantiate new (VarT _) (VarT v) = (VarT v,new)
aux_instantiate new forall (FunType a b) = let (a',newa) = aux_instantiate new forall a in
                                       let (b',newb) = aux_instantiate new forall b in
                                       if newa > newb then (FunType a' b',newa) else (FunType a' b',newb)
aux_instantiate new forall (RefType x) = let (x',newx) = aux_instantiate new forall x in
                                      (RefType x',newx)
aux_instantiate new _ (Type x) = (Type x,new)


find_variables_context :: ContextInference -> [TypeVariable]
find_variables_context (ContextScheme [])                      = []
find_variables_context (ContextScheme ((var,Scheme forall t):l)) = ((principal t) \\ forall) `union` (find_variables_context (ContextScheme l) )


generalize :: ContextInference -> TypeVariable -> TypeScheme
generalize context_applied t1_principal_type =
              let variablestype = principal t1_principal_type in
              let variables_context = find_variables_context context_applied in
              let context_variables = vcontext context_applied in Scheme (variablestype \\ variables_context) t1_principal_type

foundPrincipalType :: Maybe Unificator -> TypeVariable -> Maybe TypeVariable
foundPrincipalType (Just u) (VarT x) = case lookup (VarT x) u of
                                            Just t  -> foundPrincipalType (Just u) t
                                            Nothing -> Just (VarT x)
foundPrincipalType u (RefType x) = case (foundPrincipalType u x) of
                                            Just t -> Just (RefType t)
                                            _      -> Nothing
foundPrincipalType (Just _) (Type x) = Just (Type x)
foundPrincipalType u (FunType a b) = case ((foundPrincipalType u a),(foundPrincipalType u b)) of
                                        (Just a',Just b') -> Just (FunType a' b')
                                        _               -> Nothing
foundPrincipalType Nothing _ = Nothing

belongs :: TypeVariable -> TypeVariable -> Bool
belongs (VarT x) (VarT t)    = x==t
belongs (VarT _) (Type _)    = False
belongs (VarT x) (FunType t1 t2) = (belongs (VarT x) t1) || (belongs (VarT x) t2)
belongs (VarT x) (RefType t) = belongs (VarT x) t


composition :: Maybe Unificator -> Unificator -> Maybe Unificator
composition (Just u) [(x,s)] = case lookup s u of
                                    Just b  -> case composition (Just (u\\[(s,b)])) [(x,s)] of
                                                    Just res -> Just (res `union` u `union` [(x,b)])
                                                    Nothing -> Nothing
                                    Nothing -> Just (u `union`[(x,s)])
composition Nothing _ =  Nothing

sigma :: Unificator -> TypeVariable -> TypeVariable
sigma u (VarT x) = case lookup (VarT x) u of
                        Just t -> t
                        _      -> VarT x
sigma _ (Type t) = Type t
sigma u (FunType t1 t2) = FunType (sigma u t1) (sigma u t2)
sigma u (RefType t) = RefType (sigma u t)


applied :: Unificator -> [Costraint] -> [Costraint]
applied _ [] = []
applied u ((Costraint a b):ctail) = (Costraint (sigma u a) (sigma u b)):(applied u ctail)


unify :: [Costraint] -> Maybe Unificator
unify [] = Just []
unify ((Costraint s t):c) = case (s,t) of
                           (s',t') | s'==t' -> unify(c)
                           (VarT s',t') | not (belongs (VarT s') t') -> let xtc = applied [(VarT s',t')] c in
                                                                      let new_sigma = unify xtc in
                                                                      composition new_sigma [(VarT s',t')]
                           (s',VarT t') | not (belongs (VarT t') s') -> let xtc = applied [((VarT t'),s')] c in
                                                                      let new_sigma = unify xtc in
                                                                      composition new_sigma [((VarT t'),s')]
                           (FunType s1 s2,FunType t1 t2) -> unify (c++[Costraint s2 t2]++[Costraint s1 t1])
                           (RefType s',RefType t') -> unify(c++[Costraint s' t'])
                           _ -> Nothing
