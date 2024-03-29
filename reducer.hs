module Reducer

where
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp

freeVars :: Exp -> [Var]
freeVars (Num _) = []
freeVars (Minus a b) = (freeVars a) `union` (freeVars b)
freeVars (Plus a b) = (freeVars a) `union` (freeVars b)
freeVars (While guard prog) = (freeVars guard) `union` (freeVars prog)
freeVars (Fix t) = freeVars t
freeVars (Ref t) = freeVars t
freeVars (Assign t1 t2) = freeVars t1 `union` freeVars t2
freeVars (Deref t) = freeVars t
freeVars (Let x t1 t2) = ((freeVars t2) \\ [x]) `union` (freeVars t1)
freeVars (Seq t1 t2) = freeVars t1 `union` freeVars t2
freeVars Unit = []
freeVars Tru = []
freeVars Fls = []
freeVars (IfThenElse t t1 t2) = freeVars t `union` freeVars t1 `union` freeVars t2
freeVars (Succ t) = freeVars t
freeVars (Pred t) = freeVars t
freeVars (IsZero t) = freeVars t
freeVars (Variable x) = [x]
freeVars (Lambda v _ esp) = (freeVars esp) \\ [v]
freeVars (LambdaUntyped v esp) = (freeVars esp) \\ [v]
freeVars (App term1 term2) = (freeVars term1) `union` (freeVars term2)
freeVars _ = []

allVars :: Exp -> [Var]
allVars (Minus a b)          = (allVars a) `union` (allVars b)
allVars (Num _)              = []
allVars (Plus a b)           = (allVars a) `union` (allVars b)
allVars (While guard prog)   = (allVars guard) `union` (allVars prog)
allVars (Fix t)              = allVars t
allVars (Ref t)              = allVars t
allVars (Assign t1 t2)       = (allVars t1) `union` (allVars t2)
allVars (Deref t)            = allVars t
allVars (Let x t1 t2)        = (allVars t2) `union` [x] `union` (allVars t1)
allVars (Seq t1 t2)          = allVars t1 `union` allVars t2
allVars Unit                 = []
allVars Tru                  = []
allVars Fls                  = []
allVars (IfThenElse t t1 t2) = allVars t `union` allVars t1 `union` allVars t2
allVars (Succ t)             = allVars t
allVars (Pred t)             = allVars t
allVars (IsZero t)           = allVars t
allVars (Variable x)         = [x]
allVars (Lambda x _ esp)     = (allVars esp) `union` [x]
allVars (LambdaUntyped x esp)  = (allVars esp) `union` [x]
allVars (App term1 term2)    =  (allVars term1) `union` (allVars term2)
allVars _                    = []

subst :: Exp -> Exp -> Var -> Exp
subst (Minus a b) t' y = (Minus (subst a t' y) (subst b t' y))
subst (Num a) _ _ = (Num a)
subst (Plus a b) t' y = (Plus (subst a t' y) (subst b t' y))
subst (While guard prog) t' y = (While (subst guard t' y) (subst prog t' y))
subst (Fix t) t' y = (Fix (subst t t' y))
subst (Location (Loc x)) _ _ = (Location (Loc x))
subst (Ref t) t' y = Ref (subst t t' y)
subst (Assign t1 t2) t' y = Assign (subst t1 t' y) (subst t2 t' y)
subst (Deref t) t' y = Deref (subst t t' y)
subst (Let x t1 t2) t' y = if x==y then
                                    (Let x (subst t1 t' y) t2) else
                               if elem x (freeVars(t')) then
                                  (Let new_var (subst t1 t' y)  (subst (subst t2 (Variable new_var) x )  t' y))
                                  else
                                    (Let (x) (subst t1 t' y) (subst t2 t' y) )
                                 where new_var = (sumv (modulo (maximum set)) 1)
                                       set = (freeVars t') `union` (allVars (Variable x) `union` (allVars t2))
subst (Seq t1 t2) t' x = Seq (subst t1 t' x) (subst t2 t' x)
subst Unit _ _ = Unit
subst Tru _ _ = Tru
subst Fls _ _ = Fls
subst (IfThenElse t t1 t2) t' x = IfThenElse (subst t t' x) (subst t1 t' x) (subst t2 t' x)
subst (Succ t) t' x = Succ (subst t t' x)
subst (Pred t) t' x = Pred (subst t t' x)
subst (IsZero t) t' x = IsZero (subst t t' x)
subst (Variable (Var x)) t (Var y) = case x == y of
                                                             True -> t
                                                             _    -> (Variable (Var x))
subst (Lambda (Var x) tipo t)  t_primo (Var y) = if x==y
                                      then (Lambda (Var x) tipo t) else
                            if elem (Var x) (freeVars(t_primo)) then
                               subst (Lambda new_var tipo (subst t (Variable new_var) (Var x) )) t_primo (Var y)
                               else
                               (Lambda (Var x) tipo (subst t t_primo (Var y)))
                              where set = union (freeVars t_primo)(allVars (Lambda (Var x) tipo t))
                                    new_var = sumv (modulo (maximum set)) 1

subst (LambdaUntyped (Var x) t)  t_primo (Var y) = if x==y
                                         then (LambdaUntyped (Var x) t) else
                               if elem (Var x) (freeVars(t_primo)) then
                                  subst (LambdaUntyped (sumv (modulo (maximum set)) 1) (subst t (Variable (sumv (modulo (maximum set)) 1)) (Var x) )) t_primo (Var y)
                                  else
                                  (LambdaUntyped (Var x) (subst t t_primo (Var y)))
                                 where set = union (freeVars t_primo)(allVars (LambdaUntyped (Var x) t))

subst (App t1 t2) t (Var x) = App (subst t1 t (Var x)) (subst t2 t (Var x))

isVal:: Exp -> Bool
isVal (LambdaUntyped (Var x) t) = True
isVal (Lambda (Var x) tipo t)   = True
isVal Tru                       = True
isVal Fls                       = True
isVal Unit                      = True
isVal (Location(Loc _))         = True
isVal t                         = isNum t

isNum :: Exp -> Bool
isNum (Num _) = True
isNum _       = False

update_memory :: Int -> Exp -> Memory -> Memory
update_memory location value (Memory memory) = if (lookup location memory) == Nothing then
                                        Memory (union [(location,value)] memory) else
                                        Memory (map (\(x,val) -> if x == location then (x,value) else (x,val)) memory)

create_loc :: Memory -> Exp -> (Maybe Exp,Memory)
create_loc (Memory memory) value = let (locs,values) = unzip memory in
                                        if memory == [] then
                                        (Just(Location (Loc 0)),Memory [(0,value)]) else
                                        (Just(Location (Loc ((maximum locs)+1))),Memory(memory++[((maximum locs)+1,value)]))

reduce :: Exp -> Memory -> (Maybe Exp,Memory)
reduce (Minus (Num a) (Num b)) memory = (Just (Num (a-b)),memory)
reduce (Minus (Num a) t) memory = case reduce t memory of
                                  (Just t',memory') -> (Just (Minus (Num a) t'),memory')
                                  _ -> (Nothing,memory)
reduce (Minus t t1) memory = case reduce t memory of
                                  (Just t',memory') -> (Just (Minus t' t1),memory')
                                  _ -> (Nothing,memory)
reduce (Plus (Num a) (Num b)) memory = (Just (Num (a+b)),memory)
reduce (Plus (Num a) t) memory = case reduce t memory of
                                  (Just t',memory') -> (Just (Plus (Num a) t'),memory')
                                  _ -> (Nothing,memory)
reduce (Plus t t1) memory = case reduce t memory of
                                  (Just t',memory') -> (Just (Plus t' t1),memory')
                                  _ -> (Nothing,memory)
reduce (While guard prog) memory = (Just (IfThenElse guard (Seq prog (While guard prog)) Unit),memory)
reduce (Fix ((LambdaUntyped (Var x) t))) memory = (Just (subst t (Fix ((LambdaUntyped (Var x) t))) (Var x)),memory)
reduce (Fix t) memory = case reduce t memory of
                            (Just t',memory') -> (Just (Fix t'),memory')
                            _                 -> (Nothing,memory)
reduce (Succ (Num a)) memory = (Just (Num (a+1)),memory)
reduce (Succ t) memory = case reduce t memory of
                            (Just t',memory') -> (Just (Succ t'),memory')
                            _                 -> (Nothing,memory)
reduce (Pred (Num a))   memory      = (Just (Num (a-1)),memory)
reduce (Pred t)  memory      = case reduce t memory of
                                  (Just t',memory') -> (Just (Pred t'),memory')
                                  _                 -> (Nothing,memory)
reduce (IsZero (Num a)) memory = if a==0 then (Just Tru,memory) else (Just Fls,memory)
reduce (IsZero t)    memory            = case reduce t memory of
                                            (Just t',memory') -> (Just (IsZero t'),memory')
                                            _                 -> (Nothing,memory)
reduce (IfThenElse Tru t1 t2) memory = (Just t1,memory)
reduce (IfThenElse Fls t1 t2) memory = (Just t2,memory)
reduce (IfThenElse t t1 t2) memory = case reduce t memory of
                                        (Just t',memory') -> (Just (IfThenElse t' t1 t2),memory')
                                        _                 -> (Nothing,memory)
reduce (App (LambdaUntyped (Var x) t) v) memory | isVal v = (Just (subst t v (Var x)),memory)
reduce (App (Lambda (Var x) tipo t) v) memory | isVal v = (Just (subst t v (Var x)),memory)
reduce (App v t2) memory | isVal v = case reduce t2 memory of
                                        (Just t,memory') -> (Just (App v t),memory')
                                        _                -> (Nothing,memory)
reduce (App t1 t2) memory = case reduce t1 memory of
                                (Just t,memory') -> (Just (App t t2),memory')
                                _                -> (Nothing,memory)

reduce (Seq Unit t2) memory = (Just t2,memory)

reduce (Seq t1 t2) memory = case reduce t1 memory of
                                (Just t1',memory') -> (Just (Seq t1' t2),memory')
                                _                  -> (Nothing,memory)

reduce (Let x v t) memory | isVal v = (Just (subst t v x),memory)
reduce (Let x t1 t2) memory = case reduce t1 memory of
                                (Just t1',memory') -> (Just (Let x t1' t2),memory')
                                _                  -> (Nothing,memory)

reduce (Deref (Location (Loc x))) (Memory memory) = let value = lookup x memory in
                                                    case value of
                                                        Just mem -> (Just mem,Memory memory)
                                                        _ -> (Nothing,Memory memory)
reduce (Deref t) memory = case reduce t memory of
                              (Just t',memory') -> (Just (Deref t'),memory')
                              _                 -> (Nothing,memory)

reduce (Assign  (Location (Loc x)) v) memory | isVal v = (Just Unit,update_memory x v memory )
reduce (Assign  (Location (Loc x)) t2) memory = case reduce t2 memory of
                                                    (Just t2',memory') -> (Just (Assign (Location (Loc x)) t2'),memory')
                                                    _                  -> (Nothing,memory)
reduce (Assign t1 t2) memory = case reduce t1 memory of
                              (Just t1',memory') -> (Just (Assign t1' t2),memory')
                              _                  -> (Nothing,memory)

reduce (Ref v) memory | isVal v = create_loc memory v
reduce (Ref t) memory = case reduce t memory of
                              (Just t',memory') -> (Just (Ref t'),memory')
                              _                 -> (Nothing,memory)
reduce _ memory = (Nothing,memory)

reduceStar :: Exp -> Memory -> Exp
reduceStar t memory = case reduce t memory of
           (Just x,m) -> (reduceStar x m)
           _          -> t
