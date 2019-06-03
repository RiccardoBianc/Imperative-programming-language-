module Typechecker

where
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp

replace :: Int -> Types -> Context -> Context
replace variable new_type (Context context) = if (lookup variable context)==Nothing then Context (union [(variable,new_type)] context) else Context (map (\(x,tipo) -> if x == variable then (x,new_type) else (x,tipo)) context)

typeof :: Exp -> Context -> AssignType -> Maybe Types
typeof (Minus a b) context sigma = case (typeof a context sigma,typeof b context sigma) of
                                    (Just Integer,Just Integer) -> (Just Integer)
                                    _ -> Nothing
typeof (Num a) context sigma = Just Integer
typeof (Plus a b) context sigma = case (typeof a context sigma,typeof b context sigma) of
                                    (Just Integer,Just Integer) -> (Just Integer)
                                    _ -> Nothing
typeof (While guard prog) context sigma = case (typeof guard context sigma,typeof prog context sigma) of
                                                (Just Boolean,Just Unita) -> (Just Unita)
                                                _ -> Nothing
typeof (Fix t) context sigma = case typeof t context sigma of
                                (Just (Fun a b)) | a==b -> Just a
                                _                       -> Nothing
typeof (Tru) _ _ = Just Boolean
typeof (Fls) _ _ = Just Boolean
typeof (Succ t) context sigma = case typeof t context sigma of
                            Just Integer -> Just Integer
                            _            -> Nothing
typeof (Pred t) context sigma = case typeof t context sigma of
                            Just Integer -> Just Integer
                            _            -> Nothing
typeof (IsZero t) context sigma = case typeof t context sigma of
                            Just Integer -> Just Boolean
                            _            -> Nothing
typeof (IfThenElse t t1 t2) context sigma = case (typeof t context sigma, typeof t1 context sigma, typeof t2 context sigma) of
                                      (Just Boolean, Just ty, Just ty') -> if ty == ty'
                                                                                 then Just ty
                                                                                 else Nothing
                                      (Just Boolean, err@(Nothing), _) -> err
                                      (Just Boolean, _, err@(Nothing)) -> err
                                      (Just _, _, _) -> Nothing
                                      (err, _, _) -> err
typeof (Variable (Var x)) (Context context) sigma = let t = lookup x context in case t of
                                                                Just t -> Just t
                                                                _ -> Nothing
-- typeof (Lambda (Var x) tipo t) (Context context) sigma = let t2 = typeof t (replace x tipo (Context context)) sigma in case t2 of
--                                                                                      Just x' -> Just (Fun tipo x')
--                                                                                      _ -> Nothing
typeof (App t1 t2) context sigma = let t1' = typeof t1 context sigma in let t2' = typeof t2 context sigma in case (t1',t2') of
                                                                                        (Just (Fun a t),Just b) -> if a==b then Just t else Nothing
                                                                                        _ -> Nothing
typeof (Unit) _ _ = Just Unita
typeof (Seq t1 t2) context sigma = case typeof t1 context sigma of
                                Just Unita -> case typeof t2 context sigma of
                                                    Just t2' -> Just t2'
                                                    _        -> Nothing
                                _ -> Nothing

typeof (Let (Var x) t1 t2) (Context context) sigma = case typeof t1 (Context context) sigma of
                                Just type1 -> case typeof t2  (replace x type1 (Context context)) sigma of
                                                Just type2 -> Just type2
                                                _          -> Nothing
                                _ -> Nothing
typeof (Location (Loc x)) context (AssignType sigma) = let t = lookup x sigma in case t of
                                                                    Just t' -> Just t'
                                                                    _ -> Nothing
typeof (Ref t1) context sigma = case typeof t1 context sigma of
                                    Just t' -> Just (TypeRef t')
                                    _       -> Nothing
typeof (Deref t1) context sigma = case typeof t1 context sigma of
                                    Just (TypeRef t') -> Just (t')
                                    _                 -> Nothing
typeof (Assign t1 t2) context sigma = case (typeof t1 context sigma,typeof t2 context sigma) of
                                        (Just(TypeRef t'),Just(t'')) -> if t'==t'' then Just (Unita) else Nothing
                                        _ -> Nothing
