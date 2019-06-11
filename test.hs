module Test

where
import           Exp
import           Inference
import           Interpreter
import           Parser
import           Reducer
import           System.IO


reducerTest :: String -> Exp -> String -> String
reducerTest test result nome_test = case (parse (progparse) (filter (/='\n') test)) of
                        [] -> "Errore di parsing"
                        [(parsed,"",_)] -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,_) -> if (unify costraints) /= Nothing
                                    then if (reduceStar parsed (Memory [])) == result then "Tutto ok.(V) Test: "++nome_test else "Errore nell'assert.(X) Test: "++nome_test
                                    else "Impossibile unificare, impossibile tipare.(X) Test: "++nome_test
                                Left s -> "Impossibile trovare i costraints, variabili libere presenti.(X) Test: "++nome_test
                        [(parsed,remaining,_)] -> "Parsing non terminato.(X) Test: "++nome_test

parserTest :: String -> Exp -> String -> String
parserTest test result nome_test = case (parse (progparse) (filter (/='\n') test)) of
                        [] -> "Errore di parsing"
                        [(parsed,"",_)] -> if parsed==result then "Tutto ok.(V) Test: "++nome_test else "Errore nell'assert.(X) Test: "++nome_test
                        [(parsed,remaining,_)] -> "Parsing non terminato.(X) Test: "++nome_test

inferenceTest :: String -> TypeVariable -> String -> String
inferenceTest test result nome_test = case (parse (progparse) (filter (/='\n') test)) of
                        [] -> "Errore di parsing"
                        [(parsed,"",_)] -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,t) -> let s = unify costraints in
                                    if s == Nothing then "Impossibile unificare" else
                                        case foundPrincipalType s t of
                                            Just tipo -> if tipo == result then "Tutto ok.(V) Test: "++nome_test else "Errore nell'assert.(X) Test: "++show tipo
                                            Nothing -> "Errore nel calcolo del tipo principale. (X) Test: "++nome_test

                                Left _ -> "Impossibile trovare i costraints, variabili libere presenti.(X) Test: "++nome_test
                        _ -> "Parsing non terminato.(X) Test: "++nome_test

inferenceTestError :: String -> String -> String
inferenceTestError test nome_test = case (parse (progparse) (filter (/='\n') test)) of
                        [] -> "Errore di parsing"
                        [(parsed,"",_)] -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,t) -> let s = unify costraints in
                                    if s == Nothing then "Impossibile unificare. (V) Test: "++nome_test else
                                        case foundPrincipalType s t of
                                            Just _ -> "Tutto ok quando non dovrebbe.(X) Test: "++nome_test
                                            Nothing -> "Errore nel calcolo del tipo principale. (X) Test: "++nome_test

                                Left _ -> "Impossibile trovare i costraints, variabili libere presenti.(X) Test: "++nome_test
                        _ -> "Parsing non terminato.(X) Test: "++nome_test


testAllocEqual = "let getValueFromRef = \\ r -> *r in let elemuno = alloc 12 in let elemdue = alloc 0 in let reducerTest = \\ numuno -> \\ numdue -> iszero (numuno - numdue) in elemdue :=12; reducerTest (getValueFromRef elemuno) (getValueFromRef elemdue)"
testRefApplication = "let double = \\ f -> \\ x -> \\ g -> g (f x) in let ref = alloc double in (*ref) (\\x->x+2) 4 (\\x -> x+3)"
testCoveredDeclaration = "let id = (\\x :(int) -> x) in let id = (\\x -> x) in id true"
testCoveredDeclaration2 = "let id = (\\x -> x) in let id = (\\x:(int) -> x) in id true"
testIdPolymorphicNotWorking = "let id = (\\x -> x) in if (id true) {id 5}else{id true}"
testIdPolymorphic = "let id = (\\x -> x) in if (id false) {id 5}else{id 7}"
testRefPolymorphicNotWorking = "let es = alloc 3 in let due = es in let eee = due in eee:=true;*eee"
testRefPolymorphicWorking = "let es = alloc 3 in let due = es in let eee = due in eee:=23;*eee"
testPolimorfismoLambdaNonVa = "let id = (\\x -> x) in (\\id -> if (id true){id 40} else{id 50} )"
testPolimorfismoLambdaVa = "let id = (\\x -> x) in if (id true){id 40} else{id 50}"
testRefdiRefCorretto = "let res = alloc 4 in let new = alloc res in new := *new; *new"


test :: IO()
test = do
    putStrLn (reducerTest testAllocEqual Tru "testAllocEqual")
    putStrLn (reducerTest testRefApplication (Num 9) "testRefApplication")
    putStrLn (inferenceTest testCoveredDeclaration (Type Boolean) "testCoveredDeclaration" )
    putStrLn (reducerTest testCoveredDeclaration (Tru) "testCoveredDeclaration" )
    putStrLn (inferenceTestError testCoveredDeclaration2 "testCoveredDeclaration2")
    putStrLn (inferenceTestError testIdPolymorphicNotWorking "testIdPolymorphicNotWorking")
    putStrLn (reducerTest testIdPolymorphic (Num 7) "testIdPolymorphic")
    putStrLn (inferenceTestError testRefPolymorphicNotWorking "testRefPolymorphic")
    putStrLn (reducerTest testRefPolymorphicWorking (Num 23) "testRefPolymorphicWorking")
    putStrLn (inferenceTestError testPolimorfismoLambdaNonVa "testPolimorfismoLambdaNonVa" )
    putStrLn (reducerTest testPolimorfismoLambdaVa (Num 40) "testPolimorfismoLambdaVa")
    putStrLn (reducerTest testRefdiRefCorretto (Location (Loc 0)) "testRefdiRefCorretto")
