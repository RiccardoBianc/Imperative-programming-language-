module Imperative

where
import           Control.Monad
import           Exp
import           Inference
import           Parser
import           Reducer
import           System.IO
import           Typechecker

-- shell :: IO String
-- shell = do
--     putStr "Inserire comando\n"
--     command <- getLine
--     if command == ":file"
--         then do{putStr "Inserire path\n"; path <- getLine; lettura path;}
--         else if command == ":bash"
--             then do{putStr "Inserire programma\n";interpreter} else
--                 if command == ":exit" then do{return "fuori"} else shell

-- interpreter ::String -> IO String
-- interpreter program = do
--                 --program <- getLine
--                 case  (parse (firstparse) (filter (/='\n') program) ) of
--                                     [] -> return ("Errore di parsing")
--                                     (parsed,""):xs -> case costraint 0 (ContextInference []) parsed of
--                                             Right (_,costraints,_) -> if (unify costraints)/= Nothing
--                                                 then return(show(reduceStar parsed (Memory [])))
--                                                 else return("Errore di tipo")
--                                             Left e -> return e
--                                     (parsed,remaining):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))
parsa filename = do
    res <- readFile filename
    return (parse firstparse res)

unifica filename = do
    res <- readFile filename
    case  (parse (firstparse) (filter (/='\n') res) ) of
                        [] -> return ("Errore di parsing")
                        (parsed,"",_):xs -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,tipo) -> return (show (unify (costraints)) ) {-("costraint: "++show (costraints)++"----tipo   "++show tipo++"****"++(show (foundPrincipalType (unify (costraints)) tipo ) ))-}
                                Left s                    -> return s
                        (parsed,remaining,_):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))

lettura :: String -> IO String
lettura filename = do
    res <- readFile filename
    case  (parse (firstparse) (filter (/='\n') res) ) of
                        [] -> return ("Errore di parsing")
                        (parsed,"",_):xs -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,_) -> if (unify costraints) /= Nothing
                                    then return(show(reduceStar parsed (Memory []))++ show costraints)
                                    else return ("Impossibile unificare, impossibile tipare"++(show costraints))
                                Left s -> return s
                        (parsed,remaining,_):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))
