module Interpreter

where
import           Control.Monad
import           Exp
import           Inference
import           Parser
import           Reducer
import           System.IO
import           Typechecker


parsa filename = do
    res <- readFile filename
    return (parse progparse res)

unifica filename = do
    res <- readFile filename
    case  (parse (progparse) (filter (/='\n') res) ) of
                        [] -> return ("Errore di parsing")
                        (parsed,"",_):xs -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,tipo) -> return (show (foundPrincipalType (unify (costraints)) tipo ) ) {-("costraint: "++show (costraints)++"----tipo   "++show tipo++"****"++(show (foundPrincipalType (unify (costraints)) tipo ) ))-}
                                Left s                    -> return s
                        (parsed,remaining,_):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))

lettura :: String -> IO String
lettura filename = do
    res <- readFile filename
    case  (parse (progparse) (filter (/='\n') res) ) of
                        [] -> return ("Errore di parsing")
                        (parsed,"",_):xs -> case costraint 0 (ContextScheme []) parsed of
                                Right (_,costraints,_) -> if (unify costraints) /= Nothing
                                    then return(show(reduceStar parsed (Memory []))++ show costraints)
                                    else return ("Impossibile unificare, impossibile tipare"++(show parsed))
                                Left s -> return s
                        (parsed,remaining,_):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))
