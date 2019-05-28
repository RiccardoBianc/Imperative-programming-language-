module Imperative

where
import           Control.Monad
import           Exp
import           Inference
import           Parser
import           Reducer
import           System.IO
import           Typechecker

shell :: IO String
shell = do
    putStr "Inserire comando\n"
    command <- getLine
    if command == ":file"
        then do{putStr "Inserire path\n"; path <- getLine; lettura path;}
        else if command == ":bash"
            then do{putStr "Inserire programma\n";interpreter} else
                if command == ":exit" then do{return "fuori"} else shell

interpreter :: IO String
interpreter = do
                program <- getLine
                case  (parse (firstparse) program) of
                    [] -> return "Errore di parsing"
                    (parsed,""):xs -> case typeof parsed (Context []) (AssignType []) of
                                        Just _ -> return(show(reduceStar parsed (Memory [])))
                                        _ -> return "Errore di tipo"
                    (parsed,remaining):xs -> return ("Parsing non terminato   "++remaining++"-----"++(show parsed))

lettura :: String -> IO String
lettura filename = do
    res <- readFile filename
    case  (parse (firstparse) (filter (/='\n') res) ) of
                        [] -> return ("Errore di parsing")
                        (parsed,""):xs -> case costraint 0 (ContextInference []) parsed of
                                (_,costraints,_) -> if (unify costraints)
                                    then return(show(reduceStar parsed (Memory [])))
                                    else return("Errore di tipo")
                        (parsed,remaining):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))
