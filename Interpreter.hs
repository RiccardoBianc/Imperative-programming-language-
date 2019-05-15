module Imperative

where
import Exp
import Parser
import Typechecker
import Reducer
import System.IO
import Control.Monad

shell :: IO String
shell = do
    putStr "Inserire comando\n"
    command <- getLine
    if command == ":file"
        then do{putStr "Inserire path"; path <- getLine; lettura path;}
        else if command == ":bash"
            then do{putStr "Inserire programma";interpreter} else
                if command == ":exit" then do{return "fuori"} else shell

interpreter :: IO String
interpreter = do
                program <- getLine
                case  (parse progparse program) of
                    [] -> return "Errore di parsing"
                    (parsed,""):xs -> case typeof parsed (Context []) (AssignType []) of
                                        Just _ -> return(show(reduceStar parsed (Memory [])))
                                        _ -> return "Errore di tipo"
                    (parsed,remaining):xs -> return ("Parsing non terminato   "++remaining++"-----"++(show parsed))

lettura :: String -> IO String
lettura filename = do
    res <- readFile filename
    let program = filter (/='\n') res
    case  (parse progparse program) of
                        [] -> return ("Errore di parsing")
                        (parsed,""):xs -> case typeof parsed (Context []) (AssignType []) of
                                            Just _ -> return(show(reduceStar parsed (Memory [])))
                                            _ -> return("Errore di tipo")
                        (parsed,remaining):xs -> return("Parsing non terminato"++remaining++"-----"++(show parsed))
