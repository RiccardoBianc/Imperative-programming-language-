module Parser

where
import Exp
import Data.Char
import Data.List
import Data.Ord
import Control.Applicative (Applicative(..))
import Control.Monad       (liftM, ap)

--prog = stmt (';' prog)?
--stmt = var ':=' exp | 'let' var '=' stmt 'in' '{' prog '}' | 'letrec' var tipo stmt in stmt  |exp
--exp =  'if' exp 'then' stmt 'else' '{' stmt '}' | 'alloc' exp | '*' exp | equals
--equals = app '==' 'if' exp 'then' stmt  'else' stmt | app '==' '*' exp | app '==' app | 'fix' app | app
--app = '(' stmt ')' '(' stmt ')' | succ
--succ= 'pred' succ | 'iszero' succ | 'succ' succ | values
--var = num
--values = '\\' var ':(' tipo ')' '->' stmt | 'true' | 'false' | '0' | var

data Parser a = Parser (String -> [(a,String)])

parse :: Parser a -> String -> [(a, String)]
parse (Parser s) stringa = s stringa

instance Functor Parser where
    fmap = liftM

instance Applicative Parser where
    pure a = Parser (\stringa -> [(a,stringa)])
    (<*>) = ap

instance Monad Parser where
    return = pure
    Parser x >>= f = Parser (\string -> concat (map (\(a,b) -> parse (f a) b ) (parse (Parser x) string)))
 -- Parser c >>= f =  Parser (\stringa -> concat( map (\(Parser s,rimanente) -> s rimanente) (map (\(parsato,rimanente) -> (f parsato,rimanente)) (c stringa))))

failure :: Parser a
failure = Parser (\_ -> [])

item :: Parser Char
item = Parser(\x -> if x == [] then [] else [((head x),(tail x))])

(+++) :: Parser a -> Parser a -> Parser a
p1+++p2 = Parser (\x -> case parse p1 x of
                          [] -> parse p2 x
                          x -> x)

myparser :: Parser (Char, Char)
myparser = do
   c1 <- item
   item
   c2 <- item
   return (c1, c2)

sat :: (Char -> Bool) -> Parser Char
sat p = do
   c <- item
   if p c then return c else failure

digit = sat isDigit

upper :: Parser Char
upper = sat isUpper

lower = sat isLower

letter = sat isLetter

char :: Char -> Parser Char
char c = sat (==c)

string :: String -> Parser String
string stringa =
   case stringa of
    [] ->  return []
    x:xs -> do {c <- (char x);res <- string xs; return (c:res)}


many,many1 :: Parser a -> Parser [a]
many p = many1 p+++return []

many1 p = do
   res <- p
   not_consumed <- many p
   return (res:not_consumed)

space = many (sat isSpace)

symbol :: String -> Parser String
symbol stringa = do
   space
   res <- string stringa
   space
   return res

ifParse = do
    symbol "if"
    symbol "("
    t <- expparse
    symbol ")"
    symbol "{"
    t1 <- stmtparse
    symbol "}"
    symbol "else"
    symbol "{"
    t2 <- stmtparse
    symbol "}"
    return (IfThenElse t t1 t2)

zeroParse = do
    symbol "0"
    return Zero

predParse = do
    symbol "pred"
    t <- expparse
    return (Pred t)

succParse :: Parser Exp
succParse = do
    op <- symbol "succ"+++symbol "iszero"+++symbol "pred"+++return []
    case op of
        "succ" -> do{t <- succParse;return (Succ t)}
        "iszero" -> do{t <- succParse;return(IsZero t)}
        "pred" -> do{t <- succParse;return (Pred t)}
        _ -> do{v <- valueparse; return v}

falseParse = do
    symbol "false"
    return Fls

trueParse = do
    symbol "true"
    return Tru

iszeroparse = do
    symbol "iszero"
    t <- expparse
    return (IsZero t)

typeparse :: Parser Types
typeparse = do
    space
    tipo <- string "bool"+++string "int"
    isFunction <- symbol "->"+++symbol ""
    if isFunction == "->" then
        do{remaining <- typeparse; if tipo=="bool" then return (Fun Boolean remaining) else return (Fun Integer remaining) }
    else (if tipo == "bool" then do{return Boolean} else do{return Integer})

appParse :: Parser Exp
appParse = do
    check <- symbol "("+++return []
    if check == "(" then do{
    t1 <- stmtparse;
    symbol ")";
    symbol "(";
    t2 <- stmtparse;
    symbol ")";
    return (App t1 t2)}
    else do{suc <- succParse;return suc}

devar (Variable (Var x)) = Var x

lambdaparse :: Parser Exp
lambdaparse = do
    symbol "\\"
    var <- varparse
    symbol  ":"
    symbol "("
    tipo <- typeparse
    symbol ")"
    symbol "->"
    t <- stmtparse
    return (Lambda (devar var) (tipo) t)

allocparse :: Parser Exp
allocparse = do
    symbol "alloc"
    t <- expparse
    return (Ref t)

derefparse :: Parser Exp
derefparse = do
    symbol "*"
    t <- expparse
    return (Deref t)

expparse :: Parser Exp
expparse = do
    expr <- ifParse +++
            allocparse +++
            derefparse +++
            equalparse
    return expr

checkparse :: Parser Bool
checkparse = Parser(\x ->
                    case x of
                        [] -> [(True,x)]
                        _ -> [])

equalparse :: Parser Exp
equalparse = do
    t1 <- fixparse+++appParse
    check <- symbol "=="+++return []
    if check == [] then return t1 else do{t2 <- ifParse+++allocparse+++derefparse+++appParse;return (EqualsInt t1 t2)}

fixparse :: Parser Exp
fixparse = do
    symbol "fix"
    t <- appParse
    return (Fix t)

assignparse :: Parser Exp
assignparse = do
    var <- varparse
    symbol ":="
    t2 <- expparse
    return (Assign var t2)

varparse :: Parser Exp
varparse = do
    num <- (many(digit))+++failure
    if num /= [] then let x = (read num :: Int) in return (Variable (Var (x))) else failure

letrecparse :: Parser Exp
letrecparse = do
    symbol "letrec"
    x <- varparse
    symbol ":"
    symbol "("
    tipo <- typeparse
    symbol ")"
    symbol "="
    t1 <- stmtparse
    symbol "in"
    t2 <- stmtparse
    return (Let (devar x) (Fix (Lambda (devar x) tipo t1 ) ) t2)


stmtparse :: Parser Exp
stmtparse = do
    check <- assignparse+++letparser+++letrecparse+++expparse
    return check

letparser :: Parser Exp
letparser = do
    symbol "let"
    num <- many(digit)
    let x = read num :: Int
    symbol "="
    t1 <- progparse
    symbol "in"
    t2 <- progparse
    return (Let (Var x) t1 t2 )

progparse :: Parser Exp
progparse = do
   esp <- stmtparse
   punto_e_virgola <- symbol ";"+++return []
   if punto_e_virgola == ";" then do{t2 <- progparse; return (Seq esp t2) } else return esp

firstparse :: Parser Exp
firstparse = do
    res <- progparse
    checkparse
    return res

valueparse :: Parser Exp
valueparse = do
    t <- lambdaparse+++trueParse+++falseParse+++zeroParse+++varparse
    return t
