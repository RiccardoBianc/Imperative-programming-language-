module Parser

where
import Exp
import Data.Char
import Data.List
import Data.Ord
import Control.Applicative (Applicative(..))
import Control.Monad       (liftM, ap)

--prog = stmt (';' prog)?
--stmt = var ':=' exp | 'let' var '=' stmt 'in'  prog | 'letrec' var tipo stmt in stmt | exp
--exp =  'while' '(' equals ')' '{' prog '}'  | 'if' exp 'then' '{' stmt '}' 'else' '{' stmt '}' | 'alloc' exp | '*' exp | equals
--equals = sum '==' 'if' exp 'then' stmt  'else' stmt | sum '==' '*' exp | sum '==' sum | 'fix' sum | sum
--sum = succ ('+' sum)* | succ ('-' sum)*
--succ= 'pred' succ | 'iszero' succ | 'succ' succ | values
--var = num
--lambda = '\\' var ':(' tipo ')' '->' stmt
--values = lambda | 'true' | 'false' | NUM | var | '(' stmt ')' | var stmt | (lambda) stmt

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

--parenthesisparser :: [(String,Int)] -> Parser Exp
parenthesisparser variables = do
    symbol "("
    (arg,variables') <- stmtparse variables
    symbol ")"
    return (arg,variables')

--ifParse :: [(String,Int)] -> Parser Exp
ifParse variables = do
    symbol "if"
    symbol "("
    (t,variables') <- expparse variables
    symbol ")"
    symbol "{"
    (t1,variables'') <- stmtparse variables'
    symbol "}"
    symbol "else"
    symbol "{"
    (t2,variables''') <- stmtparse variables''
    symbol "}"
    return ((IfThenElse t t1 t2),variables''')

--parseNUM :: [(String,Int)] -> Parser Exp
parseNUM variables = do
     space
     num <- (many(digit))+++failure
     space
     if num /= [] then let x = (read num :: Int) in return (Num x,variables) else failure


--predParse :: [(String,Int)] -> Parser Exp
predParse variables = do
    symbol "pred"
    (t,variables') <- expparse variables
    return ((Pred t),variables')

succParse :: [(String,Int)] -> Parser (Exp,[(String,Int)])
succParse variables = do
    op <- symbol "succ"+++symbol "iszero"+++symbol "pred"+++return []
    case op of
        "succ" -> do{(t,variables') <- succParse variables;return ((Succ t),variables')}
        "iszero" -> do{(t,variables') <- succParse variables;return((IsZero t),variables')}
        "pred" -> do{(t,variables') <- succParse variables;return ((Pred t),variables')}
        _ -> do{(v,variable') <- valueparse variables; return (v,variable')}

falseParse variables = do
    symbol "false"
    return (Fls,variables)

trueParse variables = do
    symbol "true"
    return (Tru,variables)

isparseNUM variables = do
    symbol "iszero"
    (t,variables') <- expparse variables
    return ((IsZero t),variables')

typeparse:: Parser Types
typeparse = do
    space
    tipo <- string "bool"+++string "int"
    isFunction <- symbol "->"+++return []
    if isFunction == "->" then
        do{remaining <- typeparse; if tipo=="bool" then return (Fun Boolean remaining) else return (Fun Integer remaining) }
    else (if tipo == "bool" then do{return Boolean} else do{return Integer})

applicationParse :: [(String,Int)] -> Exp -> Parser (Exp,[(String,Int)])
applicationParse variables acc = do
        (res,variables') <-  trueParse variables+++
                             falseParse variables+++
                             parseNUM variables+++
                             varparse variables+++do{symbol "(";(lambda,variables') <- stmtparse variables; symbol ")";return (lambda,variables')};
        right <- applicationParse variables' (App acc res)+++return(App acc res,variables');
        return right


appParse :: [(String,Int)] -> Parser (Exp,[(String,Int)])
appParse variables = do
    (name,variables') <- varparse variables+++do{symbol "(";(lambda,variables') <- stmtparse variables; symbol ")";return (lambda,variables')};
    (res,variables'') <- applicationParse variables' name
    return (res,variables'')

devar (Variable (Var x)) = Var x

-- lambdaparse :: [(String,Int)] -> Parser Exp
lambdaparse variables = do
    symbol "\\"
    (var,variables') <- varparse variables
    symbol  ":"
    symbol "("
    tipo<- typeparse
    symbol ")"
    symbol "->"
    (t,variables'') <- stmtparse variables'
    return ((Lambda (devar var) (tipo) t),variables'')

-- allocparse :: [(String,Int)] -> Parser Exp
allocparse variables = do
    symbol "alloc"
    (t,variables') <- expparse variables
    return ((Ref t),variables')

-- derefparse :: [(String,Int)] -> Parser Exp
derefparse variables = do
    symbol "*"
    (t,variables') <- expparse variables
    return ((Deref t),variables')

-- expparse :: [(String,Int)] -> Parser Exp
expparse variables = do
    (expr,variables') <- ifParse variables +++
            allocparse variables +++
            derefparse variables +++
            whileparse variables +++
            equalparse variables
    return (expr,variables')

-- whileparse :: [(String,Int)] -> Parser Exp
whileparse variables = do
    symbol "while"
    symbol "("
    (guard,variables') <- equalparse variables
    symbol ")"
    symbol "{"
    (prog,variables'') <- progparse variables'
    symbol "}"
    return ((While guard prog),variables'')

-- checkparse :: Parser Bool
checkparse = Parser(\x ->
                    case x of
                        [] -> [(True,x)]
                        _ -> [])

sum_minusparse variables = do
    (a,variables') <- succParse variables
    check <- symbol "+"+++symbol "-"+++return []
    if check == [] then return (a,variables') else
        do{
        (b,variables'') <- sum_minusparse variables';
        if check == "+"
            then return ((Plus a b),variables'')
            else return ((Minus a b),variables'')
        }


equalparse :: [(String,Int)] -> Parser (Exp,[(String,Int)])
equalparse variables = do
    (t1,variables') <- fixparse variables+++sum_minusparse variables
    check <- symbol "=="+++return []
    if check == [] then return (t1,variables') else
        do{
        (t2,variables'') <- ifParse variables'+++allocparse variables'+++derefparse variables'+++sum_minusparse variables';
        return ((EqualsInt t1 t2),variables'')}

-- fixparse :: [(String,Int)] -> Parser Exp
fixparse variables = do
    symbol "fix"
    (t,variables') <- succParse variables
    return ((Fix t),variables')

-- assignparse :: [(String,Int)] -> Parser Exp
assignparse variables = do
    (var,variables') <- varparse variables
    symbol ":="
    (t2,variables'') <- expparse variables'
    return ((Assign var t2),variables'')


findFresh :: [(String,Int)] -> Int -> Int
findFresh [] acc = acc
findFresh ((name,x):xs) acc = if acc < x then findFresh xs (x+1) else if acc == x then findFresh xs (acc+1) else findFresh xs acc

varparse :: [(String,Int)] -> Parser (Exp,[(String,Int)])
varparse variables = do
    name <- (many(letter))+++failure
    if name /= [] then
        case lookup name variables of
                (Just x) -> return ((Variable (Var (x))),variables)
                _ -> return ((Variable (Var (findFresh variables 0))),variables++[(name,findFresh variables 0)])

    else failure

-- letrecparse :: [(String,Int)] -> Parser Exp
letrecparse variables = do
    symbol "letrec"
    (x,variables') <- varparse variables
    symbol ":"
    symbol "("
    tipo <- typeparse
    symbol ")"
    symbol "="
    (t1,variables'') <- stmtparse variables'
    symbol "in"
    (t2,variables''') <- stmtparse variables''
    return ((Let (devar x) (Fix (Lambda (devar x) tipo t1 ) ) t2),variables'')


-- stmtparse :: [(String,Int)] -> Parser Exp
stmtparse variables = do
    (check,variables') <- assignparse variables+++letparser variables+++letrecparse variables+++expparse variables
    return (check,variables')

-- letparser :: [(String,Int)] -> Parser Exp
letparser variables = do
    symbol "let"
    (x,variables') <- varparse variables
    symbol "="
    (t1,variables'') <- progparse variables'
    symbol "in"
    (t2,variables''') <- progparse variables''
    return ((Let (devar x) t1 t2 ),variables''')

-- progparse :: [(String,Int)] -> Parser Exp
progparse variables = do
   (esp,variables') <- stmtparse variables
   punto_e_virgola <- symbol ";"+++return []
   if punto_e_virgola == ";" then do{(t2,variables'') <- progparse variables'; return ((Seq esp t2),variables'') } else return (esp,variables')

-- firstparse :: [(String,Int)] -> Parser Exp
firstparse = do
    (res,variables') <- progparse []
    checkparse
    return res

-- valueparse :: [(String,Int)] -> Parser Exp
valueparse variables = do
    (t,variables') <- appParse variables+++lambdaparse variables+++trueParse variables+++falseParse variables+++parseNUM variables+++parenthesisparser variables+++varparse variables
    return (t,variables')
