module Parser

where
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM)
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp

--prog = stmt (';' prog)?
--stmt = var ':=' exp | 'let' var '=' stmt 'in'  prog | 'letrec' var tipo stmt in stmt | exp
--exp =  'while' '(' equals ')' '{' prog '}'  | 'if' exp 'then' '{' stmt '}' 'else' '{' stmt '}' | 'alloc' exp | '*' exp | sum
--sum = succ ('+' sum)* | succ ('-' sum)*
--succ= 'pred' succ | 'iszero' succ | 'succ' succ | values
--var = num
--lambda = '\\' var ':(' tipo ')' '->' stmt
--values = lambda | 'true' | 'false' | NUM | var | '(' stmt ')' | var stmt | (lambda) stmt

--type DictionaryVariables = [(String,Int)]

parse :: Parser a -> String -> [(a, String,[(String,Int)])]
parse p s = parser p s []

parser :: Parser a -> String -> [(String,Int)] -> [(a, String,[(String,Int)])]
parser (Parser s) stringa dict = s stringa dict

instance Functor Parser where
    fmap = liftM

instance Applicative Parser where
    pure a = Parser (\stringa dict-> [(a,stringa,dict)])
    (<*>) = ap

instance Monad Parser where
    return = pure
    Parser x >>= f = Parser (\string dict-> concat (map (\(a,b,c) -> parser (f a) b c) (parser (Parser x) string dict)))
 -- Parser c >>= f =  Parser (\stringa -> concat( map (\(Parser s,rimanente) -> s rimanente) (map (\(parsato,rimanente) -> (f parsato,rimanente)) (c stringa))))

failure :: Parser a
failure = Parser (\_ _-> [])

item :: Parser Char
item = Parser(\x dict-> if x == [] then [] else [((head x),(tail x),dict)])

(+++) :: Parser a -> Parser a -> Parser a
p1+++p2 = Parser (\x dict-> case parser p1 x dict of
                          [] -> parser p2 x dict
                          x  -> x)
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
    []   ->  return []
    x:xs -> do {c <- (char x);res <- string xs; return (c:res)}


many,many1 :: Parser a -> Parser [a]
many p = many1 p+++return []

many1 p = do
   res <- p
   not_consumed <- many p
   return (res:not_consumed)

space :: Parser String
space = many (sat isSpace)

symbol :: String -> Parser String
symbol stringa = do
   space
   res <- string stringa
   space
   return res

parenthesisparser :: Parser Exp
parenthesisparser = do
    symbol "("
    arg <- stmtparse
    symbol ")"
    return arg

ifParse :: Parser Exp
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

parseNUM :: Parser Exp
parseNUM = do
     space
     num <- (many1(digit))+++failure
     space
     if num /= [] then let x = (read num :: Int) in return (Num x) else failure


predParse :: Parser Exp
predParse = do
    symbol "pred"
    t <- expparse
    return (Pred t)

succParse :: Parser Exp
succParse = do
    op <- symbol "succ"+++symbol "iszero"+++symbol "pred"+++return []
    case op of
        "succ"   -> do{t <- succParse;return (Succ t)}
        "iszero" -> do{t <- succParse;return (IsZero t)}
        "pred"   -> do{t <- succParse;return (Pred t)}
        _        -> do{v <- valueparse; return v}

falseParse :: Parser Exp
falseParse = do
    symbol "false"
    return Fls


trueParse :: Parser Exp
trueParse = do
    symbol "true"
    return Tru


iszeroParse :: Parser Exp
iszeroParse = do
    symbol "iszero"
    t <- expparse
    return (IsZero t)

getdict :: Parser [(String,Int)]
getdict = Parser (\string dict -> [(dict,string,dict)] )

vartypeparse :: Parser TypeVariable
vartypeparse = do
        variables <- getdict
        isKey <- keywordParse
        if isKey /= [] then failure else do{
        name <- (many1(letter))+++return [];
        if name /= [] then
            case lookup name variables of
                    (Just x) -> return (VarT x)
                    _ -> Parser(\s dict -> [(VarT (findFresh variables 0),s,dict++[(name,findFresh variables 0)])])

        else failure;}

booltypeparse :: Parser TypeVariable
booltypeparse = do
    symbol "bool"
    return (Type Boolean)

inttypeparse :: Parser TypeVariable
inttypeparse = do
    symbol "int"
    return (Type Integer)

typeparse:: Parser (TypeVariable)
typeparse = do
    space
    tipo <- booltypeparse+++inttypeparse+++vartypeparse+++do{
    symbol "(";
    res <- typeparse;
    symbol ")";
    return res
    }
    isFunction <- symbol "->"+++return []
    if isFunction == "->" then
        do{remaining <- typeparse; return(FunType tipo remaining)}
    else do{return tipo}

applicationParse :: Exp -> Parser Exp
applicationParse acc = do
        res <-  trueParse +++
                falseParse+++
                parseNUM+++
                varparse+++
                do{
                symbol "(";
                lambda <- lambdaparse+++lambdatypedparse;
                symbol ")";
                return lambda};
        space;
        right <- applicationParse (App acc res)+++return (App acc res);
        space;
        return right


appParse :: Parser Exp
appParse = do
    name <- varparse+++do{symbol "(";lambda <- lambdaparse+++lambdatypedparse; symbol ")";return lambda};
    space;
    res <- applicationParse name;
    return res

devar (Variable (Var x)) = Var x

lambdaparse :: Parser Exp
lambdaparse = do
    symbol "\\"
    var <- varparse
    symbol "->"
    t <- stmtparse
    return (LambdaUntyped (devar var) t)

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
    expr <- ifParse+++
            allocparse+++
            derefparse+++
            whileparse+++
            sum_minusparse
    return expr

whileparse :: Parser Exp
whileparse = do
    symbol "while"
    symbol "("
    guard<- sum_minusparse
    symbol ")"
    symbol "{"
    prog <- progparse
    symbol "}"
    return (While guard prog)

sum_minusparse = do
    a<- succParse
    check <- symbol "+"+++symbol "-"+++return []
    if check == [] then return a else
        do{
        b <- sum_minusparse;
        if check == "+"
            then return (Plus a b)
            else return (Minus a b)
        }


fixparse :: Parser Exp
fixparse = do
    symbol "fix"
    t <- succParse
    return (Fix t)

assignparse :: Parser Exp
assignparse = do
    var<- varparse +++do{symbol "(";res<-stmtparse;symbol ")";return res}
    symbol ":="
    t2 <- expparse
    return (Assign var t2)


findFresh :: [(String,Int)] -> Int -> Int
findFresh [] acc = acc
findFresh ((name,x):xs) acc = if acc < x then findFresh xs (x+1) else if acc == x then findFresh xs (acc+1) else findFresh xs acc

keywordParse :: Parser String
keywordParse = symbol "true"+++symbol "false"+++symbol "let"+++symbol "if" +++ symbol "else" +++ symbol "while" +++ symbol "alloc" +++ symbol "in" +++ symbol "letrec" +++  symbol "fix" +++  symbol "pred" +++ symbol "succ" +++  symbol "iszero" +++return []


varparse :: Parser Exp
varparse = do
    variables <- getdict
    isKey <- keywordParse
    if isKey /= [] then failure else do{
    name <- (many1(letter))+++return [];
    if name /= [] then
        case lookup name variables of
                (Just x) -> return (Variable (Var (x)))
                _ -> Parser(\ string dict -> [((Variable (Var (findFresh variables 0))),string,dict++[(name,findFresh variables 0)])])

    else failure;}

letrecparse :: Parser Exp
letrecparse = do
    symbol "letrec"
    x <- varparse
    symbol "="
    t1 <- stmtparse
    symbol "in"
    t2 <- progparse
    return (Let (devar x) (Fix (LambdaUntyped (devar x)  t1 ) ) t2)


stmtparse :: Parser Exp
stmtparse = do
    check <- letparser+++assignparse+++letrecparse+++expparse
    return check

letparser :: Parser Exp
letparser = do
    symbol "let"
    x <- varparse
    symbol "="
    t1 <- progparse
    symbol "in"
    t2 <- progparse
    return (Let (devar x) t1 t2 )

progparse :: Parser Exp
progparse = do
   esp <- stmtparse
   punto_e_virgola <- symbol ";"+++return []
   if punto_e_virgola == ";" then do{t2 <- progparse; return (Seq esp t2) } else return esp

firstparse :: Parser Exp
firstparse = do
    res <- progparse
    return res

lambdatypedparse :: Parser Exp
lambdatypedparse = do
    symbol "\\"
    var <- varparse
    symbol ":"
    symbol "("
    typevar <- typeparse
    symbol ")"
    symbol "->"
    t <- stmtparse
    return (Lambda (devar var) typevar t)

valueparse :: Parser Exp
valueparse = do
    t <- appParse+++lambdatypedparse+++lambdaparse+++trueParse+++falseParse+++parseNUM+++parenthesisparser+++varparse
    return t
