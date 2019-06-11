module Parser

where
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM)
import           Data.Char
import           Data.List
import           Data.Ord
import           Exp

--prog = stmt (';' prog)*
--stmt = 'while' '(' exp ')' '{' prog '}'  | variable ':=' exp | 'let' variable '=' stmt 'in' prog | 'letrec' variable tipo stmt in prog | exp
--exp =  'if' '(' exp ')' '{' prog '}' 'else' '{' prog '}' | 'alloc' exp | '*' exp | sum
--sum = value ('+' sum)* | value ('-' sum)* | 'pred' sum | 'iszero' sum | 'succ' sum | application
--application = value application
--value = '(' lambda ')' | 'true' | 'false' | NUM | variable | '(' stmt ')'
--lambda = lambdatyped | lambdauntyped
--lambdatyped = '\\' variable ':(' tipo ')' '->' exp
--lambdauntyped = '\\' variable '->' stmt

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

progparse :: Parser Exp
progparse = do
  esp <- stmtparse
  punto_e_virgola <- symbol ";"+++return []
  if punto_e_virgola == ";" then do{t2 <- progparse; return (Seq esp t2) } else return esp

stmtparse :: Parser Exp
stmtparse = do
  check <- letparser+++letrecparse+++assignparse+++whileparse+++expparse
  return check

letparser :: Parser Exp
letparser = do
  symbol "let"
  (Variable (Var x)) <- varparse
  symbol "="
  t1 <- stmtparse
  symbol "in"
  t2 <- progparse
  return (Let (Var x) t1 t2 )

letrecparse :: Parser Exp
letrecparse = do
  symbol "letrec"
  (Variable (Var x)) <- varparse
  symbol "="
  t1 <- stmtparse
  symbol "in"
  t2 <- progparse
  return (Let (Var x) (Fix (LambdaUntyped (Var x)  t1 ) ) t2)

assignparse :: Parser Exp
assignparse = do
  var <- varparse +++ do{symbol "(";res<-stmtparse;symbol ")";return res}
  symbol ":="
  t2 <- expparse
  return (Assign var t2)

whileparse :: Parser Exp
whileparse = do
  symbol "while"
  symbol "("
  guard<- expparse
  symbol ")"
  symbol "{"
  prog <- progparse
  symbol "}"
  return (While guard prog)

expparse :: Parser Exp
expparse = do
  expr <- ifParse+++
          allocparse+++
          derefparse+++
          fixparse+++
          sumparse
  return expr

ifParse :: Parser Exp
ifParse = do
  symbol "if"
  symbol "("
  t <- expparse
  symbol ")"
  symbol "{"
  t1 <- progparse
  symbol "}"
  symbol "else"
  symbol "{"
  t2 <- progparse
  symbol "}"
  return (IfThenElse t t1 t2)

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

fixparse :: Parser Exp
fixparse = do
    symbol "fix"
    t <- expparse
    return (Fix t)

sumparse :: Parser Exp
sumparse = do
  op <- symbol "succ"+++symbol "iszero"+++symbol "pred"+++return []
  if op/= [] then case op of
      "succ"   -> do{t <- sumparse;return (Succ t)}
      "iszero" -> do{t <- sumparse;return (IsZero t)}
      "pred"   -> do{t <- sumparse;return (Pred t)}
  else do{
  app <- applicationParse;
  check <- symbol "+"+++symbol "-"+++return [];
  if check == [] then return app else
      case check of
          "+" -> do{b <- sumparse;return (Plus app b)}
          "-" -> do{b <- sumparse;return (Minus app b)}
  }

applicationParse :: Parser Exp
applicationParse = do
     res <- appParse+++valueparse
     return res

appParse :: Parser Exp
appParse = do
        name <- valueparse
        space;
        res <- leftAssociativeApp name;
        return res


leftAssociativeApp :: Exp -> Parser Exp
leftAssociativeApp acc = do
      res <-  valueparse
      space;
      right <- leftAssociativeApp (App acc res)+++return (App acc res);
      space;
      return right

valueparse :: Parser Exp
valueparse = do
  t <- lambdatypedparse+++lambdaparse+++do{symbol "true";return Tru}+++do{symbol "false";return Fls}+++parseNUM+++parenthesisparser+++varparse
  return t

parenthesisparser :: Parser Exp
parenthesisparser = do
    symbol "("
    arg <- stmtparse
    symbol ")"
    return arg

parseNUM :: Parser Exp
parseNUM = do
     space
     num <- (many1(digit))+++failure
     space
     if num /= [] then let x = (read num :: Int) in return (Num x) else failure

getdict :: Parser [(String,Int)]
getdict = Parser (\string dict -> [(dict,string,dict)] )

vartypeparse :: Parser TypeVariable
vartypeparse = do
        variables <- getdict
        isKey <- keywordParse
        if isKey /= [] then failure else do{
        name <- (many1(letter))+++return [];
        space;
        if name /= [] then
            case lookup name variables of
                    (Just x) -> return (VarT x)
                    _ -> Parser(\s dict -> [(VarT (findFresh variables 0),s,dict++[(name,findFresh variables 0)])])

        else failure;}

varparse :: Parser Exp
varparse = do
    variables <- getdict
    isKey <- keywordParse
    if isKey /= [] then failure else do{
    name <- (many1(letter))+++return [];
    space;
    if name /= [] then
        case lookup name variables of
                (Just x) -> return (Variable (Var (x)))
                _ -> Parser(\ string dict -> [((Variable (Var (findFresh variables 0))),string,dict++[(name,findFresh variables 0)])])

    else failure;}

keywordParse :: Parser String
keywordParse = symbol "true"+++symbol "false"+++symbol "let"+++symbol "if" +++ symbol "else" +++ symbol "while" +++ symbol "alloc" +++ symbol "in" +++ symbol "letrec" +++  symbol "fix" +++  symbol "pred" +++ symbol "succ" +++  symbol "iszero" +++return []

typeparse:: Parser (TypeVariable)
typeparse = do
    space
    tipo <- do{symbol "bool";return (Type Boolean)}+++do{symbol "int";return (Type Integer)}+++vartypeparse+++do{
    symbol "(";
    res <- typeparse;
    symbol ")";
    return res
    }
    isFunction <- symbol "->"+++return []
    if isFunction == "->" then
        do{remaining <- typeparse; return(FunType tipo remaining)}
        else do{return tipo}

lambdaparse :: Parser Exp
lambdaparse = do
    symbol "\\"
    (Variable (Var var)) <- varparse
    symbol "->"
    t <- stmtparse
    return (LambdaUntyped (Var var) t)


findFresh :: [(String,Int)] -> Int -> Int
findFresh [] acc = acc
findFresh ((name,x):xs) acc = if acc < x then findFresh xs (x+1) else if acc == x then findFresh xs (acc+1) else findFresh xs acc

lambdatypedparse :: Parser Exp
lambdatypedparse = do
    symbol "\\"
    (Variable (Var var)) <- varparse
    symbol ":"
    symbol "("
    typevar <- typeparse
    symbol ")"
    symbol "->"
    t <- stmtparse
    return (Lambda (Var var) typevar t)
