module Parser where

import AST
import Text.Parsec
import Text.Parsec.Language (emptyDef)
import Text.Parsec.String (Parser)
import Text.Parsec.Token qualified as Token

import Data.List.NonEmpty qualified as NE

languageDef :: Token.LanguageDef ()
languageDef =
    emptyDef
        { Token.identStart = letter
        , Token.identLetter = alphaNum
        , Token.reservedNames =
            [ "let"
            , "ref"
            , "if"
            , "else"
            , "true"
            , "false"
            , "H"
            , "L"
            , "while"
            , "for"
            , "in"
            , "to"
            ]
        , Token.commentLine = "--"
        }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDef

identifier :: Parser String
identifier = Token.identifier lexer

-- label :: Parser String
-- label = Token.identifier lexer

reserved :: String -> Parser ()
reserved = Token.reserved lexer

parens :: Parser a -> Parser a
parens = Token.parens lexer

angles :: Parser a -> Parser a
angles = Token.angles lexer

braces :: Parser a -> Parser a
braces = Token.braces lexer

integer :: Parser Integer
integer = Token.integer lexer

whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer

semi :: Parser String
semi = Token.semi lexer

comma :: Parser String
comma = Token.comma lexer

colon :: Parser String
colon = Token.colon lexer


parseInput :: String -> Either ParseError Expr
parseInput = parse (whiteSpace >> seqExpressions) ""

seqExpressions :: Parser Expr
seqExpressions = do
    exprs <- expression `sepBy1` semi
    return $ foldr1 Seq exprs

-- Parser for expressions
expression :: Parser Expr
expression =
    whiteSpace
        *> ( try letExpr
                <|> try record
                <|> try assign
                <|> try ifThenElse
                <|> try while
                <|> try for
                <|> try abstraction
                <|> try application
                <|> try binaryOperation
                <|> try reference
                <|> try dereference
                <|> try number
                <|> try boolean
                <|> variable

           )

-- {e_1; e_2; e_3}
-- Expression on the form l_1 : e_1
-- Returns a record, that has the body of a list of tuples 
record :: Parser Expr
record = 
    do
        body <- braces record_fields
        return $ body


-- Returns a list of tuples containing (Label, Expr)
record_fields :: Parser Expr
record_fields = 
    do
        exprs <- assign_record `sepBy1` comma
        return $ Rec (NE.fromList exprs)
        

-- Returns a tuple of a labelIdentifier (string) and the corresponding expression
-- Note it is not possible to explicit assign a security type to a label
assign_record :: Parser (Label, Expr)
assign_record = 
    do
        name <- identifier
        _ <- colon
        expr <- seqExpressions
        return $ (LabelS name, expr)
        
record_field :: Parser Expr
record_field = 
    do 
        record_ <- expression
        _ <- char '.'
        field_name <- identifier
        return $ Rec_Field record_ (LabelS field_name)

number :: Parser Expr
number = N . fromIntegral <$> integer

boolean :: Parser Expr
boolean =
    do
        reserved "true"
        return $ B True
        <|> do
            reserved "false"
            return $ B False

-- Parser for references
reference :: Parser Expr
reference = do
    reserved "ref"
    expr <- parens expression
    return $ Ref expr

dereference :: Parser Expr
dereference = do
    _ <- string "!"
    Deref . V <$> identifier

-- Parser for let expressions
letExpr :: Parser Expr
letExpr = try explicit <|> infer
    where
        explicit = do
            reserved "let"
            name <- identifier
            _ <- char '<'
            level <- try low <|> try high <|> try refLow <|> refHigh
            _ <- char '>'
            _ <- spaces *> char '=' <* spaces
            Let (V name) level <$> expression
        infer = do
            reserved "let"
            name <- identifier
            _ <- spaces *> char '=' <* spaces
            LetInf (V name) <$> expression

variable :: Parser Expr
variable = Var . V <$> identifier

ifThenElse :: Parser Expr
ifThenElse = do
    reserved "if"
    cond <- parens expression
    thenExpr <- braces seqExpressions
    reserved "else"
    elseExpr <- braces seqExpressions
    return $ IfThenElse cond thenExpr elseExpr

while :: Parser Expr
while = do
    reserved "while"
    cond <- parens expression
    body <- braces seqExpressions
    return $ While cond body

for :: Parser Expr
for = do
    reserved "for"
    name <- identifier
    _ <- spaces *> string "in" <* spaces
    start <- expression
    _ <- spaces *> string "to" <* spaces
    end <- expression
    body <- braces seqExpressions
    return $ For (V name) start end body

assign :: Parser Expr
assign = do
    name <- identifier
    _ <- string ":="
    Assign (V name) <$> expression

abstraction :: Parser Expr
abstraction = do
    _ <- char '('
    name <- identifier
    _ <- char '<'
    level <- try low <|> try high <|> try refLow <|> refHigh
    _ <- char '>'
    _ <- char ')'
    _ <- spaces *> string "=>" <* spaces
    body <- braces seqExpressions
    return $ Abs (V name) level body

application :: Parser Expr
application = do
    func <- parens expression <|> variable
    arg <- parens expression
    return $ App func arg

binaryOperation :: Parser Expr
binaryOperation = parens $ do
    left <- expression
    spaces
    op <- binaryOperator
    spaces
    right <- expression
    return $ BO op left right

-- Binary operator parser stays the same
binaryOperator :: Parser BinOper
binaryOperator = 
      (char '+' >> return Add)
  <|> (char '-' >> return Sub)
  <|> (char '*' >> return Mul)
  <|> (char '/' >> return Div)
  <|> (string "==" >> return Eql)


-- cabal run exes -- progs/4.rescript


low :: Parser LevelT
low = LH Low <$ char 'L'

high :: Parser LevelT
high = LH High <$ char 'H'

refLow :: Parser LevelT
refLow = RefLH Low <$ string "RL"

refHigh :: Parser LevelT
refHigh = RefLH High <$ string "RH"
