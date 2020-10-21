module ProdLet.Parser

import Control.Monad.Identity
import Data.String.Parser
import Data.String.Parser.Expression
import Parse
import ProdLet.Ty

%default covering

-- raw terms

mutual
  public export
  data Val = Lam  String Val
           | TT
           | Pair Val Val
           | LetP Neu String String Val
           | Emb  Neu

  public export
  data Neu = Var String
           | App Neu Val
           | Cut Val Ty

-- type parsing

table : OperatorTable Ty
table =
  [ [ Infix (token "*"  $> Prod) AssocLeft  ]
  , [ Infix (token "->" $> Imp ) AssocRight ]
  ]

mutual
  base : Parser Ty
  base = lexeme ((char '1' $> U) <|> (parens ty))
         <?> "type expression"

  ty : Parser Ty
  ty = buildExpressionParser Ty table base

-- term parsing

name : Parser String
name = takeWhile1 isLower

var : Parser Neu
var = Var <$> name

mutual
  cut : Parser Neu
  cut = (uncurry Cut) <$>
        (parens [| (lexeme val, token ":" *> ty) |])

  arg : Parser Val
  arg = (Emb <$> var) <|> parens val

  export
  neu : Parser Neu
  neu = hchainl (choice [var, cut, parens neu])
                (spaces1 $> App)
                arg

  lam : Parser Val
  lam = (uncurry Lam) <$>
        [| (token "\\" *> lexeme name, token "." *> val) |]

  tt : Parser Val
  tt = TT <$ (token "TT")

  pair : Parser Val
  pair = (uncurry Pair) <$>
         (char '(' *> [| (lexeme val, token "," *> val) |] <* char ')')

  letp : Parser Val
  letp = (\(x,y,n,v) => LetP n x y v) <$>
         [| (,,,) (token "LETP" *> token "(" *> lexeme name)
                  (token "," *> lexeme name)
                  (token ")" *> lexeme neu)
                  (token "IN" *> lexeme val) |]

  emb : Parser Val
  emb = Emb <$> neu

  val : Parser Val
  val = choice [lam, tt, pair, letp, emb, parens val]