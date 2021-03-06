module ProdSum.Parser

import Control.Monad.Identity
import Data.String.Parser
import Data.String.Parser.Expression
import Parse
import ProdSum.Ty

%default covering

-- raw terms

mutual
  public export
  data Val = Lam  String Val
           | Pair Val Val
           | Inl  Val
           | Inr  Val
           | Case Neu String Val String Val
           | Emb  Neu

  public export
  data Neu = Var String
           | App Neu Val
           | Fst Neu
           | Snd Neu
           | Cut Val Ty

-- type parsing

table : OperatorTable Ty
table =
  [ [ Infix (token "*"  $> Prod) AssocLeft  ]
  , [ Infix (token "+"  $> Sum ) AssocLeft  ]
  , [ Infix (token "->" $> Imp ) AssocRight ]
  ]

mutual
  base : Parser Ty
  base = lexeme ((char '1' $> A) <|> (parens ty))
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

  fst : Parser Neu
  fst = Fst <$> (token "_1" *> neu)

  snd : Parser Neu
  snd = Snd <$> (token "_2" *> neu)

  arg : Parser Val
  arg = (Emb <$> var) <|> parens val

  export
  neu : Parser Neu
  neu = hchainl (choice [var, cut, fst, snd, parens neu])
                (spaces1 $> App)
                arg

  lam : Parser Val
  lam = (uncurry Lam) <$>
        [| (token "\\" *> lexeme name, token "." *> val) |]

  pair : Parser Val
  pair = (uncurry Pair) <$>
         (char '(' *> [| (lexeme val, token "," *> val) |] <* char ')')

  inl : Parser Val
  inl = Inl <$> (token "_L" *> val)

  inr : Parser Val
  inr = Inr <$> (token "_R" *> val)

  cas : Parser Val
  cas = (\(n,x,l,y,r) => Case n x l y r) <$>
        [| (,,,,) (token "CASE" *> lexeme neu <* token "OF")
                  (token "L" *> lexeme name <* token ".")
                  (lexeme val <* token "|")
                  (token "R" *> lexeme name <* token ".")
                  (lexeme val) |]

  emb : Parser Val
  emb = Emb <$> neu

  val : Parser Val
  val = choice [ lam, pair, inl, inr, cas, emb, parens val ]