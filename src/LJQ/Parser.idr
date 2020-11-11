module LJQ.Parser

import Data.String.Parser
import Data.String.Parser.Expression
import Parse
import LJQ.Ty

%default covering

-- raw terms

mutual
  public export
  data Val = Lam String Neu
           | Emb NeuV

  public export
  data NeuV = Var String
            | Cut Val Ty

  public export
  data Neu = V NeuV
           | GApp String String Val Neu
           | Let String NeuV Neu

-- type parsing

table : OperatorTable Ty
table = [ [ Infix (token "->" $> Imp ) AssocRight ] ]

mutual
  base : Parser Ty
  base = lexeme ((char '1' $> A) <|> (parens ty))
         <?> "type expression"

  ty : Parser Ty
  ty = buildExpressionParser Ty table base

-- term parsing

name : Parser String
name = takeWhile1 isLower

var : Parser NeuV
var = Var <$> name

mutual
  cut : Parser NeuV
  cut = (uncurry Cut) <$>
        (parens [| (lexeme val, token ":" *> ty) |])

  export
  neuV : Parser NeuV
  neuV = choice [var, cut]

  gapp : Parser Neu
  gapp = (\(x,f,v,n) => GApp x f v n) <$>
         [| (,,,) (token "LETF" *> lexeme name <* token "=")
                  (lexeme name)
                  (lexeme val <* token "IN")
                  (lexeme neu) |]

  lett : Parser Neu
  lett = (\(x,nv,n) => Let x nv n) <$>
         [| (,,) (token "LET" *> lexeme name <* token "=")
                 (lexeme neuV <* token "IN")
                 (lexeme neu) |]

  export
  neu : Parser Neu
  neu = choice [ V <$> neuV
               , gapp
               , lett ]

  lam : Parser Val
  lam = (uncurry Lam) <$>
        [| (token "\\" *> lexeme name, token "." *> neu) |]

  emb : Parser Val
  emb = Emb <$> neuV

  val : Parser Val
  val = choice [ lam, emb ]

-- "LET f = (\\x.x : (1->1)->(1->1)) IN LETF t = f \\x.x IN t"
-- "LET f = (\\x.x : ((1->1)->(1->1))->((1->1)->(1->1))) IN LETF g = f \\x.x IN LETF t = g \\x.x IN t"
-- "LET f = (\\x.x : (1->1)->(1->1)) IN LETF g = f \\x.x IN LET h = (\\x.x : (1->1)->(1->1)) IN LETF t = h g IN t"