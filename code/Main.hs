import Text.Parsec
import Control.Applicative hiding ((<|>), many)
import System.Environment
import qualified CEM
import System.Process

data Failure = ParseFailure ParseError
             | FreeVarFailure Var

compile :: String -> Either Failure ([CEM.BasicBlock], [CEM.BasicBlock])
compile source = do
  expr <- parseExpr source
  dbexpr <- deBruijn expr
  let is = CEM.cse $ CEM.compileProgram dbexpr
  let ds = CEM.cse $ CEM.assembleData dbexpr
  return (is, ds)

type Var = String
data Expr = Lam Var Expr
          | Var Var 
          | App Expr Expr

deBruijn :: Expr -> Either Failure CEM.ClosedTerm
deBruijn e = db' [] e where
  db' :: [(String, CEM.Fin n)] -> Expr -> Either Failure (CEM.Term n)
  db' ls (Lam x t)   = CEM.Lam <$> db' ((x,CEM.FZ):map (fmap CEM.FS) ls) t
  db' ls (App t1 t2) = CEM.App <$> (db' ls t1) <*> (db' ls t2)
  db' ls (Var v) = case lookup v ls of
    Nothing -> Left $ FreeVarFailure v 
    Just ind -> Right $ CEM.Var ind

parseExpr :: String -> Either Failure Expr 
parseExpr s = either (Left . ParseFailure) Right $ parse term "" s where
  term :: Parsec String () Expr
  term =  Lam <$> ((char 'λ' <|> char '\\') *> var <* char '.') <^> term
      <|> Var <$> var
      <|> char '(' ^> (foldl1 App <$> many1 (spaces *> term <* spaces)) <^ char ')'
      <|> char '{' ^> (lets <$> many (spaces *> binding <* spaces) <^> (char '}' ^> term))
          where lets = flip $ foldr ($) 
                binding = mylet <$> var <^> (char '=' ^> term)
                mylet var term body = App (Lam var body) term
                var = many1 letter
                a <^> b = a <* spaces <*> b
                a <^ b = a <* (spaces >> b) 
                a ^> b = (a >> spaces) *> b
                infixl 4 <^>

runCompiler :: String -> IO ()
runCompiler source = case compile source of
  Left (ParseFailure p) -> print p
  Left (FreeVarFailure v) -> putStrLn $ "unbound variable: " ++ v
  Right (bs,ds) -> assemble bs ds

assemble :: [CEM.BasicBlock] -> [CEM.BasicBlock] -> IO ()
assemble bbs ds = do
  writeFile "prog.s" $ preamble ++ concatMap printBB bbs ++ ".data\n" ++ concatMap printBB ds
  callCommand "as prog.s -o prog.o"
  callCommand "ld prog.o -o prog"
  where
    printBB (CEM.BB label instrs) = unlines $ lab ++ map ("\t" ++) instrs where
      lab = if label == "" then [] else [label ++ ":"]
    preamble = unlines [ ".text"
                       , ".global _start"
                       , "_start:"
                       , "  movq $0, %rdi"
                       , "  movq $8000000, %rsi"
                       , "  movq $255, %rdx"
                       , "  movq $0x22, %r10"
                       , "  movq $-1, %r8"
                       , "  movq $0, %r9"
                       , "  movq $9, %rax"
                       , "  syscall"
                       , "  movq %rax, %rbx"
                       , "  movq %rsp, %rbp" ]

main :: IO ()
main = do
  args <- getArgs
  progname <- getProgName
  case args of 
    [filename] -> readFile filename >>= runCompiler
    _ -> putStrLn $ "usage: " ++ progname ++ " <filename>"
   
