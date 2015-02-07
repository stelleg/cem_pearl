import Text.Parsec
import Control.Applicative hiding ((<|>))
import System.Environment
import qualified CEM
import System.Process

data Failure = ParseFailure ParseError
             | FreeVarFailure Var

compile :: String -> Either Failure [CEM.BasicBlock]
compile source = do
  expr <- parseExpr source
  dbexpr <- deBruijn expr
  return $ CEM.compile dbexpr

type Var = String
data Expr = Lam Var Expr
          | Var Var 
          | App Expr Expr

deBruijn :: Expr -> Either Failure CEM.Expr
deBruijn e = db' [] e where
  db' ls (Lam x t)   = CEM.Lam <$> db' ((x,0):map (fmap succ) ls) t
  db' ls (App t1 t2) = CEM.App <$> (db' ls t1) <*> (db' ls t2)
  db' ls (Var v) = case lookup v ls of
    Nothing -> Left $ FreeVarFailure v 
    Just ind -> Right $ CEM.Var ind

parseExpr :: String -> Either Failure Expr 
parseExpr s = either (Left . ParseFailure) Right $ parse term "" s where
  term :: Parsec String () Expr
  term =  Lam <$> (char 'λ' *> var <* char '.') <^> term
      <|> Var <$> var
      <|> App <$> (char '(' *> term) <^> (term <* char ')')
          where var = many1 letter
                a <^> b = a <* spaces <*> b
                infixl 4 <^>

runCompiler :: String -> IO ()
runCompiler source = case compile source of
  Left (ParseFailure p) -> print p
  Left (FreeVarFailure v) -> putStrLn $ "unbound variable: " ++ v
  Right bbs -> assemble bbs

assemble :: [CEM.BasicBlock] -> IO ()
assemble bbs = do
  writeFile "prog.s" $ preamble ++ concatMap printBB bbs 
  callCommand "as prog.s -o prog.o"
  callCommand "ld prog.o -o prog"
  where
    printBB (label, instrs) = unlines $ [label ++ ":"] ++ map ("\t" ++) instrs 
    preamble = unlines [ ".text"
                       , ".global _start"
                       , "_start:"
                       , "  movq $0, %rdi"
                       , "  movq $1000000, %rsi"
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
   
