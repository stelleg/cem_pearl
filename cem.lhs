\documentclass[preprint]{sigplanconf}

\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage{natbib}
\usepackage{graphicx}
\usepackage{tikz}
\usepackage{mathtools}
\usetikzlibrary{chains,fit,shapes,calc}
\usepackage{verbatim}
\usepackage{semantic}
\usepackage{tabu}
\usepackage{amsthm}
\usepackage{mathptmx}
\usepackage{todonotes}

\begin{document}
\title{Lazy Mechanical Evaluation of Expressions}
\subtitle{A Functional (Compiler) Pearl}

\authorinfo{George Stelle}
           {University of New Mexico}
           {stelleg@cs.unm.edu}
\authorinfo{Darko Stefanovic}
           {University of New Mexico}
           {darko@cs.unm.edu}
\authorinfo{Stephen L. Olivier}
           {Sandia National Laboratories}
           {slolivi@sandia.gov}
\authorinfo{Stephanie Forrest}
           {University of New Mexico}
           {forrest@cs.unm.edu}

\maketitle

\begin{abstract}
This paper implements a compiler which compiles lambda calculus directly to x64
assembly code. The compiled code evaluates according to lazy, or call by need
, semantics. The implementation is remarkable primarily for its simplicity: the
entire implementation is contained in this document.

The paper achieves this feat by utilizing a novel abstract machine: the Cactus
Environment Machine (CEM). By using shared environments ensure work is only
performed once (a requirement of lazy evaluation), we acheive an implementation
significantly simpler than any existing implementation of the call by need
lambda calculus we are aware of.
\end{abstract}

\section{Introduction}
The goal of this paper is to present in a easy to understand way, the simplest
compiler of a lazy language we are aware of. To do this, we have written the
document as a literate Haskell file, which the reader may download and follow
along from \hyperref{http://cs.unm.edu/~stelleg/cem.lhs}. 

In true call by need fashion, we start with the type of the function we want,
and build from there as needed.

\begin{code}
import Text.Parsec
import Control.Applicative hiding ((<|>))
import System.Environment

compile :: String -> Either Error String
\end{code}

In words, we want a function from lambda calculus expressions to a list of x64
instructions. We assume the reader has some familiarity with lambda calculus, so
we can go ahead and inhabit the type of \texttt{Expr}. 

For the \texttt{Instr} type, however, we don't want to enumerate the entire
instruction set, for our sanity and yours, so we must wait until we know what
instructions we need. So we put that off, and will revisit the \texttt{Instr}
type when we know what values to inhabit it with.

\section{Input Syntax}
As with any language worth its weight in bits, we start with the lambda
calculus:

\begin{code}
type Var = String

data Expr = Lam Var Expr
          | Var Var
          | App Expr Expr
\end{code}

Because we aren't writing a real language, we also stop with the lambda
calculus.

\section{Evaluation}
We are concerned with evaluating expressions to weak head normal form (WHNF).
WHNF in our context is just a \texttt{Lam}, with a body that is not necessarily
in WHNF. We can say with some certainty that this is what the reader's
functional language of choice does.

Deciding how to 

Now that we have defined our expressions, we take the standard approach of
choosing an evaluation strategy. There are three common choices:

\begin{itemize}
\item strict/call by value: every bound variable is evaluated exactly once.
\item call by name: every bound variable is evaluated zero or more times.
\item lazy/call by need: every bound variable is evaluated at most once.
\end{itemize}

Clearly, lazy evaluation is the best choice, and the other two may be discarded.
\footnote{For some unknown reasons, this obvious truth has yet to be accepted by
many. If you find yourself in this class of people, I suggest deep
introspection.}

\subsection{Evaluation Background}
Now that we have chosen an evaluation strategy.

\section{Abstract Machines}
In the beginning, Peter Landin said "let there be mechanical evaluation of
expressions", and there was SECD. Since then, an immense and rich literature has
evolved. While we won't attempt to summarize the entire literature\footnote{see
?? for a nice summary of the abstract machine literature}, we will take a moment
to point out a couple of things about existing machines relevant to this work.

First, there 

Next, we need to define our output type. For a number of reasons, including the
sanity of the authors and the readers, we don't attempt

\begin{code}
type Loc = Int
data Instr = Push Loc String
           | Enter Loc Int
           | Take Loc 
\end{code}

\begin{code}
data DBExpr = Var' Int
            | Lam' DBExpr
            | App' DBExpr DBExpr

deBruijn :: Expr -> Either Error DBExpr 
deBruijn e = db' [] e where
  db' ls (Var v)     = maybe (Left $ FreeVarError v) (Right . Var') $ lookup v ls
  db' ls (Lam x t)   = Lam' <$> db' ((x,0):map (fmap succ) ls) t
  db' ls (App t1 t2) = App' <$> (db' ls t1) <*> (db' ls t2)

\end{code}

\begin{code}
compile src = (assemble . codegen) <$> (deBruijn =<< parseExpr src)

codegen :: DBExpr -> [Instr]
codegen e = codegen' 0 e
  where codegen' l e = case e of
          Var' i -> [Enter l i]
          Lam' b -> Take l  : codegen' (succ l) b
          App' m n -> Push l n' : ms ++ ns where
            ms = codegen' (succ l) m
            ns = codegen' (succ l + length ms) n
            n' = takeWhile (/= ':') $ show $ head ns

assemble :: [Instr] -> String
assemble instrs = preamble ++ concatMap show instrs where
  preamble = unlines $ ".text"
                     : ".global _start"
                     : "_start:"
                     : "movq $0, %rdi"
                     : "movq $40000000, %rsi"
                     : "movq $255, %rdx"
                     : "movq $0x22, %r10"
                     : "movq $-1, %r8"
                     : "movq $0, %r9"
                     : "movq $9, %rax"
                     : "syscall"
                     : "movq %rax, %rbx"
                     : "movq %rsp, %rbp" : []
\end{code}

\begin{code}
instance Show Instr where
  show i = case i of
    Push l n  -> unlines $ ("Push_"++show l++":")
                        : "push %rax"
                        : ("push $"++n) : []
    Enter l i -> unlines $ ("Enter_"++show l++":")
                       :  replicate i "movq 16(%rax), %rax"
                       ++ "movq %rax, %rcx"
                       :  "movq 8(%rax), %rax"
                       :  "jmp *(%rcx)" : []
    Take l -> unlines $ ["Take_"++show l++":"]
                     ++ termination 
                     ++ ["update_"++show l++":"]
                     ++ update
                     ++ ["take_"++show l++":"]
                     ++ take where
                     termination =  
                        "cmp %rsp, %rbp"
                      : ("jne update_"++show l)
                      : ("movq $"++show l++", %rdi")
                      : "movq $60, %rax"
                      : "syscall" : []
                     update = 
                        "cmpq $0, (%rsp)"
                      : ("jne take_"++show l)
                      : "movq 8(%rsp), %rcx"
                      : ("movq $Take_"++show l++", "++"(%rcx)")
                      : "movq %rax, 8(%rcx)"
                      : "add $16, %rsp"
                      : ("jmp Take_"++show l) : []
                     take = 
                        "pop (%rbx)"
                      : "pop 8(%rbx)"
                      : "movq %rax, 16(%rbx)"
                      : "movq %rbx, %rax"
                      : "add $24, %rbx" : []
\end{code}
\section{Parsing and Printing}

Now that we have an syntax, let's write a function:

\begin{code}
y = Lam "g" $ App 
  (Lam "x" (App (Var "g") (App (Var "x") (Var "x"))))
  (Lam "x" (App (Var "g") (App (Var "x") (Var "x"))))
\end{code}

Well that was a bit verbose. Perhaps we should write a parser and a pretty
printer to make things easier. 

\subsection{Parsing}

We implement a simple parser using applicative style. 

\begin{code}
data Error = ParseError ParseError 
           | FreeVarError Var

parseExpr :: String -> Either Error Expr 
parseExpr s = either (Left . ParseError) Right $ parse term "" s where
  term :: Parsec String () Expr
  term =  Lam <$> (char 'λ' *> var <* char '.') <^> term
      <|> Var <$> var
      <|> App <$> (char '(' *> term) <^> (term <* char ')')
          where var = many1 letter
                a <^> b = a <* spaces <*> b
                infixl 4 <^>
\end{code}

Those familiar with standard lambda calculus notation will see that this varies
from the vastly inferior Barendregt conventional syntax. Instead of using
parenthesis to disambiguate, we borrow from the nearly-as-ancient syntax of
lisp, and use parentheses to denote applications explicitly. Like Barendregt,
however, we assume left associativity. 

Now let us take another shot at writing that function:

\begin{code}
y' = parseExpr "λg.(λx.(g (x x)) λx.(g (x x)))"
\end{code}

Much better.

\subsection{Printing}

We also implement a similarly simple show function, to make reading our lambda
calculus programs easier.

\begin{code}
instance Show Expr where
  show e = case e of
    Var v -> v
    Lam v b -> "λ" ++ v ++ "." ++ show b
    App m n -> "(" ++ show m ++ " " ++ show n ++ ")"
\end{code}


\begin{code}
usage = putStrLn "usage: cem <filename>"
runcompiler src = case compile src of
  Left (ParseError p) -> putStrLn $ "Parse Error: " ++ show p 
  Left (FreeVarError v) -> putStrLn $ "Unbound Variable: " ++ v
  Right s -> writeFile "cem.s" s

main = do
  args <- getArgs
  case args of
      [arg] -> readFile arg >>= runcompiler
      _ -> usage
\end{code}
\end{document}

