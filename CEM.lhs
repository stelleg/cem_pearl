\documentclass[preprint]{sigplanconf}

\usepackage{hyperref}
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
\usepackage{listings}

\lstnewenvironment{code}{\lstset{language=Haskell,style=\small\ttfamily}}{}

\begin{document}
\title{Shared Environment Call-By-Need}
\subtitle{A Functional Pearl}

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
We present a compiler which compiles call-by-need lambda calculus directly to
x64 assembly code. The compiler is remarkable primarily for its simplicity,
which it achieves by implementing a novel abstract machine: the Cactus
Environment Machine (CEM). By using shared environments ensure work is only
performed once (a requirement of lazy evaluation), we acheive an implementation
significantly simpler than any existing implementation of the call-by-need
lambda calculus we are aware of.
\end{abstract}

\section{Introduction}
Lazy functional programming languages generally implement call-by-need lambda
calculus \cite{ariola95}. In these implementations, environments are implemented
\emph{flatly}, binding free variables to locations in the heap. Care must be
taken to ensure that proper sharing is ensured.  

In this paper, we propose an alternative approach. Using shared environments
(also called linked environments or linked closures), we can implement the
sharing required for call-by-need semantics by using a single large shared
environment as both an environment for every closure, as well as a heap. We
refer to this structure as a \emph{cactus environment}, and the resulting
abstract machine as the \emph{cactus environment machine} (CEM).

We don't attempt to show that the CEM is better than existing approaches by
traditional standards, e.g. speed, memory use, etc. Instead, we aim to show only
that it enables us to build a surprisingly simple native code compiler. To
emphasize the simplicity of the implemetation, we have written the paper as a
literate Haskell file, which we encourage the reader to download and tinker with
from \url{http://github/stelleg/cem.git}. 

We have attempted to leave out the pieces of the paper that are not
particularly interesting or relevant: the parser, the translation to deBruijn
indices, and the x64 preamble. If the reader is interested in these pieces, they
are available in the repository linked above.

In the spirit of call-by-need, we start with the type of the function we want,
and build from there as needed.

\begin{code}
module CEM where

compile :: Expr -> [BasicBlock]

type BasicBlock = (Label, [Instr])
type Label = String
type Instr = String
\end{code}

We opt to use a simple string representation of x64 instructions due to our
limited use of the instruction set. Specifically, we use labels 

\section{Lambda Calculus}

Before defining a Haskell datatype for lambda calculus with deBruijn indices, we
remark that we will be using standard Barendregt syntax for lambda calculus
expressions. Formally, 

$$ e ::=  \lambda x . e \; | \; e \;  e \; | \;  x  \; | \;  (e) $$

where x is a non-empty string of letters, applications are left associative, and
parenthesis close 

\begin{code}
type Var = Int
data Expr = Lam Expr
          | Var Var
          | App Expr Expr
\end{code}

The \texttt{Expr} type defines the syntax of lambda calculus with deBruijn
indices. This is identical to standard lambda calculus, except that instead of
binding named variables, a variable indexes the depth of its binding lambda with
a natural number. For example $\lambda t.\lambda f.t$ in standard lambda
calculus becomes $\lambda\lambda1$ in lambda calculus with deBruijn indices. 

Because examples are easier to write, read, and understand in standard lambda
calculus with named variables, we will occasionally give examples in this form.
The translation from lambda calculus to lambda calculus with deBruijn indices is
well understood, and may be found in the supplementary information linked in
Section~\ref{intro}.

\section{Abstract Machines}
In the beginning, Peter Landin said "let there be mechanical evaluation of
expressions", and there was SECD. Since then, an immense and rich literature has
evolved. While we won't attempt to summarize the entire literature\footnote{see
?? for a nice summary of the abstract machine literature}, we will take a moment
to point out a couple of things about existing machines relevant to this work.

\begin{code}
compile e = compile' 0 e where 
  compile' l e = case e of
    Var i -> [varBB l i]
    Lam b -> checkTermBB l 
           : termBB l 
           : checkUpdateBB l 
           : updateBB l 
           : takeBB l 
           : compile' (succ l) b
    App m n -> appBB l nlab : ms ++ ns where
      ms = compile' (succ l) m
      ns@((nlab,_):_) = compile' (succ l + length ms) n

\end{code}

\begin{code}
type Location = Int

appBB :: Location -> Label -> BasicBlock
appBB l n = ("App_"++show l, 
  ["push %rax"
  ,"push $"++n])

varBB :: Location -> Var -> BasicBlock
varBB l i = ("Var_"++show l,
  replicate i "movq 16(%rax), %rax"
  ++ ["push %rax"
     ,"push $0"
     ,"movq %rax, %rcx"
     ,"movq 8(%rax), %rax"
     ,"jmp *(%rcx)"])

checkTermBB :: Location -> BasicBlock
checkTermBB l = ("CheckTerm_"++show l,
  ["cmp %rsp, %rbp"
  ,"jne CheckUpdate_"++show l])

termBB :: Location -> BasicBlock
termBB l = ("Term_"++show l,
  ["movq $"++show l++", %rdi"
  ,"movq $60, %rax"
  ,"syscall"])

checkUpdateBB :: Location -> BasicBlock
checkUpdateBB l = ("CheckUpdate_"++show l,
  ["cmpq $0, (%rsp)"
  ,"jne Take_"++show l])

updateBB :: Location -> BasicBlock
updateBB l = ("Update_"++show l,
  ["movq 8(%rsp), %rcx"
  ,"movq $CheckTerm_"++show l++", "++"(%rcx)"
  ,"movq %rax, 8(%rcx)"
  ,"add $16, %rsp"
  ,"jmp CheckTerm_"++show l])
 
takeBB :: Location -> BasicBlock
takeBB l = ("Take_"++show l,
  ["pop (%rbx)"
  ,"pop 8(%rbx)"
  ,"movq %rax, 16(%rbx)"
  ,"movq %rbx, %rax"
  ,"add $24, %rbx"])

\end{code}

\end{document}

