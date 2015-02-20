\documentclass[preprint]{sigplanconf}

\usepackage{inconsolata}
\usepackage{hyperref}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage{natbib}
\usepackage{graphicx}
\usepackage{tikz}
\usepackage{mathtools}
\usetikzlibrary{chains,fit,shapes,calc}
\usepackage{semantic}
\usepackage{tabu}
\usepackage{amsthm}
\usepackage{mathptmx}
\usepackage{todonotes}
\usepackage{listings}

\lstset{
  frame=none,
  xleftmargin=6pt,
  stepnumber=1,
  belowcaptionskip=\bigskipamount,
  captionpos=b,
  escapeinside={*'}{'*},
  language=haskell,
  tabsize=2,
  emphstyle={\bf},
  commentstyle=\it\ttfamily,
  stringstyle=\mdseries\ttfamily\color{violet},
  showspaces=false,
  keywordstyle=\bfseries\ttfamily\color{teal},
  columns=flexible,
  basicstyle=\small\ttfamily,
  showstringspaces=false,
  morecomment=[l]\%,
}

\lstnewenvironment{code}{}{}

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
Environment Machine. By using shared environments ensure bound terms are only
evaluated once (a requirement of lazy evaluation), we achieve an implementation
significantly simpler than any existing implementation of the call-by-need
lambda calculus we are aware of.
\end{abstract}

\section{Introduction} \label{sec:intro}
Lazy functional programming languages implement call-by-need lambda calculus
\cite{ariola1995call}. In these implementations, environments are implemented
\emph{flatly}, binding free variables to locations in the heap. Care must be
taken to ensure that proper sharing is ensured.  

In this paper, we propose an alternative approach. Using shared environments
(also called linked environments or linked closures), we can implement the
sharing required for call-by-need semantics by using a single large shared
environment as both an environment for every closure, as well as a heap. We
refer to this structure as a \emph{cactus environment}, and the resulting
abstract machine as the \emph{cactus environment} ($\mathcal{CE}$) machine.

We don't attempt to show that the $\mathcal{CE}$ is better than existing
approaches by traditional standards, e.g. speed, memory use, etc. Instead, we
aim to show only that it enables us to build a surprisingly simple native code
compiler. Indeed, the entire compiler fits on a single page. 

We have omitted out the pieces of the implementation that are not novel 
: the parser, the translation to deBruijn indices, and the x64 preamble. If the
reader is interested in these pieces, they are available at
\url{http://github.com/stelleg/cem_pearl}. 

In the spirit of call-by-need, we start with the type of the function we want,
and build from there as needed.
\begin{code}
module CEM where

compile :: Expr -> [BasicBlock]

type BasicBlock = (Label, [Instr])
type Label = String
type Instr = String
\end{code}
As we can see, our compile function will take a lambda expression, and produce a
list of basic blocks. Recall that basic blocks are sequences of instructions
with exactly one exit and one entry point. While we could conceive of a fancier
mechanism for generating x64, we opt to use a simple string representation of
x64 instructions due to our limited use of the instruction set.  

\section{Preliminaries}

We assume basic familiarity with lambda calculus, environments, and closures.
We will be using standard Barendregt syntax for lambda calculus expressions.
Formally, $$ e ::=  \lambda x . e \; | \; e \;  e \; | \;
x $$ where $x$ is a non-empty string of letters, applications are left
associative, and lambda bodies extend as far as possible. 

Because our compiler will be operating on lambda calculus with deBruijn indices,
we define the equivalent syntax for these terms: $$ t ::= \lambda t \; | \; t \;
t \; | \; i $$ where $i \in \mathbb{N}$ replaces the variable name with an index
into the environment. We define the corresponding algebraic data type in Haskell:
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
Section~\ref{sec:intro}.

In mechanical evaluation of expressions, it would be too inefficient to perform
explicit substitution. To solve this, the standard approach uses closures
~\cite{landin1964mechanical, curien1991abstract, jonesstg, biernacka2007concrete}.
Closures combine an expression with an environment, which binds the free
variables in the expression to other closures.

\section{Environment Representation} \label{sec:env}

There are two common approaches that span the design space for environment
representation: \emph{flat} environments and \emph{shared} environments (also
known as linked environments)~\cite{appel1988optimizing, shao1994space}. A flat
environment is one in which each closure has its own record of what closures all
of its free variables are bound to. A shared environment is one in which parts
of that record are shared among multiple environments~\cite{appel1988optimizing,
shao1994space}. For example, consider the following closed term: $$(\lambda
x.(\lambda y.t) (\lambda z.t_1)) t_2$$ Assuming the term $t$ has both $x$ and
$y$ as free variables, we must evaluate it in the environment binding both $x$
and $y$.  Similarly, assuming $t'$ contains both $z$ and $x$ as free variables,
we must evaluate it in an environment containg bindings for both $x$ and $z$.
Thus, we can represent the closures for $t$ and $t_1$ as
$$t[x=t_2[\bullet], y=c]$$ and $$t_1[x=t_2[\bullet], z=c_1]$$ respectively. One
can imagine allocating space for each environment seperately. Such an allocation
scheme would be an example of \emph{flat} environments, where each closure comes
with its own record of all of its free variables. Because of the nested scope of
the given term, $x$ is bound to the same closure in each environment.  Thus, we
can also create a shared, linked environment, represented by the following
diagram:

\begin{center}
\begin{tikzpicture}[ 
  edge from parent path={(\tikzchildnode\tikzchildanchor) edge [-latex] (\tikzparentnode\tikzparentanchor)},
  level distance=1cm
]
\node (d) {$\bullet$} child{node (a) {$x=t_2[\bullet]$} child{node (b) {$y=c$}} child{node (c)
{$z=c_1$}}};

\end{tikzpicture}
\end{center}
Now each of the environments is represented by a linked list, with the binding
of $x$ shared between them. This is a simple example of a \emph{shared}
environment ~\cite{appel1988optimizing}. This shared, linked structure dates
back to the first machine for evaluating expressions: Landin's SECD
machine~\cite{landin1964mechanical}.

The drawbacks and advantages of each approach are well known: with a flat
environment, variable lookup can be performed with a simple offset, or even
bound to a particular register~\cite{jonesstg, appel2006compiling}. On the other
hand, significant duplication can occur. With a shared environment, that
duplication is removed, but at the cost of possible link traversal upon
dereference. 

\subsection{Call-By-Need and the Heap}

Because of the benefits of flat environments listed above, and perhaps some we
have overlooked, they have dominated call-by-need implementations
\cite{jonesstg, TIM, johnsson1984efficient, boquist1997grin}.\footnote{One could
also speculate that this was influenced by the historical dominance of doing
call-by-need evaluation using combinators, which take all their free variables
as formal parameters, and therefore suit flat environments nicely}. Note that
for call-by-need languages, one needs to be careful when using flat
environments.  Because results from bound computations have to be shared across
closures referencing them, an implementation of call-by-need can't copy closures
across environments. To illustrate this, consider again the example from
earlier. If we copied closures, results from evaluation of $t_2[\bullet]$ from
dereferencing $x$ in $t$ would not be shared with the instances of $x$ in $t_1$.
This is fine for call-by-name, but to implement call by need, we need to ensure
sharing.

The standard approach is to add a heap, which maps addresses to closures
\cite{jonesstg, TIM, johnsson1984efficient, sestoft}. After this addition, one
modifies the environments to map variables to addresses in the heap. The last
step is to add update markers pointing to heap addresses on the stack, to update
the closures at those locations in the heap with their value once they have been
evaluated. 

The particularly astute reader may see where we are headed. In the shared
environment diagram from the previous section, if we updated the
$x=t_2[\bullet]$ with $t_2[\bullet]$'s corresponding value after it had been
entered, we should get the sharing of the result between $t$ and $t_2$ without
an additional heap. Indeed, this is exactly what we now describe and implement.

\section{Shared Environment Call-By-Need} \label{sec:calc}

We use this section to describe the idea at the heart of the paper. We show how
the shared environment approach described earlier can be applied to call by need
evaluation. We start with a well known abstract machine for evaluating
call-by-name: the Krivine machine.  Figure~\ref{fig:Krivine} defines the $K$
machine. The mechanics are wonderfully simple: applications push their argument
onto the stack, abstractions pull an argument off the stack and move it into the
environment, and variables enter the closure at their index into the
environment.

\begin{figure}
\textbf{Syntax}
\begin{align*}
\tag{State} s &::= \langle c, \sigma \rangle \\
\tag{Closure} c &::= t [\rho] \\
\tag{Environment} \rho &::= \bullet \; | \; c \cdot \rho \\
\tag{Context} \sigma &::= \square \; | \; \sigma \; c  \\
\end{align*}
\textbf{Semantics}
\begin{align*}
\tag{Lam}
\langle \lambda t[\rho], \sigma \; c \rangle 
  &\rightarrow_{K}
\langle t[c \cdot \rho], \sigma \rangle  \\
\tag{App}
\langle t \; t'[\rho], \sigma \rangle
  &\rightarrow_{K}
\langle t[\rho], \sigma \; t'[\rho] \rangle \\
\tag{Var1}
\langle 0[c \cdot \rho ], \sigma  \rangle
  &\rightarrow_{K}
\langle c, \sigma \rangle  \\
\tag{Var2}
\langle i[c \cdot \rho], \sigma \rangle
  &\rightarrow_{K}
\langle (i-1)[\rho], \sigma \rangle \\
\end{align*}
\caption{Syntax and semantics of the call-by-name $K$ machine.}
\label{fig:Krivine}
\end{figure}

Note that we have not specified how the environment is represented in the $K$
machine. To move towards our final goal of sharing via environment structure,
let's force the environment to be shared, by creating a heap of environment
cells, and extending each cell manually. This gives us the $K'$ machine, given
in Figure~\ref{fig:K'}.

\begin{figure*}
\textbf{Syntax}
\begin{align*}
\langle c, \sigma, \mu f \rangle &\rightarrow_{K'} \langle c, \sigma, \mu, f \rangle \\
\tag{Closure} c &::= t [l] \\
\tag{Heap} \mu &::= \epsilon \; | \; \mu [ l \mapsto \rho ] \\
\tag{Environment} \rho &::= \bullet \; | \; c \cdot l \\
\tag{Context} \sigma &::= \square \; | \; \sigma \; c \\
\tag{Location} l,u,f &\in \mathbb{N}
\end{align*}
\textbf{Semantics}
\begin{align*}
\tag{Lam}
\langle \lambda t[l], \sigma \; c, \mu, f \rangle 
  &\rightarrow_{K'}
\langle t[f], \sigma, \mu[f \mapsto c \cdot l], f+1 \rangle  \\
\tag{App}
\langle t \; t'[l], \sigma, \mu, f \rangle
  &\rightarrow_{K'}
\langle t[l], \sigma \; t'[l], \mu, f \rangle \\
\tag{Var1}
\langle 0[l], \sigma, \mu, f \rangle
  &\rightarrow_{K'}
\langle c, \sigma, \mu, f \rangle 
\; \textnormal{where} \; c \cdot l' = \mu(l)\\
\tag{Var2}
\langle i[l], \sigma, \mu, f \rangle
  &\rightarrow_{K'}
\langle (i-1)[l'], \sigma, \mu, f \rangle
\; \textnormal{where} \; c \cdot l' = \mu(l) \\
\end{align*}
\caption{Syntax and semantics of the call-by-name $K'$ machine.}
\label{fig:K'}
\end{figure*}

Now, we have a heap of environments, which allows us to ensure that the
environments are shared when extended.  The $K'$ machine is identical to the $K$
machine, except that it forces this sharing of environments. 

Given our specified explicitly shared environments, we can add the necessary
machinery to implement full call-by-need semantics. To do this, we add similar
modifications to those others have added to the Krivine machine to make it lazy
\cite{sestoft}.  We add update markers so that when a closure is entered, the
Var1 rule pushes an update marker to the corresponding location onto the stack.
Then, when the corresponding value is our current closure, it will pop the
update marker, and replace the closure on the heap with itself. This
call-by-need $L$ machine is specified in Figure~\ref{fig:L}.

\begin{figure*}
\textbf{Syntax}
\begin{align*}
\tag{Closure} c &::= t [l] \\
\tag{Heap} \mu &::= \epsilon \; | \; \mu [ l \mapsto \rho ] \\
\tag{Environment} \rho &::= \bullet \; | \; c \cdot l \\
\tag{Value} v &::= \lambda t[l] \\
\tag{Context} \sigma &::= \square \; | \; \sigma \; c \;  | \; u:=\sigma \\
\tag{Location} l,u,f &\in \mathbb{N}
\end{align*}
\textbf{Semantics}
\begin{align*}
\tag{Upd}
\langle v, u := \sigma, \mu[u \mapsto c \cdot l], f \rangle 
  &\rightarrow_{\mathcal{CE}} 
\langle v, \sigma, \mu[u \mapsto v \cdot l], f \rangle  \\
\tag{Lam}
\langle \lambda t[l], \sigma \; c, \mu, f \rangle 
  &\rightarrow_{\mathcal{CE}}
\langle t[f], \sigma, \mu[f \mapsto c \cdot l], f+1 \rangle  \\
\tag{App}
\langle t \; t'[l], \sigma, \mu, f \rangle
  &\rightarrow_{\mathcal{CE}}
\langle t[l], \sigma \; t'[l], \mu, f \rangle \\
\tag{Var1}
\langle 0[l], \sigma, \mu, f \rangle
  &\rightarrow_{\mathcal{CE}}
\langle c, \sigma, \mu, f \rangle 
\; \textnormal{where} \; c \cdot l' = \mu(l)\\
\tag{Var2}
\langle i[l], \sigma, \mu, f \rangle
  &\rightarrow_{\mathcal{CE}}
\langle (i-1)[l'], \sigma, \mu, f \rangle
\; \textnormal{where} \; c \cdot l' = \mu(l) \\
\end{align*}
\caption{Syntax and semantics of the call-by-need $\mathcal{CE}$ machine.}
\label{fig:L}
\end{figure*}

We can see from the semantics that all that has changed between the $K'$ and the
$\mathcal{CE}$ machine is the addition of the update marker to the Context
(which can be impemented as a normal stack), and the corresponding Update and
Var1 rules. This is contrast to flat environment machines that require more
complex machinery to ensure proper sharing, such as the TIM \cite{TIM}.

This is similar to existing lazy variants of the krivine machine, such as that
defined by Sestoft \cite{sestoft}, except that instead of leaving the
environment unspecified, and adding a heap of closures, we have forced the
environment to be shared, and used that shared environment to implement the
necessary sharing of results.\footnote{In fact, in the code comments of his
dissertation, Sestoft mentions some sharing of environment, but it is never
formalized}. 

\section{An Example}

While machine semantics are beautiful in their own way, we now turn to pleasant
visualizations of example executions to get a better intuition for how this
machine will operate. Figure~\ref{fig:states} shows a visualization of portion
of the execution trace during the evaluation of $(\lambda a.(\lambda b.b \; a)
(\lambda c.c \; a)) ((\lambda i.i) (\lambda j.j))$. 

\begin{figure*}
\includegraphics[width=\linewidth/3]{figures/12.pdf}
\includegraphics[width=\linewidth/3]{figures/13.pdf}
\includegraphics[width=\linewidth/3]{figures/14.pdf}
\includegraphics[width=\linewidth/3]{figures/15.pdf}
\includegraphics[width=\linewidth/3]{figures/16.pdf}
\includegraphics[width=\linewidth/3]{figures/17.pdf}
\includegraphics[width=\linewidth/3]{figures/18.pdf}
\includegraphics[width=\linewidth/3]{figures/19.pdf}
\includegraphics[width=\linewidth/3]{figures/20.pdf}
\caption{An example sequence of machine states during the evaluation of the term
$(\lambda a.(\lambda b.b \; a) (\lambda c.c
\; a)) ((\lambda i.i) (\lambda j.j))$. Order is left to right, top to bottom.
The free heap location $f$ is left out to save space. Dotted lines denote }
\label{fig:states}
\end{figure*}

We can see each rule in effect in our visualization, and how it changes the
state of the machine, directly. Hopefully this gives the reader some intiution
for how the machine operates, and how simple its rules are from a mechanical
point of view. 

\section{Correspondence to The Call-By-Need Lambda Calculus}
To informally convince ourselves that we have correctly implemented call-by-need
semantics (if you are not already convinced!), we turn to the seminal work of
Ariola et al.\cite{ariola1995call}, which specifies an operational semantics for
call-by-need lambda calculus. In particular, we turn to their Figure 8, show in
Figure~\ref{fig:cbn}, which defines an operational semantics for call-by-need.

\begin{figure}
\begin{align*}
\tag{Id} \inference
{\langle \Phi \rangle e \Downarrow \langle \Psi \rangle \lambda x.e'}
{\langle \Phi, x \mapsto e, \Upsilon \rangle x \Downarrow \langle \Psi, x
\mapsto \lambda x.e', \Upsilon \rangle \lambda x.e'}
\end{align*}
\begin{align*}
\tag{Abs} \inference 
{}
{\langle \Phi \rangle \lambda x . e \Downarrow \langle \Phi \rangle \lambda x.e}
\end{align*}
\begin{align*}
\tag{App} \inference
{\langle \Phi \rangle e_l \Downarrow \langle \Psi \rangle \lambda 
x.e_n \\ \langle \Psi, x' \mapsto e_m \rangle [x'/x]e_n \Downarrow \langle
\Upsilon \rangle \lambda y.e'}
{\langle \Phi \rangle e_l \; e_m \Downarrow \langle \Upsilon \rangle \lambda y.e'}
\end{align*}
\caption{Ariola et. al's Call-By-Need Operational Semantics}
\label{fig:cbn}
\end{figure}

Case-wise induction on $\rightarrow_{N}$ gives us an ordering to the closures
in the cactus environment. This is similar to the ordering from Lemma 8.1 of
\cite{ariola1995call}.

With this ordering, we can define a $flatten$ function that takes any $(c, \mu)$
and flattens it accordingly. It does so by mapping any $(c, \mu)$ to a $\langle
\Phi \rangle t$, with the necessary variable hygiene. With this function, along
with structural induction on term size, it is not hard to show that
$\rightarrow_{\mathcal{CE}}$ bisimulates $\downarrow$.

It is worth noting the similarity between these semantics for pedagogical
purposes. Ariola et. al's semantics throws out environmental structure because
it doesn't need to keep it. Similarly the abstract machines derived from the
semantics (e.g.  \cite{garcia2009lazy}) are forced to do variable search in the
environment: deBruijn indices are not an option. Our machine, by retaining that
structure in the cactus environment, allows for use of deBruijn indices, and,
as we will see in Section~\ref{sec:impl}, straighforward low-level
implementation.

\section{Implementation}\label{sec:impl}

To those few readers who enjoy thinking in terms of machine code, it may be
already clear that the $\mathcal{CE}$ machine lends itself in a very
straightforward way to implementation. Indeed, we specify such an implementation
in this section. It is such a simple process that we manage to implement the
entire native code compiler in a single page. 

First, a couple of clarifiying preliminaries. We are targeting x64 GNU
assembler running on Linux. Any x64 linux machine that has GNU ld should be able
to run the compiled examples. Recall again that a basic block is a sequence of
instructions with a single entry and single exit point. We include in our
data type a label for each basic block, so that it may be jumped to directly.

We annotate each x64 instruction line with a comment summarizing its purpose. In
addition, we explain how each basic block maps onto the corresponding rule from
the abstract machine specification. Fortunately this is easy, as the mapping is
quite simple. 

Recall that the compile function takes a deBruijn indexed lambda term and
generates a list of basic blocks of x64 assembly code. In the case of the Var1
and Var2 rules, they are combined into a single basic block, which traverses the
environment linked list until it reaches a closure, then pushes an update marker
to that location. The App rule is the simplest, it consists of two instructions
that push the location of the argument term along with the current environment
pointer onto the stack. The Lam and Update rules are a little more complicated.
Recall that there is no rule in which we have a lambda as our current term, and
an empty stack. That is because this is the condition for termination. Thus, we
must add a check to see if the stack is empty (checkTermBB), and terminate if it
is (termBB). If it is not, then we check to see if it is an update marker (which
we have designated to be the NULL pointer or 0, as there cannot be a valid code
pointer to that location), (checkUpdateBB), and if it is an update marker,
update the marker and continue without changing the current closure. If it is
not an update marker, it is an argument closure, so we pop to extend our current
environment with it. 

\begin{figure*}
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

type Location = Int

appBB :: Location -> Label -> BasicBlock
appBB l n = ("App_"++show l, 
  ["push %rax"                                      -- Push environment
  ,"push $"++n])                                    -- Push argument code

varBB :: Location -> Var -> BasicBlock
varBB l i = ("Var_"++show l,
  replicate i "movq 16(%rax), %rax"                 -- Index into environment
  ++ ["push %rax"                                   -- Push update location
     ,"push $0"                                     -- Push update marker
     ,"movq %rax, %rcx"                             -- \
     ,"movq 8(%rax), %rax"                          -- Load new Environment
     ,"jmp *(%rcx)"])                               -- Jump to new code

checkTermBB :: Location -> BasicBlock
checkTermBB l = ("CheckTerm_"++show l,
  ["cmp %rsp, %rbp"                                 -- Check if stack is empty
  ,"jne CheckUpdate_"++show l])                     -- If not empty, check updates

termBB :: Location -> BasicBlock
termBB l = ("Term_"++show l,
  ["movq $"++show l++", %rdi"                       -- \
  ,"movq $60, %rax"                                 -- Exit with label exitcode
  ,"syscall"])                                      -- / 

checkUpdateBB :: Location -> BasicBlock
checkUpdateBB l = ("CheckUpdate_"++show l,
  ["cmpq $0, (%rsp)"                                -- Check for update marker
  ,"jne Take_"++show l])                            -- If not udpate, proceed to take

updateBB :: Location -> BasicBlock
updateBB l = ("Update_"++show l,
  ["movq 8(%rsp), %rcx"                             -- \
  ,"movq $CheckTerm_"++show l++", "++"(%rcx)"       --  Replace code pointer
  ,"movq %rax, 8(%rcx)"                             --  Replace env pointer
  ,"add $16, %rsp"                                  --  Pop update 
  ,"jmp CheckTerm_"++show l])                       --  Continue with new stack
 
takeBB :: Location -> BasicBlock
takeBB l = ("Take_"++show l,
  ["pop (%rbx)"                                     -- Pop code into free heap cell
  ,"pop 8(%rbx)"                                    -- Pop env into free heap cell
  ,"movq %rax, 16(%rbx)"                            -- Point env to free heap cell
  ,"movq %rbx, %rax"                                -- /
  ,"add $24, %rbx"])                                -- Increment free heap cell

\end{code}
\caption{Full compiler implementation}
\label{fig:impl}
\end{figure*}

\section{The Good, the Bad, and the Ugly}
The abstract machine as presented has some surprisingly nice properties, and some
very bad ones. There is a sense in which the CEM is \emph{lazier} than flat
environment implementations. Instead of spending time allocating a flat
environment so that if a closure is entered multiple times variable lookup, our
implementation does the minimal amount of preparation work.

Of course, this comes with the previously mentioned cost of non-constant
variable lookup time. This performance wart is both bad and ugly. Whether the
wart is fatal is a question for future work. 

\section{Conclusion}
We hope that the reader is convinced of the elegance of this approach to
call-by-need, and that our exploitation of shared environments was a worthwhile
endeavor. We are not aware of any call-by-need implementations that are nearly
this simple, and so end with a quote from Walt Whitman: "Simplicity is the glory
of expression".

% We recommend abbrvnat bibliography style.
\bibliographystyle{abbrvnat}
\bibliography{annotated}

\end{document}

