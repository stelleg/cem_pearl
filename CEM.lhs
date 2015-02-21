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
We present a compiler that compiles call-by-need lambda calculus directly to
x64 assembly code. The compiler is remarkable primarily for its simplicity,
which it achieves by implementing a new abstract machine, the Cactus
Environment Machine. By using shared environments to ensure bound terms are only
evaluated once (a requirement of lazy evaluation), we achieve an implementation
much simpler than any implementation of the call-by-need
lambda calculus we are aware of.
\end{abstract}

\section{Introduction} \label{sec:intro}
Lazy functional programming languages implement call-by-need lambda calculus
\cite{ariola1995call}. In these implementations, environments are implemented
\emph{flatly}, binding free variables to locations in the heap. Care must be
taken to ensure proper sharing.  

Here, we propose an alternative approach. 
We implement the
sharing required for call-by-need semantics by using a single large shared
environment as both an environment for every closure, as well as a heap. We
refer to this structure as a \emph{cactus environment}, and the resulting
abstract machine as the \emph{cactus environment} ($\mathcal{CE}$) machine.

We do not attempt to show that the $\mathcal{CE}$ is better than existing
approaches by traditional standards, such as speed, memory use, etc. Instead, we
show only that it enables us to build a surprisingly simple native code
compiler---it fits on a single page, Figure~\ref{fig:impl}.\footnote{We have omitted the rote pieces---the parser, the translation to deBruijn indices, and the x64 preamble;
they are available at
\url{http://github.com/stelleg/cem_pearl}.}
Our \texttt{compile} function takes a lambda term and produces a
list of x64 basic blocks. Since we use only a small subset of all x64
instructions, a simple string representation suffices.
\begin{code}
compile :: Expr -> [BasicBlock]
type BasicBlock = (Label, [Instr])
type Label = String
type Instr = String
\end{code}


\section{Preliminaries}

We assume familiarity with lambda calculus, environments, and closures.
We will use standard Barendregt syntax for lambda terms,
$$ e ::=  \lambda x . e \; | \; e \;  e \; | \;
x $$, applications are left
associative, and lambda bodies extend as far as possible. 

Internally our compiler operates on lambda terms with deBruijn indices,
so we also need the synatx $$ t ::= \lambda t \; | \; t \;
t \; | \; i $$ where $i \in \mathbb{N}$ replaces the variable name with an index
into the environment; in the implementation,
\begin{code}
type Var = Int
data Expr = Lam Expr
           | Var Var
           | App Expr Expr
\end{code}
Instead of
binding named variables, here a variable indexes the depth of its binding lambda with
a natural number. For example $\lambda t.\lambda f.t$ in standard notation
becomes $\lambda\lambda1$ in lambda calculus with deBruijn indices. 
Examples are easier to write, read, and understand in standard lambda
calculus with named variables, and we will do so.

In mechanical evaluation of expressions, it would be too inefficient to perform
explicit substitution. To solve this, the standard approach uses
closures~\cite{landin1964mechanical, curien1991abstract, jonesstg, biernacka2007concrete}.
Closures combine an expression with an environment, which binds the free
variables in the expression to other closures.

\section{Environment Representation} \label{sec:env}

There are two common approaches that span the design space for environment
representation: \emph{flat} environments and \emph{shared} environments (also
known as linked environments)~\cite{appel1988optimizing, shao1994space}. In a flat
environment, each closure has its own record of what closures all
of its free variables are bound to. In a shared environment, parts
of that record are shared among multiple environments~\cite{appel1988optimizing,
shao1994space}. For example, consider the following closed term: $$(\lambda
x.(\lambda y.t) (\lambda z.t_1)) t_2$$ Assuming the term $t$ has both $x$ and
$y$ as free variables, we must evaluate it in the environment binding both $x$
and $y$.  Similarly, assuming $t'$ contains both $z$ and $x$ as free variables,
we must evaluate it in an environment containg bindings for both $x$ and $z$.
Thus, we can represent the closures for $t$ and $t_1$ as
$$t[x=t_2[\bullet], y=c]$$ and $$t_1[x=t_2[\bullet], z=c_1]$$ respectively. One
can imagine allocating space for each environment separately. Such an allocation
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
back to Landin's SECD
machine~\cite{landin1964mechanical}.

The drawbacks and advantages of each approach are well known: with a flat
environment, variable lookup can be performed with a simple offset, or even
bound to a particular register~\cite{jonesstg, appel2006compiling}. On the other
hand, significant duplication can occur. With a shared environment, that
duplication is removed, but at the cost of possible link traversal upon
dereference. 

\subsection{Call-By-Need and the Heap}

Because of the benefits of flat environments we listed above, and perhaps others we
have overlooked, they have dominated call-by-need implementations
\cite{jonesstg, TIM, johnsson1984efficient, boquist1997grin}.\footnote{One could
also speculate that this was influenced by the historical dominance of doing
call-by-need evaluation using combinators, which take all their free variables
as formal parameters, and therefore suit flat environments well.}
Note that
for call-by-need languages, one must be careful when using flat
environments.  Because results from bound computations have to be shared across
closures referencing them, an implementation of call-by-need cannot copy closures
across environments. To illustrate this, consider again the earlier example.
If we copied closures, results from evaluation of $t_2[\bullet]$ from
dereferencing $x$ in $t$ would not be shared with the instances of $x$ in $t_1$.
This is fine for call-by-name, but to implement call by need, we must ensure
sharing.

The standard approach is to add a heap, which maps addresses to closures
\cite{jonesstg, TIM, johnsson1984efficient, sestoft}. Then, one
modifies the environments to map variables to addresses in the heap. The last
step is to add update markers pointing to heap addresses on the stack, to update
the closures at those locations in the heap with their value once they have been
evaluated. 

The reader may see where we are headed: in the shared
environment diagram from the preceding section, if we updated the
$x=t_2[\bullet]$ with $t_2[\bullet]$'s corresponding value after it had been
entered, we should get the sharing of the result between $t$ and $t_2$ without
an additional heap. This is what we now describe and implement.

\section{Shared Environment Call-By-Need} \label{sec:calc}

Here we describe the idea at the heart of the paper. We show how
the shared environment approach described earlier can be applied to call-by-need
evaluation. We start with a well known abstract machine for evaluating
call-by-name, the Krivine machine $K$, Figure~\ref{fig:Krivine}.
The mechanics are wonderfully simple: applications push their argument
onto the stack, abstractions pull an argument off the stack and move it into the
environment, and variables enter the closure at their index into the
environment.

\input{figure-K}

Note that we have not specified how the environment is represented in the $K$
machine. To move towards our final goal of sharing via environment structure,
let's force the environment to be shared, by creating a heap of environment
cells, and extending each cell manually. This gives us the $K'$ machine,
Figure~\ref{fig:K'}.

\input{figure-Kprime}

Now, we have a heap of environments, which ensures that the
environments are shared when extended.  The $K'$ machine is identical to the $K$
machine, except that it forces this sharing of environments. 

[SHOULD REPHRASE THE FOLLOWING SENTENCE--"Given our ... environments"... is awkward; "given" is a vague word]
Given our specified explicitly shared environments, we can add the necessary
machinery to implement full call-by-need semantics.
[CHECK THIS REWRITE:] To do so, we modify the $K'$ machine to make it lazy
in much the same way as Sestoft modified the Krivine machine~\cite{sestoft}.
%To do this, we add similar modifications to those others have added to the Krivine machine to make it lazy \cite{sestoft}.
We add update markers so that when a closure is entered, the
Var1 rule pushes an update marker to the corresponding location onto the stack.
Then, when the corresponding value is our current closure, it will pop the
update marker, and replace the closure on the heap with itself. This
call-by-need $L$ machine is specified in Figure~\ref{fig:L}.

\input{figure-CE}

[CONSISTENCY! IS IT $L$ or $\mathcal{CE}$? I vote for $L$]

We see from the semantics that all that has changed between the $K'$ and the
$\mathcal{CE}$ machine is the addition of the update marker to the Context
(which can be implemented as a normal stack), and the corresponding Update and
Var1 rules. This is in contrast to flat environment machines, such as the TIM~\cite{TIM}, which require more
complex machinery to ensure proper sharing.

This [WHAT?] is similar to existing lazy variants of the Krivine machine, such as that
defined by Sestoft \cite{sestoft}, except that instead of leaving the
environment unspecified, and adding a heap of closures, we have forced the
environment to be shared, and used that shared environment to implement the
necessary sharing of results.\footnote{In fact, in the code comments of his
dissertation, Sestoft mentions some sharing of environment, but it is never
formalized}. 

\section{An Example}

We now turn to 
visualizations of example executions to get a better intuition for how the $L$
machine operates. Figure~\ref{fig:states} shows a portion
of the execution trace during the evaluation of $(\lambda a.(\lambda b.b \; a)
(\lambda c.c \; a)) ((\lambda i.i) (\lambda j.j))$. 

\input{figure-states}

We can see each rule in effect in our visualization, and how it changes the
state of the machine, directly. Hopefully this gives the reader some intiution
for how the machine operates, and how simple its rules are from a mechanical
point of view. [THIS IS NOT ENOUGH. You can't expect the reader to follow the diagrams
without any guidance. Include a narrative explanation of the whole figure here. You have enough
space for the figure caption on this page.]

\section{Correspondence to The Call-By-Need Lambda Calculus}
To informally convince ourselves that we have correctly implemented call-by-need
semantics, we turn to the work of
Ariola et al.\cite{ariola1995call}, which specified an operational semantics for
call-by-need lambda calculus, Figure~\ref{fig:cbn}.

\input{figure-cbn}

Case-wise induction on $\rightarrow_{N}$ gives us an ordering to the closures
in the cactus environment. This is similar to the ordering from Lemma 8.1 of
Ref.~\cite{ariola1995call}.
With this ordering, we can define a $flatten$ function that takes any $(c, \mu)$
and flattens it accordingly. It does so by mapping any $(c, \mu)$ to a $\langle
\Phi \rangle t$, with the necessary variable hygiene. With this function, along
with structural induction on term size, it is not hard to show that
$\rightarrow_{\mathcal{CE}}$ bisimulates $\downarrow$.

It is worth noting the similarity between these semantics for pedagogical
purposes. Ariola et al.'s semantics throws out environmental structure because
it doesn't need to keep it. Similarly the abstract machines derived from the
semantics (e.g., \cite{garcia2009lazy}) are forced to do variable search in the
environment---deBruijn indices are not an option. Our machine, by retaining that
structure in the cactus environment, allows the use of deBruijn indices, and,
as we are about to show, straighforward low-level
implementation.

\section{Implementation}\label{sec:impl}

To those readers who enjoy thinking in terms of machine code, it is
already clear that the $\mathcal{CE}$ machine lends itself
straightforwardly to implementation. Indeed, our
entire native code compiler fits in a single page. 

First, some preliminaries. We are targeting the x64 GNU
assembler running on Linux. Any x64 linux machine that has GNU ld should be able
to run the compiled examples.
We include in our
data type a label for each basic block, so that it may be jumped to directly.
We annotate each x64 instruction line with a comment summarizing its purpose. 
We explain how each basic block maps onto the corresponding rule from
the abstract machine specification; the mapping is
quite simple. 

The compile function takes a deBruijn indexed lambda term and
generates a list of basic blocks of x64 assembly code. In the case of the Var1
and Var2 rules, they are combined into a single basic block, which traverses the
environment linked list until it reaches a closure, then pushes an update marker
to that location. The App rule is the simplest: it consists of two instructions
that push the location of the argument term along with the current environment
pointer onto the stack. The Lam and Update rules are a little more complicated.
Recall that there is no rule in which we have a lambda as our current term, and
an empty stack. That is so, because that is the condition for termination. Thus, we
must add a check to see if the stack is empty (\texttt{checkTermBB}), and terminate if it
is (\texttt{termBB}). If it is not, then we check (\texttt{checkUpdateBB})
to see if it is an update marker (which
we have designated to be the \texttt{NULL} pointer or 0, as there cannot be a valid code
pointer to that location), and if it is,
update the marker and continue without changing the current closure. If it is
not an update marker, it is an argument closure, so we pop to extend our current
environment with it. 

\input{figure-impl}

\section{Discussion}
The abstract machine as presented has some surprisingly nice properties, and some
very bad ones. There is a sense in which the CEM ???? is \emph{lazier} than flat
environment implementations. Instead of spending time allocating a flat
environment so that if a closure is entered multiple times ???? variable lookup, our
implementation does the minimal amount of preparation work. Of course, this
comes with the previously mentioned cost of non-constant variable lookup time. 

Instead????, we hope that this simple implementation could be of 
pedagogical value. Furthermore, we believe it could make for a good target
for abstraction thanks to its simplicity, following the approach of Van Horn et al.
\cite{van2010abstracting}. [????What does it mean to be a target for abstraction? Explain.]

\section{Conclusion and Future Work}
We hope that the reader is convinced of the elegance of this approach to implementing
call-by-need, and that our exploitation of shared environments was a worthwhile
endeavor. We are not aware of any call-by-need implementations that are nearly
this simple, and so end with a quote from Walt Whitman: "Simplicity is the glory
of expression".

We are actively exploring compile-time optimizations to make this abstract machine
practically usable for lazy language implementation. [ANYTHING ELSE?]

% We recommend abbrvnat bibliography style.
\bibliographystyle{abbrvnat}
\bibliography{annotated}

\end{document}

