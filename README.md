# Cactus environment machine

We implement call by need using shared environments. 

For a description of the approach, the functional pearl document is in `paper/`

For the implementation, see `code/`. The compiled program `cem` takes a file that
should be a closed lambda term, and produces an executable `prog`, which when
run will print the term of the resulting closure (if there is one) in lambda
calculus with deBruijn indices. For example, the program `λt.t` will print `λ0`.

There is one discrepancy between the paper and the code. The paper uses
Barendregt syntax, but the implementation uses a more lispy approach, where
every application is wrapped in parentheses. We also create a simple let rule,
which is compiled to pure lambda terms, where `{` is the standard `let` and `}`
is the usual `in`. See the `code/examples/` for examples of the syntax, but
formally:

    t ::= λx.t | (t .. t t) | x | { x = t y = t ... z = t } t

So instead of `(λx.a x) λy.y`, we would write `(λx.(a x) λy.y)`. Parentheses are
used to define applications, not to disambiguate. This has the nice property
that when a term ends is unambiguous.


