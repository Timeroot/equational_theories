# Three term-definability obstructions from one E335 magma

The five-element magma below satisfies **E335**, `xy = y(yx)`, but none of
its binary term operations satisfies **E3352**, **E3748**, or **E4408**.
Consequently all three arrows from E335 are refuted for term-definability,
both over finite carriers and over arbitrary carriers. These are unrestricted
term-depth obstructions, rather than results from searching short terms.

The 2026-10-12 audit closes three class-level arrows and twelve raw arrows
in each term-definability variant. Reduced open counts change from 254 to 251
over arbitrary carriers and from 213 to 210 over finite carriers. The
structural and FO-definability boards do not change in this round.

| · | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | 0 | 4 | 0 | 1 | 3 |
| 1 | 3 | 1 | 1 | 4 | 0 |
| 2 | 0 | 1 | 2 | 2 | 2 |
| 3 | 4 | 0 | 2 | 2 | 1 |
| 4 | 1 | 3 | 2 | 0 | 2 |

## Why the term search can be replaced by a small proof

Write `q(x) = xx`. In **every** E335 magma, the law immediately gives
`xq(x) = q(x)`; applying the law again gives `q(x)x = q(x)`, and then
`q(x)q(x) = q(x)`. Thus every unary term other than the variable itself
evaluates to `q(x)`. Any binary term is either a projection or has diagonal
`q`. For this example that diagonal is `(0, 1, 2, 2, 2)`. Both projections
fail each target law at `(0, 1)`.

For the remaining terms we use seven tiny binary relations, listed in
[the data file](../data/definability_335_five_point.json). Each is closed under
coordinatewise multiplication in the source. If a relation contains `(a,c)`
and `(b,d)`, induction on terms ensures that it contains
`(t(a,b), t(c,d))`. Only two, three, and four of these restrictions are needed
for E3352, E3748, and E4408 respectively. They constrain selected entries of
a candidate operation `f`; the target law then gives a short contradiction.

All three proofs use the restriction
`(f(0,1), f(1,0)) ∈ {(0,1),(1,0),(2,2),(3,4),(4,3)}`.
For E3352, `f(x,y) = f(y,f(y,f(x,x)))`, these five cases contradict the law
using only one further relation, which usually forces `f(2,1)=1`.
For E3748, `f(x,y) = f(f(y,x),f(x,x))`, the other two relations first force
`f(0,2)=f(2,0)=0` and `f(4,2)=2`. The law then forbids 4 anywhere in column 2,
but each surviving case forces precisely such an entry.

For E4408, `f(x,f(x,y)) = f(f(y,y),x)`, the two surviving cases force
`f(2,0)=0`, `f(2,1)=1`, and `f(4,2)=2`. Consider the row map `L(y)=f(4,y)`.
One orientation forces `L²(0)=0`, `L²(1)=3`, and `L²(3)=2`, with
`L(2)=L(4)=2`. Five cases on `L(1)` contradict these equalities. The other
orientation interchanges the roles of 0 and 1, and five cases on `L(0)`
give the same contradiction.

## Formalization and limits

[FivePoint335.lean](../equational_theories/Definability/FivePoint335.lean)
contains the universal square-absorption lemma, the source check, relation
closure, induction on terms, and all three refutations. It uses ordinary
kernel-checked `decide` and equality reasoning, with no `sorry`,
`native_decide`, or SAT certificate. The public theorems are
`Law.MagmaLaw.Equation{3352,3748,4408}_not_termDefinableFromFin_Equation335_fivePoint`
and their unrestricted `not_termDefinableFrom` counterparts.
The complete module built in 6.2 seconds in the local verification run.

These are **not FO-definability obstructions**: element 2 is uniquely
characterized in this source by having more than one square root. The
parameter-free FO-definable constant operation with value 2 satisfies all
three targets. A different witness or argument would be needed for an FO
negative.

The source arose from testing proposed constructions using the square map,
such as `t(x,y)=q(x)q(y)`. That construction does not produce E3352 in every
E335 magma. Small compatible relations revealed the stronger obstruction
to every binary term, and the final Lean proof avoids the discovery solver.
The square map need not be a homomorphism, and the image of multiplication
need not consist of idempotents, so neither should be assumed in further
construction searches.

This source does have an E4290 term operation:
`(x · ((y·x)·(y·x))) · ((x·x)·y)`. The data checker verifies this finite
example; it is not asserted to work in every E335 magma. In particular, the
present witness cannot refute E335 term-defining E4290.
It also has an E3558 term operation, found by randomized composition of
binary terms. That longer expression is saved as a 143-node directed acyclic
graph in the same data file: each internal node is just a source multiplication
of two earlier nodes. The checker evaluates it and verifies E3558 on all
25 pairs. Thus this witness cannot decide either of the two remaining
term-definability arrows from the E335 class; a different source or a positive
general construction is needed. These two finite term examples are checked
by the Python script, not asserted as additional Lean theorems.

Reproduce the independent data checks with:

```sh
python3 scripts/definability_335_five_point_check.py
python3 scripts/definability_335_five_point_check.py --search
lake build equational_theories.Definability.FivePoint335
```

The optional second command replays small Z3 UNSAT searches using just the
listed constraints and ground law instances; these are not Lean proof
dependencies.
