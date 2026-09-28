# E1483: a failed retraction and the remaining rank-descent lemmas

26 September 2026. **Uniform translation rank implying E168 is still open.**
The previously proved statement with the additional hypothesis `|G| = r²`
remains valid. This follow-up found a counterexample to one proposed proof,
then reduced a replacement proof to two precise, unproved algebraic lemmas.

Write `Row(a)={a*x : x in G}`, and `e -> a` when `a in Row(e)`.
Consider a path `e -> a -> b`, and put `t=e*b`. E1483 ensures that
`e -> t -> b` is also a path. The desired descent statement is

```
t != a  implies  |Row(t)| < |Row(a)|.
```

This would prove the uniform-rank conjecture: apply it to the path
`y*x -> x -> x*z`; equal ranks would force `(y*x)*(x*z)=x`, which is E168.

## An actual counterexample to the first retraction

The original proposed maps were

```
F : Row(t) -> Row(a),   F(y)=a*(y*t),
G : Row(a) -> Row(t),   G(x)=t*(x*a).
```

The claim `G(F(y))=y` is **false**, even in a magma satisfying both E1483
and E1485. A bounded SAT search found the following order-eight table:

```
2 5 7 4 2 7 4 5
6 3 7 1 6 7 1 3
4 4 0 4 0 0 4 0
7 1 7 1 7 7 1 1
6 3 0 1 6 0 1 3
7 1 7 1 7 7 1 1
4 4 0 4 0 0 4 0
2 5 0 4 2 0 4 5
```

Choose `e=0,a=7,b=4,t=2`. The path is witnessed by `0*2=7`, `7*6=4`,
and `0*4=2`. Here `Row(t)={0,4}`, `F(0)=5`, `F(4)=2`, and

```
G(F(0))=4=G(F(4)).
```

Thus `GF` is not even injective; taking a positive power cannot turn it into
the identity. The full E1483/E1485 table checks and the failure are proved
by kernel reduction in
[RetractionCounterexample.lean](../equational_theories/Spectrum/Equation1483/RetractionCounterexample.lean).
The main declarations are `law1483`, `law1485`, `path`,
`composite_not_injective`, and `composite_not_identity` in namespace
`Spectrum.E1483.RetractionCounterexample`. The E1483 table proof has no
axioms; the noninjectivity proof uses only `propext`.

This counterexample does **not** refute injectivity of F or strict rank
descent: F is injective here, and the ranks are two and four.

## A replacement proof, conditional on two open lemmas

The first candidate is the following absorption identity:

```
t*((t*s)*a)=t*s,       where e -> a -> b and t=e*b.           (A)
```

Self-duality would also give

```
(a*(s*t))*t=s*t.                                            (A*)
```

This suggests the different map `J(x)=t*(x*t)`. It always maps `Row(a)`
into `Row(t)`. Under (A*), E1483 translation regularity gives

```
J(F(y)) = t*((a*(y*t))*t) = t*(y*t) = y   for y in Row(t).
```

Consequently J is surjective and F is injective. The second candidate is

```
a*(b*t)=b  implies  a=t,  where e -> a -> b and t=e*b.        (B)
```

If `t!=a`, (B) implies `b!=F(b)`. Both are in `Row(a)`, while
`J(b)=b=J(F(b))`; here `b in Row(t)` and ordinary translation regularity
give the first equality. Thus J is a noninjective surjection between finite
sets, which gives the desired strict rank inequality.

The argument after (A) and (B) is complete, but **neither (A) nor (B) has
been proved**. They are not used by any Lean spectrum theorem.

The weaker condition `(b*a)*b=a` follows from the premise of (B), but cannot
replace it. In the two-point NAND model, `e=a=b=1,t=0` satisfies the weaker
condition and the path assumptions, yet `a!=t`.

## A concrete sufficient identity for absorption

For `q in Row(t)`, short-term search suggests the common predecessor

```
c=((((b*a)*q)*e)*a),       c*q=t.                            (C)
```

The second equality is still **unproved**. Its first definition guarantees
`c in Col(a)`, equivalently `c -> a`. E1483 would then give
`(c*q)*(q*a)=q`, proving (A). This is an alternative algebraic target with
an explicit witness, rather than an unproved existence claim.

## Checks and limits

The [saved record](../data/spectrum/1483_rank_descent_followup.json) contains
four full tables: the prior constant-row eight-point example, a prior
rank-two eight-point example, a central nine-point example, and the new
counterexample. The checker also examines their opposite operations.

```
python3 scripts/spectrum_1483_rank_descent_check.py
lake env lean equational_theories/Spectrum/Equation1483/RetractionCounterexample.lean
```

The checker verifies E1483 directly for every table, the explicit failed
retraction, and the surviving candidates on 732 paths and 2,534 row-point
contexts. **Agreement on these examples is not a proof of the candidates.**
The supplied examples still lie within E1485 and its previously identified
cubic twists, which limits the reach of this evidence.

The new table was found in approximately 1.55 seconds. Separate order-eight
SAT searches for failure of (A), injectivity of F, or (B) each reached a
150-second cap without a result. Targeted Vampire and Twee searches for
absorption, collapse, or the predecessor identity also failed within their
120–150-second limits. No timeout is interpreted as UNSAT or as a proof.
Inputs, exploratory scripts, and logs are preserved in
[the source archive](../data/spectrum/1483_rank_descent_sources.tar.gz).
