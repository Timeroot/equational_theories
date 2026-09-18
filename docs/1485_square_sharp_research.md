# Involutive squaring and sharp square edges

Research note, 18 September 2026. Let `S(x)=x*x`, and assume E1485
and E151, so `S²=id`. The assertion that every edge `x→S(x)` is sharp
remains unproved for finite models. This note records two finite
reformulations and a countable counterexample: the assertion is not an
unrestricted equational consequence of E1485 and E151.

## Finite reformulations

Let the model be finite, of order `n`, and let `d(x)` be its common row
and column degree. For any ordinary path `a→u→b`, the strict projection
descent in [the image note](1485_image_research.md) gives

\[
 a*b\ne u\quad\Longrightarrow\quad d(a*b)<d(u).
\]

Indeed write `b=u*c` and apply that result to `a*(u*c)`. Consequently
`S(x)` is the unique vertex of minimum degree in the set of reciprocal
ordinary neighbors of `x`: this set consists of the possible middles
of paths `x→u→x`, and its good middle is `S(x)`. E151 says that this
minimum-neighbor assignment is involutive.

For each fixed `c`, define

\[
 Q_c(x)=S(x)*(x*c).
\]

Since `S(x)→x`, strict projection descent also gives

\[
 d(Q_c(x))\le d(x),\qquad
 Q_c(x)\ne x\ \Longrightarrow\ d(Q_c(x))<d(x).
\]

It follows that the following statements are equivalent in a finite
E1485+E151 model:

1. Every square edge `x→S(x)` is sharp.
2. Every `Q_c` is the identity map.
3. Every `Q_c` is injective.
4. Every `Q_c` is surjective.

For (1) versus (2), replace `x` by `S(x)` and use `S²=id`.
For the remaining implications, a finite injective or surjective map is
a permutation. Summing the displayed degree inequality over all `x`
then excludes any strict decrease. Equivalently, (1) says
`d(x)d(S(x))=n` for every `x`, by the sharp-edge degree criterion.
These are reformulations, not proofs that the equivalent assertions hold.

## A countable counterexample

Use the five-color relaxed structure `M5` in
[the involutive research note](1485_involutive_research.md), with its
allowed-good-path relation `G`. Take five distinct vertices with colors

| Vertex | a | s | c | t | v |
|---|---|---|---|---|---|
| Color | 0 | 1 | 4 | 1 | 2 |

Require the good paths expressing

\[
 a*a=s,\qquad s*s=a,\qquad s*c=t,\qquad a*t=v.
\]

Their edge set is exactly

\[
 a\to s,\quad a\to v,\quad v\to t,\quad
 s\to a,\quad t\to c,\quad s\to t.
\]

All required color triples belong to `G`. The complete list of allowed
good paths in this seed is

\[
 (a,s,a),\ (a,v,t),\ (s,a,s),\ (s,a,v),\
 (s,t,c),\ (v,t,c).
\]

Their ordered endpoint pairs are distinct, so the seed is consistent.
The established greedy construction extends it to a countable E1485
magma satisfying E151. Every specified edge is part of a required good
product path, so these are actual edges of the associated magma graph.
In the extension,

\[
 a*(S(a)*c)=a*(s*c)=a*t=v\ne s=S(a).
\]

Thus `a→S(a)` is not sharp. In particular, unrestricted equational
proof search cannot establish the finite square-edge assertion; a proof
must use a property absent from these countable models.
