# Two translation degrees and a constant sharp degree

Research note, 18 September 2026. We use the finite degree and fiber
theorems in [the graph note](1485_graph_research.md), the moments in
[the two-degree note](1485_two_degree_research.md), and the strict
degree decrease proved in [the projection note](1485_image_research.md).

**Theorem.** Suppose a finite E1485 magma has exactly two translation
degrees `r<s`, and every high vertex has the same number `k` of central
successors. Then

\[
 k=r,\qquad s=2r,\qquad |Z|=|H|=r^2.
\]

In particular, the cases `(r,s,k)=(4,6,2)` and `(5,7,2)` do not exist.
This theorem assumes constancy of the sharp degree on the high vertices;
it does not assert that this constancy holds in every two-degree model.

## Preliminary counts and path types

Write `Z,H` for the central and high vertices, of cardinalities `m,h`.
Weighted balance gives the same sharp in-degree `k` as sharp out-degree
at every high vertex. The two moments give

\[
 hk=mr,\qquad hk^2=m^2,
\]

and hence

\[
 m=rk,\qquad h=r^2,\qquad s=r+k. \tag{1}
\]

Each high vertex therefore has exactly `r` high successors and `r`
high predecessors, as well as `k` central successors and predecessors.

Every high edge `a→b` has exactly `r−k` good high extensions and `k`
bad high extensions. Indeed, the good extensions form the fiber
`{c:a*c=b}`, of size `n/d(a)=r`, and exactly `k` of them are central:
the central successors of `b`. There are `r` high successors of `b`
in all. The same counts hold for extensions at the other end.

We also use the following consequence of strict degree decrease:

> A bad two-edge path has a high middle, and its good replacement middle
> is central.

For if `a→b→c` is bad, write `c=b*t`. Then `b∈Row(a)`, and
`P_t(b)=a*(b*t)=a*c≠b`, so `d(a*c)<d(b)`. With only two degree values,
this says precisely that `b` is high and `a*c` is central.
Consequently a high two-edge path is bad if and only if its endpoints
also admit a central middle. If high endpoints have no central middle,
their unique good middle is high, and every high middle is good.

## Closing a path through a central vertex preserves its type

Suppose `a→b→c→d` is a high path and `d→z→a` with `z` central.
In the five-cycle

\[
 a\to b\to c\to d\to z\to a,
\]

the paths `a→b→c` and `b→c→d` have the same type: either both are
good, or both are bad. If the first is good, combine it with the good
path `c→d→z` in the five-cycle law. Conversely, if the second is good,
combine it with the good path `z→a→b` in that law.

Now fix a bad high path `a→b→c`. For each of the `k` central
predecessors `z` of `a`, put `d=c*z`. This is high, and
`c→d→z→a` closes the preceding five-cycle. Thus `b→c→d` is bad.
Distinct choices of `z` give distinct `d`: otherwise the two central
middle paths `d→z→a` would violate unique goodness.

These `k` choices exhaust all bad high extensions of `b→c`.
We have proved:

\[
 \boxed{\text{If }a\to b\to c\text{ and }b\to c\to d
 \text{ are bad, then }d*a\text{ is central}.} \tag{2}
\]

## Every high five-cycle has only one path type

Take a five-cycle entirely inside `H`, and give each of its five
consecutive two-edge paths a good or bad type. The five-cycle law says
that each bad path has a bad neighbor among the two adjacent paths:
otherwise those neighbors would force it to be good.

Equation (2) says that two adjacent bad paths force the opposite
two-edge path to be bad as well. Explicitly, for a cycle with vertices
`a,b,c,d,e`, if `a→b→c` and `b→c→d` are bad, then `d*a` is central,
so the high path `d→e→a` is bad.

These two rules imply that any bad path makes all five paths bad.
To check this, number the paths cyclically `0,1,2,3,4`. A bad path has
a bad neighbor, so rotate the numbering to make `0,1` bad. Then `3`
is bad by (2). Path `3` needs a bad neighbor `2` or `4`. If `2` is
bad, the adjacent pair `1,2` forces `4` bad. If `4` is bad, the
adjacent pair `4,0` forces `2` bad. All five are bad in either case.

Thus every high five-cycle is entirely good or entirely bad.

## Mixed paths give the contradiction

If `k<r`, choose a bad high path `a→b→c`, which exists because
`k≥1`. The edge `b→c` also has a good high extension `b→c→d`,
because `r−k>0`.

There cannot be a central middle from `d` to `a`: such a middle would
make these two adjacent paths have the same type, by the central
five-cycle argument above. Therefore the unique good path from `d`
to `a` has a high middle `e`. This closes the high five-cycle

\[
 a\to b\to c\to d\to e\to a,
\]

which has both a bad and a good path, a contradiction. Hence `k=r`.
Equation (1) now yields all conclusions of the theorem.

No assumption that the high adjacency matrix squares to the all-ones
matrix is used. That property can fail even in the allowed case `k=r`.
