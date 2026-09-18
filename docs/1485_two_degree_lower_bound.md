# A lower bound from mixed high five-cycles

Research note, 18 September 2026. Use the finite structure and uniform
fiber theorems in [the graph note](1485_graph_research.md), the moments
in [the two-degree note](1485_two_degree_research.md), and the strict
degree decrease in [the projection note](1485_image_research.md).

**Theorem.** Every finite E1485 magma with exactly two translation
degrees `r<s` satisfies

\[
 \boxed{s\ge 2r.} \tag{1}
\]

This does not assume that the sharp degrees of the high vertices are
constant. We also obtain `k_a≤s−r` for every high vertex `a`.

The final bounds below classify the parameters for `r≤9`. The subsequent
[small-degree completion](1485_small_degree_completion.md) extends this
to `r≤11`, including the exclusion of every semiprime with smaller
prime factor eleven.

Write `Z,H` for the central and high sets, with sizes `m,h`, and put
`t=s−r>0`. Let `k_a` be the common number of central predecessors
and central successors of a high vertex `a`. The established counts are

\[
 m+h=rs,\qquad
 \sum_{a\in H}k_a=mr,\qquad
 \sum_{a\in H}k_a^2=m^2,\qquad h\ge r^2. \tag{2}
\]

## Good and bad high paths

A high vertex `a` has `s−k_a` high successors. Each high edge `a→b`
has exactly `r−k_b` good high extensions: its good extensions form a
translation fiber of size `r`, with exactly `k_b` central elements.
Consequently every high edge has exactly `t` bad high extensions.
Dually, each high edge has exactly `t` bad high predecessors.

Every bad path has a central good replacement middle. Indeed, if
`a→b→c` is bad and `c=b*x`, then `b∈Row(a)` and
`P_x(b)=a*c≠b`; strict degree decrease gives `d(a*c)<d(b)`.
With only two degrees, `b` is high and `a*c` is central.

Thus high endpoints with no central common middle have exactly one
high middle, and their high path is good. High endpoints with a central
common middle have only bad high paths.

There are exactly

\[
 G=h^2-mr^2 \tag{3}
\]

good high two-edge paths. To see this, there are `h²` pairs of high
endpoints. Each central middle has `r` high predecessors and `r` high
successors, and all `r²` resulting paths are good. Uniqueness of good
paths makes these `mr²` endpoint pairs disjoint. The other endpoint
pairs have their unique good middle in `H`.

## Central closures identify the exceptional bad extensions

For any high path `a→b→c→d` admitting a central closure `d→z→a`,
the two adjacent paths `a→b→c` and `b→c→d` have the same type.
This follows twice from the five-cycle law in `a,b,c,d,z`: all paths
containing `z` are good, and either of the two remaining paths forces
the other to be good.

Fix a bad high path `a→b→c`. Each central predecessor `z` of `a`
gives a bad extension `d=c*z`, by that observation. Distinct `z`
give distinct `d`, since two central paths `d→z→a` with the same
endpoints would violate unique goodness. Conversely, if a bad extension
`d` has a central middle `z` back to `a`, centrality in the path
`c→d→z` gives `d=c*z`.

Exactly `k_a` of the `t` bad extensions therefore have a central
return middle; the other `t−k_a` have a unique high return middle.
In particular `k_a≤t`. Such a bad path exists from every high vertex:
it has `s−k_a≥s−r>0` high successors, and each high edge has `t>0`
bad extensions.

## Two counts of mixed high five-cycles

All cycle counts below count ordered vertex tuples; repeated vertices
are allowed. For a high five-cycle with vertices `v_0,...,v_4`, let
`b_i` be one when its path `v_i→v_{i+1}→v_{i+2}` is bad, and zero
when it is good, with indices modulo five.

Let `N` count high five-cycles with `b_0=1,b_1=0`. A mixed high
three-edge path has no central return middle, by the central-closure
observation, so it completes uniquely to a high five-cycle. Each good
high path has exactly `t` bad predecessors. Hence

\[
 N=tG=t(h^2-mr^2). \tag{4}
\]

Let `B_0` count high five-cycles with `b_0=b_1=1,b_3=0`. For each
bad path starting at `a`, the preceding section gives exactly `t−k_a`
bad extensions with a high good return path. The number of bad paths
starting at `a` is `t(s−k_a)`. Thus

\[
 B_0=t\sum_{a\in H}(s-k_a)(t-k_a)
 =t\bigl(hst-(s+t)mr+m^2\bigr). \tag{5}
\]

The five-cycle law forbids an isolated bad path: if `b_i=1`, at least
one of `b_{i-1},b_{i+1}` is one. A mixed cyclic pattern of length five
therefore consists of a single block of two, three, or four bad paths.
Each such pattern has exactly one bad-to-good boundary. The number of
positions with two consecutive bad paths and an opposite good path is
respectively one, two, or one. The all-good and all-bad patterns
contribute zero to both counts. Summing over the five possible root
positions gives

\[
 \boxed{B_0\ge N.} \tag{6}
\]

This argument does not require free rotation of vertex tuples: sum the
five indicators on every ordered cycle, and use the fact that cyclic
rotation is a bijection on the complete set of ordered cycles.

## Factoring the difference

Put `δ=h−r²≥0`. Since `m+h=rs` and `s=r+t`, we have
`m=rt−δ`. Equations (4) and (5) become

\[
 \begin{aligned}
 N/t&=r^3(r-t)+3r^2\delta+\delta^2,\\
 B_0/t&=\delta(r^2+rt+t^2+\delta).
 \end{aligned}
\]

Subtracting gives

\[
 B_0-N=t(t-r)\bigl[r^3+(t+2r)\delta\bigr]. \tag{7}
\]

The first factor `t` and the bracket are positive. Equation (6)
therefore forces `t≥r`, which is precisely (1).

There is also an exact equality interpretation. The difference of the
cyclic indicators in the proof of (6) is one exactly for patterns with
three consecutive bad paths, and zero for every other allowed pattern.
Thus `s=2r` holds if and only if no high five-cycle has exactly three
bad paths. This statement alone does not establish constancy of the
sharp degrees or classify the equality case.

## Classifying all two-degree models with minimum degree at most nine

Call the parameters standard if `s=2r`, `m=h=r²`, and every `k_a=r`.
The [constant-sharp-degree theorem](1485_constant_sharp_degree.md)
proves this conclusion whenever all the `k_a` are equal. The older tail
bound in the two-degree note also proves it as soon as **any** `k_a=r`.

Suppose the parameters are not standard. If `r=1`, then all `k_a=1`
and the constant-sharp-degree theorem is a contradiction. Thus `r>1`,
and the [sharp-degree-one exclusion](1485_k1_exclusion.md) gives
`k_a≥2`. In fact

\[
 2\le k_a\le r-2 \quad\text{for every }a\in H. \tag{8}
\]

Indeed, `k_a=r` has already been excluded. If `k_a=r−1`, the tail
bound `#{v:k_v>r-k_a}≤k_a²` would give `h≤(r−1)²`, since all
`k_v≥2`. This contradicts `h≥r²`. In particular (8) already excludes
nonstandard parameters at `r=2,3`.

For `r≥4`, apply `(k_a-2)(k_a-(r-2))≤0` and the two moment
identities. They imply

\[
 m^2\le r^2m-2(r-2)(rs-m),
\]

or, on writing `A=r²+2r−4`,

\[
 m^2-Am+2r(r-2)s\le0.
\]

The quadratic has nonnegative discriminant. Combining this with
`s≥2r` yields the necessary condition

\[
 \boxed{A^2\ge 16r^2(r-2).} \tag{9}
\]

For `r=4,5,6,7,8,9`, the differences between the two sides of (9)
are respectively `−112, −239, −368, −439, −368, −47`. All are
negative. We conclude:

\[
 \boxed{r\le9\quad\Longrightarrow\quad
 s=2r,\quad m=h=r^2,\quad k_a=r\text{ for all }a\in H.} \tag{10}
\]

This is a classification of the cardinality and sharp degrees, not an
isomorphism classification of the multiplication tables. It also does
not cover models with three or more distinct translation degrees.

## Spectrum consequences and the remaining numerical gap

If `p<q` are distinct primes and an E1485 model has order `pq`, then
it has precisely the translation degrees `p,q`: a degree-one vertex
would give a constant-row model and hence power-of-two order. Equation
(10) therefore excludes every such order with `p∈{2,3,5,7}`, since
`q=2p` is not prime.

More generally, semiprime parameters cannot be standard. For `p≥3`
the quadratic argument above gives the sharper necessary interval

\[
 \boxed{2p\le q\le
 \left\lfloor\frac{(p^2+2p-4)^2}{8p(p-2)}\right\rfloor.} \tag{11}
\]

For example, this bound alone leaves `q=23` when `p=11`, and
`q=29,31` when `p=13`. The subsequent small-degree completion excludes
the former; the latter are still unresolved here, **not** constructed
models. Combining these notes, any nonstandard two-degree model must
have `r≥12` and nonconstant sharp degrees.

## An additional count for the equality case

Let `C_good` be the number of ordered high five-cycles all of whose
two-edge paths are good. Fix a good high path `a→b→c`. The edge
`b→c` has `r−k_c` good high extensions. Exactly `k_a` of them
have a central return middle from the final vertex to `a`, by the
same central-closure correspondence used above. Each remaining extension
has a unique high good return path. The five-cycle law makes all five
paths of the resulting cycle good: the good paths at positions `0,1,3`
force those at positions `2,4`.

Hence a good path from `a` to `c` lies in exactly `r−k_a−k_c` such
cycles. The endpoint relation `E=J-CB` from the two-degree note has
row and column sums `h-rk_a`. Summing, using the moments, gives

\[
 \begin{aligned}
 C_{\rm good}
 &=r(h^2-mr^2)-2\sum_a k_a(h-rk_a)\\
 &=r\bigl(h^2-2hm+2m^2-mr^2\bigr)\ge0. \tag{12}
 \end{aligned}
\]

In particular, if `s=2r` and `δ=h−r²=r²−m`, then
`C_good=rδ(5δ-r²)`. Thus either the parameters are standard (`δ=0`),
or `δ≥r²/5`. This is a further restriction on the still-open equality
case, not a proof that it is standard.
