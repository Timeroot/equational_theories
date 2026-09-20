# Order forty: thirteen degree-five vertices cannot have three high-sharp partners

Research note, 19 September 2026. This is an **analytic exclusion**
of one sharp-degree distribution in the thirteen/seven branch at order
forty. It uses no finite enumeration or SAT premise and is not yet a
Lean theorem. The other sharp distributions have separate exclusions;
the [completed thirteen/seven theorem](1485_order_forty_thirteen_directions.md#9-the-theorem-and-its-proof-dependencies)
lists the full dependency inventory. This page proves only its
three-high-sharp component.

Use the notation of the
[thirteen-vertex profile note](1485_order_forty_thirteen_profiles.md).
Suppose the seven degree-eight vertices consist of three vertices
`H` with sharp degree three and four vertices `L` with sharp
degree one. Let `D` denote ordinary adjacency inside this seven-point
set, and let `C` denote sharp two-step paths through degree-five
vertices.

The [universal return-matching bound](1485_general_return_matching.md)
forces the `H×H` block of `C` to be all ones. This fills its
row and column sums, so there are no cross-block `C` entries.
The `L×L` block is a permutation matrix, say

\[
C_{ij}=1\quad\Longleftrightarrow\quad j=\pi(i)
\qquad(i,j\in L).                                      \tag{1}
\]

Every high vertex has one internal predecessor and successor;
every low vertex has three. An ordinary internal two-path with no
`C` replacement is good and unique. Consequently

\[
(D^2)_{ij}\le1\quad(j\ne\pi(i)),\qquad
(D^2)_{i,\pi(i)}\le3\quad(i,j\in L).                    \tag{2}
\]

Thus the total number of internal two-paths from `L` to `L`
is at most `4·(3+3)=24`.

## 1. Every high vertex lies between two low vertices

Let `m` count internal edges from `H` to `H`. There are
`3−m` edges in each cross-block direction. For `i∈L`, put

\[
a_i=|D(i)\cap H|,\qquad b_i=|D^{-1}(i)\cap H|.
\]

The number of low-to-low two-paths with low middle is

\[
\sum_{i\in L}(3-b_i)(3-a_i)
=18+6m+\sum_i a_i b_i.                                 \tag{3}
\]

If `m≥2`, this already exceeds 24. If `m=1`, at least one
of the three high vertices has both its predecessor and successor
in `L`: a single high-to-high edge can affect at most two high
vertices. That vertex supplies an additional low-to-low two-path,
so the total is at least 25. Both alternatives contradict (2).
Therefore

\[
m=0,\qquad \sum_i a_i=\sum_i b_i=3.                     \tag{4}
\]

Each high vertex now gives a path `i→h→l` with low endpoints.
Bad-extension balance on the two edges of this path, as proved in
[the return-matching note](1485_general_return_matching.md#5-bad-extension-balance-on-every-internal-edge),
gives

\[
\boxed{b_i=a_l=\mathbf1_{\{l=\pi(i)\}}.}                 \tag{5}
\]

Indeed the bad predecessors of `i→h` are precisely its `b_i`
high predecessors, whereas its bad extension is present exactly
when `l=π(i)`. The edge `h→l` gives the other equality.
In particular, wherever both `a_i,b_i` are positive, both equal one.

## 2. The high edges meet the same three low vertices

Suppose `a_i=0`. All three internal successors of `i` lie in
`L`. Its number of two-paths ending in `L` is

\[
9-\sum_{x\in D(i)\cap L}a_x\ge6,
\]

by (4). The row bound (2) is six, so equality holds throughout.
In particular `(D²)_{i,π(i)}=3`. All three successors of `i`
are therefore predecessors of `π(i)`, filling its whole internal
in-degree. Thus `b_{π(i)}=0`. The dual column argument proves
the converse. Hence

\[
a_i=0\quad\Longleftrightarrow\quad b_{\pi(i)}=0.          \tag{6}
\]

Let `P={i:a_i>0}`, `Q={i:b_i>0}`, and `I=P∩Q`.
Equation (6) says `π(P)=Q`, so `|P|=|Q|=s`, say. Write
`h=|I|`. All entries of `a,b` on `I` equal one. For each
`i∈I`, its unique high successor has low successor `π(i)` by
(5), and (5) also puts `π(i)` in `I`. Thus `π(I)=I`.

The remaining high two-paths run from `P∖I` to `Q∖I`, but
avoid the endpoint `π(i)` at a source `i∈P∖I`, again by (5).
The two residual sets have the same size `s−h`; that size cannot
be one. If it is zero, (4) immediately gives `s=h=3`.

If it is at least two, the union bound
`|P∪Q|=h+2(s−h)≤4` forces `h=0,s=2`. The two positive
`a` entries then have values one and two. The vertex with value
two has two high successors. Their low successors must both be
the sole member of `Q` other than its forbidden `π` target.
This produces two distinct internal middles at an off-`π` pair,
contradicting (2).

Only the first alternative remains. There are three active low
vertices `M` with `a_i=b_i=1` and one inactive low vertex `o`
with `a_o=b_o=0`. The permutation `π` fixes `o` and preserves
`M`.

## 3. The remaining internal graph has an impossible five-walk

The equality argument for `a_o=0` shows that all three active
vertices are successors of `o`; its dual shows they are all
predecessors of `o`. Each active vertex has two low successors,
one of which is `o`, and two low predecessors, one of which is
`o`. The remaining edges on `M` therefore form a permutation,
say `ρ`.

For active `i,j`, there is one internal two-path via `o`, a
possible path via an active low vertex, and a possible path via
the unique high successor of `i`. Equation (5) identifies the
last endpoint. Hence

\[
(D^2)_{ij}=1+\mathbf1_{\{j=\rho^2(i)\}}
             +\mathbf1_{\{j=\pi(i)\}}.
\]

Off-`π` uniqueness in (2) forces

\[
\pi|_M=\rho^2.                                          \tag{7}
\]

Choose any `j∈M` and choose `i∈M` different from the at most
two values `ρ⁻²(j)` and `ρ³(j)`. This is possible because
`|M|=3`. Consider the closed ordinary five-walk

\[
(o,i,o,j,\rho(j)).                                      \tag{8}
\]

Its two-step path beginning at the first `o` is bad, since
`C_{oo}=1`. The two-step paths beginning at the second `o`
and at `j` are good, since one endpoint is `o` and the other
is active, while `π` fixes `o` and preserves `M`. The other two would be bad precisely if
`j=π(i)=ρ²(i)` or `i=π(ρ(j))=ρ³(j)`, respectively; the
choice of `i` excludes both. Thus (8) has exactly one bad
two-step position.

This is impossible by E1485 five-cycle goodness: two good two-step
paths with starting positions two apart force the intervening
two-step path to be good. Apply it to the two good positions
adjacent to the allegedly bad position. Repeated vertices in a
closed five-walk are allowed by the identity.

This contradiction proves that the sharp distribution
`(1,1,1,1,3,3,3)` cannot occur. In (1) of the thirteen-vertex
profile note, the remaining possibilities are therefore `k=0,1,2`.
