# Nine central elements: degree-class capacity bounds

Research note, 20 September 2026. These are analytic necessary
conditions at order forty, not an exclusion of the remaining sixteen-
or seventeen-top branches. Assume minimum degree four, nine central
elements, and at least one degree-five vertex with three top neighbors
in each direction. The degree classes are `Z,A,B,T` of degrees
`4,5,8,10`. Split `A=A_3⊔A_4` by its top-neighbor count, and
write `a_3,a_4` for their cardinalities.

**Subsequent status:** at order forty this whole size-three-profile
branch is now excluded by the
[sixteen-top](1485_nine_central_sixteen_exclusion.md) and
[seventeen-top](1485_nine_central_seventeen_degree_counts.md) proofs,
together with the earlier eighteen-top exclusion. The bounds below
remain useful intermediate lemmas, not a list of currently open cases.

Let `p,q` count global `P`-triples and `C`-triples, and let `s`
count tops of type `(3,3)`. The
[central profile argument](1485_nine_central_three_profile.md)
gives `3≤p,q≤6`, with the exact exceptional-set and zero-count
formulas used below.

The [general maximal-grid theorem](1485_maximal_first_output_grid.md)
also gives the unconditional bound `a_3≤4` in this branch. Its
proof shows that the maximal-block endpoint rectangle contains at
least nine centrally valued pairs, unavailable to degree-five products.

## 1. A sharper total bound on three-neighbor vertices

Each member of `A_3` is represented by exactly six ordered top
pairs. Both endpoint profiles partition nine into three triples,
so all these pairs lie in the `p` by `q` rectangle whose first
index has `P`-size three and second has `C`-size three.

That rectangle contains the `s` by `s` subrectangle indexed on
both sides by `(3,3)` tops. The global matrix with `C`-triple
sources and `P`-triple targets has at most `(6−p)(6−q)` zeros,
by equation (8) of the profile note. Thus at least
`s²−(6−p)(6−q)` pairs in the smaller square are centrally valued.
They cannot represent a member of `A_3`. Distinct products have
disjoint endpoint sets, so

\[
                  \boxed{6a_3\le pq-s^2+(6-p)(6-q).}     \tag{1}
\]

The two differently oriented rectangles in this argument must not
be identified. Only their common `(3,3)` square is used. For
example `(p,q,s)=(5,5,3)` gives `a_3≤2`, while `(6,6,4)` gives
`a_3≤3`.

There is also a stronger bound in many count tables. Put

\[
 L=N_{31}+2N_{32}+3N_{33},\qquad
 R=N_{13}+2N_{23}+3N_{33}.
\]

Every central row has a `C`-triple, and every central column a
`P`-triple: four blocks of size at most two cannot cover nine.
The opposite blocks of these indexed families therefore cover `Z`
with multiplicities `λ_z,μ_z≥1`, whose sums are `L,R`.
Their centrally valued endpoint count is
`Σλ_zμ_z≥L+R−9`. The same good-pair budget gives

\[
                       \boxed{6a_3\le pq-L-R+9.}         \tag{1a}
\]

In particular the seventeen-top table

\[
                   \begin{pmatrix}2&0&0\\1&8&2\\0&1&3\end{pmatrix}
\]

and its transpose are impossible: they have `(p,q,L,R)=(4,5,11,13)`,
so (1a) would give `6a_3≤5` despite `a_3≥1`. This is an analytic
exclusion, not a mixed-integer solver result.

## 2. Six triples force small top profiles at adjacent degree-eight vertices

Suppose `p=6` and `a∈A_3`. The complement-column tilings of the
profile note use every small `P`-block, so exactly `|T|−6` top
inputs of `R_a` have top outputs. Its two remaining output values
are the two sharp predecessors `b` of `a`, both in `B`.

For such a sharp edge `b⇒a`, its input fiber is exactly
`R_a^{-1}(b)=Col(b)`. The six remaining top inputs therefore
split between the top predecessor sets of these two vertices.
Each set has at least three members, since its `P`-blocks
partition nine and every block has size at most three. Both have
exactly three members. Dually,

\[
 \begin{split}
 p=6,\quad b\Rightarrow a\in A_3
     &\quad\Longrightarrow\quad |TopPred(b)|=3,\\
 q=6,\quad a\in A_3\Rightarrow b
     &\quad\Longrightarrow\quad |TopSucc(b)|=3.
 \end{split}                                           \tag{2}
\]

Each implication needs only its indicated one-sided triple count,
not both `p=q=6`.

## 3. A global bad-path count without edgewise balance

For `x∈B`, let `I_x,O_x` be its top predecessor/successor
counts, and `j_x^-,j_x^+` its sharp predecessor/successor counts
in `A`. Put `D_x^+=8−O_x−j_x^+`, the number of internal
successors in `B`. Finally let `e_x^+` count its sharp successors
lying in `A_3`.

Write `g_x` for the number of top pairs with product `x`, and
`τ_x` for the number of bad internal two-edge paths with middle
`x`. For an internal edge `x→y`, the five-element fiber
`R_y^{-1}(x)` has all `8−I_x` non-top predecessors of `x`
except its `η(x,y)` bad internal predecessors. Hence its number
of top inputs is `I_x−3+η(x,y)`. Counting the four-element fibers
`L_u^{-1}(x)` over all `I_x` top predecessors `u` gives exactly

\[
 g_x=I_x(4-j_x^+)-D_x^+(I_x-3)-\tau_x.                 \tag{3}
\]

To bound the sum of `τ_x`, count bad paths by their starting
vertex instead. Their degree-five replacements lie on sharp paths
through `A`. The distinct available endpoints number

\[
 \sum_{a:x\Rightarrow a}(5-|TopSucc(a)|)=j_x^++e_x^+.
\]

The endpoints are distinct by uniqueness of good middles. With
`D_x^+` possible internal middles, there are at most
`D_x^+(j_x^++e_x^+)` bad paths starting at `x`. Summing (3)
therefore proves

\[
 \boxed{\sum_{x\in B}g_x\ \ge
 \sum_{x\in B}\bigl[I_x(4-j_x^+)
      -D_x^+(I_x-3+j_x^++e_x^+)\bigr].}                \tag{4}
\]

Consequently, writing `h=|T|`,

\[
 h^2\ge144+6a_3+12a_4+
 \sum_{x\in B}\bigl[I_x(4-j_x^+)
      -D_x^+(I_x-3+j_x^++e_x^+)\bigr].                \tag{5}
\]

Only the **summed** bound (4) is justified: its summands are not
individual lower bounds on `g_x` and must not be separately clipped
at zero. No equality of bad extension and predecessor counts on
individual edges is assumed. The degree-three/four top profiles
in `A` give the exact global sums
`Σj_x^+=2a_3+a_4` and `Σe_x^+=2a_3`.
