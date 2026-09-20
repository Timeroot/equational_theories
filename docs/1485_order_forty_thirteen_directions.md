# Order forty, thirteen degree-five vertices: the final affine profiles are impossible

Research note, 20 September 2026. Continue with the single internal
incidence type in
[the thirteen-vertex reduction](1485_order_forty_thirteen_profiles.md#7-a-finite-incidence-reduction-leaves-one-internal-type).
That incidence reduction has a stated finite-check dependency.
The arguments on this page are analytic consequences of it. They
exclude its last incidence type, completing the thirteen/seven case
subject to the finite-incidence dependencies stated in that reduction.

Write `l` for the unique sharp-degree-one partner and `S_i,R_i`
for the six sharp-degree-two partners, indexed modulo three as in
the incidence table. Let `a_l` be the sharp-loop degree-five vertex
at `l`, with profile `(P_{p_0},Q_{q_0})`. The three `S_i`
are exactly the ordinary internal neighbors of `l`.

## 1. Affine coordinates and the attached rank-one profiles

Use the [single-coset affine coordinates](1485_order_forty_single_coset.md)
on the top grid, with vector coordinates `p,q∈F₂²` and central
labels

\[
C(p,q)=p+q,\qquad H(p,q)=L(p+\Omega q)+\delta.             \tag{1}
\]

Here `L` is invertible, `Ω` has order three, and the possible
offset `δ` will not affect any direction calculation. Write the
partner profiles as

\[
U_b=\{(B_bq+r_b,q):q\in F_2^2\},\qquad
V_b=\{(p,A_bp+s_b):p\in F_2^2\}.
\]

Their central-label transversality gives

\[
B_b+\Omega\text{ invertible},\qquad I+A_b\text{ invertible}.
                                                               \tag{2}
\]

None of the `B_b,A_b` is zero, by the no-`P`/`Q`-line theorem.
The internal edges `S_i→l` have top return fibers of size two,
obtained by removing `P_{p_0}` from `U_{S_i}`. Consequently each
`U_{S_i}` meets that line twice. Dually each `V_{S_i}` meets
`Q_{q_0}` twice. Thus their linear parts have rank one; their
projections have supports

\[
\{p_0,p_0+v_i\},\qquad\{q_0,q_0+d_i\},
\qquad v_i,d_i\ne0.                                      \tag{3}
\]

For a rank-one map over `F₂`, invertibility of `I+A` is
equivalent to `im A=ker A`. Applying the same observation to
`Ω⁻¹B` gives

\[
\operatorname{im}A_i=\ker A_i=\langle d_i\rangle,
\qquad\operatorname{im}B_i=\Omega\ker B_i
=\langle v_i\rangle.                                    \tag{4}
\]

Since `Ω` fixes no nonzero direction, `B_i` has distinct kernel
and image; thus `I+B_i` has rank one and image `ker B_i`.
Similarly `I+ΩA_i` has rank one and image `ker A_i`. Therefore
the two central-label sets on these profiles have directions

\[
C(U_{S_i}):\Omega^2v_i,
\qquad H(V_{S_i}):Ld_i.                                  \tag{5}
\]

## 2. Four good pairs align these directions

The support rectangle in (3) contains the occupied cell
`(p_0,q_0)`. For any hole in that support, there are two choices
of first top endpoint in `U_{S_i}` and two choices of second
endpoint in `V_{S_i}`. On each of those two-element sets, its
central label runs once through its full two-element label image.

Put `c_i=|C(U_{S_i})∩H(V_{S_i})|`, and let `h_i` count holes
in the support rectangle. Exactly `c_i` of each four endpoint
pairs are central-valued. The others have no degree-five
replacement and hence are good pairs with product `S_i`.
Thus its already established good-pair count is

\[
4=g_{S_i}=h_i(4-c_i),\qquad c_i\in\{0,1,2\}.             \tag{6}
\]

The case `c_i=1` is impossible. For `c_i=0` there is one
active hole; for `c_i=2` there are two. In both cases the
two central-label images have the same direction. Equation (5)
therefore gives

\[
\boxed{v_i=K d_i,\qquad K=\Omega L.}                     \tag{7}
\]

## 3. The three attached directions are neither all distinct nor all equal

The canonical incidence type has top-valued products `l*S_i`
and `S_i*l`. Their top middles are consequently unique:

\[
|V_l\cap U_{S_i}|=|V_{S_i}\cap U_l|=1.                  \tag{8}
\]

Using the affine graphs, (8) means `I+A_l B_i` and
`I+B_l A_i` are invertible. The determinant formula for a
rank-one map, together with (4) and (7), rewrites these conditions as

\[
B_l d_i\in\langle d_i\rangle,
\qquad A_l Kd_i\in\langle Ld_i\rangle.                  \tag{9}
\]

If the three nonzero directions `d_i` were distinct, both
`B_l` and `L⁻¹A_lK` would preserve all three one-dimensional
subspaces of `F₂²`. Such a map is scalar. The zero scalar is
excluded by the no-line theorem, so

\[
B_l=I,\qquad A_l=LK^{-1}=\Omega^2.
\]

Both low profiles would then meet every opposite profile line
exactly once. Each of the three holes could contribute at most
one good top pair with product `l`, giving `g_l≤3`, contrary
to `g_l=6`.

The three directions cannot all coincide either. The predecessor
profiles of two different attached vertices intersect only inside
`P_{p_0}`: an intersection point outside it would give two
ordinary degree-eight middles on a path to `l`, without the only
possible lower replacement `a_l`. If all directions coincided,
the three profiles would therefore contribute six distinct points
to the same four-point line `P_{p_0+Kd}`. This is impossible.

Consequently

\[
\boxed{\{d_0,d_1,d_2\}\text{ has multiplicities }2+1.}     \tag{10}
\]

## 4. Two support rectangles and three possible low-slope pairs

Let `d` be the repeated direction and `e` the other direction.
The two attached predecessor profiles with direction `d` partition
the union of `P_{p_0}` and `P_{p_0+Kd}`; their successor
profiles partition the corresponding two `Q` lines. Their
central-label images are complementary pairs of parallel lines.
Thus they have the same `c_i` and the same hole count in their
common support rectangle. By (6), that rectangle has one or two
holes. The remaining attached profile has one or two holes in
its support rectangle.

The two rectangles meet only at the occupied cell `(p_0,q_0)`.
Hence their hole counts are either `(1,1)`, `(1,2)` or `(2,1)`;
in the first case the third hole is outside both rectangles.

There are also few possibilities for the low linear parts.
Equation (9) makes `B_l` and `T=L⁻¹A_lK` diagonal in the
basis `d,e`. Each is nonzero. For `B_l`, condition (2) leaves
the identity and exactly one of the two rank-one projections:
its image must be `Ω` times its kernel. For `T`, the same
argument leaves the identity and exactly one projection, using
the order-three map `L⁻¹ΩL`. The two identity choices together
were already excluded by `g_l>3`. Thus at most **three pairs
of low linear parts** remain for fixed `L,d,e`. Their affine
offsets have not been determined by this argument.

Finally the line of `p_0` and the line of `q_0` each contain
at least one hole: the three attached rank-one profiles contribute
six incidences on each, exceeding the four incidences available
on a fully occupied line. No line contains all three holes,
since all seven affine non-line partner profiles meet it in at
most two points, whereas a three-hole line would require sixteen
incidences. Since `(p_0,q_0)` is occupied, its row and column
hole counts are `(1,1)`, `(1,2)` or `(2,1)`.

## 5. The low good-pair count sharply restricts the holes

Suppose first that both low profiles have rank one. Their two
central-label images have size two. As in (6), if they meet in
`c` labels and their support rectangle contains `h` holes, then

\[
6=g_l=h(4-c).                                             \tag{11}
\]

If their directions agree, `c` is zero or two, so (11) forces
`c=2` and `h=3`. All three holes are in the low rectangle.
The last paragraph of Section 4 then puts both `p_0` and `q_0`
in its projections. Its fourth, occupied cell is therefore
`(p_0,q_0)`. The equal-direction condition is exactly the
support relation `Δp=KΔq` from (7). Every attached support
rectangle has this same relation and contains `(p_0,q_0)`:
it is either the low rectangle itself or meets it only at that
occupied cell. It would thus have three holes or none, contrary
to (6).

Consequently two rank-one low profiles have **different central
directions**, and (11) gives `c=1,h=2`. Those two active holes
must be opposite corners. Indeed, if they had the same `P`
coordinate, among the two predecessor-profile points on that
line the one whose central label lies outside the successor
label image would contribute two good pairs at each hole.
Four good pairs with the same first endpoint exceed the low
fiber bound three. The dual argument excludes the same `Q`
coordinate. The third hole is outside the rectangle. At least
one of its projection pairs contains `p_0` or `q_0`, respectively:
otherwise the lone outside hole would have to lie both on
`P_{p_0}` and on `Q_{q_0}`, at the occupied cell.

Suppose instead that precisely one low profile has rank two.
For example, if `U_l` has rank two, Section 4 gives `B_l=I`,
so its central label is constant. Each hole contributes at most
two good pairs, since `V_l` has rank one. Thus all three holes
lie in the low support and each contributes two noncentral
pairs. Their `P` coordinates must be distinct, again by the
low fiber bound three. Dually, if only `V_l` has rank two,
the three holes have distinct `Q` coordinates.

## 6. Both low profiles cannot have rank one

We now exclude the remaining rank-one/rank-one possibility
analytically. Translate the profile labels so that `p_0=q_0=0`.
Keep `d` for the repeated attached direction and `e` for the
single direction, and write

\[
a=Kd,\quad b=Ke,\quad c=a+b,\quad f=d+e.
\]

First the low rectangle has *crossed* directions: up to duality,
its `P` difference is `a`, and its `Q` difference is `e`.
Here is a short verification of this claim. For the two rank-one
low maps in Section 4, `B_l` has image `Ω` times its kernel,
and `T=L^{-1}A_lK` has image `L^{-1}ΩL` times its kernel.
If `Ωd=e`, their images are respectively `e,e` when `L`
commutes with `Ω`, and `e,d` otherwise. The latter three
choices of `L` are involutions; they make the two low central
directions agree and were excluded in Section 5. Among the
commuting choices `L=I,Ω,Ω²`, the choice `Ω` also aligns
the central directions. For `L=I` the support differences are
`(a,e)`; for `L=Ω²` they are `(b,d)`. When `Ωe=d`, the
same calculation swaps these two outcomes. The second outcome
is dual to the first. This proves the claim without imposing any
unjustified change of the central alphabet.

Thus the low rectangle's `P` pair is either `{0,a}` or
`{b,c}`, and its `Q` pair is either `{0,e}` or `{d,f}`.
Section 5 says that at least one pair contains zero.

### 6.1. Forcing the low rectangle to contain the occupied origin

Suppose its pairs are `{0,a}` and `{d,f}`. Its two opposite
holes, together with the requirement that some hole lie on `Q_0`,
force the third hole to `(b,0)`: it is the only possible hole
in the single-direction attached rectangle. The two alternatives
are therefore

\[
\{(0,d),(a,f),(b,0)\},\qquad
\{(0,f),(a,d),(b,0)\}.                                   \tag{12}
\]

For any `P` line with `h` holes, the total incidence of the
seven predecessor profiles on that line is `4+4h`; the same
formula holds for successor profiles and `Q` lines. Subtract
the low and three attached profiles. In the `P` order
`(0,a,b,c)`, the residual incidence totals for the three `R`
predecessor profiles are

\[
(0,2,6,4).
\]

Consequently all three are rank one: each meets `P_b` twice,
none meets `P_0`, one has support `{a,b}`, and two have
support `{b,c}`. Their direction multiset is `{c,a,a}`.
The successor residual totals, in the `Q` order `(0,d,e,f)`,
are `(2,2,2,6)`. All three successor profiles are therefore
rank one, with supports `{0,f}`, `{d,f}`, `{e,f}` once each.
Their directions are the three distinct vectors `{f,e,d}`.

The argument of Section 2 applies to **any** partner with two
rank-one profiles and `g=4`, not just an attached partner.
Its predecessor and successor directions must be related by `K`.
The two multisets just found contradict this.

For the other possible low rectangle, with pairs `{b,c}` and
`{0,e}`, the holes are
`{(b,0),(c,e),(0,d)}` or `{(b,e),(c,0),(0,d)}`.
The residual predecessor incidence is `(2,0,4,6)`, forcing
three rank-one profiles with directions `{c,a,a}`. The residual
successor incidence is `(0,4,4,4)`, forcing three rank-one
profiles with all three directions. Alignment again fails.
Thus its pairs are `{0,a}` and `{0,e}`. Its two active holes
are exactly `(0,e)` and `(a,0)`.

### 6.2. The third hole gives an incompatible residual incidence

Before adding the third hole, subtracting the low and attached
profiles gives residual predecessor totals `(0,2,2,4)` and
successor totals `(0,0,4,4)`. The third hole adds four to
its `P` and `Q` entries. A profile meets a line at most twice,
so the three `R` profiles contribute at most six to any entry.
It follows that the third hole has `P` coordinate in `{0,a,b}`
and `Q` coordinate in `{0,d}`. It is outside the low rectangle,
leaving exactly

\[
(0,d),\quad(a,d),\quad(b,0),\quad(b,d).                   \tag{13}
\]

In every case the successor residual totals are either
`(4,0,4,4)` or `(0,4,4,4)`. All three successor profiles
are rank one: on the three nonempty lines their supports form
the three pairs, once each. In particular their directions are
all distinct.

If the third hole has `P` coordinate `a`, the predecessor
totals are `(0,6,2,4)` and the predecessor directions are
`{c,b,b}`. If it has coordinate `b`, they are `(0,2,6,4)`
and the directions are `{c,a,a}`. All are rank one in either
case, contradicting the direction alignment. Hence the third
hole is `(0,d)`, and the predecessor totals are `(4,2,2,4)`.

Each rank-two predecessor profile contributes one on every
`P` line, while each rank-one profile contributes even entries.
The number of rank-two profiles is therefore zero or two.
If it were zero, the three rank-one support directions would
have to be all distinct. Their xor would then be zero. But
the support degrees are `(2,1,1,2)` after dividing the incidence
totals by two, so the same xor, counted at the support endpoints,
is `a+b≠0`. This is impossible. Precisely two predecessor
profiles therefore have rank two.

The three successor profiles have supports `{d,e}`, `{d,f}`
and `{e,f}`. They all avoid `Q_0`, so the hole `(a,0)` is
inactive for them. Only the first successor profile sees both
remaining holes `(0,d),(0,e)`. Either of the other two sees
at most one hole; paired with a rank-two predecessor, it could
give at most two good pairs, contrary to `g_R=4`. Thus at
most one predecessor profile can have rank two, contradicting
the preceding paragraph.

We have proved

\[
\boxed{\text{Exactly one low profile has rank two; the other has rank one.}}
                                                               \tag{14}
\]

## 7. The remaining holes occupy the two attached directions

If the predecessor low profile has rank two, Section 5 makes the
three hole `P` coordinates distinct. One is zero. The repeated
attached pair already contributes four incidences on `P_a`,
and the low profile contributes one more, so that line must also
contain a hole. If the third hole were on `P_c`, that line
would require eight incidences: none comes from an attached
profile, and only one from the low profile, leaving seven for
three profiles that each meet it at most twice. Thus the hole
coordinates are exactly `{0,a,b}`. Dually, if the successor
low profile has rank two, the hole `Q` coordinates are exactly
`{0,d,e}`.

## 8. Five hole patterns exclude the remaining case

By duality assume the low predecessor profile has rank two.
The low successor profile has support `{0,v}`, with `v≠0`.
Indeed its support contains zero because some hole lies on `Q_0`,
and all three holes are active for the low profiles. Section 7
puts the holes on the three distinct `P` lines `0,a,b`.
Their `P_0` member is `(0,v)`, since the origin is occupied.
Each other hole has `Q` coordinate zero or `v`.

The repeated attached rectangle `{0,a}×{0,d}` and the single
one `{0,b}×{0,e}` must each contain a hole. These requirements
leave just the following patterns. The last column gives the
residual incidence of the three `R` successor profiles, in the
`Q` order `(0,d,e,f)`, after subtracting the low and three
attached profiles.

| `v` | Three holes | Residual successor incidence |
|---|---|---|
| `f` | `(0,f),(a,0),(b,0)` | `(4,0,2,6)` |
| `d` | `(0,d),(a,0),(b,0)` | `(4,2,2,4)` |
| `d` | `(0,d),(a,d),(b,0)` | `(0,6,2,4)` |
| `e` | `(0,e),(a,0),(b,0)` | `(4,0,4,4)` |
| `e` | `(0,e),(a,0),(b,e)` | `(0,0,8,4)` |

In every row the residual predecessor incidence, in `P` order
`(0,a,b,c)`, is

\[
(1,3,5,3).                                                \tag{15}
\]

Parity forces an odd number of rank-two predecessor profiles;
the entry five excludes three. There is exactly one rank-two
profile. Subtract its contribution `(1,1,1,1)` and divide by
two: the two rank-one support degrees are `(0,1,2,1)`.
Their supports and directions are therefore

\[
U^{(c)}:\{a,b\},\qquad U^{(a)}:\{b,c\}.                 \tag{16}
\]

Whenever either is paired with a rank-one successor profile,
Section 2 forces its direction to be respectively `f` or `d`.
We can now dispose of all five rows without determining any
affine offsets or assigning the profiles to the named `R_i`.

* In the first row all three successor profiles have rank one,
  because none meets `Q_d`. Their supports are `{0,f}` twice
  and `{e,f}` once. The latter is the only profile of direction
  `d`, so it must pair with `U^{(a)}`. This support product
  contains no hole, contradicting `g_R=4`.
* In the third row all three successor profiles again have rank
  one, now with supports `{d,f}` twice and `{d,e}` once.
  None has direction `d`, as required by `U^{(a)}`.
* In the fourth row the three rank-one successor supports are
  `{0,e}`, `{0,f}`, `{e,f}`. Once again `U^{(a)}` must
  pair with `{e,f}`, and their support product has no hole.
* The fifth row requires eight incidences on one line from
  three profiles each meeting it at most twice. It is impossible.

For the second row, parity allows either zero or two rank-two
successor profiles. Suppose first all three have rank one.
By (16), their directions include `f,d`. The xor of the three
support directions equals the xor of the odd-degree endpoints:
the degrees are `(2,1,1,2)`, giving `d+e=f`. The third
direction must therefore be `d`. The only supports with these
degrees and directions are `{0,f}`, `{0,d}`, `{e,f}`.
Alignment assigns `U^{(c)}` to the first. The support
`U^{(a)}` must pair with `{0,d}`, since pairing it with
`{e,f}` would see no hole. This leaves the rank-two predecessor
paired with `{e,f}`, which also sees no hole.

Finally suppose there are two rank-two successor profiles.
The remaining rank-one successor support is `{0,f}`.
A partner with two rank-two profiles could receive at most one
good pair per hole, hence at most three, contrary to `g_R=4`.
Thus the rank-two predecessor must pair with this unique
rank-one successor. The profile `U^{(a)}` then pairs with a
rank-two successor, but its support `{b,c}` sees only the hole
`(b,0)`. A rank-one/rank-two pair receives at most two good
pairs from a single hole, again a contradiction.

All five patterns are impossible. Therefore the last normalized
internal incidence type cannot arise from an E1485 magma. Together
with the preceding incidence exclusions, this proves that an
order-forty magma in the `r=|Z|=4`, least-noncentral-degree-five
branch cannot have thirteen degree-five vertices. The final
profile obstruction is analytic; the earlier reduction to the
single internal type retains its explicitly documented finite-check
dependency.

## 9. The theorem and its proof dependencies

**Theorem.** Suppose a finite E1485 magma has order forty,
`r=|Z|=4`, and degree classes `4,5,8,10`. Then its degree-five
class does not have thirteen members.

The complete proof divides by `k`, the number of degree-eight
vertices having sharp degree three. There is no Lean formalization
of this theorem yet. Its finite components are exhaustive small
binary-incidence checks, not SAT results; the exploratory profile
solver is not used in the proof.

| Case | Proof dependency | Recorded check time |
|---|---|---:|
| `k=3` | [Analytic three-high exclusion](1485_order_forty_thirteen_three_high.md) | — |
| `k=2` | [Two-high proof](1485_order_forty_thirteen_two_high.md), [standard-Python checker](../scripts/1485_n40_thirteen_two_high_check.py), default mode | 29.2 s on latest rerun |
| `k=1` | [One-high proof](1485_order_forty_thirteen_one_high.md), the same checker with `--one-high` | 140.6 s on latest rerun |
| `k=0` | [Analytic profile reductions and finite incidence classification](1485_order_forty_thirteen_profiles.md), [standard-Python checker](../scripts/1485_n40_thirteen_low_sharp_check.py), followed by the analytic obstruction on this page | About 2.5 s |

The stated times are whole research-checker runs, not Lean proof
elaboration or kernel-checking timings. This theorem excludes one
branch of order forty; it does not by itself exclude every possible
order-forty model or prove the full square/double-square spectrum.

As a separate regression check on the hand calculation in Sections 7–8,
the last checker also enumerates the normalized support patterns, without
affine offsets or magma tables. It finds **25** possible low-vertex/hole
patterns, **18** residual support-multiset pairs, and **96** pairings to
test; none satisfies the necessary good-pair bounds. These counts are
asserted in the script. This independently audited support check takes
negligible time within the reported 2.5-second run. It supplements the
analytic obstruction rather than supplying an unstated SAT premise.
