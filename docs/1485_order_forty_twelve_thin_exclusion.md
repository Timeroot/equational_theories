# Order forty: the twelve/eight branch has no thin predecessor line

Research note, 20 September 2026. This is a **completed finite-assisted
exclusion** of predecessor multiplicities `(4,4,3,1)` in the remaining
sharp-degree distribution `(2^4,1^4)`. It has an explicit, independently
checked LRAT refutation. It does not exclude the other multiplicities,
the whole order, or establish a Lean theorem.

Use degree classes `Z,A,B,T` of degrees `4,5,8,10` and sizes
`4,12,8,16`. The [large-class theorem](1485_min_four_large_five_class.md)
allows taking the opposite operation so that all `A` predecessor profiles
belong to one Klein-four coset: four disjoint lines `P_0,…,P_3`
partitioning the sixteen tops. Let their multiplicities be `u_p`.
The argument below **does not assume one successor coset**.

## 1. A small necessary system of integer capacities

Label the four sharp-degree-two members of `B` by `0,…,3`, the four
sharp-degree-one members by `4,…,7`, and write `j=(2^4,1^4)`.
As usual, ordinary internal adjacency `D` has both margins `4−j`,
and the binary sharp-path matrix `C` has both margins `j`.

For each `d∈B`, let `I_d` be the predecessor-line colors of the
vertices in its sharp `F`-fiber. These colors are distinct: two vertices
with the same `F` image have disjoint predecessor profiles. Therefore

\[
|I_d|=j_d,\qquad \#\{d:p\in I_d\}=u_p.
\tag{1}
\]

Put `M_bp=|TopPred(b)∩P_p|`. Each top predecessor profile has four
points, so its row sum is four. Each top point on `P_p` has ten
successors: four in `T`, one in `Z`, `u_p` in `A`, and `5−u_p`
in `B`. Counting by top points gives

\[
\sum_p M_{bp}=4,\qquad \sum_b M_{bp}=20-4u_p.
\tag{2}
\]

On an internal edge `bDd`, put

`η(b,d)=Σ_y D_yb C_yd`, `β(b,d)=Σ_x C_bx D_dx`.

The [exact return-fiber formula](1485_order_forty_eleven_profile_capacity.md#4-exact-line-capacity-equations-in-the-single-coset-case)
applies with these class sizes too. The top part of `R_d⁻¹(b)` is

\[
TopPred(b)\setminus\bigcup_{p\in I_d}P_p,
\]

and has size `1+η(b,d)`. Consequently

\[
bDd\quad\Longrightarrow\quad
\boxed{\sum_{p\in I_d}M_{bp}+\eta(b,d)=3.}
\tag{3}
\]

Every vertex has an internal successor, and `η≤j_d≤2`. If any
`M_bp=4`, the profile sum in (3) would be zero or four, whereas
`3−η` is one, two, or three. Thus every `M_bp≤3`.

Only three further standard incidence conditions are needed:

1. `(D²)_ac≥2` implies `C_ac=1`.
2. On every internal edge, `β=η`.
3. `aDbDcDd` and `C_da=1` imply `C_ac=C_bd`.

These follow from unique minimum-degree replacement, bad-extension
balance, and the one-`A` five-cycle rule. They allow loops and repeated
vertices. No affine `B`-profile assertion, mixed-return inequality,
full-core hypothesis, or unproved finite theorem is used.

## 2. Encoding and substantive controls

Set `u=(4,4,3,1)`, after renaming the four line colors. Then (2)
has column sums `(4,4,8,16)`. The deterministic encoder
[1485_n40_twelve_line_capacity_cnf.py](../scripts/1485_n40_twelve_line_capacity_cnf.py)
represents `D,C`, memberships in `I_d`, and the three monotone unary
bits of each `M_bp`. It encodes precisely (1)–(3) and the three
incidence conditions. Products of a membership bit and a unary bit
count the selected line intersections exactly. The shared threshold
encoder has exhaustive truth-table controls, including repeated,
negated, and constant events.

As a positive control the program evaluates a concrete necessary
incidence system satisfying **all** encoded conditions for `u=(4,4,2,2)`.
Changing one of its unary intersection bits is correctly rejected.
Thus these constraints are not intrinsically contradictory; the thin
line's margins are essential. The control is not a magma model.

The mathematical reduction and complete encoder were audited separately.
A putative magma supplies the primary variables, and the exact gate
definitions extend them to a satisfying CNF assignment.

## 3. Checked refutation and reproducibility

The thin-line CNF has **14,277 variables and 52,365 clauses**.
CaDiCaL 2.1.2 generated a text LRAT refutation in **6.20 seconds**;
the independent checker accepted it in **0.72 seconds**, with `VERIFIED`
and exit status zero. Generation including controls took **0.85 seconds**.
These are wall-clock timings under concurrent load, not Lean timings.

The proof is retained as
[n40_a12_thin_4431.lrat.xz](../data/1485_certificates/n40_a12_thin_4431.lrat.xz).
SHA256 hashes are:

| Artifact | SHA256 |
|---|---|
| Generated CNF | `4d81b780525177b6c2684d2c53f9077e6fe8c8a154ed160251cbea710a99c2b5` |
| Uncompressed LRAT | `23819f54dc14fc9003b95acea167e1852cf3f6aa630f8c62b6e58c85b82e5e94` |
| Archived XZ | `127f077f17410bdbbe3ca614dba559c934649350c937e742ca423ca73d692cd7` |

Use the independent `lrat-check` with provenance and controls documented
in [the certificate README](../data/1485_certificates/README.md).
Replay without a SAT solver:

```sh
python3 scripts/1485_n40_twelve_line_capacity_cnf.py --pattern 4431 --output /tmp/1485_a12_thin.cnf
xz -dc data/1485_certificates/n40_a12_thin_4431.lrat.xz > /tmp/1485_a12_thin.lrat
/tmp/lrat-check /tmp/1485_a12_thin.cnf /tmp/1485_a12_thin.lrat
```

The refutation proves that `(4,4,3,1)` is impossible. Together with the
[analytic empty-line exclusion](1485_order_forty_twelve_no_high_profiles.md#5-no-predecessor-line-can-be-empty),
the remaining predecessor multiplicities are exactly

\[
\boxed{(4,4,2,2),\quad(4,3,3,2),\quad(3,3,3,3).}
\]

These are remaining necessary possibilities, not asserted realizations.
