# Order forty: the twelve/eight branch cannot have one high-sharp partner

Research note, 20 September 2026. This is a **checked finite exclusion**,
not a purely analytic proof and not a Lean theorem. It rules out sharp
degrees `(3,2,2,1,1,1,1,1)` on the eight degree-eight vertices when
the degree-class sizes are `(4,12,8,16)` at degrees `4,5,8,10`.

The loop subcase has an exhaustive incidence checker. The other two
subcases have explicit LRAT refutations, checked by an independent
proof checker. The reduction to the finite constraints is mathematical;
the contradiction uses the stated finite certificates. No unverified
SAT verdict is being treated as a proof.

## 1. Three cases exhaust the unique high vertex's internal successor

Let `h` be the unique sharp-degree-three vertex, let `M` be the
two sharp-degree-two vertices, and let `L` be the five sharp-degree-one
vertices. Ordinary adjacency `D` within `B` has in/out degree
`4−j_b`, so `h` has a unique internal predecessor `p` and successor
`s`. The sharp-path matrix `C` is binary with row/column sums `j_b`.

There are exactly three cases:

| Internal successor of `h` | Exclusion |
| --- | --- |
| `s=h` | [Seven-point exhaustive incidence check](1485_order_forty_twelve_one_high_loop.md), 56 permutation types |
| `s∈M` | Independently checked medium-successor LRAT refutation below |
| `s∈L` | Independently checked low-successor LRAT refutation below |

Label `h=0`, the members of `M` by `1,2`, and those of `L`
by `3,…,7`. Relabeling within the last two degree classes normalizes
the second case to `D_01=1` and the third to `D_03=1`. No other
symmetry assumption is made; in particular, the predecessor is not
fixed and `D` is not assumed symmetric.

## 2. Necessary Boolean constraints

The encoder
[1485_n40_twelve_one_high_cnf.py](../scripts/1485_n40_twelve_one_high_cnf.py)
has 128 primary Boolean variables, the entries of `D,C`. It imposes
the following necessary conditions.

1. The row and column sums of `C` are `(3,2,2,1,1,1,1,1)`;
   those of `D` are `(1,2,2,3,3,3,3,3)`.
2. Two distinct ordinary internal middles force a degree-five sharp
   replacement: `(D²)_bd≥2` implies `C_bd=1`.
3. The [return-matching bound](1485_general_return_matching.md) forces
   `C_bd=1` if `j_b+j_d>5`. If the sum exceeds four, either
   `C_bd=1` or an internal two-step path exists.
4. On every internal edge `bDd`, bad-extension balance gives
   `β(b,d)=η(b,d)`, where
   `β(b,d)=#{x:C_bx=1,dDx}` and
   `η(b,d)=#{x:xDb,C_xd=1}`.
5. Let `G_db` count paths `dDxDyDb` with `C_dy=C_xb=0`.
   These are precisely the good-good all-`B` paths. Return matching
   bounds their count by `8−j_b−j_d`, `5−j_b−j_d`, or
   `4−j_b−j_d` according as `b*d` belongs to `A,B,T`.
   The three alternatives are determined by `C_bd=1`, by
   `C_bd=0<(D²)_bd`, and by `C_bd=(D²)_bd=0`.
6. Put `K=CD+DC+G`. The
   [mixed return capacities](1485_order_forty_mixed_return_counts.md)
   give `K_db≤4` for every pair. If `b*d=e∈B`, they also give
   `K_db+β(e,d)+η(b,e)≥3`,
   `K_db+β(e,d)≤4`, and `K_db+η(b,e)≤4`.
7. The [analytic high-profile argument](1485_order_forty_twelve_one_high_loop.md#5-independently-a-unique-high-sharp-profile-has-exactly-two-good-pairs)
   gives `C_ps=1` whenever `pDhDs`. This statement is independent
   of the finite loop exclusion. The large-class theorem permits
   taking the opposite operation to put one profile family in a
   single coset, and `C_ps=1` is invariant under that reversal.
8. The one-`A` five-cycle rule says that `aDbDcDd` and
   `C_da=1` imply `C_ac=C_bd`.
9. Finally impose the chosen successor unit `D_01=1` or `D_03=1`.

All quantifiers here range over eight labels. The constraints do not
assume a single successor-profile coset, full core, involutive squaring,
or the conjectured spectrum. Although the encoder also offers an
optional all-`B` five-cycle strengthening, **neither archived proof
uses that option**.

## 3. The CNF encoding and its controls

The file constructs its own CNF; no SMT-to-CNF conversion is involved.
Literal `1` is constrained true. An auxiliary conjunction `z=∧l_i`
is encoded by the clauses `¬z∨l_i` and `z∨∨¬l_i`.
Disjunction is obtained by negating a conjunction of negated literals.

For cardinalities, the sequential threshold recurrence is

\[
t_{i,k}\ \longleftrightarrow
t_{i-1,k}\lor(e_i\land t_{i-1,k-1}),
\qquad t_{0,0}=\mathsf{true},\quad
t_{0,k}=\mathsf{false}\ (k>0).
\]

Thus `t_i,k` means at least `k` of the first `i` events hold.
Repeated events are deliberately retained: different paths can have
identical Boolean conditions but still contribute separately to a count.
The small summed inequalities use these unary thresholds directly.

The code checks the threshold encoding against exhaustive truth tables
with repeated, negated, and constant literals. It also evaluates all
auxiliary variables on a concrete near-candidate satisfying **every**
pre-closure condition above, and verifies that the one-`A` closure then
rejects it. Thus the unsatisfiability is not caused by an always-false
cardinality encoding or an empty preliminary condition set.

Any hypothetical magma determines a satisfying assignment of the primary
variables and, by the gate definitions, of all auxiliary variables.
A valid CNF refutation therefore excludes that case.

## 4. Independent LRAT certification and retained artifacts

Both cases have **118,725 variables and 384,244 clauses**. They were
solved using CaDiCaL **2.1.2**, with text LRAT output and internal checking:

```sh
python3 scripts/1485_n40_twelve_one_high_cnf.py --successor medium --output /tmp/1485_onehigh_medium.cnf
cadical --lrat --no-binary --check -q -t 600 /tmp/1485_onehigh_medium.cnf /tmp/1485_onehigh_medium.lrat
python3 scripts/1485_n40_twelve_one_high_cnf.py --successor low --output /tmp/1485_onehigh_low.cnf
cadical --lrat --no-binary --check -q -t 600 /tmp/1485_onehigh_low.cnf /tmp/1485_onehigh_low.lrat
```

Both solver runs returned exit status 20, meaning UNSAT. Their proof
generation took approximately **110.1 s** and **107.8 s**, respectively,
as measured by proof-file creation and final-write timestamps.

The proofs were then checked by a separately compiled `lrat-check`
from `marijnheule/drat-trim`, commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. The checker source
`lrat-check.c` has SHA256
`bf07c2ac96b9035da1ebcc578cb95e956a2b795629d613154cdb307f8a8f4a95`.
Its RUP/RAT checking and final empty-clause requirement were inspected.
A small genuine refutation passed; a dropped-hint mutation and a fake
empty-clause proof against a satisfiable CNF were rejected.

```sh
/tmp/lrat-check /tmp/1485_onehigh_medium.cnf /tmp/1485_onehigh_medium.lrat
/tmp/lrat-check /tmp/1485_onehigh_low.cnf /tmp/1485_onehigh_low.lrat
```

Independent verification returned success in **1.18 s** and **1.51 s**.
Compressed copies of the checked refutations and their exact hashes are
retained in [data/1485_certificates](../data/1485_certificates/README.md).
The CNFs are regenerated deterministically by the encoder.

| Case | CNF SHA256 | Uncompressed LRAT SHA256 |
| --- | --- | --- |
| Medium | `a6ab60ff952bd210cded81615b0bdde4b22c1d18c493641c25b13561a7054c92` | `f3b52ec8a0c3090a89e2b5d6f1d0dc06bc0418191609daca0e44a13cb1628091` |
| Low | `5c286effab026506ce7524415628a880d297340bde90c8592727861265a613ee` | `919e52bbf372e335fd851608a1747cf2e77782aec49c9082b7c1950f7ea1f15c` |

These are external finite certificates, not Lean kernel proofs. The
mathematical reduction, the transparent Boolean encoder, the explicit
LRAT files, and the independently checked refutations together establish
the claimed finite exclusion.

## 5. Remaining twelve/eight frontier

The [analytic two-high exclusion](1485_order_forty_twelve_two_high_exclusion.md)
rules out `(1^6,3^2)`, and the present proof rules out `(1^5,2^2,3)`.
Therefore any remaining twelve/eight model would have

\[
\boxed{j=(1^4,2^4).}
\]

This last distribution, and hence the complete twelve/eight case,
is not settled by this note.
