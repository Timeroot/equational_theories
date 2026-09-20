# Order forty: the unique high-sharp partner cannot have an internal loop

Research note, 20 September 2026. This excludes a subcase of the
twelve/eight branch by a complete, small **finite incidence check**.
It is not an analytic exclusion of the whole one-high case, is not
a Lean theorem, and has no SAT or magma-enumeration dependency.
The checker uses only standard C++17.

Assume the degree-class sizes are `(4,12,8,16)` at degrees
`4,5,8,10`, and the sharp-degree distribution on `B` is
`(3,2,2,1,1,1,1,1)`. Let `h` be its unique sharp-degree-three
vertex, `M` its two sharp-degree-two vertices, and `L` the five
sharp-degree-one vertices. The claim proved here is

\[
\boxed{h\not\mathrel D h.}                              \tag{1}
\]

Here `D` is ordinary adjacency within `B` and `C` records
sharp two-edge paths through `A`, with row/column sums `4−j`
and `j` respectively. The checker does not assume affine top
profiles, a single profile coset, symmetry of `D`, or any absence
of loops at the other seven vertices.

## 1. A loop would isolate h and leave a seven-point permutation

Suppose `hDh`. Since its internal in/out degree is one, this
loop is its only internal incident edge.

For each `m∈M`, the product `h*m` cannot belong to `B`:
there is no internal two-step path from `h` to `m`. Nor can
it belong to `T`, since their sharp degrees sum to five, exceeding
the four-element top return fiber. Therefore `C_hm=1`.
Dually `C_mh=1`, and `C_hh=1` follows from the sum-six
return-matching bound. Consequently

\[
C(h)=C^{-1}(h)=\{h\}\cup M.                            \tag{2}
\]

After deleting row and column `h`, every remaining row and column
of `C` has sum one. It is therefore the permutation matrix of a
map `τ` on the seven-element set `M∪L`.

Write `E` for `D` restricted to this set. Its row and column
degrees are `(2,2,3,3,3,3,3)`, with the two degree-two vertices
labeled `0,1`. No further normalization of `E` is imposed.

## 2. Three necessary tests on E and τ

The [incidence argument used in the two-high exclusion](1485_order_forty_twelve_two_high_exclusion.md)
gives

\[
(E^2)_{ab}\ge2\quad\Longrightarrow\quad\tau(a)=b.       \tag{3}
\]

Indeed two internal middles require a lower degree-five replacement.

On every ordinary edge `bEd`, the
[bad-extension balance](1485_general_return_matching.md#5-bad-extension-balance-on-every-internal-edge)
reduces to

\[
\boxed{dE\tau(b)\quad\Longleftrightarrow\quad
\tau^{-1}(d)Eb.}                                      \tag{4}
\]

The deleted high terms vanish because no internal edge joins `h`
to these seven vertices.

Finally the one-`A` five-cycle rule says that whenever
`aEbEcEd` and `τ(d)=a`,

\[
\boxed{\bigl(\tau(a)=c\bigr)
\quad\Longleftrightarrow\quad\bigl(\tau(b)=d\bigr).}     \tag{5}
\]

To see this, close the internal three-edge path by the sharp path
`d⇒u⇒a` represented by `C_da=1`. The three two-edge paths
meeting `u∈A` are good. The other two have the same good/bad
status by the five-cycle law; their badness is exactly `C_ac=1`
and `C_bd=1`. All these arguments allow repeated vertices.

## 3. Complete enumeration and its normalization

The standalone checker is
[1485_n40_twelve_one_high_loop_check.cpp](../scripts/1485_n40_twelve_one_high_loop_check.cpp).
It performs these finite steps:

1. Generate all `7!` permutations `τ`. Relabeling within the two
   degree-two and five degree-three vertices acts by conjugation.
   The checker generates all `2!·5!` such relabelings, keeps the
   lexicographically smallest representative of each orbit, and obtains
   **56** representatives. All tests (3)–(5) and all degree conditions
   are invariant under these relabelings.
2. For each representative, enumerate each row of `E` among all
   seven-bit masks of the required cardinality. Column capacities
   enforce the required column degrees. Reject a partial assignment
   only if a column capacity is already exceeded or cannot be filled,
   or two already fixed two-step paths violate (3). Such a violation
   cannot disappear when further rows are assigned.
3. Check (4), then (5), on every complete surviving matrix.

The counts are:

| Stage | Count |
| --- | ---: |
| Sharp-permutation representatives | 56 |
| Partial row-assignment nodes | 11,502,195 |
| Complete matrices satisfying degrees and (3) | 738 |
| Also satisfying (4) | 720 |
| Also satisfying (5) | **0** |

The search is exhaustive because any hypothetical pair `(E,τ)`
can first be relabeled to one of the 56 representatives, and its
successive rows are among the enumerated choices. No rejection can
discard a completed pair satisfying the necessary conditions. The
zero at the last stage therefore proves (1).

The implementation asserts the orbit count and all complete-stage
counts. With optimization enabled, the checked run took **11.6 s**
in this workspace; timings depend on machine load. One reproducible
build and invocation is:

```sh
c++ -O3 -std=c++17 -Wall -Wextra -Werror scripts/1485_n40_twelve_one_high_loop_check.cpp -o /tmp/1485_n40_twelve_one_high_loop_check
/tmp/1485_n40_twelve_one_high_loop_check
```

Do not disable assertions with `-DNDEBUG` when auditing the stated
checks.

## 4. Positive controls

The code independently verifies that `τ=id` and the row masks

```text
E = (5, 24, 97, 42, 82, 76, 52)
```

satisfy the degree conditions, (3), and (4). This is a genuine
near-candidate, not an empty preliminary search. It fails (5) on
`a=b=d=0,c=2`: the edges `0E0E2E0` exist, but the two
claimed equalities are respectively false and true.

Conversely, the matrix consisting of seven isolated loops with
`τ=id` passes (3)–(5), although it fails the required degrees.
This checks that the closure predicate is not identically rejecting.
The controls and the positive intermediate counts are assertions
in the executable, not just descriptions in this note.

The remaining one-high case has distinct internal neighbors from
`h` itself; its predecessor and successor may coincide with each
other. This note does not exclude those possibilities.

## 5. Independently, a unique high-sharp profile has exactly two good pairs

The following is an analytic argument independent of the finite
check above. It applies to mixed successor cosets, including the
exceptional `11+1` configuration; no single-coset hypothesis is needed.

Let `p,h,s` be the unique internal predecessor, the high vertex,
and its unique internal successor. The
[high-profile theorem](1485_order_forty_twelve_high_profiles.md#2-every-sharp-degree-three-partner-has-affine-profiles)
makes `U_h` an affine four-point plane. All `A` predecessor
profiles are parallel lines of the same partition `P`.
The exact return fiber is

\[
T\cap R_s^{-1}(h)
=U_h\setminus\bigcup_{a:F(a)=s}U_a,
\qquad |T\cap R_s^{-1}(h)|=1+C_{ps}.                  \tag{6}
\]

The `j_s` removed `P` lines are distinct. If `C_ps=0`,
the difference in (6) has size one. The projection of `U_h`
to the four `P` labels has rank zero, one, or two. In ranks
zero and one, its nonempty fibers have respectively four or two
points, so removing whole fibers leaves an even cardinality.
In rank two, each `P` line meets `U_h` once, so the difference
has size `4−j_s`. Thus size one requires `j_s=3`. Uniqueness
of the high vertex gives `s=h`. Since `h` has internal indegree
one as well, this loop also gives `p=h`. But high-high return
matching forces `C_hh=1`, contrary to `C_ps=0`. This contradiction
does not use the finite loop exclusion.

The high good-pair formula now gives

\[
\boxed{C_{ps}=1,\qquad g_h=3-C_{ps}=2.}                \tag{7}
\]

Moreover, if `U_h` has rank-two projection to the `P` labels,
(6) gives `4−j_s=2`, hence `j_s=2`. This implication also
holds without the single-coset assumption used in the earlier
profile note.
