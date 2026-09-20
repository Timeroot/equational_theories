# Order forty: the four-central case is excluded

Research theorem, 20 September 2026. This is a complete finite-assisted
proof, not yet a Lean theorem. Its finite dependencies are explicit
incidence enumerations and independently checked, retained LRAT
refutations. No unverified SAT/ATP verdict is a premise.

**Theorem.** No finite E1485 magma has order forty, minimum translation
degree four, and exactly four central elements.

This is a local exclusion, **not an exclusion of order forty itself**
and not a proof of the square-or-double-square spectrum conjecture.

## 1. Exhaustive reduction to seven class sizes

The [minimal-central-count theorem](1485_minimal_central_count.md)
and the [first-output theorem](1485_first_top_output_fibers.md#4-the-smallest-central-class-forces-a-proper-divisor)
give exactly sixteen top elements, four top neighbors in each direction
at every element, and least noncentral degree five. Degrees divide
forty and lie between four and ten, so the degree classes are precisely

| Class | Degree | Cardinality |
| --- | ---: | ---: |
| Central `Z` | 4 | 4 |
| `A` | 5 | `a` |
| `B` | 8 | `20−a` |
| Top `T` | 10 | 16 |

Each element of `A` has one sharp predecessor and successor in `B`.
Those maps are onto, and their joint map is injective. The
[profile bound](1485_min_four_large_five_class.md#5-consequences-for-the-order-forty-branch)
therefore gives exactly the range `10≤a≤16` used below.

## 2. Every class size is excluded

| `a` | Completed argument | Finite dependency |
| ---: | --- | --- |
| 10 | [Repeated-profile expansion](1485_order_forty_ten_profile_expansion.md) | [8 LRAT proofs](../data/1485_certificates/A10.md) |
| 11 | [Compressed-profile capacities](1485_order_forty_eleven_profile_capacity.md) | [37 LRAT proofs](../data/1485_certificates/a11/README.md) |
| 12 | Complete subdivision in §3 below | Explicit incidence checks and retained LRAT proofs |
| 13 | [Sharp-distribution reduction](1485_order_forty_thirteen_profiles.md) and [final affine obstruction](1485_order_forty_thirteen_directions.md) | The linked seven-vertex incidence checks; final obstruction analytic |
| 14 | [Arbitrary-product return matching](1485_order_forty_fourteen_exclusion.md) | None; analytic |
| 15 | [Near-saturation return matching](1485_order_forty_near_saturation.md) | None; analytic |
| 16 | [Single-coset collapse](1485_order_forty_saturated_profiles.md) and [forced partial tables](1485_order_forty_single_coset.md) | 10,368 explicit binary-linear systems |

The thirteen/seven proof also uses the separately documented
[two-high](1485_order_forty_thirteen_two_high.md) and
[one-high](1485_order_forty_thirteen_one_high.md) incidence exclusions;
the [three-high](1485_order_forty_thirteen_three_high.md) exclusion is
analytic. The table does not silently replace these finite dependencies
by the final affine argument.

## 3. The twelve/eight subdivision is complete

Sharp counts at the eight vertices of `B` lie in `{1,2,3}` and sum
to twelve. The only distributions are the following three.

1. **`(3²,1⁶)`:** excluded by the
   [analytic two-high argument](1485_order_forty_twelve_two_high_exclusion.md).
2. **`(3,2²,1⁵)`:** the
   [one-high theorem](1485_order_forty_twelve_one_high_exclusion.md)
   excludes the internal-loop case by a 56-permutation incidence check,
   and the medium/low successor cases by two retained LRAT proofs.
3. **`(2⁴,1⁴)`:** handled exhaustively as follows.

The [large-profile theorem](1485_min_four_large_five_class.md) puts at
least one profile family in a single coset; take it to be the predecessor
family by duality. Its four multiplicities sum to twelve and are at
most four. The [no-high profile analysis](1485_order_forty_twelve_no_high_profiles.md)
excludes `4440` analytically, and the
[thin-line refutation](1485_order_forty_twelve_thin_exclusion.md)
excludes `4431`. Only `4422`, `4332`, and `3333` remain.

Every mixed successor-coset arrangement is excluded by the
[mixed-profile theorem](1485_order_forty_twelve_mixed_exclusion.md):
three split cases and two exceptional ten-plus-two cases, with all
[five refutations retained](../data/1485_certificates/A12_MIXED.md).
Thus both families use single cosets. Applying the same multiplicity
restrictions dually leaves seven profile-grid orbits, not just six:
`4332/4332` has two different hole arrangements.

The [joint-capacity theorem](1485_order_forty_twelve_joint_capacities.md)
excludes six of the seven with separately checked LRAT certificates.
The remaining `3333/3333` orbit is excluded by the
[balanced-incidence theorem](1485_order_forty_twelve_balanced_incidence.md).
Its finite step enumerates forty classes of eight-vertex incidence
matrices. All 56 survivors force affine low profiles; exact translation
fibers then give an analytic contradiction. An independent full rerun
reproduced every count and assertion in **9.74 seconds**.

There is also an independent
[regular-hole LRAT refutation](../data/1485_certificates/A12_REGULAR_HOLES.md)
of that last orbit. It uses exact individual fiber counts instead of
the forty-class incidence lemma; it is an alternative proof, not an
additional premise of the shorter incidence argument. Its retained
archive was replayed against a freshly regenerated, hash-identical CNF.

These cases exhaust the twelve/eight split and hence all seven possible
values of `a`, proving the theorem.

## 4. Precisely what remains at order forty

The possible minimum degrees dividing forty and not exceeding its square
root are `1,2,4,5`. The known full-core results exclude minima one and
two at this order. Minimum five allows only degrees five and eight,
contradicting the [two-degree theorem](1485_two_degree_lower_bound.md).
At minimum four, full core would give order `16·2^j`, also not forty.
The central-defect bounds restrict a non-full core to `m≤10`.
After the theorem above, the remaining possibilities are therefore

\[
\boxed{r=4,\qquad |Z|\in\{5,6,7,8,9,10\}.}
\]

The subsequent [analytic ten-central exclusion](1485_order_forty_ten_central_exclusion.md)
removes the last value. The current unresolved central counts at order
forty are therefore **five through nine**. Its proof uses the following
first-output facts, but not any of the four-central finite checks above.

The first noncentral top-output degree is five, since it is at most
seven and must divide forty. All four degree classes `4,5,8,10`
occur, but their cardinalities need not be those of §1.

Every degree-five element has top-profile size three or four. Indeed
least-degree sharp balance gives a common top count `t`, with
`t(t−1)` good top pairs. The central shadow gives `t≥2`, so each
such element is a first top output; the
[first-successor profile theorem](1485_first_successor_degree_profiles.md)
then gives `t∈{3,4}` and `m≤t²`. In particular `m=10` forces
size four throughout. At `m=8,9`, a size-three profile places the
central elements in respectively a three-by-three grid with one hole
or the full grid.

The surviving five-through-nine cases are unresolved branches, not
asserted constructions. Earlier
exclusions at central counts five through seven concern first-output
degree **seven** and cannot be applied to this degree-five problem.
