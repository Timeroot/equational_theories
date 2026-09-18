# E1485: current proof frontier

Updated 18 September 2026. The square-or-double-square spectrum conjecture
is **not yet proved**. The results below are pen-and-paper proofs, not Lean
declarations. Finite-table regression tests check the formulas on examples;
they are not substitutes for the proofs.

For a nonempty finite E1485 magma, write `n` for its order, `r` for its
minimum translation degree, and `Z` for its central vertices. Established
finite structure gives `n=r·max d` and `|Z|≤r²`. The **full-core hypothesis**
is `|Z|=r²`. It is known unconditionally when `r=2`.

## The latest general proof chain

1. [Ordinary-edge top rectangles](1485_canonical_triples.md): canonical
   boundary edges around any ordinary edge give a unique top-valued return.
2. [Full-core sharp regularity](1485_full_core_sharp_regularity.md): the
   canonical relation is exactly sharp adjacency, with `r` predecessors
   and successors at every vertex. This removes the earlier restrictions
   on the number of degrees and on small values of `r`.
3. [Canonical blocks](1485_full_core_cyclic_blocks.md): the carrier has a
   canonical partition into blocks of size `r²`. Sharp adjacency moves
   blocks by a permutation `σ`; its square is the complete relation from
   each block to `σ²` of that block.
4. [Boolean quotient](1485_full_core_quotient.md): top-valued rectangles
   force every ordinary adjacency block to be empty or `r`-regular.
   Choosing the intermediate block of minimum degree then proves that
   multiplication respects the blocks. The quotient has a constant row,
   so **`n=r²·2^m`**. This proves the square-or-double-square conclusion
   under full core, unconditionally at minimum degrees one and two.

Separately, [period ten](1485_full_core_period_ten.md) proves `σ¹⁰=id`
directly from actual products and their block labels. It does not
presuppose quotient compatibility and is not needed for step 4.

At minimum degree two, the same chain also proves all maximum-translation
kernel mates commute and every fixed left/right pair has the four-element
blocks as its orbits. See [the kernel-mate theorem](1485_top_kernel_cycles.md).

## The single remaining hypothesis on this route

**Full core for arbitrary `r` remains open:** prove that every finite
E1485 magma has exactly `r²` central vertices. Equivalently, for any
central `h`, prove that its `r²`-element coordinate rectangle
`{u*v : u∈Row(h), v∈Col(h)}` consists entirely of central vertices.
The rectangle always contains all central vertices; the missing
inclusion is in the other direction.

The [one-missing-vertex theorem](1485_near_full_core.md) now excludes
`|Z|=r²−1` for every finite model. Thus a failed full core has at
least two missing vertices. Its proof uses exact top-fiber counts and
E1485 itself, not the conditional full-core results. This also gives a
shorter proof of the three-central-vertex exclusion at minimum degree two.

More generally, the [small-defect gap theorem](1485_small_central_defects.md)
proves that a nonzero defect `δ=r²−|Z|` satisfies `δ≥r`.
Thus there are no central cardinalities strictly between `r²−r`
and `r²`. The key finite lemma equates full central in-degree and
out-degree once the top class and top-neighbor counts have their
expected sizes; a nonnegative incidence identity forces those sizes
when `δ<r`. The boundary `δ=r` and larger defects are not resolved
by this argument.

The block-congruence and quotient questions under full core are now
settled, including goodness reflection. No separate unproved quotient
assumption is used in that theorem.

The unrestricted rectangle assertion is false for infinite models; the
[explicit counterexample](1485_graph_research.md#why-rectangle-closure-cannot-be-proved-purely-equationally)
shows that a proof must genuinely use finiteness. The full-core
hypothesis is not silently assumed in any unconditional spectrum claim.

The [equivalent-targets note](1485_full_core_equivalences.md) identifies
the same gap with sharp regularity, equality of the extreme degree-class
sizes, or symmetry of central-valued products. A failed full core must
produce an irregular top-top output of degree in `(r,r²]`; see the
[unrestricted finite reductions](1485_unrestricted_central_incidence.md).
An equivalent one-variable target is that every top element has a
central square. Exactly `|Z|` top elements have central square already;
the missing assertion is that these exhaust the top class.
That note also proves that every central-coordinate adjacency block
is triangular with unit diagonal and has a unique perfect matching,
without assuming full core. The different central choices have not
yet been shown to select the same matchings.
Its coordinate-transpose involution identifies a precise possible
bridge between two central choices. An explicit countable counterexample
now shows that this bridge, if valid for finite models, also requires
a genuinely finite argument.
The [explicit incidence obstruction](1485_central_incidence_obstruction.md)
rules out a proof using only the basic central/top counting equations.

Other precisely recorded limits are the
[joint-support conjecture](1485_pair_joint_support.md), the
[ordinary-rank counterexample](1485_adjacency_rank_counterexample.md),
and the [bounded order-36 searches](1485_order36_countermodel_search.md).
Those searches returned unknown, not countermodels or impossibility
proofs.

## Other completed spectrum results

- The construction of every square and twice-square order is known.
- Constant-row models have power-of-two order; constant-degree models
  have square order.
- [Exactly two translation degrees](1485_two_degree_lower_bound.md) force
  `n=2r²`, without assuming full core.
- An odd number of distinct translation degrees forces square order.
- [Exactly four degrees under full core](1485_four_degree_regular_gap.md)
  force `n=8r²`, now at every minimum degree.
- [Order 24 is excluded](1485_order_twenty_four.md). That proof separates
  its analytic arguments from two small, reproducible finite incidence
  enumerations; neither enumeration is represented as a Lean proof.

The executable regression check is `scripts/1485_structure_check.py`.
Its built-in cases include an order-32 Boolean model with an order-five
twist, so the tests do not silently assume that squaring is involutive.
