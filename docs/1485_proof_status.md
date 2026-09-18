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
4. [Period ten](1485_full_core_period_ten.md): `σ¹⁰=id`. Unless all degrees
   are equal, each canonical communicating component has two or ten
   blocks. Thus **`2r²∣n`** in the nonconstant case. In the constant case,
   `n=r²` already.

The period argument uses actual products and their block labels; it does
not presuppose a multiplication on the block set.

At minimum degree two, the same chain also proves all maximum-translation
kernel mates commute and every fixed left/right pair has the four-element
blocks as its orbits. See [the kernel-mate theorem](1485_top_kernel_cycles.md).

## What would finish the full-core case

The immediate target is to prove that multiplication respects the
canonical blocks. This has passed the archived examples but is **not a
theorem**. If it did, the quotient would satisfy E1485 and have a constant
row: the central set and top set are each single blocks, and a central
row is entirely top. The
[constant-row classification](1485_spectrum_research.md#4-classification-of-the-constant-rowcolumn-case)
would then give `2^m` quotient elements. Since all blocks have size `r²`,
we would obtain `n=r²·2^m`, a square or twice a square.

For this particular argument no separate goodness-reflection theorem is
needed once block congruence is established: equal square block sizes are
already proved. Goodness reflection remains another sufficient route via
the earlier [quotient counting theorem](1485_graph_research.md).

Even after finishing that step, **full core for arbitrary `r` remains a
separate gap**. Neither gap is assumed in the claimed unconditional results.

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
