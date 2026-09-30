This law is a weaker form of the [central groupoid law 168](https://teorth.github.io/equational_theories/implications/?168).

The finite spectrum of (cardinalities of finite magmas satisfying) this law is [unknown](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087).

This law cannot hold in a non-trivial quasigroup or associative magma.

All square and twice-square orders have Lean constructions. The exact spectrum
remains open. A constant row (or a bijective row) forces a power-of-two order.
Orders 3, 5, 6, 7, and 10 are excluded in Lean; order 11 has an external exclusion
whose Lean declaration remains admitted.

A general Lean theorem now shows that taking subalgebras of permutation covers
cannot produce an order unavailable from the corresponding unpermuted direct
product. In particular every subalgebra of any finite permutation cover of the
cubic Boolean eight-point base still has square or twice-square order. See the
[proof and research notes](../docs/1483_subalgebra_research_20260930.md).

A further [Lean-proved theorem](../docs/1483_permutation_cover_definability.md)
provides FO-definable E1485 companions for finite permutation covers of
constant-row bases. The general E1483-to-E1485 definability question remains open.

Permutation covers of E168 bases satisfy E168 themselves, and permutation covers
of bases satisfying E1483 and E1485 satisfy E1485 themselves. Both preservation
results are proved in Lean without finiteness assumptions.
