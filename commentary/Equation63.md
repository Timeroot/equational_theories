## The "Dupont" equation

Closely related to the ["Dupond" equation, 1692](https://teorth.github.io/equational_theories/implications/?1692).  In particular, the two equations are equivalent for finite magmas, or for quasigroups, but [neither implies the other for infinite ones](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#dupont-section).  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Proposed.20new.20target.3A.2063.20and.201692.20.28.22Dupont.20and.20Dupond.22.29/near/477121484).

This pair shares many similarities with the "Asterix" ([equation 65](https://teorth.github.io/equational_theories/implications/?65)) and "Obelix" ([equation 1491](https://teorth.github.io/equational_theories/implications/?1491)) pair.

Law 63 implies that left and right multiplications are surjective (in contrast, law 1692 implies their injectivity).  The operations defined by `x : y = y ◇ (y ◇ x)` and `x / y = x : (x : y) = (y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ x)` satisfy `y ◇ (y : x) = x` and `(x / y) ◇ y = x`, hence they can serve as (not necessarily unique) left and right divisions.  In addition, `(y / x) : y = x`.

The left division `x : y` defined in this way satisfies [law 229](https://teorth.github.io/equational_theories/implications/?229).  For finite magmas (or for quasigroups) the operation `:` satisfies [law 125](https://teorth.github.io/equational_theories/implications/?125), and this defines a one-to-one correspondence between finite magmas (or quasigroups) satisfying law 63 and those satisfying law 125, with the inverse correspondence being to define `x◇y = (x:y):x`.  Thus the inequivalent laws 63 and 125 share the same finite spectrum.

As observed by Belousov [1], in a quasigroup satisfying this law, the pair of equations `x◇y=a` and `x=y◇b` has a unique solution `x=b/a` and `y=(b/a)/b`, which means that the quasigroup is orthogonal to its (23)-parastrophe.  It is part of a collection of [seven laws](http://arxiv.org/abs/1509.00796) with similar properties.

[1]: V.D. Belousov. Parastrophic-orthogonal quasigroups. Translated from the 1983 Russian original. Quasigroups Relat. Syst., 13(1):25–72, 2005.

This is the law of order 3 with the [most complicated finite spectrum](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087) (cardinalities of finite magmas satisfying this law).  It has no non-trivial associative model.

An [explicit construction formalized in Lean](https://github.com/Timeroot/equational_theories/blob/definability-negative/docs/63_lean_spectrum.md) gives models at every positive order except **2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158**. In particular every order at least 159 is now covered by a complete Lean proof. All twelve additional positive witnesses recovered from Bennett's [1989 construction theorem](https://doi.org/10.4153/CJM-1989-017-0) are formalized, using only six new multiplication tables and deriving the rest by construction. Orders 2 and 6 are excluded in Lean; the externally checked exclusions at 10 and 14 remain explicitly admitted. Bennett also claims existence at 90, but its required ingredient has not yet been reconstructed locally. The six mathematically unsettled orders are **18, 26, 30, 38, 42, 158**; the exact spectrum remains open.

At order 18, further checked exclusions and a combinatorial reduction show that any model must have commutative left division in the law-229 presentation. That remaining case is still open. This reduction has not been formalized in Lean.
