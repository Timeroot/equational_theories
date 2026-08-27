import equational_theories.Definability.ExactAut

/-!
# Machinery for exact-endomorphism families on `Fin 6`

`Definability/ExactEnd3.lean` explains the device: a term-structural pair has `End(M') = End(M)` on
the nose, by `Magma.IsEndo.of_termDefinable`, and `End` is a strictly finer invariant than `Aut`
because an endomorphism need not be injective.  What it cannot do past `Fin 3` is the
classification -- it enumerates all `19,683` operations, and `Fin 6` has `6 ^ 36`.

The way through is that `End(M) = E` pins the unit group `Aut(M) = E ∩ S₆` as well, so
the class already lies inside that group's invariant family, which `Definability/ExactAut6.lean`
enumerates by orbit transport.  A class is therefore an exact-`Aut` class with a different
exactness test: all `46656` self-maps are split into the ones that must be endomorphisms and the
ones that must not, and `Magma.isExact` takes arbitrary maps already.

`Definability/ExactEnd6<X>.lean` is the generated instance of this for each class that buys open
cells; see `endprune4.py` and `genend4.py`.
-/

namespace Magma

/-- The `46656` self-maps of `Fin 6`, indexed in mixed-radix order: `allMaps6 i` sends `x` to the
`x`-th base-`6` digit of `i`. Writing all of them out one match at a time is what
`Definability/ExactEnd3.lean` does with `Magma.m3_xyz`, and at `46656` maps that is no longer worth
reading; arithmetic on a literal is a kernel primitive in any case. -/
def allMaps6 (i : Fin 46656) (x : Fin 6) : Fin 6 :=
  ⟨i.1 / 6 ^ x.1 % 6, Nat.mod_lt _ (by decide)⟩

end Magma
