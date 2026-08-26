import equational_theories.Definability.ExactAut

/-!
# Machinery for exact-endomorphism families on `Fin 4`

`Definability/ExactEnd3.lean` explains the device: a term-structural pair has `End(M') = End(M)` on
the nose, by `Magma.IsEndo.of_termDefinable`, and `End` is a strictly finer invariant than `Aut`
because an endomorphism need not be injective.  What it cannot do past `Fin 3` is the
classification -- it enumerates all `19,683` operations, and `Fin 4` has `4 ^ 16`.

The way through is that `End(M) = E` pins the unit group `Aut(M) = E ∩ S₄` as well, so
the class already lies inside that group's invariant family, which `Definability/ExactAut4.lean`
enumerates by orbit transport.  A class is therefore an exact-`Aut` class with a different
exactness test: all `256` self-maps are split into the ones that must be endomorphisms and the
ones that must not, and `Magma.isExact` takes arbitrary maps already.

`Definability/ExactEnd4<X>.lean` is the generated instance of this for each class that buys open
cells; see `endprune4.py` and `genend4.py`.
-/

namespace Magma

/-- The `256` self-maps of `Fin 4`, indexed in mixed-radix order: `allMaps4 i` sends `x` to the
`x`-th base-`4` digit of `i`. Writing all of them out one match at a time is what
`Definability/ExactEnd3.lean` does with `Magma.m3_xyz`, and at `256` maps that is no longer worth
reading; arithmetic on a literal is a kernel primitive in any case. -/
def allMaps4 (i : Fin 256) (x : Fin 4) : Fin 4 :=
  ⟨i.1 / 4 ^ x.1 % 4, Nat.mod_lt _ (by decide)⟩

end Magma
