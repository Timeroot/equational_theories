import equational_theories.Definability.Structural

/-!
# Structural certificates from the *exact* automorphism group on `Fin 3`

`Definability/Structural.lean` proves that a structural pair `M`, `M'` has `Aut(M') = Aut(M)`
exactly, and spends that on the cheapest case: `Aut(M) = 1` on `Fin 2`. Every other automorphism
group is worth its own certificate, and on `Fin 3` two more of them are just as cheap, because the
classification lemmas of `Definability/Negative.lean` already cut the search down to a short list.

The subgroups of `S₃` up to conjugacy are `1`, `C₂`, `C₃` and `S₃`, and a law is closed under
relabelling the carrier, so what a structural pair preserves is the *conjugacy class* of the
automorphism group; each class is one rectangle of non-structurality facts. `S₃` is already the
`Magma.affine3` family of `Definability/Certificates.lean` — with the full symmetric group there
is no difference between "at least" and "exactly" — and the trivial group on `Fin 3` would need
all `19683` tables, so this file does the two middle cases:

* `Magma.cyclic3Exact`, the `24` magmas whose automorphism group is exactly the rotation group
  `C₃`: the `27` magmas admitting the cyclic shift (`Magma.cyclic3`, classified by
  `Magma.op_eq_of_isEndo_add_one`) minus the `3` that also admit the reflection and so have all of
  `S₃`. `1196` equations have such a model and `3498` do not.
* `Magma.reflective3Exact`, the `78` magmas whose automorphism group is exactly the `C₂` generated
  by `x ↦ -x`: the `81` magmas admitting the reflection (`Magma.reflective3`, classified by
  `Magma.op_eq_reflOp3`) minus the same `3`. `2698` equations have such a model and `1996` do not.

In both cases only two subgroups of `S₃` contain the one in question — it, and `S₃` — so "exactly"
means "at least, and not affine". Rather than re-index the family, the three affine parameters are
redirected onto a member that is kept, which leaves a family of the right `24` or `78` magmas with
three of them repeated; a repeated member costs nothing on either side of a certificate.

The two directions of the structural definability do opposite halves of the work: the forward one
carries the symmetry from `M` to the companion `M'`, and the backward one carries the *absence* of
the extra symmetry back from `M'` to `M`. It is the second that the one-sided certificates of
`Definability/Certificates.lean` cannot do, and it is the whole reason these rectangles are larger
than their `Magma.cyclic3` and `Magma.reflective3` counterparts.

`Definability/Certs/Cyclic3Exact*.lean` and `Definability/Certs/Reflective3Exact*.lean` record the
two rectangles.
-/

open Law Law.MagmaLaw

namespace Magma

/-! ### Automorphism group exactly the rotation group `C₃` -/

/-- The `24` magmas on `Fin 3` whose automorphism group is exactly the cyclic group of order `3`,
as a family indexed by the `27` first rows of `Magma.cyclic3`: the `3` affine rows, which have all
of `S₃`, are redirected onto the row `0, 0, 1`, which does not. -/
@[implicit_reducible]
def cyclic3Exact (a b c : Fin 3) : Magma (Fin 3) :=
  if (cyclic3 a b c).IsEndo ⇑(Equiv.neg (Fin 3)) then cyclic3 0 0 1 else cyclic3 a b c

theorem cyclic3Exact_isEndo_addRight (a b c : Fin 3) :
    (cyclic3Exact a b c).IsEndo ⇑(Equiv.addRight (1 : Fin 3)) := by
  revert a b c; decide

theorem cyclic3Exact_not_isEndo_neg (a b c : Fin 3) :
    ¬ (cyclic3Exact a b c).IsEndo ⇑(Equiv.neg (Fin 3)) := by
  revert a b c; decide

/-- A magma on `Fin 3` admitting the cyclic shift but not the reflection *is* the member of
`Magma.cyclic3Exact` named by its first row. -/
theorem cyclic3Exact_eq_self {M : Magma (Fin 3)}
    (h₁ : M.IsEndo ⇑(Equiv.addRight (1 : Fin 3))) (h₂ : ¬ M.IsEndo ⇑(Equiv.neg (Fin 3))) :
    cyclic3Exact (M.op 0 0) (M.op 0 1) (M.op 0 2) = M := by
  have key : cyclic3 (M.op 0 0) (M.op 0 1) (M.op 0 2) = M := by
    obtain ⟨op⟩ := M
    refine congrArg Magma.mk (funext fun x ↦ funext fun y ↦ ?_)
    calc ![op 0 0, op 0 1, op 0 2] (y - x) + x
        = op 0 (y - x) + x := by
          congr 1
          generalize y - x = t
          fin_cases t <;> rfl
      _ = op x y := (Magma.op_eq_of_isEndo_add_one h₁ x y).symm
  simp only [cyclic3Exact, key, if_neg h₂]

/-! ### Automorphism group exactly the reflection -/

/-- The `78` magmas on `Fin 3` whose automorphism group is exactly the order-`2` group generated
by `x ↦ -x`, as a family indexed by the `81` parameters of `Magma.reflective3`: the `3` affine
ones are redirected onto `0, 0, 0, 0`. -/
@[implicit_reducible]
def reflective3Exact (a b c d : Fin 3) : Magma (Fin 3) :=
  if (reflective3 a b c d).IsEndo ⇑(Equiv.addRight (1 : Fin 3)) then reflective3 0 0 0 0
  else reflective3 a b c d

theorem reflective3Exact_isEndo_neg (a b c d : Fin 3) :
    (reflective3Exact a b c d).IsEndo ⇑(Equiv.neg (Fin 3)) := by
  revert a b c d; decide

theorem reflective3Exact_not_isEndo_addRight (a b c d : Fin 3) :
    ¬ (reflective3Exact a b c d).IsEndo ⇑(Equiv.addRight (1 : Fin 3)) := by
  revert a b c d; decide

/-- A magma on `Fin 3` admitting the reflection but not the cyclic shift *is* the member of
`Magma.reflective3Exact` named by the four free entries of its table. -/
theorem reflective3Exact_eq_self {M : Magma (Fin 3)}
    (h₁ : M.IsEndo ⇑(Equiv.neg (Fin 3))) (h₂ : ¬ M.IsEndo ⇑(Equiv.addRight (1 : Fin 3))) :
    reflective3Exact (M.op 0 1) (M.op 1 0) (M.op 1 1) (M.op 1 2) = M := by
  have key : reflective3 (M.op 0 1) (M.op 1 0) (M.op 1 1) (M.op 1 2) = M := by
    obtain ⟨op⟩ := M
    exact congrArg Magma.mk (Magma.op_eq_reflOp3 h₁).symm
  simp only [reflective3Exact, key, if_neg h₂]

end Magma

namespace Law.MagmaLaw

/-- **Exact-`C₃` certificate on `Fin 3`.** If `L'` has a model on `Fin 3` whose automorphism group
is exactly the rotation group, and no such magma satisfies `L`, then `L` is not structural from
`L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_cyclic3Exact {L L' : Law.NatMagmaLaw} {a b c : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.cyclic3Exact a b c) L')
    (htgt : ∀ a b c : Fin 3, ¬ @satisfies _ (Fin 3) (Magma.cyclic3Exact a b c) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.cyclic3Exact a b c) hsrc
  have h₁ : M'.IsEndo ⇑(Equiv.addRight (1 : Fin 3)) :=
    (Magma.cyclic3Exact_isEndo_addRight a b c).of_definable hfwd
  have h₂ : ¬ M'.IsEndo ⇑(Equiv.neg (Fin 3)) := fun hn ↦
    Magma.cyclic3Exact_not_isEndo_neg a b c (hn.of_definable hback)
  refine htgt (M'.op 0 0) (M'.op 0 1) (M'.op 0 2) ?_
  rw [Magma.cyclic3Exact_eq_self h₁ h₂]
  exact hM'

/-- **Exact-reflection certificate on `Fin 3`.** If `L'` has a model on `Fin 3` whose automorphism
group is exactly the order-`2` group generated by `x ↦ -x`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_reflective3Exact {L L' : Law.NatMagmaLaw} {a b c d : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.reflective3Exact a b c d) L')
    (htgt : ∀ a b c d : Fin 3, ¬ @satisfies _ (Fin 3) (Magma.reflective3Exact a b c d) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.reflective3Exact a b c d) hsrc
  have h₁ : M'.IsEndo ⇑(Equiv.neg (Fin 3)) :=
    (Magma.reflective3Exact_isEndo_neg a b c d).of_definable hfwd
  have h₂ : ¬ M'.IsEndo ⇑(Equiv.addRight (1 : Fin 3)) := fun hn ↦
    Magma.reflective3Exact_not_isEndo_addRight a b c d (hn.of_definable hback)
  refine htgt (M'.op 0 1) (M'.op 1 0) (M'.op 1 1) (M'.op 1 2) ?_
  rw [Magma.reflective3Exact_eq_self h₁ h₂]
  exact hM'

end Law.MagmaLaw
