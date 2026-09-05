import equational_theories.Definability.AutBox

/-!
# `Law1516` is a left quasigroup on every finite carrier

`x = (y ◇ y) ◇ (x ◇ (x ◇ y))` says that `L_{y ◇ y}` is onto, with `x ↦ x ◇ (x ◇ y)` for a section.
That is a statement about the *squares* only, and over all magmas it is all one gets: no term
`t` with `t(u) ◇ t(u) = u` is known, so most rows are not visibly reached at all, and both
`DiagRow.RowQG` and `DivisionFO.LDiv` stay out of reach.

On a finite carrier the squares are enough to bootstrap the whole quasigroup:

* `L_{a ◇ a}` is onto, hence injective;
* if `a ◇ a = b ◇ b` then cancelling that row in the law gives `x ◇ (x ◇ a) = x ◇ (x ◇ b)` for
  every `x`; reading it at `x := a ◇ a` and cancelling twice more gives `a = b`, so squaring is
  injective;
* squaring is therefore onto, so *every* element is some `a ◇ a` and every row is injective.

So `AutBox.CancelLeft Law1516` holds, and with it the whole finite diagonal family --
`AutBox.diagFix_of_cancelLeft` needs nothing else.
-/

open Law Law.MagmaLaw

namespace Law.MagmaLaw

/-- Every finite model of `Law1516` is left cancellative. -/
theorem cancelLeft_Equation1516 : AutBox.CancelLeft Law1516 := by
  intro G _ M hM u v v' huv
  have h := (@Law1516.models_iff G M).mp hM
  -- the row of a square is onto: the law itself names the solution
  have hsurj : ∀ a : G, Function.Surjective (fun z : G ↦ M.op (M.op a a) z) :=
    fun a z ↦ ⟨M.op z (M.op z a), (h z a).symm⟩
  have hinj : ∀ a : G, Function.Injective (fun z : G ↦ M.op (M.op a a) z) :=
    fun a ↦ Finite.injective_iff_surjective.mpr (hsurj a)
  -- squaring is injective: cancel the common row out of the law, then cancel twice at `a ◇ a`
  have hsq : Function.Injective (fun a : G ↦ M.op a a) := by
    intro a b hab
    have key : ∀ x : G, M.op x (M.op x a) = M.op x (M.op x b) := by
      intro x
      refine hinj a ?_
      show M.op (M.op a a) (M.op x (M.op x a)) = M.op (M.op a a) (M.op x (M.op x b))
      rw [← h x a, show M.op a a = M.op b b from hab, ← h x b]
    exact hinj a (hinj a (key (M.op a a)))
  -- hence onto, so every element heads a row of the previous kind
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.mp hsq u
  exact hinj a (by simp only [ha]; exact huv)

/-- The diagonal obligation for `Law1516`, from left cancellation. -/
theorem diagFix_Equation1516 : AutBox.DiagFix Law1516 :=
  AutBox.diagFix_of_cancelLeft cancelLeft_Equation1516

/-- `x = x ◇ x` is structural on the finite models of `Law1516`: the companion is the `idem` box
`x □ y = if x = y then x else x ◇ y`, and left cancellation is the whole of its reverse half. -/
theorem Equation3_StructuralFromFin_Equation1516 : Law3.StructuralFromFin Law1516 :=
  AutBox.structuralFromFin_cancelLeft cancelLeft_Equation1516

/-- Every finite model of `Law1516` is a left quasigroup: left cancellation is injectivity of the
left translations, and a finite injective self-map is onto.  This is the hypothesis
`DivisionStructural.termStructuralFromFin_of_leftDiv'` spends. -/
theorem injLeft_Equation1516 (G : Type) [Finite G] (M : Magma G) (h : satisfies G Law1516) :
    ∀ a : G, Function.Injective fun b ↦ M.op a b :=
  fun a _ _ hb ↦ cancelLeft_Equation1516 M h a _ _ hb

end Law.MagmaLaw
