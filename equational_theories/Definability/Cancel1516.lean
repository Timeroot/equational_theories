import equational_theories.Definability.AutBox

/-!
# `Law1516` is a quasigroup on every finite carrier

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

Square roots then buy the columns too.  Reading the law at `x := u ◇ v` with `y` a square root `t`
of `u` and cancelling the leading `u` gives `(u ◇ v) ◇ ((u ◇ v) ◇ t) = v`: the product `u ◇ v`
determines a square root of its own left factor, so `v ◇ u = v' ◇ u` forces `√v = √v'` and hence
`v = v'`.  Every finite model is therefore a two-sided quasigroup, which is what a `QTerm` witness
needs before it may spend `/` -- see `injRight_Equation1516`.
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

/-- Squaring is onto on every finite model of `Law1516` -- the middle step of
`cancelLeft_Equation1516`, kept separately because right cancellation needs the square roots and
not the cancellation. -/
theorem sqSurj_Equation1516 {G : Type} [Finite G] (M : Magma G) (hM : satisfies G Law1516) :
    ∀ u : G, ∃ t : G, M.op t t = u := by
  have h := (@Law1516.models_iff G M).mp hM
  have hinj : ∀ a : G, Function.Injective (fun z : G ↦ M.op (M.op a a) z) :=
    fun a ↦ Finite.injective_iff_surjective.mpr fun z ↦ ⟨M.op z (M.op z a), (h z a).symm⟩
  have hsq : Function.Injective (fun a : G ↦ M.op a a) := by
    intro a b hab
    have key : ∀ x : G, M.op x (M.op x a) = M.op x (M.op x b) := by
      intro x
      refine hinj a ?_
      show M.op (M.op a a) (M.op x (M.op x a)) = M.op (M.op a a) (M.op x (M.op x b))
      rw [← h x a, show M.op a a = M.op b b from hab, ← h x b]
    exact hinj a (hinj a (key (M.op a a)))
  exact Finite.injective_iff_surjective.mp hsq

/-- Every finite model of `Law1516` is right cancellative, so the finite models are *two-sided*
quasigroups and both divisions are available.

The law read at `x := u ◇ v` and `y := t` with `t ◇ t = u` says
`u ◇ v = u ◇ ((u ◇ v) ◇ ((u ◇ v) ◇ t))`, and left cancellation turns that into

  `(u ◇ v) ◇ ((u ◇ v) ◇ t) = v`   whenever   `t ◇ t = u`,

which recovers a square root of the *left* factor from the product alone.  So if `v ◇ u = v' ◇ u`
then the square roots of `v` and of `v'` are both `L_{v ◇ u}`-preimages of `u` at depth two; two
more left cancellations identify them, and squaring sends them back to `v = v'`. -/
theorem cancelRight_Equation1516 : AutBox.CancelRight Law1516 := by
  intro G _ M hM u v v' huv
  have h := (@Law1516.models_iff G M).mp hM
  have hcl := cancelLeft_Equation1516 M hM
  -- a square root of the left factor is read off the product
  have key : ∀ x y t : G, M.op t t = x → M.op (M.op x y) (M.op (M.op x y) t) = y := by
    intro x y t ht
    refine hcl x _ _ ?_
    have e := h (M.op x y) t
    rw [ht] at e
    exact e.symm
  obtain ⟨s, hs⟩ := sqSurj_Equation1516 M hM v
  obtain ⟨s', hs'⟩ := sqSurj_Equation1516 M hM v'
  have e1 := key v u s hs
  have e2 := key v' u s' hs'
  rw [← huv] at e2
  rw [← hs, ← hs', hcl _ _ _ (hcl _ _ _ (e1.trans e2.symm))]

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

/-- Every finite model of `Law1516` is a *right* quasigroup as well, so a `QTerm` witness may spend
both divisions.  This is the `hr` hypothesis of `termDefinableFromFin_of_qterm`. -/
theorem injRight_Equation1516 (G : Type) [Finite G] (M : Magma G) (h : satisfies G Law1516) :
    ∀ b : G, Function.Injective fun a ↦ M.op a b :=
  fun b _ _ ha ↦ cancelRight_Equation1516 M h b _ _ ha

end Law.MagmaLaw
