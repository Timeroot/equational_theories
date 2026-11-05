import equational_theories.Parastrophes.Attributes
import equational_theories.Obelix
import equational_theories.Generated.Greedy.Eq511
import equational_theories.ManuallyProved.Equation917
import equational_theories.ManuallyProved.Equation1117
import equational_theories.ManuallyProved.Equation1289
import equational_theories.ManuallyProved.Equation1323
import equational_theories.ManuallyProved.Equation1692
import equational_theories.ManuallyProved.Equation1729
import equational_theories.Confluence1
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.Greedy.Eq677
import equational_theories.Generated.Greedy.Eq906

/-! Further established infinite countermodels, recording the failed side.
All these laws force finite left bijectivity; the obstruction is
specifically to extending the finite assertion to arbitrary carriers. -/
namespace Parastrophes.Catalogue

/-- The saved E906 countermodel has `1*1 = 1*2 = 2`. Its first row is
therefore not injective, independently of the identity it was built to refute. -/
@[parastrophe_result] theorem not_leftQuasigroup906_all :
    ¬ SideQuasigroupLaw .all Law906 .left := by
  intro h
  let e := Eq906.PartialSolution.counter3862
  have hQ := h Nat e.toMagma trivial
    ((@Law906.models_iff Nat e.toMagma).mpr e.toMagma_equation906)
  have h1 := e.of_R 1 1 2 (by unfold e Eq906.PartialSolution.counter3862; decide)
  have h2 := e.of_R 1 2 2 (by unfold e Eq906.PartialSolution.counter3862; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 1).1 (h1.trans h2.symm))

/-- In a quasigroup satisfying E677, every element has a left fixer. Left
cancellation identifies that fixer as `(x*x)*x`, forcing E255. The established
infinite E677 countermodel therefore cannot be a quasigroup. -/
@[parastrophe_result] theorem not_quasigroup677_all : ¬ QuasigroupLaw .all Law677 := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation677_not_implies_Equation255
  have hQ := h G M trivial ((@Law677.models_iff G M).mpr hE)
  apply hn
  intro x
  obtain ⟨y, hy⟩ := (hQ.2 x).2 x
  have hinv : M.op y (M.op x (M.op x y)) = x := by
    simpa only [hy] using (hE x y).symm
  have hxy : x = M.op x (M.op x y) := (hQ.1 y).1 (hy.trans hinv.symm)
  have hf : y = M.op (M.op x x) x :=
    (hQ.1 x).1 ((hQ.1 x).1 (hxy.symm.trans (hE x x)))
  rw [← hf]
  exact hy.symm

/-- E1692 already makes left translations injective. Surjectivity would rotate
it to E63, contradicting the established countermodel to E23. -/
@[parastrophe_result] theorem not_leftQuasigroup1692_all :
    ¬ SideQuasigroupLaw .all Law1692 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation1692_not_implies_Equation23
  have hQ := h G M trivial ((@Law1692.models_iff G M).mpr hE)
  apply hn
  apply @Equation63_implies_Equation23 G M
  intro x y
  obtain ⟨a, ha⟩ := (hQ y).2 x
  have hh := hE a y
  rw [ha] at hh
  exact ha.symm.trans (congrArg (M.op y) hh)

/-- Surjective left translations would rotate E1729 to E917. Its diagonal
specialization E817 fails in the existing infinite countermodel. -/
@[parastrophe_result] theorem not_leftQuasigroup1729_all :
    ¬ SideQuasigroupLaw .all Law1729 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Eq1729.not_817
  have hQ := h G M trivial ((@Law1729.models_iff G M).mpr hE)
  apply hn
  intro x
  obtain ⟨a, ha⟩ := (hQ x).2 x
  have hh := hE a x
  rw [ha] at hh
  exact ha.symm.trans (congrArg (M.op x) hh)

/-- In the free normal-form E467 magma, the row of `a` takes the same value
at the leaf `b` and at `(a*b)*((a*b)*(a*a))`, which is a different normal form. -/
@[parastrophe_result] theorem not_leftQuasigroup467_all :
    ¬ SideQuasigroupLaw .all Law467 .left := by
  intro h
  let G := Confluence.ConfMagma (@rw467.rule Nat inferInstance)
  have hE : Equation467 G := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, Confluence.bu, hx, hy]
  have hQ := h G inferInstance trivial ((@Law467.models_iff G _).mpr hE)
  let a : G := (0 : Nat)
  let b : G := (1 : Nat)
  have hc : a ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ a))) = a ◇ b := (hE (a ◇ b) a).symm
  have hn : (a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ a)) ≠ b := by decide
  exact hn ((hQ a).1 hc)

/-- In the same E467 normal-form model, multiplication on the right by a leaf
never gives a leaf: the rewrite rule requires a compound right argument. -/
@[parastrophe_result] theorem not_rightQuasigroup467_all :
    ¬ SideQuasigroupLaw .all Law467 .right := by
  intro h
  let G := Confluence.ConfMagma (@rw467.rule Nat inferInstance)
  have hE : Equation467 G := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, Confluence.bu, hx, hy]
  have hQ := h G inferInstance trivial ((@Law467.models_iff G _).mpr hE)
  let a : G := (0 : Nat)
  obtain ⟨⟨b, hb⟩, he⟩ := (hQ a).2 a
  have hv := congrArg Subtype.val he
  simp [Magma.op, Confluence.bu, a, hb, rw467.rule] at hv

/-- The existing E1110 normal-form construction has the same obstruction:
a product whose right argument is a leaf cannot reduce to a leaf. -/
@[parastrophe_result] theorem not_rightQuasigroup1110_all :
    ¬ SideQuasigroupLaw .all Law1110 .right := by
  intro h
  let G := Confluence.ConfMagma (@rw1110.rule Nat inferInstance)
  have hE : Equation1110 G := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, Confluence.bu, hx, hy]
  have hQ := h G inferInstance trivial ((@Law1110.models_iff G _).mpr hE)
  let a : G := (0 : Nat)
  obtain ⟨⟨b, hb⟩, he⟩ := (hQ a).2 a
  have hv := congrArg Subtype.val he
  simp [Magma.op, Confluence.bu, a, hb, rw1110.rule] at hv

/-- Left cancellation would rotate E511 to E714, contradicted by the saved model. -/
@[parastrophe_result] theorem not_leftQuasigroup511_all :
    ¬ SideQuasigroupLaw .all Law511 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation511_not_implies_Equation714
  have hQ := h G M trivial ((@Law511.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- Left cancellation would rotate E1289 to E3116, contradicted by its saved model. -/
@[parastrophe_result] theorem not_leftQuasigroup1289_all :
    ¬ SideQuasigroupLaw .all Law1289 .left := by
  intro h
  obtain ⟨G, M, hE, hn, _⟩ := Eq1289.not_3116_4435
  have hQ := h G M trivial ((@Law1289.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- Left cancellation would rotate E1323 to E2744, contradicted by its saved model. -/
@[parastrophe_result] theorem not_leftQuasigroup1323_all :
    ¬ SideQuasigroupLaw .all Law1323 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Eq1323.Equation1323_not_implies_Equation2744
  have hQ := h G M trivial ((@Law1323.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

private theorem integer1117 :
    @satisfies _ Int (⟨Eq1117.op⟩ : Magma Int) Law1117 := by
  apply (@Law1117.models_iff Int (⟨Eq1117.op⟩ : Magma Int)).mpr
  intro x y z
  change x = Eq1117.op y (Eq1117.op (Eq1117.op y (Eq1117.op x z)) z)
  simp only [Eq1117.op]
  omega

/-- The existing integer model x*y = 2*x - floor(y/2) has equal entries at 0 and 1. -/
@[parastrophe_result] theorem not_leftQuasigroup1117_all :
    ¬ SideQuasigroupLaw .all Law1117 .left := by
  intro h
  have hQ := h Int ⟨Eq1117.op⟩ trivial integer1117
  exact (by decide : (0 : Int) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) (by decide))

/-- The same integer model also fails right surjectivity: its zero column is
`x ↦ 2*x`, so it never attains 1. These are independent failures of the two sides. -/
@[parastrophe_result] theorem not_rightQuasigroup1117_all :
    ¬ SideQuasigroupLaw .all Law1117 .right := by
  intro h
  have hQ := h Int ⟨Eq1117.op⟩ trivial integer1117
  obtain ⟨x, hx⟩ := (hQ 0).2 1
  change 2*x - 0/2 = 1 at hx
  omega

/-- The E917 free-group construction already has a collision in its identity row. -/
@[parastrophe_result] theorem not_leftQuasigroup917_all :
    ¬ SideQuasigroupLaw .all Law917 .left := by
  intro h
  let a : FreeGroup Nat := FreeGroup.of 1
  let b : FreeGroup Nat := FreeGroup.of 2
  let c : FreeGroup Nat := FreeGroup.of 3
  let e : Eq917.Greedy.Extension :=
    ⟨Eq917.Greedy.fromList [(1,a),(a^2,1),(a⁻¹,b),(b,c),(c*a,a)], Eq917.Greedy.fromList_ok⟩
  have hQ := h (Eq917.Greedy.GreedyMagma e) inferInstance trivial
    ((@Law917.models_iff _ _).mpr (Eq917.Greedy.eq917 e))
  have he : @Magma.op (Eq917.Greedy.GreedyMagma e) _ (1 : FreeGroup Nat) (1 : FreeGroup Nat) =
      @Magma.op (Eq917.Greedy.GreedyMagma e) _ (1 : FreeGroup Nat) (c*a) := by
    change Eq917.Greedy.f e (1 * 1⁻¹) * 1 = Eq917.Greedy.f e ((c*a) * 1⁻¹) * 1
    simp only [inv_one, mul_one]
    rw [Eq917.Greedy.fromList_eval (e := e) rfl 1 a,
      Eq917.Greedy.fromList_eval (e := e) rfl (c*a) a]
  exact (by decide : (1 : FreeGroup Nat) ≠ c*a) ((hQ (1 : FreeGroup Nat)).1 he)

/-- E1491 supplies injective left translations. If they were also surjective,
the law would rotate to E65, contradicting the existing Obelix model. -/
@[parastrophe_result] theorem not_leftQuasigroup1491_all :
    ¬ SideQuasigroupLaw .all Law1491 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Obelix.PartialSolution.Equation1491_facts
  have hQ := h G M trivial ((@Law1491.models_iff G M).mpr hE)
  apply hn
  intro x y
  obtain ⟨a, ha⟩ := (hQ y).2 x
  have hh := hE a y
  rw [ha] at hh
  exact ha.symm.trans (congrArg (M.op y) hh)

end Parastrophes.Catalogue
