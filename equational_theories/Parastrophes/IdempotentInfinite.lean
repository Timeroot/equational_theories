import equational_theories.Parastrophes.Attributes
import equational_theories.ManuallyProved.Equation63Idempotent
import equational_theories.Parastrophes.Equation1083
import equational_theories.Generated.Greedy.Eq1083Idempotent
import equational_theories.Generated.Greedy.Eq1313Idempotent
import equational_theories.Generated.Greedy.Eq1286Idempotent

/-! Infinite idempotent counterexamples to bijectivity. Every finite model of
these equations is a quasigroup, so finiteness is essential in those results. -/
namespace Parastrophes.Catalogue

/-- Under idempotence, E667 is exactly E63. -/
theorem idempotent667_iff63 {G : Type*} [Magma G] (h : ∀ x : G, x ◇ x = x) :
    Equation667 G ↔ Equation63 G := by
  simp only [Equation667, Equation63, h]

/-- E870 has exactly the same reduction under idempotence. -/
theorem idempotent870_iff63 {G : Type*} [Magma G] (h : ∀ x : G, x ◇ x = x) :
    Equation870 G ↔ Equation63 G := by
  simp only [Equation870, Equation63, h]

/-- The infinite idempotent E1313 model retains `0*1 = 0*2 = 3`. -/
@[parastrophe_result] theorem not_leftQuasigroup1313_all :
    ¬ SideQuasigroupLaw .all Law1313 .left := by
  intro h
  let e := Eq1313Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1313.models_iff Nat e.toMagma).mpr e.toMagma_equation1313)
  have h1 := e.of_R 0 1 3 (by unfold e Eq1313Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1313Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The same model retains the column collision `1*0 = 2*0 = 3`. -/
@[parastrophe_result] theorem not_rightQuasigroup1313_all :
    ¬ SideQuasigroupLaw .all Law1313 .right := by
  intro h
  let e := Eq1313Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1313.models_iff Nat e.toMagma).mpr e.toMagma_equation1313)
  have h1 := e.of_R 1 0 3 (by unfold e Eq1313Idempotent.collisionSeed; decide)
  have h2 := e.of_R 2 0 3 (by unfold e Eq1313Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The infinite idempotent E1286 model retains `0*1 = 0*2 = 3`. -/
@[parastrophe_result] theorem not_leftQuasigroup1286_all :
    ¬ SideQuasigroupLaw .all Law1286 .left := by
  intro h
  let e := Eq1286Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1286.models_iff Nat e.toMagma).mpr e.toMagma_equation1286)
  have h1 := e.of_R 0 1 3 (by unfold e Eq1286Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1286Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The same model retains the column collision `1*0 = 2*0 = 3`. -/
@[parastrophe_result] theorem not_rightQuasigroup1286_all :
    ¬ SideQuasigroupLaw .all Law1286 .right := by
  intro h
  let e := Eq1286Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1286.models_iff Nat e.toMagma).mpr e.toMagma_equation1286)
  have h1 := e.of_R 1 0 3 (by unfold e Eq1286Idempotent.collisionSeed; decide)
  have h2 := e.of_R 2 0 3 (by unfold e Eq1286Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The infinite idempotent E1083 model retains `0*1 = 0*2 = 3`. -/
@[parastrophe_result] theorem not_leftQuasigroup1083_all :
    ¬ SideQuasigroupLaw .all Law1083 .left := by
  intro h
  let e := Eq1083Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1083.models_iff Nat e.toMagma).mpr e.toMagma_equation1083)
  have h1 := e.of_R 0 1 3 (by unfold e Eq1083Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1083Idempotent.collisionSeed; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- A particular missing value: the zero column is injective but never equals 2. -/
theorem idempotent1083_column_zero_misses_two (x : Nat) :
    Eq1083Idempotent.collisionSeed.complFun x 0 ≠ 2 := by
  let e := Eq1083Idempotent.collisionSeed
  letI := e.toMagma
  have hE : Equation1083 Nat := e.toMagma_equation1083
  have h1 := e.of_R 0 1 3 (by unfold e Eq1083Idempotent.collisionSeed; decide)
  have h2 := e.of_R 0 2 3 (by unfold e Eq1083Idempotent.collisionSeed; decide)
  have h4 := e.of_R 4 0 1 (by unfold e Eq1083Idempotent.collisionSeed; decide)
  intro hx
  have hh : (Parastrophes.Eq1083.translationEquiv hE 0) x =
      (Parastrophes.Eq1083.translationEquiv hE 0) 4 := by
    change e.complFun 0 (e.complFun x 0) = e.complFun 0 (e.complFun 4 0)
    rw [hx, h4, h1, h2]
  have hx4 := (Parastrophes.Eq1083.translationEquiv hE 0).injective hh
  subst x
  exact (by decide : (1 : Nat) ≠ 2) (h4.symm.trans hx)

/-- Right translations need not be surjective, despite their universal injectivity. -/
@[parastrophe_result] theorem not_rightQuasigroup1083_all :
    ¬ SideQuasigroupLaw .all Law1083 .right := by
  intro h
  let e := Eq1083Idempotent.collisionSeed
  have hQ := h Nat e.toMagma trivial
    ((@Law1083.models_iff Nat e.toMagma).mpr e.toMagma_equation1083)
  obtain ⟨x, hx⟩ := (hQ 0).2 2
  exact idempotent1083_column_zero_misses_two x hx

/-- The idempotent free-group E63 model is also an E667 model. -/
@[parastrophe_result] theorem not_leftQuasigroup667_all :
    ¬ SideQuasigroupLaw .all Law667 .left := by
  intro h
  obtain ⟨M, h63, hid, hl, hr⟩ := Eq63Idempotent.countermodel
  letI := M
  have hE : Equation667 (FreeGroup Nat) := (idempotent667_iff63 hid).mpr h63
  have hQ := h (FreeGroup Nat) M trivial ((Law667.models_iff).mpr hE)
  exact hl (hQ 1).1

/-- The idempotent free-group E63 model is also an E667 model. -/
@[parastrophe_result] theorem not_rightQuasigroup667_all :
    ¬ SideQuasigroupLaw .all Law667 .right := by
  intro h
  obtain ⟨M, h63, hid, hl, hr⟩ := Eq63Idempotent.countermodel
  letI := M
  have hE : Equation667 (FreeGroup Nat) := (idempotent667_iff63 hid).mpr h63
  have hQ := h (FreeGroup Nat) M trivial ((Law667.models_iff).mpr hE)
  exact hr (hQ 1).1

/-- The idempotent free-group E63 model is also an E870 model. -/
@[parastrophe_result] theorem not_leftQuasigroup870_all :
    ¬ SideQuasigroupLaw .all Law870 .left := by
  intro h
  obtain ⟨M, h63, hid, hl, hr⟩ := Eq63Idempotent.countermodel
  letI := M
  have hE : Equation870 (FreeGroup Nat) := (idempotent870_iff63 hid).mpr h63
  have hQ := h (FreeGroup Nat) M trivial ((Law870.models_iff).mpr hE)
  exact hl (hQ 1).1

/-- The idempotent free-group E63 model is also an E870 model. -/
@[parastrophe_result] theorem not_rightQuasigroup870_all :
    ¬ SideQuasigroupLaw .all Law870 .right := by
  intro h
  obtain ⟨M, h63, hid, hl, hr⟩ := Eq63Idempotent.countermodel
  letI := M
  have hE : Equation870 (FreeGroup Nat) := (idempotent870_iff63 hid).mpr h63
  have hQ := h (FreeGroup Nat) M trivial ((Law870.models_iff).mpr hE)
  exact hr (hQ 1).1

end Parastrophes.Catalogue
