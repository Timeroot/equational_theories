import equational_theories.Definability.Const41Rigid

/-!
# `StructuralFrom Law41`, the seven idempotent targets

See `Definability/Const41Rigid.lean` for the device.  Each proof splits on whether `tC` (resp. `tB`)
has a right identity (resp. left zero) other than the source constant: if it does not, the constant
is `∅`-definable and the tree itself is the witness; if it does, the witness *is* a two-element
carrier and a hand-built two-valued operation takes over.
-/

open Law Law.MagmaLaw Const41

namespace Law.MagmaLaw

/-- `x = (x ◇ x) ◇ (x ◇ y)` -/
theorem Equation152_StructuralFrom_Equation41 : Law152.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v
  · refine structuralOn_tC M h41 h3 ?_
    rw [@Law152.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tC_apply M c _ _ hc]
    grind (splits := 24)
  · push Not at h3
    obtain ⟨z, u, v, hz, hzc⟩ := h3
    have htwo := two_of_rid M h41 z u v hz hzc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo hzc
    refine structuralOn_twoA M c z hc hzc htwo ?_
    rw [@Law152.models_iff]
    intro x y
    simp only [twoA_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;> simp_all

/-- `x = (x ◇ x) ◇ (y ◇ x)` -/
theorem Equation153_StructuralFrom_Equation41 : Law153.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v
  · refine structuralOn_tC M h41 h3 ?_
    rw [@Law153.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tC_apply M c _ _ hc]
    grind (splits := 24)
  · push Not at h3
    obtain ⟨z, u, v, hz, hzc⟩ := h3
    have htwo := two_of_rid M h41 z u v hz hzc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo hzc
    refine structuralOn_twoA M c z hc hzc htwo ?_
    rw [@Law153.models_iff]
    intro x y
    simp only [twoA_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;> simp_all

/-- `x = (x ◇ x) ◇ (x ◇ (x ◇ y))` -/
theorem Equation1427_StructuralFrom_Equation41 : Law1427.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v
  · refine structuralOn_tC M h41 h3 ?_
    rw [@Law1427.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tC_apply M c _ _ hc]
    grind (splits := 24)
  · push Not at h3
    obtain ⟨z, u, v, hz, hzc⟩ := h3
    have htwo := two_of_rid M h41 z u v hz hzc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo hzc
    refine structuralOn_twoA M c z hc hzc htwo ?_
    rw [@Law1427.models_iff]
    intro x y
    simp only [twoA_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;> simp_all

/-- `x = (x ◇ x) ◇ (x ◇ (y ◇ x))` -/
theorem Equation1428_StructuralFrom_Equation41 : Law1428.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v
  · refine structuralOn_tC M h41 h3 ?_
    rw [@Law1428.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tC_apply M c _ _ hc]
    grind (splits := 24)
  · push Not at h3
    obtain ⟨z, u, v, hz, hzc⟩ := h3
    have htwo := two_of_rid M h41 z u v hz hzc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo hzc
    refine structuralOn_twoA M c z hc hzc htwo ?_
    rw [@Law1428.models_iff]
    intro x y
    simp only [twoA_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;> simp_all

/-- `x = (x ◇ x) ◇ ((y ◇ x) ◇ x)` -/
theorem Equation1634_StructuralFrom_Equation41 : Law1634.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v
  · refine structuralOn_tC M h41 h3 ?_
    rw [@Law1634.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tC_apply M c _ _ hc]
    grind (splits := 24)
  · push Not at h3
    obtain ⟨z, u, v, hz, hzc⟩ := h3
    have htwo := two_of_rid M h41 z u v hz hzc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo hzc
    refine structuralOn_twoA M c z hc hzc htwo ?_
    rw [@Law1634.models_iff]
    intro x y
    simp only [twoA_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;> simp_all

/-- `x = (x ◇ x) ◇ ((y ◇ x) ◇ y)`

The only one of the seven whose two-element model is not `twoA`: on `{c, d}` the law forces
`c ◇ d = d`, which `twoA` does not do.  The parity operation does. -/
theorem Equation1635_StructuralFrom_Equation41 : Law1635.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v
  · refine structuralOn_tC M h41 h3 ?_
    rw [@Law1635.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tC_apply M c _ _ hc]
    grind (splits := 24)
  · push Not at h3
    obtain ⟨z, u, v, hz, hzc⟩ := h3
    have htwo := two_of_rid M h41 z u v hz hzc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo hzc
    refine structuralOn_twoX M c z hc hzc htwo ?_
    rw [@Law1635.models_iff]
    intro x y
    simp only [twoX_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;> simp_all

/-- `x = (x ◇ y) ◇ ((y ◇ z) ◇ x)`

Three variables, and `tC` fails it: the tree that works is `tB`, whose definable point is its left
zero rather than its right identity. -/
theorem Equation1660_StructuralFrom_Equation41 : Law1660.StructuralFrom Law41 := by
  intro G M hM
  classical
  have h41 : Equation41 G := Law41.models_iff.mp hM
  by_cases h3 : ∀ z u v : G, (∀ p : G, (tB.magma M).op z p = z) → z = M.op u v
  · refine structuralOn_tB M h41 h3 ?_
    rw [@Law1660.models_iff]
    intro x y w
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [tB_apply M c _ _ hc]
    grind (splits := 32)
  · push Not at h3
    obtain ⟨t, u, v, ht, htc⟩ := h3
    have htwo := two_of_lzero M h41 t u v ht htc
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
    rw [hc u v] at htwo htc
    refine structuralOn_twoA M c t hc htc htwo ?_
    rw [@Law1660.models_iff]
    intro x y w
    simp only [twoA_apply]
    rcases htwo x with hx | hx <;> rcases htwo y with hy | hy <;>
      rcases htwo w with hw | hw <;> simp_all

end Law.MagmaLaw
