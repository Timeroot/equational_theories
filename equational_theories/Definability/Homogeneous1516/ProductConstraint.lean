import equational_theories.Definability.Homogeneous1516.Normalization
import equational_theories.Definability.HomogeneousQuasigroupProduct

/-! An additional product consequence of the existing homogeneous E1516
normalization. Kept separate from the checked classification dependency tree. -/

namespace Definability.Homogeneous1516.Normalized

variable {K : Type} [Field K] [Finite K]

theorem zero_eq_neg_cube_div {f g : K → K} {c s : K}
    (h : Normalized f g c s) : f 0 = -(c ^ 3) / s := by
  classical
  letI := Fintype.ofFinite K
  have hb : g 0 ≠ 0 := by
    intro hb
    have he := h.fg 0
    rw [hb] at he
    exact h.f_zero_ne_zero he
  calc
    f 0 = -c * g 0 := HomogeneousQuasigroup.zero_product_of_profiles f c (g 0)
      h.bijective hb (h.fg 0) h.profile_ne h.profile_injective
    _ = -(c ^ 3) / s := by rw [← h.zero_right]; ring

/-- info: 'Definability.Homogeneous1516.Normalized.zero_eq_neg_cube_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_eq_neg_cube_div

end Definability.Homogeneous1516.Normalized
