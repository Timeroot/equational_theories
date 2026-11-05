import equational_theories.Parastrophes.TranslationChains
import equational_theories.Parastrophes.Equation510

/-! E138 controls the translation indexed by every product, rather than just a
square. This control survives passage to actual left division. -/
namespace Parastrophes.Catalogue

private theorem left138 {G : Type} {M D : Magma G}
    (hd : IsDivision .left M D) (h : @Equation138 G M) : @Equation138 G D := by
  intro x y z
  have he := h x (D.op z y) z
  rw [hd.1] at he
  exact ((leftWord_eq_iff hd [D.op z y, y] x x).mp he.symm).symm

/-- Every model of E138 becomes another model of E138 under left division,
and taking left division again gives the converse. This holds on all carriers. -/
@[parastrophe_result] theorem left_characterizes138_all :
    Characterizes .all Law138 .left Law138 := by
  apply characterizes_of_division
  · intro G M _ h
    have he := (@Law138.models_iff G M).mp h
    exact sideQuasigroup_of_division (left_term127 G M trivial
      ((@Law127.models_iff G M).mpr (fun x y => he x y y)))
  all_goals
    intro G M D _ hd h
    exact (@Law138.models_iff G D).mpr (left138 hd ((@Law138.models_iff G M).mp h))

private theorem left510 {G : Type} {M D : Magma G}
    (hd : IsDivision .left M D) (h : @Equation510 G M) : @Equation510 G D := by
  have hq := sideQuasigroup_of_division hd
  have sq (x : G) : M.op (D.op x x) (D.op x x) = x := by
    apply (hq x).1
    rw [@square510 G M h, hd.1]
  intro x y
  have he := (leftWord_eq_iff hd [y, y, y]
    (M.op (D.op x x) (D.op x x)) (D.op x x)).mp (h (D.op x x) y).symm
  exact (he.trans (sq x)).symm

/-- In E510, division reverses both the left translations and the square map.
Their inverse relation is therefore unchanged, giving an exact self-image. -/
@[parastrophe_result] theorem left_characterizes510_all :
    Characterizes .all Law510 .left Law510 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_, left_term510_all⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law510.models_iff G D).mpr (left510 hd ((@Law510.models_iff G M).mp h))

end Parastrophes.Catalogue
