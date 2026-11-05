import equational_theories.Parastrophes.TranslationLoops

/-! Exact left-division images obtained by reparameterizing the indices of
left translations and reversing their compositions. These three laws are
preserved by left division on arbitrary carriers. -/

namespace Parastrophes.Catalogue

private theorem left765 {G : Type} {M D : Magma G}
    (hd : IsDivision .left M D) (h : @Equation765 G M) : @Equation765 G D := by
  intro x y z
  have hh := h (M.op y x) y (D.op y z)
  rw [hd.1] at hh
  have he := (leftWord_eq_iff hd [y, D.op y z, z] (M.op y x) (M.op y x)).mp hh.symm
  change D.op z (D.op (D.op y z) (D.op y (M.op y x))) = M.op y x at he
  rw [hd.2] at he
  have hh := congrArg (D.op y) he
  rw [hd.2] at hh
  exact hh.symm

private theorem left778 {G : Type} {M D : Magma G}
    (hd : IsDivision .left M D) (h : @Equation778 G M) : @Equation778 G D := by
  intro x y z
  have hh := h x (D.op z y) z
  rw [hd.1] at hh
  exact ((leftWord_eq_iff hd [D.op z y, z, y] x x).mp hh.symm).symm

private theorem left1184 {G : Type} {M D : Magma G}
    (hd : IsDivision .left M D) (h : @Equation1184 G M) : @Equation1184 G D := by
  intro x y z
  have hh := h x (D.op z (D.op z y)) z
  rw [hd.1, hd.1] at hh
  exact ((leftWord_eq_iff hd [D.op z (D.op z y), y] x x).mp hh.symm).symm

/-- E765 characterizes its own left-division image: invert the translation
identity at `y` and `y \ z`, then rotate its three factors. -/
@[parastrophe_result] theorem left_characterizes765_all :
    Characterizes .all Law765 .left Law765 := by
  apply characterizes_of_division
  · intro G M _ h
    have hh := (@Law765.models_iff G M).mp h
    exact leftQuasigroup_of_translationLoops M (fun y => [y, M.op y y])
      (fun y x => (hh x y y).symm)
  all_goals
    intro G M D _ hd h
    exact (@Law765.models_iff G D).mpr (left765 hd ((@Law765.models_iff G M).mp h))

/-- E778 characterizes its own left-division image: reverse the translation
identity after substituting `z \ y` for its first index. -/
@[parastrophe_result] theorem left_characterizes778_all :
    Characterizes .all Law778 .left Law778 := by
  apply characterizes_of_division
  · intro G M _ h
    have hh := (@Law778.models_iff G M).mp h
    exact leftQuasigroup_of_translationLoops M (fun y => [y, M.op y y])
      (fun y x => (hh x y y).symm)
  all_goals
    intro G M D _ hd h
    exact (@Law778.models_iff G D).mpr (left778 hd ((@Law778.models_iff G M).mp h))

/-- E1184 characterizes its own left-division image: its relation between the
translations at `y` and `z * (z * y)` also holds along the inverse orbit. -/
@[parastrophe_result] theorem left_characterizes1184_all :
    Characterizes .all Law1184 .left Law1184 := by
  apply characterizes_of_division
  · intro G M _ h
    have hh := (@Law1184.models_iff G M).mp h
    exact leftQuasigroup_of_translationLoops M (fun y => [M.op y (M.op y y)])
      (fun y x => (hh x y y).symm)
  all_goals
    intro G M D _ hd h
    exact (@Law1184.models_iff G D).mpr (left1184 hd ((@Law1184.models_iff G M).mp h))

end Parastrophes.Catalogue
