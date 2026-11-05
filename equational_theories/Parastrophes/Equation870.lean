import equational_theories.Parastrophes.FiniteSolutions

/-! E870's left division has bijective columns because each column is a
composition of two left translations of multiplication. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

/-- Write `D` for left division. E870 gives `D(y,x) = (x*x)*(x*y)`.
For fixed x this is `L_(x*x) ∘ L_x`, hence bijective. A left quasigroup
and its left division have the same right-quasigroup status. -/
@[parastrophe_result] theorem quasigroup870_fin : QuasigroupLaw .fin Law870 := by
  intro G M hG h
  have hd := left_term870_fin G M hG h
  have hL := sideQuasigroup_of_division hd
  have hR : IsSideQuasigroup .right
      (termMagma M ((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ Lf 0))) := by
    intro x
    exact (hL (M.op x x)).comp (hL x)
  exact ⟨hL, (division_otherSide_iff hd).mp hR⟩

/-- If `D` is left division, then right division is
`x / y = D(x, D(x*x, y))`. Thus a single term works at every finite order. -/
@[parastrophe_result] theorem right_term870_fin :
    UniformTermWitness .fin Law870 .right
      ((((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆
        ((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆
        (((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ Lf 0)) := by
  intro G M hG h
  have hQ := quasigroup870_fin G M hG h
  have hD := left_term870_fin G M hG h
  let D := termMagma M ((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ Lf 0))
  have hi (x y : G) :
      D.op (M.op x y) (D.op (M.op (M.op x y) (M.op x y)) y) = x := by
    let c := M.op x y
    have he : M.op (M.op c c) (M.op c x) = y :=
      (hQ.1 x).1 ((@Law870.models_iff G M).mp h c x).symm
    have hh := congrArg (D.op (M.op c c)) he
    change D.op (M.op c c) (M.op (M.op c c) (M.op c x)) =
      D.op (M.op c c) y at hh
    rw [hD.2] at hh
    rw [← hh, hD.2]
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := (hQ.2 y).2 x
    exact congrArg (fun z => M.op z y) (hi a y)
  · exact hi

end Parastrophes.Catalogue
