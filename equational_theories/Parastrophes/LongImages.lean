import equational_theories.Parastrophes.TranslationLoops

/-! Exact division images need not have a defining law in the main four-operation
catalogue. E727's target is E10577 in the extended five-operation list. It is exported
as a term tree, with the same proof and duality handling as numbered targets. -/

namespace Parastrophes
open Law FreeMagma

/-- E10577, the five-operation identity `x = y * ((z*y) * ((z*y) * x))`. -/
def leftImage727 : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ ((Lf 2 ⋆ Lf 1) ⋆ ((Lf 2 ⋆ Lf 1) ⋆ Lf 0))⟩

theorem leftImage727_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage727 ↔
      ∀ x y z, x = M.op y (M.op (M.op z y) (M.op (M.op z y) x)) := by
  constructor
  · intro h x y z
    exact h (fun n => if n = 0 then x else if n = 1 then y else z)
  · intro h v
    exact h (v 0) (v 1) (v 2)

namespace Catalogue

/-- E727's left-division image has a five-operation defining identity.
Reparameterize `z*y` as a new variable and invert the translation chain;
the converse is the same calculation in reverse. Both laws force left
bijectivity on arbitrary carriers, so this is an exact characterization. -/
@[parastrophe_result] theorem left_characterizes727_all_long :
    Characterizes .all Law727 .left leftImage727 := by
  apply characterizes_of_division
  · intro G M _ h
    have hh := (leftImage727_iff M).mp h
    exact leftQuasigroup_of_translationLoops M (fun y => [M.op y y,M.op y y])
      (fun y x => (hh x y y).symm)
  · intro G M D _ hd h
    have hh := (@Law727.models_iff G M).mp h
    apply (leftImage727_iff D).mpr
    intro x y z
    have he := hh x (D.op z y) z
    rw [hd.1] at he
    exact ((leftWord_eq_iff hd [D.op z y,D.op z y,y] x x).mp he.symm).symm
  · intro G M D _ hd h
    have hh := (leftImage727_iff M).mp h
    apply (@Law727.models_iff G D).mpr
    intro x y z
    have he := hh x (D.op z y) z
    rw [hd.1] at he
    exact ((leftWord_eq_iff hd [D.op z y,y,y] x x).mp he.symm).symm

end Catalogue
end Parastrophes
