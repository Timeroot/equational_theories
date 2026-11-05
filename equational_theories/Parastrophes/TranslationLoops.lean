import equational_theories.Parastrophes.TranslationChains

/-! A right inverse made entirely of left translations upgrades surjectivity
to bijectivity, even on an infinite carrier. -/
namespace Parastrophes
open Law FreeMagma

/-- Suppose each left translation has a right inverse that is a word of left
translations. All translations are onto; hence each such word is onto, too.
An onto right inverse forces the original translation to be injective. -/
theorem leftQuasigroup_of_translationLoops {G : Type*} (M : Magma G)
    (word : G → List G)
    (h : ∀ y x, leftWord M (y :: word y) x = x) : IsSideQuasigroup .left M := by
  have hs (y : G) : Function.Surjective (M.op y) :=
    fun x => ⟨leftWord M (word y) x, h y x⟩
  have hw (w : List G) : Function.Surjective (leftWord M w) := by
    induction w with
    | nil => exact Function.surjective_id
    | cons y w ih => exact (hs y).comp ih
  intro y
  refine ⟨?_, hs y⟩
  intro a b hab
  obtain ⟨c, rfl⟩ := hw (word y) a
  obtain ⟨d, rfl⟩ := hw (word y) b
  change leftWord M (y :: word y) c = leftWord M (y :: word y) d at hab
  rw [h, h] at hab
  rw [hab]

namespace Catalogue

/-- E716 gives `L_y L_y L_(y*y) = 1`. The final factor is onto, so these
translations are bijective without a finiteness assumption. -/
@[parastrophe_result] theorem left_term716_all :
    UniformTermWitness .all Law716 .left (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  intro G M _ h
  have hh := (@Law716.models_iff G M).mp h
  have hQ := leftQuasigroup_of_translationLoops M (fun y => [y, M.op y y])
    (fun y x => (hh x y).symm)
  exact ⟨fun x y => (hh y x).symm, fun x y => (hQ x).1 (hh (M.op x y) x).symm⟩

/-- E1122 gives `L_y L_(y*(y*y)) = 1`; both factors belong to the same
surjective family, so this is also a left inverse. -/
@[parastrophe_result] theorem left_term1122_all :
    UniformTermWitness .all Law1122 .left ((Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law1122.models_iff G M).mp h
  have hQ := leftQuasigroup_of_translationLoops M (fun y => [M.op y (M.op y y)])
    (fun y x => (hh x y).symm)
  exact ⟨fun x y => (hh y x).symm, fun x y => (hQ x).1 (hh (M.op x y) x).symm⟩

/-- E1325 gives `L_y L_((y*y)*y) = 1`, with the same conclusion. -/
@[parastrophe_result] theorem left_term1325_all :
    UniformTermWitness .all Law1325 .left (((Lf 0 ⋆ Lf 0) ⋆ Lf 0) ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law1325.models_iff G M).mp h
  have hQ := leftQuasigroup_of_translationLoops M (fun y => [M.op (M.op y y) y])
    (fun y x => (hh x y).symm)
  exact ⟨fun x y => (hh y x).symm, fun x y => (hQ x).1 (hh (M.op x y) x).symm⟩

end Catalogue
end Parastrophes
