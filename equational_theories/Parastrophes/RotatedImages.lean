import equational_theories.Parastrophes.TranslationLoops

/-!
# Longer exact identities obtained by rotating multiplication constraints

The five-operation identities below are E9321 and E10200 in
`data/eq_size5.txt`. Replacing each constraint `a * b = c` by
`a \\ c = b`, and choosing new independent variables, eliminates the
original multiplication. Both directions are explicit cancellations.
-/
namespace Parastrophes
open Law FreeMagma

/-- E9321: `x = y * ((x*y) * (x * (x*y)))`. -/
def leftImage677 : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1)))⟩

/-- E10200: `x = y * ((x*y) * ((x*y) * x))`. -/
def leftImage706 : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0))⟩

theorem leftImage677_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage677 ↔
      ∀ x y, x = M.op y (M.op (M.op x y) (M.op x (M.op x y))) := by
  constructor
  · intro h x y
    exact h (fun n => if n = 0 then x else y)
  · intro h v
    exact h (v 0) (v 1)

theorem leftImage706_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage706 ↔
      ∀ x y, x = M.op y (M.op (M.op x y) (M.op (M.op x y) x)) := by
  constructor
  · intro h x y
    exact h (fun n => if n = 0 then x else y)
  · intro h v
    exact h (v 0) (v 1)

namespace Catalogue

/-- Among E464 models admitting left division, the division operations are
exactly the E714 models, even on infinite carriers. This does not assume or
settle that every infinite E464 model admits left division. -/
@[parastrophe_result] theorem left_characterizes464_all_rotated :
    Characterizes .all Law464 .left Law714 := by
  apply characterizes_of_division
  · intro G M _ h
    exact sideQuasigroup_of_division (left_term714 G M trivial h)
  · intro G M D _ hd h
    have hh := (@Law464.models_iff G M).mp h
    apply (@Law714.models_iff G D).mpr
    intro x y
    have he := congrArg (fun v => D.op y (D.op y (D.op (D.op y x) v)))
      (hh y (D.op y x))
    simpa only [hd.1, hd.2] using he.symm
  · intro G M D _ hd h
    have hh := (@Law714.models_iff G M).mp h
    apply (@Law464.models_iff G D).mpr
    intro x y
    have he := congrArg (fun v => D.op y (D.op x (D.op x v)))
      (hh (D.op x y) x)
    simpa only [hd.1, hd.2] using he.symm

/-- E677's finite left-division image is exactly E9321. The target law
makes every row surjective; finiteness supplies injectivity. -/
@[parastrophe_result] theorem left_characterizes677_fin_long :
    Characterizes .fin Law677 .left leftImage677 := by
  apply characterizes_of_division
  · intro G M hG h
    letI : Finite G := hG
    have hh := (leftImage677_iff M).mp h
    intro y
    have hs : Function.Surjective (M.op y) := fun x =>
      ⟨M.op (M.op x y) (M.op x (M.op x y)), (hh x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd h
    have hh := (@Law677.models_iff G M).mp h
    apply (leftImage677_iff D).mpr
    intro x y
    have he := congrArg (fun v => D.op y (D.op (D.op x y) (D.op x v)))
      (hh (D.op x y) x)
    simpa only [hd.1, hd.2] using he.symm
  · intro G M D _ hd h
    have hh := (leftImage677_iff M).mp h
    apply (@Law677.models_iff G D).mpr
    intro x y
    have he := congrArg (fun v => D.op y (D.op x (D.op (D.op y x) v)))
      (hh y (D.op y x))
    simpa only [hd.1, hd.2] using he.symm

/-- The E10200 identity forces both surjectivity and injectivity of every
row. In the injectivity proof, first cancel a collision using two instances
of the identity to recover its repeated inner parameter. -/
theorem leftImage706_leftQuasigroup {G : Type} (M : Magma G)
    (h : @satisfies _ G M leftImage706) : IsSideQuasigroup .left M := by
  have hh := (leftImage706_iff M).mp h
  have hi (x y : G) :
      y = M.op (M.op (M.op x y) (M.op (M.op x y) x)) (M.op x (M.op x y)) := by
    have he := hh y (M.op (M.op x y) (M.op (M.op x y) x))
    rw [← hh x y] at he
    exact he
  intro y
  have hs : Function.Surjective (M.op y) := fun x =>
    ⟨M.op (M.op x y) (M.op (M.op x y) x), (hh x y).symm⟩
  refine ⟨?_, hs⟩
  intro a b hab
  rw [hi y a, hi y b, hab]

/-- E706's left-division image is E10200 on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes706_all_long :
    Characterizes .all Law706 .left leftImage706 := by
  apply characterizes_of_division
  · intro G M _ h
    exact leftImage706_leftQuasigroup M h
  · intro G M D _ hd h
    have hh := (@Law706.models_iff G M).mp h
    apply (leftImage706_iff D).mpr
    intro x y
    have he := congrArg (fun v => D.op y (D.op (D.op x y) (D.op (D.op x y) v)))
      (hh x (D.op x y))
    simpa only [hd.1, hd.2] using he.symm
  · intro G M D _ hd h
    have hh := (leftImage706_iff M).mp h
    apply (@Law706.models_iff G D).mpr
    intro x y
    have he := congrArg (fun v => D.op y (D.op y (D.op (D.op x y) v)))
      (hh x (D.op x y))
    simpa only [hd.1, hd.2] using he.symm

end Catalogue
end Parastrophes
