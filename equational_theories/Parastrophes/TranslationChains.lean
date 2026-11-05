import equational_theories.Parastrophes.OneSided
import equational_theories.Parastrophes.Exact
import equational_theories.Generated.TrivialBruteforce.theorems.Apply
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.VampireProven.Proofs4
import equational_theories.Generated.VampireProven.Proofs7
import equational_theories.Generated.VampireProven.Proofs11

/-! Left division reverses a chain of left translations. The resulting exact
image statements require the relevant division, never the unrelated other side. -/
namespace Parastrophes
open Law FreeMagma

def leftWord {G : Type*} (M : Magma G) (word : List G) (x : G) : G :=
  word.foldr M.op x

private theorem leftWord_append {G : Type*} (M : Magma G) (a b : List G) (x : G) :
    leftWord M (a ++ b) x = leftWord M a (leftWord M b x) := by
  exact List.foldr_append

/-- Invert a composition by reversing its factors and inverting each factor. -/
theorem leftWord_inverse {G : Type*} {M D : Magma G} (h : IsDivision .left M D)
    (word : List G) (x : G) : leftWord D word.reverse (leftWord M word x) = x := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    rw [List.reverse_cons, leftWord_append]
    change leftWord D word.reverse (D.op a (M.op a (leftWord M word x))) = x
    rw [h.2]
    exact ih

/-- Reverse a right-nested equation under actual left division. -/
theorem leftWord_eq_iff {G : Type*} {M D : Magma G} (h : IsDivision .left M D)
    (word : List G) (x y : G) : leftWord M word x = y ↔ leftWord D word.reverse y = x := by
  constructor
  · intro he
    rw [← he]
    exact leftWord_inverse h word x
  · intro he
    have hi := leftWord_inverse (division_symm h) word.reverse y
    rw [List.reverse_reverse, he] at hi
    exact hi

/-- Exact image from two inverse semantic transfers. Only the target-side
bijectivity is needed to construct the original operation in the converse. -/
theorem characterizes_of_division {scope L K side}
    (hq : SideQuasigroupLaw scope K side)
    (hf : ∀ (G : Type) (M D : Magma G), scope.Allows G → IsDivision side M D →
      @satisfies _ G M L → @satisfies _ G D K)
    (hb : ∀ (G : Type) (M D : Magma G), scope.Allows G → IsDivision side M D →
      @satisfies _ G M K → @satisfies _ G D L) : Characterizes scope L side K := by
  intro G D hG
  constructor
  · intro hD
    classical
    have h := hq G D hG hD
    have hex : ∃ M : Magma G, IsDivision side D M := by
      cases side with
      | left =>
        refine ⟨⟨fun x y => (Equiv.ofBijective (D.op x) (h x)).symm y⟩, ?_⟩
        exact ⟨fun x y => (Equiv.ofBijective (D.op x) (h x)).apply_symm_apply y,
          fun x y => (Equiv.ofBijective (D.op x) (h x)).symm_apply_apply y⟩
      | right =>
        refine ⟨⟨fun x y => (Equiv.ofBijective (fun z => D.op z y) (h y)).symm x⟩, ?_⟩
        exact ⟨fun x y => (Equiv.ofBijective (fun z => D.op z y) (h y)).apply_symm_apply x,
          fun x y => (Equiv.ofBijective (fun z => D.op z y) (h y)).symm_apply_apply x⟩
    obtain ⟨M, hm⟩ := hex
    exact ⟨M, hb G D M hG hm hD, division_symm hm⟩
  · rintro ⟨M, hM, hm⟩
    exact hf G M D hG hm hM

namespace Catalogue

/-- E75 makes every left translation have cube equal to the identity. -/
@[parastrophe_result] theorem left_term75 :
    UniformTermWitness .all Law75 .left (Lf 0 ⋆ (Lf 0 ⋆ Lf 1)) := by
  intro G M _ h
  have hh := (@Law75.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => (hh y x).symm⟩

/-- E513 makes every left translation have fourth power equal to the identity. -/
@[parastrophe_result] theorem left_term513 :
    UniformTermWitness .all Law513 .left (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) := by
  intro G M _ h
  have hh := (@Law513.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => (hh y x).symm⟩

/-- E127 supplies inverse translations indexed by squares. The inverse has a
right inverse in the same family, so finiteness is unnecessary. -/
@[parastrophe_result] theorem left_term127 :
    UniformTermWitness .all Law127 .left ((Lf 0 ⋆ Lf 0) ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law127.models_iff G M).mp h
  have hi (x : G) : Function.Injective (M.op x) := by
    intro a b hab
    have ha := hh a (M.op x x)
    have hb := hh b (M.op x x)
    rw [ha, hb] at hab
    rw [← hh, ← hh] at hab
    exact ha.trans ((congrArg (M.op (M.op x x)) hab).trans hb.symm)
  exact ⟨fun x y => (hh y x).symm, fun x y => hi x (hh (M.op x y) x).symm⟩

/-- Reversing the left-translation chain of E65 gives exactly E65.
The finite target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes65_fin_chain :
    Characterizes .fin Law65 .left Law65 := by
  apply characterizes_of_division
  · intro G M hG hM
    letI : Finite G := hG
    have hm := (@Law65.models_iff G M).mp hM
    intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨(M.op x (M.op y x)), (hm x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd hM
    have hm := (@Law65.models_iff G M).mp hM
    apply (@Law65.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, x, y] x x).mp
      (hm x y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law65.models_iff G M).mp hM
    apply (@Law65.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, x, y] x x).mp
      (hm x y).symm).symm

/-- Reversing the left-translation chain of E68 gives exactly E68.
The target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes68_all_chain :
    Characterizes .all Law68 .left Law68 := by
  apply characterizes_of_division
  · intro G M _ hM
    have hm := (@Law68.models_iff G M).mp hM
    have h1564 : @Equation1564 G M := fun x y z w => (@Apply.Equation262_implies_Equation2059 G (opposite M) (fun x y z => hm x z y)) x w z y
    have h1552 := @SimpleRewrites.Equation1564_implies_Equation1552 G M h1564
    have h86 : @Equation86 G M := fun x y z => (@Equation2039_implies_Equation267 G (opposite M) (fun x y z => h1552 x z y)) x y z
    have hp := @SimpleRewrites.Equation86_implies_Equation75 G M h86
    exact sideQuasigroup_of_division (left_term75 G M trivial
      ((@Law75.models_iff G M).mpr hp))
  · intro G M D _ hd hM
    have hm := (@Law68.models_iff G M).mp hM
    apply (@Law68.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, x, y] x x).mp
      (hm x z y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law68.models_iff G M).mp hM
    apply (@Law68.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, x, y] x x).mp
      (hm x z y).symm).symm

/-- Reversing the left-translation chain of E75 gives exactly E75.
The target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes75_all_chain :
    Characterizes .all Law75 .left Law75 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_, left_term75⟩)
  · intro G M D _ hd hM
    have hm := (@Law75.models_iff G M).mp hM
    apply (@Law75.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, y, y] x x).mp
      (hm x y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law75.models_iff G M).mp hM
    apply (@Law75.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, y, y] x x).mp
      (hm x y).symm).symm

/-- Reversing the left-translation chain of E464 gives exactly E511.
The finite target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes464_fin_chain :
    Characterizes .fin Law464 .left Law511 := by
  apply characterizes_of_division
  · intro G M hG hM
    letI : Finite G := hG
    have hm := (@Law511.models_iff G M).mp hM
    intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨(M.op y (M.op y (M.op x y))), (hm x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd hM
    have hm := (@Law464.models_iff G M).mp hM
    apply (@Law511.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [x, y, y, y] x y).mp
      (hm y x).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law511.models_iff G M).mp hM
    apply (@Law464.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [x, x, x, y] x y).mp
      (hm y x).symm).symm

/-- Reversing the left-translation chain of E466 gives exactly E466.
The finite target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes466_fin_chain :
    Characterizes .fin Law466 .left Law466 := by
  apply characterizes_of_division
  · intro G M hG hM
    letI : Finite G := hG
    have hm := (@Law466.models_iff G M).mp hM
    intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨(M.op x (M.op x (M.op y x))), (hm x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd hM
    have hm := (@Law466.models_iff G M).mp hM
    apply (@Law466.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, x, x, y] x x).mp
      (hm x y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law466.models_iff G M).mp hM
    apply (@Law466.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, x, x, y] x x).mp
      (hm x y).symm).symm

/-- Reversing the left-translation chain of E469 gives exactly E469.
The target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes469_all_chain :
    Characterizes .all Law469 .left Law469 := by
  apply characterizes_of_division
  · intro G M _ hM
    have hm := (@Law469.models_iff G M).mp hM
    have h603 := @Equation469_implies_Equation603 G M hm
    have h549 : @Equation549 G M := fun x y z w => (@Equation3084_implies_Equation3074 G (opposite M) (fun x y z w => h603 x w z y)) x w z y
    have h506 : @Equation506 G M := fun x y z => (@SimpleRewrites.Equation3074_implies_Equation3073 G (opposite M) (fun x y z w => h549 x w z y)) x z y
    have h500 : @Equation500 G M := fun x y => (@SimpleRewrites.Equation3073_implies_Equation3053 G (opposite M) (fun x y z => h506 x z y)) x y
    have h528 : @Equation528 G M := fun x y z => (@Equation3053_implies_Equation3083 G (opposite M) (fun x y => h500 x y)) x z y
    have hp := @SimpleRewrites.Equation528_implies_Equation513 G M h528
    exact sideQuasigroup_of_division (left_term513 G M trivial
      ((@Law513.models_iff G M).mpr hp))
  · intro G M D _ hd hM
    have hm := (@Law469.models_iff G M).mp hM
    apply (@Law469.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, x, x, y] x x).mp
      (hm x z y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law469.models_iff G M).mp hM
    apply (@Law469.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, x, x, y] x x).mp
      (hm x z y).symm).symm

/-- Reversing the left-translation chain of E474 gives exactly E474.
The finite target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes474_fin_chain :
    Characterizes .fin Law474 .left Law474 := by
  apply characterizes_of_division
  · intro G M hG hM
    letI : Finite G := hG
    have hm := (@Law474.models_iff G M).mp hM
    intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨(M.op x (M.op y (M.op x y))), (hm x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd hM
    have hm := (@Law474.models_iff G M).mp hM
    apply (@Law474.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [x, y, x, y] x y).mp
      (hm y x).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law474.models_iff G M).mp hM
    apply (@Law474.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [x, y, x, y] x y).mp
      (hm y x).symm).symm

/-- Reversing the left-translation chain of E476 gives exactly E503.
The finite target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes476_fin_chain :
    Characterizes .fin Law476 .left Law503 := by
  apply characterizes_of_division
  · intro G M hG hM
    letI : Finite G := hG
    have hm := (@Law503.models_iff G M).mp hM
    intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨(M.op y (M.op x (M.op y x))), (hm x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd hM
    have hm := (@Law476.models_iff G M).mp hM
    apply (@Law503.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, x, y, y] x x).mp
      (hm x y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law503.models_iff G M).mp hM
    apply (@Law476.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, y, x, y] x x).mp
      (hm x y).symm).symm

/-- Reversing the left-translation chain of E501 gives exactly E501.
The finite target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes501_fin_chain :
    Characterizes .fin Law501 .left Law501 := by
  apply characterizes_of_division
  · intro G M hG hM
    letI : Finite G := hG
    have hm := (@Law501.models_iff G M).mp hM
    intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨(M.op y (M.op x (M.op x y))), (hm x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro G M D _ hd hM
    have hm := (@Law501.models_iff G M).mp hM
    apply (@Law501.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [x, x, y, y] x y).mp
      (hm y x).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law501.models_iff G M).mp hM
    apply (@Law501.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [x, x, y, y] x y).mp
      (hm y x).symm).symm

/-- Reversing the left-translation chain of E513 gives exactly E513.
The target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes513_all_chain :
    Characterizes .all Law513 .left Law513 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_, left_term513⟩)
  · intro G M D _ hd hM
    have hm := (@Law513.models_iff G M).mp hM
    apply (@Law513.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, y, y, y] x x).mp
      (hm x y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law513.models_iff G M).mp hM
    apply (@Law513.models_iff G D).mpr
    intro x y
    exact ((leftWord_eq_iff hd [y, y, y, y] x x).mp
      (hm x y).symm).symm

/-- Reversing the left-translation chain of E528 gives exactly E528.
The target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes528_all_chain :
    Characterizes .all Law528 .left Law528 := by
  apply characterizes_of_division
  · intro G M _ hM
    have hm := (@Law528.models_iff G M).mp hM
    have h513 : @satisfies _ G M Law513 :=
      (@Law513.models_iff G M).mpr (fun x y => hm x y y)
    exact sideQuasigroup_of_division (left_term513 G M trivial h513)
  · intro G M D _ hd hM
    have hm := (@Law528.models_iff G M).mp hM
    apply (@Law528.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, z, y, y] x x).mp
      (hm x z y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law528.models_iff G M).mp hM
    apply (@Law528.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, z, y, y] x x).mp
      (hm x z y).symm).symm

/-- Reversing the left-translation chain of E562 gives exactly E562.
The target law itself supplies the required left division. -/
@[parastrophe_result] theorem left_characterizes562_all_chain :
    Characterizes .all Law562 .left Law562 := by
  apply characterizes_of_division
  · intro G M _ hM
    have hm := (@Law562.models_iff G M).mp hM
    have h513 : @satisfies _ G M Law513 :=
      (@Law513.models_iff G M).mpr (fun x y => hm x y y)
    exact sideQuasigroup_of_division (left_term513 G M trivial h513)
  · intro G M D _ hd hM
    have hm := (@Law562.models_iff G M).mp hM
    apply (@Law562.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, y, z, y] x x).mp
      (hm x z y).symm).symm
  · intro G M D _ hd hM
    have hm := (@Law562.models_iff G M).mp hM
    apply (@Law562.models_iff G D).mpr
    intro x y z
    exact ((leftWord_eq_iff hd [z, y, z, y] x x).mp
      (hm x z y).symm).symm

end Catalogue
end Parastrophes
