import equational_theories.Parastrophes.TranslationChains
import equational_theories.Parastrophes.Exact
import equational_theories.Definability.E63Family
import equational_theories.Superposition

/-!
# A single identity for the arbitrary-carrier left-division image of E125

E125's left-division image satisfies both E63 and its inverse identity E1692.
These can be joined into one identity: write `u = (z*x)*((z*x)*z)` and require
`x = y*(u*(u*y))`. This identity also forces bijective left translations.
Unlike E63 alone, it therefore characterizes the image on infinite carriers too.
-/
namespace Parastrophes
open Law FreeMagma

/-- E353668451589 in the canonical extended numbering (eleven operations). -/
def leftImage125 : NatMagmaLaw :=
  let u := (Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ Lf 2)
  ⟨Lf 0, Lf 1 ⋆ (u ⋆ (u ⋆ Lf 1))⟩

theorem leftImage125_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage125 ↔ ∀ x y z,
      x = M.op y (M.op (M.op (M.op z x) (M.op (M.op z x) z))
        (M.op (M.op (M.op z x) (M.op (M.op z x) z)) y)) := by
  constructor
  · intro h x y z
    exact h (fun n => if n = 0 then x else if n = 1 then y else z)
  · intro h v
    exact h (v 0) (v 1) (v 2)

namespace Eq125Image

/-- The joined inverse identity enforces the original E63 identity.
This short equational derivation uses no finiteness or choice. -/
theorem equation63 {G : Type} (M : Magma G)
    (hM : @satisfies _ G M leftImage125) : @Equation63 G M := by
  have h := (leftImage125_iff M).mp hM
  have e6 (x y z : G) :
      M.op y (M.op (M.op (M.op z x) (M.op (M.op z x) z))
        (M.op (M.op (M.op z x) (M.op (M.op z x) z)) y)) = x := (h x y z).symm
  have e8 (x y z w : G) :
      M.op (M.op (M.op w x) (M.op (M.op w x) w))
        (M.op (M.op (M.op w x) (M.op (M.op w x) w)) z) =
      M.op y (M.op (M.op x (M.op x z)) (M.op (M.op x (M.op x z)) y)) :=
    superpose e6 e6
  have e38 (x y z : G) :
      M.op z (M.op x (M.op (M.op y (M.op y z))
        (M.op (M.op y (M.op y z)) x))) = y := superpose e8 e6
  have e61 (x y z : G) :
      M.op (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) y))
        (M.op z (M.op x (M.op x z))) = y := superpose e38 e38
  -- Name the two repeated subterms in the final three substitutions.
  have e129 (x y z : G) :
      let p := M.op x (M.op y (M.op y x))
      let q := M.op y (M.op y p)
      p = M.op (M.op (M.op q (M.op q p)) p)
        (M.op z (M.op q (M.op q z))) := by
    dsimp only
    exact superpose e61 e61
  have e177 (x y z : G) :
      let p := M.op x (M.op y (M.op y x))
      let q := M.op y (M.op y p)
      p = M.op p (M.op z (M.op q (M.op q z))) := by
    dsimp only at e129 ⊢
    exact superpose e61 e129
  have e182 (x y : G) : M.op x (M.op y (M.op y x)) = y := by
    dsimp only at e177
    exact superpose e38 e177
  exact fun x y => (e182 y x).symm

/-- Surjectivity follows from the outer row, and a collision in the row
indexed by z makes the two occurrences of u coincide. -/
theorem leftQuasigroup {G : Type} (M : Magma G)
    (hM : @satisfies _ G M leftImage125) : IsSideQuasigroup .left M := by
  have h := (leftImage125_iff M).mp hM
  intro y
  constructor
  · intro a b hab
    rw [h a y y, h b y y, hab]
  · intro x
    exact ⟨_, (h x y y).symm⟩

/-- Precisely E63 together with its missing left cancellation. -/
theorem iff_equation63_leftQuasigroup {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage125 ↔
      @Equation63 G M ∧ IsSideQuasigroup .left M := by
  refine ⟨fun h => ⟨equation63 M h, leftQuasigroup M h⟩, ?_⟩
  rintro ⟨h63, hQ⟩
  have h1692 := (@E63Family.equation1692_iff_left_injective G M h63).mpr
    (fun y => (hQ y).1)
  apply (leftImage125_iff M).mpr
  intro x y z
  rw [← h1692 x z]
  exact h63 x y

/-- Rotation of E125 under actual left division gives E63. -/
theorem division125_63 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation125 G M) : @Equation63 G D := by
  intro x y
  have he := congrArg (fun v => D.op y (D.op x (D.op x v)))
    (@E63Family.equation73_of_125 G M h y x)
  simpa only [hd.2] using he.symm

/-- The reverse rotation needs the two division identities, not finiteness. -/
theorem division63_125 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation63 G M) : @Equation125 G D := by
  intro x y
  have he := congrArg (fun v => D.op y (D.op (D.op y x) v))
    (h y (D.op y x))
  simpa only [hd.1, hd.2] using he.symm

/-- The inverse operation is recovered uniformly by `y*(y*x)`. -/
theorem left_term : UniformTermWitness .all leftImage125 .left
    (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) := by
  intro G M _ h
  have h63 := equation63 M h
  have h1692 := (@E63Family.equation1692_iff_left_injective G M h63).mpr
    (fun y => (leftQuasigroup M h y).1)
  exact ⟨fun x y => (h63 y x).symm, fun x y => (h1692 y x).symm⟩

end Eq125Image

namespace Catalogue

/-- E125's exact left-division image, including on arbitrary infinite carriers. -/
@[parastrophe_result] theorem left_characterizes125_all_long :
    Characterizes .all Law125 .left leftImage125 := by
  apply characterizes_of_division
  · intro G M _ h
    exact Eq125Image.leftQuasigroup M h
  · intro G M D _ hd h
    apply (Eq125Image.iff_equation63_leftQuasigroup D).mpr
    exact ⟨Eq125Image.division125_63 M D hd ((@Law125.models_iff G M).mp h),
      sideQuasigroup_of_division (division_symm hd)⟩
  · intro G M D _ hd h
    exact (@Law125.models_iff G D).mpr
      (Eq125Image.division63_125 M D hd (Eq125Image.equation63 M h))

/-- Among E63 models admitting left division, its image is exactly E125
on arbitrary carriers. This does not give division to all infinite E63 models. -/
@[parastrophe_result] theorem left_characterizes63_all_partial :
    Characterizes .all Law63 .left Law125 := by
  apply characterizes_of_division
  · intro G M _ h
    exact sideQuasigroup_of_division (left_term125_alternate G M trivial h)
  · intro G M D _ hd h
    exact (@Law125.models_iff G D).mpr
      (Eq125Image.division63_125 M D hd ((@Law63.models_iff G M).mp h))
  · intro G M D _ hd h
    exact (@Law63.models_iff G D).mpr
      (Eq125Image.division125_63 M D hd ((@Law125.models_iff G M).mp h))

/-- The new long target has the same numbers of labelled and unlabelled
models as E125, with bijections on infinite carriers as well. -/
theorem sameFineSpectrum125_leftImage : SameFineSpectrum .all Law125 leftImage125 :=
  characterizes_sameFineSpectrum left_characterizes125_all_long
    (fun G M _ h => sideQuasigroup_of_division (left_term125_alternate G M trivial h))

end Catalogue
end Parastrophes
