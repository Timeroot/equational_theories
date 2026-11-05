import equational_theories.Parastrophes.TranslationChains
import equational_theories.Parastrophes.InverseIdentities

/-!
# E910 under left division

Its exact image is E427 together with bijective left translations. This is
not a single-equation characterization: even three-element models of E427
can fail cancellation. In the reverse direction E910 does characterize the
division image of those E427 models that admit left division.
-/
namespace Parastrophes.Eq910Image
open Law

def core {G : Type*} (D : Magma G) (x : G) := D.op x (D.op x (D.op x x))

/-- Rotating the E910 multiplication constraints eliminates multiplication
except for its square map. -/
theorem cross {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation910 G M) (x y : G) :
    D.op x (D.op y (D.op y x)) = M.op y y := by
  have he := congrArg (D.op y) (h (D.op y x) y)
  rw [hd.1, hd.2] at he
  exact (congrArg (D.op x) he).trans (hd.2 x (M.op y y))

theorem forward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation910 G M) : @Equation427 G D := by
  intro x y
  rw [cross M D hd h y x, hd.2]

theorem backward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation427 G D) : @Equation910 G M := by
  intro x y
  have he := h y (M.op y x)
  change y = D.op y (D.op (M.op y x) (D.op y (D.op y (M.op y x)))) at he
  rw [hd.2] at he
  have he' := congrArg (fun t => M.op y (M.op (M.op y x) (M.op y t))) he
  simpa only [hd.1] using he'.symm

/-- Both directions need actual division, but neither needs finiteness. -/
theorem rotation {G : Type} (M D : Magma G) (hd : IsDivision .left M D) :
    @Equation910 G M ↔ @Equation427 G D :=
  ⟨forward M D hd, backward M D hd⟩

/-- A short exact description, with the cancellation requirement explicit. -/
theorem inImage_iff {G : Type} (D : Magma G) :
    InImage Law910 .left D ↔ @Equation427 G D ∧ IsSideQuasigroup .left D := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact ⟨forward M D hd ((@Law910.models_iff G M).mp hM),
      sideQuasigroup_of_division (division_symm hd)⟩
  · rintro ⟨h, hq⟩
    classical
    let M : Magma G := ⟨fun x y => (Equiv.ofBijective (D.op x) (hq x)).symm y⟩
    have hd : IsDivision .left D M :=
      ⟨fun x y => (Equiv.ofBijective (D.op x) (hq x)).apply_symm_apply y,
       fun x y => (Equiv.ofBijective (D.op x) (hq x)).symm_apply_apply y⟩
    exact ⟨M, (@Law910.models_iff G M).mpr (backward M D (division_symm hd) h),
      division_symm hd⟩

/-- The original square is recovered without choosing an inverse term. -/
theorem core_eq {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation910 G M) (x : G) : core D x = M.op x x :=
  cross M D hd h x x

/-- The recovered square map squares to the division's own square map. -/
theorem core_core {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation910 G M) (x : G) : core D (core D x) = D.op x x := by
  rw [core_eq M D hd h, core_eq M D hd h]
  have he := congrArg (D.op x) (h x x)
  simpa only [hd.2] using he.symm

/-- In the idempotent subfamily, two divisions recover multiplication. -/
theorem recovery_of_idempotent {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation910 G M)
    (hi : ∀ y, M.op y y = y) (x y : G) :
    M.op x y = D.op y (D.op y x) := by
  have he := congrArg (M.op x) (cross M D hd h x y)
  rw [hd.1, hi] at he
  exact he.symm

/-- A tiny counterexample to dropping bijectivity, even if the two natural
core identities are added. -/
@[implicit_reducible] def bad : Magma (Fin 3) := ⟨fun x y =>
  (![![2, 2, 0], ![2, 2, 1], ![0, 0, 2]] : Fin 3 → Fin 3 → Fin 3) x y⟩

theorem bad_equation427 : @Equation427 (Fin 3) bad := by decide

theorem bad_cross : ∀ x y : Fin 3,
    bad.op x (bad.op y (bad.op y x)) = core bad y := by decide

theorem bad_core_core : ∀ x : Fin 3, core bad (core bad x) = bad.op x x := by decide

theorem bad_not_inImage : ¬ InImage Law910 .left bad := by
  intro h
  have hi := ((inImage_iff bad).mp h).2 0
  have he : (0 : Fin 3) = 1 := hi.1 (show bad.op 0 0 = bad.op 0 1 from rfl)
  contradiction

end Parastrophes.Eq910Image

namespace Parastrophes.Catalogue
open Law

/-- A partial-source characterization: all E910 models occur, but the
E427 source models are restricted to those admitting left division. -/
@[parastrophe_result] theorem left_characterizes427_all_partial :
    Characterizes .all Law427 .left Law910 := by
  apply characterizes_of_division
  · intro G M _ h
    exact sideQuasigroup_of_division (left_term910_all_inverse G M trivial h)
  · intro G M D _ hd h
    exact (@Law910.models_iff G D).mpr
      (Eq910Image.backward D M (division_symm hd) ((@Law427.models_iff G M).mp h))
  · intro G M D _ hd h
    exact (@Law427.models_iff G D).mpr
      (Eq910Image.forward M D hd ((@Law910.models_iff G M).mp h))

end Parastrophes.Catalogue
