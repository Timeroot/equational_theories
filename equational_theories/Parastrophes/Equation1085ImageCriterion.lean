import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-!
# A division-only criterion for E1085

For a left quasigroup D, the following implication exactly characterizes
membership in the left-division image of E1085:

    y * (x * z) = y  →  z * (y * x) = x.

This is a quasiidentity, not a single ordinary identity. In particular this
does not close the catalogue's single-equation question. Unlike a criterion
using a recovered source square, it needs no conjectural square-recovery term.
It can also be used to search directly for division tables, without carrying
a second multiplication table. The proof works on arbitrary carriers.
-/
namespace Parastrophes.Eq1085Image
open Law

def Rotation {G : Type} (D : Magma G) : Prop :=
  ∀ x y z, D.op y (D.op x z) = y → D.op z (D.op y x) = x

/-- E1085 explicitly solves each left-division equation. -/
theorem division_formula {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation1085 G M) (y x : G) :
    D.op y x = M.op (M.op x (M.op y y)) x := by
  have he := congrArg (D.op y) (h x y)
  simpa only [hd.2] using he

/-- Equal source squares give equal inverse rows. Evaluating that common
row at the common square distinguishes the two original elements. -/
theorem source_square_injective {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1085 G M) :
    Function.Injective (fun x => M.op x x) := by
  intro y z hs
  change M.op y y = M.op z z at hs
  have hr (x : G) : D.op y x = D.op z x := by
    rw [division_formula M D hd h, division_formula M D hd h, hs]
  calc
    y = D.op y (M.op y y) := (hd.2 y y).symm
    _ = D.op z (M.op z z) := by rw [hr, hs]
    _ = z := hd.2 z z

/-- Finite image searches may additionally assume the source square map
is a permutation. No fixed bound on its order is asserted. -/
theorem source_square_bijective_fin {G : Type} [Finite G] (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1085 G M) :
    Function.Bijective (fun x => M.op x x) := by
  have hi := source_square_injective M D hd h
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The hypothesis says precisely that z is the source product x*(y*y).
E1085 then rotates the two remaining divisions. -/
theorem forward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation1085 G M) : Rotation D := by
  intro x y z hz
  have hs : D.op x z = M.op y y := by
    have he := congrArg (M.op y) hz
    simpa only [hd.1] using he
  have ht : z = M.op x (M.op y y) := by
    have he := congrArg (M.op x) hs
    simpa only [hd.1] using he
  have he := congrArg (D.op y) (h x y)
  rw [hd.2] at he
  rw [he, ← ht, hd.2]

/-- Specializing the rotation at the source product x*(y*y) recovers E1085. -/
theorem backward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : Rotation D) : @Equation1085 G M := by
  intro x y
  have he := h x y (M.op x (M.op y y)) (by rw [hd.2, hd.2])
  have ht := congrArg (M.op (M.op x (M.op y y))) he
  rw [hd.1] at ht
  have hh := congrArg (M.op y) ht
  simpa only [hd.1] using hh

/-- Exact characterization with bijectivity stated explicitly. There is no
finiteness assumption and no appeal to an externally checked search. -/
theorem characterizes {G : Type} (D : Magma G) :
    InImage Law1085 .left D ↔ IsSideQuasigroup .left D ∧ Rotation D := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact ⟨sideQuasigroup_of_division (division_symm hd),
      forward M D hd ((@Law1085.models_iff G M).mp hM)⟩
  · rintro ⟨hq, hr⟩
    classical
    let e (x : G) := Equiv.ofBijective (D.op x) (hq x)
    let M : Magma G := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y, fun x y => (e x).apply_symm_apply y⟩
    exact ⟨M, (@Law1085.models_iff G M).mpr (backward M D hd hr), hd⟩

end Parastrophes.Eq1085Image
