import equational_theories.Spectrum.Equation667883Small.Basic
import equational_theories.Spectrum.SemisymmetricLoop

/-!
# Constant-diagonal E667 magmas

If every square is `e`, the permutation `J x = e ◇ x` is an involutive
automorphism. Twisting the output by `J` gives a semisymmetric loop.
Consequently a finite nonempty constant-diagonal E667 magma has order
congruent to one or two modulo three, and cannot have order seven.

These restrictions concern the constant-diagonal subclass, not all E667
magmas. In particular they exclude that subclass at orders twelve and fifteen.
-/

namespace Spectrum.E667

variable {Q : Type*} [Magma Q] [Finite Q]

/-- No left translation has its own row index in a genuine three-cycle. -/
theorem three_cycle_implies_idempotent (h : Equation667 Q) (x : Q)
    (hx : x ◇ (x ◇ (x ◇ x)) = x) : x ◇ x = x := by
  apply E667883.right_injective667 h x
  apply E667883.left_injective667 h x
  apply E667883.left_injective667 h x
  exact (h x x).symm.trans hx.symm

/-- If the row index lies in a two-cycle, its square is idempotent. -/
theorem two_cycle_square_idempotent (h : Equation667 Q) (x : Q)
    (hx : x ◇ (x ◇ x) = x) : (x ◇ x) ◇ (x ◇ x) = x ◇ x := by
  have hr : (x ◇ x) ◇ x = x := by
    apply E667883.left_injective667 h x
    apply E667883.left_injective667 h x
    exact (h x x).symm.trans hx.symm
  have he : (x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x) = x := by
    apply E667883.left_injective667 h x
    exact (h (x ◇ x) x).symm
  apply E667883.right_injective667 h x
  exact (E667883.left_injective667 h (x ◇ x) (he.trans hr.symm)).trans hr.symm

/-- The square fiber over an idempotent is exactly the union of the one- and
two-cycles of its left translation. -/
theorem square_fiber_iff (h : Equation667 Q) (e : Q) (he : e ◇ e = e) (x : Q) :
    x ◇ x = e ↔ e ◇ (e ◇ x) = x := by
  have hh : x ◇ (e ◇ (e ◇ x)) = e := by simpa only [he] using (h e x).symm
  constructor
  · intro hs
    exact E667883.left_injective667 h x (hh.trans hs.symm)
  · intro hs
    simpa only [hs] using hh

theorem square_fiber_invariant (h : Equation667 Q) (e : Q) (he : e ◇ e = e)
    (x : Q) (hx : x ◇ x = e) : (e ◇ x) ◇ (e ◇ x) = e := by
  apply (square_fiber_iff h e he (e ◇ x)).mpr
  exact congrArg (fun z => e ◇ z) ((square_fiber_iff h e he x).mp hx)

/-- A proper square fiber over an idempotent omits at least three points.
For an outside point `x`, the points `x`, `e◇x`, and `e◇(e◇x)` are distinct
and all remain outside the fiber. No closure-under-multiplication claim
about the fiber is required. -/
theorem square_fiber_complement_card_ge_three (h : Equation667 Q)
    (e : Q) (he : e ◇ e = e) (x : Q) (hx : x ◇ x ≠ e) :
    3 ≤ Nat.card {y : Q // y ◇ y ≠ e} := by
  classical
  let P := fun y : Q => e ◇ y
  have inj : Function.Injective P := E667883.left_injective667 h e
  have outside (y : Q) (hy : y ◇ y ≠ e) : P y ◇ P y ≠ e := by
    intro hz
    have hh : P (P (P y)) = P y := (square_fiber_iff h e he (P y)).mp hz
    exact hy ((square_fiber_iff h e he y).mpr (inj hh))
  have hxx : P (P x) ≠ x := fun hh => hx ((square_fiber_iff h e he x).mpr hh)
  have hpx : P x ≠ x := by
    intro hh
    apply hxx
    rw [hh, hh]
  let C := {y : Q // y ◇ y ≠ e}
  let a : C := ⟨x, hx⟩
  let b : C := ⟨P x, outside x hx⟩
  let c : C := ⟨P (P x), outside (P x) (outside x hx)⟩
  have hab : a ≠ b := fun hh => hpx (congrArg Subtype.val hh).symm
  have hac : a ≠ c := fun hh => hxx (congrArg Subtype.val hh).symm
  have hbc : b ≠ c := fun hh => hpx (inj (congrArg Subtype.val hh)).symm
  letI : Fintype C := Fintype.ofFinite C
  have hcard : ({a, b, c} : Finset C).card = 3 := by
    simp [hab, hac, hbc]
  have hh := Finset.card_le_univ ({a, b, c} : Finset C)
  rw [hcard] at hh
  simpa only [Nat.card_eq_fintype_card] using hh

spectrum_assert square_fiber_complement_card_ge_three complete

namespace ConstantDiagonal

variable {Q : Type*} [Magma Q] [Finite Q]
variable (h : Equation667 Q) (e : Q) (hsq : ∀ x : Q, x ◇ x = e)
include h hsq

omit [Finite Q] in
theorem law (x y : Q) : y ◇ (x ◇ (e ◇ y)) = x := by
  simpa only [hsq] using (h x y).symm

theorem involutive (x : Q) : e ◇ (e ◇ x) = x := by
  apply E667883.left_injective667 h x
  change x ◇ (e ◇ (e ◇ x)) = x ◇ x
  rw [law h e hsq, hsq]

theorem right_eq_left (x : Q) : x ◇ e = e ◇ x := by
  apply E667883.left_injective667 h e
  have hh := law h e hsq x e
  simpa only [hsq, involutive h e hsq] using hh

/-- Rotate an entry `(x,y,x◇y)` to `(x◇y,e◇x,y)`. -/
theorem rotate (x y : Q) : (x ◇ y) ◇ (e ◇ x) = y := by
  apply E667883.left_injective667 h x
  exact law h e hsq (x ◇ y) x

theorem rotate_twice (x y : Q) : y ◇ (e ◇ (x ◇ y)) = e ◇ x := by
  simpa only [rotate h e hsq] using rotate h e hsq (x ◇ y) (e ◇ x)

/-- Three rotations show that the involution preserves multiplication. -/
theorem map_op (x y : Q) : (e ◇ x) ◇ (e ◇ y) = e ◇ (x ◇ y) := by
  simpa only [rotate_twice h e hsq] using rotate h e hsq y (e ◇ (x ◇ y))

/-- The output twist is a semisymmetric loop, with the original common square
as its identity element. -/
def toLoop : SemisymmetricLoop Q where
  op x y := e ◇ (x ◇ y)
  unit := e
  square x := by rw [hsq, hsq]
  left_unit x := involutive h e hsq x
  right_unit x := by rw [right_eq_left h e hsq, involutive h e hsq]
  semi x y := by rw [rotate_twice h e hsq, involutive h e hsq]

open Law Law.MagmaLaw

/-- The whole known spectrum restriction for semisymmetric loops applies. -/
theorem orders [Fintype Q] : Fintype.card Q ∈ residues 3 {1, 2} {7} := by
  let L := toLoop h e hsq
  apply orders_887
  refine ⟨Fintype.card_pos_iff.mpr ⟨e⟩, ?_⟩
  exact hasModel_of_card L.magma
    ((@Law887.models_iff _ L.magma).mpr L.equation887) rfl

theorem card_mod_three_ne_zero [Fintype Q] : Fintype.card Q % 3 ≠ 0 := by
  let L := toLoop h e hsq
  letI : Fintype L.Points := Fintype.ofFinite _
  have hc : Fintype.card L.Points = Fintype.card Q - 1 := by
    change Fintype.card {x : Q // x ≠ L.unit} = Fintype.card Q - 1
    simp
  have hm := L.remove.card_mod_three
  rw [hc] at hm
  have hp : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨e⟩
  omega

omit hsq in
theorem not_constant_of_three_dvd [Fintype Q] (hd : 3 ∣ Fintype.card Q) :
    ¬ ∀ x : Q, x ◇ x = e := by
  intro hs
  exact card_mod_three_ne_zero h e hs (Nat.mod_eq_zero_of_dvd hd)

end ConstantDiagonal
end Spectrum.E667
