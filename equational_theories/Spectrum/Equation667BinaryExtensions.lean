import equational_theories.Spectrum.Equation667AutomorphismTwist
import Mathlib.Tactic.ReduceModChar

/-! Binary-fiber extensions of E667 quasigroups: the exact cocycle condition,
changes of fiber origins, and normalization over an idempotent quotient. -/
namespace Spectrum.E667.BinaryExtensions

variable {Q : Type*} (q : Q → Q → Q)

def op (C : Q → Q → ZMod 2) (x y : Q × ZMod 2) : Q × ZMod 2 :=
  (q x.1 y.1, x.2 + y.2 + C x.1 y.1)

def Cocycle (C : Q → Q → ZMod 2) : Prop := ∀ i j,
  C i i + C (q i i) j + C i (q (q i i) j) + C j (q i (q (q i i) j)) = 0

/-- The original E667 law is equivalent to the quotient law and a binary
linear cocycle equation. This holds without finiteness. -/
theorem law_iff (C : Q → Q → ZMod 2) :
    @Equation667 (Q × ZMod 2) ⟨op q C⟩ ↔ @Equation667 Q ⟨q⟩ ∧ Cocycle q C := by
  constructor
  · intro h
    constructor
    · intro i j
      exact congrArg Prod.fst (h (i, 0) (j, 0))
    · intro i j
      have hh := congrArg Prod.snd (h (i, 0) (j, 0))
      change (0 : ZMod 2) = 0 + (0 + ((0 + 0 + C i i) + 0 + C (q i i) j) +
        C i (q (q i i) j)) + C j (q i (q (q i i) j)) at hh
      simpa only [zero_add, add_zero, add_assoc] using hh.symm
  · rintro ⟨hq, hC⟩ x y
    apply Prod.ext
    · exact hq x.1 y.1
    · change x.2 = y.2 + (x.2 + ((x.2 + x.2 + C x.1 x.1) + y.2 + C (q x.1 x.1) y.1) +
        C x.1 (q (q x.1 x.1) y.1)) + C y.1 (q x.1 (q (q x.1 x.1) y.1))
      have hh := hC x.1 y.1
      linear_combination (norm := skip) -hh
      ring_nf
      reduce_mod_char

/-- Every Latin operation on two points is addition with a constant. -/
theorem latin_two_form (g : ZMod 2 → ZMod 2 → ZMod 2)
    (hL : ∀ x, Function.Injective (g x))
    (hR : ∀ y, Function.Injective (fun x => g x y)) (x y : ZMod 2) :
    g x y = x + y + g 0 0 := by
  exact (by decide +kernel : ∀ g : ZMod 2 → ZMod 2 → ZMod 2,
    (∀ x, Function.Injective (g x)) → (∀ y, Function.Injective (fun x => g x y)) →
    ∀ x y, g x y = x + y + g 0 0) g hL hR x y

def generalOp (g : Q → Q → ZMod 2 → ZMod 2 → ZMod 2)
    (x y : Q × ZMod 2) : Q × ZMod 2 := (q x.1 y.1, g x.1 y.1 x.2 y.2)

/-- The affine binary form loses no finite E667 extensions with two-point
fibers. The Latin hypotheses on blocks follow from the original law. -/
theorem every_fiber_extension [Finite Q]
    (g : Q → Q → ZMod 2 → ZMod 2 → ZMod 2)
    (h : @Equation667 (Q × ZMod 2) ⟨generalOp q g⟩) :
    generalOp q g = op q (fun i j => g i j 0 0) := by
  letI : Magma (Q × ZMod 2) := ⟨generalOp q g⟩
  funext x y
  refine Prod.ext rfl ?_
  apply latin_two_form
  · intro a b c he
    have hh : (x.1, a) ◇ (y.1, b) = (x.1, a) ◇ (y.1, c) := Prod.ext rfl he
    exact congrArg Prod.snd (E667883.left_injective667 h (x.1, a) hh)
  · intro b a c he
    have hh : (x.1, a) ◇ (y.1, b) = (x.1, c) ◇ (y.1, b) := Prod.ext rfl he
    exact congrArg Prod.snd (E667883.right_injective667 h (y.1, b) hh)

def shift (h : Q → ZMod 2) (x : Q × ZMod 2) : Q × ZMod 2 := (x.1, x.2 + h x.1)

theorem shift_involutive (h : Q → ZMod 2) : Function.Involutive (shift h) := by
  intro x
  refine Prod.ext rfl ?_
  change x.2 + h x.1 + h x.1 = x.2
  ring_nf
  reduce_mod_char

/-- The change of fiber origins as an explicit equivalence. -/
def shiftEquiv (h : Q → ZMod 2) : (Q × ZMod 2) ≃ (Q × ZMod 2) where
  toFun := shift h
  invFun := shift h
  left_inv := shift_involutive h
  right_inv := shift_involutive h

def gauge (C : Q → Q → ZMod 2) (h : Q → ZMod 2) (i j : Q) : ZMod 2 :=
  C i j + h i + h j + h (q i j)

/-- Changing the origin in every fiber gives an isomorphic operation. -/
theorem shift_hom (C : Q → Q → ZMod 2) (h : Q → ZMod 2) (x y : Q × ZMod 2) :
    shift h (op q C x y) = op q (gauge q C h) (shift h x) (shift h y) := by
  refine Prod.ext rfl ?_
  change x.2 + y.2 + C x.1 y.1 + h (q x.1 y.1) =
    (x.2 + h x.1) + (y.2 + h y.1) + (C x.1 y.1 + h x.1 + h y.1 + h (q x.1 y.1))
  ring_nf
  reduce_mod_char

theorem gauge_law (C : Q → Q → ZMod 2) (h : Q → ZMod 2)
    (hC : @Equation667 (Q × ZMod 2) ⟨op q C⟩) :
    @Equation667 (Q × ZMod 2) ⟨op q (gauge q C h)⟩ := by
  intro x y
  obtain ⟨a, rfl⟩ := (shift_involutive h).surjective x
  obtain ⟨b, rfl⟩ := (shift_involutive h).surjective y
  have hh := congrArg (shift h) (hC a b)
  simpa only [shift_hom] using hh

/-- Above an idempotent quotient, moving each fiber's square to zero makes
the diagonal cocycle vanish. -/
theorem normalize_diag (hi : ∀ i, q i i = i) (C : Q → Q → ZMod 2) (i : Q) :
    gauge q C (fun i => C i i) i i = 0 := by
  simp only [gauge, hi]
  ring_nf
  reduce_mod_char

/-- With a zero diagonal cocycle over an idempotent quotient, every square
is the distinguished zero of its fiber. -/
theorem square (hi : ∀ i, q i i = i) (C : Q → Q → ZMod 2)
    (hC : ∀ i, C i i = 0) (x : Q × ZMod 2) : op q C x x = (x.1, 0) := by
  apply Prod.ext
  · exact hi x.1
  · change x.2 + x.2 + C x.1 x.1 = 0
    rw [hC]
    ring_nf
    reduce_mod_char

spectrum_assert law_iff complete
spectrum_assert every_fiber_extension complete
spectrum_assert gauge_law complete
spectrum_assert normalize_diag complete
end Spectrum.E667.BinaryExtensions
