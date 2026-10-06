import equational_theories.Spectrum.Equation667AutomorphismTwist
import Mathlib.Tactic.ReduceModChar

/-! A family including nonmedial E667 magmas on F₅ × F₂.
Any function v : F₅ → F₂ gives
(i,a) * (j,b) = (3(i+j), a+b+v(i)+v(2j-i)).
Every square is (i,0), so squaring is a retraction with two-point fibers.
The original ten-point retraction counterexample belongs to this family. -/
namespace Spectrum.E667.BinaryFive

def base (i j : ZMod 5) : ZMod 5 := 3 * (i + j)
def cocycle (v : ZMod 5 → ZMod 2) (i j : ZMod 5) : ZMod 2 := v i + v (2 * j - i)
def op (v : ZMod 5 → ZMod 2) (x y : ZMod 5 × ZMod 2) : ZMod 5 × ZMod 2 :=
  (base x.1 y.1, x.2 + y.2 + cocycle v x.1 y.1)

theorem base_idem (i : ZMod 5) : base i i = i := by unfold base; ring_nf; reduce_mod_char

theorem base_law (i j : ZMod 5) : base j (base i (base i j)) = i := by
  unfold base
  ring_nf
  reduce_mod_char

theorem cocycle_diag (v : ZMod 5 → ZMod 2) (i : ZMod 5) : cocycle v i i = 0 := by
  have hi : 2 * i - i = i := by ring
  rw [cocycle, hi]
  ring_nf
  reduce_mod_char

/-- Three cocycle contributions cancel in pairs. -/
theorem cocycle_law (v : ZMod 5 → ZMod 2) (i j : ZMod 5) :
    cocycle v i j + cocycle v i (base i j) +
      cocycle v j (base i (base i j)) = 0 := by
  have h1 : 2 * base i j - i = j := by unfold base; ring_nf; reduce_mod_char
  have h2 : 2 * base i (base i j) - j = 2 * j - i := by
    unfold base
    ring_nf
    reduce_mod_char
    ring
  simp only [cocycle, h1, h2]
  ring_nf
  reduce_mod_char

theorem square (v : ZMod 5 → ZMod 2) (x : ZMod 5 × ZMod 2) : op v x x = (x.1, 0) := by
  apply Prod.ext
  · exact base_idem x.1
  · change x.2 + x.2 + cocycle v x.1 x.1 = 0
    rw [cocycle_diag]
    ring_nf
    reduce_mod_char

theorem law (v : ZMod 5 → ZMod 2) : @Equation667 (ZMod 5 × ZMod 2) ⟨op v⟩ := by
  intro x y
  change x = op v y (op v x (op v (op v x x) y))
  rw [square]
  apply Prod.ext
  · exact (base_law x.1 y.1).symm
  · change x.2 = y.2 + (x.2 + (0 + y.2 + cocycle v x.1 y.1) +
      cocycle v x.1 (base x.1 y.1)) + cocycle v y.1 (base x.1 (base x.1 y.1))
    have hc := cocycle_law v x.1 y.1
    linear_combination (norm := skip) -hc
    ring_nf
    reduce_mod_char

theorem square_retraction (v : ZMod 5 → ZMod 2) (x : ZMod 5 × ZMod 2) :
    op v (op v x x) (op v x x) = op v x x := by
  rw [square v x, square]

theorem idempotent_iff (v : ZMod 5 → ZMod 2) (x : ZMod 5 × ZMod 2) :
    op v x x = x ↔ x.2 = 0 := by
  rw [square]
  constructor
  · intro h
    exact (congrArg Prod.snd h).symm
  · intro h
    exact Prod.ext rfl h.symm

spectrum_assert law complete
spectrum_assert square_retraction complete
end Spectrum.E667.BinaryFive
