import equational_theories.Parastrophes.Equation917ImageBasis
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar

/-!
# The stable square image need not be a submagma

This 24-element E917 left-division image is a three-element additive extension
of an eight-element idempotent image. Its operation is
`(i,u)*(j,v) = (B(i,j),u+2v+phi(i,j))`, with fibre arithmetic modulo three.
The square map is idempotent, but its eight-element image is not closed under
multiplication. Thus passing to the stable square image cannot in general
replace the orbit-quotient argument in `Equation917UnitQuotient`.

The checks below are small kernel computations, not native evaluation or an
external SAT certificate. This refutes a proposed proof shortcut; it does not
refute any proposed single-equation characterization.
-/
namespace Parastrophes.Eq917Image.StableImageCounterexample

def base : Fin 8 → Fin 8 → Fin 8 :=
  ![![0,7,1,2,3,4,5,6], ![5,1,7,4,6,2,0,3],
    ![6,4,2,1,5,7,3,0], ![7,0,5,3,2,6,1,4],
    ![1,5,0,6,4,3,7,2], ![2,3,6,0,7,5,4,1],
    ![3,2,4,7,0,1,6,5], ![4,6,3,5,1,0,2,7]]

def offset : Fin 8 → Fin 8 → ZMod 3 :=
  ![![2,2,1,0,0,2,0,1], ![1,2,1,1,2,0,1,1],
    ![2,1,1,2,0,0,1,0], ![2,0,1,2,0,0,0,0],
    ![1,1,2,2,2,0,0,1], ![1,2,1,0,2,0,1,0],
    ![2,2,0,2,1,2,1,1], ![0,2,2,2,2,1,0,0]]

abbrev Carrier := Fin 8 × ZMod 3

@[implicit_reducible] def exampleMagma : Magma Carrier :=
  ⟨fun x y => (base x.1 y.1, x.2 + 2*y.2 + offset x.1 y.1)⟩

private theorem base_diagonal : ∀ i, base i i = i := by decide

private theorem base_cross : ∀ i j, base j (base i (base i j)) = i := by decide

private theorem offset_cross : ∀ i j,
    2*offset i i + offset i j + 2*offset i (base i j) +
      offset j (base i (base i j)) = 0 := by decide

/-- The core calculation uses only idempotence of the base and arithmetic
in characteristic three; no enumeration of the fibre coordinates is needed. -/
theorem core_formula (i : Fin 8) (u : ZMod 3) :
    core exampleMagma (i,u) = (i,offset i i) := by
  apply Prod.ext
  · change base (base i (base i i)) i = i
    simp only [base_diagonal]
  · change (u + 2*(u + 2*u + offset i i) + offset i (base i i)) +
      2*u + offset (base i (base i i)) i = offset i i
    simp only [base_diagonal]
    ring_nf
    reduce_mod_char

theorem basis : Basis exampleMagma := by
  constructor
  · rintro ⟨i,u⟩
    change (i,u) = exampleMagma.op (i,u) (core exampleMagma (i,u))
    rw [core_formula]
    apply Prod.ext
    · exact (base_diagonal i).symm
    · change u = u + 2*offset i i + offset i i
      ring_nf
      reduce_mod_char
  · rintro ⟨i,u⟩ ⟨j,v⟩
    change (i,u) = exampleMagma.op (j,v)
      (exampleMagma.op (core exampleMagma (i,u)) (exampleMagma.op (i,u) (j,v)))
    rw [core_formula]
    apply Prod.ext
    · exact (base_cross i j).symm
    · change u = v + 2*(offset i i + 2*(u + 2*v + offset i j) +
        offset i (base i j)) + offset j (base i (base i j))
      calc
        u = u + 2*offset i i + offset i j + 2*offset i (base i j) +
            offset j (base i (base i j)) := by linear_combination -(offset_cross i j)
        _ = _ := by ring_nf; reduce_mod_char

theorem inImage : InImage Law917 .left exampleMagma :=
  (characterizes_fin exampleMagma).1 basis

def square (x : Carrier) := exampleMagma.op x x

theorem square_formula (i : Fin 8) (u : ZMod 3) : square (i,u) = (i,offset i i) := by
  apply Prod.ext
  · exact base_diagonal i
  · change u + 2*u + offset i i = offset i i
    ring_nf
    reduce_mod_char

/-- The square image is already stable after one iteration. -/
theorem square_idempotent : ∀ x, square (square x) = square x := by
  rintro ⟨i,u⟩
  rw [square_formula, square_formula]

theorem square_fixed_iff (x : Carrier) : square x = x ↔ x ∈ Set.range square := by
  constructor
  · intro h
    exact ⟨x, h⟩
  · rintro ⟨y, rfl⟩
    exact square_idempotent y

def a : Carrier := (0,2)
def b : Carrier := (1,2)

theorem a_fixed : square a = a := by decide
theorem b_fixed : square b = b := by decide

theorem product_not_fixed : square (exampleMagma.op a b) ≠ exampleMagma.op a b := by
  decide

/-- In particular, the square map need not be an endomorphism. -/
theorem square_not_endomorphism :
    ¬ ∀ x y, square (exampleMagma.op x y) = exampleMagma.op (square x) (square y) := by
  intro h
  have he := h a b
  rw [a_fixed, b_fixed] at he
  exact product_not_fixed he

/-- Two idempotents multiply to a point outside the stable square image. -/
theorem stable_image_not_closed :
    ¬ ∀ x ∈ Set.range square, ∀ y ∈ Set.range square,
      exampleMagma.op x y ∈ Set.range square := by
  intro hc
  exact product_not_fixed ((square_fixed_iff _).2
    (hc a ((square_fixed_iff a).1 a_fixed) b ((square_fixed_iff b).1 b_fixed)))

end Parastrophes.Eq917Image.StableImageCounterexample
