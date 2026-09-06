import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp

/-!
# The field with sixteen elements, concretely

`Definability/Hom1516.lean` refutes a cell by algebra rather than by enumeration, and the algebra
happens in `F₁₆`. Mathlib's `GaloisField 2 4` is the right object mathematically and the wrong one
here: it is noncomputable, so none of the finitely many checks the argument still needs — "no pair
`(c, g)` of nonzero elements makes these twelve values a partial injection", "the product of the
nonzero elements is one" — can be `decide`d.

So this file builds the same field on `Fin 16`. An element is the bit pattern of its coordinates in
the basis `1, t, t², t³` over `F₂`, where `t` is a root of `X⁴ + X + 1`; addition is therefore
`xor`, and multiplication goes through the discrete logarithm to base `t`, whose powers run

    1, 2, 4, 8, 3, 6, 12, 11, 5, 10, 7, 14, 15, 13, 9

before returning to `1`. Both are kernel-cheap — `Nat.xor` and `Nat.mod` are accelerated, and the
two tables are sixteen-way matches — so every axiom below is a `decide` over at most `16³ = 4096`
cases, and downstream files get `field_simp` and `ring` on a carrier that still computes.
-/

/-- The field with sixteen elements: `F₂[t]/(t⁴ + t + 1)`, an element being the bit pattern of its
coordinates in the basis `1, t, t², t³`. -/
def F16 : Type := Fin 16

namespace F16

instance : DecidableEq F16 := inferInstanceAs (DecidableEq (Fin 16))
instance : Fintype F16 := inferInstanceAs (Fintype (Fin 16))
instance : Inhabited F16 := inferInstanceAs (Inhabited (Fin 16))

/-- The discrete logarithm to base `t = 2`; the value at `0` is junk. -/
def log : Fin 16 → ℕ
  | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 3 => 4 | 6 => 5 | 12 => 6 | 11 => 7
  | 5 => 8 | 10 => 9 | 7 => 10 | 14 => 11 | 15 => 12 | 13 => 13 | 9 => 14 | _ => 0

/-- The powers of `t = 2`, indexed modulo fifteen. -/
def exp : ℕ → Fin 16
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8 | 4 => 3 | 5 => 6 | 6 => 12 | 7 => 11
  | 8 => 5 | 9 => 10 | 10 => 7 | 11 => 14 | 12 => 15 | 13 => 13 | 14 => 9 | _ => 1

instance : Zero F16 := ⟨(0 : Fin 16)⟩
instance : One F16 := ⟨(1 : Fin 16)⟩

/-- Addition is coordinatewise in `F₂`, i.e. `xor` on the bit patterns. -/
instance : Add F16 := ⟨fun x y => (⟨(Fin.val x ^^^ Fin.val y) % 16, Nat.mod_lt _ (by decide)⟩ :
  Fin 16)⟩

/-- Every element is its own additive inverse. -/
instance : Neg F16 := ⟨id⟩
instance : Sub F16 := ⟨fun x y => x + y⟩

/-- Multiplication, through the discrete logarithm. -/
instance : Mul F16 :=
  ⟨fun x y => if x = 0 ∨ y = 0 then (0 : F16) else exp ((log x + log y) % 15)⟩

/-- Inversion, through the discrete logarithm; `0⁻¹ = 0`. -/
instance : Inv F16 := ⟨fun x => if x = 0 then (0 : F16) else exp ((15 - log x) % 15)⟩
instance : Div F16 := ⟨fun x y => x * y⁻¹⟩

instance instCommRing : CommRing F16 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_comm := by decide
  npow n x := npowRec n x

instance instField : Field F16 where
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  qsmul := _

@[simp] theorem card : Fintype.card F16 = 16 := rfl

/-- The root `t` of `X⁴ + X + 1`, i.e. the bit pattern `0010`. Beware that this is *not* the
numeral `(2 : F16)`, which is `1 + 1 = 0`: in characteristic two the numerals name only `0` and
`1`, so every other element of the field has to be spelled as a power of `t`. -/
def t : F16 := (2 : Fin 16)

theorem t_ne_zero : t ≠ 0 := by decide

theorem t_sub_one_ne_zero : t - 1 ≠ 0 := by decide

/-- `t` is a primitive root: its fifteen powers exhaust the nonzero elements. -/
theorem exists_pow_t : ∀ a : F16, a ≠ 0 → ∃ n : Fin 15, t ^ (n : ℕ) = a := by decide

/-- The product of the fifteen nonzero elements is one: Wilson's theorem in characteristic two. -/
theorem prod_ne_zero : ∏ y ∈ (Finset.univ : Finset F16) \ {0}, y = 1 := by decide

/-- Deleting one further nonzero element from that product inverts it. -/
theorem prod_sdiff_pair {p : F16} (hp : p ≠ 0) :
    ∏ y ∈ (Finset.univ : Finset F16) \ {0, p}, y = p⁻¹ := by
  have hset : (Finset.univ : Finset F16) \ {0, p}
      = ((Finset.univ : Finset F16) \ {0}).erase p := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, not_or]
    tauto
  have hmem : p ∈ (Finset.univ : Finset F16) \ {0} := by simp [hp]
  have h := Finset.mul_prod_erase _ (fun y : F16 ↦ y) hmem
  rw [prod_ne_zero] at h
  rw [hset]
  field_simp
  simpa [mul_comm] using h

end F16
