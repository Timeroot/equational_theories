import equational_theories.Spectrum.Equation63.Frame
import equational_theories.Spectrum.Equation63.IdempotentSeeds
import equational_theories.Spectrum.Status

/-! An idempotent model at 339 = 13 * 2 * 13 + 1.

The thirteen lines of PG(2,3) carry Bennett's partial C3 algebra of type 2^4,
after taking left division. This gives an E63 frame of type 2^13. Inflate
it by any thirteen-point E63 algebra and fill its enlarged holes with the
idempotent algebra of order 27. Only the 26-point frame is checked by finite
computation; inflation and filling are proved in `Frame.lean`. -/
namespace Spectrum.E63.ProjectiveFrame13

/-- Lines of the projective plane over F3, in lexicographic homogeneous
coordinates with first nonzero coordinate normalized to one. -/
def line : Fin 13 → Fin 4 → Fin 13 := ![
  ![1,4,7,10], ![0,4,5,6], ![3,4,9,11], ![2,4,8,12],
  ![0,1,2,3], ![1,6,9,12], ![1,5,8,11], ![0,10,11,12],
  ![3,6,8,10], ![2,5,9,10], ![0,7,8,9], ![2,6,7,11], ![3,5,7,12]]

def joining (i j : Fin 13) : Fin 13 :=
  ((List.finRange 13).find? (fun b =>
    (List.finRange 4).any (fun a => line b a == i) &&
    (List.finRange 4).any (fun a => line b a == j))).getD 0

def slot (b i : Fin 13) : Fin 4 :=
  ((List.finRange 4).find? (fun a => line b a == i)).getD 0

/-- Left division in Bennett's partial C3 table (1989, Figure 1).
Entries within one hole (indices equal modulo four) are unused. -/
def partial8 : Fin 8 → Fin 8 → Fin 8 := ![
  ![0,6,5,2,0,3,7,1], ![2,0,7,6,3,0,4,0],
  ![1,3,0,0,7,4,0,5], ![6,2,4,0,1,0,5,0],
  ![0,7,3,5,0,2,1,6], ![7,0,0,4,6,0,3,2],
  ![3,0,0,1,5,7,0,4], ![5,4,1,0,2,6,0,0]]

def op (x y : Fin 13 × Fin 2) : Fin 13 × Fin 2 :=
  let b := joining x.1 y.1
  let u : Fin 8 := ⟨4*x.2.val+(slot b x.1).val, by omega⟩
  let v : Fin 8 := ⟨4*y.2.val+(slot b y.1).val, by omega⟩
  let z := partial8 u v
  (line b ⟨z.val % 4, Nat.mod_lt _ (by decide)⟩, ⟨z.val / 4, by omega⟩)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem certificate : ∀ x y : Fin 13 × Fin 2, x.1 ≠ y.1 →
    op y (op x (op x y)) = x ∧
    x.1 ≠ (op x y).1 ∧ y.1 ≠ (op x (op x y)).1 := by decide +kernel

def frame : Frame (Fin 13) (Fin 2) where
  op := op
  law x y h := (certificate x y h).1
  first x y h := (certificate x y h).2.1
  second x y h := (certificate x y h).2.2

/-- A family obtained by filling the thirteen enlarged holes. -/
theorem models {m : ℕ} (hq : Model (Fin (2*m+1)) true)
    (hb : Law63.HasModel m) : Model (Fin (26*m+1)) true :=
  frame.models hq hb

theorem idem339 : Model (Fin 339) true :=
  models idem27 (modular 13 3 (by decide))

spectrum_assert certificate complete
spectrum_assert models complete
spectrum_assert idem339 complete
end Spectrum.E63.ProjectiveFrame13
