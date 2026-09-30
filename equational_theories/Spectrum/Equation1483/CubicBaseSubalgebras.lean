import equational_theories.Spectrum.Equation1483.PermutationSubalgebra
import Mathlib.Data.Fintype.Pi

/-! Every nonempty subalgebra of the cubic Boolean eight-point base has a
constant row. Thus arbitrary finite permutation covers of this base, including
the examples with no cubic untwist, have only square or twice-square subalgebras.
The eight-point calculation is checked by the kernel, not a SAT oracle. -/
namespace Spectrum.E1483.CubicBaseSubalgebras
open PermutationCover
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def rows : Fin 8 → Nat := ![0xffffff, 0xb6dfff, 0x7df7df, 0x34d7df, 0xdbfdbf, 0x92ddbf, 0x59f59f, 0x10d59f]

/-- The cubic Boolean base in `1483_general_constructions.json`. -/
def operation (x y : Fin 8) : Fin 8 :=
  ⟨(rows x >>> (3 * y.val)) % 8, Nat.mod_lt _ (by decide)⟩

theorem lawful : ∀ x y z,
    operation (operation y x) (operation x (operation y z)) = x := by
  decide +kernel

private theorem constant_row_check : ∀ P : Fin 8 → Bool,
    (∀ x y, P x = true → P y = true → P (operation x y) = true) →
    (∃ x, P x = true) →
    ∃ zero one, P zero = true ∧ P one = true ∧
      ∀ y, P y = true → operation zero y = one := by
  decide +kernel

/-- Every nonempty closed subset of the eight-point base has a constant row. -/
theorem constant_row (T : Set (Fin 8))
    (hc : ∀ x ∈ T, ∀ y ∈ T, operation x y ∈ T) (hn : T.Nonempty) :
    ∃ zero ∈ T, ∃ one ∈ T, ∀ y ∈ T, operation zero y = one := by
  classical
  have hclosed : ∀ x y, decide (x ∈ T) = true → decide (y ∈ T) = true →
      decide (operation x y ∈ T) = true := by
    simpa only [decide_eq_true_eq] using fun x y hx hy => hc x hx y hy
  have hnonempty : ∃ x, decide (x ∈ T) = true := by
    simpa only [decide_eq_true_eq] using hn
  obtain ⟨zero, one, hz, ho, he⟩ := constant_row_check (fun x => decide (x ∈ T))
    hclosed hnonempty
  refine ⟨zero, of_decide_eq_true hz, one, of_decide_eq_true ho, ?_⟩
  intro y hy
  exact he y (by simpa only [decide_eq_true_eq] using hy)

/-- No subalgebra of any finite permutation cover of this base supplies a new
spectrum order. Permutations and fiber size are unrestricted. -/
theorem subalgebra_square_or_twice_square {K S : Type*} [Finite S]
    (a b : Fin 8 → Fin 8 → K) (p : K → S ≃ S)
    (ha : ∀ x y z, b (operation y x) (operation x (operation y z)) = a y x)
    (hb : ∀ x y z, a (operation y x) (operation x (operation y z)) = b x (operation y z))
    (H : Set (Fin 8 × S × S)) (hH : Closed operation a b p H) (hn : H.Nonempty) :
    ∃ r : ℕ, Nat.card H = r ^ 2 ∨ Nat.card H = 2 * r ^ 2 := by
  let T : Set (Fin 8) := {x | ∃ u v, (x, u, v) ∈ H}
  have hc : ∀ x ∈ T, ∀ y ∈ T, operation x y ∈ T := by
    intro x hx y hy
    obtain ⟨u, v, hx⟩ := hx
    obtain ⟨s, t, hy⟩ := hy
    exact ⟨(p (b x y)).symm v, p (a x y) s, hH _ hx _ hy⟩
  have ht : T.Nonempty := by
    obtain ⟨⟨x, u, v⟩, hx⟩ := hn
    exact ⟨x, u, v, hx⟩
  obtain ⟨zero, hz, one, ho, he⟩ := constant_row T hc ht
  exact square_or_twice_square_of_constant_base hH lawful
    (extension_lawful operation a b p lawful ha hb)
    ⟨zero, hz⟩ ⟨one, ho⟩ (fun y => he y.val y.property)

/-- info: 'Spectrum.E1483.CubicBaseSubalgebras.lawful' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms lawful
/-- info: 'Spectrum.E1483.CubicBaseSubalgebras.subalgebra_square_or_twice_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subalgebra_square_or_twice_square
end Spectrum.E1483.CubicBaseSubalgebras
