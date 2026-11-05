import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

/-! Idempotent countable completion for E1315. A partial operation contains every
 diagonal product and only finitely many other products. Filling an undefined
 product with a fresh element and its forced companions preserves the rules.
 All extension and completion proofs are checked by the kernel. The private
 clause lemmas replay a first-order proof of extension; splitting these steps
 into declarations keeps elaboration of the two longest checks bounded. -/
namespace Eq1315Idempotent

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem step_0_eq46 {G : Type*} {a : G} {b : G} (ab : a ≠ b) : a ≠ b := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ab | grind only

private theorem step_0_eq47 {G : Type*} {old : G → G → G → Prop} (diagonal : ∀ x, old x x x) : ∀ (X0 : G), (old X0 X0 X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using diagonal | grind only

private theorem step_0_eq48 {G : Type*} {a : G} {c : G} (ac : a ≠ c) : a ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ac | grind only

private theorem step_0_eq49 {G : Type*} {b : G} {c : G} (bc : b ≠ c) : b ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using bc | grind only

private theorem step_0_eq50 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (p3 : ∀ z, ¬ old a b z) : ∀ (X0 : G), ¬(old a b X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p3 | grind only

private theorem step_0_eq51 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_0_eq53 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_0_eq54 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_0_eq55 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_0_eq56 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_0_eq57 {G : Type*} {old : G → G → G → Prop} (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_0 | grind only

private theorem step_0_eq65 {G : Type*} {a : G} {sP0 : G → G → G → Prop} (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_0 | grind only

private theorem step_0_eq66 {G : Type*} {b : G} {sP0 : G → G → G → Prop} (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_1 | grind only

private theorem step_0_eq67 {G : Type*} {c : G} {sP0 : G → G → G → Prop} (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_2 | grind only

private theorem step_0_eq69 {G : Type*} {c : G} {sP1 : G → G → G → Prop} (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_0 | grind only

private theorem step_0_eq70 {G : Type*} {b : G} {sP1 : G → G → G → Prop} (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_1 | grind only

private theorem step_0_eq71 {G : Type*} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_2 | grind only

private theorem step_0_eq74 {G : Type*} {c : G} {sP2 : G → G → G → Prop} (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_0 | grind only

private theorem step_0_eq75 {G : Type*} {a : G} {sP2 : G → G → G → Prop} (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_1 | grind only

private theorem step_0_eq77 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_3 | grind only

private theorem step_0_eq79 {G : Type*} {a : G} {sP3 : G → G → G → Prop} (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_0 | grind only

private theorem step_0_eq80 {G : Type*} {c : G} {sP3 : G → G → G → Prop} (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_1 | grind only

private theorem step_0_eq81 {G : Type*} {b : G} {sP3 : G → G → G → Prop} (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_2 | grind only

private theorem step_0_eq84 {G : Type*} {c : G} {sP4 : G → G → G → Prop} (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_0 | grind only

private theorem step_0_eq85 {G : Type*} {a : G} {sP4 : G → G → G → Prop} (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_1 | grind only

private theorem step_0_eq88 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_4 | grind only

private theorem step_0_eq90 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_imp | grind only

private theorem step_0_eq91 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_0 : new sk0 sk1 sk2) : (new sk0 sk1 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_0 | grind only

private theorem step_0_eq92 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (preserve_1 : new sk0 sk1 sk3) : (new sk0 sk1 sk3) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_1 | grind only

private theorem step_0_eq93 {G : Type*} {sk2 : G} {sk3 : G} (preserve_2 : ¬ (sk2 = sk3)) : sk2 ≠ sk3 := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_2 | grind only

private theorem step_0_eq114 {G : Type*} {old : G → G → G → Prop} (eq57 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) (eq47 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1 := by
  intro X0 X1
  first | exact resolve eq57 eq47 | exact resolve eq47 eq57 | grind only

private theorem step_0_eq120 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq71 : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) ∨ b = c := by
  intro X0 X1
  first | exact resolve eq71 eq56 | exact resolve eq56 eq71 | grind only

private theorem step_0_eq122 {G : Type*} {b : G} {c : G} {sP1 : G → G → G → Prop} (eq120 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) ∨ b = c) (eq49 : b ≠ c) : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) := by
  intro X0 X1
  first | exact resolve eq120 eq49 | exact resolve eq49 eq120 | grind only

private theorem step_0_eq151 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq90 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq91 : (new sk0 sk1 sk2)) : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) := by
  first | exact resolve eq90 eq91 | exact resolve eq91 eq90 | grind only

private theorem step_0_eq152 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq90 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq92 : (new sk0 sk1 sk3)) : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) := by
  first | exact resolve eq90 eq92 | exact resolve eq92 eq90 | grind only

private theorem step_0_eq155 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq151 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 := by
  first | exact resolve eq151 eq67 | exact resolve eq67 eq151 | grind only

private theorem step_0_eq156 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq151 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 := by
  first | exact resolve eq151 eq66 | exact resolve eq66 eq151 | grind only

private theorem step_0_eq157 {G : Type*} {a : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq151 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2)) (eq65 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 := by
  first | exact resolve eq151 eq65 | exact resolve eq65 eq151 | grind only

private theorem step_0_eq158 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq157 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0) (eq79 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 := by
  first | exact resolve eq157 eq79 | exact resolve eq79 eq157 | grind only

private theorem step_0_eq159 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq152 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 := by
  first | exact resolve eq152 eq67 | exact resolve eq67 eq152 | grind only

private theorem step_0_eq160 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq152 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 := by
  first | exact resolve eq152 eq66 | exact resolve eq66 eq152 | grind only

private theorem step_0_eq161 {G : Type*} {a : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq152 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3)) (eq65 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 := by
  first | exact resolve eq152 eq65 | exact resolve eq65 eq152 | grind only

private theorem step_0_eq162 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq161 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0) (eq79 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 := by
  first | exact resolve eq161 eq79 | exact resolve eq79 eq161 | grind only

private theorem step_0_eq163 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq158 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) := by
  first | exact resolve eq158 eq77 | exact resolve eq77 eq158 | grind only

private theorem step_0_eq165 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq158 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 := by
  first | exact resolve eq158 eq75 | exact resolve eq75 eq158 | grind only

private theorem step_0_eq166 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq158 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := by
  first | exact resolve eq158 eq74 | exact resolve eq74 eq158 | grind only

private theorem step_0_eq167 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq166 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := by
  first | exact resolve eq166 eq84 | exact resolve eq84 eq166 | grind only

private theorem step_0_eq168 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq165 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 := by
  first | exact resolve eq165 eq85 | exact resolve eq85 eq165 | grind only

private theorem step_0_eq170 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq163 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) := by
  first | exact resolve eq163 eq88 | exact resolve eq88 eq163 | grind only

private theorem step_0_eq176 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq167 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 := by
  first | exact resolve eq167 eq70 | exact resolve eq70 eq167 | grind only

private theorem step_0_eq177 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq167 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq167 eq69 | exact resolve eq69 eq167 | grind only

private theorem step_0_eq200 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq177 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) (eq57 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = X0 := by
  intro X0
  first | exact resolve eq177 eq57 | exact resolve eq57 eq177 | grind only

private theorem step_0_eq214 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq168 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 ∨ c = sk1 := by
  first | exact resolve eq168 eq69 | exact resolve eq69 eq168 | grind only

private theorem step_0_eq313 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq162 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) := by
  first | exact resolve eq162 eq77 | exact resolve eq77 eq162 | grind only

private theorem step_0_eq315 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq162 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 := by
  first | exact resolve eq162 eq75 | exact resolve eq75 eq162 | grind only

private theorem step_0_eq316 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq162 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 := by
  first | exact resolve eq162 eq74 | exact resolve eq74 eq162 | grind only

private theorem step_0_eq317 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq316 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 := by
  first | exact resolve eq316 eq84 | exact resolve eq84 eq316 | grind only

private theorem step_0_eq318 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq315 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 := by
  first | exact resolve eq315 eq85 | exact resolve eq85 eq315 | grind only

private theorem step_0_eq320 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq313 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) := by
  first | exact resolve eq313 eq88 | exact resolve eq88 eq313 | grind only

private theorem step_0_eq324 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq317 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
  first | exact resolve eq317 eq70 | exact resolve eq70 eq317 | grind only

private theorem step_0_eq325 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq317 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq317 eq69 | exact resolve eq69 eq317 | grind only

private theorem step_0_eq328 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq155 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq155 eq80 | exact resolve eq80 eq155 | grind only

private theorem step_0_eq330 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq328 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq328 eq69 | exact resolve eq69 eq328 | grind only

private theorem step_0_eq342 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq156 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
  first | exact resolve eq156 eq81 | exact resolve eq81 eq156 | grind only

private theorem step_0_eq343 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq156 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq156 eq80 | exact resolve eq80 eq156 | grind only

private theorem step_0_eq345 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq343 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq343 eq69 | exact resolve eq69 eq343 | grind only

private theorem step_0_eq346 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq342 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
  first | exact resolve eq342 eq70 | exact resolve eq70 eq342 | grind only

private theorem step_0_eq358 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq159 : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq159 eq80 | exact resolve eq80 eq159 | grind only

private theorem step_0_eq360 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq358 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq358 eq69 | exact resolve eq69 eq358 | grind only

private theorem step_0_eq366 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq318 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 ∨ c = sk1 := by
  first | exact resolve eq318 eq69 | exact resolve eq69 eq318 | grind only

private theorem step_0_eq368 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq160 : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
  first | exact resolve eq160 eq81 | exact resolve eq81 eq160 | grind only

private theorem step_0_eq369 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq160 : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq160 eq80 | exact resolve eq80 eq160 | grind only

private theorem step_0_eq371 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq369 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq369 eq69 | exact resolve eq69 eq369 | grind only

private theorem step_0_eq372 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq368 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
  first | exact resolve eq368 eq70 | exact resolve eq70 eq368 | grind only

private theorem step_0_eq457 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq170 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a)) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk2 := by
  first | exact resolve eq170 eq70 | exact resolve eq70 eq170 | grind only

private theorem step_0_eq476 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq457 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk2) (eq57 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = X0 := by
  intro X0
  first | exact resolve eq457 eq57 | exact resolve eq57 eq457 | grind only

private theorem step_0_eq568 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq320 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a)) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk3 := by
  first | exact resolve eq320 eq70 | exact resolve eq70 eq320 | grind only

private theorem step_0_eq754 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq330 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq330 eq74 | exact resolve eq74 eq330 | grind only

private theorem step_0_eq757 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq754 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq754 eq84 | exact resolve eq84 eq754 | grind only

private theorem step_0_eq762 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq757 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) (eq57 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = X0 := by
  intro X0
  first | exact resolve eq757 eq57 | exact resolve eq57 eq757 | grind only

private theorem step_0_eq797 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq345 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq345 eq74 | exact resolve eq74 eq345 | grind only

private theorem step_0_eq800 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq797 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq797 eq84 | exact resolve eq84 eq797 | grind only

private theorem step_0_eq818 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq346 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := by
  first | exact resolve eq346 eq74 | exact resolve eq74 eq346 | grind only

private theorem step_0_eq819 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq818 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := by
  first | exact resolve eq818 eq84 | exact resolve eq84 eq818 | grind only

private theorem step_0_eq837 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq360 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq360 eq74 | exact resolve eq74 eq360 | grind only

private theorem step_0_eq839 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq837 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq837 eq84 | exact resolve eq84 eq837 | grind only

private theorem step_0_eq879 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq371 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq371 eq74 | exact resolve eq74 eq371 | grind only

private theorem step_0_eq881 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq879 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq879 eq84 | exact resolve eq84 eq879 | grind only

private theorem step_0_eq896 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq372 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := by
  first | exact resolve eq372 eq77 | exact resolve eq77 eq372 | grind only

private theorem step_0_eq899 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq372 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 := by
  first | exact resolve eq372 eq74 | exact resolve eq74 eq372 | grind only

private theorem step_0_eq900 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq899 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 := by
  first | exact resolve eq899 eq84 | exact resolve eq84 eq899 | grind only

private theorem step_0_eq903 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq896 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := by
  first | exact resolve eq896 eq88 | exact resolve eq88 eq896 | grind only

private theorem step_0_eq1466 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq200 : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = X0) (eq325 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) : c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq200 eq325 | exact resolve eq325 eq200 | grind only

private theorem step_0_eq1497 {G : Type*} {a : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1466 : c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) : c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = sk3 := by
  first | exact resolve eq1466 rfl | grind only

private theorem step_0_eq1529 {G : Type*} {a : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1497 : c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = sk3) (eq93 : sk2 ≠ sk3) : c = sk1 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq1497 eq93 | exact resolve eq93 eq1497 | grind only

private theorem step_0_eq1556 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq176 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2) (eq1529 : c = sk1 ∨ c = sk0 ∨ a = sk0) : (old sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 := by
  first | exact superpose eq176 eq1529 | exact superpose eq1529 eq176 | grind only

private theorem step_0_eq1565 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq324 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3) (eq1529 : c = sk1 ∨ c = sk0 ∨ a = sk0) : (old sk0 c sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 ∨ c = sk0 ∨ a = sk0 := by
  first | exact superpose eq324 eq1529 | exact superpose eq1529 eq324 | grind only

private theorem step_0_eq1624 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq1565 : (old sk0 c sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 ∨ c = sk0 ∨ a = sk0) : (old sk0 c sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
  first | exact resolve eq1565 rfl | grind only

private theorem step_0_eq1633 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq1556 : (old sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0) : (old sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 := by
  first | exact resolve eq1556 rfl | grind only

private theorem step_0_eq1683 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq1624 : (old sk0 c sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = sk3 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq1624 eq54 | exact resolve eq54 eq1624 | grind only

private theorem step_0_eq1691 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq1633 : (old sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = sk2 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq1633 eq54 | exact resolve eq54 eq1633 | grind only

private theorem step_0_eq1735 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq93 : sk2 ≠ sk3) (eq1683 : b = sk3 ∨ c = sk0 ∨ a = sk0) : b ≠ sk2 ∨ c = sk0 ∨ a = sk0 := by
  first | exact superpose eq93 eq1683 | exact superpose eq1683 eq93 | grind only

private theorem step_0_eq1778 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq1735 : b ≠ sk2 ∨ c = sk0 ∨ a = sk0) (eq1691 : b = sk2 ∨ c = sk0 ∨ a = sk0) : a = sk0 ∨ c = sk0 := by
  first | exact resolve eq1735 eq1691 | exact resolve eq1691 eq1735 | grind only

private theorem step_0_eq1811 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq757 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) (eq1778 : a = sk0 ∨ c = sk0) : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = c ∨ c = sk0 := by
  first | exact superpose eq757 eq1778 | exact superpose eq1778 eq757 | grind only

private theorem step_0_eq1817 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq800 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq1778 : a = sk0 ∨ c = sk0) : (old a sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk0 := by
  first | exact superpose eq800 eq1778 | exact superpose eq1778 eq800 | grind only

private theorem step_0_eq1823 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq839 : (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0) (eq1778 : a = sk0 ∨ c = sk0) : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk0 := by
  first | exact superpose eq839 eq1778 | exact superpose eq1778 eq839 | grind only

private theorem step_0_eq1863 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1823 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk0) (eq48 : a ≠ c) : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq1823 eq48 | exact resolve eq48 eq1823 | grind only

private theorem step_0_eq1865 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1817 : (old a sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk0) (eq48 : a ≠ c) : (old a sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq1817 eq48 | exact resolve eq48 eq1817 | grind only

private theorem step_0_eq1867 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1811 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = c ∨ c = sk0) (eq48 : a ≠ c) : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq1811 eq48 | exact resolve eq48 eq1811 | grind only

private theorem step_0_eq4747 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq762 : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = X0) (eq881 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq762 eq881 | exact resolve eq881 eq762 | grind only

private theorem step_0_eq4759 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq4747 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 := by
  first | exact resolve eq4747 rfl | grind only

private theorem step_0_eq4787 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq4759 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1) (eq93 : sk2 ≠ sk3) : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq4759 eq93 | exact resolve eq93 eq4759 | grind only

private theorem step_0_eq4835 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1865 : (old a sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq4787 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1) : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 := by
  first | exact superpose eq1865 eq4787 | exact superpose eq4787 eq1865 | grind only

private theorem step_0_eq4838 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq4835 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1) : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq4835 rfl | grind only

private theorem step_0_eq4873 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq4838 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq51 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq4838 eq51 | exact resolve eq51 eq4838 | grind only

private theorem step_0_eq5005 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq819 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0) (eq4873 : c = sk1 ∨ b = sk1 ∨ c = sk0) : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq819 eq4873 | exact superpose eq4873 eq819 | grind only

private theorem step_0_eq5013 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq900 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ c = sk0) (eq4873 : c = sk1 ∨ b = sk1 ∨ c = sk0) : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq900 eq4873 | exact superpose eq4873 eq900 | grind only

private theorem step_0_eq5066 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq5013 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0) : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq5013 rfl | grind only

private theorem step_0_eq5068 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5005 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0) : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq5005 rfl | grind only

private theorem step_0_eq5108 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq5066 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq5066 eq54 | exact resolve eq54 eq5066 | grind only

private theorem step_0_eq5116 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5068 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq5068 eq54 | exact resolve eq54 eq5068 | grind only

private theorem step_0_eq5148 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk3 : G} (eq5108 : b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1) (eq49 : b ≠ c) : b = sk3 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq5108 eq49 | exact resolve eq49 eq5108 | grind only

private theorem step_0_eq5152 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq5116 : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1) (eq49 : b ≠ c) : b = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq5116 eq49 | exact resolve eq49 eq5116 | grind only

private theorem step_0_eq5255 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq93 : sk2 ≠ sk3) (eq5148 : b = sk3 ∨ c = sk0 ∨ b = sk1) : b ≠ sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq93 eq5148 | exact superpose eq5148 eq93 | grind only

private theorem step_0_eq5346 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq5255 : b ≠ sk2 ∨ c = sk0 ∨ b = sk1) (eq5152 : b = sk2 ∨ c = sk0 ∨ b = sk1) : b = sk1 ∨ c = sk0 := by
  first | exact resolve eq5255 eq5152 | exact resolve eq5152 eq5255 | grind only

private theorem step_0_eq5505 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1863 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0) (eq5346 : b = sk1 ∨ c = sk0) : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk0 := by
  first | exact superpose eq1863 eq5346 | exact superpose eq5346 eq1863 | grind only

private theorem step_0_eq5507 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1867 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) (eq5346 : b = sk1 ∨ c = sk0) : (old a b sk2) ∨ c = sk2 ∨ b = c ∨ c = sk0 ∨ c = sk0 := by
  first | exact superpose eq1867 eq5346 | exact superpose eq5346 eq1867 | grind only

private theorem step_0_eq5515 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq5507 : (old a b sk2) ∨ c = sk2 ∨ b = c ∨ c = sk0 ∨ c = sk0) : (old a b sk2) ∨ c = sk2 ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq5507 rfl | grind only

private theorem step_0_eq5517 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq5505 : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk0) : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq5505 rfl | grind only

private theorem step_0_eq5551 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq5515 : (old a b sk2) ∨ c = sk2 ∨ b = c ∨ c = sk0) (eq50 : ∀ (X0 : G), ¬(old a b X0)) : c = sk2 ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq5515 eq50 | exact resolve eq50 eq5515 | grind only

private theorem step_0_eq5553 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq5517 : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk0) (eq50 : ∀ (X0 : G), ¬(old a b X0)) : c = sk3 ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq5517 eq50 | exact resolve eq50 eq5517 | grind only

private theorem step_0_eq5569 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq5551 : c = sk2 ∨ b = c ∨ c = sk0) (eq49 : b ≠ c) : c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5551 eq49 | exact resolve eq49 eq5551 | grind only

private theorem step_0_eq5570 {G : Type*} {b : G} {c : G} {sk0 : G} {sk3 : G} (eq5553 : c = sk3 ∨ b = c ∨ c = sk0) (eq49 : b ≠ c) : c = sk3 ∨ c = sk0 := by
  first | exact resolve eq5553 eq49 | exact resolve eq49 eq5553 | grind only

private theorem step_0_eq5796 {G : Type*} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq93 : sk2 ≠ sk3) (eq5570 : c = sk3 ∨ c = sk0) : c ≠ sk2 ∨ c = sk0 := by
  first | exact superpose eq93 eq5570 | exact superpose eq5570 eq93 | grind only

private theorem step_0_eq5874 {G : Type*} {c : G} {sk0 : G} {sk2 : G} (eq5796 : c ≠ sk2 ∨ c = sk0) (eq5569 : c = sk2 ∨ c = sk0) : c = sk0 := by
  first | exact resolve eq5796 eq5569 | exact resolve eq5569 eq5796 | grind only

private theorem step_0_eq5955 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq168 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2) (eq5874 : c = sk0) : (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = sk2 := by
  first | exact superpose eq168 eq5874 | exact superpose eq5874 eq168 | grind only

private theorem step_0_eq5961 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq214 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 ∨ c = sk1) (eq5874 : c = sk0) : (old c sk1 sk2) ∨ a = c ∨ a = sk2 ∨ c = sk1 := by
  first | exact superpose eq214 eq5874 | exact superpose eq5874 eq214 | grind only

private theorem step_0_eq5968 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq318 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3) (eq5874 : c = sk0) : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = c ∨ a = sk3 := by
  first | exact superpose eq318 eq5874 | exact superpose eq5874 eq318 | grind only

private theorem step_0_eq5984 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq366 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 ∨ c = sk1) (eq5874 : c = sk0) : (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ c = sk1 := by
  first | exact superpose eq366 eq5874 | exact superpose eq5874 eq366 | grind only

private theorem step_0_eq6100 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq5984 : (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ c = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ a = sk3 ∨ c = sk1 := by
  first | exact resolve eq5984 eq56 | exact resolve eq56 eq5984 | grind only

private theorem step_0_eq6115 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq5968 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = c ∨ a = sk3) (eq122 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1)) : (old c sk1 sk3) ∨ a = c ∨ a = sk3 := by
  first | exact resolve eq5968 eq122 | exact resolve eq122 eq5968 | grind only

private theorem step_0_eq6121 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq5961 : (old c sk1 sk2) ∨ a = c ∨ a = sk2 ∨ c = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ a = sk2 ∨ c = sk1 := by
  first | exact resolve eq5961 eq56 | exact resolve eq56 eq5961 | grind only

private theorem step_0_eq6127 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq5955 : (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = sk2) (eq122 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1)) : (old c sk1 sk2) ∨ a = c ∨ a = sk2 := by
  first | exact resolve eq5955 eq122 | exact resolve eq122 eq5955 | grind only

private theorem step_0_eq6144 {G : Type*} {a : G} {c : G} {sk1 : G} {sk3 : G} (eq6100 : a = c ∨ a = sk3 ∨ c = sk1) (eq48 : a ≠ c) : a = sk3 ∨ c = sk1 := by
  first | exact resolve eq6100 eq48 | exact resolve eq48 eq6100 | grind only

private theorem step_0_eq6149 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq6115 : (old c sk1 sk3) ∨ a = c ∨ a = sk3) (eq48 : a ≠ c) : (old c sk1 sk3) ∨ a = sk3 := by
  first | exact resolve eq6115 eq48 | exact resolve eq48 eq6115 | grind only

private theorem step_0_eq6150 {G : Type*} {a : G} {c : G} {sk1 : G} {sk2 : G} (eq6121 : a = c ∨ a = sk2 ∨ c = sk1) (eq48 : a ≠ c) : a = sk2 ∨ c = sk1 := by
  first | exact resolve eq6121 eq48 | exact resolve eq48 eq6121 | grind only

private theorem step_0_eq6153 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq6127 : (old c sk1 sk2) ∨ a = c ∨ a = sk2) (eq48 : a ≠ c) : (old c sk1 sk2) ∨ a = sk2 := by
  first | exact resolve eq6127 eq48 | exact resolve eq48 eq6127 | grind only

private theorem step_0_eq6400 {G : Type*} {a : G} {c : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq93 : sk2 ≠ sk3) (eq6144 : a = sk3 ∨ c = sk1) : a ≠ sk2 ∨ c = sk1 := by
  first | exact superpose eq93 eq6144 | exact superpose eq6144 eq93 | grind only

private theorem step_0_eq6481 {G : Type*} {a : G} {c : G} {sk1 : G} {sk2 : G} (eq6400 : a ≠ sk2 ∨ c = sk1) (eq6150 : a = sk2 ∨ c = sk1) : c = sk1 := by
  first | exact resolve eq6400 eq6150 | exact resolve eq6150 eq6400 | grind only

private theorem step_0_eq6623 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq903 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a)) (eq6481 : c = sk1) : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ (old b c a) := by
  first | exact superpose eq903 eq6481 | exact superpose eq6481 eq903 | grind only

private theorem step_0_eq6676 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq6623 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ (old b c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk0 c sk3) ∨ b = c ∨ b = sk3 := by
  first | exact resolve eq6623 eq54 | exact resolve eq54 eq6623 | grind only

private theorem step_0_eq6733 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq6676 : (old sk0 c sk3) ∨ b = c ∨ b = sk3) (eq49 : b ≠ c) : (old sk0 c sk3) ∨ b = sk3 := by
  first | exact resolve eq6676 eq49 | exact resolve eq49 eq6676 | grind only

private theorem step_0_eq6781 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq6733 : (old sk0 c sk3) ∨ b = sk3) (eq5874 : c = sk0) : (old c c sk3) ∨ b = sk3 := by
  first | simpa only [eq5874, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq6733 | grind only

private theorem step_0_eq7520 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq6149 : (old c sk1 sk3) ∨ a = sk3) (eq55 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk3 ∨ c = sk3 := by
  first | exact resolve eq6149 eq55 | exact resolve eq55 eq6149 | grind only

private theorem step_0_eq7793 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq6153 : (old c sk1 sk2) ∨ a = sk2) (eq55 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk2 ∨ c = sk2 := by
  first | exact resolve eq6153 eq55 | exact resolve eq55 eq6153 | grind only

private theorem step_0_eq8332 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk3 : G} (eq6781 : (old c c sk3) ∨ b = sk3) (eq114 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : c = sk3 ∨ b = sk3 := by
  first | exact resolve eq6781 eq114 | exact resolve eq114 eq6781 | grind only

private theorem step_0_eq8407 {G : Type*} {a : G} {b : G} {c : G} {sk3 : G} (eq8332 : c = sk3 ∨ b = sk3) (eq7520 : a = sk3 ∨ c = sk3) : a = c ∨ a = b ∨ c = sk3 := by
  first | exact superpose eq8332 eq7520 | exact superpose eq7520 eq8332 | grind only

private theorem step_0_eq8488 {G : Type*} {a : G} {b : G} {c : G} {sk3 : G} (eq8407 : a = c ∨ a = b ∨ c = sk3) (eq48 : a ≠ c) : a = b ∨ c = sk3 := by
  first | exact resolve eq8407 eq48 | exact resolve eq48 eq8407 | grind only

private theorem step_0_eq8509 {G : Type*} {a : G} {b : G} {c : G} {sk3 : G} (eq8488 : a = b ∨ c = sk3) (eq46 : a ≠ b) : c = sk3 := by
  first | exact resolve eq8488 eq46 | exact resolve eq46 eq8488 | grind only

private theorem step_0_eq8877 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq476 : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = X0) (eq568 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk3) : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk3 := by
  first | exact resolve eq476 eq568 | exact resolve eq568 eq476 | grind only

private theorem step_0_eq8904 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq8877 : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk3) : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = sk3 ∨ b = sk3 := by
  first | exact resolve eq8877 rfl | grind only

private theorem step_0_eq8927 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq8904 : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = sk3 ∨ b = sk3) (eq93 : sk2 ≠ sk3) : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ b = sk3 := by
  first | exact resolve eq8904 eq93 | exact resolve eq93 eq8904 | grind only

private theorem step_0_eq8931 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq8927 : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ b = sk3) (eq6481 : c = sk1) : (old b c a) ∨ b = sk2 ∨ a = sk0 ∨ b = sk3 := by
  first | simpa only [eq6481, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq8927 | grind only

private theorem step_0_eq8935 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq8931 : (old b c a) ∨ b = sk2 ∨ a = sk0 ∨ b = sk3) (eq5874 : c = sk0) : a = c ∨ (old b c a) ∨ b = sk2 ∨ b = sk3 := by
  first | simpa only [eq5874, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq8931 | grind only

private theorem step_0_eq8938 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq8935 : a = c ∨ (old b c a) ∨ b = sk2 ∨ b = sk3) (eq48 : a ≠ c) : (old b c a) ∨ b = sk2 ∨ b = sk3 := by
  first | exact resolve eq8935 eq48 | exact resolve eq48 eq8935 | grind only

private theorem step_0_eq8940 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq8938 : (old b c a) ∨ b = sk2 ∨ b = sk3) (eq8509 : c = sk3) : b = c ∨ (old b c a) ∨ b = sk2 := by
  first | simpa only [eq8509, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq8938 | grind only

private theorem step_0_eq8942 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq8940 : b = c ∨ (old b c a) ∨ b = sk2) (eq49 : b ≠ c) : (old b c a) ∨ b = sk2 := by
  first | exact resolve eq8940 eq49 | exact resolve eq49 eq8940 | grind only

private theorem step_0_eq9179 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq8942 : (old b c a) ∨ b = sk2) (eq53 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk2 ∨ a = c := by
  first | exact resolve eq8942 eq53 | exact resolve eq53 eq8942 | grind only

private theorem step_0_eq9190 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq9179 : b = sk2 ∨ a = c) (eq48 : a ≠ c) : b = sk2 := by
  first | exact resolve eq9179 eq48 | exact resolve eq48 eq9179 | grind only

private theorem step_0_eq9284 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq7793 : a = sk2 ∨ c = sk2) (eq9190 : b = sk2) : a = b ∨ b = c := by
  first | exact superpose eq7793 eq9190 | exact superpose eq9190 eq7793 | grind only

private theorem step_0_eq9289 {G : Type*} {a : G} {b : G} {c : G} (eq9284 : a = b ∨ b = c) (eq46 : a ≠ b) : b = c := by
  first | exact resolve eq9284 eq46 | exact resolve eq46 eq9284 | grind only

set_option maxHeartbeats 2000000 in
private theorem preserve_0 (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (ab : a ≠ b) (diagonal : ∀ x, old x x x) (ac : a ≠ c) (bc : b ≠ c) (p3 : ∀ z, ¬ old a b z) (p4XY : ∀ x y, old x y c → x = c ∧ y = c) (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq46 : a ≠ b := step_0_eq46 ab
  have eq47 (X0 : G) : (old X0 X0 X0) := step_0_eq47 diagonal X0
  have eq48 : a ≠ c := step_0_eq48 ac
  have eq49 : b ≠ c := step_0_eq49 bc
  have eq50 (X0 : G) : ¬(old a b X0) := step_0_eq50 p3 X0
  have eq51 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X1 := step_0_eq51 p4XY X0 X1
  have eq53 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X1 := step_0_eq53 p4XZ X0 X1
  have eq54 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X0 := step_0_eq54 p4XZ X0 X1
  have eq55 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X1 := step_0_eq55 p4YZ X0 X1
  have eq56 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X0 := step_0_eq56 p4YZ X0 X1
  have eq57 (X0 X1 X2 X3 : G) : ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := step_0_eq57 old_0 X0 X1 X2 X3
  have eq65 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ a = X0 := step_0_eq65 rule_def_0_0 X0 X1 X2
  have eq66 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ b = X1 := step_0_eq66 rule_def_0_1 X0 X1 X2
  have eq67 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ c = X2 := step_0_eq67 rule_def_0_2 X0 X1 X2
  have eq69 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ c = X1 := step_0_eq69 rule_def_1_0 X0 X1 X2
  have eq70 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ b = X2 := step_0_eq70 rule_def_1_1 X0 X1 X2
  have eq71 (X0 X1 X2 : G) : (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := step_0_eq71 rule_def_1_2 X0 X1 X2
  have eq74 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ c = X0 := step_0_eq74 rule_def_2_0 X0 X1 X2
  have eq75 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = X2 := step_0_eq75 rule_def_2_1 X0 X1 X2
  have eq77 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := step_0_eq77 rule_def_2_3 X0 X1 X2
  have eq79 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = X0 := step_0_eq79 rule_def_3_0 X0 X1 X2
  have eq80 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ c = X1 := step_0_eq80 rule_def_3_1 X0 X1 X2
  have eq81 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ b = X2 := step_0_eq81 rule_def_3_2 X0 X1 X2
  have eq84 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ c = X0 := step_0_eq84 rule_def_4_0 X0 X1 X2
  have eq85 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = X2 := step_0_eq85 rule_def_4_1 X0 X1 X2
  have eq88 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := step_0_eq88 rule_def_4_4 X0 X1 X2
  have eq90 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := step_0_eq90 new_imp X0 X1 X2
  have eq91 : (new sk0 sk1 sk2) := step_0_eq91 preserve_0
  have eq92 : (new sk0 sk1 sk3) := step_0_eq92 preserve_1
  have eq93 : sk2 ≠ sk3 := step_0_eq93 preserve_2
  have eq114 (X0 X1 : G) : ¬(old X0 X0 X1) ∨ X0 = X1 := step_0_eq114 eq57 eq47 X0 X1
  have eq120 (X0 X1 : G) : ¬(sP1 c X0 X1) ∨ b = c := step_0_eq120 eq71 eq56 X0 X1
  have eq122 (X0 X1 : G) : ¬(sP1 c X0 X1) := step_0_eq122 eq120 eq49 X0 X1
  have eq151 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) := step_0_eq151 eq90 eq91
  have eq152 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) := step_0_eq152 eq90 eq92
  have eq155 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 := step_0_eq155 eq151 eq67
  have eq156 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 := step_0_eq156 eq151 eq66
  have eq157 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 := step_0_eq157 eq151 eq65
  have eq158 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 := step_0_eq158 eq157 eq79
  have eq159 : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 := step_0_eq159 eq152 eq67
  have eq160 : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 := step_0_eq160 eq152 eq66
  have eq161 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 := step_0_eq161 eq152 eq65
  have eq162 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 := step_0_eq162 eq161 eq79
  have eq163 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) := step_0_eq163 eq158 eq77
  have eq165 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 := step_0_eq165 eq158 eq75
  have eq166 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := step_0_eq166 eq158 eq74
  have eq167 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := step_0_eq167 eq166 eq84
  have eq168 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 := step_0_eq168 eq165 eq85
  have eq170 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) := step_0_eq170 eq163 eq88
  have eq176 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 := step_0_eq176 eq167 eq70
  have eq177 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := step_0_eq177 eq167 eq69
  have eq200 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = X0 := step_0_eq200 eq177 eq57 X0
  have eq214 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 ∨ c = sk1 := step_0_eq214 eq168 eq69
  have eq313 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) := step_0_eq313 eq162 eq77
  have eq315 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 := step_0_eq315 eq162 eq75
  have eq316 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 := step_0_eq316 eq162 eq74
  have eq317 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 := step_0_eq317 eq316 eq84
  have eq318 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 := step_0_eq318 eq315 eq85
  have eq320 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) := step_0_eq320 eq313 eq88
  have eq324 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := step_0_eq324 eq317 eq70
  have eq325 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := step_0_eq325 eq317 eq69
  have eq328 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := step_0_eq328 eq155 eq80
  have eq330 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := step_0_eq330 eq328 eq69
  have eq342 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := step_0_eq342 eq156 eq81
  have eq343 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := step_0_eq343 eq156 eq80
  have eq345 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := step_0_eq345 eq343 eq69
  have eq346 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := step_0_eq346 eq342 eq70
  have eq358 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := step_0_eq358 eq159 eq80
  have eq360 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := step_0_eq360 eq358 eq69
  have eq366 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = sk3 ∨ c = sk1 := step_0_eq366 eq318 eq69
  have eq368 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := step_0_eq368 eq160 eq81
  have eq369 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := step_0_eq369 eq160 eq80
  have eq371 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := step_0_eq371 eq369 eq69
  have eq372 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := step_0_eq372 eq368 eq70
  have eq457 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk2 := step_0_eq457 eq170 eq70
  have eq476 (X0 : G) : ¬(old sk0 sk1 X0) ∨ (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = X0 := step_0_eq476 eq457 eq57 X0
  have eq568 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk3 := step_0_eq568 eq320 eq70
  have eq754 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_0_eq754 eq330 eq74
  have eq757 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_0_eq757 eq754 eq84
  have eq762 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = X0 := step_0_eq762 eq757 eq57 X0
  have eq797 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq797 eq345 eq74
  have eq800 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq800 eq797 eq84
  have eq818 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := step_0_eq818 eq346 eq74
  have eq819 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := step_0_eq819 eq818 eq84
  have eq837 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := step_0_eq837 eq360 eq74
  have eq839 : (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := step_0_eq839 eq837 eq84
  have eq879 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq879 eq371 eq74
  have eq881 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq881 eq879 eq84
  have eq896 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := step_0_eq896 eq372 eq77
  have eq899 : (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 := step_0_eq899 eq372 eq74
  have eq900 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 := step_0_eq900 eq899 eq84
  have eq903 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := step_0_eq903 eq896 eq88
  have eq1466 : c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := step_0_eq1466 eq200 eq325
  have eq1497 : c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ sk2 = sk3 := step_0_eq1497 eq1466
  have eq1529 : c = sk1 ∨ c = sk0 ∨ a = sk0 := step_0_eq1529 eq1497 eq93
  have eq1556 : (old sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 := step_0_eq1556 eq176 eq1529
  have eq1565 : (old sk0 c sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 ∨ c = sk0 ∨ a = sk0 := step_0_eq1565 eq324 eq1529
  have eq1624 : (old sk0 c sk3) ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := step_0_eq1624 eq1565
  have eq1633 : (old sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 := step_0_eq1633 eq1556
  have eq1683 : b = sk3 ∨ c = sk0 ∨ a = sk0 := step_0_eq1683 eq1624 eq54
  have eq1691 : b = sk2 ∨ c = sk0 ∨ a = sk0 := step_0_eq1691 eq1633 eq54
  have eq1735 : b ≠ sk2 ∨ c = sk0 ∨ a = sk0 := step_0_eq1735 eq93 eq1683
  have eq1778 : a = sk0 ∨ c = sk0 := step_0_eq1778 eq1735 eq1691
  have eq1811 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = c ∨ c = sk0 := step_0_eq1811 eq757 eq1778
  have eq1817 : (old a sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk0 := step_0_eq1817 eq800 eq1778
  have eq1823 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk0 := step_0_eq1823 eq839 eq1778
  have eq1863 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := step_0_eq1863 eq1823 eq48
  have eq1865 : (old a sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq1865 eq1817 eq48
  have eq1867 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_0_eq1867 eq1811 eq48
  have eq4747 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq4747 eq762 eq881
  have eq4759 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 := step_0_eq4759 eq4747
  have eq4787 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 := step_0_eq4787 eq4759 eq93
  have eq4835 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 := step_0_eq4835 eq1865 eq4787
  have eq4838 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_0_eq4838 eq4835
  have eq4873 : c = sk1 ∨ b = sk1 ∨ c = sk0 := step_0_eq4873 eq4838 eq51
  have eq5005 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 := step_0_eq5005 eq819 eq4873
  have eq5013 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 := step_0_eq5013 eq900 eq4873
  have eq5066 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 := step_0_eq5066 eq5013
  have eq5068 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := step_0_eq5068 eq5005
  have eq5108 : b = c ∨ b = sk3 ∨ c = sk0 ∨ b = sk1 := step_0_eq5108 eq5066 eq54
  have eq5116 : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := step_0_eq5116 eq5068 eq54
  have eq5148 : b = sk3 ∨ c = sk0 ∨ b = sk1 := step_0_eq5148 eq5108 eq49
  have eq5152 : b = sk2 ∨ c = sk0 ∨ b = sk1 := step_0_eq5152 eq5116 eq49
  have eq5255 : b ≠ sk2 ∨ c = sk0 ∨ b = sk1 := step_0_eq5255 eq93 eq5148
  have eq5346 : b = sk1 ∨ c = sk0 := step_0_eq5346 eq5255 eq5152
  have eq5505 : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk0 := step_0_eq5505 eq1863 eq5346
  have eq5507 : (old a b sk2) ∨ c = sk2 ∨ b = c ∨ c = sk0 ∨ c = sk0 := step_0_eq5507 eq1867 eq5346
  have eq5515 : (old a b sk2) ∨ c = sk2 ∨ b = c ∨ c = sk0 := step_0_eq5515 eq5507
  have eq5517 : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk0 := step_0_eq5517 eq5505
  have eq5551 : c = sk2 ∨ b = c ∨ c = sk0 := step_0_eq5551 eq5515 eq50
  have eq5553 : c = sk3 ∨ b = c ∨ c = sk0 := step_0_eq5553 eq5517 eq50
  have eq5569 : c = sk2 ∨ c = sk0 := step_0_eq5569 eq5551 eq49
  have eq5570 : c = sk3 ∨ c = sk0 := step_0_eq5570 eq5553 eq49
  have eq5796 : c ≠ sk2 ∨ c = sk0 := step_0_eq5796 eq93 eq5570
  have eq5874 : c = sk0 := step_0_eq5874 eq5796 eq5569
  have eq5955 : (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = sk2 := step_0_eq5955 eq168 eq5874
  have eq5961 : (old c sk1 sk2) ∨ a = c ∨ a = sk2 ∨ c = sk1 := step_0_eq5961 eq214 eq5874
  have eq5968 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = c ∨ a = sk3 := step_0_eq5968 eq318 eq5874
  have eq5984 : (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ c = sk1 := step_0_eq5984 eq366 eq5874
  have eq6100 : a = c ∨ a = sk3 ∨ c = sk1 := step_0_eq6100 eq5984 eq56
  have eq6115 : (old c sk1 sk3) ∨ a = c ∨ a = sk3 := step_0_eq6115 eq5968 eq122
  have eq6121 : a = c ∨ a = sk2 ∨ c = sk1 := step_0_eq6121 eq5961 eq56
  have eq6127 : (old c sk1 sk2) ∨ a = c ∨ a = sk2 := step_0_eq6127 eq5955 eq122
  have eq6144 : a = sk3 ∨ c = sk1 := step_0_eq6144 eq6100 eq48
  have eq6149 : (old c sk1 sk3) ∨ a = sk3 := step_0_eq6149 eq6115 eq48
  have eq6150 : a = sk2 ∨ c = sk1 := step_0_eq6150 eq6121 eq48
  have eq6153 : (old c sk1 sk2) ∨ a = sk2 := step_0_eq6153 eq6127 eq48
  have eq6400 : a ≠ sk2 ∨ c = sk1 := step_0_eq6400 eq93 eq6144
  have eq6481 : c = sk1 := step_0_eq6481 eq6400 eq6150
  have eq6623 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 ∨ (old b c a) := step_0_eq6623 eq903 eq6481
  have eq6676 : (old sk0 c sk3) ∨ b = c ∨ b = sk3 := step_0_eq6676 eq6623 eq54
  have eq6733 : (old sk0 c sk3) ∨ b = sk3 := step_0_eq6733 eq6676 eq49
  have eq6781 : (old c c sk3) ∨ b = sk3 := step_0_eq6781 eq6733 eq5874
  have eq7520 : a = sk3 ∨ c = sk3 := step_0_eq7520 eq6149 eq55
  have eq7793 : a = sk2 ∨ c = sk2 := step_0_eq7793 eq6153 eq55
  have eq8332 : c = sk3 ∨ b = sk3 := step_0_eq8332 eq6781 eq114
  have eq8407 : a = c ∨ a = b ∨ c = sk3 := step_0_eq8407 eq8332 eq7520
  have eq8488 : a = b ∨ c = sk3 := step_0_eq8488 eq8407 eq48
  have eq8509 : c = sk3 := step_0_eq8509 eq8488 eq46
  have eq8877 : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ (old b sk1 a) ∨ b = sk3 := step_0_eq8877 eq476 eq568
  have eq8904 : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ sk2 = sk3 ∨ b = sk3 := step_0_eq8904 eq8877
  have eq8927 : (old b sk1 a) ∨ b = sk2 ∨ a = sk0 ∨ b = sk3 := step_0_eq8927 eq8904 eq93
  have eq8931 : (old b c a) ∨ b = sk2 ∨ a = sk0 ∨ b = sk3 := step_0_eq8931 eq8927 eq6481
  have eq8935 : a = c ∨ (old b c a) ∨ b = sk2 ∨ b = sk3 := step_0_eq8935 eq8931 eq5874
  have eq8938 : (old b c a) ∨ b = sk2 ∨ b = sk3 := step_0_eq8938 eq8935 eq48
  have eq8940 : b = c ∨ (old b c a) ∨ b = sk2 := step_0_eq8940 eq8938 eq8509
  have eq8942 : (old b c a) ∨ b = sk2 := step_0_eq8942 eq8940 eq49
  have eq9179 : b = sk2 ∨ a = c := step_0_eq9179 eq8942 eq53
  have eq9190 : b = sk2 := step_0_eq9190 eq9179 eq48
  have eq9284 : a = b ∨ b = c := step_0_eq9284 eq7793 eq9190
  have eq9289 : b = c := step_0_eq9289 eq9284 eq46
  clear * - eq9289 eq49
  first | subsumption eq9289 eq49 | grind only


private theorem step_1_eq47 {G : Type*} {a : G} {b : G} (ab : a ≠ b) : a ≠ b := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ab | grind only

private theorem step_1_eq48 {G : Type*} {old : G → G → G → Prop} (diagonal : ∀ x, old x x x) : ∀ (X0 : G), (old X0 X0 X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using diagonal | grind only

private theorem step_1_eq49 {G : Type*} {a : G} {c : G} (ac : a ≠ c) : a ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ac | grind only

private theorem step_1_eq50 {G : Type*} {b : G} {c : G} (bc : b ≠ c) : b ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using bc | grind only

private theorem step_1_eq51 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (p3 : ∀ z, ¬ old a b z) : ∀ (X0 : G), ¬(old a b X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p3 | grind only

private theorem step_1_eq52 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_1_eq53 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_1_eq54 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_1_eq55 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_1_eq56 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_1_eq57 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_1_eq58 {G : Type*} {old : G → G → G → Prop} (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_0 | grind only

private theorem step_1_eq59 {G : Type*} {old : G → G → G → Prop} (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X2 X0 X3 ∨ ¬ old X3 X1 X4 ∨ old X0 X4 X1)) : ∀ (X0 X1 X2 X3 X4 : G), ¬(old X3 X1 X4) ∨ ¬(old X2 X0 X3) ∨ ¬(old X0 X1 X2) ∨ (old X0 X4 X1) := by
  intro X0 X1 X2 X3 X4
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_1 | grind only

private theorem step_1_eq61 {G : Type*} {old : G → G → G → Prop} (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ old X1 X2 X0)) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ (old X1 X2 X0) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_3 | grind only

private theorem step_1_eq62 {G : Type*} {old : G → G → G → Prop} (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X0 ∨ ¬ old X3 X1 X2 ∨ ¬ old X3 X2 X2 ∨ old X2 X3 X0)) : ∀ (X0 X1 X2 X3 : G), ¬(old X3 X2 X2) ∨ ¬(old X1 X3 X0) ∨ ¬(old X3 X1 X2) ∨ ¬(old X0 X1 X2) ∨ (old X2 X3 X0) := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_4 | grind only

private theorem step_1_eq63 {G : Type*} {old : G → G → G → Prop} (old_5 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X1 X0 X3 ∨ ¬ old X2 X0 X4 ∨ ¬ old X3 X1 X5 ∨ ¬ old X5 X3 X4 ∨ old X4 X1 X2)) : ∀ (X0 X1 X2 X3 X4 X5 : G), ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2) := by
  intro X0 X1 X2 X3 X4 X5
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_5 | grind only

private theorem step_1_eq64 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : ∀ (X0 X1 X2 : G), (new X0 X1 X2) ∨ ¬(old X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_0 | grind only

private theorem step_1_eq66 {G : Type*} {a : G} {sP0 : G → G → G → Prop} (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_0 | grind only

private theorem step_1_eq67 {G : Type*} {b : G} {sP0 : G → G → G → Prop} (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_1 | grind only

private theorem step_1_eq68 {G : Type*} {c : G} {sP0 : G → G → G → Prop} (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_2 | grind only

private theorem step_1_eq69 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ b ≠ Z ∨ ¬ old X b X2 ∨ ¬ old X2 X a ∨ new X Y Z) : ∀ (X0 X1 X2 X3 : G), c ≠ X1 ∨ b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X3 X0 a) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_2 | grind only

private theorem step_1_eq70 {G : Type*} {c : G} {sP1 : G → G → G → Prop} (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_0 | grind only

private theorem step_1_eq71 {G : Type*} {b : G} {sP1 : G → G → G → Prop} (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_1 | grind only

private theorem step_1_eq72 {G : Type*} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old X0 b (sF0 X0 X1 X2)) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_2 | grind only

private theorem step_1_eq73 {G : Type*} {a : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_3 | grind only

private theorem step_1_eq75 {G : Type*} {c : G} {sP2 : G → G → G → Prop} (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_0 | grind only

private theorem step_1_eq76 {G : Type*} {a : G} {sP2 : G → G → G → Prop} (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_1 | grind only

private theorem step_1_eq77 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_2 | grind only

private theorem step_1_eq78 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_3 | grind only

private theorem step_1_eq80 {G : Type*} {a : G} {sP3 : G → G → G → Prop} (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_0 | grind only

private theorem step_1_eq81 {G : Type*} {c : G} {sP3 : G → G → G → Prop} (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_1 | grind only

private theorem step_1_eq82 {G : Type*} {b : G} {sP3 : G → G → G → Prop} (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_2 | grind only

private theorem step_1_eq83 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP3 : G → G → G → Prop} (rule_def_3_3 : ∀ (X Y Z : G), old b a a ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ (old b a a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_3 | grind only

private theorem step_1_eq85 {G : Type*} {c : G} {sP4 : G → G → G → Prop} (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_0 | grind only

private theorem step_1_eq86 {G : Type*} {a : G} {sP4 : G → G → G → Prop} (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_1 | grind only

private theorem step_1_eq87 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_2 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_2 | grind only

private theorem step_1_eq88 {G : Type*} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_3 | grind only

private theorem step_1_eq90 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} (new_new : new a b c) : (new a b c) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_new | grind only

private theorem step_1_eq91 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_imp | grind only

private theorem step_1_eq92 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_0 : new sk0 sk1 sk2) : (new sk0 sk1 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_0 | grind only

private theorem step_1_eq93 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (preserve_1 : new sk2 sk0 sk3) : (new sk2 sk0 sk3) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_1 | grind only

private theorem step_1_eq94 {G : Type*} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (preserve_2 : new sk3 sk1 sk4) : (new sk3 sk1 sk4) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_2 | grind only

private theorem step_1_eq95 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (preserve_3 : ¬ (new sk0 sk4 sk1)) : ¬(new sk0 sk4 sk1) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_3 | grind only

private theorem step_1_eq99 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq69 : ∀ (X0 X1 X2 X3 : G), c ≠ X1 ∨ b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X3 X0 a) ∨ (new X0 X1 X2)) : ∀ (X0 X2 X3 : G), b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X3 X0 a) ∨ (new X0 c X2) := by
  intro X0 X2 X3
  first | exact resolve eq69 rfl | grind only

private theorem step_1_eq100 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq99 : ∀ (X0 X2 X3 : G), b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X3 X0 a) ∨ (new X0 c X2)) : ∀ (X0 X3 : G), ¬(old X3 X0 a) ∨ ¬(old X0 b X3) ∨ (new X0 c b) := by
  intro X0 X3
  first | exact resolve eq99 rfl | grind only

private theorem step_1_eq115 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq64 : ∀ (X0 X1 X2 : G), (new X0 X1 X2) ∨ ¬(old X0 X1 X2)) (eq95 : ¬(new sk0 sk4 sk1)) : ¬(old sk0 sk4 sk1) := by
  first | exact resolve eq64 eq95 | exact resolve eq95 eq64 | grind only

private theorem step_1_eq116 {G : Type*} {old : G → G → G → Prop} (eq58 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) (eq48 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1 := by
  intro X0 X1
  first | exact resolve eq58 eq48 | exact resolve eq48 eq58 | grind only

private theorem step_1_eq118 {G : Type*} {old : G → G → G → Prop} (eq61 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ (old X1 X2 X0)) (eq48 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ (old X0 X1 X0) := by
  intro X0 X1
  first | exact resolve eq61 eq48 | exact resolve eq48 eq61 | grind only

private theorem step_1_eq129 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq91 : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | exact resolve eq91 eq68 | exact resolve eq68 eq91 | grind only

private theorem step_1_eq130 {G : Type*} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq91 : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | exact resolve eq91 eq67 | exact resolve eq67 eq91 | grind only

private theorem step_1_eq131 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq91 : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : ∀ (X0 X1 X2 : G), (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | exact resolve eq91 eq66 | exact resolve eq66 eq91 | grind only

private theorem step_1_eq132 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq131 : ∀ (X0 X1 X2 : G), (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | exact resolve eq131 eq80 | exact resolve eq80 eq131 | grind only

private theorem step_1_eq134 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq132 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq132 eq78 | exact resolve eq78 eq132 | grind only

private theorem step_1_eq135 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq132 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | exact resolve eq132 eq77 | exact resolve eq77 eq132 | grind only

private theorem step_1_eq136 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq132 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq132 eq76 | exact resolve eq76 eq132 | grind only

private theorem step_1_eq137 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq132 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq132 eq75 | exact resolve eq75 eq132 | grind only

private theorem step_1_eq138 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq137 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq137 eq85 | exact resolve eq85 eq137 | grind only

private theorem step_1_eq139 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq136 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ a = X2) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq136 eq86 | exact resolve eq86 eq136 | grind only

private theorem step_1_eq140 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq135 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old X1 b b)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b)) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | exact resolve eq135 eq88 | exact resolve eq88 eq135 | grind only

private theorem step_1_eq141 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq134 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old b X1 a)) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq134 eq87 | exact resolve eq87 eq134 | grind only

private theorem step_1_eq142 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq138 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq73 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old (sF0 X0 X1 X2) X0 a) := by
  intro X0 X1 X2
  first | exact resolve eq138 eq73 | exact resolve eq73 eq138 | grind only

private theorem step_1_eq143 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq138 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old X0 b (sF0 X0 X1 X2))) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2)) := by
  intro X0 X1 X2
  first | exact resolve eq138 eq72 | exact resolve eq72 eq138 | grind only

private theorem step_1_eq144 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq138 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq138 eq71 | exact resolve eq71 eq138 | grind only

private theorem step_1_eq145 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq138 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq138 eq70 | exact resolve eq70 eq138 | grind only

private theorem step_1_eq148 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq129 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq129 eq81 | exact resolve eq81 eq129 | grind only

private theorem step_1_eq150 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq148 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq148 eq70 | exact resolve eq70 eq148 | grind only

private theorem step_1_eq156 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq144 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 := by
  first | exact resolve eq144 eq92 | exact resolve eq92 eq144 | grind only

private theorem step_1_eq157 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq144 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ a = sk2 ∨ c = sk2 ∨ b = sk3 := by
  first | exact resolve eq144 eq93 | exact resolve eq93 eq144 | grind only

private theorem step_1_eq159 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq130 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1) (eq83 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ (old b a a)) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ (old b a a) := by
  intro X0 X1 X2
  first | exact resolve eq130 eq83 | exact resolve eq83 eq130 | grind only

private theorem step_1_eq160 {G : Type*} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq130 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq130 eq82 | exact resolve eq82 eq130 | grind only

private theorem step_1_eq161 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq130 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq130 eq81 | exact resolve eq81 eq130 | grind only

private theorem step_1_eq163 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq161 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq161 eq70 | exact resolve eq70 eq161 | grind only

private theorem step_1_eq164 {G : Type*} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq160 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq160 eq71 | exact resolve eq71 eq160 | grind only

private theorem step_1_eq172 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq139 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq139 eq70 | exact resolve eq70 eq139 | grind only

private theorem step_1_eq180 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq140 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old X1 b b)) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq140 eq70 | exact resolve eq70 eq140 | grind only

private theorem step_1_eq185 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq141 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a)) (eq73 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a) := by
  intro X0 X1 X2
  first | exact resolve eq141 eq73 | exact resolve eq73 eq141 | grind only

private theorem step_1_eq188 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq141 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a)) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq141 eq70 | exact resolve eq70 eq141 | grind only

private theorem step_1_eq191 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq150 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq150 eq78 | exact resolve eq78 eq150 | grind only

private theorem step_1_eq193 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq150 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq150 eq76 | exact resolve eq76 eq150 | grind only

private theorem step_1_eq194 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq150 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq150 eq75 | exact resolve eq75 eq150 | grind only

private theorem step_1_eq195 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq194 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq194 eq85 | exact resolve eq85 eq194 | grind only

private theorem step_1_eq196 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq193 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq193 eq86 | exact resolve eq86 eq193 | grind only

private theorem step_1_eq198 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq191 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ (old b X1 a)) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq191 eq87 | exact resolve eq87 eq191 | grind only

private theorem step_1_eq211 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq163 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq163 eq78 | exact resolve eq78 eq163 | grind only

private theorem step_1_eq212 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq163 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | exact resolve eq163 eq77 | exact resolve eq77 eq163 | grind only

private theorem step_1_eq213 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq163 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq163 eq76 | exact resolve eq76 eq163 | grind only

private theorem step_1_eq214 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq163 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq163 eq75 | exact resolve eq75 eq163 | grind only

private theorem step_1_eq215 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq214 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq214 eq85 | exact resolve eq85 eq214 | grind only

private theorem step_1_eq216 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq213 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq213 eq86 | exact resolve eq86 eq213 | grind only

private theorem step_1_eq217 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq212 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | exact resolve eq212 eq88 | exact resolve eq88 eq212 | grind only

private theorem step_1_eq218 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq211 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a)) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq211 eq87 | exact resolve eq87 eq211 | grind only

private theorem step_1_eq222 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq164 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq164 eq75 | exact resolve eq75 eq164 | grind only

private theorem step_1_eq223 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq222 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq222 eq85 | exact resolve eq85 eq222 | grind only

private theorem step_1_eq238 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq159 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ (old b a a)) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq159 eq75 | exact resolve eq75 eq159 | grind only

private theorem step_1_eq239 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq238 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq238 eq85 | exact resolve eq85 eq238 | grind only

private theorem step_1_eq248 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq145 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq145 eq92 | exact resolve eq92 eq145 | grind only

private theorem step_1_eq250 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq145 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq145 eq94 | exact resolve eq94 eq145 | grind only

private theorem step_1_eq274 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq172 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 ∨ c = sk1 := by
  first | exact resolve eq172 eq92 | exact resolve eq92 eq172 | grind only

private theorem step_1_eq287 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq195 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq195 eq92 | exact resolve eq92 eq195 | grind only

private theorem step_1_eq288 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq195 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq195 eq93 | exact resolve eq93 eq195 | grind only

private theorem step_1_eq289 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq195 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq195 eq94 | exact resolve eq94 eq195 | grind only

private theorem step_1_eq301 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq196 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = sk3 := by
  first | exact resolve eq196 eq93 | exact resolve eq93 eq196 | grind only

private theorem step_1_eq339 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq215 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq215 eq92 | exact resolve eq92 eq215 | grind only

private theorem step_1_eq340 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq215 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq215 eq93 | exact resolve eq93 eq215 | grind only

private theorem step_1_eq341 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq215 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq215 eq94 | exact resolve eq94 eq215 | grind only

private theorem step_1_eq353 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq216 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk3 := by
  first | exact resolve eq216 eq93 | exact resolve eq93 eq216 | grind only

private theorem step_1_eq354 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq216 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 := by
  first | exact resolve eq216 eq94 | exact resolve eq94 eq216 | grind only

private theorem step_1_eq365 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq223 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := by
  first | exact resolve eq223 eq92 | exact resolve eq92 eq223 | grind only

private theorem step_1_eq367 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq223 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 ∨ c = sk3 := by
  first | exact resolve eq223 eq94 | exact resolve eq94 eq223 | grind only

private theorem step_1_eq397 {G : Type*} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq289 : (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk3) (eq59 : ∀ (X0 X1 X2 X3 X4 : G), ¬(old X3 X1 X4) ∨ ¬(old X2 X0 X3) ∨ ¬(old X0 X1 X2) ∨ (old X0 X4 X1)) : ∀ (X0 X1 : G), ¬(old X0 X1 sk3) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1) := by
  intro X0 X1
  first | exact resolve eq289 eq59 | exact resolve eq59 eq289 | grind only

private theorem step_1_eq428 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq188 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1) (eq92 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1 := by
  first | exact resolve eq188 eq92 | exact resolve eq92 eq188 | grind only

private theorem step_1_eq430 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq188 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ a = sk3 ∨ (old b sk1 a) ∨ c = sk1 := by
  first | exact resolve eq188 eq94 | exact resolve eq94 eq188 | grind only

private theorem step_1_eq454 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq198 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ (old b X1 a)) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ (old b sk0 a) := by
  first | exact resolve eq198 eq93 | exact resolve eq93 eq198 | grind only

private theorem step_1_eq493 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq217 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b)) (eq93 : (new sk2 sk0 sk3)) : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ (old sk0 b b) := by
  first | exact resolve eq217 eq93 | exact resolve eq93 eq217 | grind only

private theorem step_1_eq494 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq217 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b)) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) := by
  first | exact resolve eq217 eq94 | exact resolve eq94 eq217 | grind only

private theorem step_1_eq507 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq218 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a)) (eq94 : (new sk3 sk1 sk4)) : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := by
  first | exact resolve eq218 eq94 | exact resolve eq94 eq218 | grind only

private theorem step_1_eq544 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq142 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old (sF0 X0 X1 X2) X0 a)) (eq92 : (new sk0 sk1 sk2)) : (old (sF0 sk0 sk1 sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2) := by
  first | exact resolve eq142 eq92 | exact resolve eq92 eq142 | grind only

private theorem step_1_eq546 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk3 : G} {sk4 : G} (eq142 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old (sF0 X0 X1 X2) X0 a)) (eq94 : (new sk3 sk1 sk4)) : (old (sF0 sk3 sk1 sk4) sk3 a) ∨ a = sk3 ∨ c = sk3 ∨ (old sk3 sk1 sk4) := by
  first | exact resolve eq142 eq94 | exact resolve eq94 eq142 | grind only

private theorem step_1_eq557 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq143 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2))) (eq92 : (new sk0 sk1 sk2)) : (old sk0 b (sF0 sk0 sk1 sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2) := by
  first | exact resolve eq143 eq92 | exact resolve eq92 eq143 | grind only

private theorem step_1_eq559 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk3 : G} {sk4 : G} (eq143 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2))) (eq94 : (new sk3 sk1 sk4)) : (old sk3 b (sF0 sk3 sk1 sk4)) ∨ a = sk3 ∨ c = sk3 ∨ (old sk3 sk1 sk4) := by
  first | exact resolve eq143 eq94 | exact resolve eq94 eq143 | grind only

private theorem step_1_eq662 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq239 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old X0 b (sF0 X0 X1 X2))) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2)) := by
  intro X0 X1 X2
  first | exact resolve eq239 eq72 | exact resolve eq72 eq239 | grind only

private theorem step_1_eq756 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq430 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ (old b sk1 a) ∨ c = sk1) (eq59 : ∀ (X0 X1 X2 X3 X4 : G), ¬(old X3 X1 X4) ∨ ¬(old X2 X0 X3) ∨ ¬(old X0 X1 X2) ∨ (old X0 X4 X1)) : ∀ (X0 X1 : G), ¬(old X0 X1 sk3) ∨ (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1) := by
  intro X0 X1
  first | exact resolve eq430 eq59 | exact resolve eq59 eq430 | grind only

private theorem step_1_eq982 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk3 : G} {sk4 : G} (eq546 : (old (sF0 sk3 sk1 sk4) sk3 a) ∨ a = sk3 ∨ c = sk3 ∨ (old sk3 sk1 sk4)) (eq63 : ∀ (X0 X1 X2 X3 X4 X5 : G), ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 sk3) ∨ c = sk3 ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X2 X1 a) ∨ ¬(old sk3 X0 (sF0 sk3 sk1 sk4)) ∨ ¬(old X1 X0 X2) ∨ (old a X0 X2) := by
  intro X0 X1 X2
  first | exact resolve eq546 eq63 | exact resolve eq63 eq546 | grind only

private theorem step_1_eq2164 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk3 : G} {sk4 : G} (eq662 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2))) (eq94 : (new sk3 sk1 sk4)) : (old sk3 b (sF0 sk3 sk1 sk4)) ∨ b = sk1 ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 sk1 sk4) := by
  first | exact resolve eq662 eq94 | exact resolve eq94 eq662 | grind only

private theorem step_1_eq5009 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq397 : ∀ (X0 X1 : G), ¬(old X0 X1 sk3) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1)) (eq288 : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq397 eq288 | exact resolve eq288 eq397 | grind only

private theorem step_1_eq5022 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq397 : ∀ (X0 X1 : G), ¬(old X0 X1 sk3) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1)) (eq454 : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ (old b sk0 a)) : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ (old b sk0 a) := by
  first | exact resolve eq397 eq454 | exact resolve eq454 eq397 | grind only

private theorem step_1_eq5037 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq5022 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ (old b sk0 a)) : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ (old b sk0 a) := by
  first | exact resolve eq5022 rfl | grind only

private theorem step_1_eq5042 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq5009 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5009 rfl | grind only

private theorem step_1_eq5052 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq5037 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ (old b sk0 a)) (eq115 : ¬(old sk0 sk4 sk1)) : ¬(old sk0 sk1 sk2) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ (old b sk0 a) := by
  first | exact resolve eq5037 eq115 | exact resolve eq115 eq5037 | grind only

private theorem step_1_eq5061 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq5042 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ c = sk2) (eq287 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5042 eq287 | exact resolve eq287 eq5042 | grind only

private theorem step_1_eq5065 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq5061 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ c = sk2) (eq115 : ¬(old sk0 sk4 sk1)) : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5061 eq115 | exact resolve eq115 eq5061 | grind only

private theorem step_1_eq5078 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq341 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3) (eq5065 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq341 eq5065 | exact superpose eq5065 eq341 | grind only

private theorem step_1_eq5132 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5078 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5078 rfl | grind only

private theorem step_1_eq5145 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5132 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5132 eq52 | exact resolve eq52 eq5132 | grind only

private theorem step_1_eq5172 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq340 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq5145 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq340 eq5145 | exact superpose eq5145 eq340 | grind only

private theorem step_1_eq5175 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq354 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4) (eq5145 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq354 eq5145 | exact superpose eq5145 eq354 | grind only

private theorem step_1_eq5197 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq494 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b)) (eq5145 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq494 eq5145 | exact superpose eq5145 eq494 | grind only

private theorem step_1_eq5199 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq507 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a)) (eq5145 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq507 eq5145 | exact superpose eq5145 eq507 | grind only

private theorem step_1_eq5296 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq5199 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5199 rfl | grind only

private theorem step_1_eq5298 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq5197 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5197 rfl | grind only

private theorem step_1_eq5313 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq5175 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5175 rfl | grind only

private theorem step_1_eq5316 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5172 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq5172 rfl | grind only

private theorem step_1_eq5349 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq5296 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk0 ∨ c = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5296 eq57 | exact resolve eq57 eq5296 | grind only

private theorem step_1_eq5351 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq5298 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) ∨ c = sk0 ∨ c = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : (old sk1 b b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5298 eq57 | exact resolve eq57 eq5298 | grind only

private theorem step_1_eq5369 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq5313 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 ∨ c = sk0 ∨ c = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq5313 eq57 | exact resolve eq57 eq5313 | grind only

private theorem step_1_eq5371 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5316 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq5316 eq52 | exact resolve eq52 eq5316 | grind only

private theorem step_1_eq5690 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq339 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq5371 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1) : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := by
  first | exact superpose eq339 eq5371 | exact superpose eq5371 eq339 | grind only

private theorem step_1_eq5833 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq5690 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1) : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq5690 rfl | grind only

private theorem step_1_eq5882 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq5833 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq5833 eq52 | exact resolve eq52 eq5833 | grind only

private theorem step_1_eq5923 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq95 : ¬(new sk0 sk4 sk1)) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : ¬(new sk0 sk4 c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq95 eq5882 | exact superpose eq5882 eq95 | grind only

private theorem step_1_eq5942 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq365 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq365 eq5882 | exact superpose eq5882 eq365 | grind only

private theorem step_1_eq5943 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq367 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 ∨ c = sk3) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk3 c sk4) ∨ b = c ∨ b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq367 eq5882 | exact superpose eq5882 eq367 | grind only

private theorem step_1_eq5966 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq544 : (old (sF0 sk0 sk1 sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2)) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq544 eq5882 | exact superpose eq5882 eq544 | grind only

private theorem step_1_eq5968 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq557 : (old sk0 b (sF0 sk0 sk1 sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2)) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq557 eq5882 | exact superpose eq5882 eq557 | grind only

private theorem step_1_eq6025 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq5968 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq5968 rfl | grind only

private theorem step_1_eq6026 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq5966 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq5966 rfl | grind only

private theorem step_1_eq6029 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5942 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq5942 rfl | grind only

private theorem step_1_eq6055 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq6025 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ b = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq6025 eq55 | exact resolve eq55 eq6025 | grind only

private theorem step_1_eq6057 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq6026 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ b = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq6026 eq55 | exact resolve eq55 eq6026 | grind only

private theorem step_1_eq6070 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq5943 : (old sk3 c sk4) ∨ b = c ∨ b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = c ∨ b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq5943 eq55 | exact resolve eq55 eq5943 | grind only

private theorem step_1_eq6071 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq6029 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq6029 eq55 | exact resolve eq55 eq6029 | grind only

private theorem step_1_eq6087 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq6070 : b = c ∨ b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq50 : b ≠ c) : b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq6070 eq50 | exact resolve eq50 eq6070 | grind only

private theorem step_1_eq6088 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq6071 : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) (eq50 : b ≠ c) : b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq6071 eq50 | exact resolve eq50 eq6071 | grind only

private theorem step_1_eq6218 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq340 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq6088 : b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = c ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact superpose eq340 eq6088 | exact superpose eq6088 eq340 | grind only

private theorem step_1_eq6382 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq6218 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = c ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = c ∨ b = sk1 := by
  first | exact resolve eq6218 rfl | grind only

private theorem step_1_eq6438 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq6382 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = c ∨ b = sk1) (eq50 : b ≠ c) : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq6382 eq50 | exact resolve eq50 eq6382 | grind only

private theorem step_1_eq8426 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq5923 : ¬(new sk0 sk4 c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq6087 : b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : ¬(new sk0 b c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq5923 eq6087 | exact superpose eq6087 eq5923 | grind only

private theorem step_1_eq8427 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq8426 : ¬(new sk0 b c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : ¬(new sk0 b c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 := by
  first | exact resolve eq8426 rfl | grind only

private theorem step_1_eq9440 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq2164 : (old sk3 b (sF0 sk3 sk1 sk4)) ∨ b = sk1 ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 sk1 sk4)) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk3 b (sF0 sk3 c sk4)) ∨ b = c ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 c sk4) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq2164 eq5882 | exact superpose eq5882 eq2164 | grind only

private theorem step_1_eq9452 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq9440 : (old sk3 b (sF0 sk3 c sk4)) ∨ b = c ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 c sk4) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq50 : b ≠ c) : (old sk3 b (sF0 sk3 c sk4)) ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 c sk4) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq9440 eq50 | exact resolve eq50 eq9440 | grind only

private theorem step_1_eq9453 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq9452 : (old sk3 b (sF0 sk3 c sk4)) ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 c sk4) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk3 b (sF0 sk3 c sk4)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq9452 eq55 | exact resolve eq55 eq9452 | grind only

private theorem step_1_eq9499 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5351 : (old sk1 b b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq61 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ (old X1 X2 X0)) : ∀ (X0 : G), ¬(old b sk1 X0) ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (old b X0 sk1) := by
  intro X0
  first | exact resolve eq5351 eq61 | exact resolve eq61 eq5351 | grind only

private theorem step_1_eq9998 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq756 : ∀ (X0 X1 : G), ¬(old X0 X1 sk3) ∨ (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1)) (eq353 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk3) : (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ b = sk0 ∨ c = sk0 ∨ a = sk3 := by
  first | exact resolve eq756 eq353 | exact resolve eq353 eq756 | grind only

private theorem step_1_eq10016 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq9998 : (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ b = sk0 ∨ c = sk0 ∨ a = sk3) : (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ b = sk0 ∨ c = sk0 := by
  first | exact resolve eq9998 rfl | grind only

private theorem step_1_eq10031 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq10016 : (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ b = sk0 ∨ c = sk0) (eq115 : ¬(old sk0 sk4 sk1)) : ¬(old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk3 ∨ (old b sk1 a) ∨ b = sk0 ∨ c = sk0 := by
  first | exact resolve eq10016 eq115 | exact resolve eq115 eq10016 | grind only

private theorem step_1_eq17397 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq982 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 sk3) ∨ c = sk3 ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X2 X1 a) ∨ ¬(old sk3 X0 (sF0 sk3 sk1 sk4)) ∨ ¬(old X1 X0 X2) ∨ (old a X0 X2)) (eq301 : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = sk3) : ∀ (X0 : G), c = sk3 ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 sk2 (sF0 sk3 sk1 sk4)) ∨ ¬(old sk0 sk2 X0) ∨ (old a sk2 X0) ∨ c = sk3 ∨ c = sk0 ∨ a = sk3 := by
  intro X0
  first | exact resolve eq982 eq301 | exact resolve eq301 eq982 | grind only

private theorem step_1_eq17425 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq17397 : ∀ (X0 : G), c = sk3 ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 sk2 (sF0 sk3 sk1 sk4)) ∨ ¬(old sk0 sk2 X0) ∨ (old a sk2 X0) ∨ c = sk3 ∨ c = sk0 ∨ a = sk3) : ∀ (X0 : G), ¬(old sk0 sk2 X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 sk2 (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a sk2 X0) ∨ c = sk0 := by
  intro X0
  first | exact resolve eq17397 rfl | grind only

private theorem step_1_eq21227 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq5052 : ¬(old sk0 sk1 sk2) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ (old b sk0 a)) (eq248 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) : c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ (old b sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq5052 eq248 | exact resolve eq248 eq5052 | grind only

private theorem step_1_eq21262 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq21227 : c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ (old b sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) : (old b sk0 a) ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq21227 rfl | grind only

private theorem step_1_eq22987 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq10031 : ¬(old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk3 ∨ (old b sk1 a) ∨ b = sk0 ∨ c = sk0) (eq428 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1) : c = sk1 ∨ a = sk3 ∨ (old b sk1 a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1 := by
  first | exact resolve eq10031 eq428 | exact resolve eq428 eq10031 | grind only

private theorem step_1_eq23004 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq22987 : c = sk1 ∨ a = sk3 ∨ (old b sk1 a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1) : (old b sk1 a) ∨ a = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq22987 rfl | grind only

private theorem step_1_eq30357 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq9499 : ∀ (X0 : G), ¬(old b sk1 X0) ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (old b X0 sk1)) (eq5349 : (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (old b a sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq9499 eq5349 | exact resolve eq5349 eq9499 | grind only

private theorem step_1_eq30404 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq30357 : b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (old b a sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old b a sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq30357 rfl | grind only

private theorem step_1_eq65331 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq17425 : ∀ (X0 : G), ¬(old sk0 sk2 X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 sk2 (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a sk2 X0) ∨ c = sk0) (eq6088 : b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 b (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  intro X0
  first | exact superpose eq17425 eq6088 | exact superpose eq6088 eq17425 | grind only

private theorem step_1_eq65334 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq65331 : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 b (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 b (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  intro X0
  first | exact resolve eq65331 rfl | grind only

private theorem step_1_eq65336 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq65334 : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 b (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) (eq559 : (old sk3 b (sF0 sk3 sk1 sk4)) ∨ a = sk3 ∨ c = sk3 ∨ (old sk3 sk1 sk4)) : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  intro X0
  first | exact resolve eq65334 eq559 | exact resolve eq559 eq65334 | grind only

private theorem step_1_eq65337 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq65336 : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  intro X0
  first | exact resolve eq65336 eq51 | exact resolve eq51 eq65336 | grind only

private theorem step_1_eq73422 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq9453 : (old sk3 b (sF0 sk3 c sk4)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq6087 : b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk3 b (sF0 sk3 c b)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq9453 eq6087 | exact superpose eq6087 eq9453 | grind only

private theorem step_1_eq73465 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq73422 : (old sk3 b (sF0 sk3 c b)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk3 b (sF0 sk3 c b)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq73422 rfl | grind only

private theorem step_1_eq189713 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq65337 : ∀ (X0 : G), ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) (eq6055 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq65337 eq6055 | exact resolve eq6055 eq65337 | grind only

private theorem step_1_eq189790 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq189713 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 := by
  first | exact resolve eq189713 rfl | grind only

private theorem step_1_eq189820 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq189790 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0) (eq6057 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 := by
  first | exact resolve eq189790 eq6057 | exact resolve eq6057 eq189790 | grind only

private theorem step_1_eq189904 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq189820 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0) (eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk3 c sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq189820 eq5882 | exact superpose eq5882 eq189820 | grind only

private theorem step_1_eq189981 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq189904 : (old sk3 c sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old sk3 c sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := by
  first | exact resolve eq189904 rfl | grind only

private theorem step_1_eq190017 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq189981 : (old sk3 c sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := by
  first | exact resolve eq189981 eq55 | exact resolve eq55 eq189981 | grind only

private theorem step_1_eq190018 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk3 : G} (eq190017 : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1) (eq50 : b ≠ c) : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := by
  first | exact resolve eq190017 eq50 | exact resolve eq50 eq190017 | grind only

private theorem step_1_eq190186 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq6438 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1) (eq190018 : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1) : (old b sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := by
  first | exact superpose eq6438 eq190018 | exact superpose eq190018 eq6438 | grind only

private theorem step_1_eq190460 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq73465 : (old sk3 b (sF0 sk3 c b)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) (eq190018 : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1) : (old a b (sF0 a c b)) ∨ (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := by
  first | exact superpose eq73465 eq190018 | exact superpose eq190018 eq73465 | grind only

private theorem step_1_eq190498 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq190460 : (old a b (sF0 a c b)) ∨ (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1) : (old a b (sF0 a c b)) ∨ (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq190460 rfl | grind only

private theorem step_1_eq190647 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq190186 : (old b sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1) : (old b sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq190186 rfl | grind only

private theorem step_1_eq190730 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq190498 : (old a b (sF0 a c b)) ∨ (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq190498 eq51 | exact resolve eq51 eq190498 | grind only

private theorem step_1_eq190862 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq190730 : (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0) (eq49 : a ≠ c) : (old b a a) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq190730 eq49 | exact resolve eq49 eq190730 | grind only

private theorem step_1_eq191830 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq190862 : (old b a a) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0) (eq62 : ∀ (X0 X1 X2 X3 : G), ¬(old X3 X2 X2) ∨ ¬(old X1 X3 X0) ∨ ¬(old X3 X1 X2) ∨ ¬(old X0 X1 X2) ∨ (old X2 X3 X0)) : ∀ (X0 X1 : G), b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old X0 b X1) ∨ ¬(old b X0 a) ∨ ¬(old X1 X0 a) ∨ (old a b X1) := by
  intro X0 X1
  first | exact resolve eq190862 eq62 | exact resolve eq62 eq190862 | grind only

private theorem step_1_eq191916 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq191830 : ∀ (X0 X1 : G), b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old X0 b X1) ∨ ¬(old b X0 a) ∨ ¬(old X1 X0 a) ∨ (old a b X1)) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : ∀ (X0 X1 : G), ¬(old b X0 a) ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old X0 b X1) ∨ b = sk1 ∨ ¬(old X1 X0 a) := by
  intro X0 X1
  first | exact resolve eq191830 eq51 | exact resolve eq51 eq191830 | grind only

private theorem step_1_eq210509 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq191916 : ∀ (X0 X1 : G), ¬(old b X0 a) ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old X0 b X1) ∨ b = sk1 ∨ ¬(old X1 X0 a)) (eq190647 : (old b sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ a = sk0) : ∀ (X0 : G), c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old sk0 b X0) ∨ b = sk1 ∨ ¬(old X0 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ a = sk0 := by
  intro X0
  first | exact resolve eq191916 eq190647 | exact resolve eq190647 eq191916 | grind only

private theorem step_1_eq210722 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq210509 : ∀ (X0 : G), c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old sk0 b X0) ∨ b = sk1 ∨ ¬(old X0 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ a = sk0) : ∀ (X0 : G), ¬(old sk0 b X0) ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old X0 sk0 a) := by
  intro X0
  first | exact resolve eq210509 rfl | grind only

private theorem step_1_eq210896 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq210722 : ∀ (X0 : G), ¬(old sk0 b X0) ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old X0 sk0 a)) (eq6055 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq210722 eq6055 | exact resolve eq6055 eq210722 | grind only

private theorem step_1_eq210995 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq210896 : b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) := by
  first | exact resolve eq210896 rfl | grind only

private theorem step_1_eq211079 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq210995 : b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old (sF0 sk0 c sk2) sk0 a)) (eq6057 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0) : c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq210995 eq6057 | exact resolve eq6057 eq210995 | grind only

private theorem step_1_eq211300 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq6438 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1) (eq211079 : c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1) : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq6438 eq211079 | exact superpose eq211079 eq6438 | grind only

private theorem step_1_eq211867 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq211300 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1) : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ a = sk0 := by
  first | exact resolve eq211300 rfl | grind only

private theorem step_1_eq212188 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq211867 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ a = sk0) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact resolve eq211867 eq52 | exact resolve eq52 eq211867 | grind only

private theorem step_1_eq212353 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq94 : (new sk3 sk1 sk4)) (eq212188 : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (new sk3 b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact superpose eq94 eq212188 | exact superpose eq212188 eq94 | grind only

private theorem step_1_eq212354 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq95 : ¬(new sk0 sk4 sk1)) (eq212188 : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : ¬(new sk0 sk4 b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact superpose eq95 eq212188 | exact superpose eq212188 eq95 | grind only

private theorem step_1_eq212365 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq248 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) (eq212188 : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact superpose eq248 eq212188 | exact superpose eq212188 eq248 | grind only

private theorem step_1_eq213009 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq23004 : (old b sk1 a) ∨ a = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) (eq212188 : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (old b b a) ∨ a = sk3 ∨ b = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact superpose eq23004 eq212188 | exact superpose eq212188 eq23004 | grind only

private theorem step_1_eq213722 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq213009 : (old b b a) ∨ a = sk3 ∨ b = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (old b b a) ∨ a = sk3 ∨ b = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq213009 rfl | grind only

private theorem step_1_eq214083 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq212365 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = c ∨ b = sk0 := by
  first | exact resolve eq212365 rfl | grind only

private theorem step_1_eq214244 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq213722 : (old b b a) ∨ a = sk3 ∨ b = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) (eq50 : b ≠ c) : (old b b a) ∨ a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq213722 eq50 | exact resolve eq50 eq213722 | grind only

private theorem step_1_eq214452 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq214083 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = c ∨ b = sk0) (eq50 : b ≠ c) : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq214083 eq50 | exact resolve eq50 eq214083 | grind only

private theorem step_1_eq217796 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq214244 : (old b b a) ∨ a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) (eq116 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ a = b := by
  first | exact resolve eq214244 eq116 | exact resolve eq116 eq214244 | grind only

private theorem step_1_eq217804 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk3 : G} (eq217796 : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ a = b) (eq47 : a ≠ b) : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := by
  first | exact resolve eq217796 eq47 | exact resolve eq47 eq217796 | grind only

private theorem step_1_eq217913 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq340 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq217804 : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) : (old sk2 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := by
  first | exact superpose eq340 eq217804 | exact superpose eq217804 eq340 | grind only

private theorem step_1_eq218391 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk3 : G} {sk4 : G} (eq212353 : (new sk3 b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) (eq217804 : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) : (new a b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := by
  first | exact superpose eq212353 eq217804 | exact superpose eq217804 eq212353 | grind only

private theorem step_1_eq218392 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq218391 : (new a b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) : (new a b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact resolve eq218391 rfl | grind only

private theorem step_1_eq218511 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq217913 : (old sk2 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0) : (old sk2 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 := by
  first | exact resolve eq217913 rfl | grind only

private theorem step_1_eq219037 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq218392 : (new a b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) (eq195 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ (old a b sk4) ∨ c = sk4 ∨ b = c ∨ a = c := by
  first | exact resolve eq218392 eq195 | exact resolve eq195 eq218392 | grind only

private theorem step_1_eq219152 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq219037 : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ (old a b sk4) ∨ c = sk4 ∨ b = c ∨ a = c) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk4 ∨ b = c ∨ a = c := by
  first | exact resolve eq219037 eq51 | exact resolve eq51 eq219037 | grind only

private theorem step_1_eq219160 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk4 : G} (eq219152 : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk4 ∨ b = c ∨ a = c) (eq50 : b ≠ c) : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk4 ∨ a = c := by
  first | exact resolve eq219152 eq50 | exact resolve eq50 eq219152 | grind only

private theorem step_1_eq219162 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk4 : G} (eq219160 : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk4 ∨ a = c) (eq49 : a ≠ c) : c = sk4 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := by
  first | exact resolve eq219160 eq49 | exact resolve eq49 eq219160 | grind only

private theorem step_1_eq219405 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq212354 : ¬(new sk0 sk4 b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) (eq219162 : c = sk4 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0) : ¬(new sk0 c b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := by
  first | exact superpose eq212354 eq219162 | exact superpose eq219162 eq212354 | grind only

private theorem step_1_eq219412 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} (eq219405 : ¬(new sk0 c b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0) : ¬(new sk0 c b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact resolve eq219405 rfl | grind only

private theorem step_1_eq222788 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq218511 : (old sk2 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0) (eq100 : ∀ (X0 X3 : G), ¬(old X3 X0 a) ∨ ¬(old X0 b X3) ∨ (new X0 c b)) : b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ ¬(old sk0 b sk2) ∨ (new sk0 c b) := by
  first | exact resolve eq218511 eq100 | exact resolve eq100 eq218511 | grind only

private theorem step_1_eq222837 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq222788 : b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ ¬(old sk0 b sk2) ∨ (new sk0 c b)) (eq214452 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0) : b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ (new sk0 c b) := by
  first | exact resolve eq222788 eq214452 | exact resolve eq214452 eq222788 | grind only

private theorem step_1_eq222838 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq222837 : b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ (new sk0 c b)) (eq219412 : ¬(new sk0 c b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact resolve eq222837 eq219412 | exact resolve eq219412 eq222837 | grind only

private theorem step_1_eq223817 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq214452 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0) (eq222838 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (old sk0 b c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := by
  first | exact superpose eq214452 eq222838 | exact superpose eq222838 eq214452 | grind only

private theorem step_1_eq223822 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq223817 : (old sk0 b c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0) : (old sk0 b c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq223817 rfl | grind only

private theorem step_1_eq224264 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq223822 : (old sk0 b c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0) : a = sk0 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq223822 eq53 | exact resolve eq53 eq223822 | grind only

private theorem step_1_eq224807 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq92 : (new sk0 sk1 sk2)) (eq224264 : a = sk0 ∨ c = sk0 ∨ b = sk0) : (new a sk1 sk2) ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq92 eq224264 | exact superpose eq224264 eq92 | grind only

private theorem step_1_eq224878 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq493 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ (old sk0 b b)) (eq224264 : a = sk0 ∨ c = sk0 ∨ b = sk0) : (old sk2 a sk3) ∨ a = b ∨ a = c ∨ (old a b b) ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq493 eq224264 | exact superpose eq224264 eq493 | grind only

private theorem step_1_eq225169 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq8427 : ¬(new sk0 b c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3) (eq224264 : a = sk0 ∨ c = sk0 ∨ b = sk0) : ¬(new a b c) ∨ b = sk1 ∨ a = c ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq8427 eq224264 | exact superpose eq224264 eq8427 | grind only

private theorem step_1_eq226477 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq225169 : ¬(new a b c) ∨ b = sk1 ∨ a = c ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0) (eq90 : (new a b c)) : b = sk1 ∨ a = c ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq225169 eq90 | exact resolve eq90 eq225169 | grind only

private theorem step_1_eq226627 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq224878 : (old sk2 a sk3) ∨ a = b ∨ a = c ∨ (old a b b) ∨ c = sk0 ∨ b = sk0) (eq47 : a ≠ b) : (old sk2 a sk3) ∨ a = c ∨ (old a b b) ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq224878 eq47 | exact resolve eq47 eq224878 | grind only

private theorem step_1_eq226751 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk3 : G} (eq226477 : b = sk1 ∨ a = c ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0) (eq49 : a ≠ c) : b = sk1 ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq226477 eq49 | exact resolve eq49 eq226477 | grind only

private theorem step_1_eq226811 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq226627 : (old sk2 a sk3) ∨ a = c ∨ (old a b b) ∨ c = sk0 ∨ b = sk0) (eq49 : a ≠ c) : (old sk2 a sk3) ∨ (old a b b) ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq226627 eq49 | exact resolve eq49 eq226627 | grind only

private theorem step_1_eq226829 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk3 : G} (eq226751 : b = sk1 ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0) (eq47 : a ≠ b) : c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq226751 eq47 | exact resolve eq47 eq226751 | grind only

private theorem step_1_eq226836 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq226811 : (old sk2 a sk3) ∨ (old a b b) ∨ c = sk0 ∨ b = sk0) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : (old sk2 a sk3) ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq226811 eq51 | exact resolve eq51 eq226811 | grind only

private theorem step_1_eq229347 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq6438 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1) (eq226829 : c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq6438 eq226829 | exact superpose eq226829 eq6438 | grind only

private theorem step_1_eq229930 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq229347 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0) : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq229347 rfl | grind only

private theorem step_1_eq230245 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq229930 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq229930 eq52 | exact resolve eq52 eq229930 | grind only

private theorem step_1_eq231681 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq224807 : (new a sk1 sk2) ∨ c = sk0 ∨ b = sk0) (eq230245 : b = sk1 ∨ c = sk0 ∨ b = sk0) : (new a b sk2) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 := by
  first | exact superpose eq224807 eq230245 | exact superpose eq230245 eq224807 | grind only

private theorem step_1_eq231686 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq231681 : (new a b sk2) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0) : (new a b sk2) ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq231681 rfl | grind only

private theorem step_1_eq232992 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq231686 : (new a b sk2) ∨ c = sk0 ∨ b = sk0) (eq195 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) : c = sk0 ∨ b = sk0 ∨ (old a b sk2) ∨ c = sk2 ∨ b = c ∨ a = c := by
  first | exact resolve eq231686 eq195 | exact resolve eq195 eq231686 | grind only

private theorem step_1_eq233043 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq232992 : c = sk0 ∨ b = sk0 ∨ (old a b sk2) ∨ c = sk2 ∨ b = c ∨ a = c) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : c = sk0 ∨ b = sk0 ∨ c = sk2 ∨ b = c ∨ a = c := by
  first | exact resolve eq232992 eq51 | exact resolve eq51 eq232992 | grind only

private theorem step_1_eq233051 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq233043 : c = sk0 ∨ b = sk0 ∨ c = sk2 ∨ b = c ∨ a = c) (eq50 : b ≠ c) : c = sk0 ∨ b = sk0 ∨ c = sk2 ∨ a = c := by
  first | exact resolve eq233043 eq50 | exact resolve eq50 eq233043 | grind only

private theorem step_1_eq233053 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq233051 : c = sk0 ∨ b = sk0 ∨ c = sk2 ∨ a = c) (eq49 : a ≠ c) : c = sk2 ∨ b = sk0 ∨ c = sk0 := by
  first | exact resolve eq233051 eq49 | exact resolve eq49 eq233051 | grind only

private theorem step_1_eq233881 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq226836 : (old sk2 a sk3) ∨ c = sk0 ∨ b = sk0) (eq233053 : c = sk2 ∨ b = sk0 ∨ c = sk0) : (old c a sk3) ∨ c = sk0 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 := by
  first | exact superpose eq226836 eq233053 | exact superpose eq233053 eq226836 | grind only

private theorem step_1_eq233886 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq233881 : (old c a sk3) ∨ c = sk0 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0) : (old c a sk3) ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq233881 rfl | grind only

private theorem step_1_eq235715 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq233886 : (old c a sk3) ∨ c = sk0 ∨ b = sk0) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : c = sk0 ∨ b = sk0 ∨ a = c := by
  first | exact resolve eq233886 eq57 | exact resolve eq57 eq233886 | grind only

private theorem step_1_eq235873 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} (eq235715 : c = sk0 ∨ b = sk0 ∨ a = c) (eq49 : a ≠ c) : c = sk0 ∨ b = sk0 := by
  first | exact resolve eq235715 eq49 | exact resolve eq49 eq235715 | grind only

private theorem step_1_eq235875 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq92 : (new sk0 sk1 sk2)) (eq235873 : c = sk0 ∨ b = sk0) : (new c sk1 sk2) ∨ b = sk0 := by
  first | exact superpose eq92 eq235873 | exact superpose eq235873 eq92 | grind only

private theorem step_1_eq235876 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq93 : (new sk2 sk0 sk3)) (eq235873 : c = sk0 ∨ b = sk0) : (new sk2 c sk3) ∨ b = sk0 := by
  first | exact superpose eq93 eq235873 | exact superpose eq235873 eq93 | grind only

private theorem step_1_eq235878 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq115 : ¬(old sk0 sk4 sk1)) (eq235873 : c = sk0 ∨ b = sk0) : ¬(old c sk4 sk1) ∨ b = sk0 := by
  first | exact superpose eq115 eq235873 | exact superpose eq235873 eq115 | grind only

private theorem step_1_eq235885 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq274 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 ∨ c = sk1) (eq235873 : c = sk0 ∨ b = sk0) : (old c sk1 sk2) ∨ a = c ∨ a = sk2 ∨ c = sk1 ∨ b = sk0 := by
  first | exact superpose eq274 eq235873 | exact superpose eq235873 eq274 | grind only

private theorem step_1_eq235912 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq428 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1) (eq235873 : c = sk0 ∨ b = sk0) : (old c sk1 sk2) ∨ a = c ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk0 := by
  first | exact superpose eq428 eq235873 | exact superpose eq235873 eq428 | grind only

private theorem step_1_eq237447 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq235912 : (old c sk1 sk2) ∨ a = c ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk0) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq235912 eq57 | exact resolve eq57 eq235912 | grind only

private theorem step_1_eq237461 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq235885 : (old c sk1 sk2) ∨ a = c ∨ a = sk2 ∨ c = sk1 ∨ b = sk0) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ a = sk2 ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq235885 eq57 | exact resolve eq57 eq235885 | grind only

private theorem step_1_eq237583 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq237447 : a = c ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk0) (eq49 : a ≠ c) : (old b sk1 a) ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq237447 eq49 | exact resolve eq49 eq237447 | grind only

private theorem step_1_eq237585 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq237461 : a = c ∨ a = sk2 ∨ c = sk1 ∨ b = sk0) (eq49 : a ≠ c) : a = sk2 ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq237461 eq49 | exact resolve eq49 eq237461 | grind only

private theorem step_1_eq237611 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq235875 : (new c sk1 sk2) ∨ b = sk0) (eq180 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) ∨ c = X1) : b = sk0 ∨ (old c sk1 sk2) ∨ a = c ∨ (old sk1 b b) ∨ c = sk1 := by
  first | exact resolve eq235875 eq180 | exact resolve eq180 eq235875 | grind only

private theorem step_1_eq237682 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq237611 : b = sk0 ∨ (old c sk1 sk2) ∨ a = c ∨ (old sk1 b b) ∨ c = sk1) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : b = sk0 ∨ a = c ∨ (old sk1 b b) ∨ c = sk1 := by
  first | exact resolve eq237611 eq57 | exact resolve eq57 eq237611 | grind only

private theorem step_1_eq237691 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq237682 : b = sk0 ∨ a = c ∨ (old sk1 b b) ∨ c = sk1) (eq49 : a ≠ c) : (old sk1 b b) ∨ b = sk0 ∨ c = sk1 := by
  first | exact resolve eq237682 eq49 | exact resolve eq49 eq237682 | grind only

private theorem step_1_eq240100 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq235876 : (new sk2 c sk3) ∨ b = sk0) (eq237585 : a = sk2 ∨ c = sk1 ∨ b = sk0) : (new a c sk3) ∨ b = sk0 ∨ c = sk1 ∨ b = sk0 := by
  first | exact superpose eq235876 eq237585 | exact superpose eq237585 eq235876 | grind only

private theorem step_1_eq240101 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq240100 : (new a c sk3) ∨ b = sk0 ∨ c = sk1 ∨ b = sk0) : (new a c sk3) ∨ b = sk0 ∨ c = sk1 := by
  first | exact resolve eq240100 rfl | grind only

private theorem step_1_eq243500 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq237691 : (old sk1 b b) ∨ b = sk0 ∨ c = sk1) (eq61 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ (old X1 X2 X0)) : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk0 ∨ (old b X0 sk1) := by
  intro X0
  first | exact resolve eq237691 eq61 | exact resolve eq61 eq237691 | grind only

private theorem step_1_eq244180 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq240101 : (new a c sk3) ∨ b = sk0 ∨ c = sk1) (eq662 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2))) : b = sk0 ∨ c = sk1 ∨ (old a c sk3) ∨ b = c ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3)) := by
  first | exact resolve eq240101 eq662 | exact resolve eq662 eq240101 | grind only

private theorem step_1_eq244235 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq244180 : b = sk0 ∨ c = sk1 ∨ (old a c sk3) ∨ b = c ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3))) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = sk0 ∨ c = sk1 ∨ b = c ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3)) := by
  first | exact resolve eq244180 eq55 | exact resolve eq55 eq244180 | grind only

private theorem step_1_eq244251 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq244235 : b = sk0 ∨ c = sk1 ∨ b = c ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3))) (eq50 : b ≠ c) : b = sk0 ∨ c = sk1 ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3)) := by
  first | exact resolve eq244235 eq50 | exact resolve eq50 eq244235 | grind only

private theorem step_1_eq244259 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq244251 : b = sk0 ∨ c = sk1 ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3))) (eq49 : a ≠ c) : b = sk0 ∨ c = sk1 ∨ (old b a a) ∨ (old a b (sF0 a c sk3)) := by
  first | exact resolve eq244251 eq49 | exact resolve eq49 eq244251 | grind only

private theorem step_1_eq244263 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk3 : G} (eq244259 : b = sk0 ∨ c = sk1 ∨ (old b a a) ∨ (old a b (sF0 a c sk3))) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : (old b a a) ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq244259 eq51 | exact resolve eq51 eq244259 | grind only

private theorem step_1_eq247039 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq244263 : (old b a a) ∨ c = sk1 ∨ b = sk0) (eq58 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) : ∀ (X0 : G), ¬(old b a X0) ∨ b = sk0 ∨ c = sk1 ∨ a = X0 := by
  intro X0
  first | exact resolve eq244263 eq58 | exact resolve eq58 eq244263 | grind only

private theorem step_1_eq257022 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq243500 : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk0 ∨ (old b X0 sk1)) (eq237583 : (old b sk1 a) ∨ c = sk1 ∨ b = sk0) : c = sk1 ∨ b = sk0 ∨ (old b a sk1) ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq243500 eq237583 | exact resolve eq237583 eq243500 | grind only

private theorem step_1_eq257041 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq257022 : c = sk1 ∨ b = sk0 ∨ (old b a sk1) ∨ c = sk1 ∨ b = sk0) : (old b a sk1) ∨ b = sk0 ∨ c = sk1 := by
  first | exact resolve eq257022 rfl | grind only

private theorem step_1_eq257483 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq257041 : (old b a sk1) ∨ b = sk0 ∨ c = sk1) (eq247039 : ∀ (X0 : G), ¬(old b a X0) ∨ b = sk0 ∨ c = sk1 ∨ a = X0) : b = sk0 ∨ c = sk1 ∨ b = sk0 ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq257041 eq247039 | exact resolve eq247039 eq257041 | grind only

private theorem step_1_eq257686 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} (eq257483 : b = sk0 ∨ c = sk1 ∨ b = sk0 ∨ c = sk1 ∨ a = sk1) : a = sk1 ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq257483 rfl | grind only

private theorem step_1_eq259783 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq237691 : (old sk1 b b) ∨ b = sk0 ∨ c = sk1) (eq257686 : a = sk1 ∨ c = sk1 ∨ b = sk0) : (old a b b) ∨ b = sk0 ∨ a = c ∨ c = sk1 ∨ b = sk0 := by
  first | exact superpose eq237691 eq257686 | exact superpose eq257686 eq237691 | grind only

private theorem step_1_eq259895 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq259783 : (old a b b) ∨ b = sk0 ∨ a = c ∨ c = sk1 ∨ b = sk0) : (old a b b) ∨ b = sk0 ∨ a = c ∨ c = sk1 := by
  first | exact resolve eq259783 rfl | grind only

private theorem step_1_eq260395 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq259895 : (old a b b) ∨ b = sk0 ∨ a = c ∨ c = sk1) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : b = sk0 ∨ a = c ∨ c = sk1 := by
  first | exact resolve eq259895 eq51 | exact resolve eq51 eq259895 | grind only

private theorem step_1_eq260492 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} (eq260395 : b = sk0 ∨ a = c ∨ c = sk1) (eq49 : a ≠ c) : c = sk1 ∨ b = sk0 := by
  first | exact resolve eq260395 eq49 | exact resolve eq49 eq260395 | grind only

private theorem step_1_eq260635 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq94 : (new sk3 sk1 sk4)) (eq260492 : c = sk1 ∨ b = sk0) : (new sk3 c sk4) ∨ b = sk0 := by
  first | exact superpose eq94 eq260492 | exact superpose eq260492 eq94 | grind only

private theorem step_1_eq261599 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq235875 : (new c sk1 sk2) ∨ b = sk0) (eq260492 : c = sk1 ∨ b = sk0) : (new c c sk2) ∨ b = sk0 ∨ b = sk0 := by
  first | exact superpose eq235875 eq260492 | exact superpose eq260492 eq235875 | grind only

private theorem step_1_eq261601 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq235878 : ¬(old c sk4 sk1) ∨ b = sk0) (eq260492 : c = sk1 ∨ b = sk0) : ¬(old c sk4 c) ∨ b = sk0 ∨ b = sk0 := by
  first | exact superpose eq235878 eq260492 | exact superpose eq260492 eq235878 | grind only

private theorem step_1_eq261686 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq261601 : ¬(old c sk4 c) ∨ b = sk0 ∨ b = sk0) : ¬(old c sk4 c) ∨ b = sk0 := by
  first | exact resolve eq261601 rfl | grind only

private theorem step_1_eq261688 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq261599 : (new c c sk2) ∨ b = sk0 ∨ b = sk0) : (new c c sk2) ∨ b = sk0 := by
  first | exact resolve eq261599 rfl | grind only

private theorem step_1_eq263479 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk2 : G} (eq261688 : (new c c sk2) ∨ b = sk0) (eq185 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a)) : b = sk0 ∨ (old c c sk2) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk2) c a) := by
  first | exact resolve eq261688 eq185 | exact resolve eq185 eq261688 | grind only

private theorem step_1_eq263544 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk2 : G} (eq263479 : b = sk0 ∨ (old c c sk2) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk2) c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk0 ∨ (old c c sk2) ∨ a = c ∨ (old (sF0 c c sk2) c a) := by
  first | exact resolve eq263479 eq54 | exact resolve eq54 eq263479 | grind only

private theorem step_1_eq263560 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk2 : G} (eq263544 : b = sk0 ∨ (old c c sk2) ∨ a = c ∨ (old (sF0 c c sk2) c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk0 ∨ (old c c sk2) ∨ a = c := by
  first | exact resolve eq263544 eq54 | exact resolve eq54 eq263544 | grind only

private theorem step_1_eq263565 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq263560 : b = sk0 ∨ (old c c sk2) ∨ a = c) (eq49 : a ≠ c) : (old c c sk2) ∨ b = sk0 := by
  first | exact resolve eq263560 eq49 | exact resolve eq49 eq263560 | grind only

private theorem step_1_eq263742 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq263565 : (old c c sk2) ∨ b = sk0) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk2 ∨ b = sk0 := by
  first | exact resolve eq263565 eq56 | exact resolve eq56 eq263565 | grind only

private theorem step_1_eq264768 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq235876 : (new sk2 c sk3) ∨ b = sk0) (eq263742 : c = sk2 ∨ b = sk0) : (new c c sk3) ∨ b = sk0 ∨ b = sk0 := by
  first | exact superpose eq235876 eq263742 | exact superpose eq263742 eq235876 | grind only

private theorem step_1_eq264805 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq264768 : (new c c sk3) ∨ b = sk0 ∨ b = sk0) : (new c c sk3) ∨ b = sk0 := by
  first | exact resolve eq264768 rfl | grind only

private theorem step_1_eq267061 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk3 : G} (eq264805 : (new c c sk3) ∨ b = sk0) (eq185 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a)) : b = sk0 ∨ (old c c sk3) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk3) c a) := by
  first | exact resolve eq264805 eq185 | exact resolve eq185 eq264805 | grind only

private theorem step_1_eq267144 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk3 : G} (eq267061 : b = sk0 ∨ (old c c sk3) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk3) c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk0 ∨ (old c c sk3) ∨ a = c ∨ (old (sF0 c c sk3) c a) := by
  first | exact resolve eq267061 eq54 | exact resolve eq54 eq267061 | grind only

private theorem step_1_eq267160 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk3 : G} (eq267144 : b = sk0 ∨ (old c c sk3) ∨ a = c ∨ (old (sF0 c c sk3) c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk0 ∨ (old c c sk3) ∨ a = c := by
  first | exact resolve eq267144 eq54 | exact resolve eq54 eq267144 | grind only

private theorem step_1_eq267165 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq267160 : b = sk0 ∨ (old c c sk3) ∨ a = c) (eq49 : a ≠ c) : (old c c sk3) ∨ b = sk0 := by
  first | exact resolve eq267160 eq49 | exact resolve eq49 eq267160 | grind only

private theorem step_1_eq268947 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq267165 : (old c c sk3) ∨ b = sk0) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk3 ∨ b = sk0 := by
  first | exact resolve eq267165 eq56 | exact resolve eq56 eq267165 | grind only

private theorem step_1_eq270024 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk3 : G} {sk4 : G} (eq260635 : (new sk3 c sk4) ∨ b = sk0) (eq268947 : c = sk3 ∨ b = sk0) : (new c c sk4) ∨ b = sk0 ∨ b = sk0 := by
  first | exact superpose eq260635 eq268947 | exact superpose eq268947 eq260635 | grind only

private theorem step_1_eq270031 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq270024 : (new c c sk4) ∨ b = sk0 ∨ b = sk0) : (new c c sk4) ∨ b = sk0 := by
  first | exact resolve eq270024 rfl | grind only

private theorem step_1_eq272177 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk4 : G} (eq270031 : (new c c sk4) ∨ b = sk0) (eq185 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a)) : b = sk0 ∨ (old c c sk4) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk4) c a) := by
  first | exact resolve eq270031 eq185 | exact resolve eq185 eq270031 | grind only

private theorem step_1_eq272299 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk4 : G} (eq272177 : b = sk0 ∨ (old c c sk4) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk4) c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk0 ∨ (old c c sk4) ∨ a = c ∨ (old (sF0 c c sk4) c a) := by
  first | exact resolve eq272177 eq54 | exact resolve eq54 eq272177 | grind only

private theorem step_1_eq272315 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk4 : G} (eq272299 : b = sk0 ∨ (old c c sk4) ∨ a = c ∨ (old (sF0 c c sk4) c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk0 ∨ (old c c sk4) ∨ a = c := by
  first | exact resolve eq272299 eq54 | exact resolve eq54 eq272299 | grind only

private theorem step_1_eq272320 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq272315 : b = sk0 ∨ (old c c sk4) ∨ a = c) (eq49 : a ≠ c) : (old c c sk4) ∨ b = sk0 := by
  first | exact resolve eq272315 eq49 | exact resolve eq49 eq272315 | grind only

private theorem step_1_eq273537 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq272320 : (old c c sk4) ∨ b = sk0) (eq118 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ (old X0 X1 X0)) : b = sk0 ∨ (old c sk4 c) := by
  first | exact resolve eq272320 eq118 | exact resolve eq118 eq272320 | grind only

private theorem step_1_eq273609 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq273537 : b = sk0 ∨ (old c sk4 c)) (eq261686 : ¬(old c sk4 c) ∨ b = sk0) : b = sk0 := by
  first | exact resolve eq273537 eq261686 | exact resolve eq261686 eq273537 | grind only

private theorem step_1_eq273790 {G : Type*} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq115 : ¬(old sk0 sk4 sk1)) (eq273609 : b = sk0) : ¬(old b sk4 sk1) := by
  first | exact superpose eq115 eq273609 | exact superpose eq273609 eq115 | grind only

private theorem step_1_eq273791 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq156 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2) (eq273609 : b = sk0) : (old b sk1 sk2) ∨ a = b ∨ b = c ∨ b = sk2 := by
  first | exact superpose eq156 eq273609 | exact superpose eq273609 eq156 | grind only

private theorem step_1_eq273801 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq248 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1) (eq273609 : b = sk0) : (old b sk1 sk2) ∨ a = b ∨ b = c ∨ c = sk1 := by
  first | exact superpose eq248 eq273609 | exact superpose eq273609 eq248 | grind only

private theorem step_1_eq274519 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq21262 : (old b sk0 a) ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ a = sk0) (eq273609 : b = sk0) : (old b b a) ∨ c = sk4 ∨ c = sk1 ∨ b = c ∨ c = sk3 ∨ a = b := by
  first | exact superpose eq21262 eq273609 | exact superpose eq273609 eq21262 | grind only

private theorem step_1_eq275513 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq274519 : (old b b a) ∨ c = sk4 ∨ c = sk1 ∨ b = c ∨ c = sk3 ∨ a = b) (eq116 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : c = sk4 ∨ c = sk1 ∨ b = c ∨ c = sk3 ∨ a = b := by
  first | exact resolve eq274519 eq116 | exact resolve eq116 eq274519 | grind only

private theorem step_1_eq275838 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq273801 : (old b sk1 sk2) ∨ a = b ∨ b = c ∨ c = sk1) (eq47 : a ≠ b) : (old b sk1 sk2) ∨ b = c ∨ c = sk1 := by
  first | exact resolve eq273801 eq47 | exact resolve eq47 eq273801 | grind only

private theorem step_1_eq275844 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq273791 : (old b sk1 sk2) ∨ a = b ∨ b = c ∨ b = sk2) (eq47 : a ≠ b) : (old b sk1 sk2) ∨ b = c ∨ b = sk2 := by
  first | exact resolve eq273791 eq47 | exact resolve eq47 eq273791 | grind only

private theorem step_1_eq275933 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq275513 : c = sk4 ∨ c = sk1 ∨ b = c ∨ c = sk3 ∨ a = b) (eq50 : b ≠ c) : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ a = b := by
  first | exact resolve eq275513 eq50 | exact resolve eq50 eq275513 | grind only

private theorem step_1_eq276015 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq275838 : (old b sk1 sk2) ∨ b = c ∨ c = sk1) (eq50 : b ≠ c) : (old b sk1 sk2) ∨ c = sk1 := by
  first | exact resolve eq275838 eq50 | exact resolve eq50 eq275838 | grind only

private theorem step_1_eq276021 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq275844 : (old b sk1 sk2) ∨ b = c ∨ b = sk2) (eq50 : b ≠ c) : (old b sk1 sk2) ∨ b = sk2 := by
  first | exact resolve eq275844 eq50 | exact resolve eq50 eq275844 | grind only

private theorem step_1_eq276032 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk3 : G} {sk4 : G} (eq275933 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ a = b) (eq47 : a ≠ b) : c = sk4 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq275933 eq47 | exact resolve eq47 eq275933 | grind only

private theorem step_1_eq276612 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq273790 : ¬(old b sk4 sk1)) (eq5369 : a = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : ¬(old b a sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq273790 eq5369 | exact superpose eq5369 eq273790 | grind only

private theorem step_1_eq276670 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq276612 : ¬(old b a sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq30404 : (old b a sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1) : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq276612 eq30404 | exact resolve eq30404 eq276612 | grind only

private theorem step_1_eq276686 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq276670 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq273609 : b = sk0) : b = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk2 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq276670 | grind only

private theorem step_1_eq276701 {G : Type*} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq276686 : b = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk2) (eq50 : b ≠ c) : c = sk2 ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq276686 eq50 | exact resolve eq50 eq276686 | grind only

private theorem step_1_eq279699 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk4 : G} (eq250 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1) (eq276032 : c = sk4 ∨ c = sk1 ∨ c = sk3) : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk1 ∨ c = sk3 := by
  first | exact superpose eq250 eq276032 | exact superpose eq276032 eq250 | grind only

private theorem step_1_eq280031 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq279699 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk1 ∨ c = sk3) : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq279699 rfl | grind only

private theorem step_1_eq280152 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq280031 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : a = sk3 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq280031 eq52 | exact resolve eq52 eq280031 | grind only

private theorem step_1_eq281061 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq276015 : (old b sk1 sk2) ∨ c = sk1) (eq276701 : c = sk2 ∨ b = sk1 ∨ c = sk1) : (old b sk1 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq276015 eq276701 | exact superpose eq276701 eq276015 | grind only

private theorem step_1_eq281064 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq281061 : (old b sk1 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1) : (old b sk1 c) ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq281061 rfl | grind only

private theorem step_1_eq281329 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq281064 : (old b sk1 c) ∨ c = sk1 ∨ b = sk1) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk1 ∨ b = sk1 := by
  first | exact resolve eq281064 eq52 | exact resolve eq52 eq281064 | grind only

private theorem step_1_eq282449 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq544 : (old (sF0 sk0 sk1 sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2)) (eq281329 : c = sk1 ∨ b = sk1) : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 := by
  first | exact superpose eq544 eq281329 | exact superpose eq281329 eq544 | grind only

private theorem step_1_eq282451 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq557 : (old sk0 b (sF0 sk0 sk1 sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2)) (eq281329 : c = sk1 ∨ b = sk1) : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 := by
  first | exact superpose eq557 eq281329 | exact superpose eq281329 eq557 | grind only

private theorem step_1_eq283906 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq282451 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq282451 eq55 | exact resolve eq55 eq282451 | grind only

private theorem step_1_eq283908 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq282449 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq282449 eq55 | exact resolve eq55 eq282449 | grind only

private theorem step_1_eq284290 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq283906 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1) (eq273609 : b = sk0) : (old b b (sF0 b c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq283906 | grind only

private theorem step_1_eq284291 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq283908 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1) (eq273609 : b = sk0) : (old (sF0 b c sk2) b a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq283908 | grind only

private theorem step_1_eq284541 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq284290 : (old b b (sF0 b c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1) (eq273609 : b = sk0) : a = b ∨ (old b b (sF0 b c sk2)) ∨ c = sk0 ∨ b = sk1 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq284290 | grind only

private theorem step_1_eq284542 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq284291 : (old (sF0 b c sk2) b a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1) (eq273609 : b = sk0) : a = b ∨ (old (sF0 b c sk2) b a) ∨ c = sk0 ∨ b = sk1 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq284291 | grind only

private theorem step_1_eq284707 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq284541 : a = b ∨ (old b b (sF0 b c sk2)) ∨ c = sk0 ∨ b = sk1) (eq47 : a ≠ b) : (old b b (sF0 b c sk2)) ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq284541 eq47 | exact resolve eq47 eq284541 | grind only

private theorem step_1_eq284708 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq284542 : a = b ∨ (old (sF0 b c sk2) b a) ∨ c = sk0 ∨ b = sk1) (eq47 : a ≠ b) : (old (sF0 b c sk2) b a) ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq284542 eq47 | exact resolve eq47 eq284542 | grind only

private theorem step_1_eq284794 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq284707 : (old b b (sF0 b c sk2)) ∨ c = sk0 ∨ b = sk1) (eq273609 : b = sk0) : b = c ∨ (old b b (sF0 b c sk2)) ∨ b = sk1 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq284707 | grind only

private theorem step_1_eq284795 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk0 : G} {sk1 : G} {sk2 : G} (eq284708 : (old (sF0 b c sk2) b a) ∨ c = sk0 ∨ b = sk1) (eq273609 : b = sk0) : b = c ∨ (old (sF0 b c sk2) b a) ∨ b = sk1 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq284708 | grind only

private theorem step_1_eq284822 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq284794 : b = c ∨ (old b b (sF0 b c sk2)) ∨ b = sk1) (eq50 : b ≠ c) : (old b b (sF0 b c sk2)) ∨ b = sk1 := by
  first | exact resolve eq284794 eq50 | exact resolve eq50 eq284794 | grind only

private theorem step_1_eq284823 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq284795 : b = c ∨ (old (sF0 b c sk2) b a) ∨ b = sk1) (eq50 : b ≠ c) : (old (sF0 b c sk2) b a) ∨ b = sk1 := by
  first | exact resolve eq284795 eq50 | exact resolve eq50 eq284795 | grind only

private theorem step_1_eq299556 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq284822 : (old b b (sF0 b c sk2)) ∨ b = sk1) (eq116 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : b = (sF0 b c sk2) ∨ b = sk1 := by
  first | exact resolve eq284822 eq116 | exact resolve eq116 eq284822 | grind only

private theorem step_1_eq299614 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq284823 : (old (sF0 b c sk2) b a) ∨ b = sk1) (eq299556 : b = (sF0 b c sk2) ∨ b = sk1) : (old b b a) ∨ b = sk1 ∨ b = sk1 := by
  first | exact superpose eq284823 eq299556 | exact superpose eq299556 eq284823 | grind only

private theorem step_1_eq299615 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk1 : G} (eq299614 : (old b b a) ∨ b = sk1 ∨ b = sk1) : (old b b a) ∨ b = sk1 := by
  first | exact resolve eq299614 rfl | grind only

private theorem step_1_eq299627 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk1 : G} (eq299615 : (old b b a) ∨ b = sk1) (eq116 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : b = sk1 ∨ a = b := by
  first | exact resolve eq299615 eq116 | exact resolve eq116 eq299615 | grind only

private theorem step_1_eq299635 {G : Type*} {a : G} {b : G} {sk1 : G} (eq299627 : b = sk1 ∨ a = b) (eq47 : a ≠ b) : b = sk1 := by
  first | exact resolve eq299627 eq47 | exact resolve eq47 eq299627 | grind only

private theorem step_1_eq300834 {G : Type*} {b : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq276021 : (old b sk1 sk2) ∨ b = sk2) (eq299635 : b = sk1) : (old b b sk2) ∨ b = sk2 := by
  first | exact superpose eq276021 eq299635 | exact superpose eq299635 eq276021 | grind only

private theorem step_1_eq300854 {G : Type*} {b : G} {old : G → G → G → Prop} {sk2 : G} (eq300834 : (old b b sk2) ∨ b = sk2) (eq116 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : b = sk2 := by
  first | exact resolve eq300834 eq116 | exact resolve eq116 eq300834 | grind only

private theorem step_1_eq302642 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq157 : (old sk2 sk0 sk3) ∨ a = sk2 ∨ c = sk2 ∨ b = sk3) (eq300854 : b = sk2) : (old b sk0 sk3) ∨ a = b ∨ b = c ∨ b = sk3 := by
  first | exact superpose eq157 eq300854 | exact superpose eq300854 eq157 | grind only

private theorem step_1_eq304464 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq302642 : (old b sk0 sk3) ∨ a = b ∨ b = c ∨ b = sk3) (eq47 : a ≠ b) : (old b sk0 sk3) ∨ b = c ∨ b = sk3 := by
  first | exact resolve eq302642 eq47 | exact resolve eq47 eq302642 | grind only

private theorem step_1_eq305027 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq304464 : (old b sk0 sk3) ∨ b = c ∨ b = sk3) (eq50 : b ≠ c) : (old b sk0 sk3) ∨ b = sk3 := by
  first | exact resolve eq304464 eq50 | exact resolve eq50 eq304464 | grind only

private theorem step_1_eq305476 {G : Type*} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq305027 : (old b sk0 sk3) ∨ b = sk3) (eq273609 : b = sk0) : (old b b sk3) ∨ b = sk3 := by
  first | simpa only [eq273609, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq305027 | grind only

private theorem step_1_eq305789 {G : Type*} {b : G} {old : G → G → G → Prop} {sk3 : G} (eq305476 : (old b b sk3) ∨ b = sk3) (eq116 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : b = sk3 := by
  first | exact resolve eq305476 eq116 | exact resolve eq116 eq305476 | grind only

private theorem step_1_eq307247 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk3 : G} (eq280152 : a = sk3 ∨ c = sk3 ∨ c = sk1) (eq305789 : b = sk3) : a = b ∨ b = c ∨ c = sk1 := by
  first | exact superpose eq280152 eq305789 | exact superpose eq305789 eq280152 | grind only

private theorem step_1_eq307256 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} (eq307247 : a = b ∨ b = c ∨ c = sk1) (eq47 : a ≠ b) : b = c ∨ c = sk1 := by
  first | exact resolve eq307247 eq47 | exact resolve eq47 eq307247 | grind only

private theorem step_1_eq307723 {G : Type*} {b : G} {c : G} {sk1 : G} (eq307256 : b = c ∨ c = sk1) (eq50 : b ≠ c) : c = sk1 := by
  first | exact resolve eq307256 eq50 | exact resolve eq50 eq307256 | grind only

private theorem step_1_eq308169 {G : Type*} {b : G} {c : G} {sk1 : G} (eq307723 : c = sk1) (eq299635 : b = sk1) : b = c := by
  first | simpa only [eq299635, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq307723 | grind only

set_option maxHeartbeats 2000000 in
private theorem preserve_1 (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (ab : a ≠ b) (diagonal : ∀ x, old x x x) (ac : a ≠ c) (bc : b ≠ c) (p3 : ∀ z, ¬ old a b z) (p4XY : ∀ x y, old x y c → x = c ∧ y = c) (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) (new_new : new a b c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X2 X0 X3 ∨ ¬ old X3 X1 X4 ∨ old X0 X4 X1)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ old X1 X2 X0)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X0 ∨ ¬ old X3 X1 X2 ∨ ¬ old X3 X2 X2 ∨ old X2 X3 X0)) (old_5 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X1 X0 X3 ∨ ¬ old X2 X0 X4 ∨ ¬ old X3 X1 X5 ∨ ¬ old X5 X3 X4 ∨ old X4 X1 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ b ≠ Z ∨ ¬ old X b X2 ∨ ¬ old X2 X a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b a a ∨ ¬ sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X2 X0 X3 ∨ ¬ new X3 X1 X4 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq47 : a ≠ b := step_1_eq47 ab
  have eq48 (X0 : G) : (old X0 X0 X0) := step_1_eq48 diagonal X0
  have eq49 : a ≠ c := step_1_eq49 ac
  have eq50 : b ≠ c := step_1_eq50 bc
  have eq51 (X0 : G) : ¬(old a b X0) := step_1_eq51 p3 X0
  have eq52 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X1 := step_1_eq52 p4XY X0 X1
  have eq53 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X0 := step_1_eq53 p4XY X0 X1
  have eq54 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X1 := step_1_eq54 p4XZ X0 X1
  have eq55 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X0 := step_1_eq55 p4XZ X0 X1
  have eq56 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X1 := step_1_eq56 p4YZ X0 X1
  have eq57 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X0 := step_1_eq57 p4YZ X0 X1
  have eq58 (X0 X1 X2 X3 : G) : ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := step_1_eq58 old_0 X0 X1 X2 X3
  have eq59 (X0 X1 X2 X3 X4 : G) : ¬(old X3 X1 X4) ∨ ¬(old X2 X0 X3) ∨ ¬(old X0 X1 X2) ∨ (old X0 X4 X1) := step_1_eq59 old_1 X0 X1 X2 X3 X4
  have eq61 (X0 X1 X2 : G) : ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ (old X1 X2 X0) := step_1_eq61 old_3 X0 X1 X2
  have eq62 (X0 X1 X2 X3 : G) : ¬(old X3 X2 X2) ∨ ¬(old X1 X3 X0) ∨ ¬(old X3 X1 X2) ∨ ¬(old X0 X1 X2) ∨ (old X2 X3 X0) := step_1_eq62 old_4 X0 X1 X2 X3
  have eq63 (X0 X1 X2 X3 X4 X5 : G) : ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2) := step_1_eq63 old_5 X0 X1 X2 X3 X4 X5
  have eq64 (X0 X1 X2 : G) : (new X0 X1 X2) ∨ ¬(old X0 X1 X2) := step_1_eq64 imp_new_0 X0 X1 X2
  have eq66 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ a = X0 := step_1_eq66 rule_def_0_0 X0 X1 X2
  have eq67 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ b = X1 := step_1_eq67 rule_def_0_1 X0 X1 X2
  have eq68 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ c = X2 := step_1_eq68 rule_def_0_2 X0 X1 X2
  have eq69 (X0 X1 X2 X3 : G) : c ≠ X1 ∨ b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X3 X0 a) ∨ (new X0 X1 X2) := step_1_eq69 imp_new_2 X0 X1 X2 X3
  have eq70 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ c = X1 := step_1_eq70 rule_def_1_0 X0 X1 X2
  have eq71 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ b = X2 := step_1_eq71 rule_def_1_1 X0 X1 X2
  have eq72 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (old X0 b (sF0 X0 X1 X2)) := step_1_eq72 rule_def_1_2 X0 X1 X2
  have eq73 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a) := step_1_eq73 rule_def_1_3 X0 X1 X2
  have eq75 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ c = X0 := step_1_eq75 rule_def_2_0 X0 X1 X2
  have eq76 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = X2 := step_1_eq76 rule_def_2_1 X0 X1 X2
  have eq77 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := step_1_eq77 rule_def_2_2 X0 X1 X2
  have eq78 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := step_1_eq78 rule_def_2_3 X0 X1 X2
  have eq80 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = X0 := step_1_eq80 rule_def_3_0 X0 X1 X2
  have eq81 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ c = X1 := step_1_eq81 rule_def_3_1 X0 X1 X2
  have eq82 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ b = X2 := step_1_eq82 rule_def_3_2 X0 X1 X2
  have eq83 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ (old b a a) := step_1_eq83 rule_def_3_3 X0 X1 X2
  have eq85 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ c = X0 := step_1_eq85 rule_def_4_0 X0 X1 X2
  have eq86 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = X2 := step_1_eq86 rule_def_4_1 X0 X1 X2
  have eq87 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := step_1_eq87 rule_def_4_2 X0 X1 X2
  have eq88 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := step_1_eq88 rule_def_4_3 X0 X1 X2
  have eq90 : (new a b c) := step_1_eq90 new_new
  have eq91 (X0 X1 X2 : G) : (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := step_1_eq91 new_imp X0 X1 X2
  have eq92 : (new sk0 sk1 sk2) := step_1_eq92 preserve_0
  have eq93 : (new sk2 sk0 sk3) := step_1_eq93 preserve_1
  have eq94 : (new sk3 sk1 sk4) := step_1_eq94 preserve_2
  have eq95 : ¬(new sk0 sk4 sk1) := step_1_eq95 preserve_3
  have eq99 (X0 X2 X3 : G) : b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X3 X0 a) ∨ (new X0 c X2) := step_1_eq99 eq69 X0 X2 X3
  have eq100 (X0 X3 : G) : ¬(old X3 X0 a) ∨ ¬(old X0 b X3) ∨ (new X0 c b) := step_1_eq100 eq99 X0 X3
  have eq115 : ¬(old sk0 sk4 sk1) := step_1_eq115 eq64 eq95
  have eq116 (X0 X1 : G) : ¬(old X0 X0 X1) ∨ X0 = X1 := step_1_eq116 eq58 eq48 X0 X1
  have eq118 (X0 X1 : G) : ¬(old X0 X0 X1) ∨ (old X0 X1 X0) := step_1_eq118 eq61 eq48 X0 X1
  have eq129 (X0 X1 X2 : G) : (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 := step_1_eq129 eq91 eq68 X0 X1 X2
  have eq130 (X0 X1 X2 : G) : (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 := step_1_eq130 eq91 eq67 X0 X1 X2
  have eq131 (X0 X1 X2 : G) : (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := step_1_eq131 eq91 eq66 X0 X1 X2
  have eq132 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := step_1_eq132 eq131 eq80 X0 X1 X2
  have eq134 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := step_1_eq134 eq132 eq78 X0 X1 X2
  have eq135 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) := step_1_eq135 eq132 eq77 X0 X1 X2
  have eq136 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ a = X2 := step_1_eq136 eq132 eq76 X0 X1 X2
  have eq137 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ c = X0 := step_1_eq137 eq132 eq75 X0 X1 X2
  have eq138 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 := step_1_eq138 eq137 eq85 X0 X1 X2
  have eq139 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 := step_1_eq139 eq136 eq86 X0 X1 X2
  have eq140 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) := step_1_eq140 eq135 eq88 X0 X1 X2
  have eq141 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := step_1_eq141 eq134 eq87 X0 X1 X2
  have eq142 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old (sF0 X0 X1 X2) X0 a) := step_1_eq142 eq138 eq73 X0 X1 X2
  have eq143 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2)) := step_1_eq143 eq138 eq72 X0 X1 X2
  have eq144 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2 := step_1_eq144 eq138 eq71 X0 X1 X2
  have eq145 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1 := step_1_eq145 eq138 eq70 X0 X1 X2
  have eq148 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := step_1_eq148 eq129 eq81 X0 X1 X2
  have eq150 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := step_1_eq150 eq148 eq70 X0 X1 X2
  have eq156 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk2 := step_1_eq156 eq144 eq92
  have eq157 : (old sk2 sk0 sk3) ∨ a = sk2 ∨ c = sk2 ∨ b = sk3 := step_1_eq157 eq144 eq93
  have eq159 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ (old b a a) := step_1_eq159 eq130 eq83 X0 X1 X2
  have eq160 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := step_1_eq160 eq130 eq82 X0 X1 X2
  have eq161 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := step_1_eq161 eq130 eq81 X0 X1 X2
  have eq163 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := step_1_eq163 eq161 eq70 X0 X1 X2
  have eq164 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := step_1_eq164 eq160 eq71 X0 X1 X2
  have eq172 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1 := step_1_eq172 eq139 eq70 X0 X1 X2
  have eq180 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old X1 b b) ∨ c = X1 := step_1_eq180 eq140 eq70 X0 X1 X2
  have eq185 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a) := step_1_eq185 eq141 eq73 X0 X1 X2
  have eq188 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1 := step_1_eq188 eq141 eq70 X0 X1 X2
  have eq191 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ (old b X1 a) := step_1_eq191 eq150 eq78 X0 X1 X2
  have eq193 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := step_1_eq193 eq150 eq76 X0 X1 X2
  have eq194 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := step_1_eq194 eq150 eq75 X0 X1 X2
  have eq195 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := step_1_eq195 eq194 eq85 X0 X1 X2
  have eq196 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := step_1_eq196 eq193 eq86 X0 X1 X2
  have eq198 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ (old b X1 a) := step_1_eq198 eq191 eq87 X0 X1 X2
  have eq211 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := step_1_eq211 eq163 eq78 X0 X1 X2
  have eq212 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := step_1_eq212 eq163 eq77 X0 X1 X2
  have eq213 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := step_1_eq213 eq163 eq76 X0 X1 X2
  have eq214 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := step_1_eq214 eq163 eq75 X0 X1 X2
  have eq215 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := step_1_eq215 eq214 eq85 X0 X1 X2
  have eq216 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := step_1_eq216 eq213 eq86 X0 X1 X2
  have eq217 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := step_1_eq217 eq212 eq88 X0 X1 X2
  have eq218 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := step_1_eq218 eq211 eq87 X0 X1 X2
  have eq222 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := step_1_eq222 eq164 eq75 X0 X1 X2
  have eq223 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := step_1_eq223 eq222 eq85 X0 X1 X2
  have eq238 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 := step_1_eq238 eq159 eq75 X0 X1 X2
  have eq239 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 := step_1_eq239 eq238 eq85 X0 X1 X2
  have eq248 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := step_1_eq248 eq145 eq92
  have eq250 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 := step_1_eq250 eq145 eq94
  have eq274 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = sk2 ∨ c = sk1 := step_1_eq274 eq172 eq92
  have eq287 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_1_eq287 eq195 eq92
  have eq288 : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_1_eq288 eq195 eq93
  have eq289 : (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk3 := step_1_eq289 eq195 eq94
  have eq301 : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = sk3 := step_1_eq301 eq196 eq93
  have eq339 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_1_eq339 eq215 eq92
  have eq340 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_1_eq340 eq215 eq93
  have eq341 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 := step_1_eq341 eq215 eq94
  have eq353 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk3 := step_1_eq353 eq216 eq93
  have eq354 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 := step_1_eq354 eq216 eq94
  have eq365 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := step_1_eq365 eq223 eq92
  have eq367 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 ∨ c = sk3 := step_1_eq367 eq223 eq94
  have eq397 (X0 X1 : G) : ¬(old X0 X1 sk3) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1) := step_1_eq397 eq289 eq59 X0 X1
  have eq428 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1 := step_1_eq428 eq188 eq92
  have eq430 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ (old b sk1 a) ∨ c = sk1 := step_1_eq430 eq188 eq94
  have eq454 : (old sk2 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ (old b sk0 a) := step_1_eq454 eq198 eq93
  have eq493 : (old sk2 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ (old sk0 b b) := step_1_eq493 eq217 eq93
  have eq494 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) := step_1_eq494 eq217 eq94
  have eq507 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := step_1_eq507 eq218 eq94
  have eq544 : (old (sF0 sk0 sk1 sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2) := step_1_eq544 eq142 eq92
  have eq546 : (old (sF0 sk3 sk1 sk4) sk3 a) ∨ a = sk3 ∨ c = sk3 ∨ (old sk3 sk1 sk4) := step_1_eq546 eq142 eq94
  have eq557 : (old sk0 b (sF0 sk0 sk1 sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 sk1 sk2) := step_1_eq557 eq143 eq92
  have eq559 : (old sk3 b (sF0 sk3 sk1 sk4)) ∨ a = sk3 ∨ c = sk3 ∨ (old sk3 sk1 sk4) := step_1_eq559 eq143 eq94
  have eq662 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ (old b a a) ∨ c = X0 ∨ (old X0 b (sF0 X0 X1 X2)) := step_1_eq662 eq239 eq72 X0 X1 X2
  have eq756 (X0 X1 : G) : ¬(old X0 X1 sk3) ∨ (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old X1 sk1 X0) ∨ (old X1 sk4 sk1) := step_1_eq756 eq430 eq59 X0 X1
  have eq982 (X0 X1 X2 : G) : ¬(old X0 X1 sk3) ∨ c = sk3 ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X2 X1 a) ∨ ¬(old sk3 X0 (sF0 sk3 sk1 sk4)) ∨ ¬(old X1 X0 X2) ∨ (old a X0 X2) := step_1_eq982 eq546 eq63 X0 X1 X2
  have eq2164 : (old sk3 b (sF0 sk3 sk1 sk4)) ∨ b = sk1 ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 sk1 sk4) := step_1_eq2164 eq662 eq94
  have eq5009 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_1_eq5009 eq397 eq288
  have eq5022 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ (old b sk0 a) := step_1_eq5022 eq397 eq454
  have eq5037 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ (old b sk0 a) := step_1_eq5037 eq5022
  have eq5042 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ c = sk2 := step_1_eq5042 eq5009
  have eq5052 : ¬(old sk0 sk1 sk2) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ (old b sk0 a) := step_1_eq5052 eq5037 eq115
  have eq5061 : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ c = sk2 := step_1_eq5061 eq5042 eq287
  have eq5065 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5065 eq5061 eq115
  have eq5078 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5078 eq341 eq5065
  have eq5132 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_1_eq5132 eq5078
  have eq5145 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5145 eq5132 eq52
  have eq5172 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5172 eq340 eq5145
  have eq5175 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5175 eq354 eq5145
  have eq5197 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5197 eq494 eq5145
  have eq5199 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5199 eq507 eq5145
  have eq5296 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk0 ∨ c = sk2 := step_1_eq5296 eq5199
  have eq5298 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 b b) ∨ c = sk0 ∨ c = sk2 := step_1_eq5298 eq5197
  have eq5313 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ a = sk4 ∨ c = sk0 ∨ c = sk2 := step_1_eq5313 eq5175
  have eq5316 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 := step_1_eq5316 eq5172
  have eq5349 : (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5349 eq5296 eq57
  have eq5351 : (old sk1 b b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5351 eq5298 eq57
  have eq5369 : a = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq5369 eq5313 eq57
  have eq5371 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := step_1_eq5371 eq5316 eq52
  have eq5690 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := step_1_eq5690 eq339 eq5371
  have eq5833 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5833 eq5690
  have eq5882 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5882 eq5833 eq52
  have eq5923 : ¬(new sk0 sk4 c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5923 eq95 eq5882
  have eq5942 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5942 eq365 eq5882
  have eq5943 : (old sk3 c sk4) ∨ b = c ∨ b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5943 eq367 eq5882
  have eq5966 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5966 eq544 eq5882
  have eq5968 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq5968 eq557 eq5882
  have eq6025 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ b = sk0 := step_1_eq6025 eq5968
  have eq6026 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 ∨ b = sk0 := step_1_eq6026 eq5966
  have eq6029 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq6029 eq5942
  have eq6055 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq6055 eq6025 eq55
  have eq6057 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq6057 eq6026 eq55
  have eq6070 : b = c ∨ b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq6070 eq5943 eq55
  have eq6071 : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq6071 eq6029 eq55
  have eq6087 : b = sk4 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq6087 eq6070 eq50
  have eq6088 : b = sk2 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq6088 eq6071 eq50
  have eq6218 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = c ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq6218 eq340 eq6088
  have eq6382 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = c ∨ b = sk1 := step_1_eq6382 eq6218
  have eq6438 : (old b sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq6438 eq6382 eq50
  have eq8426 : ¬(new sk0 b c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq8426 eq5923 eq6087
  have eq8427 : ¬(new sk0 b c) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 := step_1_eq8427 eq8426
  have eq9440 : (old sk3 b (sF0 sk3 c sk4)) ∨ b = c ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 c sk4) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq9440 eq2164 eq5882
  have eq9452 : (old sk3 b (sF0 sk3 c sk4)) ∨ (old b a a) ∨ c = sk3 ∨ (old sk3 c sk4) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq9452 eq9440 eq50
  have eq9453 : (old sk3 b (sF0 sk3 c sk4)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq9453 eq9452 eq55
  have eq9499 (X0 : G) : ¬(old b sk1 X0) ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (old b X0 sk1) := step_1_eq9499 eq5351 eq61 X0
  have eq9998 : (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ b = sk0 ∨ c = sk0 ∨ a = sk3 := step_1_eq9998 eq756 eq353
  have eq10016 : (old b sk1 a) ∨ c = sk1 ∨ a = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk0 sk4 sk1) ∨ b = sk0 ∨ c = sk0 := step_1_eq10016 eq9998
  have eq10031 : ¬(old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk3 ∨ (old b sk1 a) ∨ b = sk0 ∨ c = sk0 := step_1_eq10031 eq10016 eq115
  have eq17397 (X0 : G) : c = sk3 ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 sk2 (sF0 sk3 sk1 sk4)) ∨ ¬(old sk0 sk2 X0) ∨ (old a sk2 X0) ∨ c = sk3 ∨ c = sk0 ∨ a = sk3 := step_1_eq17397 eq982 eq301 X0
  have eq17425 (X0 : G) : ¬(old sk0 sk2 X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 sk2 (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a sk2 X0) ∨ c = sk0 := step_1_eq17425 eq17397 X0
  have eq21227 : c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ (old b sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := step_1_eq21227 eq5052 eq248
  have eq21262 : (old b sk0 a) ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 := step_1_eq21262 eq21227
  have eq22987 : c = sk1 ∨ a = sk3 ∨ (old b sk1 a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1 := step_1_eq22987 eq10031 eq428
  have eq23004 : (old b sk1 a) ∨ a = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := step_1_eq23004 eq22987
  have eq30357 : b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (old b a sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq30357 eq9499 eq5349
  have eq30404 : (old b a sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 := step_1_eq30404 eq30357
  have eq65331 (X0 : G) : ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 b (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq65331 eq17425 eq6088 X0
  have eq65334 (X0 : G) : ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ ¬(old sk3 b (sF0 sk3 sk1 sk4)) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq65334 eq65331 X0
  have eq65336 (X0 : G) : ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ c = sk3 ∨ (old a b X0) ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq65336 eq65334 eq559 X0
  have eq65337 (X0 : G) : ¬(old sk0 b X0) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old X0 sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq65337 eq65336 eq51 X0
  have eq73422 : (old sk3 b (sF0 sk3 c b)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq73422 eq9453 eq6087
  have eq73465 : (old sk3 b (sF0 sk3 c b)) ∨ (old b a a) ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq73465 eq73422
  have eq189713 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq189713 eq65337 eq6055
  have eq189790 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 := step_1_eq189790 eq189713
  have eq189820 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 := step_1_eq189820 eq189790 eq6057
  have eq189904 : (old sk3 c sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq189904 eq189820 eq5882
  have eq189981 : (old sk3 c sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := step_1_eq189981 eq189904
  have eq190017 : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = c ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := step_1_eq190017 eq189981 eq55
  have eq190018 : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := step_1_eq190018 eq190017 eq50
  have eq190186 : (old b sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := step_1_eq190186 eq6438 eq190018
  have eq190460 : (old a b (sF0 a c b)) ∨ (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 := step_1_eq190460 eq73465 eq190018
  have eq190498 : (old a b (sF0 a c b)) ∨ (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 := step_1_eq190498 eq190460
  have eq190647 : (old b sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ a = sk0 := step_1_eq190647 eq190186
  have eq190730 : (old b a a) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 := step_1_eq190730 eq190498 eq51
  have eq190862 : (old b a a) ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 := step_1_eq190862 eq190730 eq49
  have eq191830 (X0 X1 : G) : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old X0 b X1) ∨ ¬(old b X0 a) ∨ ¬(old X1 X0 a) ∨ (old a b X1) := step_1_eq191830 eq190862 eq62 X0 X1
  have eq191916 (X0 X1 : G) : ¬(old b X0 a) ∨ c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old X0 b X1) ∨ b = sk1 ∨ ¬(old X1 X0 a) := step_1_eq191916 eq191830 eq51 X0 X1
  have eq210509 (X0 : G) : c = sk0 ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ ¬(old sk0 b X0) ∨ b = sk1 ∨ ¬(old X0 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ c = sk3 ∨ a = sk0 := step_1_eq210509 eq191916 eq190647 X0
  have eq210722 (X0 : G) : ¬(old sk0 b X0) ∨ b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old X0 sk0 a) := step_1_eq210722 eq210509 X0
  have eq210896 : b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 := step_1_eq210896 eq210722 eq6055
  have eq210995 : b = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 ∨ ¬(old (sF0 sk0 c sk2) sk0 a) := step_1_eq210995 eq210896
  have eq211079 : c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq211079 eq210995 eq6057
  have eq211300 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq211300 eq6438 eq211079
  have eq211867 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ a = sk0 := step_1_eq211867 eq211300
  have eq212188 : b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq212188 eq211867 eq52
  have eq212353 : (new sk3 b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq212353 eq94 eq212188
  have eq212354 : ¬(new sk0 sk4 b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq212354 eq95 eq212188
  have eq212365 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq212365 eq248 eq212188
  have eq213009 : (old b b a) ∨ a = sk3 ∨ b = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq213009 eq23004 eq212188
  have eq213722 : (old b b a) ∨ a = sk3 ∨ b = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := step_1_eq213722 eq213009
  have eq214083 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = c ∨ b = sk0 := step_1_eq214083 eq212365
  have eq214244 : (old b b a) ∨ a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := step_1_eq214244 eq213722 eq50
  have eq214452 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := step_1_eq214452 eq214083 eq50
  have eq217796 : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ a = b := step_1_eq217796 eq214244 eq116
  have eq217804 : a = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := step_1_eq217804 eq217796 eq47
  have eq217913 : (old sk2 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := step_1_eq217913 eq340 eq217804
  have eq218391 : (new a b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := step_1_eq218391 eq212353 eq217804
  have eq218392 : (new a b sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq218392 eq218391
  have eq218511 : (old sk2 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 := step_1_eq218511 eq217913
  have eq219037 : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ (old a b sk4) ∨ c = sk4 ∨ b = c ∨ a = c := step_1_eq219037 eq218392 eq195
  have eq219152 : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk4 ∨ b = c ∨ a = c := step_1_eq219152 eq219037 eq51
  have eq219160 : c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk4 ∨ a = c := step_1_eq219160 eq219152 eq50
  have eq219162 : c = sk4 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := step_1_eq219162 eq219160 eq49
  have eq219405 : ¬(new sk0 c b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := step_1_eq219405 eq212354 eq219162
  have eq219412 : ¬(new sk0 c b) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq219412 eq219405
  have eq222788 : b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ ¬(old sk0 b sk2) ∨ (new sk0 c b) := step_1_eq222788 eq218511 eq100
  have eq222837 : b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ (new sk0 c b) := step_1_eq222837 eq222788 eq214452
  have eq222838 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq222838 eq222837 eq219412
  have eq223817 : (old sk0 b c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := step_1_eq223817 eq214452 eq222838
  have eq223822 : (old sk0 b c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := step_1_eq223822 eq223817
  have eq224264 : a = sk0 ∨ c = sk0 ∨ b = sk0 := step_1_eq224264 eq223822 eq53
  have eq224807 : (new a sk1 sk2) ∨ c = sk0 ∨ b = sk0 := step_1_eq224807 eq92 eq224264
  have eq224878 : (old sk2 a sk3) ∨ a = b ∨ a = c ∨ (old a b b) ∨ c = sk0 ∨ b = sk0 := step_1_eq224878 eq493 eq224264
  have eq225169 : ¬(new a b c) ∨ b = sk1 ∨ a = c ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := step_1_eq225169 eq8427 eq224264
  have eq226477 : b = sk1 ∨ a = c ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := step_1_eq226477 eq225169 eq90
  have eq226627 : (old sk2 a sk3) ∨ a = c ∨ (old a b b) ∨ c = sk0 ∨ b = sk0 := step_1_eq226627 eq224878 eq47
  have eq226751 : b = sk1 ∨ a = b ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := step_1_eq226751 eq226477 eq49
  have eq226811 : (old sk2 a sk3) ∨ (old a b b) ∨ c = sk0 ∨ b = sk0 := step_1_eq226811 eq226627 eq49
  have eq226829 : c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq226829 eq226751 eq47
  have eq226836 : (old sk2 a sk3) ∨ c = sk0 ∨ b = sk0 := step_1_eq226836 eq226811 eq51
  have eq229347 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq229347 eq6438 eq226829
  have eq229930 : (old b sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq229930 eq229347
  have eq230245 : b = sk1 ∨ c = sk0 ∨ b = sk0 := step_1_eq230245 eq229930 eq52
  have eq231681 : (new a b sk2) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 := step_1_eq231681 eq224807 eq230245
  have eq231686 : (new a b sk2) ∨ c = sk0 ∨ b = sk0 := step_1_eq231686 eq231681
  have eq232992 : c = sk0 ∨ b = sk0 ∨ (old a b sk2) ∨ c = sk2 ∨ b = c ∨ a = c := step_1_eq232992 eq231686 eq195
  have eq233043 : c = sk0 ∨ b = sk0 ∨ c = sk2 ∨ b = c ∨ a = c := step_1_eq233043 eq232992 eq51
  have eq233051 : c = sk0 ∨ b = sk0 ∨ c = sk2 ∨ a = c := step_1_eq233051 eq233043 eq50
  have eq233053 : c = sk2 ∨ b = sk0 ∨ c = sk0 := step_1_eq233053 eq233051 eq49
  have eq233881 : (old c a sk3) ∨ c = sk0 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 := step_1_eq233881 eq226836 eq233053
  have eq233886 : (old c a sk3) ∨ c = sk0 ∨ b = sk0 := step_1_eq233886 eq233881
  have eq235715 : c = sk0 ∨ b = sk0 ∨ a = c := step_1_eq235715 eq233886 eq57
  have eq235873 : c = sk0 ∨ b = sk0 := step_1_eq235873 eq235715 eq49
  have eq235875 : (new c sk1 sk2) ∨ b = sk0 := step_1_eq235875 eq92 eq235873
  have eq235876 : (new sk2 c sk3) ∨ b = sk0 := step_1_eq235876 eq93 eq235873
  have eq235878 : ¬(old c sk4 sk1) ∨ b = sk0 := step_1_eq235878 eq115 eq235873
  have eq235885 : (old c sk1 sk2) ∨ a = c ∨ a = sk2 ∨ c = sk1 ∨ b = sk0 := step_1_eq235885 eq274 eq235873
  have eq235912 : (old c sk1 sk2) ∨ a = c ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk0 := step_1_eq235912 eq428 eq235873
  have eq237447 : a = c ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk0 := step_1_eq237447 eq235912 eq57
  have eq237461 : a = c ∨ a = sk2 ∨ c = sk1 ∨ b = sk0 := step_1_eq237461 eq235885 eq57
  have eq237583 : (old b sk1 a) ∨ c = sk1 ∨ b = sk0 := step_1_eq237583 eq237447 eq49
  have eq237585 : a = sk2 ∨ c = sk1 ∨ b = sk0 := step_1_eq237585 eq237461 eq49
  have eq237611 : b = sk0 ∨ (old c sk1 sk2) ∨ a = c ∨ (old sk1 b b) ∨ c = sk1 := step_1_eq237611 eq235875 eq180
  have eq237682 : b = sk0 ∨ a = c ∨ (old sk1 b b) ∨ c = sk1 := step_1_eq237682 eq237611 eq57
  have eq237691 : (old sk1 b b) ∨ b = sk0 ∨ c = sk1 := step_1_eq237691 eq237682 eq49
  have eq240100 : (new a c sk3) ∨ b = sk0 ∨ c = sk1 ∨ b = sk0 := step_1_eq240100 eq235876 eq237585
  have eq240101 : (new a c sk3) ∨ b = sk0 ∨ c = sk1 := step_1_eq240101 eq240100
  have eq243500 (X0 : G) : ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk0 ∨ (old b X0 sk1) := step_1_eq243500 eq237691 eq61 X0
  have eq244180 : b = sk0 ∨ c = sk1 ∨ (old a c sk3) ∨ b = c ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3)) := step_1_eq244180 eq240101 eq662
  have eq244235 : b = sk0 ∨ c = sk1 ∨ b = c ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3)) := step_1_eq244235 eq244180 eq55
  have eq244251 : b = sk0 ∨ c = sk1 ∨ (old b a a) ∨ a = c ∨ (old a b (sF0 a c sk3)) := step_1_eq244251 eq244235 eq50
  have eq244259 : b = sk0 ∨ c = sk1 ∨ (old b a a) ∨ (old a b (sF0 a c sk3)) := step_1_eq244259 eq244251 eq49
  have eq244263 : (old b a a) ∨ c = sk1 ∨ b = sk0 := step_1_eq244263 eq244259 eq51
  have eq247039 (X0 : G) : ¬(old b a X0) ∨ b = sk0 ∨ c = sk1 ∨ a = X0 := step_1_eq247039 eq244263 eq58 X0
  have eq257022 : c = sk1 ∨ b = sk0 ∨ (old b a sk1) ∨ c = sk1 ∨ b = sk0 := step_1_eq257022 eq243500 eq237583
  have eq257041 : (old b a sk1) ∨ b = sk0 ∨ c = sk1 := step_1_eq257041 eq257022
  have eq257483 : b = sk0 ∨ c = sk1 ∨ b = sk0 ∨ c = sk1 ∨ a = sk1 := step_1_eq257483 eq257041 eq247039
  have eq257686 : a = sk1 ∨ c = sk1 ∨ b = sk0 := step_1_eq257686 eq257483
  have eq259783 : (old a b b) ∨ b = sk0 ∨ a = c ∨ c = sk1 ∨ b = sk0 := step_1_eq259783 eq237691 eq257686
  have eq259895 : (old a b b) ∨ b = sk0 ∨ a = c ∨ c = sk1 := step_1_eq259895 eq259783
  have eq260395 : b = sk0 ∨ a = c ∨ c = sk1 := step_1_eq260395 eq259895 eq51
  have eq260492 : c = sk1 ∨ b = sk0 := step_1_eq260492 eq260395 eq49
  have eq260635 : (new sk3 c sk4) ∨ b = sk0 := step_1_eq260635 eq94 eq260492
  have eq261599 : (new c c sk2) ∨ b = sk0 ∨ b = sk0 := step_1_eq261599 eq235875 eq260492
  have eq261601 : ¬(old c sk4 c) ∨ b = sk0 ∨ b = sk0 := step_1_eq261601 eq235878 eq260492
  have eq261686 : ¬(old c sk4 c) ∨ b = sk0 := step_1_eq261686 eq261601
  have eq261688 : (new c c sk2) ∨ b = sk0 := step_1_eq261688 eq261599
  have eq263479 : b = sk0 ∨ (old c c sk2) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk2) c a) := step_1_eq263479 eq261688 eq185
  have eq263544 : b = sk0 ∨ (old c c sk2) ∨ a = c ∨ (old (sF0 c c sk2) c a) := step_1_eq263544 eq263479 eq54
  have eq263560 : b = sk0 ∨ (old c c sk2) ∨ a = c := step_1_eq263560 eq263544 eq54
  have eq263565 : (old c c sk2) ∨ b = sk0 := step_1_eq263565 eq263560 eq49
  have eq263742 : c = sk2 ∨ b = sk0 := step_1_eq263742 eq263565 eq56
  have eq264768 : (new c c sk3) ∨ b = sk0 ∨ b = sk0 := step_1_eq264768 eq235876 eq263742
  have eq264805 : (new c c sk3) ∨ b = sk0 := step_1_eq264805 eq264768
  have eq267061 : b = sk0 ∨ (old c c sk3) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk3) c a) := step_1_eq267061 eq264805 eq185
  have eq267144 : b = sk0 ∨ (old c c sk3) ∨ a = c ∨ (old (sF0 c c sk3) c a) := step_1_eq267144 eq267061 eq54
  have eq267160 : b = sk0 ∨ (old c c sk3) ∨ a = c := step_1_eq267160 eq267144 eq54
  have eq267165 : (old c c sk3) ∨ b = sk0 := step_1_eq267165 eq267160 eq49
  have eq268947 : c = sk3 ∨ b = sk0 := step_1_eq268947 eq267165 eq56
  have eq270024 : (new c c sk4) ∨ b = sk0 ∨ b = sk0 := step_1_eq270024 eq260635 eq268947
  have eq270031 : (new c c sk4) ∨ b = sk0 := step_1_eq270031 eq270024
  have eq272177 : b = sk0 ∨ (old c c sk4) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk4) c a) := step_1_eq272177 eq270031 eq185
  have eq272299 : b = sk0 ∨ (old c c sk4) ∨ a = c ∨ (old (sF0 c c sk4) c a) := step_1_eq272299 eq272177 eq54
  have eq272315 : b = sk0 ∨ (old c c sk4) ∨ a = c := step_1_eq272315 eq272299 eq54
  have eq272320 : (old c c sk4) ∨ b = sk0 := step_1_eq272320 eq272315 eq49
  have eq273537 : b = sk0 ∨ (old c sk4 c) := step_1_eq273537 eq272320 eq118
  have eq273609 : b = sk0 := step_1_eq273609 eq273537 eq261686
  have eq273790 : ¬(old b sk4 sk1) := step_1_eq273790 eq115 eq273609
  have eq273791 : (old b sk1 sk2) ∨ a = b ∨ b = c ∨ b = sk2 := step_1_eq273791 eq156 eq273609
  have eq273801 : (old b sk1 sk2) ∨ a = b ∨ b = c ∨ c = sk1 := step_1_eq273801 eq248 eq273609
  have eq274519 : (old b b a) ∨ c = sk4 ∨ c = sk1 ∨ b = c ∨ c = sk3 ∨ a = b := step_1_eq274519 eq21262 eq273609
  have eq275513 : c = sk4 ∨ c = sk1 ∨ b = c ∨ c = sk3 ∨ a = b := step_1_eq275513 eq274519 eq116
  have eq275838 : (old b sk1 sk2) ∨ b = c ∨ c = sk1 := step_1_eq275838 eq273801 eq47
  have eq275844 : (old b sk1 sk2) ∨ b = c ∨ b = sk2 := step_1_eq275844 eq273791 eq47
  have eq275933 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ a = b := step_1_eq275933 eq275513 eq50
  have eq276015 : (old b sk1 sk2) ∨ c = sk1 := step_1_eq276015 eq275838 eq50
  have eq276021 : (old b sk1 sk2) ∨ b = sk2 := step_1_eq276021 eq275844 eq50
  have eq276032 : c = sk4 ∨ c = sk1 ∨ c = sk3 := step_1_eq276032 eq275933 eq47
  have eq276612 : ¬(old b a sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq276612 eq273790 eq5369
  have eq276670 : c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_1_eq276670 eq276612 eq30404
  have eq276686 : b = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk2 := step_1_eq276686 eq276670 eq273609
  have eq276701 : c = sk2 ∨ b = sk1 ∨ c = sk1 := step_1_eq276701 eq276686 eq50
  have eq279699 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk1 ∨ c = sk3 := step_1_eq279699 eq250 eq276032
  have eq280031 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 := step_1_eq280031 eq279699
  have eq280152 : a = sk3 ∨ c = sk3 ∨ c = sk1 := step_1_eq280152 eq280031 eq52
  have eq281061 : (old b sk1 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 := step_1_eq281061 eq276015 eq276701
  have eq281064 : (old b sk1 c) ∨ c = sk1 ∨ b = sk1 := step_1_eq281064 eq281061
  have eq281329 : c = sk1 ∨ b = sk1 := step_1_eq281329 eq281064 eq52
  have eq282449 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 := step_1_eq282449 eq544 eq281329
  have eq282451 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ (old sk0 c sk2) ∨ b = sk1 := step_1_eq282451 eq557 eq281329
  have eq283906 : (old sk0 b (sF0 sk0 c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq283906 eq282451 eq55
  have eq283908 : (old (sF0 sk0 c sk2) sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq283908 eq282449 eq55
  have eq284290 : (old b b (sF0 b c sk2)) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq284290 eq283906 eq273609
  have eq284291 : (old (sF0 b c sk2) b a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk1 := step_1_eq284291 eq283908 eq273609
  have eq284541 : a = b ∨ (old b b (sF0 b c sk2)) ∨ c = sk0 ∨ b = sk1 := step_1_eq284541 eq284290 eq273609
  have eq284542 : a = b ∨ (old (sF0 b c sk2) b a) ∨ c = sk0 ∨ b = sk1 := step_1_eq284542 eq284291 eq273609
  have eq284707 : (old b b (sF0 b c sk2)) ∨ c = sk0 ∨ b = sk1 := step_1_eq284707 eq284541 eq47
  have eq284708 : (old (sF0 b c sk2) b a) ∨ c = sk0 ∨ b = sk1 := step_1_eq284708 eq284542 eq47
  have eq284794 : b = c ∨ (old b b (sF0 b c sk2)) ∨ b = sk1 := step_1_eq284794 eq284707 eq273609
  have eq284795 : b = c ∨ (old (sF0 b c sk2) b a) ∨ b = sk1 := step_1_eq284795 eq284708 eq273609
  have eq284822 : (old b b (sF0 b c sk2)) ∨ b = sk1 := step_1_eq284822 eq284794 eq50
  have eq284823 : (old (sF0 b c sk2) b a) ∨ b = sk1 := step_1_eq284823 eq284795 eq50
  have eq299556 : b = (sF0 b c sk2) ∨ b = sk1 := step_1_eq299556 eq284822 eq116
  have eq299614 : (old b b a) ∨ b = sk1 ∨ b = sk1 := step_1_eq299614 eq284823 eq299556
  have eq299615 : (old b b a) ∨ b = sk1 := step_1_eq299615 eq299614
  have eq299627 : b = sk1 ∨ a = b := step_1_eq299627 eq299615 eq116
  have eq299635 : b = sk1 := step_1_eq299635 eq299627 eq47
  have eq300834 : (old b b sk2) ∨ b = sk2 := step_1_eq300834 eq276021 eq299635
  have eq300854 : b = sk2 := step_1_eq300854 eq300834 eq116
  have eq302642 : (old b sk0 sk3) ∨ a = b ∨ b = c ∨ b = sk3 := step_1_eq302642 eq157 eq300854
  have eq304464 : (old b sk0 sk3) ∨ b = c ∨ b = sk3 := step_1_eq304464 eq302642 eq47
  have eq305027 : (old b sk0 sk3) ∨ b = sk3 := step_1_eq305027 eq304464 eq50
  have eq305476 : (old b b sk3) ∨ b = sk3 := step_1_eq305476 eq305027 eq273609
  have eq305789 : b = sk3 := step_1_eq305789 eq305476 eq116
  have eq307247 : a = b ∨ b = c ∨ c = sk1 := step_1_eq307247 eq280152 eq305789
  have eq307256 : b = c ∨ c = sk1 := step_1_eq307256 eq307247 eq47
  have eq307723 : c = sk1 := step_1_eq307723 eq307256 eq50
  have eq308169 : b = c := step_1_eq308169 eq307723 eq299635
  clear * - eq308169 eq50
  first | subsumption eq308169 eq50 | grind only


private theorem step_2_eq47 {G : Type*} {a : G} {b : G} (ab : a ≠ b) : a ≠ b := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ab | grind only

private theorem step_2_eq48 {G : Type*} {old : G → G → G → Prop} (diagonal : ∀ x, old x x x) : ∀ (X0 : G), (old X0 X0 X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using diagonal | grind only

private theorem step_2_eq49 {G : Type*} {a : G} {c : G} (ac : a ≠ c) : a ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ac | grind only

private theorem step_2_eq50 {G : Type*} {b : G} {c : G} (bc : b ≠ c) : b ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using bc | grind only

private theorem step_2_eq51 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (p3 : ∀ z, ¬ old a b z) : ∀ (X0 : G), ¬(old a b X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p3 | grind only

private theorem step_2_eq52 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_2_eq53 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_2_eq54 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_2_eq55 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_2_eq56 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_2_eq57 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_2_eq60 {G : Type*} {old : G → G → G → Prop} (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ ¬ old X2 X1 X3 ∨ old X3 X0 X2)) : ∀ (X0 X1 X2 X3 : G), ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2) := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_2 | grind only

private theorem step_2_eq61 {G : Type*} {old : G → G → G → Prop} (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ old X1 X2 X0)) : ∀ (X0 X1 X2 : G), ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_3 | grind only

private theorem step_2_eq64 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_0 | grind only

private theorem step_2_eq66 {G : Type*} {a : G} {sP0 : G → G → G → Prop} (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_0 | grind only

private theorem step_2_eq67 {G : Type*} {b : G} {sP0 : G → G → G → Prop} (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_1 | grind only

private theorem step_2_eq68 {G : Type*} {c : G} {sP0 : G → G → G → Prop} (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_2 | grind only

private theorem step_2_eq70 {G : Type*} {c : G} {sP1 : G → G → G → Prop} (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_0 | grind only

private theorem step_2_eq71 {G : Type*} {b : G} {sP1 : G → G → G → Prop} (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_1 | grind only

private theorem step_2_eq72 {G : Type*} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_2 | grind only

private theorem step_2_eq73 {G : Type*} {a : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), (old (sF0 X0 X1 X2) X0 a) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_3 | grind only

private theorem step_2_eq75 {G : Type*} {c : G} {sP2 : G → G → G → Prop} (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_0 | grind only

private theorem step_2_eq76 {G : Type*} {a : G} {sP2 : G → G → G → Prop} (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_1 | grind only

private theorem step_2_eq77 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_2 | grind only

private theorem step_2_eq78 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_3 | grind only

private theorem step_2_eq80 {G : Type*} {a : G} {sP3 : G → G → G → Prop} (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_0 | grind only

private theorem step_2_eq81 {G : Type*} {c : G} {sP3 : G → G → G → Prop} (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_1 | grind only

private theorem step_2_eq82 {G : Type*} {b : G} {sP3 : G → G → G → Prop} (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_2 | grind only

private theorem step_2_eq84 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_5 : ∀ X Y Z, c ≠ X ∨ a ≠ Z ∨ ¬ old b Y a ∨ ¬ old Y b b ∨ ¬ old b Y a ∨ new X Y Z) : ∀ (X0 X1 X2 : G), c ≠ X0 ∨ a ≠ X2 ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_5 | grind only

private theorem step_2_eq85 {G : Type*} {c : G} {sP4 : G → G → G → Prop} (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_0 | grind only

private theorem step_2_eq86 {G : Type*} {a : G} {sP4 : G → G → G → Prop} (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_1 | grind only

private theorem step_2_eq88 {G : Type*} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_3 | grind only

private theorem step_2_eq89 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_4 | grind only

private theorem step_2_eq91 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_imp | grind only

private theorem step_2_eq92 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (preserve_0 : new sk0 sk1 sk1) : (new sk0 sk1 sk1) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_0 | grind only

private theorem step_2_eq93 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_1 : new sk1 sk0 sk2) : (new sk1 sk0 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_1 | grind only

private theorem step_2_eq94 {G : Type*} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (preserve_2 : new sk2 sk1 sk3) : (new sk2 sk1 sk3) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_2 | grind only

private theorem step_2_eq95 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (preserve_3 : ¬ (new sk3 sk0 sk2)) : ¬(new sk3 sk0 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_3 | grind only

private theorem step_2_eq106 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq84 : ∀ (X0 X1 X2 : G), c ≠ X0 ∨ a ≠ X2 ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new X0 X1 X2)) : ∀ (X1 X2 : G), a ≠ X2 ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 X2) := by
  intro X1 X2
  first | exact resolve eq84 rfl | grind only

private theorem step_2_eq107 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq106 : ∀ (X1 X2 : G), a ≠ X2 ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 X2)) : ∀ (X1 : G), ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 a) := by
  intro X1
  first | exact resolve eq106 rfl | grind only

private theorem step_2_eq108 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq107 : ∀ (X1 : G), ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 a)) : ∀ (X1 : G), ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ (new c X1 a) := by
  intro X1
  first | exact resolve eq107 rfl | grind only

private theorem step_2_eq120 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq72 : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) ∨ b = c := by
  intro X0 X1
  first | exact resolve eq72 eq57 | exact resolve eq57 eq72 | grind only

private theorem step_2_eq122 {G : Type*} {b : G} {c : G} {sP1 : G → G → G → Prop} (eq120 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) ∨ b = c) (eq50 : b ≠ c) : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) := by
  intro X0 X1
  first | exact resolve eq120 eq50 | exact resolve eq50 eq120 | grind only

private theorem step_2_eq140 {G : Type*} {a : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq60 : ∀ (X0 X1 X2 X3 : G), ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2)) (eq73 : ∀ (X0 X1 X2 : G), (old (sF0 X0 X1 X2) X0 a) ∨ ¬(sP1 X0 X1 X2)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 (sF0 X0 X2 X3)) ∨ ¬(old X1 X0 X0) ∨ (old a X1 (sF0 X0 X2 X3)) ∨ ¬(sP1 X0 X2 X3) := by
  intro X0 X1 X2 X3
  first | exact resolve eq60 eq73 | exact resolve eq73 eq60 | grind only

private theorem step_2_eq153 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq91 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq92 : (new sk0 sk1 sk1)) : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) := by
  first | exact resolve eq91 eq92 | exact resolve eq92 eq91 | grind only

private theorem step_2_eq154 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq91 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq93 : (new sk1 sk0 sk2)) : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) := by
  first | exact resolve eq91 eq93 | exact resolve eq93 eq91 | grind only

private theorem step_2_eq155 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq91 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq94 : (new sk2 sk1 sk3)) : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) := by
  first | exact resolve eq91 eq94 | exact resolve eq94 eq91 | grind only

private theorem step_2_eq158 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq153 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := by
  first | exact resolve eq153 eq68 | exact resolve eq68 eq153 | grind only

private theorem step_2_eq159 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq153 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := by
  first | exact resolve eq153 eq67 | exact resolve eq67 eq153 | grind only

private theorem step_2_eq162 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq159 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := by
  first | exact resolve eq159 eq71 | exact resolve eq71 eq159 | grind only

private theorem step_2_eq163 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq158 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := by
  first | exact resolve eq158 eq70 | exact resolve eq70 eq158 | grind only

private theorem step_2_eq164 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq162 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := by
  first | exact resolve eq162 eq82 | exact resolve eq82 eq162 | grind only

private theorem step_2_eq165 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq163 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := by
  first | exact resolve eq163 eq81 | exact resolve eq81 eq163 | grind only

private theorem step_2_eq166 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq154 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 := by
  first | exact resolve eq154 eq68 | exact resolve eq68 eq154 | grind only

private theorem step_2_eq167 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq154 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 := by
  first | exact resolve eq154 eq67 | exact resolve eq67 eq154 | grind only

private theorem step_2_eq168 {G : Type*} {a : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq154 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := by
  first | exact resolve eq154 eq66 | exact resolve eq66 eq154 | grind only

private theorem step_2_eq169 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq168 : (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := by
  first | exact resolve eq168 eq80 | exact resolve eq80 eq168 | grind only

private theorem step_2_eq173 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq164 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq164 eq75 | exact resolve eq75 eq164 | grind only

private theorem step_2_eq174 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq173 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq173 eq85 | exact resolve eq85 eq173 | grind only

private theorem step_2_eq178 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq155 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 := by
  first | exact resolve eq155 eq68 | exact resolve eq68 eq155 | grind only

private theorem step_2_eq179 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq155 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 := by
  first | exact resolve eq155 eq67 | exact resolve eq67 eq155 | grind only

private theorem step_2_eq180 {G : Type*} {a : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq155 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 := by
  first | exact resolve eq155 eq66 | exact resolve eq66 eq155 | grind only

private theorem step_2_eq181 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq180 : (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 := by
  first | exact resolve eq180 eq80 | exact resolve eq80 eq180 | grind only

private theorem step_2_eq292 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq165 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b)) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := by
  first | exact resolve eq165 eq77 | exact resolve eq77 eq165 | grind only

private theorem step_2_eq293 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq165 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq165 eq76 | exact resolve eq76 eq165 | grind only

private theorem step_2_eq294 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq165 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq165 eq75 | exact resolve eq75 eq165 | grind only

private theorem step_2_eq295 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq294 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq294 eq85 | exact resolve eq85 eq294 | grind only

private theorem step_2_eq296 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq293 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq293 eq86 | exact resolve eq86 eq293 | grind only

private theorem step_2_eq297 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq292 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b)) : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := by
  first | exact resolve eq292 eq88 | exact resolve eq88 eq292 | grind only

private theorem step_2_eq339 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq140 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 (sF0 X0 X2 X3)) ∨ ¬(old X1 X0 X0) ∨ (old a X1 (sF0 X0 X2 X3)) ∨ ¬(sP1 X0 X2 X3)) (eq72 : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | exact resolve eq140 eq72 | exact resolve eq72 eq140 | grind only

private theorem step_2_eq340 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq339 : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | exact resolve eq339 rfl | grind only

private theorem step_2_eq341 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq340 : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ ¬(old b X0 X0) := by
  intro X0 X1 X2
  first | exact resolve eq340 eq51 | exact resolve eq51 eq340 | grind only

private theorem step_2_eq415 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq169 : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := by
  first | exact resolve eq169 eq76 | exact resolve eq76 eq169 | grind only

private theorem step_2_eq416 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq169 : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq169 eq75 | exact resolve eq75 eq169 | grind only

private theorem step_2_eq417 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq416 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq416 eq85 | exact resolve eq85 eq416 | grind only

private theorem step_2_eq418 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq415 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := by
  first | exact resolve eq415 eq86 | exact resolve eq86 eq415 | grind only

private theorem step_2_eq428 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq181 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 ∨ a = sk3 := by
  first | exact resolve eq181 eq76 | exact resolve eq76 eq181 | grind only

private theorem step_2_eq429 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq181 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 := by
  first | exact resolve eq181 eq75 | exact resolve eq75 eq181 | grind only

private theorem step_2_eq430 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq429 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 := by
  first | exact resolve eq429 eq85 | exact resolve eq85 eq429 | grind only

private theorem step_2_eq431 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq428 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 ∨ a = sk3) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ a = sk3 := by
  first | exact resolve eq428 eq86 | exact resolve eq86 eq428 | grind only

private theorem step_2_eq441 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq166 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq166 eq81 | exact resolve eq81 eq166 | grind only

private theorem step_2_eq443 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq441 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq441 eq70 | exact resolve eq70 eq441 | grind only

private theorem step_2_eq449 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq417 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq417 eq70 | exact resolve eq70 eq417 | grind only

private theorem step_2_eq451 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq167 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := by
  first | exact resolve eq167 eq82 | exact resolve eq82 eq167 | grind only

private theorem step_2_eq455 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq451 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := by
  first | exact resolve eq451 eq71 | exact resolve eq71 eq451 | grind only

private theorem step_2_eq468 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq178 : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq178 eq81 | exact resolve eq81 eq178 | grind only

private theorem step_2_eq470 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq468 : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq468 eq70 | exact resolve eq70 eq468 | grind only

private theorem step_2_eq475 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq449 : (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0) (eq61 : ∀ (X0 X1 X2 : G), ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0)) : a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0) := by
  first | exact resolve eq449 eq61 | exact resolve eq61 eq449 | grind only

private theorem step_2_eq481 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq475 : a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0)) (eq296 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) : (old sk1 sk2 sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := by
  first | exact resolve eq475 eq296 | exact resolve eq296 eq475 | grind only

private theorem step_2_eq483 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq179 : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
  first | exact resolve eq179 eq82 | exact resolve eq82 eq179 | grind only

private theorem step_2_eq484 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq179 : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq179 eq81 | exact resolve eq81 eq179 | grind only

private theorem step_2_eq486 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq484 : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq484 eq70 | exact resolve eq70 eq484 | grind only

private theorem step_2_eq487 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq483 : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
  first | exact resolve eq483 eq71 | exact resolve eq71 eq483 | grind only

private theorem step_2_eq499 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq341 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ ¬(old b X0 X0)) (eq417 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1) : ¬(old b sk1 sk1) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq341 eq417 | exact resolve eq417 eq341 | grind only

private theorem step_2_eq554 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq430 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq430 eq70 | exact resolve eq70 eq430 | grind only

private theorem step_2_eq555 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq430 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 ∨ b = sk3 := by
  first | exact resolve eq430 eq71 | exact resolve eq71 eq430 | grind only

private theorem step_2_eq569 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq554 : (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 ∨ c = sk1) (eq60 : ∀ (X0 X1 X2 X3 : G), ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2)) : ∀ (X0 : G), ¬(old sk1 X0 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old X0 sk1 sk1) ∨ (old sk3 X0 sk2) := by
  intro X0
  first | exact resolve eq554 eq60 | exact resolve eq60 eq554 | grind only

private theorem step_2_eq938 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq443 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := by
  first | exact resolve eq443 eq76 | exact resolve eq76 eq443 | grind only

private theorem step_2_eq939 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq443 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq443 eq75 | exact resolve eq75 eq443 | grind only

private theorem step_2_eq940 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq939 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq939 eq85 | exact resolve eq85 eq939 | grind only

private theorem step_2_eq941 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq938 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := by
  first | exact resolve eq938 eq86 | exact resolve eq86 eq938 | grind only

private theorem step_2_eq988 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq455 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := by
  first | exact resolve eq455 eq78 | exact resolve eq78 eq455 | grind only

private theorem step_2_eq995 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq988 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a)) (eq89 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (old sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := by
  first | exact resolve eq988 eq89 | exact resolve eq89 eq988 | grind only

private theorem step_2_eq1008 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq470 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq470 eq75 | exact resolve eq75 eq470 | grind only

private theorem step_2_eq1009 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1008 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq1008 eq85 | exact resolve eq85 eq1008 | grind only

private theorem step_2_eq1042 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq486 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 := by
  first | exact resolve eq486 eq76 | exact resolve eq76 eq486 | grind only

private theorem step_2_eq1043 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq486 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq486 eq75 | exact resolve eq75 eq486 | grind only

private theorem step_2_eq1044 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1043 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq1043 eq85 | exact resolve eq85 eq1043 | grind only

private theorem step_2_eq1045 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1042 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 := by
  first | exact resolve eq1042 eq86 | exact resolve eq86 eq1042 | grind only

private theorem step_2_eq1057 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq487 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := by
  first | exact resolve eq487 eq78 | exact resolve eq78 eq487 | grind only

private theorem step_2_eq1064 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1057 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a)) (eq89 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (old sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := by
  first | exact resolve eq1057 eq89 | exact resolve eq89 eq1057 | grind only

private theorem step_2_eq1084 {G : Type*} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1009 : (old sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2) (eq60 : ∀ (X0 X1 X2 X3 : G), ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2)) : ∀ (X0 : G), ¬(old sk1 X0 sk2) ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old X0 sk1 sk1) ∨ (old sk3 X0 sk2) := by
  intro X0
  first | exact resolve eq1009 eq60 | exact resolve eq60 eq1009 | grind only

private theorem step_2_eq5605 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq569 : ∀ (X0 : G), ¬(old sk1 X0 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old X0 sk1 sk1) ∨ (old sk3 X0 sk2)) (eq941 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2) : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := by
  first | exact resolve eq569 eq941 | exact resolve eq941 eq569 | grind only

private theorem step_2_eq5624 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5605 : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2) : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk0 := by
  first | exact resolve eq5605 rfl | grind only

private theorem step_2_eq5634 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5624 : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk0) (eq295 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0) : (old sk3 sk0 sk2) ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5624 eq295 | exact resolve eq295 eq5624 | grind only

private theorem step_2_eq5652 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5634 : (old sk3 sk0 sk2) ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0) (eq64 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) : c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ (new sk3 sk0 sk2) := by
  first | exact resolve eq5634 eq64 | exact resolve eq64 eq5634 | grind only

private theorem step_2_eq5664 {G : Type*} {a : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5652 : c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ (new sk3 sk0 sk2)) (eq95 : ¬(new sk3 sk0 sk2)) : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5652 eq95 | exact resolve eq95 eq5652 | grind only

private theorem step_2_eq5708 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq940 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1) (eq5664 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) : (old sk1 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq940 eq5664 | exact superpose eq5664 eq940 | grind only

private theorem step_2_eq5719 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1009 : (old sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2) (eq5664 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq1009 eq5664 | exact superpose eq5664 eq1009 | grind only

private theorem step_2_eq5729 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1044 : (old sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) (eq5664 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq1044 eq5664 | exact superpose eq5664 eq1044 | grind only

private theorem step_2_eq5927 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5729 : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5729 rfl | grind only

private theorem step_2_eq5933 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5719 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5719 rfl | grind only

private theorem step_2_eq5942 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5708 : (old sk1 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) : (old sk1 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq5708 rfl | grind only

private theorem step_2_eq6024 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5927 : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk2 ∨ c = sk0) (eq49 : a ≠ c) : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5927 eq49 | exact resolve eq49 eq5927 | grind only

private theorem step_2_eq6026 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq5933 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk2 ∨ c = sk0) (eq49 : a ≠ c) : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq5933 eq49 | exact resolve eq49 eq5933 | grind only

private theorem step_2_eq6035 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq5942 : (old sk1 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq49 : a ≠ c) : (old sk1 sk0 a) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq5942 eq49 | exact resolve eq49 eq5942 | grind only

private theorem step_2_eq7290 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1084 : ∀ (X0 : G), ¬(old sk1 X0 sk2) ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old X0 sk1 sk1) ∨ (old sk3 X0 sk2)) (eq940 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1) : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq1084 eq940 | exact resolve eq940 eq1084 | grind only

private theorem step_2_eq7311 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq7290 : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1) : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk0 := by
  first | exact resolve eq7290 rfl | grind only

private theorem step_2_eq7317 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq7311 : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk0) (eq295 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0) : (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq7311 eq295 | exact resolve eq295 eq7311 | grind only

private theorem step_2_eq7341 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq7317 : (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0) (eq64 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ (new sk3 sk0 sk2) := by
  first | exact resolve eq7317 eq64 | exact resolve eq64 eq7317 | grind only

private theorem step_2_eq7359 {G : Type*} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq7341 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ (new sk3 sk0 sk2)) (eq95 : ¬(new sk3 sk0 sk2)) : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq7341 eq95 | exact resolve eq95 eq7341 | grind only

private theorem step_2_eq7436 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq6024 : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) (eq7359 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact superpose eq6024 eq7359 | exact superpose eq7359 eq6024 | grind only

private theorem step_2_eq7442 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq7436 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq7436 rfl | grind only

private theorem step_2_eq7490 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq7442 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq7442 eq52 | exact resolve eq52 eq7442 | grind only

private theorem step_2_eq7580 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq95 : ¬(new sk3 sk0 sk2)) (eq7490 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : ¬(new sk3 sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq95 eq7490 | exact superpose eq7490 eq95 | grind only

private theorem step_2_eq7608 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq481 : (old sk1 sk2 sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1) (eq7490 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : (old sk1 c sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq481 eq7490 | exact superpose eq7490 eq481 | grind only

private theorem step_2_eq7677 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1045 : (old sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3) (eq7490 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : (old c sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq1045 eq7490 | exact superpose eq7490 eq1045 | grind only

private theorem step_2_eq7891 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq7677 : (old c sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : (old c sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 := by
  first | exact resolve eq7677 rfl | grind only

private theorem step_2_eq7928 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq7608 : (old sk1 c sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : (old sk1 c sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk1 := by
  first | exact resolve eq7608 rfl | grind only

private theorem step_2_eq7985 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq7891 : (old c sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 ∨ c = sk0) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq7891 eq57 | exact resolve eq57 eq7891 | grind only

private theorem step_2_eq8027 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq7928 : (old sk1 c sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := by
  first | exact resolve eq7928 eq54 | exact resolve eq54 eq7928 | grind only

private theorem step_2_eq8717 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq296 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq8027 : c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := by
  first | exact superpose eq296 eq8027 | exact superpose eq8027 eq296 | grind only

private theorem step_2_eq8957 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq8717 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := by
  first | exact resolve eq8717 rfl | grind only

private theorem step_2_eq9039 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq8957 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk1 ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq8957 eq56 | exact resolve eq56 eq8957 | grind only

private theorem step_2_eq9105 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq93 : (new sk1 sk0 sk2)) (eq9039 : a = sk1 ∨ c = sk1 ∨ b = sk1) : (new a sk0 sk2) ∨ c = sk1 ∨ b = sk1 := by
  first | exact superpose eq93 eq9039 | exact superpose eq9039 eq93 | grind only

private theorem step_2_eq9708 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq9105 : (new a sk0 sk2) ∨ c = sk1 ∨ b = sk1) (eq7490 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : (new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq9105 eq7490 | exact superpose eq7490 eq9105 | grind only

private theorem step_2_eq9711 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq9708 : (new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : (new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq9708 rfl | grind only

private theorem step_2_eq11664 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq7580 : ¬(new sk3 sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) (eq7985 : a = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : ¬(new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact superpose eq7580 eq7985 | exact superpose eq7985 eq7580 | grind only

private theorem step_2_eq11669 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq11664 : ¬(new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : ¬(new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq11664 rfl | grind only

private theorem step_2_eq11670 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq11669 : ¬(new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) (eq9711 : (new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0) : c = sk0 ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq11669 eq9711 | exact resolve eq9711 eq11669 | grind only

private theorem step_2_eq11710 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq297 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b)) (eq11670 : c = sk0 ∨ b = sk1 ∨ c = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq297 eq11670 | exact superpose eq11670 eq297 | grind only

private theorem step_2_eq11932 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq11710 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk1 ∨ c = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk1 := by
  first | exact resolve eq11710 rfl | grind only

private theorem step_2_eq11995 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq11932 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : (old sk1 b b) ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq11932 eq56 | exact resolve eq56 eq11932 | grind only

private theorem step_2_eq12792 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq11995 : (old sk1 b b) ∨ c = sk1 ∨ b = sk1) (eq9039 : a = sk1 ∨ c = sk1 ∨ b = sk1) : (old a b b) ∨ a = c ∨ a = b ∨ c = sk1 ∨ b = sk1 := by
  first | exact superpose eq11995 eq9039 | exact superpose eq9039 eq11995 | grind only

private theorem step_2_eq12795 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq12792 : (old a b b) ∨ a = c ∨ a = b ∨ c = sk1 ∨ b = sk1) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : a = c ∨ a = b ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq12792 eq51 | exact resolve eq51 eq12792 | grind only

private theorem step_2_eq12796 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} (eq12795 : a = c ∨ a = b ∨ c = sk1 ∨ b = sk1) (eq49 : a ≠ c) : a = b ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq12795 eq49 | exact resolve eq49 eq12795 | grind only

private theorem step_2_eq12797 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} (eq12796 : a = b ∨ c = sk1 ∨ b = sk1) (eq47 : a ≠ b) : c = sk1 ∨ b = sk1 := by
  first | exact resolve eq12796 eq47 | exact resolve eq47 eq12796 | grind only

private theorem step_2_eq12814 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq93 : (new sk1 sk0 sk2)) (eq12797 : c = sk1 ∨ b = sk1) : (new c sk0 sk2) ∨ b = sk1 := by
  first | exact superpose eq93 eq12797 | exact superpose eq12797 eq93 | grind only

private theorem step_2_eq12824 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq174 : (old sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0) (eq12797 : c = sk1 ∨ b = sk1) : (old sk0 c c) ∨ b = c ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq174 eq12797 | exact superpose eq12797 eq174 | grind only

private theorem step_2_eq12851 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq418 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2) (eq12797 : c = sk1 ∨ b = sk1) : (sP1 c sk0 sk2) ∨ (old c sk0 sk2) ∨ a = c ∨ a = sk2 ∨ b = sk1 := by
  first | exact superpose eq418 eq12797 | exact superpose eq12797 eq418 | grind only

private theorem step_2_eq12944 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1064 : (old sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a)) (eq12797 : c = sk1 ∨ b = sk1) : (old sk2 c sk3) ∨ b = c ∨ b = sk3 ∨ (old b c a) ∨ b = sk1 := by
  first | exact superpose eq1064 eq12797 | exact superpose eq12797 eq1064 | grind only

private theorem step_2_eq13124 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq12944 : (old sk2 c sk3) ∨ b = c ∨ b = sk3 ∨ (old b c a) ∨ b = sk1) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk2 c sk3) ∨ b = c ∨ b = sk3 ∨ b = sk1 := by
  first | exact resolve eq12944 eq55 | exact resolve eq55 eq12944 | grind only

private theorem step_2_eq13179 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq12851 : (sP1 c sk0 sk2) ∨ (old c sk0 sk2) ∨ a = c ∨ a = sk2 ∨ b = sk1) (eq122 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1)) : (old c sk0 sk2) ∨ a = c ∨ a = sk2 ∨ b = sk1 := by
  first | exact resolve eq12851 eq122 | exact resolve eq122 eq12851 | grind only

private theorem step_2_eq13197 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq12824 : (old sk0 c c) ∨ b = c ∨ c = sk0 ∨ b = sk1) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0) : b = c ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq12824 eq53 | exact resolve eq53 eq12824 | grind only

private theorem step_2_eq13230 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq13124 : (old sk2 c sk3) ∨ b = c ∨ b = sk3 ∨ b = sk1) (eq50 : b ≠ c) : (old sk2 c sk3) ∨ b = sk3 ∨ b = sk1 := by
  first | exact resolve eq13124 eq50 | exact resolve eq50 eq13124 | grind only

private theorem step_2_eq13237 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq13179 : (old c sk0 sk2) ∨ a = c ∨ a = sk2 ∨ b = sk1) (eq49 : a ≠ c) : (old c sk0 sk2) ∨ a = sk2 ∨ b = sk1 := by
  first | exact resolve eq13179 eq49 | exact resolve eq49 eq13179 | grind only

private theorem step_2_eq13249 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} (eq13197 : b = c ∨ c = sk0 ∨ b = sk1) (eq50 : b ≠ c) : c = sk0 ∨ b = sk1 := by
  first | exact resolve eq13197 eq50 | exact resolve eq50 eq13197 | grind only

private theorem step_2_eq13272 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq95 : ¬(new sk3 sk0 sk2)) (eq13249 : c = sk0 ∨ b = sk1) : ¬(new sk3 c sk2) ∨ b = sk1 := by
  first | exact superpose eq95 eq13249 | exact superpose eq13249 eq95 | grind only

private theorem step_2_eq13367 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq995 : (old sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a)) (eq13249 : c = sk0 ∨ b = sk1) : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ (old b c a) ∨ b = sk1 := by
  first | exact superpose eq995 eq13249 | exact superpose eq13249 eq995 | grind only

private theorem step_2_eq13501 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq13367 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ (old b c a) ∨ b = sk1) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ b = sk1 := by
  first | exact resolve eq13367 eq55 | exact resolve eq55 eq13367 | grind only

private theorem step_2_eq13534 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq13501 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ b = sk1) (eq50 : b ≠ c) : (old sk1 c sk2) ∨ b = sk2 ∨ b = sk1 := by
  first | exact resolve eq13501 eq50 | exact resolve eq50 eq13501 | grind only

private theorem step_2_eq13577 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq12814 : (new c sk0 sk2) ∨ b = sk1) (eq13249 : c = sk0 ∨ b = sk1) : (new c c sk2) ∨ b = sk1 ∨ b = sk1 := by
  first | exact superpose eq12814 eq13249 | exact superpose eq13249 eq12814 | grind only

private theorem step_2_eq13595 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq13577 : (new c c sk2) ∨ b = sk1 ∨ b = sk1) : (new c c sk2) ∨ b = sk1 := by
  first | exact resolve eq13577 rfl | grind only

private theorem step_2_eq15216 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq13230 : (old sk2 c sk3) ∨ b = sk3 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : c = sk3 ∨ b = sk1 ∨ b = sk3 := by
  first | exact resolve eq13230 eq54 | exact resolve eq54 eq13230 | grind only

private theorem step_2_eq15388 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq13272 : ¬(new sk3 c sk2) ∨ b = sk1) (eq15216 : c = sk3 ∨ b = sk1 ∨ b = sk3) : ¬(new c c sk2) ∨ b = sk1 ∨ b = sk1 ∨ b = sk3 := by
  first | exact superpose eq13272 eq15216 | exact superpose eq15216 eq13272 | grind only

private theorem step_2_eq15390 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq15388 : ¬(new c c sk2) ∨ b = sk1 ∨ b = sk1 ∨ b = sk3) : ¬(new c c sk2) ∨ b = sk1 ∨ b = sk3 := by
  first | exact resolve eq15388 rfl | grind only

private theorem step_2_eq15457 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq15390 : ¬(new c c sk2) ∨ b = sk1 ∨ b = sk3) (eq13595 : (new c c sk2) ∨ b = sk1) : b = sk3 ∨ b = sk1 := by
  first | exact resolve eq15390 eq13595 | exact resolve eq13595 eq15390 | grind only

private theorem step_2_eq15981 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq13237 : (old c sk0 sk2) ∨ a = sk2 ∨ b = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk2 ∨ b = sk1 ∨ c = sk2 := by
  first | exact resolve eq13237 eq56 | exact resolve eq56 eq13237 | grind only

private theorem step_2_eq16591 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq13534 : (old sk1 c sk2) ∨ b = sk2 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : c = sk2 ∨ b = sk1 ∨ b = sk2 := by
  first | exact resolve eq13534 eq54 | exact resolve eq54 eq13534 | grind only

private theorem step_2_eq16633 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq16591 : c = sk2 ∨ b = sk1 ∨ b = sk2) (eq15981 : a = sk2 ∨ b = sk1 ∨ c = sk2) : a = c ∨ b = sk1 ∨ a = b ∨ b = sk1 ∨ c = sk2 := by
  first | exact superpose eq16591 eq15981 | exact superpose eq15981 eq16591 | grind only

private theorem step_2_eq17007 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq16633 : a = c ∨ b = sk1 ∨ a = b ∨ b = sk1 ∨ c = sk2) : a = c ∨ b = sk1 ∨ a = b ∨ c = sk2 := by
  first | exact resolve eq16633 rfl | grind only

private theorem step_2_eq17062 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq17007 : a = c ∨ b = sk1 ∨ a = b ∨ c = sk2) (eq49 : a ≠ c) : b = sk1 ∨ a = b ∨ c = sk2 := by
  first | exact resolve eq17007 eq49 | exact resolve eq49 eq17007 | grind only

private theorem step_2_eq17078 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq17062 : b = sk1 ∨ a = b ∨ c = sk2) (eq47 : a ≠ b) : c = sk2 ∨ b = sk1 := by
  first | exact resolve eq17062 eq47 | exact resolve eq47 eq17062 | grind only

private theorem step_2_eq17124 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq431 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ a = sk3) (eq17078 : c = sk2 ∨ b = sk1) : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ b = sk1 := by
  first | exact superpose eq431 eq17078 | exact superpose eq17078 eq431 | grind only

private theorem step_2_eq17534 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq17124 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ b = sk1) (eq122 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1)) : (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ b = sk1 := by
  first | exact resolve eq17124 eq122 | exact resolve eq122 eq17124 | grind only

private theorem step_2_eq17553 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq17534 : (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ b = sk1) (eq49 : a ≠ c) : (old c sk1 sk3) ∨ a = sk3 ∨ b = sk1 := by
  first | exact resolve eq17534 eq49 | exact resolve eq49 eq17534 | grind only

private theorem step_2_eq20891 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq17553 : (old c sk1 sk3) ∨ a = sk3 ∨ b = sk1) (eq15457 : b = sk3 ∨ b = sk1) : (old c sk1 b) ∨ a = b ∨ b = sk1 ∨ b = sk1 := by
  first | exact superpose eq17553 eq15457 | exact superpose eq15457 eq17553 | grind only

private theorem step_2_eq20897 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq20891 : (old c sk1 b) ∨ a = b ∨ b = sk1 ∨ b = sk1) : (old c sk1 b) ∨ a = b ∨ b = sk1 := by
  first | exact resolve eq20891 rfl | grind only

private theorem step_2_eq20914 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq20897 : (old c sk1 b) ∨ a = b ∨ b = sk1) (eq47 : a ≠ b) : (old c sk1 b) ∨ b = sk1 := by
  first | exact resolve eq20897 eq47 | exact resolve eq47 eq20897 | grind only

private theorem step_2_eq20945 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq20914 : (old c sk1 b) ∨ b = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : b = sk1 ∨ b = c := by
  first | exact resolve eq20914 eq56 | exact resolve eq56 eq20914 | grind only

private theorem step_2_eq21003 {G : Type*} {b : G} {c : G} {sk1 : G} (eq20945 : b = sk1 ∨ b = c) (eq50 : b ≠ c) : b = sk1 := by
  first | exact resolve eq20945 eq50 | exact resolve eq50 eq20945 | grind only

private theorem step_2_eq21051 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq295 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0) (eq21003 : b = sk1) : (old sk0 b b) ∨ b = c ∨ c = sk0 := by
  first | exact superpose eq295 eq21003 | exact superpose eq21003 eq295 | grind only

private theorem step_2_eq21052 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq296 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq21003 : b = sk1) : (old sk0 b b) ∨ b = c ∨ a = b := by
  first | exact superpose eq296 eq21003 | exact superpose eq21003 eq296 | grind only

private theorem step_2_eq21108 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq499 : ¬(old b sk1 sk1) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1) (eq21003 : b = sk1) : ¬(old b b b) ∨ (old b sk0 sk2) ∨ a = b ∨ b = c := by
  first | exact superpose eq499 eq21003 | exact superpose eq21003 eq499 | grind only

private theorem step_2_eq21405 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq6026 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0) (eq21003 : b = sk1) : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq6026 eq21003 | exact superpose eq21003 eq6026 | grind only

private theorem step_2_eq21407 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq6035 : (old sk1 sk0 a) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq21003 : b = sk1) : (old b sk0 a) ∨ c = sk0 ∨ b = c ∨ c = sk2 := by
  first | exact superpose eq6035 eq21003 | exact superpose eq21003 eq6035 | grind only

private theorem step_2_eq21435 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21407 : (old b sk0 a) ∨ c = sk0 ∨ b = c ∨ c = sk2) (eq50 : b ≠ c) : (old b sk0 a) ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq21407 eq50 | exact resolve eq50 eq21407 | grind only

private theorem step_2_eq21437 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq21405 : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk2 ∨ c = sk0) (eq51 : ∀ (X0 : G), ¬(old a b X0)) : c = sk3 ∨ b = c ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq21405 eq51 | exact resolve eq51 eq21405 | grind only

private theorem step_2_eq21595 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21108 : ¬(old b b b) ∨ (old b sk0 sk2) ∨ a = b ∨ b = c) (eq48 : ∀ (X0 : G), (old X0 X0 X0)) : (old b sk0 sk2) ∨ a = b ∨ b = c := by
  first | exact resolve eq21108 eq48 | exact resolve eq48 eq21108 | grind only

private theorem step_2_eq21631 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq21052 : (old sk0 b b) ∨ b = c ∨ a = b) (eq50 : b ≠ c) : (old sk0 b b) ∨ a = b := by
  first | exact resolve eq21052 eq50 | exact resolve eq50 eq21052 | grind only

private theorem step_2_eq21632 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq21051 : (old sk0 b b) ∨ b = c ∨ c = sk0) (eq50 : b ≠ c) : (old sk0 b b) ∨ c = sk0 := by
  first | exact resolve eq21051 eq50 | exact resolve eq50 eq21051 | grind only

private theorem step_2_eq21635 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq21437 : c = sk3 ∨ b = c ∨ c = sk2 ∨ c = sk0) (eq50 : b ≠ c) : c = sk3 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq21437 eq50 | exact resolve eq50 eq21437 | grind only

private theorem step_2_eq21658 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21595 : (old b sk0 sk2) ∨ a = b ∨ b = c) (eq47 : a ≠ b) : (old b sk0 sk2) ∨ b = c := by
  first | exact resolve eq21595 eq47 | exact resolve eq47 eq21595 | grind only

private theorem step_2_eq21680 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sk0 : G} (eq21631 : (old sk0 b b) ∨ a = b) (eq47 : a ≠ b) : (old sk0 b b) := by
  first | exact resolve eq21631 eq47 | exact resolve eq47 eq21631 | grind only

private theorem step_2_eq21682 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21658 : (old b sk0 sk2) ∨ b = c) (eq50 : b ≠ c) : (old b sk0 sk2) := by
  first | exact resolve eq21658 eq50 | exact resolve eq50 eq21658 | grind only

private theorem step_2_eq21865 {G : Type*} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21682 : (old b sk0 sk2)) (eq61 : ∀ (X0 X1 X2 : G), ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0)) : ¬(old sk0 b b) ∨ (old b sk2 sk0) := by
  first | exact resolve eq21682 eq61 | exact resolve eq61 eq21682 | grind only

private theorem step_2_eq21885 {G : Type*} {b : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21865 : ¬(old sk0 b b) ∨ (old b sk2 sk0)) (eq21680 : (old sk0 b b)) : (old b sk2 sk0) := by
  first | exact resolve eq21865 eq21680 | exact resolve eq21680 eq21865 | grind only

private theorem step_2_eq23423 {G : Type*} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq95 : ¬(new sk3 sk0 sk2)) (eq21635 : c = sk3 ∨ c = sk2 ∨ c = sk0) : ¬(new c sk0 sk2) ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq95 eq21635 | exact superpose eq21635 eq95 | grind only

private theorem step_2_eq23435 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq555 : (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 ∨ b = sk3) (eq21635 : c = sk3 ∨ c = sk2 ∨ c = sk0) : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq555 eq21635 | exact superpose eq21635 eq555 | grind only

private theorem step_2_eq23627 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq23435 : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk2 ∨ c = sk0) : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq23435 rfl | grind only

private theorem step_2_eq23649 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq23627 : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk0) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0) : a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq23627 eq53 | exact resolve eq53 eq23627 | grind only

private theorem step_2_eq23666 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq23649 : a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk0) (eq50 : b ≠ c) : a = sk2 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq23649 eq50 | exact resolve eq50 eq23649 | grind only

private theorem step_2_eq24378 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21435 : (old b sk0 a) ∨ c = sk0 ∨ c = sk2) (eq108 : ∀ (X1 : G), ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ (new c X1 a)) : c = sk0 ∨ c = sk2 ∨ ¬(old sk0 b b) ∨ (new c sk0 a) := by
  first | exact resolve eq21435 eq108 | exact resolve eq108 eq21435 | grind only

private theorem step_2_eq24422 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq24378 : c = sk0 ∨ c = sk2 ∨ ¬(old sk0 b b) ∨ (new c sk0 a)) (eq21632 : (old sk0 b b) ∨ c = sk0) : c = sk0 ∨ c = sk2 ∨ (new c sk0 a) := by
  first | exact resolve eq24378 eq21632 | exact resolve eq21632 eq24378 | grind only

private theorem step_2_eq25675 {G : Type*} {a : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq23423 : ¬(new c sk0 sk2) ∨ c = sk2 ∨ c = sk0) (eq23666 : a = sk2 ∨ c = sk2 ∨ c = sk0) : ¬(new c sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq23423 eq23666 | exact superpose eq23666 eq23423 | grind only

private theorem step_2_eq25676 {G : Type*} {a : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq25675 : ¬(new c sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk2 ∨ c = sk0) : ¬(new c sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq25675 rfl | grind only

private theorem step_2_eq25679 {G : Type*} {a : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq25676 : ¬(new c sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk2) (eq24422 : c = sk0 ∨ c = sk2 ∨ (new c sk0 a)) : a = c ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq25676 eq24422 | exact resolve eq24422 eq25676 | grind only

private theorem step_2_eq25680 {G : Type*} {a : G} {c : G} {sk0 : G} {sk2 : G} (eq25679 : a = c ∨ c = sk0 ∨ c = sk2) (eq49 : a ≠ c) : c = sk2 ∨ c = sk0 := by
  first | exact resolve eq25679 eq49 | exact resolve eq49 eq25679 | grind only

private theorem step_2_eq26094 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq21885 : (old b sk2 sk0)) (eq25680 : c = sk2 ∨ c = sk0) : (old b c sk0) ∨ c = sk0 := by
  first | exact superpose eq21885 eq25680 | exact superpose eq25680 eq21885 | grind only

private theorem step_2_eq26171 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq26094 : (old b c sk0) ∨ c = sk0) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : c = sk0 := by
  first | exact resolve eq26094 eq54 | exact resolve eq54 eq26094 | grind only

private theorem step_2_eq26372 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq296 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq26171 : c = sk0) : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 := by
  first | exact superpose eq296 eq26171 | exact superpose eq26171 eq296 | grind only

private theorem step_2_eq26743 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq26372 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk1 ∨ a = sk1 := by
  first | exact resolve eq26372 eq56 | exact resolve eq56 eq26372 | grind only

private theorem step_2_eq26850 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} (eq26743 : c = sk1 ∨ a = sk1) (eq21003 : b = sk1) : b = c ∨ a = sk1 := by
  first | simpa only [eq21003, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq26743 | grind only

private theorem step_2_eq26928 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} (eq26850 : b = c ∨ a = sk1) (eq50 : b ≠ c) : a = sk1 := by
  first | exact resolve eq26850 eq50 | exact resolve eq50 eq26850 | grind only

private theorem step_2_eq26985 {G : Type*} {a : G} {b : G} {sk1 : G} (eq26928 : a = sk1) (eq21003 : b = sk1) : a = b := by
  first | simpa only [eq21003, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq26928 | grind only

set_option maxHeartbeats 2000000 in
private theorem preserve_2 (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (ab : a ≠ b) (diagonal : ∀ x, old x x x) (ac : a ≠ c) (bc : b ≠ c) (p3 : ∀ z, ¬ old a b z) (p4XY : ∀ x y, old x y c → x = c ∧ y = c) (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ ¬ old X2 X1 X3 ∨ old X3 X0 X2)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ old X1 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) (imp_new_5 : ∀ X Y Z, c ≠ X ∨ a ≠ Z ∨ ¬ old b Y a ∨ ¬ old Y b b ∨ ¬ old b Y a ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X1 ∨ ¬ new X1 X0 X2 ∨ ¬ new X2 X1 X3 ∨ new X3 X0 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq47 : a ≠ b := step_2_eq47 ab
  have eq48 (X0 : G) : (old X0 X0 X0) := step_2_eq48 diagonal X0
  have eq49 : a ≠ c := step_2_eq49 ac
  have eq50 : b ≠ c := step_2_eq50 bc
  have eq51 (X0 : G) : ¬(old a b X0) := step_2_eq51 p3 X0
  have eq52 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X1 := step_2_eq52 p4XY X0 X1
  have eq53 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X0 := step_2_eq53 p4XY X0 X1
  have eq54 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X1 := step_2_eq54 p4XZ X0 X1
  have eq55 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X0 := step_2_eq55 p4XZ X0 X1
  have eq56 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X1 := step_2_eq56 p4YZ X0 X1
  have eq57 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X0 := step_2_eq57 p4YZ X0 X1
  have eq60 (X0 X1 X2 X3 : G) : ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2) := step_2_eq60 old_2 X0 X1 X2 X3
  have eq61 (X0 X1 X2 : G) : ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0) := step_2_eq61 old_3 X0 X1 X2
  have eq64 (X0 X1 X2 : G) : ¬(old X0 X1 X2) ∨ (new X0 X1 X2) := step_2_eq64 imp_new_0 X0 X1 X2
  have eq66 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ a = X0 := step_2_eq66 rule_def_0_0 X0 X1 X2
  have eq67 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ b = X1 := step_2_eq67 rule_def_0_1 X0 X1 X2
  have eq68 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ c = X2 := step_2_eq68 rule_def_0_2 X0 X1 X2
  have eq70 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ c = X1 := step_2_eq70 rule_def_1_0 X0 X1 X2
  have eq71 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ b = X2 := step_2_eq71 rule_def_1_1 X0 X1 X2
  have eq72 (X0 X1 X2 : G) : (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := step_2_eq72 rule_def_1_2 X0 X1 X2
  have eq73 (X0 X1 X2 : G) : (old (sF0 X0 X1 X2) X0 a) ∨ ¬(sP1 X0 X1 X2) := step_2_eq73 rule_def_1_3 X0 X1 X2
  have eq75 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ c = X0 := step_2_eq75 rule_def_2_0 X0 X1 X2
  have eq76 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = X2 := step_2_eq76 rule_def_2_1 X0 X1 X2
  have eq77 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := step_2_eq77 rule_def_2_2 X0 X1 X2
  have eq78 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := step_2_eq78 rule_def_2_3 X0 X1 X2
  have eq80 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = X0 := step_2_eq80 rule_def_3_0 X0 X1 X2
  have eq81 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ c = X1 := step_2_eq81 rule_def_3_1 X0 X1 X2
  have eq82 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ b = X2 := step_2_eq82 rule_def_3_2 X0 X1 X2
  have eq84 (X0 X1 X2 : G) : c ≠ X0 ∨ a ≠ X2 ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new X0 X1 X2) := step_2_eq84 imp_new_5 X0 X1 X2
  have eq85 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ c = X0 := step_2_eq85 rule_def_4_0 X0 X1 X2
  have eq86 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = X2 := step_2_eq86 rule_def_4_1 X0 X1 X2
  have eq88 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := step_2_eq88 rule_def_4_3 X0 X1 X2
  have eq89 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := step_2_eq89 rule_def_4_4 X0 X1 X2
  have eq91 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := step_2_eq91 new_imp X0 X1 X2
  have eq92 : (new sk0 sk1 sk1) := step_2_eq92 preserve_0
  have eq93 : (new sk1 sk0 sk2) := step_2_eq93 preserve_1
  have eq94 : (new sk2 sk1 sk3) := step_2_eq94 preserve_2
  have eq95 : ¬(new sk3 sk0 sk2) := step_2_eq95 preserve_3
  have eq106 (X1 X2 : G) : a ≠ X2 ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 X2) := step_2_eq106 eq84 X1 X2
  have eq107 (X1 : G) : ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 a) := step_2_eq107 eq106 X1
  have eq108 (X1 : G) : ¬(old b X1 a) ∨ ¬(old X1 b b) ∨ (new c X1 a) := step_2_eq108 eq107 X1
  have eq120 (X0 X1 : G) : ¬(sP1 c X0 X1) ∨ b = c := step_2_eq120 eq72 eq57 X0 X1
  have eq122 (X0 X1 : G) : ¬(sP1 c X0 X1) := step_2_eq122 eq120 eq50 X0 X1
  have eq140 (X0 X1 X2 X3 : G) : ¬(old X0 X1 (sF0 X0 X2 X3)) ∨ ¬(old X1 X0 X0) ∨ (old a X1 (sF0 X0 X2 X3)) ∨ ¬(sP1 X0 X2 X3) := step_2_eq140 eq60 eq73 X0 X1 X2 X3
  have eq153 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) := step_2_eq153 eq91 eq92
  have eq154 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) := step_2_eq154 eq91 eq93
  have eq155 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) := step_2_eq155 eq91 eq94
  have eq158 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := step_2_eq158 eq153 eq68
  have eq159 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := step_2_eq159 eq153 eq67
  have eq162 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := step_2_eq162 eq159 eq71
  have eq163 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := step_2_eq163 eq158 eq70
  have eq164 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := step_2_eq164 eq162 eq82
  have eq165 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := step_2_eq165 eq163 eq81
  have eq166 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 := step_2_eq166 eq154 eq68
  have eq167 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 := step_2_eq167 eq154 eq67
  have eq168 : (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := step_2_eq168 eq154 eq66
  have eq169 : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := step_2_eq169 eq168 eq80
  have eq173 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := step_2_eq173 eq164 eq75
  have eq174 : (old sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := step_2_eq174 eq173 eq85
  have eq178 : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 := step_2_eq178 eq155 eq68
  have eq179 : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 := step_2_eq179 eq155 eq67
  have eq180 : (old sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 := step_2_eq180 eq155 eq66
  have eq181 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 := step_2_eq181 eq180 eq80
  have eq292 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := step_2_eq292 eq165 eq77
  have eq293 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := step_2_eq293 eq165 eq76
  have eq294 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := step_2_eq294 eq165 eq75
  have eq295 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := step_2_eq295 eq294 eq85
  have eq296 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := step_2_eq296 eq293 eq86
  have eq297 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := step_2_eq297 eq292 eq88
  have eq339 (X0 X1 X2 : G) : ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := step_2_eq339 eq140 eq72 X0 X1 X2
  have eq340 (X0 X1 X2 : G) : ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := step_2_eq340 eq339 X0 X1 X2
  have eq341 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old b X0 X0) := step_2_eq341 eq340 eq51 X0 X1 X2
  have eq415 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := step_2_eq415 eq169 eq76
  have eq416 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := step_2_eq416 eq169 eq75
  have eq417 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := step_2_eq417 eq416 eq85
  have eq418 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := step_2_eq418 eq415 eq86
  have eq428 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 ∨ a = sk3 := step_2_eq428 eq181 eq76
  have eq429 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 := step_2_eq429 eq181 eq75
  have eq430 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 := step_2_eq430 eq429 eq85
  have eq431 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ a = sk3 := step_2_eq431 eq428 eq86
  have eq441 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := step_2_eq441 eq166 eq81
  have eq443 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := step_2_eq443 eq441 eq70
  have eq449 : (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := step_2_eq449 eq417 eq70
  have eq451 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := step_2_eq451 eq167 eq82
  have eq455 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := step_2_eq455 eq451 eq71
  have eq468 : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := step_2_eq468 eq178 eq81
  have eq470 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := step_2_eq470 eq468 eq70
  have eq475 : a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0) := step_2_eq475 eq449 eq61
  have eq481 : (old sk1 sk2 sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := step_2_eq481 eq475 eq296
  have eq483 : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := step_2_eq483 eq179 eq82
  have eq484 : (sP1 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := step_2_eq484 eq179 eq81
  have eq486 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := step_2_eq486 eq484 eq70
  have eq487 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := step_2_eq487 eq483 eq71
  have eq499 : ¬(old b sk1 sk1) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := step_2_eq499 eq341 eq417
  have eq554 : (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 ∨ c = sk1 := step_2_eq554 eq430 eq70
  have eq555 : (old sk2 sk1 sk3) ∨ a = sk2 ∨ c = sk2 ∨ b = sk3 := step_2_eq555 eq430 eq71
  have eq569 (X0 : G) : ¬(old sk1 X0 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old X0 sk1 sk1) ∨ (old sk3 X0 sk2) := step_2_eq569 eq554 eq60 X0
  have eq938 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := step_2_eq938 eq443 eq76
  have eq939 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := step_2_eq939 eq443 eq75
  have eq940 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := step_2_eq940 eq939 eq85
  have eq941 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := step_2_eq941 eq938 eq86
  have eq988 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := step_2_eq988 eq455 eq78
  have eq995 : (old sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := step_2_eq995 eq988 eq89
  have eq1008 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := step_2_eq1008 eq470 eq75
  have eq1009 : (old sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := step_2_eq1009 eq1008 eq85
  have eq1042 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 := step_2_eq1042 eq486 eq76
  have eq1043 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_2_eq1043 eq486 eq75
  have eq1044 : (old sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_2_eq1044 eq1043 eq85
  have eq1045 : (old sk2 sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 := step_2_eq1045 eq1042 eq86
  have eq1057 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := step_2_eq1057 eq487 eq78
  have eq1064 : (old sk2 sk1 sk3) ∨ b = sk1 ∨ b = sk3 ∨ (old b sk1 a) := step_2_eq1064 eq1057 eq89
  have eq1084 (X0 : G) : ¬(old sk1 X0 sk2) ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old X0 sk1 sk1) ∨ (old sk3 X0 sk2) := step_2_eq1084 eq1009 eq60 X0
  have eq5605 : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := step_2_eq5605 eq569 eq941
  have eq5624 : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk0 := step_2_eq5624 eq5605
  have eq5634 : (old sk3 sk0 sk2) ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 := step_2_eq5634 eq5624 eq295
  have eq5652 : c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ (new sk3 sk0 sk2) := step_2_eq5652 eq5634 eq64
  have eq5664 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq5664 eq5652 eq95
  have eq5708 : (old sk1 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq5708 eq940 eq5664
  have eq5719 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq5719 eq1009 eq5664
  have eq5729 : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq5729 eq1044 eq5664
  have eq5927 : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk2 ∨ c = sk0 := step_2_eq5927 eq5729
  have eq5933 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ c = sk2 ∨ c = sk0 := step_2_eq5933 eq5719
  have eq5942 : (old sk1 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_2_eq5942 eq5708
  have eq6024 : (old a sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq6024 eq5927 eq49
  have eq6026 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq6026 eq5933 eq49
  have eq6035 : (old sk1 sk0 a) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_2_eq6035 eq5942 eq49
  have eq7290 : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := step_2_eq7290 eq1084 eq940
  have eq7311 : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk3 sk0 sk2) ∨ c = sk0 := step_2_eq7311 eq7290
  have eq7317 : (old sk3 sk0 sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := step_2_eq7317 eq7311 eq295
  have eq7341 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ (new sk3 sk0 sk2) := step_2_eq7341 eq7317 eq64
  have eq7359 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_2_eq7359 eq7341 eq95
  have eq7436 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_2_eq7436 eq6024 eq7359
  have eq7442 : (old a sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := step_2_eq7442 eq7436
  have eq7490 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq7490 eq7442 eq52
  have eq7580 : ¬(new sk3 sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq7580 eq95 eq7490
  have eq7608 : (old sk1 c sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq7608 eq481 eq7490
  have eq7677 : (old c sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq7677 eq1045 eq7490
  have eq7891 : (old c sk1 sk3) ∨ b = sk1 ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 := step_2_eq7891 eq7677
  have eq7928 : (old sk1 c sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk1 := step_2_eq7928 eq7608
  have eq7985 : a = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq7985 eq7891 eq57
  have eq8027 : c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := step_2_eq8027 eq7928 eq54
  have eq8717 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := step_2_eq8717 eq296 eq8027
  have eq8957 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := step_2_eq8957 eq8717
  have eq9039 : a = sk1 ∨ c = sk1 ∨ b = sk1 := step_2_eq9039 eq8957 eq56
  have eq9105 : (new a sk0 sk2) ∨ c = sk1 ∨ b = sk1 := step_2_eq9105 eq93 eq9039
  have eq9708 : (new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq9708 eq9105 eq7490
  have eq9711 : (new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq9711 eq9708
  have eq11664 : ¬(new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq11664 eq7580 eq7985
  have eq11669 : ¬(new a sk0 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := step_2_eq11669 eq11664
  have eq11670 : c = sk0 ∨ b = sk1 ∨ c = sk1 := step_2_eq11670 eq11669 eq9711
  have eq11710 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk1 ∨ c = sk1 := step_2_eq11710 eq297 eq11670
  have eq11932 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk1 := step_2_eq11932 eq11710
  have eq11995 : (old sk1 b b) ∨ c = sk1 ∨ b = sk1 := step_2_eq11995 eq11932 eq56
  have eq12792 : (old a b b) ∨ a = c ∨ a = b ∨ c = sk1 ∨ b = sk1 := step_2_eq12792 eq11995 eq9039
  have eq12795 : a = c ∨ a = b ∨ c = sk1 ∨ b = sk1 := step_2_eq12795 eq12792 eq51
  have eq12796 : a = b ∨ c = sk1 ∨ b = sk1 := step_2_eq12796 eq12795 eq49
  have eq12797 : c = sk1 ∨ b = sk1 := step_2_eq12797 eq12796 eq47
  have eq12814 : (new c sk0 sk2) ∨ b = sk1 := step_2_eq12814 eq93 eq12797
  have eq12824 : (old sk0 c c) ∨ b = c ∨ c = sk0 ∨ b = sk1 := step_2_eq12824 eq174 eq12797
  have eq12851 : (sP1 c sk0 sk2) ∨ (old c sk0 sk2) ∨ a = c ∨ a = sk2 ∨ b = sk1 := step_2_eq12851 eq418 eq12797
  have eq12944 : (old sk2 c sk3) ∨ b = c ∨ b = sk3 ∨ (old b c a) ∨ b = sk1 := step_2_eq12944 eq1064 eq12797
  have eq13124 : (old sk2 c sk3) ∨ b = c ∨ b = sk3 ∨ b = sk1 := step_2_eq13124 eq12944 eq55
  have eq13179 : (old c sk0 sk2) ∨ a = c ∨ a = sk2 ∨ b = sk1 := step_2_eq13179 eq12851 eq122
  have eq13197 : b = c ∨ c = sk0 ∨ b = sk1 := step_2_eq13197 eq12824 eq53
  have eq13230 : (old sk2 c sk3) ∨ b = sk3 ∨ b = sk1 := step_2_eq13230 eq13124 eq50
  have eq13237 : (old c sk0 sk2) ∨ a = sk2 ∨ b = sk1 := step_2_eq13237 eq13179 eq49
  have eq13249 : c = sk0 ∨ b = sk1 := step_2_eq13249 eq13197 eq50
  have eq13272 : ¬(new sk3 c sk2) ∨ b = sk1 := step_2_eq13272 eq95 eq13249
  have eq13367 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ (old b c a) ∨ b = sk1 := step_2_eq13367 eq995 eq13249
  have eq13501 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ b = sk1 := step_2_eq13501 eq13367 eq55
  have eq13534 : (old sk1 c sk2) ∨ b = sk2 ∨ b = sk1 := step_2_eq13534 eq13501 eq50
  have eq13577 : (new c c sk2) ∨ b = sk1 ∨ b = sk1 := step_2_eq13577 eq12814 eq13249
  have eq13595 : (new c c sk2) ∨ b = sk1 := step_2_eq13595 eq13577
  have eq15216 : c = sk3 ∨ b = sk1 ∨ b = sk3 := step_2_eq15216 eq13230 eq54
  have eq15388 : ¬(new c c sk2) ∨ b = sk1 ∨ b = sk1 ∨ b = sk3 := step_2_eq15388 eq13272 eq15216
  have eq15390 : ¬(new c c sk2) ∨ b = sk1 ∨ b = sk3 := step_2_eq15390 eq15388
  have eq15457 : b = sk3 ∨ b = sk1 := step_2_eq15457 eq15390 eq13595
  have eq15981 : a = sk2 ∨ b = sk1 ∨ c = sk2 := step_2_eq15981 eq13237 eq56
  have eq16591 : c = sk2 ∨ b = sk1 ∨ b = sk2 := step_2_eq16591 eq13534 eq54
  have eq16633 : a = c ∨ b = sk1 ∨ a = b ∨ b = sk1 ∨ c = sk2 := step_2_eq16633 eq16591 eq15981
  have eq17007 : a = c ∨ b = sk1 ∨ a = b ∨ c = sk2 := step_2_eq17007 eq16633
  have eq17062 : b = sk1 ∨ a = b ∨ c = sk2 := step_2_eq17062 eq17007 eq49
  have eq17078 : c = sk2 ∨ b = sk1 := step_2_eq17078 eq17062 eq47
  have eq17124 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ b = sk1 := step_2_eq17124 eq431 eq17078
  have eq17534 : (old c sk1 sk3) ∨ a = c ∨ a = sk3 ∨ b = sk1 := step_2_eq17534 eq17124 eq122
  have eq17553 : (old c sk1 sk3) ∨ a = sk3 ∨ b = sk1 := step_2_eq17553 eq17534 eq49
  have eq20891 : (old c sk1 b) ∨ a = b ∨ b = sk1 ∨ b = sk1 := step_2_eq20891 eq17553 eq15457
  have eq20897 : (old c sk1 b) ∨ a = b ∨ b = sk1 := step_2_eq20897 eq20891
  have eq20914 : (old c sk1 b) ∨ b = sk1 := step_2_eq20914 eq20897 eq47
  have eq20945 : b = sk1 ∨ b = c := step_2_eq20945 eq20914 eq56
  have eq21003 : b = sk1 := step_2_eq21003 eq20945 eq50
  have eq21051 : (old sk0 b b) ∨ b = c ∨ c = sk0 := step_2_eq21051 eq295 eq21003
  have eq21052 : (old sk0 b b) ∨ b = c ∨ a = b := step_2_eq21052 eq296 eq21003
  have eq21108 : ¬(old b b b) ∨ (old b sk0 sk2) ∨ a = b ∨ b = c := step_2_eq21108 eq499 eq21003
  have eq21405 : (old a b sk3) ∨ c = sk3 ∨ b = c ∨ c = sk2 ∨ c = sk0 := step_2_eq21405 eq6026 eq21003
  have eq21407 : (old b sk0 a) ∨ c = sk0 ∨ b = c ∨ c = sk2 := step_2_eq21407 eq6035 eq21003
  have eq21435 : (old b sk0 a) ∨ c = sk0 ∨ c = sk2 := step_2_eq21435 eq21407 eq50
  have eq21437 : c = sk3 ∨ b = c ∨ c = sk2 ∨ c = sk0 := step_2_eq21437 eq21405 eq51
  have eq21595 : (old b sk0 sk2) ∨ a = b ∨ b = c := step_2_eq21595 eq21108 eq48
  have eq21631 : (old sk0 b b) ∨ a = b := step_2_eq21631 eq21052 eq50
  have eq21632 : (old sk0 b b) ∨ c = sk0 := step_2_eq21632 eq21051 eq50
  have eq21635 : c = sk3 ∨ c = sk2 ∨ c = sk0 := step_2_eq21635 eq21437 eq50
  have eq21658 : (old b sk0 sk2) ∨ b = c := step_2_eq21658 eq21595 eq47
  have eq21680 : (old sk0 b b) := step_2_eq21680 eq21631 eq47
  have eq21682 : (old b sk0 sk2) := step_2_eq21682 eq21658 eq50
  have eq21865 : ¬(old sk0 b b) ∨ (old b sk2 sk0) := step_2_eq21865 eq21682 eq61
  have eq21885 : (old b sk2 sk0) := step_2_eq21885 eq21865 eq21680
  have eq23423 : ¬(new c sk0 sk2) ∨ c = sk2 ∨ c = sk0 := step_2_eq23423 eq95 eq21635
  have eq23435 : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk2 ∨ c = sk0 := step_2_eq23435 eq555 eq21635
  have eq23627 : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk0 := step_2_eq23627 eq23435
  have eq23649 : a = sk2 ∨ c = sk2 ∨ b = c ∨ c = sk0 := step_2_eq23649 eq23627 eq53
  have eq23666 : a = sk2 ∨ c = sk2 ∨ c = sk0 := step_2_eq23666 eq23649 eq50
  have eq24378 : c = sk0 ∨ c = sk2 ∨ ¬(old sk0 b b) ∨ (new c sk0 a) := step_2_eq24378 eq21435 eq108
  have eq24422 : c = sk0 ∨ c = sk2 ∨ (new c sk0 a) := step_2_eq24422 eq24378 eq21632
  have eq25675 : ¬(new c sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 := step_2_eq25675 eq23423 eq23666
  have eq25676 : ¬(new c sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk2 := step_2_eq25676 eq25675
  have eq25679 : a = c ∨ c = sk0 ∨ c = sk2 := step_2_eq25679 eq25676 eq24422
  have eq25680 : c = sk2 ∨ c = sk0 := step_2_eq25680 eq25679 eq49
  have eq26094 : (old b c sk0) ∨ c = sk0 := step_2_eq26094 eq21885 eq25680
  have eq26171 : c = sk0 := step_2_eq26171 eq26094 eq54
  have eq26372 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 := step_2_eq26372 eq296 eq26171
  have eq26743 : c = sk1 ∨ a = sk1 := step_2_eq26743 eq26372 eq56
  have eq26850 : b = c ∨ a = sk1 := step_2_eq26850 eq26743 eq21003
  have eq26928 : a = sk1 := step_2_eq26928 eq26850 eq50
  have eq26985 : a = b := step_2_eq26985 eq26928 eq21003
  clear * - eq26985 eq47
  first | subsumption eq26985 eq47 | grind only


private theorem step_3_eq46 {G : Type*} {a : G} {b : G} (ab : a ≠ b) : a ≠ b := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ab | grind only

private theorem step_3_eq47 {G : Type*} {old : G → G → G → Prop} (diagonal : ∀ x, old x x x) : ∀ (X0 : G), (old X0 X0 X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using diagonal | grind only

private theorem step_3_eq48 {G : Type*} {a : G} {c : G} (ac : a ≠ c) : a ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ac | grind only

private theorem step_3_eq49 {G : Type*} {b : G} {c : G} (bc : b ≠ c) : b ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using bc | grind only

private theorem step_3_eq50 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (p3 : ∀ z, ¬ old a b z) : ∀ (X0 : G), ¬(old a b X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p3 | grind only

private theorem step_3_eq51 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_3_eq52 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_3_eq54 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_3_eq55 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_3_eq56 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_3_eq57 {G : Type*} {old : G → G → G → Prop} (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_0 | grind only

private theorem step_3_eq60 {G : Type*} {old : G → G → G → Prop} (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ old X1 X2 X0)) : ∀ (X0 X1 X2 : G), ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_3 | grind only

private theorem step_3_eq63 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_0 | grind only

private theorem step_3_eq65 {G : Type*} {a : G} {sP0 : G → G → G → Prop} (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_0 | grind only

private theorem step_3_eq66 {G : Type*} {b : G} {sP0 : G → G → G → Prop} (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_1 | grind only

private theorem step_3_eq67 {G : Type*} {c : G} {sP0 : G → G → G → Prop} (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_2 | grind only

private theorem step_3_eq69 {G : Type*} {c : G} {sP1 : G → G → G → Prop} (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_0 | grind only

private theorem step_3_eq70 {G : Type*} {b : G} {sP1 : G → G → G → Prop} (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_1 | grind only

private theorem step_3_eq71 {G : Type*} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_2 | grind only

private theorem step_3_eq74 {G : Type*} {c : G} {sP2 : G → G → G → Prop} (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_0 | grind only

private theorem step_3_eq75 {G : Type*} {a : G} {sP2 : G → G → G → Prop} (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_1 | grind only

private theorem step_3_eq76 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_2 | grind only

private theorem step_3_eq77 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_3 | grind only

private theorem step_3_eq78 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_4 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ ¬ old b a a ∨ new X Y Z) : ∀ (X0 X1 X2 : G), a ≠ X0 ∨ c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b a a) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_4 | grind only

private theorem step_3_eq79 {G : Type*} {a : G} {sP3 : G → G → G → Prop} (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_0 | grind only

private theorem step_3_eq80 {G : Type*} {c : G} {sP3 : G → G → G → Prop} (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_1 | grind only

private theorem step_3_eq81 {G : Type*} {b : G} {sP3 : G → G → G → Prop} (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_2 | grind only

private theorem step_3_eq84 {G : Type*} {c : G} {sP4 : G → G → G → Prop} (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_0 | grind only

private theorem step_3_eq85 {G : Type*} {a : G} {sP4 : G → G → G → Prop} (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_1 | grind only

private theorem step_3_eq87 {G : Type*} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_3 | grind only

private theorem step_3_eq88 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_4 | grind only

private theorem step_3_eq90 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_imp | grind only

private theorem step_3_eq91 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (preserve_0 : new sk0 sk1 sk1) : (new sk0 sk1 sk1) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_0 | grind only

private theorem step_3_eq92 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_1 : new sk1 sk0 sk2) : (new sk1 sk0 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_1 | grind only

private theorem step_3_eq93 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_2 : ¬ (new sk1 sk2 sk0)) : ¬(new sk1 sk2 sk0) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_2 | grind only

private theorem step_3_eq101 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq78 : ∀ (X0 X1 X2 : G), a ≠ X0 ∨ c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b a a) ∨ (new X0 X1 X2)) : ∀ (X1 X2 : G), c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b a a) ∨ (new a X1 X2) := by
  intro X1 X2
  first | exact resolve eq78 rfl | grind only

private theorem step_3_eq102 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq101 : ∀ (X1 X2 : G), c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b a a) ∨ (new a X1 X2)) : ∀ (X2 : G), b ≠ X2 ∨ ¬(old b a a) ∨ (new a c X2) := by
  intro X2
  first | exact resolve eq101 rfl | grind only

private theorem step_3_eq103 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq102 : ∀ (X2 : G), b ≠ X2 ∨ ¬(old b a a) ∨ (new a c X2)) : ¬(old b a a) ∨ (new a c b) := by
  first | exact resolve eq102 rfl | grind only

private theorem step_3_eq113 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq63 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) (eq47 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 : G), (new X0 X0 X0) := by
  intro X0
  first | exact resolve eq63 eq47 | exact resolve eq47 eq63 | grind only

private theorem step_3_eq114 {G : Type*} {old : G → G → G → Prop} (eq57 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) (eq47 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1 := by
  intro X0 X1
  first | exact resolve eq57 eq47 | exact resolve eq47 eq57 | grind only

private theorem step_3_eq120 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq71 : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) (eq56 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) ∨ b = c := by
  intro X0 X1
  first | exact resolve eq71 eq56 | exact resolve eq56 eq71 | grind only

private theorem step_3_eq122 {G : Type*} {b : G} {c : G} {sP1 : G → G → G → Prop} (eq120 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) ∨ b = c) (eq49 : b ≠ c) : ∀ (X0 X1 : G), ¬(sP1 c X0 X1) := by
  intro X0 X1
  first | exact resolve eq120 eq49 | exact resolve eq49 eq120 | grind only

private theorem step_3_eq151 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq90 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq91 : (new sk0 sk1 sk1)) : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) := by
  first | exact resolve eq90 eq91 | exact resolve eq91 eq90 | grind only

private theorem step_3_eq152 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq90 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq92 : (new sk1 sk0 sk2)) : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) := by
  first | exact resolve eq90 eq92 | exact resolve eq92 eq90 | grind only

private theorem step_3_eq155 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq151 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := by
  first | exact resolve eq151 eq67 | exact resolve eq67 eq151 | grind only

private theorem step_3_eq156 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq151 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := by
  first | exact resolve eq151 eq66 | exact resolve eq66 eq151 | grind only

private theorem step_3_eq159 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq156 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := by
  first | exact resolve eq156 eq70 | exact resolve eq70 eq156 | grind only

private theorem step_3_eq160 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq155 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := by
  first | exact resolve eq155 eq69 | exact resolve eq69 eq155 | grind only

private theorem step_3_eq161 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq159 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := by
  first | exact resolve eq159 eq81 | exact resolve eq81 eq159 | grind only

private theorem step_3_eq162 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq160 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := by
  first | exact resolve eq160 eq80 | exact resolve eq80 eq160 | grind only

private theorem step_3_eq163 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq152 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 := by
  first | exact resolve eq152 eq67 | exact resolve eq67 eq152 | grind only

private theorem step_3_eq164 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq152 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2)) (eq66 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 := by
  first | exact resolve eq152 eq66 | exact resolve eq66 eq152 | grind only

private theorem step_3_eq165 {G : Type*} {a : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq152 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2)) (eq65 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := by
  first | exact resolve eq152 eq65 | exact resolve eq65 eq152 | grind only

private theorem step_3_eq166 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq165 : (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1) (eq79 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := by
  first | exact resolve eq165 eq79 | exact resolve eq79 eq165 | grind only

private theorem step_3_eq170 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq161 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq161 eq74 | exact resolve eq74 eq161 | grind only

private theorem step_3_eq171 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq170 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq170 eq84 | exact resolve eq84 eq170 | grind only

private theorem step_3_eq295 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq162 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b)) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := by
  first | exact resolve eq162 eq76 | exact resolve eq76 eq162 | grind only

private theorem step_3_eq296 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq162 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq162 eq75 | exact resolve eq75 eq162 | grind only

private theorem step_3_eq297 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq162 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq162 eq74 | exact resolve eq74 eq162 | grind only

private theorem step_3_eq298 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq297 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq297 eq84 | exact resolve eq84 eq297 | grind only

private theorem step_3_eq299 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq296 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq296 eq85 | exact resolve eq85 eq296 | grind only

private theorem step_3_eq300 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq295 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b)) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b)) : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := by
  first | exact resolve eq295 eq87 | exact resolve eq87 eq295 | grind only

private theorem step_3_eq382 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq166 : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := by
  first | exact resolve eq166 eq75 | exact resolve eq75 eq166 | grind only

private theorem step_3_eq383 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq166 : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq166 eq74 | exact resolve eq74 eq166 | grind only

private theorem step_3_eq384 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq383 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq383 eq84 | exact resolve eq84 eq383 | grind only

private theorem step_3_eq385 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq382 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2) (eq85 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := by
  first | exact resolve eq382 eq85 | exact resolve eq85 eq382 | grind only

private theorem step_3_eq403 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq163 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq163 eq80 | exact resolve eq80 eq163 | grind only

private theorem step_3_eq405 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq403 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq403 eq69 | exact resolve eq69 eq403 | grind only

private theorem step_3_eq421 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq164 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := by
  first | exact resolve eq164 eq81 | exact resolve eq81 eq164 | grind only

private theorem step_3_eq422 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq164 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 := by
  first | exact resolve eq164 eq80 | exact resolve eq80 eq164 | grind only

private theorem step_3_eq424 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq422 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 := by
  first | exact resolve eq422 eq69 | exact resolve eq69 eq422 | grind only

private theorem step_3_eq425 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq421 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := by
  first | exact resolve eq421 eq70 | exact resolve eq70 eq421 | grind only

private theorem step_3_eq440 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq384 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq384 eq69 | exact resolve eq69 eq384 | grind only

private theorem step_3_eq452 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq440 : (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0) (eq60 : ∀ (X0 X1 X2 : G), ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0)) : a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0) := by
  first | exact resolve eq440 eq60 | exact resolve eq60 eq440 | grind only

private theorem step_3_eq458 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq452 : a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0)) (eq299 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) : (old sk1 sk2 sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := by
  first | exact resolve eq452 eq299 | exact resolve eq299 eq452 | grind only

private theorem step_3_eq481 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq458 : (old sk1 sk2 sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1) (eq63 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) : c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ (new sk1 sk2 sk0) := by
  first | exact resolve eq458 eq63 | exact resolve eq63 eq458 | grind only

private theorem step_3_eq485 {G : Type*} {a : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq481 : c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ (new sk1 sk2 sk0)) (eq93 : ¬(new sk1 sk2 sk0)) : c = sk0 ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq481 eq93 | exact resolve eq93 eq481 | grind only

private theorem step_3_eq506 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq299 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq485 : c = sk0 ∨ c = sk1 ∨ a = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 := by
  first | exact superpose eq299 eq485 | exact superpose eq485 eq299 | grind only

private theorem step_3_eq519 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq506 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 := by
  first | exact resolve eq506 rfl | grind only

private theorem step_3_eq529 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq519 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1) (eq55 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk1 ∨ c = sk1 := by
  first | exact resolve eq519 eq55 | exact resolve eq55 eq519 | grind only

private theorem step_3_eq544 {G : Type*} {a : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq93 : ¬(new sk1 sk2 sk0)) (eq529 : a = sk1 ∨ c = sk1) : ¬(new a sk2 sk0) ∨ c = sk1 := by
  first | exact superpose eq93 eq529 | exact superpose eq529 eq93 | grind only

private theorem step_3_eq559 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq300 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b)) (eq529 : a = sk1 ∨ c = sk1) : (old sk0 a a) ∨ a = c ∨ (old a b b) ∨ c = sk1 := by
  first | exact superpose eq300 eq529 | exact superpose eq529 eq300 | grind only

private theorem step_3_eq566 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq559 : (old sk0 a a) ∨ a = c ∨ (old a b b) ∨ c = sk1) (eq48 : a ≠ c) : (old sk0 a a) ∨ (old a b b) ∨ c = sk1 := by
  first | exact resolve eq559 eq48 | exact resolve eq48 eq559 | grind only

private theorem step_3_eq579 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq566 : (old sk0 a a) ∨ (old a b b) ∨ c = sk1) (eq50 : ∀ (X0 : G), ¬(old a b X0)) : (old sk0 a a) ∨ c = sk1 := by
  first | exact resolve eq566 eq50 | exact resolve eq50 eq566 | grind only

private theorem step_3_eq1000 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq405 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq405 eq74 | exact resolve eq74 eq405 | grind only

private theorem step_3_eq1003 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1000 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq1000 eq84 | exact resolve eq84 eq1000 | grind only

private theorem step_3_eq1010 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1003 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1) (eq60 : ∀ (X0 X1 X2 : G), ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0)) : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0) := by
  first | exact resolve eq1003 eq60 | exact resolve eq60 eq1003 | grind only

private theorem step_3_eq1020 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1010 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0)) (eq298 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0) : (old sk1 sk2 sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq1010 eq298 | exact resolve eq298 eq1010 | grind only

private theorem step_3_eq1045 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq424 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0) (eq74 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq424 eq74 | exact resolve eq74 eq424 | grind only

private theorem step_3_eq1048 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1045 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq1045 eq84 | exact resolve eq84 eq1045 | grind only

private theorem step_3_eq1065 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq425 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := by
  first | exact resolve eq425 eq77 | exact resolve eq77 eq425 | grind only

private theorem step_3_eq1074 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1065 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a)) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (old sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := by
  first | exact resolve eq1065 eq88 | exact resolve eq88 eq1065 | grind only

private theorem step_3_eq1254 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1020 : (old sk1 sk2 sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq63 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) : c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk2 sk0) := by
  first | exact resolve eq1020 eq63 | exact resolve eq63 eq1020 | grind only

private theorem step_3_eq1262 {G : Type*} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1254 : c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk2 sk0)) (eq93 : ¬(new sk1 sk2 sk0)) : c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq1254 eq93 | exact resolve eq93 eq1254 | grind only

private theorem step_3_eq1291 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1048 : (old sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1) (eq1262 : c = sk2 ∨ c = sk1 ∨ c = sk0) : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact superpose eq1048 eq1262 | exact superpose eq1262 eq1048 | grind only

private theorem step_3_eq1297 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1291 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk0) : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq1291 rfl | grind only

private theorem step_3_eq1315 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1297 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1) (eq51 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk0 ∨ b = sk0 ∨ c = sk1 := by
  first | exact resolve eq1297 eq51 | exact resolve eq51 eq1297 | grind only

private theorem step_3_eq1358 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq300 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b)) (eq1315 : c = sk0 ∨ b = sk0 ∨ c = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk0 ∨ c = sk1 := by
  first | exact superpose eq300 eq1315 | exact superpose eq1315 eq300 | grind only

private theorem step_3_eq1406 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1358 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk0 ∨ c = sk1) : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk0 := by
  first | exact resolve eq1358 rfl | grind only

private theorem step_3_eq1420 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1406 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : (old sk1 b b) ∨ c = sk1 ∨ b = sk0 := by
  first | exact resolve eq1406 eq55 | exact resolve eq55 eq1406 | grind only

private theorem step_3_eq1578 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1420 : (old sk1 b b) ∨ c = sk1 ∨ b = sk0) (eq529 : a = sk1 ∨ c = sk1) : (old a b b) ∨ a = c ∨ b = sk0 ∨ c = sk1 := by
  first | exact superpose eq1420 eq529 | exact superpose eq529 eq1420 | grind only

private theorem step_3_eq1579 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1578 : (old a b b) ∨ a = c ∨ b = sk0 ∨ c = sk1) (eq50 : ∀ (X0 : G), ¬(old a b X0)) : a = c ∨ b = sk0 ∨ c = sk1 := by
  first | exact resolve eq1578 eq50 | exact resolve eq50 eq1578 | grind only

private theorem step_3_eq1580 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} (eq1579 : a = c ∨ b = sk0 ∨ c = sk1) (eq48 : a ≠ c) : b = sk0 ∨ c = sk1 := by
  first | exact resolve eq1579 eq48 | exact resolve eq48 eq1579 | grind only

private theorem step_3_eq1644 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq544 : ¬(new a sk2 sk0) ∨ c = sk1) (eq1580 : b = sk0 ∨ c = sk1) : ¬(new a sk2 b) ∨ c = sk1 ∨ c = sk1 := by
  first | exact superpose eq544 eq1580 | exact superpose eq1580 eq544 | grind only

private theorem step_3_eq1648 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq579 : (old sk0 a a) ∨ c = sk1) (eq1580 : b = sk0 ∨ c = sk1) : (old b a a) ∨ c = sk1 ∨ c = sk1 := by
  first | exact superpose eq579 eq1580 | exact superpose eq1580 eq579 | grind only

private theorem step_3_eq1671 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq1648 : (old b a a) ∨ c = sk1 ∨ c = sk1) : (old b a a) ∨ c = sk1 := by
  first | exact resolve eq1648 rfl | grind only

private theorem step_3_eq1675 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq1644 : ¬(new a sk2 b) ∨ c = sk1 ∨ c = sk1) : ¬(new a sk2 b) ∨ c = sk1 := by
  first | exact resolve eq1644 rfl | grind only

private theorem step_3_eq1784 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} (eq1671 : (old b a a) ∨ c = sk1) (eq103 : ¬(old b a a) ∨ (new a c b)) : (new a c b) ∨ c = sk1 := by
  first | exact resolve eq1671 eq103 | exact resolve eq103 eq1671 | grind only

private theorem step_3_eq1809 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1675 : ¬(new a sk2 b) ∨ c = sk1) (eq1262 : c = sk2 ∨ c = sk1 ∨ c = sk0) : ¬(new a c b) ∨ c = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact superpose eq1675 eq1262 | exact superpose eq1262 eq1675 | grind only

private theorem step_3_eq1812 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1809 : ¬(new a c b) ∨ c = sk1 ∨ c = sk1 ∨ c = sk0) : ¬(new a c b) ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq1809 rfl | grind only

private theorem step_3_eq1814 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq1812 : ¬(new a c b) ∨ c = sk1 ∨ c = sk0) (eq1784 : (new a c b) ∨ c = sk1) : c = sk0 ∨ c = sk1 := by
  first | exact resolve eq1812 eq1784 | exact resolve eq1784 eq1812 | grind only

private theorem step_3_eq1884 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} (eq1580 : b = sk0 ∨ c = sk1) (eq1814 : c = sk0 ∨ c = sk1) : b = c ∨ c = sk1 ∨ c = sk1 := by
  first | exact superpose eq1580 eq1814 | exact superpose eq1814 eq1580 | grind only

private theorem step_3_eq1885 {G : Type*} {b : G} {c : G} {sk1 : G} (eq1884 : b = c ∨ c = sk1 ∨ c = sk1) : b = c ∨ c = sk1 := by
  first | exact resolve eq1884 rfl | grind only

private theorem step_3_eq1905 {G : Type*} {b : G} {c : G} {sk1 : G} (eq1885 : b = c ∨ c = sk1) (eq49 : b ≠ c) : c = sk1 := by
  first | exact resolve eq1885 eq49 | exact resolve eq49 eq1885 | grind only

private theorem step_3_eq1957 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq171 : (old sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0) (eq1905 : c = sk1) : (old sk0 c c) ∨ b = c ∨ c = sk0 := by
  first | exact superpose eq171 eq1905 | exact superpose eq1905 eq171 | grind only

private theorem step_3_eq1969 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq385 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2) (eq1905 : c = sk1) : (sP1 c sk0 sk2) ∨ (old c sk0 sk2) ∨ a = c ∨ a = sk2 := by
  first | exact superpose eq385 eq1905 | exact superpose eq1905 eq385 | grind only

private theorem step_3_eq2010 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq1969 : (sP1 c sk0 sk2) ∨ (old c sk0 sk2) ∨ a = c ∨ a = sk2) (eq122 : ∀ (X0 X1 : G), ¬(sP1 c X0 X1)) : (old c sk0 sk2) ∨ a = c ∨ a = sk2 := by
  first | exact resolve eq1969 eq122 | exact resolve eq122 eq1969 | grind only

private theorem step_3_eq2016 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq1957 : (old sk0 c c) ∨ b = c ∨ c = sk0) (eq52 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0) : b = c ∨ c = sk0 := by
  first | exact resolve eq1957 eq52 | exact resolve eq52 eq1957 | grind only

private theorem step_3_eq2027 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq2010 : (old c sk0 sk2) ∨ a = c ∨ a = sk2) (eq48 : a ≠ c) : (old c sk0 sk2) ∨ a = sk2 := by
  first | exact resolve eq2010 eq48 | exact resolve eq48 eq2010 | grind only

private theorem step_3_eq2030 {G : Type*} {b : G} {c : G} {sk0 : G} (eq2016 : b = c ∨ c = sk0) (eq49 : b ≠ c) : c = sk0 := by
  first | exact resolve eq2016 eq49 | exact resolve eq49 eq2016 | grind only

private theorem step_3_eq2109 {G : Type*} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq93 : ¬(new sk1 sk2 sk0)) (eq2030 : c = sk0) : ¬(new sk1 sk2 c) := by
  first | exact superpose eq93 eq2030 | exact superpose eq2030 eq93 | grind only

private theorem step_3_eq2161 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1074 : (old sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a)) (eq2030 : c = sk0) : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ (old b c a) := by
  first | exact superpose eq1074 eq2030 | exact superpose eq2030 eq1074 | grind only

private theorem step_3_eq2163 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq2161 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ (old b c a)) (eq54 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : (old sk1 c sk2) ∨ b = c ∨ b = sk2 := by
  first | exact resolve eq2161 eq54 | exact resolve eq54 eq2161 | grind only

private theorem step_3_eq2196 {G : Type*} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq2109 : ¬(new sk1 sk2 c)) (eq1905 : c = sk1) : ¬(new c sk2 c) := by
  first | simpa only [eq1905, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq2109 | grind only

private theorem step_3_eq2199 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq2163 : (old sk1 c sk2) ∨ b = c ∨ b = sk2) (eq49 : b ≠ c) : (old sk1 c sk2) ∨ b = sk2 := by
  first | exact resolve eq2163 eq49 | exact resolve eq49 eq2163 | grind only

private theorem step_3_eq2227 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq2199 : (old sk1 c sk2) ∨ b = sk2) (eq1905 : c = sk1) : (old c c sk2) ∨ b = sk2 := by
  first | simpa only [eq1905, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq2199 | grind only

private theorem step_3_eq3095 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq2027 : (old c sk0 sk2) ∨ a = sk2) (eq55 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk2 ∨ c = sk2 := by
  first | exact resolve eq2027 eq55 | exact resolve eq55 eq2027 | grind only

private theorem step_3_eq3414 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq2227 : (old c c sk2) ∨ b = sk2) (eq114 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : c = sk2 ∨ b = sk2 := by
  first | exact resolve eq2227 eq114 | exact resolve eq114 eq2227 | grind only

private theorem step_3_eq3463 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq3414 : c = sk2 ∨ b = sk2) (eq3095 : a = sk2 ∨ c = sk2) : a = c ∨ a = b ∨ c = sk2 := by
  first | exact superpose eq3414 eq3095 | exact superpose eq3095 eq3414 | grind only

private theorem step_3_eq3516 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk2 : G} (eq2196 : ¬(new c sk2 c)) (eq3414 : c = sk2 ∨ b = sk2) : ¬(new c c c) ∨ b = sk2 := by
  first | exact superpose eq2196 eq3414 | exact superpose eq3414 eq2196 | grind only

private theorem step_3_eq3520 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk2 : G} (eq3516 : ¬(new c c c) ∨ b = sk2) (eq113 : ∀ (X0 : G), (new X0 X0 X0)) : b = sk2 := by
  first | exact resolve eq3516 eq113 | exact resolve eq113 eq3516 | grind only

private theorem step_3_eq3541 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq3463 : a = c ∨ a = b ∨ c = sk2) (eq48 : a ≠ c) : a = b ∨ c = sk2 := by
  first | exact resolve eq3463 eq48 | exact resolve eq48 eq3463 | grind only

private theorem step_3_eq3542 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq3541 : a = b ∨ c = sk2) (eq46 : a ≠ b) : c = sk2 := by
  first | exact resolve eq3541 eq46 | exact resolve eq46 eq3541 | grind only

private theorem step_3_eq3543 {G : Type*} {b : G} {c : G} {sk2 : G} (eq3542 : c = sk2) (eq3520 : b = sk2) : b = c := by
  first | simpa only [eq3520, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq3542 | grind only

set_option maxHeartbeats 2000000 in
private theorem preserve_3 (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (ab : a ≠ b) (diagonal : ∀ x, old x x x) (ac : a ≠ c) (bc : b ≠ c) (p3 : ∀ z, ¬ old a b z) (p4XY : ∀ x y, old x y c → x = c ∧ y = c) (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ old X1 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) (imp_new_4 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ ¬ old b a a ∨ new X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X1 X1 ∨ ¬ new X1 X0 X2 ∨ new X1 X2 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq46 : a ≠ b := step_3_eq46 ab
  have eq47 (X0 : G) : (old X0 X0 X0) := step_3_eq47 diagonal X0
  have eq48 : a ≠ c := step_3_eq48 ac
  have eq49 : b ≠ c := step_3_eq49 bc
  have eq50 (X0 : G) : ¬(old a b X0) := step_3_eq50 p3 X0
  have eq51 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X1 := step_3_eq51 p4XY X0 X1
  have eq52 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X0 := step_3_eq52 p4XY X0 X1
  have eq54 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X0 := step_3_eq54 p4XZ X0 X1
  have eq55 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X1 := step_3_eq55 p4YZ X0 X1
  have eq56 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X0 := step_3_eq56 p4YZ X0 X1
  have eq57 (X0 X1 X2 X3 : G) : ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := step_3_eq57 old_0 X0 X1 X2 X3
  have eq60 (X0 X1 X2 : G) : ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X1 X2 X0) := step_3_eq60 old_3 X0 X1 X2
  have eq63 (X0 X1 X2 : G) : ¬(old X0 X1 X2) ∨ (new X0 X1 X2) := step_3_eq63 imp_new_0 X0 X1 X2
  have eq65 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ a = X0 := step_3_eq65 rule_def_0_0 X0 X1 X2
  have eq66 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ b = X1 := step_3_eq66 rule_def_0_1 X0 X1 X2
  have eq67 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ c = X2 := step_3_eq67 rule_def_0_2 X0 X1 X2
  have eq69 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ c = X1 := step_3_eq69 rule_def_1_0 X0 X1 X2
  have eq70 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ b = X2 := step_3_eq70 rule_def_1_1 X0 X1 X2
  have eq71 (X0 X1 X2 : G) : (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := step_3_eq71 rule_def_1_2 X0 X1 X2
  have eq74 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ c = X0 := step_3_eq74 rule_def_2_0 X0 X1 X2
  have eq75 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = X2 := step_3_eq75 rule_def_2_1 X0 X1 X2
  have eq76 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := step_3_eq76 rule_def_2_2 X0 X1 X2
  have eq77 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := step_3_eq77 rule_def_2_3 X0 X1 X2
  have eq78 (X0 X1 X2 : G) : a ≠ X0 ∨ c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b a a) ∨ (new X0 X1 X2) := step_3_eq78 imp_new_4 X0 X1 X2
  have eq79 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = X0 := step_3_eq79 rule_def_3_0 X0 X1 X2
  have eq80 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ c = X1 := step_3_eq80 rule_def_3_1 X0 X1 X2
  have eq81 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ b = X2 := step_3_eq81 rule_def_3_2 X0 X1 X2
  have eq84 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ c = X0 := step_3_eq84 rule_def_4_0 X0 X1 X2
  have eq85 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = X2 := step_3_eq85 rule_def_4_1 X0 X1 X2
  have eq87 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := step_3_eq87 rule_def_4_3 X0 X1 X2
  have eq88 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := step_3_eq88 rule_def_4_4 X0 X1 X2
  have eq90 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := step_3_eq90 new_imp X0 X1 X2
  have eq91 : (new sk0 sk1 sk1) := step_3_eq91 preserve_0
  have eq92 : (new sk1 sk0 sk2) := step_3_eq92 preserve_1
  have eq93 : ¬(new sk1 sk2 sk0) := step_3_eq93 preserve_2
  have eq101 (X1 X2 : G) : c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b a a) ∨ (new a X1 X2) := step_3_eq101 eq78 X1 X2
  have eq102 (X2 : G) : b ≠ X2 ∨ ¬(old b a a) ∨ (new a c X2) := step_3_eq102 eq101 X2
  have eq103 : ¬(old b a a) ∨ (new a c b) := step_3_eq103 eq102
  have eq113 (X0 : G) : (new X0 X0 X0) := step_3_eq113 eq63 eq47 X0
  have eq114 (X0 X1 : G) : ¬(old X0 X0 X1) ∨ X0 = X1 := step_3_eq114 eq57 eq47 X0 X1
  have eq120 (X0 X1 : G) : ¬(sP1 c X0 X1) ∨ b = c := step_3_eq120 eq71 eq56 X0 X1
  have eq122 (X0 X1 : G) : ¬(sP1 c X0 X1) := step_3_eq122 eq120 eq49 X0 X1
  have eq151 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) := step_3_eq151 eq90 eq91
  have eq152 : (sP0 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) := step_3_eq152 eq90 eq92
  have eq155 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := step_3_eq155 eq151 eq67
  have eq156 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := step_3_eq156 eq151 eq66
  have eq159 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := step_3_eq159 eq156 eq70
  have eq160 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := step_3_eq160 eq155 eq69
  have eq161 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 := step_3_eq161 eq159 eq81
  have eq162 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 := step_3_eq162 eq160 eq80
  have eq163 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 := step_3_eq163 eq152 eq67
  have eq164 : (sP3 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 := step_3_eq164 eq152 eq66
  have eq165 : (old sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (sP3 sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := step_3_eq165 eq152 eq65
  have eq166 : (sP2 sk1 sk0 sk2) ∨ (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 := step_3_eq166 eq165 eq79
  have eq170 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := step_3_eq170 eq161 eq74
  have eq171 : (old sk0 sk1 sk1) ∨ b = sk1 ∨ c = sk0 := step_3_eq171 eq170 eq84
  have eq295 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := step_3_eq295 eq162 eq76
  have eq296 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := step_3_eq296 eq162 eq75
  have eq297 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := step_3_eq297 eq162 eq74
  have eq298 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := step_3_eq298 eq297 eq84
  have eq299 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = sk1 := step_3_eq299 eq296 eq85
  have eq300 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := step_3_eq300 eq295 eq87
  have eq382 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := step_3_eq382 eq166 eq75
  have eq383 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := step_3_eq383 eq166 eq74
  have eq384 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 := step_3_eq384 eq383 eq84
  have eq385 : (sP1 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ a = sk1 ∨ a = sk2 := step_3_eq385 eq382 eq85
  have eq403 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := step_3_eq403 eq163 eq80
  have eq405 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 := step_3_eq405 eq403 eq69
  have eq421 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := step_3_eq421 eq164 eq81
  have eq422 : (sP1 sk1 sk0 sk2) ∨ (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 := step_3_eq422 eq164 eq80
  have eq424 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 := step_3_eq424 eq422 eq69
  have eq425 : (sP2 sk1 sk0 sk2) ∨ (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 := step_3_eq425 eq421 eq70
  have eq440 : (old sk1 sk0 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := step_3_eq440 eq384 eq69
  have eq452 : a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0) := step_3_eq452 eq440 eq60
  have eq458 : (old sk1 sk2 sk0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := step_3_eq458 eq452 eq299
  have eq481 : c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ (new sk1 sk2 sk0) := step_3_eq481 eq458 eq63
  have eq485 : c = sk0 ∨ c = sk1 ∨ a = sk1 := step_3_eq485 eq481 eq93
  have eq506 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 := step_3_eq506 eq299 eq485
  have eq519 : (old c sk1 sk1) ∨ c = sk1 ∨ a = sk1 := step_3_eq519 eq506
  have eq529 : a = sk1 ∨ c = sk1 := step_3_eq529 eq519 eq55
  have eq544 : ¬(new a sk2 sk0) ∨ c = sk1 := step_3_eq544 eq93 eq529
  have eq559 : (old sk0 a a) ∨ a = c ∨ (old a b b) ∨ c = sk1 := step_3_eq559 eq300 eq529
  have eq566 : (old sk0 a a) ∨ (old a b b) ∨ c = sk1 := step_3_eq566 eq559 eq48
  have eq579 : (old sk0 a a) ∨ c = sk1 := step_3_eq579 eq566 eq50
  have eq1000 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := step_3_eq1000 eq405 eq74
  have eq1003 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := step_3_eq1003 eq1000 eq84
  have eq1010 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ ¬(old sk0 sk1 sk1) ∨ (old sk1 sk2 sk0) := step_3_eq1010 eq1003 eq60
  have eq1020 : (old sk1 sk2 sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_3_eq1020 eq1010 eq298
  have eq1045 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := step_3_eq1045 eq424 eq74
  have eq1048 : (old sk1 sk0 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := step_3_eq1048 eq1045 eq84
  have eq1065 : (old sk1 sk0 sk2) ∨ (sP4 sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := step_3_eq1065 eq425 eq77
  have eq1074 : (old sk1 sk0 sk2) ∨ b = sk0 ∨ b = sk2 ∨ (old b sk0 a) := step_3_eq1074 eq1065 eq88
  have eq1254 : c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk2 sk0) := step_3_eq1254 eq1020 eq63
  have eq1262 : c = sk2 ∨ c = sk1 ∨ c = sk0 := step_3_eq1262 eq1254 eq93
  have eq1291 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk0 := step_3_eq1291 eq1048 eq1262
  have eq1297 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := step_3_eq1297 eq1291
  have eq1315 : c = sk0 ∨ b = sk0 ∨ c = sk1 := step_3_eq1315 eq1297 eq51
  have eq1358 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk0 ∨ c = sk1 := step_3_eq1358 eq300 eq1315
  have eq1406 : (old c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ b = sk0 := step_3_eq1406 eq1358
  have eq1420 : (old sk1 b b) ∨ c = sk1 ∨ b = sk0 := step_3_eq1420 eq1406 eq55
  have eq1578 : (old a b b) ∨ a = c ∨ b = sk0 ∨ c = sk1 := step_3_eq1578 eq1420 eq529
  have eq1579 : a = c ∨ b = sk0 ∨ c = sk1 := step_3_eq1579 eq1578 eq50
  have eq1580 : b = sk0 ∨ c = sk1 := step_3_eq1580 eq1579 eq48
  have eq1644 : ¬(new a sk2 b) ∨ c = sk1 ∨ c = sk1 := step_3_eq1644 eq544 eq1580
  have eq1648 : (old b a a) ∨ c = sk1 ∨ c = sk1 := step_3_eq1648 eq579 eq1580
  have eq1671 : (old b a a) ∨ c = sk1 := step_3_eq1671 eq1648
  have eq1675 : ¬(new a sk2 b) ∨ c = sk1 := step_3_eq1675 eq1644
  have eq1784 : (new a c b) ∨ c = sk1 := step_3_eq1784 eq1671 eq103
  have eq1809 : ¬(new a c b) ∨ c = sk1 ∨ c = sk1 ∨ c = sk0 := step_3_eq1809 eq1675 eq1262
  have eq1812 : ¬(new a c b) ∨ c = sk1 ∨ c = sk0 := step_3_eq1812 eq1809
  have eq1814 : c = sk0 ∨ c = sk1 := step_3_eq1814 eq1812 eq1784
  have eq1884 : b = c ∨ c = sk1 ∨ c = sk1 := step_3_eq1884 eq1580 eq1814
  have eq1885 : b = c ∨ c = sk1 := step_3_eq1885 eq1884
  have eq1905 : c = sk1 := step_3_eq1905 eq1885 eq49
  have eq1957 : (old sk0 c c) ∨ b = c ∨ c = sk0 := step_3_eq1957 eq171 eq1905
  have eq1969 : (sP1 c sk0 sk2) ∨ (old c sk0 sk2) ∨ a = c ∨ a = sk2 := step_3_eq1969 eq385 eq1905
  have eq2010 : (old c sk0 sk2) ∨ a = c ∨ a = sk2 := step_3_eq2010 eq1969 eq122
  have eq2016 : b = c ∨ c = sk0 := step_3_eq2016 eq1957 eq52
  have eq2027 : (old c sk0 sk2) ∨ a = sk2 := step_3_eq2027 eq2010 eq48
  have eq2030 : c = sk0 := step_3_eq2030 eq2016 eq49
  have eq2109 : ¬(new sk1 sk2 c) := step_3_eq2109 eq93 eq2030
  have eq2161 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 ∨ (old b c a) := step_3_eq2161 eq1074 eq2030
  have eq2163 : (old sk1 c sk2) ∨ b = c ∨ b = sk2 := step_3_eq2163 eq2161 eq54
  have eq2196 : ¬(new c sk2 c) := step_3_eq2196 eq2109 eq1905
  have eq2199 : (old sk1 c sk2) ∨ b = sk2 := step_3_eq2199 eq2163 eq49
  have eq2227 : (old c c sk2) ∨ b = sk2 := step_3_eq2227 eq2199 eq1905
  have eq3095 : a = sk2 ∨ c = sk2 := step_3_eq3095 eq2027 eq55
  have eq3414 : c = sk2 ∨ b = sk2 := step_3_eq3414 eq2227 eq114
  have eq3463 : a = c ∨ a = b ∨ c = sk2 := step_3_eq3463 eq3414 eq3095
  have eq3516 : ¬(new c c c) ∨ b = sk2 := step_3_eq3516 eq2196 eq3414
  have eq3520 : b = sk2 := step_3_eq3520 eq3516 eq113
  have eq3541 : a = b ∨ c = sk2 := step_3_eq3541 eq3463 eq48
  have eq3542 : c = sk2 := step_3_eq3542 eq3541 eq46
  have eq3543 : b = c := step_3_eq3543 eq3542 eq3520
  clear * - eq3543 eq49
  first | subsumption eq3543 eq49 | grind only


private theorem step_4_eq48 {G : Type*} {a : G} {b : G} (ab : a ≠ b) : a ≠ b := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ab | grind only

private theorem step_4_eq49 {G : Type*} {old : G → G → G → Prop} (diagonal : ∀ x, old x x x) : ∀ (X0 : G), (old X0 X0 X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using diagonal | grind only

private theorem step_4_eq50 {G : Type*} {a : G} {c : G} (ac : a ≠ c) : a ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ac | grind only

private theorem step_4_eq51 {G : Type*} {b : G} {c : G} (bc : b ≠ c) : b ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using bc | grind only

private theorem step_4_eq52 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (p3 : ∀ z, ¬ old a b z) : ∀ (X0 : G), ¬(old a b X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p3 | grind only

private theorem step_4_eq53 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_4_eq54 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_4_eq55 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_4_eq56 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_4_eq57 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_4_eq61 {G : Type*} {old : G → G → G → Prop} (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ ¬ old X2 X1 X3 ∨ old X3 X0 X2)) : ∀ (X0 X1 X2 X3 : G), ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2) := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_2 | grind only

private theorem step_4_eq63 {G : Type*} {old : G → G → G → Prop} (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X0 ∨ ¬ old X3 X1 X2 ∨ ¬ old X3 X2 X2 ∨ old X2 X3 X0)) : ∀ (X0 X1 X2 X3 : G), ¬(old X3 X2 X2) ∨ ¬(old X1 X3 X0) ∨ ¬(old X3 X1 X2) ∨ ¬(old X0 X1 X2) ∨ (old X2 X3 X0) := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_4 | grind only

private theorem step_4_eq65 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_0 | grind only

private theorem step_4_eq67 {G : Type*} {a : G} {sP0 : G → G → G → Prop} (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_0 | grind only

private theorem step_4_eq68 {G : Type*} {b : G} {sP0 : G → G → G → Prop} (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_1 | grind only

private theorem step_4_eq69 {G : Type*} {c : G} {sP0 : G → G → G → Prop} (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_2 | grind only

private theorem step_4_eq71 {G : Type*} {c : G} {sP1 : G → G → G → Prop} (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_0 | grind only

private theorem step_4_eq72 {G : Type*} {b : G} {sP1 : G → G → G → Prop} (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_1 | grind only

private theorem step_4_eq73 {G : Type*} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_2 | grind only

private theorem step_4_eq74 {G : Type*} {a : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), (old (sF0 X0 X1 X2) X0 a) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_3 | grind only

private theorem step_4_eq76 {G : Type*} {c : G} {sP2 : G → G → G → Prop} (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_0 | grind only

private theorem step_4_eq77 {G : Type*} {a : G} {sP2 : G → G → G → Prop} (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_1 | grind only

private theorem step_4_eq78 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_2 | grind only

private theorem step_4_eq79 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_3 | grind only

private theorem step_4_eq81 {G : Type*} {a : G} {sP3 : G → G → G → Prop} (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_0 | grind only

private theorem step_4_eq82 {G : Type*} {c : G} {sP3 : G → G → G → Prop} (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_1 | grind only

private theorem step_4_eq83 {G : Type*} {b : G} {sP3 : G → G → G → Prop} (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_2 | grind only

private theorem step_4_eq86 {G : Type*} {c : G} {sP4 : G → G → G → Prop} (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_0 | grind only

private theorem step_4_eq87 {G : Type*} {a : G} {sP4 : G → G → G → Prop} (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_1 | grind only

private theorem step_4_eq89 {G : Type*} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_3 | grind only

private theorem step_4_eq90 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_4 | grind only

private theorem step_4_eq92 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_imp | grind only

private theorem step_4_eq93 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_0 : new sk0 sk1 sk2) : (new sk0 sk1 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_0 | grind only

private theorem step_4_eq94 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (preserve_1 : new sk1 sk3 sk0) : (new sk1 sk3 sk0) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_1 | grind only

private theorem step_4_eq95 {G : Type*} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (preserve_2 : new sk3 sk1 sk2) : (new sk3 sk1 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_2 | grind only

private theorem step_4_eq96 {G : Type*} {new : G → G → G → Prop} {sk2 : G} {sk3 : G} (preserve_3 : new sk3 sk2 sk2) : (new sk3 sk2 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_3 | grind only

private theorem step_4_eq97 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (preserve_4 : ¬ (new sk2 sk3 sk0)) : ¬(new sk2 sk3 sk0) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_4 | grind only

private theorem step_4_eq142 {G : Type*} {a : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq61 : ∀ (X0 X1 X2 X3 : G), ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2)) (eq74 : ∀ (X0 X1 X2 : G), (old (sF0 X0 X1 X2) X0 a) ∨ ¬(sP1 X0 X1 X2)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 (sF0 X0 X2 X3)) ∨ ¬(old X1 X0 X0) ∨ (old a X1 (sF0 X0 X2 X3)) ∨ ¬(sP1 X0 X2 X3) := by
  intro X0 X1 X2 X3
  first | exact resolve eq61 eq74 | exact resolve eq74 eq61 | grind only

private theorem step_4_eq155 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq92 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq93 : (new sk0 sk1 sk2)) : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) := by
  first | exact resolve eq92 eq93 | exact resolve eq93 eq92 | grind only

private theorem step_4_eq156 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq92 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq94 : (new sk1 sk3 sk0)) : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) := by
  first | exact resolve eq92 eq94 | exact resolve eq94 eq92 | grind only

private theorem step_4_eq157 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq92 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq95 : (new sk3 sk1 sk2)) : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) := by
  first | exact resolve eq92 eq95 | exact resolve eq95 eq92 | grind only

private theorem step_4_eq158 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq92 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq96 : (new sk3 sk2 sk2)) : (sP0 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) := by
  first | exact resolve eq92 eq96 | exact resolve eq96 eq92 | grind only

private theorem step_4_eq161 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq155 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2)) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 := by
  first | exact resolve eq155 eq69 | exact resolve eq69 eq155 | grind only

private theorem step_4_eq165 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq156 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0)) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 := by
  first | exact resolve eq156 eq69 | exact resolve eq69 eq156 | grind only

private theorem step_4_eq166 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq156 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 := by
  first | exact resolve eq156 eq68 | exact resolve eq68 eq156 | grind only

private theorem step_4_eq167 {G : Type*} {a : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq156 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0)) (eq67 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 := by
  first | exact resolve eq156 eq67 | exact resolve eq67 eq156 | grind only

private theorem step_4_eq168 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq167 : (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1) (eq81 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : (sP2 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 := by
  first | exact resolve eq167 eq81 | exact resolve eq81 eq167 | grind only

private theorem step_4_eq177 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq157 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2)) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 := by
  first | exact resolve eq157 eq69 | exact resolve eq69 eq157 | grind only

private theorem step_4_eq178 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq157 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 := by
  first | exact resolve eq157 eq68 | exact resolve eq68 eq157 | grind only

private theorem step_4_eq185 {G : Type*} {c : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq158 : (sP0 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2)) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 := by
  first | exact resolve eq158 eq69 | exact resolve eq69 eq158 | grind only

private theorem step_4_eq186 {G : Type*} {b : G} {old : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq158 : (sP0 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 := by
  first | exact resolve eq158 eq68 | exact resolve eq68 eq158 | grind only

private theorem step_4_eq189 {G : Type*} {b : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq186 : (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (old sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 := by
  first | exact resolve eq186 eq72 | exact resolve eq72 eq186 | grind only

private theorem step_4_eq190 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq185 : (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 := by
  first | exact resolve eq185 eq71 | exact resolve eq71 eq185 | grind only

private theorem step_4_eq191 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq189 : (old sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2) (eq83 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 := by
  first | exact resolve eq189 eq83 | exact resolve eq83 eq189 | grind only

private theorem step_4_eq192 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq190 : (old sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 := by
  first | exact resolve eq190 eq82 | exact resolve eq82 eq190 | grind only

private theorem step_4_eq299 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq191 : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 ∨ c = sk3 := by
  first | exact resolve eq191 eq76 | exact resolve eq76 eq191 | grind only

private theorem step_4_eq300 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq299 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 ∨ c = sk3) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk3 sk2 sk2) ∨ b = sk2 ∨ c = sk3 := by
  first | exact resolve eq299 eq86 | exact resolve eq86 eq299 | grind only

private theorem step_4_eq314 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq142 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 (sF0 X0 X2 X3)) ∨ ¬(old X1 X0 X0) ∨ (old a X1 (sF0 X0 X2 X3)) ∨ ¬(sP1 X0 X2 X3)) (eq73 : ∀ (X0 X1 X2 : G), (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | exact resolve eq142 eq73 | exact resolve eq73 eq142 | grind only

private theorem step_4_eq315 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq314 : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
  intro X0 X1 X2
  first | exact resolve eq314 rfl | grind only

private theorem step_4_eq316 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq315 : ∀ (X0 X1 X2 : G), ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2)) (eq52 : ∀ (X0 : G), ¬(old a b X0)) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ ¬(old b X0 X0) := by
  intro X0 X1 X2
  first | exact resolve eq315 eq52 | exact resolve eq52 eq315 | grind only

private theorem step_4_eq355 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq192 : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b)) : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) := by
  first | exact resolve eq192 eq78 | exact resolve eq78 eq192 | grind only

private theorem step_4_eq356 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq192 : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ a = sk2 := by
  first | exact resolve eq192 eq77 | exact resolve eq77 eq192 | grind only

private theorem step_4_eq357 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq192 : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ c = sk3 := by
  first | exact resolve eq192 eq76 | exact resolve eq76 eq192 | grind only

private theorem step_4_eq358 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq357 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ c = sk3) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk3 sk2 sk2) ∨ c = sk2 ∨ c = sk3 := by
  first | exact resolve eq357 eq86 | exact resolve eq86 eq357 | grind only

private theorem step_4_eq359 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq356 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ a = sk2) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk3 sk2 sk2) ∨ c = sk2 ∨ a = sk2 := by
  first | exact resolve eq356 eq87 | exact resolve eq87 eq356 | grind only

private theorem step_4_eq360 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq355 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b)) (eq89 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b)) : (old sk3 sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) := by
  first | exact resolve eq355 eq89 | exact resolve eq89 eq355 | grind only

private theorem step_4_eq362 {G : Type*} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq358 : (old sk3 sk2 sk2) ∨ c = sk2 ∨ c = sk3) (eq63 : ∀ (X0 X1 X2 X3 : G), ¬(old X3 X2 X2) ∨ ¬(old X1 X3 X0) ∨ ¬(old X3 X1 X2) ∨ ¬(old X0 X1 X2) ∨ (old X2 X3 X0)) : ∀ (X0 X1 : G), ¬(old sk3 X0 sk2) ∨ c = sk3 ∨ ¬(old X0 sk3 X1) ∨ c = sk2 ∨ ¬(old X1 X0 sk2) ∨ (old sk2 sk3 X1) := by
  intro X0 X1
  first | exact resolve eq358 eq63 | exact resolve eq63 eq358 | grind only

private theorem step_4_eq374 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq168 : (sP2 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 := by
  first | exact resolve eq168 eq77 | exact resolve eq77 eq168 | grind only

private theorem step_4_eq375 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq168 : (sP2 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq168 eq76 | exact resolve eq76 eq168 | grind only

private theorem step_4_eq376 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq375 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq375 eq86 | exact resolve eq86 eq375 | grind only

private theorem step_4_eq377 {G : Type*} {a : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq374 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 := by
  first | exact resolve eq374 eq87 | exact resolve eq87 eq374 | grind only

private theorem step_4_eq427 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq161 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2) (eq83 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
  first | exact resolve eq161 eq83 | exact resolve eq83 eq161 | grind only

private theorem step_4_eq428 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq161 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq161 eq82 | exact resolve eq82 eq161 | grind only

private theorem step_4_eq430 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq428 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq428 eq71 | exact resolve eq71 eq428 | grind only

private theorem step_4_eq431 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq427 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
  first | exact resolve eq427 eq72 | exact resolve eq72 eq427 | grind only

private theorem step_4_eq466 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq165 : (sP3 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 := by
  first | exact resolve eq165 eq82 | exact resolve eq82 eq165 | grind only

private theorem step_4_eq468 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq466 : (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 := by
  first | exact resolve eq466 eq71 | exact resolve eq71 eq466 | grind only

private theorem step_4_eq485 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq166 : (sP3 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 := by
  first | exact resolve eq166 eq82 | exact resolve eq82 eq166 | grind only

private theorem step_4_eq487 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq485 : (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 := by
  first | exact resolve eq485 eq71 | exact resolve eq71 eq485 | grind only

private theorem step_4_eq503 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq177 : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2) (eq83 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
  first | exact resolve eq177 eq83 | exact resolve eq83 eq177 | grind only

private theorem step_4_eq504 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq177 : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq177 eq82 | exact resolve eq82 eq177 | grind only

private theorem step_4_eq506 {G : Type*} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq504 : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
  first | exact resolve eq504 eq71 | exact resolve eq71 eq504 | grind only

private theorem step_4_eq507 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq503 : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
  first | exact resolve eq503 eq72 | exact resolve eq72 eq503 | grind only

private theorem step_4_eq515 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq178 : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq178 eq82 | exact resolve eq82 eq178 | grind only

private theorem step_4_eq517 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq515 : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq515 eq71 | exact resolve eq71 eq515 | grind only

private theorem step_4_eq531 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq316 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ ¬(old b X0 X0)) (eq376 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1) : ¬(old b sk1 sk1) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1 := by
  first | exact resolve eq316 eq376 | exact resolve eq376 eq316 | grind only

private theorem step_4_eq545 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP1 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq377 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0) (eq71 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 ∨ c = sk3 := by
  first | exact resolve eq377 eq71 | exact resolve eq71 eq377 | grind only

private theorem step_4_eq1061 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq430 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 := by
  first | exact resolve eq430 eq77 | exact resolve eq77 eq430 | grind only

private theorem step_4_eq1062 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq430 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq430 eq76 | exact resolve eq76 eq430 | grind only

private theorem step_4_eq1063 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1062 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq1062 eq86 | exact resolve eq86 eq1062 | grind only

private theorem step_4_eq1064 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1061 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 := by
  first | exact resolve eq1061 eq87 | exact resolve eq87 eq1061 | grind only

private theorem step_4_eq1078 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq431 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := by
  first | exact resolve eq431 eq77 | exact resolve eq77 eq431 | grind only

private theorem step_4_eq1081 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1078 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := by
  first | exact resolve eq1078 eq87 | exact resolve eq87 eq1078 | grind only

private theorem step_4_eq1127 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq468 : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3) (eq79 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) := by
  first | exact resolve eq468 eq79 | exact resolve eq79 eq468 | grind only

private theorem step_4_eq1129 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq468 : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq468 eq77 | exact resolve eq77 eq468 | grind only

private theorem step_4_eq1130 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq468 : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq468 eq76 | exact resolve eq76 eq468 | grind only

private theorem step_4_eq1131 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1130 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq1130 eq86 | exact resolve eq86 eq1130 | grind only

private theorem step_4_eq1132 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1129 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq1129 eq87 | exact resolve eq87 eq1129 | grind only

private theorem step_4_eq1134 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1127 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a)) (eq90 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) := by
  first | exact resolve eq1127 eq90 | exact resolve eq90 eq1127 | grind only

private theorem step_4_eq1163 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq487 : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq487 eq77 | exact resolve eq77 eq487 | grind only

private theorem step_4_eq1166 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1163 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 ∨ a = sk0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 ∨ a = sk0 := by
  first | exact resolve eq1163 eq87 | exact resolve eq87 eq1163 | grind only

private theorem step_4_eq1198 {G : Type*} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq506 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq506 eq76 | exact resolve eq76 eq506 | grind only

private theorem step_4_eq1199 {G : Type*} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1198 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq1198 eq86 | exact resolve eq86 eq1198 | grind only

private theorem step_4_eq1214 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq507 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := by
  first | exact resolve eq507 eq77 | exact resolve eq77 eq507 | grind only

private theorem step_4_eq1215 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq507 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2) (eq76 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 := by
  first | exact resolve eq507 eq76 | exact resolve eq76 eq507 | grind only

private theorem step_4_eq1216 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1215 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3) (eq86 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : (old sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 := by
  first | exact resolve eq1215 eq86 | exact resolve eq86 eq1215 | grind only

private theorem step_4_eq1217 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1214 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := by
  first | exact resolve eq1214 eq87 | exact resolve eq87 eq1214 | grind only

private theorem step_4_eq1231 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq517 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := by
  first | exact resolve eq517 eq77 | exact resolve eq77 eq517 | grind only

private theorem step_4_eq1234 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1231 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : (old sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := by
  first | exact resolve eq1231 eq87 | exact resolve eq87 eq1231 | grind only

private theorem step_4_eq3668 {G : Type*} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq362 : ∀ (X0 X1 : G), ¬(old sk3 X0 sk2) ∨ c = sk3 ∨ ¬(old X0 sk3 X1) ∨ c = sk2 ∨ ¬(old X1 X0 sk2) ∨ (old sk2 sk3 X1)) (eq1199 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3) : ∀ (X0 : G), c = sk3 ∨ ¬(old sk1 sk3 X0) ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 := by
  intro X0
  first | exact resolve eq362 eq1199 | exact resolve eq1199 eq362 | grind only

private theorem step_4_eq3687 {G : Type*} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq3668 : ∀ (X0 : G), c = sk3 ∨ ¬(old sk1 sk3 X0) ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3) : ∀ (X0 : G), ¬(old sk1 sk3 X0) ∨ c = sk3 ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ c = sk1 := by
  intro X0
  first | exact resolve eq3668 rfl | grind only

private theorem step_4_eq9561 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq3687 : ∀ (X0 : G), ¬(old sk1 sk3 X0) ∨ c = sk3 ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ c = sk1) (eq1131 : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1) : c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq3687 eq1131 | exact resolve eq1131 eq3687 | grind only

private theorem step_4_eq9588 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq9561 : c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ c = sk1) : c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq9561 rfl | grind only

private theorem step_4_eq9601 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq9588 : c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk0) (eq1063 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : (old sk2 sk3 sk0) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq9588 eq1063 | exact resolve eq1063 eq9588 | grind only

private theorem step_4_eq9628 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq9601 : (old sk2 sk3 sk0) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0) (eq65 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ (new sk2 sk3 sk0) := by
  first | exact resolve eq9601 eq65 | exact resolve eq65 eq9601 | grind only

private theorem step_4_eq9646 {G : Type*} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq9628 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ (new sk2 sk3 sk0)) (eq97 : ¬(new sk2 sk3 sk0)) : c = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq9628 eq97 | exact resolve eq97 eq9628 | grind only

private theorem step_4_eq9829 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1132 : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0) (eq9646 : c = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0) : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq1132 eq9646 | exact superpose eq9646 eq1132 | grind only

private theorem step_4_eq9831 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1134 : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a)) (eq9646 : c = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0) : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq1134 eq9646 | exact superpose eq9646 eq1134 | grind only

private theorem step_4_eq9853 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1216 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3) (eq9646 : c = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0) : (old sk3 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq1216 eq9646 | exact superpose eq9646 eq1216 | grind only

private theorem step_4_eq10139 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq9853 : (old sk3 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0) : (old sk3 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk0 := by
  first | exact resolve eq9853 rfl | grind only

private theorem step_4_eq10152 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq9831 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0) : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) ∨ c = sk2 := by
  first | exact resolve eq9831 rfl | grind only

private theorem step_4_eq10154 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq9829 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0) : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk2 := by
  first | exact resolve eq9829 rfl | grind only

private theorem step_4_eq10268 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq10139 : (old sk3 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk0) (eq55 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : c = sk0 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2 := by
  first | exact resolve eq10139 eq55 | exact resolve eq55 eq10139 | grind only

private theorem step_4_eq10280 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq10152 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) ∨ c = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : (old b sk3 a) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq10152 eq57 | exact resolve eq57 eq10152 | grind only

private theorem step_4_eq10282 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq10154 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk0 ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq10154 eq57 | exact resolve eq57 eq10154 | grind only

private theorem step_4_eq10465 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq545 : (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 ∨ c = sk3) (eq10268 : c = sk0 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2) : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2 := by
  first | exact superpose eq545 eq10268 | exact superpose eq10268 eq545 | grind only

private theorem step_4_eq10499 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq1081 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2) (eq10268 : c = sk0 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2) : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2 := by
  first | exact superpose eq1081 eq10268 | exact superpose eq10268 eq1081 | grind only

private theorem step_4_eq10668 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq10499 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2) : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ c = sk3 := by
  first | exact resolve eq10499 rfl | grind only

private theorem step_4_eq10681 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq10465 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2) : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq10465 rfl | grind only

private theorem step_4_eq10742 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq10668 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ c = sk3) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk3 ∨ b = sk2 ∨ a = sk2 ∨ c = sk2 := by
  first | exact resolve eq10668 eq57 | exact resolve eq57 eq10668 | grind only

private theorem step_4_eq10764 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq10681 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk2) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq10681 eq53 | exact resolve eq53 eq10681 | grind only

private theorem step_4_eq10826 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq10764 : a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk2) (eq50 : a ≠ c) : a = sk1 ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq10764 eq50 | exact resolve eq50 eq10764 | grind only

private theorem step_4_eq11310 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1217 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2) (eq10742 : c = sk3 ∨ b = sk2 ∨ a = sk2 ∨ c = sk2) : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ a = sk2 ∨ c = sk2 := by
  first | exact superpose eq1217 eq10742 | exact superpose eq10742 eq1217 | grind only

private theorem step_4_eq11523 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq11310 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ a = sk2 ∨ c = sk2) : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := by
  first | exact resolve eq11310 rfl | grind only

private theorem step_4_eq11642 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq11523 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk2 ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq11523 eq57 | exact resolve eq57 eq11523 | grind only

private theorem step_4_eq11762 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq97 : ¬(new sk2 sk3 sk0)) (eq11642 : a = sk2 ∨ b = sk2 ∨ c = sk2) : ¬(new a sk3 sk0) ∨ b = sk2 ∨ c = sk2 := by
  first | exact superpose eq97 eq11642 | exact superpose eq11642 eq97 | grind only

private theorem step_4_eq12823 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq94 : (new sk1 sk3 sk0)) (eq10826 : a = sk1 ∨ c = sk3 ∨ b = sk2 ∨ c = sk2) : (new a sk3 sk0) ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := by
  first | exact superpose eq94 eq10826 | exact superpose eq10826 eq94 | grind only

private theorem step_4_eq13675 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq12823 : (new a sk3 sk0) ∨ c = sk3 ∨ b = sk2 ∨ c = sk2) (eq11762 : ¬(new a sk3 sk0) ∨ b = sk2 ∨ c = sk2) : c = sk3 ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq12823 eq11762 | exact resolve eq11762 eq12823 | grind only

private theorem step_4_eq13750 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq360 : (old sk3 sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b)) (eq13675 : c = sk3 ∨ b = sk2 ∨ c = sk2) : (old c sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) ∨ b = sk2 ∨ c = sk2 := by
  first | exact superpose eq360 eq13675 | exact superpose eq13675 eq360 | grind only

private theorem step_4_eq14085 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq13750 : (old c sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) ∨ b = sk2 ∨ c = sk2) : (old c sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) ∨ b = sk2 := by
  first | exact resolve eq13750 rfl | grind only

private theorem step_4_eq14200 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq14085 : (old c sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) ∨ b = sk2) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : (old sk2 b b) ∨ c = sk2 ∨ b = sk2 := by
  first | exact resolve eq14085 eq57 | exact resolve eq57 eq14085 | grind only

private theorem step_4_eq14568 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq14200 : (old sk2 b b) ∨ c = sk2 ∨ b = sk2) (eq11642 : a = sk2 ∨ b = sk2 ∨ c = sk2) : (old a b b) ∨ a = c ∨ a = b ∨ b = sk2 ∨ c = sk2 := by
  first | exact superpose eq14200 eq11642 | exact superpose eq11642 eq14200 | grind only

private theorem step_4_eq14570 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} (eq14568 : (old a b b) ∨ a = c ∨ a = b ∨ b = sk2 ∨ c = sk2) (eq52 : ∀ (X0 : G), ¬(old a b X0)) : a = c ∨ a = b ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq14568 eq52 | exact resolve eq52 eq14568 | grind only

private theorem step_4_eq14571 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq14570 : a = c ∨ a = b ∨ b = sk2 ∨ c = sk2) (eq50 : a ≠ c) : a = b ∨ b = sk2 ∨ c = sk2 := by
  first | exact resolve eq14570 eq50 | exact resolve eq50 eq14570 | grind only

private theorem step_4_eq14572 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} (eq14571 : a = b ∨ b = sk2 ∨ c = sk2) (eq48 : a ≠ b) : c = sk2 ∨ b = sk2 := by
  first | exact resolve eq14571 eq48 | exact resolve eq48 eq14571 | grind only

private theorem step_4_eq14633 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq97 : ¬(new sk2 sk3 sk0)) (eq14572 : c = sk2 ∨ b = sk2) : ¬(new c sk3 sk0) ∨ b = sk2 := by
  first | exact superpose eq97 eq14572 | exact superpose eq14572 eq97 | grind only

private theorem step_4_eq14659 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq300 : (old sk3 sk2 sk2) ∨ b = sk2 ∨ c = sk3) (eq14572 : c = sk2 ∨ b = sk2) : (old sk3 c c) ∨ b = c ∨ c = sk3 ∨ b = sk2 := by
  first | exact superpose eq300 eq14572 | exact superpose eq14572 eq300 | grind only

private theorem step_4_eq14728 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq1234 : (old sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2) (eq14572 : c = sk2 ∨ b = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ b = sk2 := by
  first | exact superpose eq1234 eq14572 | exact superpose eq14572 eq1234 | grind only

private theorem step_4_eq14827 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk3 : G} (eq14728 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ b = sk2) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk1 ∨ c = sk1 ∨ a = c ∨ b = sk2 := by
  first | exact resolve eq14728 eq53 | exact resolve eq53 eq14728 | grind only

private theorem step_4_eq14872 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq14659 : (old sk3 c c) ∨ b = c ∨ c = sk3 ∨ b = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X0) : b = c ∨ c = sk3 ∨ b = sk2 := by
  first | exact resolve eq14659 eq54 | exact resolve eq54 eq14659 | grind only

private theorem step_4_eq14900 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq14827 : b = sk1 ∨ c = sk1 ∨ a = c ∨ b = sk2) (eq50 : a ≠ c) : c = sk1 ∨ b = sk1 ∨ b = sk2 := by
  first | exact resolve eq14827 eq50 | exact resolve eq50 eq14827 | grind only

private theorem step_4_eq14922 {G : Type*} {b : G} {c : G} {sk2 : G} {sk3 : G} (eq14872 : b = c ∨ c = sk3 ∨ b = sk2) (eq51 : b ≠ c) : c = sk3 ∨ b = sk2 := by
  first | exact resolve eq14872 eq51 | exact resolve eq51 eq14872 | grind only

private theorem step_4_eq14933 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq94 : (new sk1 sk3 sk0)) (eq14922 : c = sk3 ∨ b = sk2) : (new sk1 c sk0) ∨ b = sk2 := by
  first | exact superpose eq94 eq14922 | exact superpose eq14922 eq94 | grind only

private theorem step_4_eq15500 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq14633 : ¬(new c sk3 sk0) ∨ b = sk2) (eq14922 : c = sk3 ∨ b = sk2) : ¬(new c c sk0) ∨ b = sk2 ∨ b = sk2 := by
  first | exact superpose eq14633 eq14922 | exact superpose eq14922 eq14633 | grind only

private theorem step_4_eq15510 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq15500 : ¬(new c c sk0) ∨ b = sk2 ∨ b = sk2) : ¬(new c c sk0) ∨ b = sk2 := by
  first | exact resolve eq15500 rfl | grind only

private theorem step_4_eq16923 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq14933 : (new sk1 c sk0) ∨ b = sk2) (eq14900 : c = sk1 ∨ b = sk1 ∨ b = sk2) : (new c c sk0) ∨ b = sk2 ∨ b = sk1 ∨ b = sk2 := by
  first | exact superpose eq14933 eq14900 | exact superpose eq14900 eq14933 | grind only

private theorem step_4_eq16929 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq16923 : (new c c sk0) ∨ b = sk2 ∨ b = sk1 ∨ b = sk2) : (new c c sk0) ∨ b = sk2 ∨ b = sk1 := by
  first | exact resolve eq16923 rfl | grind only

private theorem step_4_eq17101 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq16929 : (new c c sk0) ∨ b = sk2 ∨ b = sk1) (eq15510 : ¬(new c c sk0) ∨ b = sk2) : b = sk1 ∨ b = sk2 := by
  first | exact resolve eq16929 eq15510 | exact resolve eq15510 eq16929 | grind only

private theorem step_4_eq17294 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq531 : ¬(old b sk1 sk1) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1) (eq17101 : b = sk1 ∨ b = sk2) : ¬(old b b b) ∨ (old b sk3 sk0) ∨ a = b ∨ b = c ∨ b = sk2 := by
  first | exact superpose eq531 eq17101 | exact superpose eq17101 eq531 | grind only

private theorem step_4_eq17885 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq17294 : ¬(old b b b) ∨ (old b sk3 sk0) ∨ a = b ∨ b = c ∨ b = sk2) (eq49 : ∀ (X0 : G), (old X0 X0 X0)) : (old b sk3 sk0) ∨ a = b ∨ b = c ∨ b = sk2 := by
  first | exact resolve eq17294 eq49 | exact resolve eq49 eq17294 | grind only

private theorem step_4_eq17928 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq17885 : (old b sk3 sk0) ∨ a = b ∨ b = c ∨ b = sk2) (eq48 : a ≠ b) : (old b sk3 sk0) ∨ b = c ∨ b = sk2 := by
  first | exact resolve eq17885 eq48 | exact resolve eq48 eq17885 | grind only

private theorem step_4_eq17942 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq17928 : (old b sk3 sk0) ∨ b = c ∨ b = sk2) (eq51 : b ≠ c) : (old b sk3 sk0) ∨ b = sk2 := by
  first | exact resolve eq17928 eq51 | exact resolve eq51 eq17928 | grind only

private theorem step_4_eq18369 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq17942 : (old b sk3 sk0) ∨ b = sk2) (eq14922 : c = sk3 ∨ b = sk2) : (old b c sk0) ∨ b = sk2 ∨ b = sk2 := by
  first | exact superpose eq17942 eq14922 | exact superpose eq14922 eq17942 | grind only

private theorem step_4_eq18379 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq18369 : (old b c sk0) ∨ b = sk2 ∨ b = sk2) : (old b c sk0) ∨ b = sk2 := by
  first | exact resolve eq18369 rfl | grind only

private theorem step_4_eq18417 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} (eq18379 : (old b c sk0) ∨ b = sk2) (eq56 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = sk2 ∨ b = c := by
  first | exact resolve eq18379 eq56 | exact resolve eq56 eq18379 | grind only

private theorem step_4_eq18435 {G : Type*} {b : G} {c : G} {sk2 : G} (eq18417 : b = sk2 ∨ b = c) (eq51 : b ≠ c) : b = sk2 := by
  first | exact resolve eq18417 eq51 | exact resolve eq51 eq18417 | grind only

private theorem step_4_eq18536 {G : Type*} {b : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq97 : ¬(new sk2 sk3 sk0)) (eq18435 : b = sk2) : ¬(new b sk3 sk0) := by
  first | exact superpose eq97 eq18435 | exact superpose eq18435 eq97 | grind only

private theorem step_4_eq18605 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq1064 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2) (eq18435 : b = sk2) : (old sk0 sk1 b) ∨ b = c ∨ c = sk1 ∨ a = b := by
  first | exact superpose eq1064 eq18435 | exact superpose eq18435 eq1064 | grind only

private theorem step_4_eq18730 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq18605 : (old sk0 sk1 b) ∨ b = c ∨ c = sk1 ∨ a = b) (eq51 : b ≠ c) : (old sk0 sk1 b) ∨ c = sk1 ∨ a = b := by
  first | exact resolve eq18605 eq51 | exact resolve eq51 eq18605 | grind only

private theorem step_4_eq18775 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq18730 : (old sk0 sk1 b) ∨ c = sk1 ∨ a = b) (eq48 : a ≠ b) : (old sk0 sk1 b) ∨ c = sk1 := by
  first | exact resolve eq18730 eq48 | exact resolve eq48 eq18730 | grind only

private theorem step_4_eq18973 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq18536 : ¬(new b sk3 sk0)) (eq10282 : a = sk0 ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) : ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq18536 eq10282 | exact superpose eq10282 eq18536 | grind only

private theorem step_4_eq18975 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq18973 : ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) (eq18435 : b = sk2) : b = c ∨ ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 := by
  first | simpa only [eq18435, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq18973 | grind only

private theorem step_4_eq18976 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq18975 : b = c ∨ ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0) (eq51 : b ≠ c) : ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 := by
  first | exact resolve eq18975 eq51 | exact resolve eq51 eq18975 | grind only

private theorem step_4_eq40291 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq10280 : (old b sk3 a) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) (eq65 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 X2) ∨ (new X0 X1 X2)) : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ (new b sk3 a) := by
  first | exact resolve eq10280 eq65 | exact resolve eq65 eq10280 | grind only

private theorem step_4_eq40314 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk3 : G} (eq40291 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ (new b sk3 a)) (eq18976 : ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0) : c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq40291 eq18976 | exact resolve eq18976 eq40291 | grind only

private theorem step_4_eq40322 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq40314 : c = sk3 ∨ c = sk0 ∨ c = sk2) (eq18435 : b = sk2) : b = c ∨ c = sk3 ∨ c = sk0 := by
  first | simpa only [eq18435, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq40314 | grind only

private theorem step_4_eq40328 {G : Type*} {b : G} {c : G} {sk0 : G} {sk3 : G} (eq40322 : b = c ∨ c = sk3 ∨ c = sk0) (eq51 : b ≠ c) : c = sk0 ∨ c = sk3 := by
  first | exact resolve eq40322 eq51 | exact resolve eq51 eq40322 | grind only

private theorem step_4_eq40417 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq545 : (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 ∨ c = sk3) (eq40328 : c = sk0 ∨ c = sk3) : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ c = sk3 := by
  first | exact superpose eq545 eq40328 | exact superpose eq40328 eq545 | grind only

private theorem step_4_eq40475 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq1166 : (old sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 ∨ a = sk0) (eq40328 : c = sk0 ∨ c = sk3) : (old sk1 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk3 := by
  first | exact superpose eq1166 eq40328 | exact superpose eq40328 eq1166 | grind only

private theorem step_4_eq40649 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq40475 : (old sk1 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk3) : (old sk1 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c := by
  first | exact resolve eq40475 rfl | grind only

private theorem step_4_eq40659 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq40417 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ c = sk3) : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 := by
  first | exact resolve eq40417 rfl | grind only

private theorem step_4_eq40717 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq40649 : (old sk1 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk3 ∨ c = sk3 ∨ a = c := by
  first | exact resolve eq40649 eq53 | exact resolve eq53 eq40649 | grind only

private theorem step_4_eq40738 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq40659 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3) (eq53 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : a = sk1 ∨ a = c ∨ c = sk3 := by
  first | exact resolve eq40659 eq53 | exact resolve eq53 eq40659 | grind only

private theorem step_4_eq40797 {G : Type*} {a : G} {b : G} {c : G} {sk3 : G} (eq40717 : b = sk3 ∨ c = sk3 ∨ a = c) (eq50 : a ≠ c) : c = sk3 ∨ b = sk3 := by
  first | exact resolve eq40717 eq50 | exact resolve eq50 eq40717 | grind only

private theorem step_4_eq40811 {G : Type*} {a : G} {c : G} {sk1 : G} {sk3 : G} (eq40738 : a = sk1 ∨ a = c ∨ c = sk3) (eq50 : a ≠ c) : a = sk1 ∨ c = sk3 := by
  first | exact resolve eq40738 eq50 | exact resolve eq50 eq40738 | grind only

private theorem step_4_eq40921 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq359 : (old sk3 sk2 sk2) ∨ c = sk2 ∨ a = sk2) (eq40797 : c = sk3 ∨ b = sk3) : (old c sk2 sk2) ∨ c = sk2 ∨ a = sk2 ∨ b = sk3 := by
  first | exact superpose eq359 eq40797 | exact superpose eq40797 eq359 | grind only

private theorem step_4_eq41410 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk2 : G} {sk3 : G} (eq40921 : (old c sk2 sk2) ∨ c = sk2 ∨ a = sk2 ∨ b = sk3) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk2 ∨ a = sk2 ∨ b = sk3 := by
  first | exact resolve eq40921 eq57 | exact resolve eq57 eq40921 | grind only

private theorem step_4_eq41498 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} {sk3 : G} (eq41410 : c = sk2 ∨ a = sk2 ∨ b = sk3) (eq18435 : b = sk2) : b = c ∨ a = sk2 ∨ b = sk3 := by
  first | simpa only [eq18435, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq41410 | grind only

private theorem step_4_eq41549 {G : Type*} {a : G} {b : G} {c : G} {sk2 : G} {sk3 : G} (eq41498 : b = c ∨ a = sk2 ∨ b = sk3) (eq51 : b ≠ c) : a = sk2 ∨ b = sk3 := by
  first | exact resolve eq41498 eq51 | exact resolve eq51 eq41498 | grind only

private theorem step_4_eq41579 {G : Type*} {a : G} {b : G} {sk2 : G} {sk3 : G} (eq41549 : a = sk2 ∨ b = sk3) (eq18435 : b = sk2) : a = b ∨ b = sk3 := by
  first | simpa only [eq18435, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq41549 | grind only

private theorem step_4_eq41593 {G : Type*} {a : G} {b : G} {sk3 : G} (eq41579 : a = b ∨ b = sk3) (eq48 : a ≠ b) : b = sk3 := by
  first | exact resolve eq41579 eq48 | exact resolve eq48 eq41579 | grind only

private theorem step_4_eq43792 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq18775 : (old sk0 sk1 b) ∨ c = sk1) (eq40811 : a = sk1 ∨ c = sk3) : (old sk0 a b) ∨ a = c ∨ c = sk3 := by
  first | exact superpose eq18775 eq40811 | exact superpose eq40811 eq18775 | grind only

private theorem step_4_eq43961 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq43792 : (old sk0 a b) ∨ a = c ∨ c = sk3) (eq50 : a ≠ c) : (old sk0 a b) ∨ c = sk3 := by
  first | exact resolve eq43792 eq50 | exact resolve eq50 eq43792 | grind only

private theorem step_4_eq44102 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq43961 : (old sk0 a b) ∨ c = sk3) (eq41593 : b = sk3) : b = c ∨ (old sk0 a b) := by
  first | simpa only [eq41593, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq43961 | grind only

private theorem step_4_eq44235 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} (eq44102 : b = c ∨ (old sk0 a b)) (eq51 : b ≠ c) : (old sk0 a b) := by
  first | exact resolve eq44102 eq51 | exact resolve eq51 eq44102 | grind only

private theorem step_4_eq44721 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq44235 : (old sk0 a b)) (eq40328 : c = sk0 ∨ c = sk3) : (old c a b) ∨ c = sk3 := by
  first | exact superpose eq44235 eq40328 | exact superpose eq40328 eq44235 | grind only

private theorem step_4_eq44727 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk3 : G} (eq44721 : (old c a b) ∨ c = sk3) (eq41593 : b = sk3) : b = c ∨ (old c a b) := by
  first | simpa only [eq41593, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq44721 | grind only

private theorem step_4_eq44728 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} (eq44727 : b = c ∨ (old c a b)) (eq51 : b ≠ c) : (old c a b) := by
  first | exact resolve eq44727 eq51 | exact resolve eq51 eq44727 | grind only

private theorem step_4_eq44767 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} (eq44728 : (old c a b)) (eq57 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : b = c := by
  first | exact resolve eq44728 eq57 | exact resolve eq57 eq44728 | grind only

set_option maxHeartbeats 2000000 in
private theorem preserve_4 (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (ab : a ≠ b) (diagonal : ∀ x, old x x x) (ac : a ≠ c) (bc : b ≠ c) (p3 : ∀ z, ¬ old a b z) (p4XY : ∀ x y, old x y c → x = c ∧ y = c) (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ ¬ old X2 X1 X3 ∨ old X3 X0 X2)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X0 ∨ ¬ old X3 X1 X2 ∨ ¬ old X3 X2 X2 ∨ old X2 X3 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬ sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X1 X3 X0 ∨ ¬ new X3 X1 X2 ∨ ¬ new X3 X2 X2 ∨ new X2 X3 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq48 : a ≠ b := step_4_eq48 ab
  have eq49 (X0 : G) : (old X0 X0 X0) := step_4_eq49 diagonal X0
  have eq50 : a ≠ c := step_4_eq50 ac
  have eq51 : b ≠ c := step_4_eq51 bc
  have eq52 (X0 : G) : ¬(old a b X0) := step_4_eq52 p3 X0
  have eq53 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X1 := step_4_eq53 p4XY X0 X1
  have eq54 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X0 := step_4_eq54 p4XY X0 X1
  have eq55 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X1 := step_4_eq55 p4XZ X0 X1
  have eq56 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X0 := step_4_eq56 p4XZ X0 X1
  have eq57 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X1 := step_4_eq57 p4YZ X0 X1
  have eq61 (X0 X1 X2 X3 : G) : ¬(old X2 X1 X3) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X1 X1) ∨ (old X3 X0 X2) := step_4_eq61 old_2 X0 X1 X2 X3
  have eq63 (X0 X1 X2 X3 : G) : ¬(old X3 X2 X2) ∨ ¬(old X1 X3 X0) ∨ ¬(old X3 X1 X2) ∨ ¬(old X0 X1 X2) ∨ (old X2 X3 X0) := step_4_eq63 old_4 X0 X1 X2 X3
  have eq65 (X0 X1 X2 : G) : ¬(old X0 X1 X2) ∨ (new X0 X1 X2) := step_4_eq65 imp_new_0 X0 X1 X2
  have eq67 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ a = X0 := step_4_eq67 rule_def_0_0 X0 X1 X2
  have eq68 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ b = X1 := step_4_eq68 rule_def_0_1 X0 X1 X2
  have eq69 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ c = X2 := step_4_eq69 rule_def_0_2 X0 X1 X2
  have eq71 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ c = X1 := step_4_eq71 rule_def_1_0 X0 X1 X2
  have eq72 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ b = X2 := step_4_eq72 rule_def_1_1 X0 X1 X2
  have eq73 (X0 X1 X2 : G) : (old X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := step_4_eq73 rule_def_1_2 X0 X1 X2
  have eq74 (X0 X1 X2 : G) : (old (sF0 X0 X1 X2) X0 a) ∨ ¬(sP1 X0 X1 X2) := step_4_eq74 rule_def_1_3 X0 X1 X2
  have eq76 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ c = X0 := step_4_eq76 rule_def_2_0 X0 X1 X2
  have eq77 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = X2 := step_4_eq77 rule_def_2_1 X0 X1 X2
  have eq78 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := step_4_eq78 rule_def_2_2 X0 X1 X2
  have eq79 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := step_4_eq79 rule_def_2_3 X0 X1 X2
  have eq81 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = X0 := step_4_eq81 rule_def_3_0 X0 X1 X2
  have eq82 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ c = X1 := step_4_eq82 rule_def_3_1 X0 X1 X2
  have eq83 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ b = X2 := step_4_eq83 rule_def_3_2 X0 X1 X2
  have eq86 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ c = X0 := step_4_eq86 rule_def_4_0 X0 X1 X2
  have eq87 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = X2 := step_4_eq87 rule_def_4_1 X0 X1 X2
  have eq89 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := step_4_eq89 rule_def_4_3 X0 X1 X2
  have eq90 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := step_4_eq90 rule_def_4_4 X0 X1 X2
  have eq92 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP0 X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := step_4_eq92 new_imp X0 X1 X2
  have eq93 : (new sk0 sk1 sk2) := step_4_eq93 preserve_0
  have eq94 : (new sk1 sk3 sk0) := step_4_eq94 preserve_1
  have eq95 : (new sk3 sk1 sk2) := step_4_eq95 preserve_2
  have eq96 : (new sk3 sk2 sk2) := step_4_eq96 preserve_3
  have eq97 : ¬(new sk2 sk3 sk0) := step_4_eq97 preserve_4
  have eq142 (X0 X1 X2 X3 : G) : ¬(old X0 X1 (sF0 X0 X2 X3)) ∨ ¬(old X1 X0 X0) ∨ (old a X1 (sF0 X0 X2 X3)) ∨ ¬(sP1 X0 X2 X3) := step_4_eq142 eq61 eq74 X0 X1 X2 X3
  have eq155 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) := step_4_eq155 eq92 eq93
  have eq156 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) := step_4_eq156 eq92 eq94
  have eq157 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) := step_4_eq157 eq92 eq95
  have eq158 : (sP0 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) := step_4_eq158 eq92 eq96
  have eq161 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 := step_4_eq161 eq155 eq69
  have eq165 : (sP3 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 := step_4_eq165 eq156 eq69
  have eq166 : (sP3 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 := step_4_eq166 eq156 eq68
  have eq167 : (old sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (sP3 sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 := step_4_eq167 eq156 eq67
  have eq168 : (sP2 sk1 sk3 sk0) ∨ (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 := step_4_eq168 eq167 eq81
  have eq177 : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 := step_4_eq177 eq157 eq69
  have eq178 : (sP3 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 := step_4_eq178 eq157 eq68
  have eq185 : (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 := step_4_eq185 eq158 eq69
  have eq186 : (old sk3 sk2 sk2) ∨ (sP1 sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 := step_4_eq186 eq158 eq68
  have eq189 : (old sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 := step_4_eq189 eq186 eq72
  have eq190 : (old sk3 sk2 sk2) ∨ (sP2 sk3 sk2 sk2) ∨ (sP3 sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 := step_4_eq190 eq185 eq71
  have eq191 : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 := step_4_eq191 eq189 eq83
  have eq192 : (sP2 sk3 sk2 sk2) ∨ (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 := step_4_eq192 eq190 eq82
  have eq299 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ b = sk2 ∨ c = sk3 := step_4_eq299 eq191 eq76
  have eq300 : (old sk3 sk2 sk2) ∨ b = sk2 ∨ c = sk3 := step_4_eq300 eq299 eq86
  have eq314 (X0 X1 X2 : G) : ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := step_4_eq314 eq142 eq73 X0 X1 X2
  have eq315 (X0 X1 X2 : G) : ¬(old b X0 X0) ∨ (old a b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := step_4_eq315 eq314 X0 X1 X2
  have eq316 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old b X0 X0) := step_4_eq316 eq315 eq52 X0 X1 X2
  have eq355 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) := step_4_eq355 eq192 eq78
  have eq356 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ a = sk2 := step_4_eq356 eq192 eq77
  have eq357 : (old sk3 sk2 sk2) ∨ (sP4 sk3 sk2 sk2) ∨ c = sk2 ∨ c = sk3 := step_4_eq357 eq192 eq76
  have eq358 : (old sk3 sk2 sk2) ∨ c = sk2 ∨ c = sk3 := step_4_eq358 eq357 eq86
  have eq359 : (old sk3 sk2 sk2) ∨ c = sk2 ∨ a = sk2 := step_4_eq359 eq356 eq87
  have eq360 : (old sk3 sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) := step_4_eq360 eq355 eq89
  have eq362 (X0 X1 : G) : ¬(old sk3 X0 sk2) ∨ c = sk3 ∨ ¬(old X0 sk3 X1) ∨ c = sk2 ∨ ¬(old X1 X0 sk2) ∨ (old sk2 sk3 X1) := step_4_eq362 eq358 eq63 X0 X1
  have eq374 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 := step_4_eq374 eq168 eq77
  have eq375 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1 := step_4_eq375 eq168 eq76
  have eq376 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1 := step_4_eq376 eq375 eq86
  have eq377 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 := step_4_eq377 eq374 eq87
  have eq427 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := step_4_eq427 eq161 eq83
  have eq428 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := step_4_eq428 eq161 eq82
  have eq430 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := step_4_eq430 eq428 eq71
  have eq431 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := step_4_eq431 eq427 eq72
  have eq466 : (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 := step_4_eq466 eq165 eq82
  have eq468 : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 := step_4_eq468 eq466 eq71
  have eq485 : (sP1 sk1 sk3 sk0) ∨ (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 := step_4_eq485 eq166 eq82
  have eq487 : (sP2 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 := step_4_eq487 eq485 eq71
  have eq503 : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := step_4_eq503 eq177 eq83
  have eq504 : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := step_4_eq504 eq177 eq82
  have eq506 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := step_4_eq506 eq504 eq71
  have eq507 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := step_4_eq507 eq503 eq72
  have eq515 : (sP1 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := step_4_eq515 eq178 eq82
  have eq517 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := step_4_eq517 eq515 eq71
  have eq531 : ¬(old b sk1 sk1) ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ c = sk1 := step_4_eq531 eq316 eq376
  have eq545 : (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk0 ∨ c = sk3 := step_4_eq545 eq377 eq71
  have eq1061 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 := step_4_eq1061 eq430 eq77
  have eq1062 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_4_eq1062 eq430 eq76
  have eq1063 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_4_eq1063 eq1062 eq86
  have eq1064 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk2 := step_4_eq1064 eq1061 eq87
  have eq1078 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := step_4_eq1078 eq431 eq77
  have eq1081 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := step_4_eq1081 eq1078 eq87
  have eq1127 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) := step_4_eq1127 eq468 eq79
  have eq1129 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 := step_4_eq1129 eq468 eq77
  have eq1130 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := step_4_eq1130 eq468 eq76
  have eq1131 : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := step_4_eq1131 eq1130 eq86
  have eq1132 : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 := step_4_eq1132 eq1129 eq87
  have eq1134 : (old sk1 sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) := step_4_eq1134 eq1127 eq90
  have eq1163 : (old sk1 sk3 sk0) ∨ (sP4 sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 ∨ a = sk0 := step_4_eq1163 eq487 eq77
  have eq1166 : (old sk1 sk3 sk0) ∨ b = sk3 ∨ c = sk3 ∨ a = sk0 := step_4_eq1166 eq1163 eq87
  have eq1198 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 := step_4_eq1198 eq506 eq76
  have eq1199 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 := step_4_eq1199 eq1198 eq86
  have eq1214 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := step_4_eq1214 eq507 eq77
  have eq1215 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 := step_4_eq1215 eq507 eq76
  have eq1216 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 := step_4_eq1216 eq1215 eq86
  have eq1217 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := step_4_eq1217 eq1214 eq87
  have eq1231 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := step_4_eq1231 eq517 eq77
  have eq1234 : (old sk3 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := step_4_eq1234 eq1231 eq87
  have eq3668 (X0 : G) : c = sk3 ∨ ¬(old sk1 sk3 X0) ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 := step_4_eq3668 eq362 eq1199 X0
  have eq3687 (X0 : G) : ¬(old sk1 sk3 X0) ∨ c = sk3 ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ c = sk1 := step_4_eq3687 eq3668 X0
  have eq9561 : c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := step_4_eq9561 eq3687 eq1131
  have eq9588 : c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk0 := step_4_eq9588 eq9561
  have eq9601 : (old sk2 sk3 sk0) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := step_4_eq9601 eq9588 eq1063
  have eq9628 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ (new sk2 sk3 sk0) := step_4_eq9628 eq9601 eq65
  have eq9646 : c = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := step_4_eq9646 eq9628 eq97
  have eq9829 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := step_4_eq9829 eq1132 eq9646
  have eq9831 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := step_4_eq9831 eq1134 eq9646
  have eq9853 : (old sk3 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := step_4_eq9853 eq1216 eq9646
  have eq10139 : (old sk3 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk0 := step_4_eq10139 eq9853
  have eq10152 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ (old b sk3 a) ∨ c = sk2 := step_4_eq10152 eq9831
  have eq10154 : (old c sk3 sk0) ∨ c = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk2 := step_4_eq10154 eq9829
  have eq10268 : c = sk0 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2 := step_4_eq10268 eq10139 eq55
  have eq10280 : (old b sk3 a) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_4_eq10280 eq10152 eq57
  have eq10282 : a = sk0 ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_4_eq10282 eq10154 eq57
  have eq10465 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2 := step_4_eq10465 eq545 eq10268
  have eq10499 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk3 ∨ c = sk2 := step_4_eq10499 eq1081 eq10268
  have eq10668 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ c = sk3 := step_4_eq10668 eq10499
  have eq10681 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := step_4_eq10681 eq10465
  have eq10742 : c = sk3 ∨ b = sk2 ∨ a = sk2 ∨ c = sk2 := step_4_eq10742 eq10668 eq57
  have eq10764 : a = sk1 ∨ a = c ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := step_4_eq10764 eq10681 eq53
  have eq10826 : a = sk1 ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := step_4_eq10826 eq10764 eq50
  have eq11310 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ a = sk2 ∨ c = sk2 := step_4_eq11310 eq1217 eq10742
  have eq11523 : (old c sk1 sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := step_4_eq11523 eq11310
  have eq11642 : a = sk2 ∨ b = sk2 ∨ c = sk2 := step_4_eq11642 eq11523 eq57
  have eq11762 : ¬(new a sk3 sk0) ∨ b = sk2 ∨ c = sk2 := step_4_eq11762 eq97 eq11642
  have eq12823 : (new a sk3 sk0) ∨ c = sk3 ∨ b = sk2 ∨ c = sk2 := step_4_eq12823 eq94 eq10826
  have eq13675 : c = sk3 ∨ b = sk2 ∨ c = sk2 := step_4_eq13675 eq12823 eq11762
  have eq13750 : (old c sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) ∨ b = sk2 ∨ c = sk2 := step_4_eq13750 eq360 eq13675
  have eq14085 : (old c sk2 sk2) ∨ c = sk2 ∨ (old sk2 b b) ∨ b = sk2 := step_4_eq14085 eq13750
  have eq14200 : (old sk2 b b) ∨ c = sk2 ∨ b = sk2 := step_4_eq14200 eq14085 eq57
  have eq14568 : (old a b b) ∨ a = c ∨ a = b ∨ b = sk2 ∨ c = sk2 := step_4_eq14568 eq14200 eq11642
  have eq14570 : a = c ∨ a = b ∨ b = sk2 ∨ c = sk2 := step_4_eq14570 eq14568 eq52
  have eq14571 : a = b ∨ b = sk2 ∨ c = sk2 := step_4_eq14571 eq14570 eq50
  have eq14572 : c = sk2 ∨ b = sk2 := step_4_eq14572 eq14571 eq48
  have eq14633 : ¬(new c sk3 sk0) ∨ b = sk2 := step_4_eq14633 eq97 eq14572
  have eq14659 : (old sk3 c c) ∨ b = c ∨ c = sk3 ∨ b = sk2 := step_4_eq14659 eq300 eq14572
  have eq14728 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ b = sk2 := step_4_eq14728 eq1234 eq14572
  have eq14827 : b = sk1 ∨ c = sk1 ∨ a = c ∨ b = sk2 := step_4_eq14827 eq14728 eq53
  have eq14872 : b = c ∨ c = sk3 ∨ b = sk2 := step_4_eq14872 eq14659 eq54
  have eq14900 : c = sk1 ∨ b = sk1 ∨ b = sk2 := step_4_eq14900 eq14827 eq50
  have eq14922 : c = sk3 ∨ b = sk2 := step_4_eq14922 eq14872 eq51
  have eq14933 : (new sk1 c sk0) ∨ b = sk2 := step_4_eq14933 eq94 eq14922
  have eq15500 : ¬(new c c sk0) ∨ b = sk2 ∨ b = sk2 := step_4_eq15500 eq14633 eq14922
  have eq15510 : ¬(new c c sk0) ∨ b = sk2 := step_4_eq15510 eq15500
  have eq16923 : (new c c sk0) ∨ b = sk2 ∨ b = sk1 ∨ b = sk2 := step_4_eq16923 eq14933 eq14900
  have eq16929 : (new c c sk0) ∨ b = sk2 ∨ b = sk1 := step_4_eq16929 eq16923
  have eq17101 : b = sk1 ∨ b = sk2 := step_4_eq17101 eq16929 eq15510
  have eq17294 : ¬(old b b b) ∨ (old b sk3 sk0) ∨ a = b ∨ b = c ∨ b = sk2 := step_4_eq17294 eq531 eq17101
  have eq17885 : (old b sk3 sk0) ∨ a = b ∨ b = c ∨ b = sk2 := step_4_eq17885 eq17294 eq49
  have eq17928 : (old b sk3 sk0) ∨ b = c ∨ b = sk2 := step_4_eq17928 eq17885 eq48
  have eq17942 : (old b sk3 sk0) ∨ b = sk2 := step_4_eq17942 eq17928 eq51
  have eq18369 : (old b c sk0) ∨ b = sk2 ∨ b = sk2 := step_4_eq18369 eq17942 eq14922
  have eq18379 : (old b c sk0) ∨ b = sk2 := step_4_eq18379 eq18369
  have eq18417 : b = sk2 ∨ b = c := step_4_eq18417 eq18379 eq56
  have eq18435 : b = sk2 := step_4_eq18435 eq18417 eq51
  have eq18536 : ¬(new b sk3 sk0) := step_4_eq18536 eq97 eq18435
  have eq18605 : (old sk0 sk1 b) ∨ b = c ∨ c = sk1 ∨ a = b := step_4_eq18605 eq1064 eq18435
  have eq18730 : (old sk0 sk1 b) ∨ c = sk1 ∨ a = b := step_4_eq18730 eq18605 eq51
  have eq18775 : (old sk0 sk1 b) ∨ c = sk1 := step_4_eq18775 eq18730 eq48
  have eq18973 : ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_4_eq18973 eq18536 eq10282
  have eq18975 : b = c ∨ ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 := step_4_eq18975 eq18973 eq18435
  have eq18976 : ¬(new b sk3 a) ∨ c = sk3 ∨ c = sk0 := step_4_eq18976 eq18975 eq51
  have eq40291 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ (new b sk3 a) := step_4_eq40291 eq10280 eq65
  have eq40314 : c = sk3 ∨ c = sk0 ∨ c = sk2 := step_4_eq40314 eq40291 eq18976
  have eq40322 : b = c ∨ c = sk3 ∨ c = sk0 := step_4_eq40322 eq40314 eq18435
  have eq40328 : c = sk0 ∨ c = sk3 := step_4_eq40328 eq40322 eq51
  have eq40417 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 ∨ c = sk3 := step_4_eq40417 eq545 eq40328
  have eq40475 : (old sk1 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk3 := step_4_eq40475 eq1166 eq40328
  have eq40649 : (old sk1 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c := step_4_eq40649 eq40475
  have eq40659 : (old sk1 sk3 c) ∨ a = sk1 ∨ a = c ∨ c = sk3 := step_4_eq40659 eq40417
  have eq40717 : b = sk3 ∨ c = sk3 ∨ a = c := step_4_eq40717 eq40649 eq53
  have eq40738 : a = sk1 ∨ a = c ∨ c = sk3 := step_4_eq40738 eq40659 eq53
  have eq40797 : c = sk3 ∨ b = sk3 := step_4_eq40797 eq40717 eq50
  have eq40811 : a = sk1 ∨ c = sk3 := step_4_eq40811 eq40738 eq50
  have eq40921 : (old c sk2 sk2) ∨ c = sk2 ∨ a = sk2 ∨ b = sk3 := step_4_eq40921 eq359 eq40797
  have eq41410 : c = sk2 ∨ a = sk2 ∨ b = sk3 := step_4_eq41410 eq40921 eq57
  have eq41498 : b = c ∨ a = sk2 ∨ b = sk3 := step_4_eq41498 eq41410 eq18435
  have eq41549 : a = sk2 ∨ b = sk3 := step_4_eq41549 eq41498 eq51
  have eq41579 : a = b ∨ b = sk3 := step_4_eq41579 eq41549 eq18435
  have eq41593 : b = sk3 := step_4_eq41593 eq41579 eq48
  have eq43792 : (old sk0 a b) ∨ a = c ∨ c = sk3 := step_4_eq43792 eq18775 eq40811
  have eq43961 : (old sk0 a b) ∨ c = sk3 := step_4_eq43961 eq43792 eq50
  have eq44102 : b = c ∨ (old sk0 a b) := step_4_eq44102 eq43961 eq41593
  have eq44235 : (old sk0 a b) := step_4_eq44235 eq44102 eq51
  have eq44721 : (old c a b) ∨ c = sk3 := step_4_eq44721 eq44235 eq40328
  have eq44727 : b = c ∨ (old c a b) := step_4_eq44727 eq44721 eq41593
  have eq44728 : (old c a b) := step_4_eq44728 eq44727 eq51
  have eq44767 : b = c := step_4_eq44767 eq44728 eq57
  clear * - eq44767 eq51
  first | subsumption eq44767 eq51 | grind only


private theorem step_5_eq49 {G : Type*} {a : G} {b : G} (ab : a ≠ b) : a ≠ b := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ab | grind only

private theorem step_5_eq50 {G : Type*} {old : G → G → G → Prop} (diagonal : ∀ x, old x x x) : ∀ (X0 : G), (old X0 X0 X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using diagonal | grind only

private theorem step_5_eq51 {G : Type*} {a : G} {c : G} (ac : a ≠ c) : a ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using ac | grind only

private theorem step_5_eq52 {G : Type*} {b : G} {c : G} (bc : b ≠ c) : b ≠ c := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using bc | grind only

private theorem step_5_eq53 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (p3 : ∀ z, ¬ old a b z) : ∀ (X0 : G), ¬(old a b X0) := by
  intro X0
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p3 | grind only

private theorem step_5_eq54 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XY : ∀ x y, old x y c → x = c ∧ y = c) : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XY | grind only

private theorem step_5_eq56 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_5_eq57 {G : Type*} {c : G} {old : G → G → G → Prop} (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4XZ | grind only

private theorem step_5_eq58 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_5_eq59 {G : Type*} {c : G} {old : G → G → G → Prop} (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0 := by
  intro X0 X1
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using p4YZ | grind only

private theorem step_5_eq60 {G : Type*} {old : G → G → G → Prop} (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_0 | grind only

private theorem step_5_eq62 {G : Type*} {old : G → G → G → Prop} (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ ¬ old X2 X1 X3 ∨ old X3 X0 X2)) : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ ¬(old X2 X1 X3) ∨ (old X3 X0 X2) := by
  intro X0 X1 X2 X3
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_2 | grind only

private theorem step_5_eq65 {G : Type*} {old : G → G → G → Prop} (old_5 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X1 X0 X3 ∨ ¬ old X2 X0 X4 ∨ ¬ old X3 X1 X5 ∨ ¬ old X5 X3 X4 ∨ old X4 X1 X2)) : ∀ (X0 X1 X2 X3 X4 X5 : G), ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2) := by
  intro X0 X1 X2 X3 X4 X5
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using old_5 | grind only

private theorem step_5_eq66 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : ∀ (X0 X1 X2 : G), (new X0 X1 X2) ∨ ¬(old X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_0 | grind only

private theorem step_5_eq68 {G : Type*} {a : G} {sP0 : G → G → G → Prop} (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_0 | grind only

private theorem step_5_eq69 {G : Type*} {b : G} {sP0 : G → G → G → Prop} (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_1 | grind only

private theorem step_5_eq70 {G : Type*} {c : G} {sP0 : G → G → G → Prop} (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_0_2 | grind only

private theorem step_5_eq72 {G : Type*} {c : G} {sP1 : G → G → G → Prop} (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_0 | grind only

private theorem step_5_eq73 {G : Type*} {b : G} {sP1 : G → G → G → Prop} (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_1 | grind only

private theorem step_5_eq75 {G : Type*} {a : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_1_3 | grind only

private theorem step_5_eq76 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (imp_new_3 : ∀ X Y Z, c ≠ X ∨ a ≠ Z ∨ ¬ old Y b b ∨ ¬ old b Y a ∨ new X Y Z) : ∀ (X0 X1 X2 : G), c ≠ X0 ∨ a ≠ X2 ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using imp_new_3 | grind only

private theorem step_5_eq77 {G : Type*} {c : G} {sP2 : G → G → G → Prop} (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_0 | grind only

private theorem step_5_eq78 {G : Type*} {a : G} {sP2 : G → G → G → Prop} (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_1 | grind only

private theorem step_5_eq79 {G : Type*} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_2 | grind only

private theorem step_5_eq80 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP2 : G → G → G → Prop} (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_2_3 | grind only

private theorem step_5_eq82 {G : Type*} {a : G} {sP3 : G → G → G → Prop} (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_0 | grind only

private theorem step_5_eq83 {G : Type*} {c : G} {sP3 : G → G → G → Prop} (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_1 | grind only

private theorem step_5_eq84 {G : Type*} {b : G} {sP3 : G → G → G → Prop} (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_3_2 | grind only

private theorem step_5_eq87 {G : Type*} {c : G} {sP4 : G → G → G → Prop} (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_0 | grind only

private theorem step_5_eq88 {G : Type*} {a : G} {sP4 : G → G → G → Prop} (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2 := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_1 | grind only

private theorem step_5_eq89 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_2 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_2 | grind only

private theorem step_5_eq90 {G : Type*} {b : G} {old : G → G → G → Prop} {sP4 : G → G → G → Prop} (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using rule_def_4_3 | grind only

private theorem step_5_eq92 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} (new_new : new a b c) : (new a b c) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_new | grind only

private theorem step_5_eq93 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := by
  intro X0 X1 X2
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using new_imp | grind only

private theorem step_5_eq94 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (preserve_0 : new sk0 sk1 sk2) : (new sk0 sk1 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_0 | grind only

private theorem step_5_eq95 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (preserve_1 : new sk1 sk0 sk3) : (new sk1 sk0 sk3) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_1 | grind only

private theorem step_5_eq96 {G : Type*} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (preserve_2 : new sk2 sk0 sk4) : (new sk2 sk0 sk4) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_2 | grind only

private theorem step_5_eq97 {G : Type*} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (preserve_3 : new sk3 sk1 sk5) : (new sk3 sk1 sk5) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_3 | grind only

private theorem step_5_eq98 {G : Type*} {new : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (preserve_4 : new sk5 sk3 sk4) : (new sk5 sk3 sk4) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_4 | grind only

private theorem step_5_eq99 {G : Type*} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (preserve_5 : ¬ (new sk4 sk1 sk2)) : ¬(new sk4 sk1 sk2) := by
  first | simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using preserve_5 | grind only

private theorem step_5_eq105 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq76 : ∀ (X0 X1 X2 : G), c ≠ X0 ∨ a ≠ X2 ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new X0 X1 X2)) : ∀ (X1 X2 : G), a ≠ X2 ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 X2) := by
  intro X1 X2
  first | exact resolve eq76 rfl | grind only

private theorem step_5_eq106 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} (eq105 : ∀ (X1 X2 : G), a ≠ X2 ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 X2)) : ∀ (X1 : G), (new c X1 a) ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) := by
  intro X1
  first | exact resolve eq105 rfl | grind only

private theorem step_5_eq119 {G : Type*} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq66 : ∀ (X0 X1 X2 : G), (new X0 X1 X2) ∨ ¬(old X0 X1 X2)) (eq99 : ¬(new sk4 sk1 sk2)) : ¬(old sk4 sk1 sk2) := by
  first | exact resolve eq66 eq99 | exact resolve eq99 eq66 | grind only

private theorem step_5_eq120 {G : Type*} {old : G → G → G → Prop} (eq60 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) (eq50 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1 := by
  intro X0 X1
  first | exact resolve eq60 eq50 | exact resolve eq50 eq60 | grind only

private theorem step_5_eq127 {G : Type*} {old : G → G → G → Prop} (eq62 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ ¬(old X2 X1 X3) ∨ (old X3 X0 X2)) (eq50 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 X2 : G), ¬(old X0 X0 X1) ∨ ¬(old X1 X0 X2) ∨ (old X2 X0 X1) := by
  intro X0 X1 X2
  first | exact resolve eq62 eq50 | exact resolve eq50 eq62 | grind only

private theorem step_5_eq128 {G : Type*} {old : G → G → G → Prop} (eq127 : ∀ (X0 X1 X2 : G), ¬(old X0 X0 X1) ∨ ¬(old X1 X0 X2) ∨ (old X2 X0 X1)) (eq50 : ∀ (X0 : G), (old X0 X0 X0)) : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ (old X1 X0 X0) := by
  intro X0 X1
  first | exact resolve eq127 eq50 | exact resolve eq50 eq127 | grind only

private theorem step_5_eq133 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq93 : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq70 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ c = X2) : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 := by
  intro X0 X1 X2
  first | exact resolve eq93 eq70 | exact resolve eq70 eq93 | grind only

private theorem step_5_eq134 {G : Type*} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq93 : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq69 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ b = X1) : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 := by
  intro X0 X1 X2
  first | exact resolve eq93 eq69 | exact resolve eq69 eq93 | grind only

private theorem step_5_eq135 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP0 : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq93 : ∀ (X0 X1 X2 : G), (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2)) (eq68 : ∀ (X0 X1 X2 : G), ¬(sP0 X0 X1 X2) ∨ a = X0) : ∀ (X0 X1 X2 : G), (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | exact resolve eq93 eq68 | exact resolve eq68 eq93 | grind only

private theorem step_5_eq136 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq135 : ∀ (X0 X1 X2 : G), (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq82 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ a = X0) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := by
  intro X0 X1 X2
  first | exact resolve eq135 eq82 | exact resolve eq82 eq135 | grind only

private theorem step_5_eq138 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq136 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq136 eq80 | exact resolve eq80 eq136 | grind only

private theorem step_5_eq140 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq136 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq136 eq78 | exact resolve eq78 eq136 | grind only

private theorem step_5_eq141 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq136 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq136 eq77 | exact resolve eq77 eq136 | grind only

private theorem step_5_eq142 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq141 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq141 eq87 | exact resolve eq87 eq141 | grind only

private theorem step_5_eq143 {G : Type*} {a : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq140 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ a = X2) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq140 eq88 | exact resolve eq88 eq140 | grind only

private theorem step_5_eq145 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq138 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old b X1 a)) (eq89 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq138 eq89 | exact resolve eq89 eq138 | grind only

private theorem step_5_eq148 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq142 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq73 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq142 eq73 | exact resolve eq73 eq142 | grind only

private theorem step_5_eq149 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq142 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq142 eq72 | exact resolve eq72 eq142 | grind only

private theorem step_5_eq151 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq133 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq133 eq84 | exact resolve eq84 eq133 | grind only

private theorem step_5_eq152 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq133 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2) (eq83 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq133 eq83 | exact resolve eq83 eq133 | grind only

private theorem step_5_eq154 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq152 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq152 eq72 | exact resolve eq72 eq152 | grind only

private theorem step_5_eq155 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq151 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2) (eq73 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq151 eq73 | exact resolve eq73 eq151 | grind only

private theorem step_5_eq163 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq148 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk5 := by
  first | exact resolve eq148 eq97 | exact resolve eq97 eq148 | grind only

private theorem step_5_eq166 {G : Type*} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq134 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1) (eq84 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq134 eq84 | exact resolve eq84 eq134 | grind only

private theorem step_5_eq167 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP3 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq134 : ∀ (X0 X1 X2 : G), (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1) (eq83 : ∀ (X0 X1 X2 : G), ¬(sP3 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq134 eq83 | exact resolve eq83 eq134 | grind only

private theorem step_5_eq169 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq167 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq167 eq72 | exact resolve eq72 eq167 | grind only

private theorem step_5_eq170 {G : Type*} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq166 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2) (eq73 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ b = X2) : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := by
  intro X0 X1 X2
  first | exact resolve eq166 eq73 | exact resolve eq73 eq166 | grind only

private theorem step_5_eq178 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq143 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq143 eq72 | exact resolve eq72 eq143 | grind only

private theorem step_5_eq191 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sP1 : G → G → G → Prop} (eq145 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a)) (eq75 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a) := by
  intro X0 X1 X2
  first | exact resolve eq145 eq75 | exact resolve eq75 eq145 | grind only

private theorem step_5_eq194 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP1 : G → G → G → Prop} (eq145 : ∀ (X0 X1 X2 : G), (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a)) (eq72 : ∀ (X0 X1 X2 : G), ¬(sP1 X0 X1 X2) ∨ c = X1) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1 := by
  intro X0 X1 X2
  first | exact resolve eq145 eq72 | exact resolve eq72 eq145 | grind only

private theorem step_5_eq201 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq154 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq154 eq78 | exact resolve eq78 eq154 | grind only

private theorem step_5_eq202 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq154 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq154 eq77 | exact resolve eq77 eq154 | grind only

private theorem step_5_eq203 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq202 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq202 eq87 | exact resolve eq87 eq202 | grind only

private theorem step_5_eq204 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq201 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq201 eq88 | exact resolve eq88 eq201 | grind only

private theorem step_5_eq214 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq155 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq155 eq77 | exact resolve eq77 eq155 | grind only

private theorem step_5_eq215 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq214 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 ∨ c = X0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ b = X2 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq214 eq87 | exact resolve eq87 eq214 | grind only

private theorem step_5_eq221 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq169 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq80 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq169 eq80 | exact resolve eq80 eq169 | grind only

private theorem step_5_eq222 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq169 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq79 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ (old X1 b b)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | exact resolve eq169 eq79 | exact resolve eq79 eq169 | grind only

private theorem step_5_eq223 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq169 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq78 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq169 eq78 | exact resolve eq78 eq169 | grind only

private theorem step_5_eq224 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq169 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq169 eq77 | exact resolve eq77 eq169 | grind only

private theorem step_5_eq225 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq224 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq224 eq87 | exact resolve eq87 eq224 | grind only

private theorem step_5_eq226 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq223 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq88 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ a = X2) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := by
  intro X0 X1 X2
  first | exact resolve eq223 eq88 | exact resolve eq88 eq223 | grind only

private theorem step_5_eq227 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq222 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b)) (eq90 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old X1 b b)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := by
  intro X0 X1 X2
  first | exact resolve eq222 eq90 | exact resolve eq90 eq222 | grind only

private theorem step_5_eq228 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq221 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a)) (eq89 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ (old b X1 a)) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := by
  intro X0 X1 X2
  first | exact resolve eq221 eq89 | exact resolve eq89 eq221 | grind only

private theorem step_5_eq234 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP2 : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq170 : ∀ (X0 X1 X2 : G), (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2) (eq77 : ∀ (X0 X1 X2 : G), ¬(sP2 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq170 eq77 | exact resolve eq77 eq170 | grind only

private theorem step_5_eq235 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sP4 : G → G → G → Prop} (eq234 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) (eq87 : ∀ (X0 X1 X2 : G), ¬(sP4 X0 X1 X2) ∨ c = X0) : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := by
  intro X0 X1 X2
  first | exact resolve eq234 eq87 | exact resolve eq87 eq234 | grind only

private theorem step_5_eq266 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq149 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1) (eq95 : (new sk1 sk0 sk3)) : (old sk1 sk0 sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq149 eq95 | exact resolve eq95 eq149 | grind only

private theorem step_5_eq267 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq149 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1) (eq96 : (new sk2 sk0 sk4)) : (old sk2 sk0 sk4) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq149 eq96 | exact resolve eq96 eq149 | grind only

private theorem step_5_eq268 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq149 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 := by
  first | exact resolve eq149 eq97 | exact resolve eq97 eq149 | grind only

private theorem step_5_eq296 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq178 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1) (eq95 : (new sk1 sk0 sk3)) : (old sk1 sk0 sk3) ∨ a = sk1 ∨ a = sk3 ∨ c = sk0 := by
  first | exact resolve eq178 eq95 | exact resolve eq95 eq178 | grind only

private theorem step_5_eq297 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq178 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1) (eq96 : (new sk2 sk0 sk4)) : (old sk2 sk0 sk4) ∨ a = sk2 ∨ a = sk4 ∨ c = sk0 := by
  first | exact resolve eq178 eq96 | exact resolve eq96 eq178 | grind only

private theorem step_5_eq304 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq267 : (old sk2 sk0 sk4) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0) (eq60 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) : ∀ (X0 : G), ¬(old sk2 sk0 X0) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 ∨ sk4 = X0 := by
  intro X0
  first | exact resolve eq267 eq60 | exact resolve eq60 eq267 | grind only

private theorem step_5_eq310 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq203 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq94 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq203 eq94 | exact resolve eq94 eq203 | grind only

private theorem step_5_eq311 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq203 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq95 : (new sk1 sk0 sk3)) : (old sk1 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq203 eq95 | exact resolve eq95 eq203 | grind only

private theorem step_5_eq312 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq203 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq96 : (new sk2 sk0 sk4)) : (old sk2 sk0 sk4) ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq203 eq96 | exact resolve eq96 eq203 | grind only

private theorem step_5_eq313 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq203 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ c = sk5 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq203 eq97 | exact resolve eq97 eq203 | grind only

private theorem step_5_eq314 {G : Type*} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq203 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) (eq98 : (new sk5 sk3 sk4)) : (old sk5 sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ c = sk5 := by
  first | exact resolve eq203 eq98 | exact resolve eq98 eq203 | grind only

private theorem step_5_eq329 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq204 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2) (eq98 : (new sk5 sk3 sk4)) : (old sk5 sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 := by
  first | exact resolve eq204 eq98 | exact resolve eq98 eq204 | grind only

private theorem step_5_eq341 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq215 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ b = X2 ∨ c = X0) (eq95 : (new sk1 sk0 sk3)) : (old sk1 sk0 sk3) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 := by
  first | exact resolve eq215 eq95 | exact resolve eq95 eq215 | grind only

private theorem step_5_eq370 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq225 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq94 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := by
  first | exact resolve eq225 eq94 | exact resolve eq94 eq225 | grind only

private theorem step_5_eq371 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq225 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq95 : (new sk1 sk0 sk3)) : (old sk1 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := by
  first | exact resolve eq225 eq95 | exact resolve eq95 eq225 | grind only

private theorem step_5_eq372 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq225 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq96 : (new sk2 sk0 sk4)) : (old sk2 sk0 sk4) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq225 eq96 | exact resolve eq96 eq225 | grind only

private theorem step_5_eq373 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq225 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 := by
  first | exact resolve eq225 eq97 | exact resolve eq97 eq225 | grind only

private theorem step_5_eq374 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq225 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0) (eq98 : (new sk5 sk3 sk4)) : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ c = sk5 := by
  first | exact resolve eq225 eq98 | exact resolve eq98 eq225 | grind only

private theorem step_5_eq385 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq226 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq94 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := by
  first | exact resolve eq226 eq94 | exact resolve eq94 eq226 | grind only

private theorem step_5_eq388 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq226 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
  first | exact resolve eq226 eq97 | exact resolve eq97 eq226 | grind only

private theorem step_5_eq389 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq226 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2) (eq98 : (new sk5 sk3 sk4)) : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ a = sk4 := by
  first | exact resolve eq226 eq98 | exact resolve eq98 eq226 | grind only

private theorem step_5_eq400 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq235 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) (eq94 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := by
  first | exact resolve eq235 eq94 | exact resolve eq94 eq235 | grind only

private theorem step_5_eq403 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq235 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ b = sk1 ∨ b = sk5 ∨ c = sk3 := by
  first | exact resolve eq235 eq97 | exact resolve eq97 eq235 | grind only

private theorem step_5_eq475 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq194 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1) (eq94 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1 := by
  first | exact resolve eq194 eq94 | exact resolve eq94 eq194 | grind only

private theorem step_5_eq476 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq194 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1) (eq95 : (new sk1 sk0 sk3)) : (old sk1 sk0 sk3) ∨ a = sk1 ∨ (old b sk0 a) ∨ c = sk0 := by
  first | exact resolve eq194 eq95 | exact resolve eq95 eq194 | grind only

private theorem step_5_eq554 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq227 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b)) (eq98 : (new sk5 sk3 sk4)) : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ (old sk3 b b) := by
  first | exact resolve eq227 eq98 | exact resolve eq98 eq227 | grind only

private theorem step_5_eq556 {G : Type*} {c : G} {old : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq314 : (old sk5 sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ c = sk5) (eq65 : ∀ (X0 X1 X2 X3 X4 X5 : G), ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 sk3) ∨ c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X2 X1 sk4) ∨ ¬(old sk3 X0 sk5) ∨ ¬(old X1 X0 X2) ∨ (old sk4 X0 X2) := by
  intro X0 X1 X2
  first | exact resolve eq314 eq65 | exact resolve eq65 eq314 | grind only

private theorem step_5_eq565 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq228 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a)) (eq94 : (new sk0 sk1 sk2)) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := by
  first | exact resolve eq228 eq94 | exact resolve eq94 eq228 | grind only

private theorem step_5_eq568 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq228 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a)) (eq97 : (new sk3 sk1 sk5)) : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := by
  first | exact resolve eq228 eq97 | exact resolve eq97 eq228 | grind only

private theorem step_5_eq769 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq370 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq60 : ∀ (X0 X1 X2 X3 : G), ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3) : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 ∨ sk2 = X0 := by
  intro X0
  first | exact resolve eq370 eq60 | exact resolve eq60 eq370 | grind only

private theorem step_5_eq802 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk3 : G} {sk4 : G} {sk5 : G} (eq374 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ c = sk5) (eq65 : ∀ (X0 X1 X2 X3 X4 X5 : G), ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2)) : ∀ (X0 X1 X2 : G), ¬(old X0 X1 sk3) ∨ c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X2 X1 sk4) ∨ ¬(old sk3 X0 sk5) ∨ ¬(old X1 X0 X2) ∨ (old sk4 X0 X2) := by
  intro X0 X1 X2
  first | exact resolve eq374 eq65 | exact resolve eq65 eq374 | grind only

private theorem step_5_eq13684 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq556 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 sk3) ∨ c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X2 X1 sk4) ∨ ¬(old sk3 X0 sk5) ∨ ¬(old X1 X0 X2) ∨ (old sk4 X0 X2)) (eq311 : (old sk1 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1) : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := by
  intro X0
  first | exact resolve eq556 eq311 | exact resolve eq311 eq556 | grind only

private theorem step_5_eq13704 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13684 : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1) : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk0 ∨ c = sk1 := by
  intro X0
  first | exact resolve eq13684 rfl | grind only

private theorem step_5_eq13709 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13704 : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk0 ∨ c = sk1) (eq313 : (old sk3 sk1 sk5) ∨ c = sk5 ∨ c = sk1 ∨ c = sk3) : ∀ (X0 : G), ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk0 ∨ c = sk1 := by
  intro X0
  first | exact resolve eq13704 eq313 | exact resolve eq313 eq13704 | grind only

private theorem step_5_eq13957 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq802 : ∀ (X0 X1 X2 : G), ¬(old X0 X1 sk3) ∨ c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X2 X1 sk4) ∨ ¬(old sk3 X0 sk5) ∨ ¬(old X1 X0 X2) ∨ (old sk4 X0 X2)) (eq341 : (old sk1 sk0 sk3) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1) : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 := by
  intro X0
  first | exact resolve eq802 eq341 | exact resolve eq341 eq802 | grind only

private theorem step_5_eq13977 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13957 : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1) : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1 := by
  intro X0
  first | exact resolve eq13957 rfl | grind only

private theorem step_5_eq13985 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13977 : ∀ (X0 : G), c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1) (eq313 : (old sk3 sk1 sk5) ∨ c = sk5 ∨ c = sk1 ∨ c = sk3) : ∀ (X0 : G), ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1 := by
  intro X0
  first | exact resolve eq13977 eq313 | exact resolve eq313 eq13977 | grind only

private theorem step_5_eq17643 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13985 : ∀ (X0 : G), ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1) (eq312 : (old sk2 sk0 sk4) ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq13985 eq312 | exact resolve eq312 eq13985 | grind only

private theorem step_5_eq17647 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13985 : ∀ (X0 : G), ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1) (eq372 : (old sk2 sk0 sk4) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq13985 eq372 | exact resolve eq372 eq13985 | grind only

private theorem step_5_eq17684 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq17647 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq310 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq17647 eq310 | exact resolve eq310 eq17647 | grind only

private theorem step_5_eq17688 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq17643 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) (eq310 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq17643 eq310 | exact resolve eq310 eq17643 | grind only

private theorem step_5_eq17694 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq17684 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq119 : ¬(old sk4 sk1 sk2)) : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq17684 eq119 | exact resolve eq119 eq17684 | grind only

private theorem step_5_eq17695 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq17688 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) (eq119 : ¬(old sk4 sk1 sk2)) : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq17688 eq119 | exact resolve eq119 eq17688 | grind only

private theorem step_5_eq17710 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq373 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3) (eq17694 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq373 eq17694 | exact superpose eq17694 eq373 | grind only

private theorem step_5_eq18028 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq17710 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq17710 rfl | grind only

private theorem step_5_eq18195 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq18028 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq18028 eq54 | exact resolve eq54 eq18028 | grind only

private theorem step_5_eq18304 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq268 : (old sk3 sk1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1) (eq17695 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq268 eq17695 | exact superpose eq17695 eq268 | grind only

private theorem step_5_eq18312 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq373 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3) (eq17695 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq373 eq17695 | exact superpose eq17695 eq373 | grind only

private theorem step_5_eq18652 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq18312 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq18312 rfl | grind only

private theorem step_5_eq18658 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq18304 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq18304 rfl | grind only

private theorem step_5_eq18820 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq18652 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq18652 eq54 | exact resolve eq54 eq18652 | grind only

private theorem step_5_eq18827 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq18658 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq18658 eq54 | exact resolve eq54 eq18658 | grind only

private theorem step_5_eq20471 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq371 : (old sk1 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1) (eq18195 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq371 eq18195 | exact superpose eq18195 eq371 | grind only

private theorem step_5_eq20928 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq20471 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk2 := by
  first | exact resolve eq20471 rfl | grind only

private theorem step_5_eq21140 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq20928 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk3 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 := by
  first | exact resolve eq20928 eq54 | exact resolve eq54 eq20928 | grind only

private theorem step_5_eq23452 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq389 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ a = sk4) (eq18820 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq389 eq18820 | exact superpose eq18820 eq389 | grind only

private theorem step_5_eq23644 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq23452 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq23452 rfl | grind only

private theorem step_5_eq23744 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq23644 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq23644 eq54 | exact resolve eq54 eq23644 | grind only

private theorem step_5_eq23783 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq23744 : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq51 : a ≠ c) : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq23744 eq51 | exact resolve eq51 eq23744 | grind only

private theorem step_5_eq23797 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq98 : (new sk5 sk3 sk4)) (eq23783 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (new sk5 c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq98 eq23783 | exact superpose eq23783 eq98 | grind only

private theorem step_5_eq23818 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq388 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5) (eq23783 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq388 eq23783 | exact superpose eq23783 eq388 | grind only

private theorem step_5_eq24262 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq23818 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq23818 rfl | grind only

private theorem step_5_eq24461 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq24262 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = sk5 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq24262 eq59 | exact resolve eq59 eq24262 | grind only

private theorem step_5_eq26061 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq23797 : (new sk5 c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq24461 : a = sk5 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) : (new a c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq23797 eq24461 | exact superpose eq24461 eq23797 | grind only

private theorem step_5_eq26076 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq26061 : (new a c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) : (new a c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq26061 rfl | grind only

private theorem step_5_eq26770 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq26076 : (new a c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) (eq235 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ (old a c sk4) ∨ b = c ∨ b = sk4 ∨ a = c := by
  first | exact resolve eq26076 eq235 | exact resolve eq235 eq26076 | grind only

private theorem step_5_eq26815 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq26770 : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ (old a c sk4) ∨ b = c ∨ b = sk4 ∨ a = c) (eq57 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = c ∨ b = sk4 ∨ a = c := by
  first | exact resolve eq26770 eq57 | exact resolve eq57 eq26770 | grind only

private theorem step_5_eq26832 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq26815 : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = c ∨ b = sk4 ∨ a = c) (eq52 : b ≠ c) : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk4 ∨ a = c := by
  first | exact resolve eq26815 eq52 | exact resolve eq52 eq26815 | grind only

private theorem step_5_eq26838 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq26832 : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk4 ∨ a = c) (eq51 : a ≠ c) : b = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 := by
  first | exact resolve eq26832 eq51 | exact resolve eq51 eq26832 | grind only

private theorem step_5_eq26845 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq99 : ¬(new sk4 sk1 sk2)) (eq26838 : b = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3) : ¬(new b sk1 sk2) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 := by
  first | exact superpose eq99 eq26838 | exact superpose eq26838 eq99 | grind only

private theorem step_5_eq27549 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq389 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ a = sk4) (eq18827 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2) : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq389 eq18827 | exact superpose eq18827 eq389 | grind only

private theorem step_5_eq27751 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq27549 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2) : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq27549 rfl | grind only

private theorem step_5_eq27852 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq27751 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq27751 eq54 | exact resolve eq54 eq27751 | grind only

private theorem step_5_eq27891 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq27852 : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2) (eq51 : a ≠ c) : a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq27852 eq51 | exact resolve eq51 eq27852 | grind only

private theorem step_5_eq27966 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq554 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ (old sk3 b b)) (eq27891 : a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) : (old sk5 a sk4) ∨ a = b ∨ a = c ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq554 eq27891 | exact superpose eq27891 eq554 | grind only

private theorem step_5_eq28510 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq27966 : (old sk5 a sk4) ∨ a = b ∨ a = c ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) (eq49 : a ≠ b) : (old sk5 a sk4) ∨ a = c ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq27966 eq49 | exact resolve eq49 eq27966 | grind only

private theorem step_5_eq28580 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq28510 : (old sk5 a sk4) ∨ a = c ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) (eq51 : a ≠ c) : (old sk5 a sk4) ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq28510 eq51 | exact resolve eq51 eq28510 | grind only

private theorem step_5_eq28591 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq28580 : (old sk5 a sk4) ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) (eq53 : ∀ (X0 : G), ¬(old a b X0)) : (old sk5 a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq28580 eq53 | exact resolve eq53 eq28580 | grind only

private theorem step_5_eq29508 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq28591 : (old sk5 a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2) (eq17695 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : (old c a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq28591 eq17695 | exact superpose eq17695 eq28591 | grind only

private theorem step_5_eq29521 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq29508 : (old c a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : (old c a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk4 := by
  first | exact resolve eq29508 rfl | grind only

private theorem step_5_eq29525 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq29521 : (old c a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk4) (eq58 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk4 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 := by
  first | exact resolve eq29521 eq58 | exact resolve eq58 eq29521 | grind only

private theorem step_5_eq30069 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq389 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ a = sk4) (eq29525 : c = sk4 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3) : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 := by
  first | exact superpose eq389 eq29525 | exact superpose eq29525 eq389 | grind only

private theorem step_5_eq30275 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq30069 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3) : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq30069 rfl | grind only

private theorem step_5_eq30393 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq30275 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq30275 eq54 | exact resolve eq54 eq30275 | grind only

private theorem step_5_eq30442 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq30393 : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) (eq51 : a ≠ c) : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq30393 eq51 | exact resolve eq51 eq30393 | grind only

private theorem step_5_eq30468 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq266 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0) (eq30442 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk1 sk0 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq266 eq30442 | exact superpose eq30442 eq266 | grind only

private theorem step_5_eq30919 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq30468 : (old sk1 sk0 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk1 sk0 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk3 ∨ c = sk2 := by
  first | exact resolve eq30468 rfl | grind only

private theorem step_5_eq31125 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq30919 : (old sk1 sk0 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk3 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := by
  first | exact resolve eq30919 eq54 | exact resolve eq54 eq30919 | grind only

private theorem step_5_eq32154 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq98 : (new sk5 sk3 sk4)) (eq31125 : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2) : (new sk5 b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := by
  first | exact superpose eq98 eq31125 | exact superpose eq31125 eq98 | grind only

private theorem step_5_eq50018 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq13709 : ∀ (X0 : G), ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk0 ∨ c = sk1) (eq312 : (old sk2 sk0 sk4) ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq13709 eq312 | exact resolve eq312 eq13709 | grind only

private theorem step_5_eq50074 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq50018 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq50018 rfl | grind only

private theorem step_5_eq50103 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq50074 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq310 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0) : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq50074 eq310 | exact resolve eq310 eq50074 | grind only

private theorem step_5_eq50114 {G : Type*} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq50103 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq119 : ¬(old sk4 sk1 sk2)) : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq50103 eq119 | exact resolve eq119 eq50103 | grind only

private theorem step_5_eq50131 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq329 : (old sk5 sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4) (eq50114 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) : (old c sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact superpose eq329 eq50114 | exact superpose eq50114 eq329 | grind only

private theorem step_5_eq50133 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} {sk5 : G} (eq373 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3) (eq50114 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact superpose eq373 eq50114 | exact superpose eq50114 eq373 | grind only

private theorem step_5_eq50595 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq50133 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq50133 rfl | grind only

private theorem step_5_eq50597 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq50131 : (old c sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) : (old c sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq50131 rfl | grind only

private theorem step_5_eq50793 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq50595 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq50595 eq54 | exact resolve eq54 eq50595 | grind only

private theorem step_5_eq50795 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq50597 : (old c sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq58 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : a = sk4 ∨ c = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq50597 eq58 | exact resolve eq58 eq50597 | grind only

private theorem step_5_eq50921 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq267 : (old sk2 sk0 sk4) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0) (eq50793 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk2 sk0 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq267 eq50793 | exact superpose eq50793 eq267 | grind only

private theorem step_5_eq50929 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq372 : (old sk2 sk0 sk4) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2) (eq50793 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq372 eq50793 | exact superpose eq50793 eq372 | grind only

private theorem step_5_eq51181 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq50929 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 := by
  first | exact resolve eq50929 rfl | grind only

private theorem step_5_eq51187 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq50921 : (old sk2 sk0 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2) : (old sk2 sk0 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 := by
  first | exact resolve eq50921 rfl | grind only

private theorem step_5_eq51299 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq51181 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 := by
  first | exact resolve eq51181 eq54 | exact resolve eq54 eq51181 | grind only

private theorem step_5_eq51305 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq51187 : (old sk2 sk0 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := by
  first | exact resolve eq51187 eq54 | exact resolve eq54 eq51187 | grind only

private theorem step_5_eq52619 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq21140 : b = sk3 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2) (eq51299 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1) : b = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 := by
  first | exact superpose eq21140 eq51299 | exact superpose eq51299 eq21140 | grind only

private theorem step_5_eq52680 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq52619 : b = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1) : b = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 := by
  first | exact resolve eq52619 rfl | grind only

private theorem step_5_eq52874 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq52680 : b = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2) (eq52 : b ≠ c) : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
  first | exact resolve eq52680 eq52 | exact resolve eq52 eq52680 | grind only

private theorem step_5_eq53289 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq370 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq52874 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0) : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
  first | exact superpose eq370 eq52874 | exact superpose eq52874 eq370 | grind only

private theorem step_5_eq53715 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq53289 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0) : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := by
  first | exact resolve eq53289 rfl | grind only

private theorem step_5_eq53923 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq53715 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq53715 eq54 | exact resolve eq54 eq53715 | grind only

private theorem step_5_eq54046 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq96 : (new sk2 sk0 sk4)) (eq53923 : c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (new sk2 c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact superpose eq96 eq53923 | exact superpose eq53923 eq96 | grind only

private theorem step_5_eq54075 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq385 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2) (eq53923 : c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact superpose eq385 eq53923 | exact superpose eq53923 eq385 | grind only

private theorem step_5_eq54102 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq565 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a)) (eq53923 : c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact superpose eq565 eq53923 | exact superpose eq53923 eq565 | grind only

private theorem step_5_eq54794 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq54102 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ b = sk0 := by
  first | exact resolve eq54102 rfl | grind only

private theorem step_5_eq54806 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq54075 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ b = sk0 := by
  first | exact resolve eq54075 rfl | grind only

private theorem step_5_eq55105 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq54794 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ b = sk0) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq54794 eq59 | exact resolve eq59 eq54794 | grind only

private theorem step_5_eq55127 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq54806 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ b = sk0) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq54806 eq59 | exact resolve eq59 eq54806 | grind only

private theorem step_5_eq55325 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq119 : ¬(old sk4 sk1 sk2)) (eq55127 : a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : ¬(old sk4 sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact superpose eq119 eq55127 | exact superpose eq55127 eq119 | grind only

private theorem step_5_eq57315 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq54046 : (new sk2 c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) (eq55127 : a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (new a c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact superpose eq54046 eq55127 | exact superpose eq55127 eq54046 | grind only

private theorem step_5_eq57344 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq57315 : (new a c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : (new a c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq57315 rfl | grind only

private theorem step_5_eq58336 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq57344 : (new a c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) (eq235 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0) : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ (old a c sk4) ∨ b = c ∨ b = sk4 ∨ a = c := by
  first | exact resolve eq57344 eq235 | exact resolve eq235 eq57344 | grind only

private theorem step_5_eq58401 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq58336 : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ (old a c sk4) ∨ b = c ∨ b = sk4 ∨ a = c) (eq57 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = c ∨ b = sk4 ∨ a = c := by
  first | exact resolve eq58336 eq57 | exact resolve eq57 eq58336 | grind only

private theorem step_5_eq58418 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk4 : G} (eq58401 : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = c ∨ b = sk4 ∨ a = c) (eq52 : b ≠ c) : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = sk4 ∨ a = c := by
  first | exact resolve eq58401 eq52 | exact resolve eq52 eq58401 | grind only

private theorem step_5_eq58424 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk4 : G} (eq58418 : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = sk4 ∨ a = c) (eq51 : a ≠ c) : b = sk4 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 := by
  first | exact resolve eq58418 eq51 | exact resolve eq51 eq58418 | grind only

private theorem step_5_eq58673 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq55325 : ¬(old sk4 sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) (eq58424 : b = sk4 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1) : ¬(old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 := by
  first | exact superpose eq55325 eq58424 | exact superpose eq58424 eq55325 | grind only

private theorem step_5_eq58678 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq58673 : ¬(old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1) : ¬(old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := by
  first | exact resolve eq58673 rfl | grind only

private theorem step_5_eq58754 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq58678 : ¬(old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) (eq55105 : (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0) : b = sk0 ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq58678 eq55105 | exact resolve eq55105 eq58678 | grind only

private theorem step_5_eq58836 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq94 : (new sk0 sk1 sk2)) (eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1) : (new b sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq94 eq58754 | exact superpose eq58754 eq94 | grind only

private theorem step_5_eq58873 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq312 : (old sk2 sk0 sk4) ∨ c = sk4 ∨ c = sk0 ∨ c = sk2) (eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1) : (old sk2 b sk4) ∨ c = sk4 ∨ b = c ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq312 eq58754 | exact superpose eq58754 eq312 | grind only

private theorem step_5_eq58890 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq370 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0) (eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1) : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq370 eq58754 | exact superpose eq58754 eq370 | grind only

private theorem step_5_eq59002 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq769 : ∀ (X0 : G), ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 ∨ sk2 = X0) (eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1) : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ sk2 = X0 ∨ b = sk1 ∨ c = sk1 := by
  intro X0
  first | exact superpose eq769 eq58754 | exact superpose eq58754 eq769 | grind only

private theorem step_5_eq59757 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq59002 : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ sk2 = X0 ∨ b = sk1 ∨ c = sk1) : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ sk2 = X0 := by
  intro X0
  first | exact resolve eq59002 rfl | grind only

private theorem step_5_eq59792 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq58890 : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ c = sk1) : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = c := by
  first | exact resolve eq58890 rfl | grind only

private theorem step_5_eq60036 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq59757 : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ sk2 = X0) (eq52 : b ≠ c) : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0 := by
  intro X0
  first | exact resolve eq59757 eq52 | exact resolve eq52 eq59757 | grind only

private theorem step_5_eq60087 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq59792 : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = c) (eq52 : b ≠ c) : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq59792 eq52 | exact resolve eq52 eq59792 | grind only

private theorem step_5_eq60095 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq58873 : (old sk2 b sk4) ∨ c = sk4 ∨ b = c ∨ c = sk2 ∨ b = sk1 ∨ c = sk1) (eq52 : b ≠ c) : (old sk2 b sk4) ∨ c = sk4 ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq58873 eq52 | exact resolve eq52 eq58873 | grind only

private theorem step_5_eq60188 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq58836 : (new b sk1 sk2) ∨ b = sk1 ∨ c = sk1) (eq26845 : ¬(new b sk1 sk2) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3) : b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 := by
  first | exact resolve eq58836 eq26845 | exact resolve eq26845 eq58836 | grind only

private theorem step_5_eq60265 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq60188 : b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3) : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk1 := by
  first | exact resolve eq60188 rfl | grind only

private theorem step_5_eq60866 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq95 : (new sk1 sk0 sk3)) (eq60265 : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk1) : (new sk1 sk0 b) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk1 := by
  first | exact superpose eq95 eq60265 | exact superpose eq60265 eq95 | grind only

private theorem step_5_eq64181 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq60866 : (new sk1 sk0 b) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk1) (eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1) : (new sk1 b b) ∨ c = sk1 ∨ b = c ∨ c = sk2 ∨ b = sk1 ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq60866 eq58754 | exact superpose eq58754 eq60866 | grind only

private theorem step_5_eq64182 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq64181 : (new sk1 b b) ∨ c = sk1 ∨ b = c ∨ c = sk2 ∨ b = sk1 ∨ b = sk1 ∨ c = sk1) : (new sk1 b b) ∨ c = sk1 ∨ b = c ∨ c = sk2 ∨ b = sk1 := by
  first | exact resolve eq64181 rfl | grind only

private theorem step_5_eq64204 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq64182 : (new sk1 b b) ∨ c = sk1 ∨ b = c ∨ c = sk2 ∨ b = sk1) (eq52 : b ≠ c) : (new sk1 b b) ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 := by
  first | exact resolve eq64182 eq52 | exact resolve eq52 eq64182 | grind only

private theorem step_5_eq64236 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq64204 : (new sk1 b b) ∨ c = sk1 ∨ c = sk2 ∨ b = sk1) (eq203 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0) : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old sk1 b b) ∨ b = c ∨ b = c ∨ c = sk1 := by
  first | exact resolve eq64204 eq203 | exact resolve eq203 eq64204 | grind only

private theorem step_5_eq64281 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq64236 : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old sk1 b b) ∨ b = c ∨ b = c ∨ c = sk1) : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old sk1 b b) ∨ b = c := by
  first | exact resolve eq64236 rfl | grind only

private theorem step_5_eq64294 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq64281 : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old sk1 b b) ∨ b = c) (eq52 : b ≠ c) : (old sk1 b b) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq64281 eq52 | exact resolve eq52 eq64281 | grind only

private theorem step_5_eq77860 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq568 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a)) (eq51305 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1) : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := by
  first | exact superpose eq568 eq51305 | exact superpose eq51305 eq568 | grind only

private theorem step_5_eq78542 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk5 : G} (eq77860 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1) : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := by
  first | exact resolve eq77860 rfl | grind only

private theorem step_5_eq78834 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk5 : G} (eq78542 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2) (eq60036 : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0) : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := by
  first | exact resolve eq78542 eq60036 | exact resolve eq60036 eq78542 | grind only

private theorem step_5_eq78955 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk5 : G} (eq78834 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk2) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq78834 eq59 | exact resolve eq59 eq78834 | grind only

private theorem step_5_eq78997 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq94 : (new sk0 sk1 sk2)) (eq78955 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk1) : (new sk0 sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq94 eq78955 | exact superpose eq78955 eq94 | grind only

private theorem step_5_eq80452 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq78997 : (new sk0 sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk1) (eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1) : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = c ∨ b = sk1 ∨ b = sk1 ∨ c = sk1 := by
  first | exact superpose eq78997 eq58754 | exact superpose eq58754 eq78997 | grind only

private theorem step_5_eq80453 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq80452 : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = c ∨ b = sk1 ∨ b = sk1 ∨ c = sk1) : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = c ∨ b = sk1 := by
  first | exact resolve eq80452 rfl | grind only

private theorem step_5_eq80484 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq80453 : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = c ∨ b = sk1) (eq52 : b ≠ c) : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 := by
  first | exact resolve eq80453 eq52 | exact resolve eq52 eq80453 | grind only

private theorem step_5_eq80526 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq80484 : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = sk1) (eq228 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a)) : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old b sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := by
  first | exact resolve eq80484 eq228 | exact resolve eq228 eq80484 | grind only

private theorem step_5_eq80561 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq80526 : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old b sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a)) : (old b sk1 a) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq80526 rfl | grind only

private theorem step_5_eq80616 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq80561 : (old b sk1 a) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1) (eq60036 : ∀ (X0 : G), ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0) : c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ a = sk2 := by
  first | exact resolve eq80561 eq60036 | exact resolve eq60036 eq80561 | grind only

private theorem step_5_eq80626 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} (eq80616 : c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ a = sk2) : a = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq80616 rfl | grind only

private theorem step_5_eq80634 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq99 : ¬(new sk4 sk1 sk2)) (eq80626 : a = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) : ¬(new sk4 sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact superpose eq99 eq80626 | exact superpose eq80626 eq99 | grind only

private theorem step_5_eq80932 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq60095 : (old sk2 b sk4) ∨ c = sk4 ∨ c = sk2 ∨ b = sk1 ∨ c = sk1) (eq80626 : a = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) : (old a b sk4) ∨ c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact superpose eq60095 eq80626 | exact superpose eq80626 eq60095 | grind only

private theorem step_5_eq80956 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq80932 : (old a b sk4) ∨ c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) : (old a b sk4) ∨ c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq80932 rfl | grind only

private theorem step_5_eq81032 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq80956 : (old a b sk4) ∨ c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) (eq53 : ∀ (X0 : G), ¬(old a b X0)) : c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq80956 eq53 | exact resolve eq53 eq80956 | grind only

private theorem step_5_eq81084 {G : Type*} {a : G} {b : G} {c : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq81032 : c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) (eq51 : a ≠ c) : c = sk4 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq81032 eq51 | exact resolve eq51 eq81032 | grind only

private theorem step_5_eq82623 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq80634 : ¬(new sk4 sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) (eq81084 : c = sk4 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) : ¬(new c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact superpose eq80634 eq81084 | exact superpose eq81084 eq80634 | grind only

private theorem step_5_eq82624 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq82623 : ¬(new c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) : ¬(new c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq82623 rfl | grind only

private theorem step_5_eq83278 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq82624 : ¬(new c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2) (eq106 : ∀ (X1 : G), (new c X1 a) ∨ ¬(old b X1 a) ∨ ¬(old X1 b b)) : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old b sk1 a) ∨ ¬(old sk1 b b) := by
  first | exact resolve eq82624 eq106 | exact resolve eq106 eq82624 | grind only

private theorem step_5_eq83284 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq83278 : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old b sk1 a) ∨ ¬(old sk1 b b)) (eq80561 : (old b sk1 a) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1) : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old sk1 b b) := by
  first | exact resolve eq83278 eq80561 | exact resolve eq80561 eq83278 | grind only

private theorem step_5_eq83285 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq83284 : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old sk1 b b)) (eq64294 : (old sk1 b b) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1) : c = sk2 ∨ c = sk1 ∨ b = sk1 := by
  first | exact resolve eq83284 eq64294 | exact resolve eq64294 eq83284 | grind only

private theorem step_5_eq83616 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq60087 : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1) (eq83285 : c = sk2 ∨ c = sk1 ∨ b = sk1) : (old b sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := by
  first | exact superpose eq60087 eq83285 | exact superpose eq83285 eq60087 | grind only

private theorem step_5_eq83621 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq83616 : (old b sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1) : (old b sk1 c) ∨ b = sk1 ∨ c = sk1 := by
  first | exact resolve eq83616 rfl | grind only

private theorem step_5_eq83686 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq83621 : (old b sk1 c) ∨ b = sk1 ∨ c = sk1) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk1 ∨ b = sk1 := by
  first | exact resolve eq83621 eq54 | exact resolve eq54 eq83621 | grind only

private theorem step_5_eq83928 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq94 : (new sk0 sk1 sk2)) (eq83686 : c = sk1 ∨ b = sk1) : (new sk0 c sk2) ∨ b = sk1 := by
  first | exact superpose eq94 eq83686 | exact superpose eq83686 eq94 | grind only

private theorem step_5_eq83930 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq97 : (new sk3 sk1 sk5)) (eq83686 : c = sk1 ∨ b = sk1) : (new sk3 c sk5) ∨ b = sk1 := by
  first | exact superpose eq97 eq83686 | exact superpose eq83686 eq97 | grind only

private theorem step_5_eq83931 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq99 : ¬(new sk4 sk1 sk2)) (eq83686 : c = sk1 ∨ b = sk1) : ¬(new sk4 c sk2) ∨ b = sk1 := by
  first | exact superpose eq99 eq83686 | exact superpose eq83686 eq99 | grind only

private theorem step_5_eq83932 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq119 : ¬(old sk4 sk1 sk2)) (eq83686 : c = sk1 ∨ b = sk1) : ¬(old sk4 c sk2) ∨ b = sk1 := by
  first | exact superpose eq119 eq83686 | exact superpose eq83686 eq119 | grind only

private theorem step_5_eq83944 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq296 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ a = sk3 ∨ c = sk0) (eq83686 : c = sk1 ∨ b = sk1) : (old c sk0 sk3) ∨ a = c ∨ a = sk3 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq296 eq83686 | exact superpose eq83686 eq296 | grind only

private theorem step_5_eq83962 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq400 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0) (eq83686 : c = sk1 ∨ b = sk1) : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq400 eq83686 | exact superpose eq83686 eq400 | grind only

private theorem step_5_eq83963 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq403 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ b = sk5 ∨ c = sk3) (eq83686 : c = sk1 ∨ b = sk1) : (old sk3 c sk5) ∨ b = c ∨ b = sk5 ∨ c = sk3 ∨ b = sk1 := by
  first | exact superpose eq403 eq83686 | exact superpose eq83686 eq403 | grind only

private theorem step_5_eq83976 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq476 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ (old b sk0 a) ∨ c = sk0) (eq83686 : c = sk1 ∨ b = sk1) : (old c sk0 sk3) ∨ a = c ∨ (old b sk0 a) ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq476 eq83686 | exact superpose eq83686 eq476 | grind only

private theorem step_5_eq84961 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq83976 : (old c sk0 sk3) ∨ a = c ∨ (old b sk0 a) ∨ c = sk0 ∨ b = sk1) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ (old b sk0 a) ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq83976 eq59 | exact resolve eq59 eq83976 | grind only

private theorem step_5_eq84966 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq83963 : (old sk3 c sk5) ∨ b = c ∨ b = sk5 ∨ c = sk3 ∨ b = sk1) (eq57 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = c ∨ b = sk5 ∨ c = sk3 ∨ b = sk1 := by
  first | exact resolve eq83963 eq57 | exact resolve eq57 eq83963 | grind only

private theorem step_5_eq84967 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq83962 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1) (eq57 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X0) : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq83962 eq57 | exact resolve eq57 eq83962 | grind only

private theorem step_5_eq84979 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq83944 : (old c sk0 sk3) ∨ a = c ∨ a = sk3 ∨ c = sk0 ∨ b = sk1) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ a = sk3 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq83944 eq59 | exact resolve eq59 eq83944 | grind only

private theorem step_5_eq85080 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq84961 : a = c ∨ (old b sk0 a) ∨ c = sk0 ∨ b = sk1) (eq51 : a ≠ c) : (old b sk0 a) ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq84961 eq51 | exact resolve eq51 eq84961 | grind only

private theorem step_5_eq85081 {G : Type*} {b : G} {c : G} {sk1 : G} {sk3 : G} {sk5 : G} (eq84966 : b = c ∨ b = sk5 ∨ c = sk3 ∨ b = sk1) (eq52 : b ≠ c) : b = sk5 ∨ c = sk3 ∨ b = sk1 := by
  first | exact resolve eq84966 eq52 | exact resolve eq52 eq84966 | grind only

private theorem step_5_eq85082 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} (eq84967 : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1) (eq52 : b ≠ c) : b = sk2 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq84967 eq52 | exact resolve eq52 eq84967 | grind only

private theorem step_5_eq85083 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk3 : G} (eq84979 : a = c ∨ a = sk3 ∨ c = sk0 ∨ b = sk1) (eq51 : a ≠ c) : a = sk3 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq84979 eq51 | exact resolve eq51 eq84979 | grind only

private theorem step_5_eq86295 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} {sk5 : G} (eq83930 : (new sk3 c sk5) ∨ b = sk1) (eq85081 : b = sk5 ∨ c = sk3 ∨ b = sk1) : (new sk3 c b) ∨ b = sk1 ∨ c = sk3 ∨ b = sk1 := by
  first | exact superpose eq83930 eq85081 | exact superpose eq85081 eq83930 | grind only

private theorem step_5_eq86296 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk3 : G} (eq86295 : (new sk3 c b) ∨ b = sk1 ∨ c = sk3 ∨ b = sk1) : (new sk3 c b) ∨ b = sk1 ∨ c = sk3 := by
  first | exact resolve eq86295 rfl | grind only

private theorem step_5_eq86747 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq304 : ∀ (X0 : G), ¬(old sk2 sk0 X0) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 ∨ sk4 = X0) (eq85082 : b = sk2 ∨ c = sk0 ∨ b = sk1) : ∀ (X0 : G), ¬(old b sk0 X0) ∨ b = c ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ c = sk0 ∨ b = sk1 := by
  intro X0
  first | exact superpose eq304 eq85082 | exact superpose eq85082 eq304 | grind only

private theorem step_5_eq87205 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq83931 : ¬(new sk4 c sk2) ∨ b = sk1) (eq85082 : b = sk2 ∨ c = sk0 ∨ b = sk1) : ¬(new sk4 c b) ∨ b = sk1 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq83931 eq85082 | exact superpose eq85082 eq83931 | grind only

private theorem step_5_eq87208 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq87205 : ¬(new sk4 c b) ∨ b = sk1 ∨ c = sk0 ∨ b = sk1) : ¬(new sk4 c b) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq87205 rfl | grind only

private theorem step_5_eq87374 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq86747 : ∀ (X0 : G), ¬(old b sk0 X0) ∨ b = c ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ c = sk0 ∨ b = sk1) : ∀ (X0 : G), ¬(old b sk0 X0) ∨ b = c ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ b = sk1 := by
  intro X0
  first | exact resolve eq86747 rfl | grind only

private theorem step_5_eq87585 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq87374 : ∀ (X0 : G), ¬(old b sk0 X0) ∨ b = c ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ b = sk1) (eq52 : b ≠ c) : ∀ (X0 : G), ¬(old b sk0 X0) ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ b = sk1 := by
  intro X0
  first | exact resolve eq87374 eq52 | exact resolve eq52 eq87374 | grind only

private theorem step_5_eq87638 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq87585 : ∀ (X0 : G), ¬(old b sk0 X0) ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ b = sk1) (eq49 : a ≠ b) : ∀ (X0 : G), ¬(old b sk0 X0) ∨ c = sk0 ∨ sk4 = X0 ∨ b = sk1 := by
  intro X0
  first | exact resolve eq87585 eq49 | exact resolve eq49 eq87585 | grind only

private theorem step_5_eq92988 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq86296 : (new sk3 c b) ∨ b = sk1 ∨ c = sk3) (eq85083 : a = sk3 ∨ c = sk0 ∨ b = sk1) : (new a c b) ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq86296 eq85083 | exact superpose eq85083 eq86296 | grind only

private theorem step_5_eq92991 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq92988 : (new a c b) ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ b = sk1) : (new a c b) ∨ b = sk1 ∨ a = c ∨ c = sk0 := by
  first | exact resolve eq92988 rfl | grind only

private theorem step_5_eq93012 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq92991 : (new a c b) ∨ b = sk1 ∨ a = c ∨ c = sk0) (eq51 : a ≠ c) : (new a c b) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq92991 eq51 | exact resolve eq51 eq92991 | grind only

private theorem step_5_eq102284 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq87638 : ∀ (X0 : G), ¬(old b sk0 X0) ∨ c = sk0 ∨ sk4 = X0 ∨ b = sk1) (eq85080 : (old b sk0 a) ∨ c = sk0 ∨ b = sk1) : c = sk0 ∨ a = sk4 ∨ b = sk1 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq87638 eq85080 | exact resolve eq85080 eq87638 | grind only

private theorem step_5_eq102289 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk4 : G} (eq102284 : c = sk0 ∨ a = sk4 ∨ b = sk1 ∨ c = sk0 ∨ b = sk1) : a = sk4 ∨ c = sk0 ∨ b = sk1 := by
  first | exact resolve eq102284 rfl | grind only

private theorem step_5_eq102586 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk4 : G} (eq87208 : ¬(new sk4 c b) ∨ b = sk1 ∨ c = sk0) (eq102289 : a = sk4 ∨ c = sk0 ∨ b = sk1) : ¬(new a c b) ∨ b = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk1 := by
  first | exact superpose eq87208 eq102289 | exact superpose eq102289 eq87208 | grind only

private theorem step_5_eq102619 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq102586 : ¬(new a c b) ∨ b = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk1) : ¬(new a c b) ∨ b = sk1 ∨ c = sk0 := by
  first | exact resolve eq102586 rfl | grind only

private theorem step_5_eq102723 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} (eq102619 : ¬(new a c b) ∨ b = sk1 ∨ c = sk0) (eq93012 : (new a c b) ∨ b = sk1 ∨ c = sk0) : c = sk0 ∨ b = sk1 := by
  first | exact resolve eq102619 eq93012 | exact resolve eq93012 eq102619 | grind only

private theorem step_5_eq102768 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq96 : (new sk2 sk0 sk4)) (eq102723 : c = sk0 ∨ b = sk1) : (new sk2 c sk4) ∨ b = sk1 := by
  first | exact superpose eq96 eq102723 | exact superpose eq102723 eq96 | grind only

private theorem step_5_eq103486 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq83928 : (new sk0 c sk2) ∨ b = sk1) (eq102723 : c = sk0 ∨ b = sk1) : (new c c sk2) ∨ b = sk1 ∨ b = sk1 := by
  first | exact superpose eq83928 eq102723 | exact superpose eq102723 eq83928 | grind only

private theorem step_5_eq103517 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq103486 : (new c c sk2) ∨ b = sk1 ∨ b = sk1) : (new c c sk2) ∨ b = sk1 := by
  first | exact resolve eq103486 rfl | grind only

private theorem step_5_eq104500 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq103517 : (new c c sk2) ∨ b = sk1) (eq191 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a)) : b = sk1 ∨ (old c c sk2) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk2) c a) := by
  first | exact resolve eq103517 eq191 | exact resolve eq191 eq103517 | grind only

private theorem step_5_eq104570 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq104500 : b = sk1 ∨ (old c c sk2) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk2) c a)) (eq56 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk1 ∨ (old c c sk2) ∨ a = c ∨ (old (sF0 c c sk2) c a) := by
  first | exact resolve eq104500 eq56 | exact resolve eq56 eq104500 | grind only

private theorem step_5_eq104586 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk2 : G} (eq104570 : b = sk1 ∨ (old c c sk2) ∨ a = c ∨ (old (sF0 c c sk2) c a)) (eq56 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk1 ∨ (old c c sk2) ∨ a = c := by
  first | exact resolve eq104570 eq56 | exact resolve eq56 eq104570 | grind only

private theorem step_5_eq104591 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq104586 : b = sk1 ∨ (old c c sk2) ∨ a = c) (eq51 : a ≠ c) : (old c c sk2) ∨ b = sk1 := by
  first | exact resolve eq104586 eq51 | exact resolve eq51 eq104586 | grind only

private theorem step_5_eq105780 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq104591 : (old c c sk2) ∨ b = sk1) (eq58 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X1) : c = sk2 ∨ b = sk1 := by
  first | exact resolve eq104591 eq58 | exact resolve eq58 eq104591 | grind only

private theorem step_5_eq106198 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq83932 : ¬(old sk4 c sk2) ∨ b = sk1) (eq105780 : c = sk2 ∨ b = sk1) : ¬(old sk4 c c) ∨ b = sk1 ∨ b = sk1 := by
  first | exact superpose eq83932 eq105780 | exact superpose eq105780 eq83932 | grind only

private theorem step_5_eq106202 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq102768 : (new sk2 c sk4) ∨ b = sk1) (eq105780 : c = sk2 ∨ b = sk1) : (new c c sk4) ∨ b = sk1 ∨ b = sk1 := by
  first | exact superpose eq102768 eq105780 | exact superpose eq105780 eq102768 | grind only

private theorem step_5_eq106207 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk1 : G} {sk4 : G} (eq106202 : (new c c sk4) ∨ b = sk1 ∨ b = sk1) : (new c c sk4) ∨ b = sk1 := by
  first | exact resolve eq106202 rfl | grind only

private theorem step_5_eq106211 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk4 : G} (eq106198 : ¬(old sk4 c c) ∨ b = sk1 ∨ b = sk1) : ¬(old sk4 c c) ∨ b = sk1 := by
  first | exact resolve eq106198 rfl | grind only

private theorem step_5_eq107532 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk4 : G} (eq106207 : (new c c sk4) ∨ b = sk1) (eq191 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a)) : b = sk1 ∨ (old c c sk4) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk4) c a) := by
  first | exact resolve eq106207 eq191 | exact resolve eq191 eq106207 | grind only

private theorem step_5_eq107618 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk4 : G} (eq107532 : b = sk1 ∨ (old c c sk4) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk4) c a)) (eq56 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk1 ∨ (old c c sk4) ∨ a = c ∨ (old (sF0 c c sk4) c a) := by
  first | exact resolve eq107532 eq56 | exact resolve eq56 eq107532 | grind only

private theorem step_5_eq107634 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sF0 : G → G → G → G} {sk1 : G} {sk4 : G} (eq107618 : b = sk1 ∨ (old c c sk4) ∨ a = c ∨ (old (sF0 c c sk4) c a)) (eq56 : ∀ (X0 X1 : G), ¬(old X0 c X1) ∨ c = X1) : b = sk1 ∨ (old c c sk4) ∨ a = c := by
  first | exact resolve eq107618 eq56 | exact resolve eq56 eq107618 | grind only

private theorem step_5_eq107639 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk4 : G} (eq107634 : b = sk1 ∨ (old c c sk4) ∨ a = c) (eq51 : a ≠ c) : (old c c sk4) ∨ b = sk1 := by
  first | exact resolve eq107634 eq51 | exact resolve eq51 eq107634 | grind only

private theorem step_5_eq109356 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk4 : G} (eq107639 : (old c c sk4) ∨ b = sk1) (eq128 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ (old X1 X0 X0)) : b = sk1 ∨ (old sk4 c c) := by
  first | exact resolve eq107639 eq128 | exact resolve eq128 eq107639 | grind only

private theorem step_5_eq109391 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk4 : G} (eq109356 : b = sk1 ∨ (old sk4 c c)) (eq106211 : ¬(old sk4 c c) ∨ b = sk1) : b = sk1 := by
  first | exact resolve eq109356 eq106211 | exact resolve eq106211 eq109356 | grind only

private theorem step_5_eq109396 {G : Type*} {b : G} {new : G → G → G → Prop} {sk1 : G} {sk2 : G} {sk4 : G} (eq99 : ¬(new sk4 sk1 sk2)) (eq109391 : b = sk1) : ¬(new sk4 b sk2) := by
  first | exact superpose eq99 eq109391 | exact superpose eq109391 eq99 | grind only

private theorem step_5_eq109412 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk3 : G} (eq266 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0) (eq109391 : b = sk1) : (old b sk0 sk3) ∨ a = b ∨ b = c ∨ c = sk0 := by
  first | exact superpose eq266 eq109391 | exact superpose eq109391 eq266 | grind only

private theorem step_5_eq110601 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq109412 : (old b sk0 sk3) ∨ a = b ∨ b = c ∨ c = sk0) (eq49 : a ≠ b) : (old b sk0 sk3) ∨ b = c ∨ c = sk0 := by
  first | exact resolve eq109412 eq49 | exact resolve eq49 eq109412 | grind only

private theorem step_5_eq110683 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk3 : G} (eq110601 : (old b sk0 sk3) ∨ b = c ∨ c = sk0) (eq52 : b ≠ c) : (old b sk0 sk3) ∨ c = sk0 := by
  first | exact resolve eq110601 eq52 | exact resolve eq52 eq110601 | grind only

private theorem step_5_eq111335 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq110683 : (old b sk0 sk3) ∨ c = sk0) (eq30442 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) : (old b sk0 c) ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq110683 eq30442 | exact superpose eq30442 eq110683 | grind only

private theorem step_5_eq111355 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq111335 : (old b sk0 c) ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2) : (old b sk0 c) ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq111335 rfl | grind only

private theorem step_5_eq111371 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq111355 : (old b sk0 c) ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2) (eq54 : ∀ (X0 X1 : G), ¬(old X0 X1 c) ∨ c = X1) : c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq111355 eq54 | exact resolve eq54 eq111355 | grind only

private theorem step_5_eq111418 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq111371 : c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2) (eq109391 : b = sk1) : b = c ∨ c = sk0 ∨ b = sk3 ∨ c = sk2 := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq111371 | grind only

private theorem step_5_eq111444 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq111418 : b = c ∨ c = sk0 ∨ b = sk3 ∨ c = sk2) (eq52 : b ≠ c) : b = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq111418 eq52 | exact resolve eq52 eq111418 | grind only

private theorem step_5_eq112146 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk5 : G} (eq163 : (old sk3 sk1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk5) (eq111444 : b = sk3 ∨ c = sk0 ∨ c = sk2) : (old b sk1 sk5) ∨ a = b ∨ b = c ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq163 eq111444 | exact superpose eq111444 eq163 | grind only

private theorem step_5_eq113211 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk5 : G} (eq112146 : (old b sk1 sk5) ∨ a = b ∨ b = c ∨ b = sk5 ∨ c = sk0 ∨ c = sk2) (eq49 : a ≠ b) : (old b sk1 sk5) ∨ b = c ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq112146 eq49 | exact resolve eq49 eq112146 | grind only

private theorem step_5_eq113514 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk5 : G} (eq113211 : (old b sk1 sk5) ∨ b = c ∨ b = sk5 ∨ c = sk0 ∨ c = sk2) (eq52 : b ≠ c) : (old b sk1 sk5) ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq113211 eq52 | exact resolve eq52 eq113211 | grind only

private theorem step_5_eq113767 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk5 : G} (eq113514 : (old b sk1 sk5) ∨ b = sk5 ∨ c = sk0 ∨ c = sk2) (eq109391 : b = sk1) : (old b b sk5) ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq113514 | grind only

private theorem step_5_eq113930 {G : Type*} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk5 : G} (eq113767 : (old b b sk5) ∨ b = sk5 ∨ c = sk0 ∨ c = sk2) (eq120 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : b = sk5 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq113767 eq120 | exact resolve eq120 eq113767 | grind only

private theorem step_5_eq114503 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} {sk5 : G} (eq32154 : (new sk5 b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2) (eq113930 : b = sk5 ∨ c = sk0 ∨ c = sk2) : (new b b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq32154 eq113930 | exact superpose eq113930 eq32154 | grind only

private theorem step_5_eq114642 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq114503 : (new b b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2) : (new b b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := by
  first | exact resolve eq114503 rfl | grind only

private theorem step_5_eq114705 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq114642 : (new b b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2) (eq109391 : b = sk1) : b = c ∨ (new b b sk4) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq114642 | grind only

private theorem step_5_eq114946 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq114705 : b = c ∨ (new b b sk4) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2) (eq52 : b ≠ c) : (new b b sk4) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := by
  first | exact resolve eq114705 eq52 | exact resolve eq52 eq114705 | grind only

private theorem step_5_eq115088 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} {sk4 : G} (eq114946 : (new b b sk4) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2) (eq109391 : b = sk1) : a = b ∨ (new b b sk4) ∨ c = sk0 ∨ c = sk2 := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq114946 | grind only

private theorem step_5_eq115173 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq115088 : a = b ∨ (new b b sk4) ∨ c = sk0 ∨ c = sk2) (eq49 : a ≠ b) : (new b b sk4) ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq115088 eq49 | exact resolve eq49 eq115088 | grind only

private theorem step_5_eq118444 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq115173 : (new b b sk4) ∨ c = sk0 ∨ c = sk2) (eq148 : ∀ (X0 X1 X2 : G), ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2) : c = sk0 ∨ c = sk2 ∨ (old b b sk4) ∨ a = b ∨ b = c ∨ b = sk4 := by
  first | exact resolve eq115173 eq148 | exact resolve eq148 eq115173 | grind only

private theorem step_5_eq118547 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq118444 : c = sk0 ∨ c = sk2 ∨ (old b b sk4) ∨ a = b ∨ b = c ∨ b = sk4) (eq120 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : c = sk0 ∨ c = sk2 ∨ a = b ∨ b = c ∨ b = sk4 := by
  first | exact resolve eq118444 eq120 | exact resolve eq120 eq118444 | grind only

private theorem step_5_eq118560 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk4 : G} (eq118547 : c = sk0 ∨ c = sk2 ∨ a = b ∨ b = c ∨ b = sk4) (eq49 : a ≠ b) : c = sk0 ∨ c = sk2 ∨ b = c ∨ b = sk4 := by
  first | exact resolve eq118547 eq49 | exact resolve eq49 eq118547 | grind only

private theorem step_5_eq118564 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk4 : G} (eq118560 : c = sk0 ∨ c = sk2 ∨ b = c ∨ b = sk4) (eq52 : b ≠ c) : b = sk4 ∨ c = sk2 ∨ c = sk0 := by
  first | exact resolve eq118560 eq52 | exact resolve eq52 eq118560 | grind only

private theorem step_5_eq118846 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} {sk4 : G} (eq50795 : a = sk4 ∨ c = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq118564 : b = sk4 ∨ c = sk2 ∨ c = sk0) : a = b ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk0 := by
  first | exact superpose eq50795 eq118564 | exact superpose eq118564 eq50795 | grind only

private theorem step_5_eq118955 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq118846 : a = b ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk0) : a = b ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq118846 rfl | grind only

private theorem step_5_eq119057 {G : Type*} {a : G} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq118955 : a = b ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq49 : a ≠ b) : c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq118955 eq49 | exact resolve eq49 eq118955 | grind only

private theorem step_5_eq119164 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq119057 : c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq52 : b ≠ c) : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := by
  first | exact resolve eq119057 eq52 | exact resolve eq52 eq119057 | grind only

private theorem step_5_eq119198 {G : Type*} {b : G} {c : G} {sk0 : G} {sk1 : G} {sk2 : G} {sk3 : G} (eq119164 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2) (eq109391 : b = sk1) : b = c ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq119164 | grind only

private theorem step_5_eq119214 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq119198 : b = c ∨ c = sk3 ∨ c = sk0 ∨ c = sk2) (eq52 : b ≠ c) : c = sk3 ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq119198 eq52 | exact resolve eq52 eq119198 | grind only

private theorem step_5_eq119843 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} {sk3 : G} (eq111444 : b = sk3 ∨ c = sk0 ∨ c = sk2) (eq119214 : c = sk3 ∨ c = sk0 ∨ c = sk2) : b = c ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 := by
  first | exact superpose eq111444 eq119214 | exact superpose eq119214 eq111444 | grind only

private theorem step_5_eq119848 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq119843 : b = c ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2) : b = c ∨ c = sk0 ∨ c = sk2 := by
  first | exact resolve eq119843 rfl | grind only

private theorem step_5_eq119905 {G : Type*} {b : G} {c : G} {sk0 : G} {sk2 : G} (eq119848 : b = c ∨ c = sk0 ∨ c = sk2) (eq52 : b ≠ c) : c = sk2 ∨ c = sk0 := by
  first | exact resolve eq119848 eq52 | exact resolve eq52 eq119848 | grind only

private theorem step_5_eq120672 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq297 : (old sk2 sk0 sk4) ∨ a = sk2 ∨ a = sk4 ∨ c = sk0) (eq119905 : c = sk2 ∨ c = sk0) : (old c sk0 sk4) ∨ a = c ∨ a = sk4 ∨ c = sk0 ∨ c = sk0 := by
  first | exact superpose eq297 eq119905 | exact superpose eq119905 eq297 | grind only

private theorem step_5_eq121021 {G : Type*} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk2 : G} {sk4 : G} (eq109396 : ¬(new sk4 b sk2)) (eq119905 : c = sk2 ∨ c = sk0) : ¬(new sk4 b c) ∨ c = sk0 := by
  first | exact superpose eq109396 eq119905 | exact superpose eq119905 eq109396 | grind only

private theorem step_5_eq121100 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq120672 : (old c sk0 sk4) ∨ a = c ∨ a = sk4 ∨ c = sk0 ∨ c = sk0) : (old c sk0 sk4) ∨ a = c ∨ a = sk4 ∨ c = sk0 := by
  first | exact resolve eq120672 rfl | grind only

private theorem step_5_eq121323 {G : Type*} {a : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq121100 : (old c sk0 sk4) ∨ a = c ∨ a = sk4 ∨ c = sk0) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ a = sk4 ∨ c = sk0 := by
  first | exact resolve eq121100 eq59 | exact resolve eq59 eq121100 | grind only

private theorem step_5_eq121443 {G : Type*} {a : G} {c : G} {sk0 : G} {sk4 : G} (eq121323 : a = c ∨ a = sk4 ∨ c = sk0) (eq51 : a ≠ c) : a = sk4 ∨ c = sk0 := by
  first | exact resolve eq121323 eq51 | exact resolve eq51 eq121323 | grind only

private theorem step_5_eq124470 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} {sk4 : G} (eq121021 : ¬(new sk4 b c) ∨ c = sk0) (eq121443 : a = sk4 ∨ c = sk0) : ¬(new a b c) ∨ c = sk0 ∨ c = sk0 := by
  first | exact superpose eq121021 eq121443 | exact superpose eq121443 eq121021 | grind only

private theorem step_5_eq124471 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} (eq124470 : ¬(new a b c) ∨ c = sk0 ∨ c = sk0) : ¬(new a b c) ∨ c = sk0 := by
  first | exact resolve eq124470 rfl | grind only

private theorem step_5_eq124485 {G : Type*} {a : G} {b : G} {c : G} {new : G → G → G → Prop} {sk0 : G} (eq124471 : ¬(new a b c) ∨ c = sk0) (eq92 : (new a b c)) : c = sk0 := by
  first | exact resolve eq124471 eq92 | exact resolve eq92 eq124471 | grind only

private theorem step_5_eq124536 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk0 : G} {sk1 : G} {sk2 : G} (eq475 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1) (eq124485 : c = sk0) : (old c sk1 sk2) ∨ a = c ∨ (old b sk1 a) ∨ c = sk1 := by
  first | exact superpose eq475 eq124485 | exact superpose eq124485 eq475 | grind only

private theorem step_5_eq125667 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} {sk2 : G} (eq124536 : (old c sk1 sk2) ∨ a = c ∨ (old b sk1 a) ∨ c = sk1) (eq59 : ∀ (X0 X1 : G), ¬(old c X0 X1) ∨ c = X0) : a = c ∨ (old b sk1 a) ∨ c = sk1 := by
  first | exact resolve eq124536 eq59 | exact resolve eq59 eq124536 | grind only

private theorem step_5_eq126016 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq125667 : a = c ∨ (old b sk1 a) ∨ c = sk1) (eq51 : a ≠ c) : (old b sk1 a) ∨ c = sk1 := by
  first | exact resolve eq125667 eq51 | exact resolve eq51 eq125667 | grind only

private theorem step_5_eq126276 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq126016 : (old b sk1 a) ∨ c = sk1) (eq109391 : b = sk1) : (old b b a) ∨ c = sk1 := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq126016 | grind only

private theorem step_5_eq126436 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} {sk1 : G} (eq126276 : (old b b a) ∨ c = sk1) (eq109391 : b = sk1) : b = c ∨ (old b b a) := by
  first | simpa only [eq109391, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq126276 | grind only

private theorem step_5_eq126509 {G : Type*} {a : G} {b : G} {c : G} {old : G → G → G → Prop} (eq126436 : b = c ∨ (old b b a)) (eq52 : b ≠ c) : (old b b a) := by
  first | exact resolve eq126436 eq52 | exact resolve eq52 eq126436 | grind only

private theorem step_5_eq132607 {G : Type*} {a : G} {b : G} {old : G → G → G → Prop} (eq126509 : (old b b a)) (eq120 : ∀ (X0 X1 : G), ¬(old X0 X0 X1) ∨ X0 = X1) : a = b := by
  first | exact resolve eq126509 eq120 | exact resolve eq120 eq126509 | grind only

set_option maxHeartbeats 2000000 in
private theorem preserve_5 (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (ab : a ≠ b) (diagonal : ∀ x, old x x x) (ac : a ≠ c) (bc : b ≠ c) (p3 : ∀ z, ¬ old a b z) (p4XY : ∀ x y, old x y c → x = c ∧ y = c) (p4XZ : ∀ x z, old x c z → x = c ∧ z = c) (p4YZ : ∀ y z, old c y z → y = c ∧ z = c) (new_new : new a b c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X1 ∨ ¬ old X1 X0 X2 ∨ ¬ old X2 X1 X3 ∨ old X3 X0 X2)) (old_5 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X1 X0 X3 ∨ ¬ old X2 X0 X4 ∨ ¬ old X3 X1 X5 ∨ ¬ old X5 X3 X4 ∨ old X4 X1 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬ sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬ sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬ sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬ sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬ sP1 X Y Z) (imp_new_3 : ∀ X Y Z, c ≠ X ∨ a ≠ Z ∨ ¬ old Y b b ∨ ¬ old b Y a ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = X ∨ ¬ sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬ sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬ sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬ sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), a = Z ∨ ¬ sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Y a ∨ ¬ sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old Y b b ∨ ¬ sP4 X Y Z) (new_imp : ∀ X Y Z, ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ X Y Z, ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4 X5, ¬ new X0 X1 X2 ∨ ¬ new X1 X0 X3 ∨ ¬ new X2 X0 X4 ∨ ¬ new X3 X1 X5 ∨ ¬ new X5 X3 X4 ∨ new X4 X1 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4, preserve_5⟩ := nh
  have eq49 : a ≠ b := step_5_eq49 ab
  have eq50 (X0 : G) : (old X0 X0 X0) := step_5_eq50 diagonal X0
  have eq51 : a ≠ c := step_5_eq51 ac
  have eq52 : b ≠ c := step_5_eq52 bc
  have eq53 (X0 : G) : ¬(old a b X0) := step_5_eq53 p3 X0
  have eq54 (X0 X1 : G) : ¬(old X0 X1 c) ∨ c = X1 := step_5_eq54 p4XY X0 X1
  have eq56 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X1 := step_5_eq56 p4XZ X0 X1
  have eq57 (X0 X1 : G) : ¬(old X0 c X1) ∨ c = X0 := step_5_eq57 p4XZ X0 X1
  have eq58 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X1 := step_5_eq58 p4YZ X0 X1
  have eq59 (X0 X1 : G) : ¬(old c X0 X1) ∨ c = X0 := step_5_eq59 p4YZ X0 X1
  have eq60 (X0 X1 X2 X3 : G) : ¬(old X0 X1 X3) ∨ ¬(old X0 X1 X2) ∨ X2 = X3 := step_5_eq60 old_0 X0 X1 X2 X3
  have eq62 (X0 X1 X2 X3 : G) : ¬(old X0 X1 X1) ∨ ¬(old X1 X0 X2) ∨ ¬(old X2 X1 X3) ∨ (old X3 X0 X2) := step_5_eq62 old_2 X0 X1 X2 X3
  have eq65 (X0 X1 X2 X3 X4 X5 : G) : ¬(old X5 X3 X4) ∨ ¬(old X1 X0 X3) ∨ ¬(old X2 X0 X4) ∨ ¬(old X3 X1 X5) ∨ ¬(old X0 X1 X2) ∨ (old X4 X1 X2) := step_5_eq65 old_5 X0 X1 X2 X3 X4 X5
  have eq66 (X0 X1 X2 : G) : (new X0 X1 X2) ∨ ¬(old X0 X1 X2) := step_5_eq66 imp_new_0 X0 X1 X2
  have eq68 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ a = X0 := step_5_eq68 rule_def_0_0 X0 X1 X2
  have eq69 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ b = X1 := step_5_eq69 rule_def_0_1 X0 X1 X2
  have eq70 (X0 X1 X2 : G) : ¬(sP0 X0 X1 X2) ∨ c = X2 := step_5_eq70 rule_def_0_2 X0 X1 X2
  have eq72 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ c = X1 := step_5_eq72 rule_def_1_0 X0 X1 X2
  have eq73 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ b = X2 := step_5_eq73 rule_def_1_1 X0 X1 X2
  have eq75 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (old (sF0 X0 X1 X2) X0 a) := step_5_eq75 rule_def_1_3 X0 X1 X2
  have eq76 (X0 X1 X2 : G) : c ≠ X0 ∨ a ≠ X2 ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new X0 X1 X2) := step_5_eq76 imp_new_3 X0 X1 X2
  have eq77 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ c = X0 := step_5_eq77 rule_def_2_0 X0 X1 X2
  have eq78 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = X2 := step_5_eq78 rule_def_2_1 X0 X1 X2
  have eq79 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old X1 b b) := step_5_eq79 rule_def_2_2 X0 X1 X2
  have eq80 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (old b X1 a) := step_5_eq80 rule_def_2_3 X0 X1 X2
  have eq82 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = X0 := step_5_eq82 rule_def_3_0 X0 X1 X2
  have eq83 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ c = X1 := step_5_eq83 rule_def_3_1 X0 X1 X2
  have eq84 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ b = X2 := step_5_eq84 rule_def_3_2 X0 X1 X2
  have eq87 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ c = X0 := step_5_eq87 rule_def_4_0 X0 X1 X2
  have eq88 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = X2 := step_5_eq88 rule_def_4_1 X0 X1 X2
  have eq89 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old b X1 a) := step_5_eq89 rule_def_4_2 X0 X1 X2
  have eq90 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (old X1 b b) := step_5_eq90 rule_def_4_3 X0 X1 X2
  have eq92 : (new a b c) := step_5_eq92 new_new
  have eq93 (X0 X1 X2 : G) : (sP0 X0 X1 X2) ∨ (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) := step_5_eq93 new_imp X0 X1 X2
  have eq94 : (new sk0 sk1 sk2) := step_5_eq94 preserve_0
  have eq95 : (new sk1 sk0 sk3) := step_5_eq95 preserve_1
  have eq96 : (new sk2 sk0 sk4) := step_5_eq96 preserve_2
  have eq97 : (new sk3 sk1 sk5) := step_5_eq97 preserve_3
  have eq98 : (new sk5 sk3 sk4) := step_5_eq98 preserve_4
  have eq99 : ¬(new sk4 sk1 sk2) := step_5_eq99 preserve_5
  have eq105 (X1 X2 : G) : a ≠ X2 ∨ ¬(old X1 b b) ∨ ¬(old b X1 a) ∨ (new c X1 X2) := step_5_eq105 eq76 X1 X2
  have eq106 (X1 : G) : (new c X1 a) ∨ ¬(old b X1 a) ∨ ¬(old X1 b b) := step_5_eq106 eq105 X1
  have eq119 : ¬(old sk4 sk1 sk2) := step_5_eq119 eq66 eq99
  have eq120 (X0 X1 : G) : ¬(old X0 X0 X1) ∨ X0 = X1 := step_5_eq120 eq60 eq50 X0 X1
  have eq127 (X0 X1 X2 : G) : ¬(old X0 X0 X1) ∨ ¬(old X1 X0 X2) ∨ (old X2 X0 X1) := step_5_eq127 eq62 eq50 X0 X1 X2
  have eq128 (X0 X1 : G) : ¬(old X0 X0 X1) ∨ (old X1 X0 X0) := step_5_eq128 eq127 eq50 X0 X1
  have eq133 (X0 X1 X2 : G) : (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 := step_5_eq133 eq93 eq70 X0 X1 X2
  have eq134 (X0 X1 X2 : G) : (sP3 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 := step_5_eq134 eq93 eq69 X0 X1 X2
  have eq135 (X0 X1 X2 : G) : (old X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (sP3 X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := step_5_eq135 eq93 eq68 X0 X1 X2
  have eq136 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 := step_5_eq136 eq135 eq82 X0 X1 X2
  have eq138 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := step_5_eq138 eq136 eq80 X0 X1 X2
  have eq140 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ a = X2 := step_5_eq140 eq136 eq78 X0 X1 X2
  have eq141 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ a = X0 ∨ c = X0 := step_5_eq141 eq136 eq77 X0 X1 X2
  have eq142 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 := step_5_eq142 eq141 eq87 X0 X1 X2
  have eq143 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 := step_5_eq143 eq140 eq88 X0 X1 X2
  have eq145 (X0 X1 X2 : G) : (sP1 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) := step_5_eq145 eq138 eq89 X0 X1 X2
  have eq148 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ b = X2 := step_5_eq148 eq142 eq73 X0 X1 X2
  have eq149 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ c = X0 ∨ c = X1 := step_5_eq149 eq142 eq72 X0 X1 X2
  have eq151 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 := step_5_eq151 eq133 eq84 X0 X1 X2
  have eq152 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := step_5_eq152 eq133 eq83 X0 X1 X2
  have eq154 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 := step_5_eq154 eq152 eq72 X0 X1 X2
  have eq155 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 := step_5_eq155 eq151 eq73 X0 X1 X2
  have eq163 : (old sk3 sk1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk5 := step_5_eq163 eq148 eq97
  have eq166 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := step_5_eq166 eq134 eq84 X0 X1 X2
  have eq167 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (sP1 X0 X1 X2) ∨ (sP2 X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := step_5_eq167 eq134 eq83 X0 X1 X2
  have eq169 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 := step_5_eq169 eq167 eq72 X0 X1 X2
  have eq170 (X0 X1 X2 : G) : (sP2 X0 X1 X2) ∨ ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 := step_5_eq170 eq166 eq73 X0 X1 X2
  have eq178 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ a = X2 ∨ c = X1 := step_5_eq178 eq143 eq72 X0 X1 X2
  have eq191 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ (old (sF0 X0 X1 X2) X0 a) := step_5_eq191 eq145 eq75 X0 X1 X2
  have eq194 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ a = X0 ∨ (old b X1 a) ∨ c = X1 := step_5_eq194 eq145 eq72 X0 X1 X2
  have eq201 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := step_5_eq201 eq154 eq78 X0 X1 X2
  have eq202 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := step_5_eq202 eq154 eq77 X0 X1 X2
  have eq203 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ c = X0 := step_5_eq203 eq202 eq87 X0 X1 X2
  have eq204 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ c = X1 ∨ a = X2 := step_5_eq204 eq201 eq88 X0 X1 X2
  have eq214 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ c = X2 ∨ b = X2 ∨ c = X0 := step_5_eq214 eq155 eq77 X0 X1 X2
  have eq215 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ c = X2 ∨ b = X2 ∨ c = X0 := step_5_eq215 eq214 eq87 X0 X1 X2
  have eq221 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := step_5_eq221 eq169 eq80 X0 X1 X2
  have eq222 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := step_5_eq222 eq169 eq79 X0 X1 X2
  have eq223 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := step_5_eq223 eq169 eq78 X0 X1 X2
  have eq224 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := step_5_eq224 eq169 eq77 X0 X1 X2
  have eq225 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ c = X0 := step_5_eq225 eq224 eq87 X0 X1 X2
  have eq226 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ a = X2 := step_5_eq226 eq223 eq88 X0 X1 X2
  have eq227 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old X1 b b) := step_5_eq227 eq222 eq90 X0 X1 X2
  have eq228 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ c = X1 ∨ (old b X1 a) := step_5_eq228 eq221 eq89 X0 X1 X2
  have eq234 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ (sP4 X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := step_5_eq234 eq170 eq77 X0 X1 X2
  have eq235 (X0 X1 X2 : G) : ¬(new X0 X1 X2) ∨ (old X0 X1 X2) ∨ b = X1 ∨ b = X2 ∨ c = X0 := step_5_eq235 eq234 eq87 X0 X1 X2
  have eq266 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := step_5_eq266 eq149 eq95
  have eq267 : (old sk2 sk0 sk4) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 := step_5_eq267 eq149 eq96
  have eq268 : (old sk3 sk1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 := step_5_eq268 eq149 eq97
  have eq296 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ a = sk3 ∨ c = sk0 := step_5_eq296 eq178 eq95
  have eq297 : (old sk2 sk0 sk4) ∨ a = sk2 ∨ a = sk4 ∨ c = sk0 := step_5_eq297 eq178 eq96
  have eq304 (X0 : G) : ¬(old sk2 sk0 X0) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 ∨ sk4 = X0 := step_5_eq304 eq267 eq60 X0
  have eq310 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := step_5_eq310 eq203 eq94
  have eq311 : (old sk1 sk0 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := step_5_eq311 eq203 eq95
  have eq312 : (old sk2 sk0 sk4) ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq312 eq203 eq96
  have eq313 : (old sk3 sk1 sk5) ∨ c = sk5 ∨ c = sk1 ∨ c = sk3 := step_5_eq313 eq203 eq97
  have eq314 : (old sk5 sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ c = sk5 := step_5_eq314 eq203 eq98
  have eq329 : (old sk5 sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 := step_5_eq329 eq204 eq98
  have eq341 : (old sk1 sk0 sk3) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 := step_5_eq341 eq215 eq95
  have eq370 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := step_5_eq370 eq225 eq94
  have eq371 : (old sk1 sk0 sk3) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := step_5_eq371 eq225 eq95
  have eq372 : (old sk2 sk0 sk4) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq372 eq225 eq96
  have eq373 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 := step_5_eq373 eq225 eq97
  have eq374 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ c = sk5 := step_5_eq374 eq225 eq98
  have eq385 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := step_5_eq385 eq226 eq94
  have eq388 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := step_5_eq388 eq226 eq97
  have eq389 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ a = sk4 := step_5_eq389 eq226 eq98
  have eq400 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := step_5_eq400 eq235 eq94
  have eq403 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ b = sk5 ∨ c = sk3 := step_5_eq403 eq235 eq97
  have eq475 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b sk1 a) ∨ c = sk1 := step_5_eq475 eq194 eq94
  have eq476 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ (old b sk0 a) ∨ c = sk0 := step_5_eq476 eq194 eq95
  have eq554 : (old sk5 sk3 sk4) ∨ b = sk3 ∨ c = sk3 ∨ (old sk3 b b) := step_5_eq554 eq227 eq98
  have eq556 (X0 X1 X2 : G) : ¬(old X0 X1 sk3) ∨ c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X2 X1 sk4) ∨ ¬(old sk3 X0 sk5) ∨ ¬(old X1 X0 X2) ∨ (old sk4 X0 X2) := step_5_eq556 eq314 eq65 X0 X1 X2
  have eq565 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := step_5_eq565 eq228 eq94
  have eq568 : (old sk3 sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := step_5_eq568 eq228 eq97
  have eq769 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 ∨ sk2 = X0 := step_5_eq769 eq370 eq60 X0
  have eq802 (X0 X1 X2 : G) : ¬(old X0 X1 sk3) ∨ c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X2 X1 sk4) ∨ ¬(old sk3 X0 sk5) ∨ ¬(old X1 X0 X2) ∨ (old sk4 X0 X2) := step_5_eq802 eq374 eq65 X0 X1 X2
  have eq13684 (X0 : G) : c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := step_5_eq13684 eq556 eq311 X0
  have eq13704 (X0 : G) : c = sk3 ∨ c = sk5 ∨ c = sk4 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk0 ∨ c = sk1 := step_5_eq13704 eq13684 X0
  have eq13709 (X0 : G) : ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk0 ∨ c = sk1 := step_5_eq13709 eq13704 eq313 X0
  have eq13957 (X0 : G) : c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 := step_5_eq13957 eq802 eq341 X0
  have eq13977 (X0 : G) : c = sk3 ∨ c = sk5 ∨ b = sk3 ∨ ¬(old X0 sk0 sk4) ∨ ¬(old sk3 sk1 sk5) ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1 := step_5_eq13977 eq13957 X0
  have eq13985 (X0 : G) : ¬(old X0 sk0 sk4) ∨ c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ (old sk4 sk1 X0) ∨ c = sk1 := step_5_eq13985 eq13977 eq313 X0
  have eq17643 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq17643 eq13985 eq312
  have eq17647 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq17647 eq13985 eq372
  have eq17684 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq17684 eq17647 eq310
  have eq17688 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq17688 eq17643 eq310
  have eq17694 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq17694 eq17684 eq119
  have eq17695 : c = sk5 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq17695 eq17688 eq119
  have eq17710 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq17710 eq373 eq17694
  have eq18028 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq18028 eq17710
  have eq18195 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq18195 eq18028 eq54
  have eq18304 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq18304 eq268 eq17695
  have eq18312 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq18312 eq373 eq17695
  have eq18652 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq18652 eq18312
  have eq18658 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq18658 eq18304
  have eq18820 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq18820 eq18652 eq54
  have eq18827 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq18827 eq18658 eq54
  have eq20471 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 := step_5_eq20471 eq371 eq18195
  have eq20928 : (old sk1 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk2 := step_5_eq20928 eq20471
  have eq21140 : b = sk3 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 := step_5_eq21140 eq20928 eq54
  have eq23452 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq23452 eq389 eq18820
  have eq23644 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq23644 eq23452
  have eq23744 : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq23744 eq23644 eq54
  have eq23783 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq23783 eq23744 eq51
  have eq23797 : (new sk5 c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq23797 eq98 eq23783
  have eq23818 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq23818 eq388 eq23783
  have eq24262 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq24262 eq23818
  have eq24461 : a = sk5 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq24461 eq24262 eq59
  have eq26061 : (new a c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq26061 eq23797 eq24461
  have eq26076 : (new a c sk4) ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq26076 eq26061
  have eq26770 : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ (old a c sk4) ∨ b = c ∨ b = sk4 ∨ a = c := step_5_eq26770 eq26076 eq235
  have eq26815 : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = c ∨ b = sk4 ∨ a = c := step_5_eq26815 eq26770 eq57
  have eq26832 : b = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk4 ∨ a = c := step_5_eq26832 eq26815 eq52
  have eq26838 : b = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 := step_5_eq26838 eq26832 eq51
  have eq26845 : ¬(new b sk1 sk2) ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 := step_5_eq26845 eq99 eq26838
  have eq27549 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq27549 eq389 eq18827
  have eq27751 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq27751 eq27549
  have eq27852 : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq27852 eq27751 eq54
  have eq27891 : a = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq27891 eq27852 eq51
  have eq27966 : (old sk5 a sk4) ∨ a = b ∨ a = c ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq27966 eq554 eq27891
  have eq28510 : (old sk5 a sk4) ∨ a = c ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq28510 eq27966 eq49
  have eq28580 : (old sk5 a sk4) ∨ (old a b b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq28580 eq28510 eq51
  have eq28591 : (old sk5 a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq28591 eq28580 eq53
  have eq29508 : (old c a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq29508 eq28591 eq17695
  have eq29521 : (old c a sk4) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk4 := step_5_eq29521 eq29508
  have eq29525 : c = sk4 ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 := step_5_eq29525 eq29521 eq58
  have eq30069 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 := step_5_eq30069 eq389 eq29525
  have eq30275 : (old sk5 sk3 c) ∨ b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq30275 eq30069
  have eq30393 : b = sk3 ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq30393 eq30275 eq54
  have eq30442 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq30442 eq30393 eq51
  have eq30468 : (old sk1 sk0 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq30468 eq266 eq30442
  have eq30919 : (old sk1 sk0 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk3 ∨ c = sk2 := step_5_eq30919 eq30468
  have eq31125 : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := step_5_eq31125 eq30919 eq54
  have eq32154 : (new sk5 b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := step_5_eq32154 eq98 eq31125
  have eq50018 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq50018 eq13709 eq312
  have eq50074 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50074 eq50018
  have eq50103 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ (old sk4 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50103 eq50074 eq310
  have eq50114 : c = sk5 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50114 eq50103 eq119
  have eq50131 : (old c sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50131 eq329 eq50114
  have eq50133 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50133 eq373 eq50114
  have eq50595 : (old sk3 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk2 := step_5_eq50595 eq50133
  have eq50597 : (old c sk3 sk4) ∨ c = sk4 ∨ c = sk3 ∨ a = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50597 eq50131
  have eq50793 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq50793 eq50595 eq54
  have eq50795 : a = sk4 ∨ c = sk3 ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq50795 eq50597 eq58
  have eq50921 : (old sk2 sk0 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq50921 eq267 eq50793
  have eq50929 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq50929 eq372 eq50793
  have eq51181 : (old sk2 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 := step_5_eq51181 eq50929
  have eq51187 : (old sk2 sk0 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk1 := step_5_eq51187 eq50921
  have eq51299 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 := step_5_eq51299 eq51181 eq54
  have eq51305 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := step_5_eq51305 eq51187 eq54
  have eq52619 : b = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 := step_5_eq52619 eq21140 eq51299
  have eq52680 : b = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk2 := step_5_eq52680 eq52619
  have eq52874 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := step_5_eq52874 eq52680 eq52
  have eq53289 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := step_5_eq53289 eq370 eq52874
  have eq53715 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := step_5_eq53715 eq53289
  have eq53923 : c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq53923 eq53715 eq54
  have eq54046 : (new sk2 c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq54046 eq96 eq53923
  have eq54075 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq54075 eq385 eq53923
  have eq54102 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq54102 eq565 eq53923
  have eq54794 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ b = sk0 := step_5_eq54794 eq54102
  have eq54806 : (old c sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ b = sk0 := step_5_eq54806 eq54075
  have eq55105 : (old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq55105 eq54794 eq59
  have eq55127 : a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq55127 eq54806 eq59
  have eq55325 : ¬(old sk4 sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq55325 eq119 eq55127
  have eq57315 : (new a c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq57315 eq54046 eq55127
  have eq57344 : (new a c sk4) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq57344 eq57315
  have eq58336 : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ (old a c sk4) ∨ b = c ∨ b = sk4 ∨ a = c := step_5_eq58336 eq57344 eq235
  have eq58401 : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = c ∨ b = sk4 ∨ a = c := step_5_eq58401 eq58336 eq57
  have eq58418 : c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = sk4 ∨ a = c := step_5_eq58418 eq58401 eq52
  have eq58424 : b = sk4 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 := step_5_eq58424 eq58418 eq51
  have eq58673 : ¬(old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ b = sk1 ∨ b = sk0 ∨ c = sk1 := step_5_eq58673 eq55325 eq58424
  have eq58678 : ¬(old b sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 := step_5_eq58678 eq58673
  have eq58754 : b = sk0 ∨ b = sk1 ∨ c = sk1 := step_5_eq58754 eq58678 eq55105
  have eq58836 : (new b sk1 sk2) ∨ b = sk1 ∨ c = sk1 := step_5_eq58836 eq94 eq58754
  have eq58873 : (old sk2 b sk4) ∨ c = sk4 ∨ b = c ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := step_5_eq58873 eq312 eq58754
  have eq58890 : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ c = sk1 := step_5_eq58890 eq370 eq58754
  have eq59002 (X0 : G) : ¬(old b sk1 X0) ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ sk2 = X0 ∨ b = sk1 ∨ c = sk1 := step_5_eq59002 eq769 eq58754 X0
  have eq59757 (X0 : G) : ¬(old b sk1 X0) ∨ c = sk1 ∨ b = c ∨ b = sk1 ∨ sk2 = X0 := step_5_eq59757 eq59002 X0
  have eq59792 : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = c := step_5_eq59792 eq58890
  have eq60036 (X0 : G) : ¬(old b sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0 := step_5_eq60036 eq59757 eq52 X0
  have eq60087 : (old b sk1 sk2) ∨ b = sk1 ∨ c = sk1 := step_5_eq60087 eq59792 eq52
  have eq60095 : (old sk2 b sk4) ∨ c = sk4 ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := step_5_eq60095 eq58873 eq52
  have eq60188 : b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk3 := step_5_eq60188 eq58836 eq26845
  have eq60265 : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk1 := step_5_eq60265 eq60188
  have eq60866 : (new sk1 sk0 b) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ b = sk1 := step_5_eq60866 eq95 eq60265
  have eq64181 : (new sk1 b b) ∨ c = sk1 ∨ b = c ∨ c = sk2 ∨ b = sk1 ∨ b = sk1 ∨ c = sk1 := step_5_eq64181 eq60866 eq58754
  have eq64182 : (new sk1 b b) ∨ c = sk1 ∨ b = c ∨ c = sk2 ∨ b = sk1 := step_5_eq64182 eq64181
  have eq64204 : (new sk1 b b) ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 := step_5_eq64204 eq64182 eq52
  have eq64236 : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old sk1 b b) ∨ b = c ∨ b = c ∨ c = sk1 := step_5_eq64236 eq64204 eq203
  have eq64281 : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old sk1 b b) ∨ b = c := step_5_eq64281 eq64236
  have eq64294 : (old sk1 b b) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := step_5_eq64294 eq64281 eq52
  have eq77860 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := step_5_eq77860 eq568 eq51305
  have eq78542 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := step_5_eq78542 eq77860
  have eq78834 : (old c sk1 sk5) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk2 := step_5_eq78834 eq78542 eq60036
  have eq78955 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk1 := step_5_eq78955 eq78834 eq59
  have eq78997 : (new sk0 sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk1 := step_5_eq78997 eq94 eq78955
  have eq80452 : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = c ∨ b = sk1 ∨ b = sk1 ∨ c = sk1 := step_5_eq80452 eq78997 eq58754
  have eq80453 : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = c ∨ b = sk1 := step_5_eq80453 eq80452
  have eq80484 : (new b sk1 a) ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 := step_5_eq80484 eq80453 eq52
  have eq80526 : c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (old b sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ (old b sk1 a) := step_5_eq80526 eq80484 eq228
  have eq80561 : (old b sk1 a) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := step_5_eq80561 eq80526
  have eq80616 : c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ a = sk2 := step_5_eq80616 eq80561 eq60036
  have eq80626 : a = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq80626 eq80616
  have eq80634 : ¬(new sk4 sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq80634 eq99 eq80626
  have eq80932 : (old a b sk4) ∨ c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq80932 eq60095 eq80626
  have eq80956 : (old a b sk4) ∨ c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq80956 eq80932
  have eq81032 : c = sk4 ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq81032 eq80956 eq53
  have eq81084 : c = sk4 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq81084 eq81032 eq51
  have eq82623 : ¬(new c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq82623 eq80634 eq81084
  have eq82624 : ¬(new c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := step_5_eq82624 eq82623
  have eq83278 : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old b sk1 a) ∨ ¬(old sk1 b b) := step_5_eq83278 eq82624 eq106
  have eq83284 : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old sk1 b b) := step_5_eq83284 eq83278 eq80561
  have eq83285 : c = sk2 ∨ c = sk1 ∨ b = sk1 := step_5_eq83285 eq83284 eq64294
  have eq83616 : (old b sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := step_5_eq83616 eq60087 eq83285
  have eq83621 : (old b sk1 c) ∨ b = sk1 ∨ c = sk1 := step_5_eq83621 eq83616
  have eq83686 : c = sk1 ∨ b = sk1 := step_5_eq83686 eq83621 eq54
  have eq83928 : (new sk0 c sk2) ∨ b = sk1 := step_5_eq83928 eq94 eq83686
  have eq83930 : (new sk3 c sk5) ∨ b = sk1 := step_5_eq83930 eq97 eq83686
  have eq83931 : ¬(new sk4 c sk2) ∨ b = sk1 := step_5_eq83931 eq99 eq83686
  have eq83932 : ¬(old sk4 c sk2) ∨ b = sk1 := step_5_eq83932 eq119 eq83686
  have eq83944 : (old c sk0 sk3) ∨ a = c ∨ a = sk3 ∨ c = sk0 ∨ b = sk1 := step_5_eq83944 eq296 eq83686
  have eq83962 : (old sk0 c sk2) ∨ b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := step_5_eq83962 eq400 eq83686
  have eq83963 : (old sk3 c sk5) ∨ b = c ∨ b = sk5 ∨ c = sk3 ∨ b = sk1 := step_5_eq83963 eq403 eq83686
  have eq83976 : (old c sk0 sk3) ∨ a = c ∨ (old b sk0 a) ∨ c = sk0 ∨ b = sk1 := step_5_eq83976 eq476 eq83686
  have eq84961 : a = c ∨ (old b sk0 a) ∨ c = sk0 ∨ b = sk1 := step_5_eq84961 eq83976 eq59
  have eq84966 : b = c ∨ b = sk5 ∨ c = sk3 ∨ b = sk1 := step_5_eq84966 eq83963 eq57
  have eq84967 : b = c ∨ b = sk2 ∨ c = sk0 ∨ b = sk1 := step_5_eq84967 eq83962 eq57
  have eq84979 : a = c ∨ a = sk3 ∨ c = sk0 ∨ b = sk1 := step_5_eq84979 eq83944 eq59
  have eq85080 : (old b sk0 a) ∨ c = sk0 ∨ b = sk1 := step_5_eq85080 eq84961 eq51
  have eq85081 : b = sk5 ∨ c = sk3 ∨ b = sk1 := step_5_eq85081 eq84966 eq52
  have eq85082 : b = sk2 ∨ c = sk0 ∨ b = sk1 := step_5_eq85082 eq84967 eq52
  have eq85083 : a = sk3 ∨ c = sk0 ∨ b = sk1 := step_5_eq85083 eq84979 eq51
  have eq86295 : (new sk3 c b) ∨ b = sk1 ∨ c = sk3 ∨ b = sk1 := step_5_eq86295 eq83930 eq85081
  have eq86296 : (new sk3 c b) ∨ b = sk1 ∨ c = sk3 := step_5_eq86296 eq86295
  have eq86747 (X0 : G) : ¬(old b sk0 X0) ∨ b = c ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ c = sk0 ∨ b = sk1 := step_5_eq86747 eq304 eq85082 X0
  have eq87205 : ¬(new sk4 c b) ∨ b = sk1 ∨ c = sk0 ∨ b = sk1 := step_5_eq87205 eq83931 eq85082
  have eq87208 : ¬(new sk4 c b) ∨ b = sk1 ∨ c = sk0 := step_5_eq87208 eq87205
  have eq87374 (X0 : G) : ¬(old b sk0 X0) ∨ b = c ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ b = sk1 := step_5_eq87374 eq86747 X0
  have eq87585 (X0 : G) : ¬(old b sk0 X0) ∨ c = sk0 ∨ a = b ∨ sk4 = X0 ∨ b = sk1 := step_5_eq87585 eq87374 eq52 X0
  have eq87638 (X0 : G) : ¬(old b sk0 X0) ∨ c = sk0 ∨ sk4 = X0 ∨ b = sk1 := step_5_eq87638 eq87585 eq49 X0
  have eq92988 : (new a c b) ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ b = sk1 := step_5_eq92988 eq86296 eq85083
  have eq92991 : (new a c b) ∨ b = sk1 ∨ a = c ∨ c = sk0 := step_5_eq92991 eq92988
  have eq93012 : (new a c b) ∨ b = sk1 ∨ c = sk0 := step_5_eq93012 eq92991 eq51
  have eq102284 : c = sk0 ∨ a = sk4 ∨ b = sk1 ∨ c = sk0 ∨ b = sk1 := step_5_eq102284 eq87638 eq85080
  have eq102289 : a = sk4 ∨ c = sk0 ∨ b = sk1 := step_5_eq102289 eq102284
  have eq102586 : ¬(new a c b) ∨ b = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk1 := step_5_eq102586 eq87208 eq102289
  have eq102619 : ¬(new a c b) ∨ b = sk1 ∨ c = sk0 := step_5_eq102619 eq102586
  have eq102723 : c = sk0 ∨ b = sk1 := step_5_eq102723 eq102619 eq93012
  have eq102768 : (new sk2 c sk4) ∨ b = sk1 := step_5_eq102768 eq96 eq102723
  have eq103486 : (new c c sk2) ∨ b = sk1 ∨ b = sk1 := step_5_eq103486 eq83928 eq102723
  have eq103517 : (new c c sk2) ∨ b = sk1 := step_5_eq103517 eq103486
  have eq104500 : b = sk1 ∨ (old c c sk2) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk2) c a) := step_5_eq104500 eq103517 eq191
  have eq104570 : b = sk1 ∨ (old c c sk2) ∨ a = c ∨ (old (sF0 c c sk2) c a) := step_5_eq104570 eq104500 eq56
  have eq104586 : b = sk1 ∨ (old c c sk2) ∨ a = c := step_5_eq104586 eq104570 eq56
  have eq104591 : (old c c sk2) ∨ b = sk1 := step_5_eq104591 eq104586 eq51
  have eq105780 : c = sk2 ∨ b = sk1 := step_5_eq105780 eq104591 eq58
  have eq106198 : ¬(old sk4 c c) ∨ b = sk1 ∨ b = sk1 := step_5_eq106198 eq83932 eq105780
  have eq106202 : (new c c sk4) ∨ b = sk1 ∨ b = sk1 := step_5_eq106202 eq102768 eq105780
  have eq106207 : (new c c sk4) ∨ b = sk1 := step_5_eq106207 eq106202
  have eq106211 : ¬(old sk4 c c) ∨ b = sk1 := step_5_eq106211 eq106198
  have eq107532 : b = sk1 ∨ (old c c sk4) ∨ a = c ∨ (old b c a) ∨ (old (sF0 c c sk4) c a) := step_5_eq107532 eq106207 eq191
  have eq107618 : b = sk1 ∨ (old c c sk4) ∨ a = c ∨ (old (sF0 c c sk4) c a) := step_5_eq107618 eq107532 eq56
  have eq107634 : b = sk1 ∨ (old c c sk4) ∨ a = c := step_5_eq107634 eq107618 eq56
  have eq107639 : (old c c sk4) ∨ b = sk1 := step_5_eq107639 eq107634 eq51
  have eq109356 : b = sk1 ∨ (old sk4 c c) := step_5_eq109356 eq107639 eq128
  have eq109391 : b = sk1 := step_5_eq109391 eq109356 eq106211
  have eq109396 : ¬(new sk4 b sk2) := step_5_eq109396 eq99 eq109391
  have eq109412 : (old b sk0 sk3) ∨ a = b ∨ b = c ∨ c = sk0 := step_5_eq109412 eq266 eq109391
  have eq110601 : (old b sk0 sk3) ∨ b = c ∨ c = sk0 := step_5_eq110601 eq109412 eq49
  have eq110683 : (old b sk0 sk3) ∨ c = sk0 := step_5_eq110683 eq110601 eq52
  have eq111335 : (old b sk0 c) ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := step_5_eq111335 eq110683 eq30442
  have eq111355 : (old b sk0 c) ∨ c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := step_5_eq111355 eq111335
  have eq111371 : c = sk0 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := step_5_eq111371 eq111355 eq54
  have eq111418 : b = c ∨ c = sk0 ∨ b = sk3 ∨ c = sk2 := step_5_eq111418 eq111371 eq109391
  have eq111444 : b = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq111444 eq111418 eq52
  have eq112146 : (old b sk1 sk5) ∨ a = b ∨ b = c ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := step_5_eq112146 eq163 eq111444
  have eq113211 : (old b sk1 sk5) ∨ b = c ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := step_5_eq113211 eq112146 eq49
  have eq113514 : (old b sk1 sk5) ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := step_5_eq113514 eq113211 eq52
  have eq113767 : (old b b sk5) ∨ b = sk5 ∨ c = sk0 ∨ c = sk2 := step_5_eq113767 eq113514 eq109391
  have eq113930 : b = sk5 ∨ c = sk0 ∨ c = sk2 := step_5_eq113930 eq113767 eq120
  have eq114503 : (new b b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 := step_5_eq114503 eq32154 eq113930
  have eq114642 : (new b b sk4) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := step_5_eq114642 eq114503
  have eq114705 : b = c ∨ (new b b sk4) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := step_5_eq114705 eq114642 eq109391
  have eq114946 : (new b b sk4) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := step_5_eq114946 eq114705 eq52
  have eq115088 : a = b ∨ (new b b sk4) ∨ c = sk0 ∨ c = sk2 := step_5_eq115088 eq114946 eq109391
  have eq115173 : (new b b sk4) ∨ c = sk0 ∨ c = sk2 := step_5_eq115173 eq115088 eq49
  have eq118444 : c = sk0 ∨ c = sk2 ∨ (old b b sk4) ∨ a = b ∨ b = c ∨ b = sk4 := step_5_eq118444 eq115173 eq148
  have eq118547 : c = sk0 ∨ c = sk2 ∨ a = b ∨ b = c ∨ b = sk4 := step_5_eq118547 eq118444 eq120
  have eq118560 : c = sk0 ∨ c = sk2 ∨ b = c ∨ b = sk4 := step_5_eq118560 eq118547 eq49
  have eq118564 : b = sk4 ∨ c = sk2 ∨ c = sk0 := step_5_eq118564 eq118560 eq52
  have eq118846 : a = b ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk0 := step_5_eq118846 eq50795 eq118564
  have eq118955 : a = b ∨ c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq118955 eq118846
  have eq119057 : c = sk3 ∨ b = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq119057 eq118955 eq49
  have eq119164 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := step_5_eq119164 eq119057 eq52
  have eq119198 : b = c ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq119198 eq119164 eq109391
  have eq119214 : c = sk3 ∨ c = sk0 ∨ c = sk2 := step_5_eq119214 eq119198 eq52
  have eq119843 : b = c ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk2 := step_5_eq119843 eq111444 eq119214
  have eq119848 : b = c ∨ c = sk0 ∨ c = sk2 := step_5_eq119848 eq119843
  have eq119905 : c = sk2 ∨ c = sk0 := step_5_eq119905 eq119848 eq52
  have eq120672 : (old c sk0 sk4) ∨ a = c ∨ a = sk4 ∨ c = sk0 ∨ c = sk0 := step_5_eq120672 eq297 eq119905
  have eq121021 : ¬(new sk4 b c) ∨ c = sk0 := step_5_eq121021 eq109396 eq119905
  have eq121100 : (old c sk0 sk4) ∨ a = c ∨ a = sk4 ∨ c = sk0 := step_5_eq121100 eq120672
  have eq121323 : a = c ∨ a = sk4 ∨ c = sk0 := step_5_eq121323 eq121100 eq59
  have eq121443 : a = sk4 ∨ c = sk0 := step_5_eq121443 eq121323 eq51
  have eq124470 : ¬(new a b c) ∨ c = sk0 ∨ c = sk0 := step_5_eq124470 eq121021 eq121443
  have eq124471 : ¬(new a b c) ∨ c = sk0 := step_5_eq124471 eq124470
  have eq124485 : c = sk0 := step_5_eq124485 eq124471 eq92
  have eq124536 : (old c sk1 sk2) ∨ a = c ∨ (old b sk1 a) ∨ c = sk1 := step_5_eq124536 eq475 eq124485
  have eq125667 : a = c ∨ (old b sk1 a) ∨ c = sk1 := step_5_eq125667 eq124536 eq59
  have eq126016 : (old b sk1 a) ∨ c = sk1 := step_5_eq126016 eq125667 eq51
  have eq126276 : (old b b a) ∨ c = sk1 := step_5_eq126276 eq126016 eq109391
  have eq126436 : b = c ∨ (old b b a) := step_5_eq126436 eq126276 eq109391
  have eq126509 : (old b b a) := step_5_eq126509 eq126436 eq52
  have eq132607 : a = b := step_5_eq132607 eq126509 eq120
  clear * - eq132607 eq49
  first | subsumption eq132607 eq49 | grind only


structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  diagonal : ∀ x, R x x x
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X2 X0 X3 ∨ ¬ R X3 X1 X4 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X1 ∨ ¬ R X1 X0 X2 ∨ ¬ R X2 X1 X3 ∨ R X3 X0 X2)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X1 X1 ∨ ¬ R X1 X0 X2 ∨ R X1 X2 X0)
  rule_4 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X1 X3 X0 ∨ ¬ R X3 X1 X2 ∨ ¬ R X3 X2 X2 ∨ R X2 X3 X0)
  rule_5 : (∀ X0 X1 X2 X3 X4 X5, ¬ R X0 X1 X2 ∨ ¬ R X1 X0 X3 ∨ ¬ R X2 X0 X4 ∨ ¬ R X3 X1 X5 ∨ ¬ R X5 X3 X4 ∨ R X4 X1 X2)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬ R X Y Z ∨ (X = Y ∧ Y = Z) ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬ R X Y Z ∨ (X = Y ∧ Y = Z) ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬ R X Y Z ∨ (X = Y ∧ Y = Z) ∨ Z ∈ finsupp

variable {G : Type*} (ps : PartialSolution G)

set_option maxHeartbeats 4000000 in
/-- Extend the partial multiplication without altering any old product. -/
theorem PartialSolution.adjoin (a b c : G) (ab : a ≠ b) (ac : a ≠ c) (bc : c ≠ b)
    (p3 : ∀ z, ¬ ps.R a b z)
    (p4XY : ∀ x y, ps.R x y c → x = c ∧ y = c)
    (p4XZ : ∀ x z, ps.R x c z → x = c ∧ z = c)
    (p4YZ : ∀ y z, ps.R c y z → y = c ∧ z = c) :
    ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by
  classical
  let sP0 (X Y Z : G) := a = X ∧ b = Y ∧ c = Z
  have hsP0 (X Y Z : G) (h : sP0 X Y Z) : a = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP0
  obtain ⟨rule_def_0_0, rule_def_0_1, rule_def_0_2⟩ := hsP0
  simp_rw [or_comm] at rule_def_0_0 rule_def_0_1 rule_def_0_2
  let sP1 (X Y Z : G) := ∃ sF0, c = Y ∧ b = Z ∧ ps.R X b sF0 ∧ ps.R sF0 X a
  choose! sF0 hsP1 using fun (X Y Z : G) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z : G) := c = X ∧ a = Z ∧ ps.R Y b b ∧ ps.R b Y a
  have hsP2 (X Y Z : G) (h : sP2 X Y Z) : c = X ∧ a = Z ∧ ps.R Y b b ∧ ps.R b Y a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3
  let sP3 (X Y Z : G) := a = X ∧ c = Y ∧ b = Z ∧ ps.R b a a
  have hsP3 (X Y Z : G) (h : sP3 X Y Z) : a = X ∧ c = Y ∧ b = Z ∧ ps.R b a a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP3
  obtain ⟨rule_def_3_0, rule_def_3_1, rule_def_3_2, rule_def_3_3⟩ := hsP3
  simp_rw [or_comm] at rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3
  let sP4 (X Y Z : G) := c = X ∧ a = Z ∧ ps.R b Y a ∧ ps.R Y b b ∧ ps.R b Y a
  have hsP4 (X Y Z : G) (h : sP4 X Y Z) : c = X ∧ a = Z ∧ ps.R b Y a ∧ ps.R Y b b ∧ ps.R b Y a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP4
  obtain ⟨rule_def_4_0, rule_def_4_1, rule_def_4_2, rule_def_4_3, rule_def_4_4⟩ := hsP4
  simp_rw [or_comm] at rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4
  let new (X Y Z : G) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z
  have new_new : new a b c := by simp only [new, sP0, true_or, or_true, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_4 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_5 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z := id
  simp only [imp_iff_not_or] at imp_new_0 new_imp
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [not_and, not_exists, imp_iff_not_or, sP3, ← forall_or_right, or_assoc] at imp_new_4
  simp only [not_and, not_exists, imp_iff_not_or, sP4, ← forall_or_right, or_assoc] at imp_new_5
  have prev_0 := preserve_0 G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 ab ps.diagonal ac (Ne.symm bc) p3 p4XY p4XZ p4YZ ps.rule_0 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_4 new_imp
  have prev_1 := preserve_1 G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 ab ps.diagonal ac (Ne.symm bc) p3 p4XY p4XZ p4YZ new_new ps.rule_0 ps.rule_1 ps.rule_3 ps.rule_4 ps.rule_5 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 new_imp imp_new_0
  have prev_2 := preserve_2 G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 ab ps.diagonal ac (Ne.symm bc) p3 p4XY p4XZ p4YZ ps.rule_2 ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_3 rule_def_4_4 new_imp imp_new_0
  have prev_3 := preserve_3 G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 ab ps.diagonal ac (Ne.symm bc) p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 imp_new_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_3 rule_def_4_4 new_imp imp_new_0
  have prev_4 := preserve_4 G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 ab ps.diagonal ac (Ne.symm bc) p3 p4XY p4XZ p4YZ ps.rule_2 ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_3 rule_def_4_4 new_imp imp_new_0
  have prev_5 := preserve_5 G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 ab ps.diagonal ac (Ne.symm bc) p3 p4XY p4XZ p4YZ new_new ps.rule_0 ps.rule_2 ps.rule_5 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_3 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 new_imp imp_new_0
  refine ⟨{ R := new, diagonal := fun x => Or.inl (ps.diagonal x), rule_0 := prev_0, rule_1 := prev_1, rule_2 := prev_2, rule_3 := prev_3, rule_4 := prev_4, rule_5 := prev_5,
            finsupp := ps.finsupp ∪ {a, b, c}, mem_1 := ?_, mem_2 := ?_, mem_3 := ?_ }, ?_⟩
  · have hm := ps.mem_1
    have hm2 := ps.mem_2
    have hm3 := ps.mem_3
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    simp only [new, sP0, sP1, sP2, sP3, sP4]
    clear * - ps hm hm2 hm3 a b c ab ac bc
    grind only
  · have hm := ps.mem_1
    have hm2 := ps.mem_2
    have hm3 := ps.mem_3
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    simp only [new, sP0, sP1, sP2, sP3, sP4]
    clear * - ps hm hm2 hm3 a b c ab ac bc
    grind only
  · have hm := ps.mem_1
    have hm2 := ps.mem_2
    have hm3 := ps.mem_3
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    simp only [new, sP0, sP1, sP2, sP3, sP4]
    clear * - ps hm hm2 hm3 a b c ab ac bc
    grind only
  · exact ⟨new_new, fun _ _ _ h => Or.inl h⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose_spec
    (ps.adjoin a b c (by intro hab; subst b; exact h ⟨a, ps.diagonal a⟩)
        (by simp_all [eq_comm]) (by simp_all) (by simpa using h)
        (fun x y hr ↦ by have := ps.mem_3 x y c; simp_all)
        (fun x z hr ↦ by have := ps.mem_2 x c z; simp_all)
        (fun y z hr ↦ by have := ps.mem_1 c y z; simp_all)).choose

lemma PartialSolution.addArbitrary_covers [Infinite G] (a b : G) :
    ∃ c, (ps.addArbitrary a b).R a b c := by
  unfold addArbitrary
  split
  · assumption
  · generalize_proofs h1 h2 h3
    exact ⟨h1.choose, (h3 h2).choose_spec.1⟩

lemma PartialSolution.addArbitrary_contains [Infinite G] (a b : G) :
    ∀ x y z, ps.R x y z → (ps.addArbitrary a b).R x y z := by
  unfold addArbitrary
  split
  · simp
  · generalize_proofs v1 v2 v3
    exact (v3 v2).choose_spec.2

variable (ps : PartialSolution ℕ)

include ps in
noncomputable def PartialSolution.complSeq : ℕ → PartialSolution ℕ
| 0 => ps
| n+1 => (complSeq n).addArbitrary n.unpair.1 n.unpair.2

lemma PartialSolution.complSeq_exists (a b : ℕ) : ∃ c, (complSeq ps (Nat.pair a b + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_covers

lemma PartialSolution.complSeq_mono_add_one (i : ℕ) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps (i + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_contains
  exact h

lemma PartialSolution.complSeq_mono (i j : ℕ) (hij : i ≤ j) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps j).R a b c := by
  induction hij
  · exact h
  · apply ps.complSeq_mono_add_one
    assumption

lemma PartialSolution.complSeq_exists_of_lt (a b i : ℕ) (h : Nat.pair a b < i) :
    ∃ c, (complSeq ps i).R a b c := by
  obtain ⟨c, hc⟩ := ps.complSeq_exists a b
  use c
  apply complSeq_mono _ _ _ _ _ _ _ hc
  omega

noncomputable def PartialSolution.compl (a b c : ℕ) : Prop :=
  (ps.complSeq (Nat.pair a b + 1)).R a b c

theorem PartialSolution.compl_rule0 (a b c d : ℕ)
    (h : ps.compl a b c) (h2 : ps.compl a b d) : c = d := by
  unfold compl at *
  have := (ps.complSeq (Nat.pair a b + 1)).rule_0 a b c d
  simp_all

theorem PartialSolution.compl_exists (a b : ℕ) : ∃ c, ps.compl a b c :=
  complSeq_exists ..

lemma PartialSolution.complSeq_of_compl_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) (h : ps.compl a b c) : (ps.complSeq i).R a b c :=
  PartialSolution.complSeq_mono _ _ _ (by omega) _ _ _ h

lemma PartialSolution.complSeq_iff_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) : ps.compl a b c ↔ (ps.complSeq i).R a b c := by
  constructor
  · intro
    apply PartialSolution.complSeq_of_compl_of_lt <;> assumption
  · intro h
    have ⟨c', hc⟩ := ps.compl_exists a b
    convert hc
    have := ps.complSeq_of_compl_of_lt a b i habi c' hc
    have := (ps.complSeq i).rule_0 a b c c'
    simp_all

theorem PartialSolution.compl_rule1 : (∀ X0 X1 X2 X3 X4, ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X2 X0 X3 ∨ ¬ ps.compl X3 X1 X4 ∨ ps.compl X0 X4 X1) := by
  intro X0 X1 X2 X3 X4
  let i := 1 + (max (Nat.pair X0 X4) (max (Nat.pair X3 X1) (max (Nat.pair X2 X0) (max (Nat.pair X0 X1) 0))))
  repeat rw [PartialSolution.complSeq_iff_of_lt _ _ _ i]
  apply PartialSolution.rule_1
  all_goals omega

noncomputable def PartialSolution.complFun (a b : ℕ) : ℕ := (ps.compl_exists a b).choose

theorem PartialSolution.complFun_eq_iff (a b c : ℕ) : ps.complFun a b = c ↔ ps.compl a b c := by
  constructor
  · rintro rfl
    exact (ps.compl_exists a b).choose_spec
  · intro h
    have : ps.compl a b (ps.complFun a b) := (ps.compl_exists a b).choose_spec
    exact ps.compl_rule0 a b _ _ this h

lemma PartialSolution.of_R (a b c : ℕ) (h : ps.R a b c) : ps.complFun a b = c := by
  rw [PartialSolution.complFun_eq_iff]
  apply PartialSolution.complSeq_mono _ 0 _ (by simp) _ _ _ h

@[implicit_reducible] noncomputable def PartialSolution.toMagma : Magma ℕ where
  op := ps.complFun

theorem PartialSolution.toMagma_equation1315 :
    letI := ps.toMagma
    Equation1315 ℕ := by
  simp only [Equation1315]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 (X1) (X0) (ps.complFun X1 X0) (ps.complFun (ps.complFun X1 X0) X1) (ps.complFun (ps.complFun (ps.complFun X1 X0) X1) X0)

theorem PartialSolution.toMagma_idempotent (x : ℕ) :
    ps.complFun x x = x := ps.of_R x x x (ps.diagonal x)

/-- Two entries in the zero row agree, and all diagonal products are present. -/
def collisionSeed : PartialSolution Nat where
  R x y z := (x = y ∧ y = z) ∨ (x = 0 ∧ (y = 1 ∨ y = 2) ∧ z = 3)
  diagonal x := Or.inl ⟨rfl, rfl⟩
  rule_0 := by simp only [← imp_iff_not_or]; grind
  rule_1 := by simp only [← imp_iff_not_or]; grind
  rule_2 := by simp only [← imp_iff_not_or]; grind
  rule_3 := by simp only [← imp_iff_not_or]; grind
  rule_4 := by simp only [← imp_iff_not_or]; grind
  rule_5 := by simp only [← imp_iff_not_or]; grind
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or, Finset.mem_insert, Finset.mem_singleton]; grind
  mem_2 := by simp only [← imp_iff_not_or, Finset.mem_insert, Finset.mem_singleton]; grind
  mem_3 := by simp only [← imp_iff_not_or, Finset.mem_insert, Finset.mem_singleton]; grind


end Eq1315Idempotent
