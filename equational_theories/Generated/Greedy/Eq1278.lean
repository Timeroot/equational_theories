import Mathlib.Tactic.ClearExcept
import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

/-!
# Countable completions for E1278 with injective squaring

Every finite partial table satisfying the four core invariants below extends to a
model of E1278 on `Nat`. The extra square-injectivity invariant makes the greedy
extension close after seven patterns of new products. Nine other discovered
invariants follow from the four core conditions. Enumerating all pairs of
natural numbers then gives a total operation, without identifying old elements.

The preservation lemmas replay Vampire's first-order and propositional proofs
as ordinary Lean proofs. No external prover or certificate is needed at build
time. The small collision seed and the catalogue result are in
`Parastrophes/Equation1278.lean`.
-/

set_option linter.all false
namespace Eq1278

set_option maxHeartbeats 8000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_10 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X0 ∨ ¬ old X1 X0 X2 ∨ ¬ old X1 X1 X1 ∨ ¬ old X1 X3 X2 ∨ ¬ old X3 X3 X3 ∨ X0 = X3)) (old_12 : (∀ X0 X1 X2 X3 X4 X5 X6 X7, ¬ old X0 X0 X1 ∨ ¬ old X2 X0 X3 ∨ ¬ old X2 X2 X4 ∨ ¬ old X2 X5 X3 ∨ ¬ old X4 X1 X6 ∨ ¬ old X4 X7 X6 ∨ ¬ old X5 X5 X7 ∨ X0 = X5)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old b a a ∨ ¬sP2 X Y Z) (rule_def_2_5 : ∀ (X Y Z : G), old b b b ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b Z a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z Z Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old (sF1 X Y Z) (sF2 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old Z Z (sF2 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_6_4 : ∀ (X Y Z : G), old a a (sF6 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  classical
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have f1 : (a ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using ac
  have f2 : (b ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using bc
  have f3 : (∀ (X0 : G), (¬ (old a b X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p3
  have f4 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XY
  have f5 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XZ
  have f6 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4YZ
  have f7 : (∀ (X0 X1 X2 X3 : G), ((¬ (old X0 X1 X2)) ∨ ((¬ (old X0 X1 X3)) ∨ (X2 = X3)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_0
  have f17 : (∀ (X0 X1 X2 X3 : G), ((¬ (old X0 X0 X0)) ∨ ((¬ (old X1 X0 X2)) ∨ ((¬ (old X1 X1 X1)) ∨ ((¬ (old X1 X3 X2)) ∨ ((¬ (old X3 X3 X3)) ∨ (X0 = X3))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_10
  have f19 : (∀ (X0 X1 X2 X3 X4 X5 X6 X7 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X2 X0 X3)) ∨ ((¬ (old X2 X2 X4)) ∨ ((¬ (old X2 X5 X3)) ∨ ((¬ (old X4 X1 X6)) ∨ ((¬ (old X4 X7 X6)) ∨ ((¬ (old X5 X5 X7)) ∨ (X0 = X5))))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_12
  have f22 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_0
  have f23 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_1
  have f24 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_2
  have f26 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_0
  have f27 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_1
  have f29 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_3
  have f31 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_0
  have f32 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_1
  have f33 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_2
  have f34 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old a a a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_3
  have f35 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b a a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_4
  have f36 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_5
  have f38 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_0
  have f39 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_1
  have f40 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_2
  have f41 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b X2 a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_3
  have f42 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old X2 X2 X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_4
  have f44 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_0
  have f45 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_1
  have f46 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_2
  have f47 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old (sF1 X0 X1 X2) (sF2 X0 X1 X2) a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_3
  have f48 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old X2 X2 (sF2 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_4
  have f50 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_0
  have f51 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_1
  have f52 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_2
  have f57 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_0
  have f58 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_1
  have f59 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_2
  have f60 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_3
  have f61 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old a a (sF6 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_4
  have f65 : (∀ (X0 X1 X2 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using new_imp
  have f66 : (new sk0 sk1 sk2) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_0
  have f67 : (new sk0 sk1 sk3) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_1
  have f68 : (sk2 ≠ sk3) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_2
  have f69 : (a ≠ c) := by
    clear * - f1
    grind (instances := 3000) only
  have f70 : (c ≠ b) := by
    clear * - f2
    grind (instances := 3000) only
  have f71 : (∀ (X0 : G), (¬ (old a b X0))) := by
    clear * - f3
    grind (instances := 3000) only
  have f72 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by
    clear * - f4
    grind (instances := 3000) only
  have f73 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by
    clear * - f5
    grind (instances := 3000) only
  have f74 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by
    clear * - f6
    grind (instances := 3000) only
  have f75 : (∀ (X2 X3 X0 X1 : G), ((¬ (old X0 X1 X3)) ∨ ((¬ (old X0 X1 X2)) ∨ (X2 = X3)))) := by
    clear * - f7
    grind (instances := 3000) only
  have f85 : (∀ (X2 X3 X0 X1 : G), ((¬ (old X3 X3 X3)) ∨ ((¬ (old X1 X0 X2)) ∨ ((¬ (old X1 X1 X1)) ∨ ((¬ (old X1 X3 X2)) ∨ ((¬ (old X0 X0 X0)) ∨ (X0 = X3))))))) := by
    clear * - f17
    grind (instances := 3000) only
  have f87 : (∀ (X2 X3 X0 X1 X6 X7 X4 X5 : G), ((¬ (old X5 X5 X7)) ∨ ((¬ (old X2 X0 X3)) ∨ ((¬ (old X2 X2 X4)) ∨ ((¬ (old X2 X5 X3)) ∨ ((¬ (old X4 X1 X6)) ∨ ((¬ (old X4 X7 X6)) ∨ ((¬ (old X0 X0 X1)) ∨ (X0 = X5))))))))) := by
    clear * - f19
    grind (instances := 3000) only
  have f90 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by
    clear * - f22
    grind (instances := 3000) only
  have f91 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by
    clear * - f23
    grind (instances := 3000) only
  have f92 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by
    clear * - f24
    grind (instances := 3000) only
  have f94 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f26
    grind (instances := 3000) only
  have f95 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f27
    grind (instances := 3000) only
  have f97 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by
    clear * - f29
    grind (instances := 3000) only
  have f99 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f31
    grind (instances := 3000) only
  have f100 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f32
    grind (instances := 3000) only
  have f101 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by
    clear * - f33
    grind (instances := 3000) only
  have f102 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old a a a))) := by
    clear * - f34
    grind (instances := 3000) only
  have f103 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b a a))) := by
    clear * - f35
    grind (instances := 3000) only
  have f104 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f36
    grind (instances := 3000) only
  have f106 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f38
    grind (instances := 3000) only
  have f107 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f39
    grind (instances := 3000) only
  have f108 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f40
    grind (instances := 3000) only
  have f109 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b X2 a))) := by
    clear * - f41
    grind (instances := 3000) only
  have f110 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old X2 X2 X2))) := by
    clear * - f42
    grind (instances := 3000) only
  have f112 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f44
    grind (instances := 3000) only
  have f113 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by
    clear * - f45
    grind (instances := 3000) only
  have f114 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by
    clear * - f46
    grind (instances := 3000) only
  have f115 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old (sF1 X0 X1 X2) (sF2 X0 X1 X2) a))) := by
    clear * - f47
    grind (instances := 3000) only
  have f116 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old X2 X2 (sF2 X0 X1 X2)))) := by
    clear * - f48
    grind (instances := 3000) only
  have f118 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f50
    grind (instances := 3000) only
  have f119 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f51
    grind (instances := 3000) only
  have f120 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by
    clear * - f52
    grind (instances := 3000) only
  have f125 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by
    clear * - f57
    grind (instances := 3000) only
  have f126 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f58
    grind (instances := 3000) only
  have f127 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f59
    grind (instances := 3000) only
  have f128 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f60
    grind (instances := 3000) only
  have f129 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old a a (sF6 X0 X1 X2)))) := by
    clear * - f61
    grind (instances := 3000) only
  have f133 : (∀ (X2 X0 X1 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by
    clear * - f65
    grind (instances := 3000) only
  have f134 : (new sk0 sk1 sk2) := by
    clear * - f66
    grind (instances := 3000) only
  have f135 : (new sk0 sk1 sk3) := by
    clear * - f67
    grind (instances := 3000) only
  have f136 : (sk2 ≠ sk3) := by
    clear * - f68
    grind (instances := 3000) only
  have f153 : ((old sk0 sk1 sk2) ∨ ((sP0 sk0 sk1 sk2) ∨ ((sP1 sk0 sk1 sk2) ∨ ((sP2 sk0 sk1 sk2) ∨ ((sP3 sk0 sk1 sk2) ∨ ((sP4 sk0 sk1 sk2) ∨ ((sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2)))))))) := by
    clear * - f134 f133
    first | exact resolve f134 f133 | exact resolve f133 f134 | grind (instances := 3000) only
  have f154 : ((old sk0 sk1 sk3) ∨ ((sP0 sk0 sk1 sk3) ∨ ((sP1 sk0 sk1 sk3) ∨ ((sP2 sk0 sk1 sk3) ∨ ((sP3 sk0 sk1 sk3) ∨ ((sP4 sk0 sk1 sk3) ∨ ((sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3)))))))) := by
    clear * - f135 f133
    first | exact resolve f135 f133 | exact resolve f133 f135 | grind (instances := 3000) only
  let spl0_1 : Prop := (sP6 sk0 sk1 sk2)
  have f156 : (spl0_1 ↔ (sP6 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_1
  have f157 : ((sP6 sk0 sk1 sk2) ∨ (¬ spl0_1)) := by
    clear * - f156
    grind (instances := 3000) only
  let spl0_2 : Prop := (sP5 sk0 sk1 sk2)
  have f159 : (spl0_2 ↔ (sP5 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_2
  have f160 : ((sP5 sk0 sk1 sk2) ∨ (¬ spl0_2)) := by
    clear * - f159
    grind (instances := 3000) only
  let spl0_3 : Prop := (sP4 sk0 sk1 sk2)
  have f162 : (spl0_3 ↔ (sP4 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_3
  have f163 : ((sP4 sk0 sk1 sk2) ∨ (¬ spl0_3)) := by
    clear * - f162
    grind (instances := 3000) only
  let spl0_4 : Prop := (sP3 sk0 sk1 sk2)
  have f165 : (spl0_4 ↔ (sP3 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_4
  have f166 : ((sP3 sk0 sk1 sk2) ∨ (¬ spl0_4)) := by
    clear * - f165
    grind (instances := 3000) only
  let spl0_5 : Prop := (sP2 sk0 sk1 sk2)
  have f168 : (spl0_5 ↔ (sP2 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_5
  have f169 : ((sP2 sk0 sk1 sk2) ∨ (¬ spl0_5)) := by
    clear * - f168
    grind (instances := 3000) only
  let spl0_6 : Prop := (sP1 sk0 sk1 sk2)
  have f171 : (spl0_6 ↔ (sP1 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_6
  have f172 : ((sP1 sk0 sk1 sk2) ∨ (¬ spl0_6)) := by
    clear * - f171
    grind (instances := 3000) only
  let spl0_7 : Prop := (sP0 sk0 sk1 sk2)
  have f174 : (spl0_7 ↔ (sP0 sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_7
  have f175 : ((sP0 sk0 sk1 sk2) ∨ (¬ spl0_7)) := by
    clear * - f174
    grind (instances := 3000) only
  let spl0_8 : Prop := (old sk0 sk1 sk2)
  have f177 : (spl0_8 ↔ (old sk0 sk1 sk2)) := Iff.rfl
  clear_value spl0_8
  have f178 : ((old sk0 sk1 sk2) ∨ (¬ spl0_8)) := by
    clear * - f177
    grind (instances := 3000) only
  have f179 : (spl0_1 ∨ (spl0_2 ∨ (spl0_3 ∨ (spl0_4 ∨ (spl0_5 ∨ (spl0_6 ∨ (spl0_7 ∨ spl0_8))))))) := by
    clear * - f153 f177 f174 f171 f168 f165 f162 f159 f156
    grind (instances := 3000) only
  have f180 : ((a = b) ∨ (¬ spl0_1)) := by
    clear * - f157 f125
    first | exact resolve f157 f125 | exact resolve f125 f157 | grind (instances := 3000) only
  have f181 : ((c = sk0) ∨ (¬ spl0_1)) := by
    clear * - f157 f126
    first | exact resolve f157 f126 | exact resolve f126 f157 | grind (instances := 3000) only
  have f182 : ((c = sk1) ∨ (¬ spl0_1)) := by
    clear * - f157 f127
    first | exact resolve f157 f127 | exact resolve f127 f157 | grind (instances := 3000) only
  have f183 : ((b = sk2) ∨ (¬ spl0_1)) := by
    clear * - f157 f128
    first | exact resolve f157 f128 | exact resolve f128 f157 | grind (instances := 3000) only
  have f191 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_1))) := by
    clear * - f71 f180
    first | exact superpose f71 f180 | exact superpose f180 f71 | grind (instances := 3000) only
  have f193 : ((sP6 c sk1 sk2) ∨ (¬ spl0_1)) := by
    clear * - f157 f181
    first | exact superpose f157 f181 | exact superpose f181 f157 | grind (instances := 3000) only
  have f198 : ((sP6 c sk1 b) ∨ (¬ spl0_1)) := by
    clear * - f193 f183
    grind (instances := 3000) only
  have f200 : ((sP6 c c b) ∨ (¬ spl0_1)) := by
    clear * - f198 f182
    grind (instances := 3000) only
  have f224 : ((old a a (sF6 c c b)) ∨ (¬ spl0_1)) := by
    clear * - f200 f129
    first | exact resolve f200 f129 | exact resolve f129 f200 | grind (instances := 3000) only
  have f230 : ((old b b (sF6 c c b)) ∨ (¬ spl0_1)) := by
    clear * - f224 f180
    grind (instances := 3000) only
  have f231 : (False ∨ (¬ spl0_1)) := by
    clear * - f230 f191
    first | exact resolve f230 f191 | exact resolve f191 f230 | grind (instances := 3000) only
  have f232 : (¬ spl0_1) := by
    clear * - f231
    grind (instances := 3000) only
  have f236 : ((old (sF3 sk0 sk1 sk2) a sk0) ∨ (¬ spl0_2)) := by
    clear * - f160 f120
    first | exact resolve f160 f120 | exact resolve f120 f160 | grind (instances := 3000) only
  have f237 : ((b = sk2) ∨ (¬ spl0_2)) := by
    clear * - f160 f119
    first | exact resolve f160 f119 | exact resolve f119 f160 | grind (instances := 3000) only
  have f238 : ((c = sk1) ∨ (¬ spl0_2)) := by
    clear * - f160 f118
    first | exact resolve f160 f118 | exact resolve f118 f160 | grind (instances := 3000) only
  have f239 : ((old (sF3 sk0 sk1 b) a sk0) ∨ (¬ spl0_2)) := by
    clear * - f236 f237
    grind (instances := 3000) only
  have f243 : ((old (sF3 sk0 c b) a sk0) ∨ (¬ spl0_2)) := by
    clear * - f239 f238
    grind (instances := 3000) only
  have f252 : ((new sk0 c sk3) ∨ (¬ spl0_2)) := by
    clear * - f135 f238
    first | exact superpose f135 f238 | exact superpose f238 f135 | grind (instances := 3000) only
  have f263 : ((old sk0 c sk3) ∨ ((sP0 sk0 c sk3) ∨ ((sP1 sk0 c sk3) ∨ ((sP2 sk0 c sk3) ∨ ((sP3 sk0 c sk3) ∨ ((sP4 sk0 c sk3) ∨ ((sP5 sk0 c sk3) ∨ ((sP6 sk0 c sk3) ∨ (¬ spl0_2))))))))) := by
    clear * - f252 f133
    first | exact resolve f252 f133 | exact resolve f133 f252 | grind (instances := 3000) only
  have f264 : ((sP0 sk0 c sk3) ∨ ((sP1 sk0 c sk3) ∨ ((sP2 sk0 c sk3) ∨ ((sP3 sk0 c sk3) ∨ ((sP4 sk0 c sk3) ∨ ((sP5 sk0 c sk3) ∨ ((sP6 sk0 c sk3) ∨ (¬ spl0_2)))))))) := by
    clear * - f263 f73
    first | exact resolve f263 f73 | exact resolve f73 f263 | grind (instances := 3000) only
  let spl0_11 : Prop := (sP6 sk0 c sk3)
  have f313 : (spl0_11 ↔ (sP6 sk0 c sk3)) := Iff.rfl
  clear_value spl0_11
  have f314 : ((sP6 sk0 c sk3) ∨ (¬ spl0_11)) := by
    clear * - f313
    grind (instances := 3000) only
  let spl0_12 : Prop := (sP5 sk0 c sk3)
  have f316 : (spl0_12 ↔ (sP5 sk0 c sk3)) := Iff.rfl
  clear_value spl0_12
  have f317 : ((sP5 sk0 c sk3) ∨ (¬ spl0_12)) := by
    clear * - f316
    grind (instances := 3000) only
  let spl0_13 : Prop := (sP4 sk0 c sk3)
  have f319 : (spl0_13 ↔ (sP4 sk0 c sk3)) := Iff.rfl
  clear_value spl0_13
  have f320 : ((sP4 sk0 c sk3) ∨ (¬ spl0_13)) := by
    clear * - f319
    grind (instances := 3000) only
  let spl0_14 : Prop := (sP3 sk0 c sk3)
  have f322 : (spl0_14 ↔ (sP3 sk0 c sk3)) := Iff.rfl
  clear_value spl0_14
  have f323 : ((sP3 sk0 c sk3) ∨ (¬ spl0_14)) := by
    clear * - f322
    grind (instances := 3000) only
  let spl0_15 : Prop := (sP2 sk0 c sk3)
  have f325 : (spl0_15 ↔ (sP2 sk0 c sk3)) := Iff.rfl
  clear_value spl0_15
  have f326 : ((sP2 sk0 c sk3) ∨ (¬ spl0_15)) := by
    clear * - f325
    grind (instances := 3000) only
  let spl0_16 : Prop := (sP1 sk0 c sk3)
  have f328 : (spl0_16 ↔ (sP1 sk0 c sk3)) := Iff.rfl
  clear_value spl0_16
  have f329 : ((sP1 sk0 c sk3) ∨ (¬ spl0_16)) := by
    clear * - f328
    grind (instances := 3000) only
  let spl0_17 : Prop := (sP0 sk0 c sk3)
  have f331 : (spl0_17 ↔ (sP0 sk0 c sk3)) := Iff.rfl
  clear_value spl0_17
  have f332 : ((sP0 sk0 c sk3) ∨ (¬ spl0_17)) := by
    clear * - f331
    grind (instances := 3000) only
  have f333 : (spl0_11 ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ (spl0_16 ∨ (spl0_17 ∨ (¬ spl0_2)))))))) := by
    clear * - f264 f159 f331 f328 f325 f322 f319 f316 f313
    grind (instances := 3000) only
  have f334 : ((a = b) ∨ (¬ spl0_11)) := by
    clear * - f314 f125
    first | exact resolve f314 f125 | exact resolve f125 f314 | grind (instances := 3000) only
  have f335 : ((c = sk0) ∨ (¬ spl0_11)) := by
    clear * - f314 f126
    first | exact resolve f314 f126 | exact resolve f126 f314 | grind (instances := 3000) only
  have f346 : ((old (sF3 sk0 c b) b sk0) ∨ ((¬ spl0_2) ∨ (¬ spl0_11))) := by
    clear * - f243 f334
    first | exact superpose f243 f334 | exact superpose f334 f243 | grind (instances := 3000) only
  have f368 : ((old (sF3 c c b) b c) ∨ ((¬ spl0_2) ∨ (¬ spl0_11))) := by
    clear * - f346 f335
    grind (instances := 3000) only
  have f377 : (False ∨ ((¬ spl0_2) ∨ (¬ spl0_11))) := by
    clear * - f368 f72
    first | exact resolve f368 f72 | exact resolve f72 f368 | grind (instances := 3000) only
  have f378 : ((¬ spl0_2) ∨ (¬ spl0_11)) := by
    clear * - f377
    grind (instances := 3000) only
  have f380 : ((c = b) ∨ (¬ spl0_17)) := by
    clear * - f332 f91
    first | exact resolve f332 f91 | exact resolve f91 f332 | grind (instances := 3000) only
  have f382 : (False ∨ (¬ spl0_17)) := by
    clear * - f380 f70
    first | exact resolve f380 f70 | exact resolve f70 f380 | grind (instances := 3000) only
  have f383 : (¬ spl0_17) := by
    clear * - f382
    grind (instances := 3000) only
  have f388 : ((b = sk3) ∨ (¬ spl0_12)) := by
    clear * - f317 f119
    first | exact resolve f317 f119 | exact resolve f119 f317 | grind (instances := 3000) only
  have f397 : ((b ≠ sk2) ∨ (¬ spl0_12)) := by
    clear * - f136 f388
    first | exact superpose f136 f388 | exact superpose f388 f136 | grind (instances := 3000) only
  have f398 : (False ∨ ((¬ spl0_2) ∨ (¬ spl0_12))) := by
    clear * - f397 f237
    first | exact resolve f397 f237 | exact resolve f237 f397 | grind (instances := 3000) only
  have f399 : ((¬ spl0_2) ∨ (¬ spl0_12)) := by
    clear * - f398
    grind (instances := 3000) only
  have f403 : ((b = sk3) ∨ (¬ spl0_16)) := by
    clear * - f329 f95
    first | exact resolve f329 f95 | exact resolve f95 f329 | grind (instances := 3000) only
  have f410 : ((b ≠ sk2) ∨ (¬ spl0_16)) := by
    clear * - f136 f403
    first | exact superpose f136 f403 | exact superpose f403 f136 | grind (instances := 3000) only
  have f411 : (False ∨ ((¬ spl0_2) ∨ (¬ spl0_16))) := by
    clear * - f410 f237
    first | exact resolve f410 f237 | exact resolve f237 f410 | grind (instances := 3000) only
  have f412 : ((¬ spl0_2) ∨ (¬ spl0_16)) := by
    clear * - f411
    grind (instances := 3000) only
  have f416 : ((old b sk3 c) ∨ (¬ spl0_13)) := by
    clear * - f320 f114
    first | exact resolve f320 f114 | exact resolve f114 f320 | grind (instances := 3000) only
  have f420 : (False ∨ (¬ spl0_13)) := by
    clear * - f416 f72
    first | exact resolve f416 f72 | exact resolve f72 f416 | grind (instances := 3000) only
  have f421 : (¬ spl0_13) := by
    clear * - f420
    grind (instances := 3000) only
  have f427 : ((a = c) ∨ (¬ spl0_14)) := by
    clear * - f323 f107
    first | exact resolve f323 f107 | exact resolve f107 f323 | grind (instances := 3000) only
  have f429 : (False ∨ (¬ spl0_14)) := by
    clear * - f427 f69
    first | exact resolve f427 f69 | exact resolve f69 f427 | grind (instances := 3000) only
  have f430 : (¬ spl0_14) := by
    clear * - f429
    grind (instances := 3000) only
  have f435 : ((a = c) ∨ (¬ spl0_15)) := by
    clear * - f326 f100
    first | exact resolve f326 f100 | exact resolve f100 f326 | grind (instances := 3000) only
  have f437 : (False ∨ (¬ spl0_15)) := by
    clear * - f435 f69
    first | exact resolve f435 f69 | exact resolve f69 f435 | grind (instances := 3000) only
  have f438 : (¬ spl0_15) := by
    clear * - f437
    grind (instances := 3000) only
  have f440 : (∀ (X0 : G), (((¬ (old sk0 sk1 X0)) ∨ (sk2 = X0)) ∨ (¬ spl0_8))) := by
    clear * - f178 f75
    first | exact resolve f178 f75 | exact resolve f75 f178 | grind (instances := 3000) only
  let spl0_18 : Prop := (sP6 sk0 sk1 sk3)
  have f443 : (spl0_18 ↔ (sP6 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_18
  have f444 : ((sP6 sk0 sk1 sk3) ∨ (¬ spl0_18)) := by
    clear * - f443
    grind (instances := 3000) only
  let spl0_19 : Prop := (sP5 sk0 sk1 sk3)
  have f446 : (spl0_19 ↔ (sP5 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_19
  have f447 : ((sP5 sk0 sk1 sk3) ∨ (¬ spl0_19)) := by
    clear * - f446
    grind (instances := 3000) only
  let spl0_20 : Prop := (sP4 sk0 sk1 sk3)
  have f449 : (spl0_20 ↔ (sP4 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_20
  have f450 : ((sP4 sk0 sk1 sk3) ∨ (¬ spl0_20)) := by
    clear * - f449
    grind (instances := 3000) only
  let spl0_21 : Prop := (sP3 sk0 sk1 sk3)
  have f452 : (spl0_21 ↔ (sP3 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_21
  have f453 : ((sP3 sk0 sk1 sk3) ∨ (¬ spl0_21)) := by
    clear * - f452
    grind (instances := 3000) only
  let spl0_22 : Prop := (sP2 sk0 sk1 sk3)
  have f455 : (spl0_22 ↔ (sP2 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_22
  have f456 : ((sP2 sk0 sk1 sk3) ∨ (¬ spl0_22)) := by
    clear * - f455
    grind (instances := 3000) only
  let spl0_23 : Prop := (sP1 sk0 sk1 sk3)
  have f458 : (spl0_23 ↔ (sP1 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_23
  have f459 : ((sP1 sk0 sk1 sk3) ∨ (¬ spl0_23)) := by
    clear * - f458
    grind (instances := 3000) only
  let spl0_24 : Prop := (sP0 sk0 sk1 sk3)
  have f461 : (spl0_24 ↔ (sP0 sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_24
  have f462 : ((sP0 sk0 sk1 sk3) ∨ (¬ spl0_24)) := by
    clear * - f461
    grind (instances := 3000) only
  let spl0_25 : Prop := (old sk0 sk1 sk3)
  have f464 : (spl0_25 ↔ (old sk0 sk1 sk3)) := Iff.rfl
  clear_value spl0_25
  have f465 : ((old sk0 sk1 sk3) ∨ (¬ spl0_25)) := by
    clear * - f464
    grind (instances := 3000) only
  have f466 : (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (spl0_21 ∨ (spl0_22 ∨ (spl0_23 ∨ (spl0_24 ∨ spl0_25))))))) := by
    clear * - f154 f464 f461 f458 f455 f452 f449 f446 f443
    grind (instances := 3000) only
  have f467 : ((sk2 = sk3) ∨ ((¬ spl0_8) ∨ (¬ spl0_25))) := by
    clear * - f465 f440
    first | exact resolve f465 f440 | exact resolve f440 f465 | grind (instances := 3000) only
  have f470 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_25))) := by
    clear * - f467 f136
    first | exact resolve f467 f136 | exact resolve f136 f467 | grind (instances := 3000) only
  have f471 : ((¬ spl0_8) ∨ (¬ spl0_25)) := by
    clear * - f470
    grind (instances := 3000) only
  have f472 : ((c = sk3) ∨ (¬ spl0_24)) := by
    clear * - f462 f92
    first | exact resolve f462 f92 | exact resolve f92 f462 | grind (instances := 3000) only
  have f473 : ((b = sk1) ∨ (¬ spl0_24)) := by
    clear * - f462 f91
    first | exact resolve f462 f91 | exact resolve f91 f462 | grind (instances := 3000) only
  have f474 : ((a = sk0) ∨ (¬ spl0_24)) := by
    clear * - f462 f90
    first | exact resolve f462 f90 | exact resolve f90 f462 | grind (instances := 3000) only
  have f477 : ((c ≠ sk2) ∨ (¬ spl0_24)) := by
    clear * - f136 f472
    first | exact superpose f136 f472 | exact superpose f472 f136 | grind (instances := 3000) only
  have f484 : ((old sk0 b sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_24))) := by
    clear * - f178 f473
    first | exact superpose f178 f473 | exact superpose f473 f178 | grind (instances := 3000) only
  have f491 : ((old a b sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_24))) := by
    clear * - f484 f474
    grind (instances := 3000) only
  have f495 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_24))) := by
    clear * - f491 f71
    first | exact resolve f491 f71 | exact resolve f71 f491 | grind (instances := 3000) only
  have f496 : ((¬ spl0_8) ∨ (¬ spl0_24)) := by
    clear * - f495
    grind (instances := 3000) only
  have f500 : ((b = sk3) ∨ (¬ spl0_23)) := by
    clear * - f459 f95
    first | exact resolve f459 f95 | exact resolve f95 f459 | grind (instances := 3000) only
  have f501 : ((c = sk1) ∨ (¬ spl0_23)) := by
    clear * - f459 f94
    first | exact resolve f459 f94 | exact resolve f94 f459 | grind (instances := 3000) only
  have f508 : ((b ≠ sk2) ∨ (¬ spl0_23)) := by
    clear * - f136 f500
    first | exact superpose f136 f500 | exact superpose f500 f136 | grind (instances := 3000) only
  have f513 : ((old sk0 c sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_23))) := by
    clear * - f178 f501
    first | exact superpose f178 f501 | exact superpose f501 f178 | grind (instances := 3000) only
  have f518 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_23))) := by
    clear * - f513 f73
    first | exact resolve f513 f73 | exact resolve f73 f513 | grind (instances := 3000) only
  have f519 : ((¬ spl0_8) ∨ (¬ spl0_23)) := by
    clear * - f518
    grind (instances := 3000) only
  have f521 : ((old b b b) ∨ (¬ spl0_22)) := by
    clear * - f456 f104
    first | exact resolve f456 f104 | exact resolve f104 f456 | grind (instances := 3000) only
  have f522 : ((old b a a) ∨ (¬ spl0_22)) := by
    clear * - f456 f103
    first | exact resolve f456 f103 | exact resolve f103 f456 | grind (instances := 3000) only
  have f523 : ((old a a a) ∨ (¬ spl0_22)) := by
    clear * - f456 f102
    first | exact resolve f456 f102 | exact resolve f102 f456 | grind (instances := 3000) only
  have f524 : ((a = sk3) ∨ (¬ spl0_22)) := by
    clear * - f456 f101
    first | exact resolve f456 f101 | exact resolve f101 f456 | grind (instances := 3000) only
  have f525 : ((a = sk1) ∨ (¬ spl0_22)) := by
    clear * - f456 f100
    first | exact resolve f456 f100 | exact resolve f100 f456 | grind (instances := 3000) only
  have f526 : ((c = sk0) ∨ (¬ spl0_22)) := by
    clear * - f456 f99
    first | exact resolve f456 f99 | exact resolve f99 f456 | grind (instances := 3000) only
  have f529 : ((a ≠ sk2) ∨ (¬ spl0_22)) := by
    clear * - f136 f524
    first | exact superpose f136 f524 | exact superpose f524 f136 | grind (instances := 3000) only
  have f536 : ((old sk0 a sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_22))) := by
    clear * - f178 f525
    first | exact superpose f178 f525 | exact superpose f525 f178 | grind (instances := 3000) only
  have f543 : ((old c a sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_22))) := by
    clear * - f536 f526
    grind (instances := 3000) only
  have f547 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_22))) := by
    clear * - f543 f74
    first | exact resolve f543 f74 | exact resolve f74 f543 | grind (instances := 3000) only
  have f548 : ((¬ spl0_8) ∨ (¬ spl0_22)) := by
    clear * - f547
    grind (instances := 3000) only
  have f550 : ((old sk3 sk3 sk3) ∨ (¬ spl0_21)) := by
    clear * - f453 f110
    first | exact resolve f453 f110 | exact resolve f110 f453 | grind (instances := 3000) only
  have f551 : ((old b sk3 a) ∨ (¬ spl0_21)) := by
    clear * - f453 f109
    first | exact resolve f453 f109 | exact resolve f109 f453 | grind (instances := 3000) only
  have f552 : ((old b b b) ∨ (¬ spl0_21)) := by
    clear * - f453 f108
    first | exact resolve f453 f108 | exact resolve f108 f453 | grind (instances := 3000) only
  have f553 : ((a = sk1) ∨ (¬ spl0_21)) := by
    clear * - f453 f107
    first | exact resolve f453 f107 | exact resolve f107 f453 | grind (instances := 3000) only
  have f554 : ((c = sk0) ∨ (¬ spl0_21)) := by
    clear * - f453 f106
    first | exact resolve f453 f106 | exact resolve f106 f453 | grind (instances := 3000) only
  have f557 : ((old sk0 a sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_21))) := by
    clear * - f178 f553
    first | exact superpose f178 f553 | exact superpose f553 f178 | grind (instances := 3000) only
  have f564 : ((old c a sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_21))) := by
    clear * - f557 f554
    grind (instances := 3000) only
  have f567 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_21))) := by
    clear * - f564 f74
    first | exact resolve f564 f74 | exact resolve f74 f564 | grind (instances := 3000) only
  have f568 : ((¬ spl0_8) ∨ (¬ spl0_21)) := by
    clear * - f567
    grind (instances := 3000) only
  have f571 : ((old b sk3 sk1) ∨ (¬ spl0_20)) := by
    clear * - f450 f114
    first | exact resolve f450 f114 | exact resolve f114 f450 | grind (instances := 3000) only
  have f573 : ((c = sk0) ∨ (¬ spl0_20)) := by
    clear * - f450 f112
    first | exact resolve f450 f112 | exact resolve f112 f450 | grind (instances := 3000) only
  have f579 : ((old c sk1 sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_20))) := by
    clear * - f178 f573
    first | exact superpose f178 f573 | exact superpose f573 f178 | grind (instances := 3000) only
  have f581 : ((sP4 c sk1 sk3) ∨ (¬ spl0_20)) := by
    clear * - f450 f573
    first | exact superpose f450 f573 | exact superpose f573 f450 | grind (instances := 3000) only
  have f582 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_20))) := by
    clear * - f579 f74
    first | exact resolve f579 f74 | exact resolve f74 f579 | grind (instances := 3000) only
  have f583 : ((¬ spl0_8) ∨ (¬ spl0_20)) := by
    clear * - f582
    grind (instances := 3000) only
  have f588 : ((b = sk3) ∨ (¬ spl0_19)) := by
    clear * - f447 f119
    first | exact resolve f447 f119 | exact resolve f119 f447 | grind (instances := 3000) only
  have f589 : ((c = sk1) ∨ (¬ spl0_19)) := by
    clear * - f447 f118
    first | exact resolve f447 f118 | exact resolve f118 f447 | grind (instances := 3000) only
  have f600 : ((b ≠ sk2) ∨ (¬ spl0_19)) := by
    clear * - f136 f588
    first | exact superpose f136 f588 | exact superpose f588 f136 | grind (instances := 3000) only
  have f605 : ((old sk0 c sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_19))) := by
    clear * - f178 f589
    first | exact superpose f178 f589 | exact superpose f589 f178 | grind (instances := 3000) only
  have f610 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_19))) := by
    clear * - f605 f73
    first | exact resolve f605 f73 | exact resolve f73 f605 | grind (instances := 3000) only
  have f611 : ((¬ spl0_8) ∨ (¬ spl0_19)) := by
    clear * - f610
    grind (instances := 3000) only
  have f613 : ((a = b) ∨ (¬ spl0_18)) := by
    clear * - f444 f125
    first | exact resolve f444 f125 | exact resolve f125 f444 | grind (instances := 3000) only
  have f614 : ((c = sk0) ∨ (¬ spl0_18)) := by
    clear * - f444 f126
    first | exact resolve f444 f126 | exact resolve f126 f444 | grind (instances := 3000) only
  have f615 : ((c = sk1) ∨ (¬ spl0_18)) := by
    clear * - f444 f127
    first | exact resolve f444 f127 | exact resolve f127 f444 | grind (instances := 3000) only
  have f620 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_18))) := by
    clear * - f71 f613
    first | exact superpose f71 f613 | exact superpose f613 f71 | grind (instances := 3000) only
  have f628 : ((old c sk1 sk2) ∨ ((¬ spl0_8) ∨ (¬ spl0_18))) := by
    clear * - f178 f614
    first | exact superpose f178 f614 | exact superpose f614 f178 | grind (instances := 3000) only
  have f632 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_18))) := by
    clear * - f628 f74
    first | exact resolve f628 f74 | exact resolve f74 f628 | grind (instances := 3000) only
  have f633 : ((¬ spl0_8) ∨ (¬ spl0_18)) := by
    clear * - f632
    grind (instances := 3000) only
  have f638 : ((sP4 sk0 c sk2) ∨ ((¬ spl0_3) ∨ (¬ spl0_18))) := by
    clear * - f163 f615
    grind (instances := 3000) only
  have f639 : ((sP4 c c sk2) ∨ ((¬ spl0_3) ∨ (¬ spl0_18))) := by
    clear * - f638 f614
    grind (instances := 3000) only
  have f657 : ((old b sk2 c) ∨ ((¬ spl0_3) ∨ (¬ spl0_18))) := by
    clear * - f639 f114
    first | exact resolve f639 f114 | exact resolve f114 f639 | grind (instances := 3000) only
  have f662 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_18))) := by
    clear * - f657 f72
    first | exact resolve f657 f72 | exact resolve f72 f657 | grind (instances := 3000) only
  have f663 : ((¬ spl0_3) ∨ (¬ spl0_18)) := by
    clear * - f662
    grind (instances := 3000) only
  have f665 : ((sP3 sk0 c sk2) ∨ ((¬ spl0_4) ∨ (¬ spl0_18))) := by
    clear * - f166 f615
    grind (instances := 3000) only
  have f666 : ((sP3 c c sk2) ∨ ((¬ spl0_4) ∨ (¬ spl0_18))) := by
    clear * - f665 f614
    grind (instances := 3000) only
  have f669 : ((old b b b) ∨ ((¬ spl0_4) ∨ (¬ spl0_18))) := by
    clear * - f666 f108
    first | exact resolve f666 f108 | exact resolve f108 f666 | grind (instances := 3000) only
  have f674 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_18))) := by
    clear * - f669 f620
    first | exact resolve f669 f620 | exact resolve f620 f669 | grind (instances := 3000) only
  have f675 : ((¬ spl0_4) ∨ (¬ spl0_18)) := by
    clear * - f674
    grind (instances := 3000) only
  have f677 : ((sP2 sk0 c sk2) ∨ ((¬ spl0_5) ∨ (¬ spl0_18))) := by
    clear * - f169 f615
    grind (instances := 3000) only
  have f678 : ((sP2 c c sk2) ∨ ((¬ spl0_5) ∨ (¬ spl0_18))) := by
    clear * - f677 f614
    grind (instances := 3000) only
  have f680 : ((old b a a) ∨ ((¬ spl0_5) ∨ (¬ spl0_18))) := by
    clear * - f678 f103
    first | exact resolve f678 f103 | exact resolve f103 f678 | grind (instances := 3000) only
  have f689 : ((old b b b) ∨ ((¬ spl0_5) ∨ (¬ spl0_18))) := by
    clear * - f680 f613
    grind (instances := 3000) only
  have f696 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_18))) := by
    clear * - f689 f620
    first | exact resolve f689 f620 | exact resolve f620 f689 | grind (instances := 3000) only
  have f697 : ((¬ spl0_5) ∨ (¬ spl0_18)) := by
    clear * - f696
    grind (instances := 3000) only
  have f698 : ((sP1 sk0 c sk2) ∨ ((¬ spl0_6) ∨ (¬ spl0_18))) := by
    clear * - f172 f615
    grind (instances := 3000) only
  have f699 : ((sP1 c c sk2) ∨ ((¬ spl0_6) ∨ (¬ spl0_18))) := by
    clear * - f698 f614
    grind (instances := 3000) only
  have f700 : ((old (sF0 c c sk2) c a) ∨ ((¬ spl0_6) ∨ (¬ spl0_18))) := by
    clear * - f699 f97
    first | exact resolve f699 f97 | exact resolve f97 f699 | grind (instances := 3000) only
  have f708 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_18))) := by
    clear * - f700 f73
    first | exact resolve f700 f73 | exact resolve f73 f700 | grind (instances := 3000) only
  have f709 : ((¬ spl0_6) ∨ (¬ spl0_18)) := by
    clear * - f708
    grind (instances := 3000) only
  have f710 : ((sP0 sk0 c sk2) ∨ ((¬ spl0_7) ∨ (¬ spl0_18))) := by
    clear * - f175 f615
    grind (instances := 3000) only
  have f711 : ((sP0 c c sk2) ∨ ((¬ spl0_7) ∨ (¬ spl0_18))) := by
    clear * - f710 f614
    grind (instances := 3000) only
  have f713 : ((c = b) ∨ ((¬ spl0_7) ∨ (¬ spl0_18))) := by
    clear * - f711 f91
    first | exact resolve f711 f91 | exact resolve f91 f711 | grind (instances := 3000) only
  have f717 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_18))) := by
    clear * - f713 f70
    first | exact resolve f713 f70 | exact resolve f70 f713 | grind (instances := 3000) only
  have f718 : ((¬ spl0_7) ∨ (¬ spl0_18)) := by
    clear * - f717
    grind (instances := 3000) only
  have f719 : ((sP0 sk0 c sk2) ∨ ((¬ spl0_7) ∨ (¬ spl0_19))) := by
    clear * - f175 f589
    grind (instances := 3000) only
  have f745 : ((c = b) ∨ ((¬ spl0_7) ∨ (¬ spl0_19))) := by
    clear * - f719 f91
    first | exact resolve f719 f91 | exact resolve f91 f719 | grind (instances := 3000) only
  have f747 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_19))) := by
    clear * - f745 f70
    first | exact resolve f745 f70 | exact resolve f70 f745 | grind (instances := 3000) only
  have f748 : ((¬ spl0_7) ∨ (¬ spl0_19)) := by
    clear * - f747
    grind (instances := 3000) only
  have f749 : ((c = sk2) ∨ (¬ spl0_7)) := by
    clear * - f175 f92
    first | exact resolve f175 f92 | exact resolve f92 f175 | grind (instances := 3000) only
  have f750 : ((b = sk1) ∨ (¬ spl0_7)) := by
    clear * - f175 f91
    first | exact resolve f175 f91 | exact resolve f91 f175 | grind (instances := 3000) only
  have f751 : ((a = sk0) ∨ (¬ spl0_7)) := by
    clear * - f175 f90
    first | exact resolve f175 f90 | exact resolve f90 f175 | grind (instances := 3000) only
  have f776 : ((old a sk1 sk3) ∨ ((¬ spl0_7) ∨ (¬ spl0_25))) := by
    clear * - f465 f751
    first | exact superpose f465 f751 | exact superpose f751 f465 | grind (instances := 3000) only
  have f779 : ((old a b sk3) ∨ ((¬ spl0_7) ∨ (¬ spl0_25))) := by
    clear * - f776 f750
    grind (instances := 3000) only
  have f784 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_25))) := by
    clear * - f779 f71
    first | exact resolve f779 f71 | exact resolve f71 f779 | grind (instances := 3000) only
  have f785 : ((¬ spl0_7) ∨ (¬ spl0_25)) := by
    clear * - f784
    grind (instances := 3000) only
  have f791 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_24))) := by
    clear * - f477 f749
    first | exact resolve f477 f749 | exact resolve f749 f477 | grind (instances := 3000) only
  have f792 : ((¬ spl0_7) ∨ (¬ spl0_24)) := by
    clear * - f791
    grind (instances := 3000) only
  have f798 : ((c = b) ∨ ((¬ spl0_7) ∨ (¬ spl0_23))) := by
    clear * - f501 f750
    grind (instances := 3000) only
  have f803 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_23))) := by
    clear * - f798 f70
    first | exact resolve f798 f70 | exact resolve f70 f798 | grind (instances := 3000) only
  have f804 : ((¬ spl0_7) ∨ (¬ spl0_23)) := by
    clear * - f803
    grind (instances := 3000) only
  have f808 : ((a = c) ∨ ((¬ spl0_7) ∨ (¬ spl0_22))) := by
    clear * - f526 f751
    grind (instances := 3000) only
  have f812 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_22))) := by
    clear * - f808 f69
    first | exact resolve f808 f69 | exact resolve f69 f808 | grind (instances := 3000) only
  have f813 : ((¬ spl0_7) ∨ (¬ spl0_22)) := by
    clear * - f812
    grind (instances := 3000) only
  have f820 : ((a = c) ∨ ((¬ spl0_7) ∨ (¬ spl0_21))) := by
    clear * - f554 f751
    grind (instances := 3000) only
  have f823 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_21))) := by
    clear * - f820 f69
    first | exact resolve f820 f69 | exact resolve f69 f820 | grind (instances := 3000) only
  have f824 : ((¬ spl0_7) ∨ (¬ spl0_21)) := by
    clear * - f823
    grind (instances := 3000) only
  have f831 : ((a = c) ∨ ((¬ spl0_7) ∨ (¬ spl0_20))) := by
    clear * - f573 f751
    grind (instances := 3000) only
  have f835 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_20))) := by
    clear * - f831 f69
    first | exact resolve f831 f69 | exact resolve f69 f831 | grind (instances := 3000) only
  have f836 : ((¬ spl0_7) ∨ (¬ spl0_20)) := by
    clear * - f835
    grind (instances := 3000) only
  have f839 : ((b = sk2) ∨ (¬ spl0_6)) := by
    clear * - f172 f95
    first | exact resolve f172 f95 | exact resolve f95 f172 | grind (instances := 3000) only
  have f840 : ((c = sk1) ∨ (¬ spl0_6)) := by
    clear * - f172 f94
    first | exact resolve f172 f94 | exact resolve f94 f172 | grind (instances := 3000) only
  have f856 : ((old sk0 c sk3) ∨ ((¬ spl0_6) ∨ (¬ spl0_25))) := by
    clear * - f465 f840
    first | exact superpose f465 f840 | exact superpose f840 f465 | grind (instances := 3000) only
  have f857 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_25))) := by
    clear * - f856 f73
    first | exact resolve f856 f73 | exact resolve f73 f856 | grind (instances := 3000) only
  have f858 : ((¬ spl0_6) ∨ (¬ spl0_25)) := by
    clear * - f857
    grind (instances := 3000) only
  have f871 : ((c = b) ∨ ((¬ spl0_6) ∨ (¬ spl0_24))) := by
    clear * - f473 f840
    first | exact superpose f473 f840 | exact superpose f840 f473 | grind (instances := 3000) only
  have f881 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_24))) := by
    clear * - f871 f70
    first | exact resolve f871 f70 | exact resolve f70 f871 | grind (instances := 3000) only
  have f882 : ((¬ spl0_6) ∨ (¬ spl0_24)) := by
    clear * - f881
    grind (instances := 3000) only
  have f888 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_23))) := by
    clear * - f508 f839
    first | exact resolve f508 f839 | exact resolve f839 f508 | grind (instances := 3000) only
  have f889 : ((¬ spl0_6) ∨ (¬ spl0_23)) := by
    clear * - f888
    grind (instances := 3000) only
  have f897 : ((a ≠ sk2) ∨ (¬ spl0_22)) := by
    clear * - f136 f524
    first | exact superpose f136 f524 | exact superpose f524 f136 | grind (instances := 3000) only
  have f901 : ((a = c) ∨ ((¬ spl0_6) ∨ (¬ spl0_22))) := by
    clear * - f525 f840
    first | exact superpose f525 f840 | exact superpose f840 f525 | grind (instances := 3000) only
  have f911 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_22))) := by
    clear * - f901 f69
    first | exact resolve f901 f69 | exact resolve f69 f901 | grind (instances := 3000) only
  have f912 : ((¬ spl0_6) ∨ (¬ spl0_22)) := by
    clear * - f911
    grind (instances := 3000) only
  have f919 : ((a = c) ∨ ((¬ spl0_6) ∨ (¬ spl0_21))) := by
    clear * - f553 f840
    first | exact superpose f553 f840 | exact superpose f840 f553 | grind (instances := 3000) only
  have f929 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_21))) := by
    clear * - f919 f69
    first | exact resolve f919 f69 | exact resolve f69 f919 | grind (instances := 3000) only
  have f930 : ((¬ spl0_6) ∨ (¬ spl0_21)) := by
    clear * - f929
    grind (instances := 3000) only
  have f935 : ((old b sk3 c) ∨ ((¬ spl0_6) ∨ (¬ spl0_20))) := by
    clear * - f571 f840
    grind (instances := 3000) only
  have f939 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_20))) := by
    clear * - f935 f72
    first | exact resolve f935 f72 | exact resolve f72 f935 | grind (instances := 3000) only
  have f940 : ((¬ spl0_6) ∨ (¬ spl0_20)) := by
    clear * - f939
    grind (instances := 3000) only
  have f944 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_19))) := by
    clear * - f600 f839
    first | exact resolve f600 f839 | exact resolve f839 f600 | grind (instances := 3000) only
  have f945 : ((¬ spl0_6) ∨ (¬ spl0_19)) := by
    clear * - f944
    grind (instances := 3000) only
  have f947 : ((old b b b) ∨ (¬ spl0_5)) := by
    clear * - f169 f104
    first | exact resolve f169 f104 | exact resolve f104 f169 | grind (instances := 3000) only
  have f948 : ((old b a a) ∨ (¬ spl0_5)) := by
    clear * - f169 f103
    first | exact resolve f169 f103 | exact resolve f103 f169 | grind (instances := 3000) only
  have f949 : ((old a a a) ∨ (¬ spl0_5)) := by
    clear * - f169 f102
    first | exact resolve f169 f102 | exact resolve f102 f169 | grind (instances := 3000) only
  have f950 : ((a = sk2) ∨ (¬ spl0_5)) := by
    clear * - f169 f101
    first | exact resolve f169 f101 | exact resolve f101 f169 | grind (instances := 3000) only
  have f951 : ((a = sk1) ∨ (¬ spl0_5)) := by
    clear * - f169 f100
    first | exact resolve f169 f100 | exact resolve f100 f169 | grind (instances := 3000) only
  have f952 : ((c = sk0) ∨ (¬ spl0_5)) := by
    clear * - f169 f99
    first | exact resolve f169 f99 | exact resolve f99 f169 | grind (instances := 3000) only
  have f978 : ((old sk0 a sk3) ∨ ((¬ spl0_5) ∨ (¬ spl0_25))) := by
    clear * - f465 f951
    first | exact superpose f465 f951 | exact superpose f951 f465 | grind (instances := 3000) only
  have f979 : ((old c a sk3) ∨ ((¬ spl0_5) ∨ (¬ spl0_25))) := by
    clear * - f978 f952
    grind (instances := 3000) only
  have f984 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_25))) := by
    clear * - f979 f74
    first | exact resolve f979 f74 | exact resolve f74 f979 | grind (instances := 3000) only
  have f985 : ((¬ spl0_5) ∨ (¬ spl0_25)) := by
    clear * - f984
    grind (instances := 3000) only
  have f1015 : ((a = c) ∨ ((¬ spl0_5) ∨ (¬ spl0_24))) := by
    clear * - f474 f952
    first | exact superpose f474 f952 | exact superpose f952 f474 | grind (instances := 3000) only
  have f1025 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_24))) := by
    clear * - f1015 f69
    first | exact resolve f1015 f69 | exact resolve f69 f1015 | grind (instances := 3000) only
  have f1026 : ((¬ spl0_5) ∨ (¬ spl0_24)) := by
    clear * - f1025
    grind (instances := 3000) only
  have f1038 : ((a = c) ∨ ((¬ spl0_5) ∨ (¬ spl0_23))) := by
    clear * - f501 f951
    grind (instances := 3000) only
  have f1043 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_23))) := by
    clear * - f1038 f69
    first | exact resolve f1038 f69 | exact resolve f69 f1038 | grind (instances := 3000) only
  have f1044 : ((¬ spl0_5) ∨ (¬ spl0_23)) := by
    clear * - f1043
    grind (instances := 3000) only
  have f1052 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_22))) := by
    clear * - f897 f950
    first | exact resolve f897 f950 | exact resolve f950 f897 | grind (instances := 3000) only
  have f1053 : ((¬ spl0_5) ∨ (¬ spl0_22)) := by
    clear * - f1052
    grind (instances := 3000) only
  have f1064 : (∀ (X2 X0 X1 : G), (((¬ (old X1 X1 X1)) ∨ ((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 sk3 X2)) ∨ ((¬ (old X0 X1 X2)) ∨ (sk3 = X1))))) ∨ (¬ spl0_21))) := by
    clear * - f550 f85
    first | exact resolve f550 f85 | exact resolve f85 f550 | grind (instances := 3000) only
  have f1090 : (∀ (X0 : G), (((¬ (old b b X0)) ∨ (b = X0)) ∨ (¬ spl0_5))) := by
    clear * - f947 f75
    first | exact resolve f947 f75 | exact resolve f75 f947 | grind (instances := 3000) only
  have f1099 : (∀ (X2 X3 X0 X1 X4 X5 : G), (((¬ (old X3 a X5)) ∨ ((¬ (old X0 X0 X3)) ∨ ((¬ (old X0 a X2)) ∨ ((¬ (old X3 X4 X5)) ∨ ((¬ (old X0 X1 X2)) ∨ ((¬ (old X1 X1 X4)) ∨ (a = X1))))))) ∨ (¬ spl0_5))) := by
    clear * - f949 f87
    first | exact resolve f949 f87 | exact resolve f87 f949 | grind (instances := 3000) only
  have f1211 : (∀ (X0 X1 : G), (((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 a X1)) ∨ (a = sk3)))) ∨ ((¬ spl0_5) ∨ (¬ spl0_21)))) := by
    clear * - f1064 f949
    first | exact resolve f1064 f949 | exact resolve f949 f1064 | grind (instances := 3000) only
  let spl0_36 : Prop := (a = sk3)
  have f1224 : (spl0_36 ↔ (a = sk3)) := Iff.rfl
  clear_value spl0_36
  have f1225 : ((a = sk3) ∨ (¬ spl0_36)) := by
    clear * - f1224
    grind (instances := 3000) only
  let spl0_37 : Prop := (∀ (X0 X1 : G), ((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 sk3 X1)))))
  have f1227 : (spl0_37 ↔ (∀ (X0 X1 : G), ((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 sk3 X1)))))) := Iff.rfl
  clear_value spl0_37
  have f1228 : (∀ (X0 X1 : G), (((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 X0 X0)))) ∨ (¬ spl0_37))) := by
    clear * - f1227
    grind (instances := 3000) only
  have f1229 : (spl0_36 ∨ (spl0_37 ∨ ((¬ spl0_5) ∨ (¬ spl0_21)))) := by
    clear * - f1211 f452 f168 f1227 f1224
    grind (instances := 3000) only
  have f1231 : ((¬ (old b a a)) ∨ ((¬ (old b b b)) ∨ ((¬ spl0_21) ∨ (¬ spl0_37)))) := by
    clear * - f1228 f551
    first | exact resolve f1228 f551 | exact resolve f551 f1228 | grind (instances := 3000) only
  have f1232 : ((¬ (old b b b)) ∨ ((¬ spl0_5) ∨ ((¬ spl0_21) ∨ (¬ spl0_37)))) := by
    clear * - f1231 f948
    first | exact resolve f1231 f948 | exact resolve f948 f1231 | grind (instances := 3000) only
  have f1233 : (False ∨ ((¬ spl0_5) ∨ ((¬ spl0_21) ∨ (¬ spl0_37)))) := by
    clear * - f1232 f947
    first | exact resolve f1232 f947 | exact resolve f947 f1232 | grind (instances := 3000) only
  have f1234 : ((¬ spl0_5) ∨ ((¬ spl0_21) ∨ (¬ spl0_37))) := by
    clear * - f1233
    grind (instances := 3000) only
  have f1236 : ((a ≠ sk2) ∨ (¬ spl0_36)) := by
    clear * - f136 f1225
    first | exact superpose f136 f1225 | exact superpose f1225 f136 | grind (instances := 3000) only
  have f1264 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_36))) := by
    clear * - f1236 f950
    first | exact resolve f1236 f950 | exact resolve f950 f1236 | grind (instances := 3000) only
  have f1265 : ((¬ spl0_5) ∨ (¬ spl0_36)) := by
    clear * - f1264
    grind (instances := 3000) only
  have f1269 : ((sP4 c a sk3) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f581 f951
    grind (instances := 3000) only
  have f1270 : ((old b sk3 a) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f571 f951
    grind (instances := 3000) only
  have f1282 : ((old sk3 sk3 (sF2 c a sk3)) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f1269 f116
    first | exact resolve f1269 f116 | exact resolve f116 f1269 | grind (instances := 3000) only
  have f1283 : ((old (sF1 c a sk3) (sF2 c a sk3) a) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f1269 f115
    first | exact resolve f1269 f115 | exact resolve f115 f1269 | grind (instances := 3000) only
  have f1285 : ((old b b (sF1 c a sk3)) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f1269 f113
    first | exact resolve f1269 f113 | exact resolve f113 f1269 | grind (instances := 3000) only
  have f1299 : ((b = (sF1 c a sk3)) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f1285 f1090
    first | exact resolve f1285 f1090 | exact resolve f1090 f1285 | grind (instances := 3000) only
  have f1330 : ((old b (sF2 c a sk3) a) ∨ ((¬ spl0_5) ∨ (¬ spl0_20))) := by
    clear * - f1283 f1299
    first | exact superpose f1283 f1299 | exact superpose f1299 f1283 | grind (instances := 3000) only
  have f1637 : (∀ (X2 X3 X0 X1 : G), (((¬ (old b X2 a)) ∨ ((¬ (old X0 a X1)) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X3 X1)) ∨ ((¬ (old X3 X3 X2)) ∨ (a = X3)))))) ∨ (¬ spl0_5))) := by
    clear * - f1099 f948
    first | exact resolve f1099 f948 | exact resolve f948 f1099 | grind (instances := 3000) only
  have f1642 : (∀ (X2 X0 X1 : G), (((¬ (old X2 X2 (sF2 c a sk3))) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X2 X1)) ∨ ((¬ (old X0 a X1)) ∨ (a = X2))))) ∨ ((¬ spl0_5) ∨ (¬ spl0_20)))) := by
    clear * - f1637 f1330
    first | exact resolve f1637 f1330 | exact resolve f1330 f1637 | grind (instances := 3000) only
  have f1644 : (∀ (X0 X1 : G), (((¬ (old X0 X0 b)) ∨ ((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 a X1)) ∨ (a = sk3)))) ∨ ((¬ spl0_5) ∨ (¬ spl0_20)))) := by
    clear * - f1642 f1282
    first | exact resolve f1642 f1282 | exact resolve f1282 f1642 | grind (instances := 3000) only
  let spl0_85 : Prop := (∀ (X0 X1 : G), ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 sk3 X1)))))
  have f1646 : (spl0_85 ↔ (∀ (X0 X1 : G), ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 sk3 X1)))))) := Iff.rfl
  clear_value spl0_85
  have f1647 : (∀ (X0 X1 : G), (((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 X0 b)))) ∨ (¬ spl0_85))) := by
    clear * - f1646
    grind (instances := 3000) only
  have f1648 : (spl0_36 ∨ (spl0_85 ∨ ((¬ spl0_5) ∨ (¬ spl0_20)))) := by
    clear * - f1644 f449 f168 f1646 f1224
    grind (instances := 3000) only
  have f1649 : ((¬ (old b a a)) ∨ ((¬ (old b b b)) ∨ ((¬ spl0_5) ∨ ((¬ spl0_20) ∨ (¬ spl0_85))))) := by
    clear * - f1647 f1270
    first | exact resolve f1647 f1270 | exact resolve f1270 f1647 | grind (instances := 3000) only
  have f1653 : ((¬ (old b b b)) ∨ ((¬ spl0_5) ∨ ((¬ spl0_20) ∨ (¬ spl0_85)))) := by
    clear * - f1649 f948
    first | exact resolve f1649 f948 | exact resolve f948 f1649 | grind (instances := 3000) only
  have f1654 : (False ∨ ((¬ spl0_5) ∨ ((¬ spl0_20) ∨ (¬ spl0_85)))) := by
    clear * - f1653 f947
    first | exact resolve f1653 f947 | exact resolve f947 f1653 | grind (instances := 3000) only
  have f1655 : ((¬ spl0_5) ∨ ((¬ spl0_20) ∨ (¬ spl0_85))) := by
    clear * - f1654
    grind (instances := 3000) only
  have f1660 : ((a = c) ∨ ((¬ spl0_5) ∨ (¬ spl0_19))) := by
    clear * - f589 f951
    grind (instances := 3000) only
  have f1665 : (False ∨ ((¬ spl0_5) ∨ (¬ spl0_19))) := by
    clear * - f1660 f69
    first | exact resolve f1660 f69 | exact resolve f69 f1660 | grind (instances := 3000) only
  have f1666 : ((¬ spl0_5) ∨ (¬ spl0_19)) := by
    clear * - f1665
    grind (instances := 3000) only
  have f1676 : ((old sk2 sk2 sk2) ∨ (¬ spl0_4)) := by
    clear * - f166 f110
    first | exact resolve f166 f110 | exact resolve f110 f166 | grind (instances := 3000) only
  have f1677 : ((old b sk2 a) ∨ (¬ spl0_4)) := by
    clear * - f166 f109
    first | exact resolve f166 f109 | exact resolve f109 f166 | grind (instances := 3000) only
  have f1678 : ((old b b b) ∨ (¬ spl0_4)) := by
    clear * - f166 f108
    first | exact resolve f166 f108 | exact resolve f108 f166 | grind (instances := 3000) only
  have f1679 : ((a = sk1) ∨ (¬ spl0_4)) := by
    clear * - f166 f107
    first | exact resolve f166 f107 | exact resolve f107 f166 | grind (instances := 3000) only
  have f1680 : ((c = sk0) ∨ (¬ spl0_4)) := by
    clear * - f166 f106
    first | exact resolve f166 f106 | exact resolve f106 f166 | grind (instances := 3000) only
  have f1696 : ((old sk0 a sk3) ∨ ((¬ spl0_4) ∨ (¬ spl0_25))) := by
    clear * - f465 f1679
    first | exact superpose f465 f1679 | exact superpose f1679 f465 | grind (instances := 3000) only
  have f1697 : ((old c a sk3) ∨ ((¬ spl0_4) ∨ (¬ spl0_25))) := by
    clear * - f1696 f1680
    grind (instances := 3000) only
  have f1702 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_25))) := by
    clear * - f1697 f74
    first | exact resolve f1697 f74 | exact resolve f74 f1697 | grind (instances := 3000) only
  have f1703 : ((¬ spl0_4) ∨ (¬ spl0_25)) := by
    clear * - f1702
    grind (instances := 3000) only
  have f1740 : ((a = c) ∨ ((¬ spl0_4) ∨ (¬ spl0_24))) := by
    clear * - f474 f1680
    first | exact superpose f474 f1680 | exact superpose f1680 f474 | grind (instances := 3000) only
  have f1750 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_24))) := by
    clear * - f1740 f69
    first | exact resolve f1740 f69 | exact resolve f69 f1740 | grind (instances := 3000) only
  have f1751 : ((¬ spl0_4) ∨ (¬ spl0_24)) := by
    clear * - f1750
    grind (instances := 3000) only
  have f1757 : ((a = c) ∨ ((¬ spl0_4) ∨ (¬ spl0_23))) := by
    clear * - f501 f1679
    grind (instances := 3000) only
  have f1760 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_23))) := by
    clear * - f1757 f69
    first | exact resolve f1757 f69 | exact resolve f69 f1757 | grind (instances := 3000) only
  have f1761 : ((¬ spl0_4) ∨ (¬ spl0_23)) := by
    clear * - f1760
    grind (instances := 3000) only
  have f1794 : (∀ (X2 X0 X1 : G), (((¬ (old X1 X1 X1)) ∨ ((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 a X2)) ∨ ((¬ (old X0 X1 X2)) ∨ (a = X1))))) ∨ (¬ spl0_22))) := by
    clear * - f523 f85
    first | exact resolve f523 f85 | exact resolve f85 f523 | grind (instances := 3000) only
  have f1807 : (∀ (X2 X0 X1 : G), (((¬ (old X1 X1 X1)) ∨ ((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 sk2 X2)) ∨ ((¬ (old X0 X1 X2)) ∨ (sk2 = X1))))) ∨ (¬ spl0_4))) := by
    clear * - f1676 f85
    first | exact resolve f1676 f85 | exact resolve f85 f1676 | grind (instances := 3000) only
  have f1809 : (∀ (X2 X3 X0 X1 X4 X5 : G), (((¬ (old X3 sk2 X5)) ∨ ((¬ (old X0 X0 X3)) ∨ ((¬ (old X0 sk2 X2)) ∨ ((¬ (old X3 X4 X5)) ∨ ((¬ (old X0 X1 X2)) ∨ ((¬ (old X1 X1 X4)) ∨ (sk2 = X1))))))) ∨ (¬ spl0_4))) := by
    clear * - f1676 f87
    first | exact resolve f1676 f87 | exact resolve f87 f1676 | grind (instances := 3000) only
  have f1831 : (∀ (X0 : G), (((¬ (old b b X0)) ∨ (b = X0)) ∨ (¬ spl0_4))) := by
    clear * - f1678 f75
    first | exact resolve f1678 f75 | exact resolve f75 f1678 | grind (instances := 3000) only
  have f1935 : (∀ (X0 X1 : G), (((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 a X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (a = sk2)))) ∨ ((¬ spl0_4) ∨ (¬ spl0_22)))) := by
    clear * - f1794 f1676
    first | exact resolve f1794 f1676 | exact resolve f1676 f1794 | grind (instances := 3000) only
  have f1938 : (∀ (X0 X1 : G), (((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 a X1)) ∨ (¬ (old X0 X0 X0)))) ∨ ((¬ spl0_4) ∨ (¬ spl0_22)))) := by
    clear * - f1935 f529
    first | exact resolve f1935 f529 | exact resolve f529 f1935 | grind (instances := 3000) only
  have f1940 : ((¬ (old b a a)) ∨ ((¬ (old b b b)) ∨ ((¬ spl0_4) ∨ (¬ spl0_22)))) := by
    clear * - f1938 f1677
    first | exact resolve f1938 f1677 | exact resolve f1677 f1938 | grind (instances := 3000) only
  have f1941 : ((¬ (old b b b)) ∨ ((¬ spl0_4) ∨ (¬ spl0_22))) := by
    clear * - f1940 f522
    first | exact resolve f1940 f522 | exact resolve f522 f1940 | grind (instances := 3000) only
  have f1942 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_22))) := by
    clear * - f1941 f1678
    first | exact resolve f1941 f1678 | exact resolve f1678 f1941 | grind (instances := 3000) only
  have f1943 : ((¬ spl0_4) ∨ (¬ spl0_22)) := by
    clear * - f1942
    grind (instances := 3000) only
  have f2011 : (∀ (X0 X1 : G), (((¬ (old X0 X0 X0)) ∨ ((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 sk3 X1)) ∨ (sk2 = sk3)))) ∨ ((¬ spl0_4) ∨ (¬ spl0_21)))) := by
    clear * - f1807 f550
    first | exact resolve f1807 f550 | exact resolve f550 f1807 | grind (instances := 3000) only
  have f2013 : (∀ (X0 X1 : G), (((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (¬ (old X0 X0 X0)))) ∨ ((¬ spl0_4) ∨ (¬ spl0_21)))) := by
    clear * - f2011 f136
    first | exact resolve f2011 f136 | exact resolve f136 f2011 | grind (instances := 3000) only
  have f2015 : ((¬ (old b sk2 a)) ∨ ((¬ (old b b b)) ∨ ((¬ spl0_4) ∨ (¬ spl0_21)))) := by
    clear * - f2013 f551
    first | exact resolve f2013 f551 | exact resolve f551 f2013 | grind (instances := 3000) only
  have f2016 : ((¬ (old b b b)) ∨ ((¬ spl0_4) ∨ (¬ spl0_21))) := by
    clear * - f2015 f1677
    first | exact resolve f2015 f1677 | exact resolve f1677 f2015 | grind (instances := 3000) only
  have f2017 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_21))) := by
    clear * - f2016 f1678
    first | exact resolve f2016 f1678 | exact resolve f1678 f2016 | grind (instances := 3000) only
  have f2018 : ((¬ spl0_4) ∨ (¬ spl0_21)) := by
    clear * - f2017
    grind (instances := 3000) only
  have f2020 : ((sP4 c a sk3) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f581 f1679
    grind (instances := 3000) only
  have f2021 : ((old b sk3 a) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f571 f1679
    grind (instances := 3000) only
  have f2030 : ((old sk3 sk3 (sF2 c a sk3)) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2020 f116
    first | exact resolve f2020 f116 | exact resolve f116 f2020 | grind (instances := 3000) only
  have f2031 : ((old (sF1 c a sk3) (sF2 c a sk3) a) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2020 f115
    first | exact resolve f2020 f115 | exact resolve f115 f2020 | grind (instances := 3000) only
  have f2033 : ((old b b (sF1 c a sk3)) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2020 f113
    first | exact resolve f2020 f113 | exact resolve f113 f2020 | grind (instances := 3000) only
  have f2047 : ((b = (sF1 c a sk3)) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2033 f1831
    first | exact resolve f2033 f1831 | exact resolve f1831 f2033 | grind (instances := 3000) only
  have f2071 : ((old b (sF2 c a sk3) a) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2031 f2047
    first | exact superpose f2031 f2047 | exact superpose f2047 f2031 | grind (instances := 3000) only
  have f2438 : (∀ (X2 X3 X0 X1 : G), (((¬ (old b X2 a)) ∨ ((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X3 X1)) ∨ ((¬ (old X3 X3 X2)) ∨ (sk2 = X3)))))) ∨ (¬ spl0_4))) := by
    clear * - f1809 f1677
    first | exact resolve f1809 f1677 | exact resolve f1677 f1809 | grind (instances := 3000) only
  have f2446 : (∀ (X2 X0 X1 : G), (((¬ (old X2 X2 (sF2 c a sk3))) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X2 X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (sk2 = X2))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_20)))) := by
    clear * - f2438 f2071
    first | exact resolve f2438 f2071 | exact resolve f2071 f2438 | grind (instances := 3000) only
  have f2449 : (∀ (X0 X1 : G), (((¬ (old X0 X0 b)) ∨ ((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (sk2 = sk3)))) ∨ ((¬ spl0_4) ∨ (¬ spl0_20)))) := by
    clear * - f2446 f2030
    first | exact resolve f2446 f2030 | exact resolve f2030 f2446 | grind (instances := 3000) only
  have f2450 : (∀ (X0 X1 : G), (((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 X0 b)) ∨ (¬ (old X0 sk2 X1)))) ∨ ((¬ spl0_4) ∨ (¬ spl0_20)))) := by
    clear * - f2449 f136
    first | exact resolve f2449 f136 | exact resolve f136 f2449 | grind (instances := 3000) only
  have f2451 : ((¬ (old b b b)) ∨ ((¬ (old b sk2 a)) ∨ ((¬ spl0_4) ∨ (¬ spl0_20)))) := by
    clear * - f2450 f2021
    first | exact resolve f2450 f2021 | exact resolve f2021 f2450 | grind (instances := 3000) only
  have f2456 : ((¬ (old b sk2 a)) ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2451 f1678
    first | exact resolve f2451 f1678 | exact resolve f1678 f2451 | grind (instances := 3000) only
  have f2457 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_20))) := by
    clear * - f2456 f1677
    first | exact resolve f2456 f1677 | exact resolve f1677 f2456 | grind (instances := 3000) only
  have f2458 : ((¬ spl0_4) ∨ (¬ spl0_20)) := by
    clear * - f2457
    grind (instances := 3000) only
  have f2463 : ((a = c) ∨ ((¬ spl0_4) ∨ (¬ spl0_19))) := by
    clear * - f589 f1679
    grind (instances := 3000) only
  have f2465 : (False ∨ ((¬ spl0_4) ∨ (¬ spl0_19))) := by
    clear * - f2463 f69
    first | exact resolve f2463 f69 | exact resolve f69 f2463 | grind (instances := 3000) only
  have f2466 : ((¬ spl0_4) ∨ (¬ spl0_19)) := by
    clear * - f2465
    grind (instances := 3000) only
  have f2490 : ((old sk2 sk2 (sF2 sk0 sk1 sk2)) ∨ (¬ spl0_3)) := by
    clear * - f163 f116
    first | exact resolve f163 f116 | exact resolve f116 f163 | grind (instances := 3000) only
  have f2491 : ((old (sF1 sk0 sk1 sk2) (sF2 sk0 sk1 sk2) a) ∨ (¬ spl0_3)) := by
    clear * - f163 f115
    first | exact resolve f163 f115 | exact resolve f115 f163 | grind (instances := 3000) only
  have f2492 : ((old b sk2 sk1) ∨ (¬ spl0_3)) := by
    clear * - f163 f114
    first | exact resolve f163 f114 | exact resolve f114 f163 | grind (instances := 3000) only
  have f2493 : ((old b b (sF1 sk0 sk1 sk2)) ∨ (¬ spl0_3)) := by
    clear * - f163 f113
    first | exact resolve f163 f113 | exact resolve f113 f163 | grind (instances := 3000) only
  have f2494 : ((c = sk0) ∨ (¬ spl0_3)) := by
    clear * - f163 f112
    first | exact resolve f163 f112 | exact resolve f112 f163 | grind (instances := 3000) only
  have f2497 : ((old b sk2 c) ∨ ((¬ spl0_3) ∨ (¬ spl0_19))) := by
    clear * - f2492 f589
    grind (instances := 3000) only
  have f2501 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_19))) := by
    clear * - f2497 f72
    first | exact resolve f2497 f72 | exact resolve f72 f2497 | grind (instances := 3000) only
  have f2502 : ((¬ spl0_3) ∨ (¬ spl0_19)) := by
    clear * - f2501
    grind (instances := 3000) only
  have f2505 : ((old c sk1 sk3) ∨ ((¬ spl0_3) ∨ (¬ spl0_25))) := by
    clear * - f465 f2494
    grind (instances := 3000) only
  have f2506 : ((old b b (sF1 c sk1 sk2)) ∨ (¬ spl0_3)) := by
    clear * - f2493 f2494
    grind (instances := 3000) only
  have f2507 : ((old (sF1 c sk1 sk2) (sF2 c sk1 sk2) a) ∨ (¬ spl0_3)) := by
    clear * - f2491 f2494
    grind (instances := 3000) only
  have f2508 : ((old sk2 sk2 (sF2 c sk1 sk2)) ∨ (¬ spl0_3)) := by
    clear * - f2490 f2494
    grind (instances := 3000) only
  have f2509 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_25))) := by
    clear * - f2505 f74
    first | exact resolve f2505 f74 | exact resolve f74 f2505 | grind (instances := 3000) only
  have f2510 : ((¬ spl0_3) ∨ (¬ spl0_25)) := by
    clear * - f2509
    grind (instances := 3000) only
  have f2561 : ((a = c) ∨ ((¬ spl0_3) ∨ (¬ spl0_24))) := by
    clear * - f2494 f474
    first | exact superpose f2494 f474 | exact superpose f474 f2494 | grind (instances := 3000) only
  have f2564 : ((sP4 c sk1 sk2) ∨ (¬ spl0_3)) := by
    clear * - f163 f2494
    first | exact superpose f163 f2494 | exact superpose f2494 f163 | grind (instances := 3000) only
  have f2571 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_24))) := by
    clear * - f2561 f69
    first | exact resolve f2561 f69 | exact resolve f69 f2561 | grind (instances := 3000) only
  have f2572 : ((¬ spl0_3) ∨ (¬ spl0_24)) := by
    clear * - f2571
    grind (instances := 3000) only
  have f2612 : ((old b sk2 c) ∨ ((¬ spl0_3) ∨ (¬ spl0_23))) := by
    clear * - f2492 f501
    first | exact superpose f2492 f501 | exact superpose f501 f2492 | grind (instances := 3000) only
  have f2613 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_23))) := by
    clear * - f2612 f72
    first | exact resolve f2612 f72 | exact resolve f72 f2612 | grind (instances := 3000) only
  have f2614 : ((¬ spl0_3) ∨ (¬ spl0_23)) := by
    clear * - f2613
    grind (instances := 3000) only
  have f2623 : ((sP4 c a sk2) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f2564 f525
    grind (instances := 3000) only
  have f2669 : (∀ (X0 : G), (((¬ (old b b X0)) ∨ (b = X0)) ∨ (¬ spl0_22))) := by
    clear * - f521 f75
    first | exact resolve f521 f75 | exact resolve f75 f521 | grind (instances := 3000) only
  have f2678 : (∀ (X2 X3 X0 X1 X4 X5 : G), (((¬ (old X3 a X5)) ∨ ((¬ (old X0 X0 X3)) ∨ ((¬ (old X0 a X2)) ∨ ((¬ (old X3 X4 X5)) ∨ ((¬ (old X0 X1 X2)) ∨ ((¬ (old X1 X1 X4)) ∨ (a = X1))))))) ∨ (¬ spl0_22))) := by
    clear * - f523 f87
    first | exact resolve f523 f87 | exact resolve f87 f523 | grind (instances := 3000) only
  have f2700 : (∀ (X0 : G), (((¬ (old b b X0)) ∨ ((sF1 c sk1 sk2) = X0)) ∨ (¬ spl0_3))) := by
    clear * - f2506 f75
    first | exact resolve f2506 f75 | exact resolve f75 f2506 | grind (instances := 3000) only
  have f2712 : ((old sk2 sk2 (sF2 c a sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f2623 f116
    first | exact resolve f2623 f116 | exact resolve f116 f2623 | grind (instances := 3000) only
  have f2713 : ((old (sF1 c a sk2) (sF2 c a sk2) a) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f2623 f115
    first | exact resolve f2623 f115 | exact resolve f115 f2623 | grind (instances := 3000) only
  have f2719 : (∀ (X2 X3 X0 X1 X4 X5 : G), (((¬ (old X3 (sF2 c sk1 sk2) X5)) ∨ ((¬ (old X0 X0 X3)) ∨ ((¬ (old X0 sk2 X2)) ∨ ((¬ (old X3 X4 X5)) ∨ ((¬ (old X0 X1 X2)) ∨ ((¬ (old X1 X1 X4)) ∨ (sk2 = X1))))))) ∨ (¬ spl0_3))) := by
    clear * - f2508 f87
    first | exact resolve f2508 f87 | exact resolve f87 f2508 | grind (instances := 3000) only
  have f2741 : ((b = (sF1 c sk1 sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f2669 f2506
    first | exact resolve f2669 f2506 | exact resolve f2506 f2669 | grind (instances := 3000) only
  have f2742 : ((b = (sF1 c a sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f2741 f525
    grind (instances := 3000) only
  have f2783 : ((old b (sF2 c a sk2) a) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f2713 f2742
    first | exact superpose f2713 f2742 | exact superpose f2742 f2713 | grind (instances := 3000) only
  have f3178 : (∀ (X2 X3 X0 X1 : G), (((¬ (old b X2 a)) ∨ ((¬ (old X0 a X1)) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X3 X1)) ∨ ((¬ (old X3 X3 X2)) ∨ (a = X3)))))) ∨ (¬ spl0_22))) := by
    clear * - f2678 f522
    first | exact resolve f2678 f522 | exact resolve f522 f2678 | grind (instances := 3000) only
  have f3183 : (∀ (X2 X0 X1 : G), (((¬ (old X2 X2 (sF2 c a sk2))) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X2 X1)) ∨ ((¬ (old X0 a X1)) ∨ (a = X2))))) ∨ ((¬ spl0_3) ∨ (¬ spl0_22)))) := by
    clear * - f3178 f2783
    first | exact resolve f3178 f2783 | exact resolve f2783 f3178 | grind (instances := 3000) only
  have f3185 : (∀ (X0 X1 : G), (((¬ (old X0 X0 b)) ∨ ((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 a X1)) ∨ (a = sk2)))) ∨ ((¬ spl0_3) ∨ (¬ spl0_22)))) := by
    clear * - f3183 f2712
    first | exact resolve f3183 f2712 | exact resolve f2712 f3183 | grind (instances := 3000) only
  have f3186 : (∀ (X0 X1 : G), (((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 X0 b)) ∨ (¬ (old X0 a X1)))) ∨ ((¬ spl0_3) ∨ (¬ spl0_22)))) := by
    clear * - f3185 f529
    first | exact resolve f3185 f529 | exact resolve f529 f3185 | grind (instances := 3000) only
  have f3187 : ((¬ (old b b b)) ∨ ((¬ (old b a sk1)) ∨ ((¬ spl0_3) ∨ (¬ spl0_22)))) := by
    clear * - f3186 f2492
    first | exact resolve f3186 f2492 | exact resolve f2492 f3186 | grind (instances := 3000) only
  have f3195 : ((¬ (old b a sk1)) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f3187 f521
    first | exact resolve f3187 f521 | exact resolve f521 f3187 | grind (instances := 3000) only
  have f3198 : ((¬ (old b a a)) ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f3195 f525
    grind (instances := 3000) only
  have f3199 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_22))) := by
    clear * - f3198 f522
    first | exact resolve f3198 f522 | exact resolve f522 f3198 | grind (instances := 3000) only
  have f3200 : ((¬ spl0_3) ∨ (¬ spl0_22)) := by
    clear * - f3199
    grind (instances := 3000) only
  have f3234 : ((old b sk2 a) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f2492 f553
    first | exact superpose f2492 f553 | exact superpose f553 f2492 | grind (instances := 3000) only
  have f3235 : ((old b b (sF1 c a sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f2506 f553
    first | exact superpose f2506 f553 | exact superpose f553 f2506 | grind (instances := 3000) only
  have f3236 : ((old (sF1 c a sk2) (sF2 c a sk2) a) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f2507 f553
    first | exact superpose f2507 f553 | exact superpose f553 f2507 | grind (instances := 3000) only
  have f3237 : ((old sk2 sk2 (sF2 c a sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f2508 f553
    first | exact superpose f2508 f553 | exact superpose f553 f2508 | grind (instances := 3000) only
  have f3246 : (∀ (X2 X3 X0 X1 X4 X5 : G), (((¬ (old X3 sk3 X5)) ∨ ((¬ (old X0 X0 X3)) ∨ ((¬ (old X0 sk3 X2)) ∨ ((¬ (old X3 X4 X5)) ∨ ((¬ (old X0 X1 X2)) ∨ ((¬ (old X1 X1 X4)) ∨ (sk3 = X1))))))) ∨ (¬ spl0_21))) := by
    clear * - f550 f87
    first | exact resolve f550 f87 | exact resolve f87 f550 | grind (instances := 3000) only
  have f3268 : (∀ (X0 : G), (((¬ (old b b X0)) ∨ (b = X0)) ∨ (¬ spl0_21))) := by
    clear * - f552 f75
    first | exact resolve f552 f75 | exact resolve f75 f552 | grind (instances := 3000) only
  have f3304 : ((b = (sF1 c a sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f3268 f3235
    first | exact resolve f3268 f3235 | exact resolve f3235 f3268 | grind (instances := 3000) only
  have f3320 : ((old b (sF2 c a sk2) a) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f3236 f3304
    first | exact superpose f3236 f3304 | exact superpose f3304 f3236 | grind (instances := 3000) only
  have f3769 : (∀ (X2 X3 X0 X1 : G), (((¬ (old b X2 a)) ∨ ((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X3 X1)) ∨ ((¬ (old X3 X3 X2)) ∨ (sk3 = X3)))))) ∨ (¬ spl0_21))) := by
    clear * - f3246 f551
    first | exact resolve f3246 f551 | exact resolve f551 f3246 | grind (instances := 3000) only
  have f3775 : (∀ (X2 X0 X1 : G), (((¬ (old X2 X2 (sF2 c a sk2))) ∨ ((¬ (old X0 X0 b)) ∨ ((¬ (old X0 X2 X1)) ∨ ((¬ (old X0 sk3 X1)) ∨ (sk3 = X2))))) ∨ ((¬ spl0_3) ∨ (¬ spl0_21)))) := by
    clear * - f3769 f3320
    first | exact resolve f3769 f3320 | exact resolve f3320 f3769 | grind (instances := 3000) only
  have f3778 : (∀ (X0 X1 : G), (((¬ (old X0 X0 b)) ∨ ((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 sk3 X1)) ∨ (sk2 = sk3)))) ∨ ((¬ spl0_3) ∨ (¬ spl0_21)))) := by
    clear * - f3775 f3237
    first | exact resolve f3775 f3237 | exact resolve f3237 f3775 | grind (instances := 3000) only
  have f3779 : (∀ (X0 X1 : G), (((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (¬ (old X0 X0 b)))) ∨ ((¬ spl0_3) ∨ (¬ spl0_21)))) := by
    clear * - f3778 f136
    first | exact resolve f3778 f136 | exact resolve f136 f3778 | grind (instances := 3000) only
  have f3781 : ((¬ (old b sk2 a)) ∨ ((¬ (old b b b)) ∨ ((¬ spl0_3) ∨ (¬ spl0_21)))) := by
    clear * - f3779 f551
    first | exact resolve f3779 f551 | exact resolve f551 f3779 | grind (instances := 3000) only
  have f3786 : ((¬ (old b b b)) ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f3781 f3234
    first | exact resolve f3781 f3234 | exact resolve f3234 f3781 | grind (instances := 3000) only
  have f3787 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_21))) := by
    clear * - f3786 f552
    first | exact resolve f3786 f552 | exact resolve f552 f3786 | grind (instances := 3000) only
  have f3788 : ((¬ spl0_3) ∨ (¬ spl0_21)) := by
    clear * - f3787
    grind (instances := 3000) only
  have f3794 : ((old sk3 sk3 (sF2 c sk1 sk3)) ∨ (¬ spl0_20)) := by
    clear * - f581 f116
    first | exact resolve f581 f116 | exact resolve f116 f581 | grind (instances := 3000) only
  have f3795 : ((old (sF1 c sk1 sk3) (sF2 c sk1 sk3) a) ∨ (¬ spl0_20)) := by
    clear * - f581 f115
    first | exact resolve f581 f115 | exact resolve f115 f581 | grind (instances := 3000) only
  have f3797 : ((old b b (sF1 c sk1 sk3)) ∨ (¬ spl0_20)) := by
    clear * - f581 f113
    first | exact resolve f581 f113 | exact resolve f113 f581 | grind (instances := 3000) only
  have f3822 : (((sF1 c sk1 sk3) = (sF1 c sk1 sk2)) ∨ ((¬ spl0_3) ∨ (¬ spl0_20))) := by
    clear * - f2700 f3797
    first | exact resolve f2700 f3797 | exact resolve f3797 f2700 | grind (instances := 3000) only
  have f3828 : ((old (sF1 c sk1 sk2) (sF2 c sk1 sk3) a) ∨ ((¬ spl0_3) ∨ (¬ spl0_20))) := by
    clear * - f3795 f3822
    first | exact superpose f3795 f3822 | exact superpose f3822 f3795 | grind (instances := 3000) only
  have f3865 : (∀ (X2 X3 X0 X1 : G), (((¬ (old (sF1 c sk1 sk2) X2 a)) ∨ ((¬ (old X0 sk2 X1)) ∨ ((¬ (old X0 X0 (sF1 c sk1 sk2))) ∨ ((¬ (old X0 X3 X1)) ∨ ((¬ (old X3 X3 X2)) ∨ (sk2 = X3)))))) ∨ (¬ spl0_3))) := by
    clear * - f2719 f2507
    first | exact resolve f2719 f2507 | exact resolve f2507 f2719 | grind (instances := 3000) only
  have f3867 : (∀ (X2 X0 X1 : G), (((¬ (old X2 X2 (sF2 c sk1 sk3))) ∨ ((¬ (old X0 X0 (sF1 c sk1 sk2))) ∨ ((¬ (old X0 X2 X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (sk2 = X2))))) ∨ ((¬ spl0_3) ∨ (¬ spl0_20)))) := by
    clear * - f3865 f3828
    first | exact resolve f3865 f3828 | exact resolve f3828 f3865 | grind (instances := 3000) only
  have f3868 : (∀ (X0 X1 : G), (((¬ (old X0 X0 (sF1 c sk1 sk2))) ∨ ((¬ (old X0 sk3 X1)) ∨ ((¬ (old X0 sk2 X1)) ∨ (sk2 = sk3)))) ∨ ((¬ spl0_3) ∨ (¬ spl0_20)))) := by
    clear * - f3867 f3794
    first | exact resolve f3867 f3794 | exact resolve f3794 f3867 | grind (instances := 3000) only
  have f3869 : (∀ (X0 X1 : G), (((¬ (old X0 X0 (sF1 c sk1 sk2))) ∨ ((¬ (old X0 sk3 X1)) ∨ (¬ (old X0 sk2 X1)))) ∨ ((¬ spl0_3) ∨ (¬ spl0_20)))) := by
    clear * - f3868 f136
    first | exact resolve f3868 f136 | exact resolve f136 f3868 | grind (instances := 3000) only
  have f3870 : (∀ (X0 : G), (((¬ (old b sk3 X0)) ∨ (¬ (old b sk2 X0))) ∨ ((¬ spl0_3) ∨ (¬ spl0_20)))) := by
    clear * - f3869 f2506
    first | exact resolve f3869 f2506 | exact resolve f2506 f3869 | grind (instances := 3000) only
  have f3871 : ((¬ (old b sk2 sk1)) ∨ ((¬ spl0_3) ∨ (¬ spl0_20))) := by
    clear * - f3870 f571
    first | exact resolve f3870 f571 | exact resolve f571 f3870 | grind (instances := 3000) only
  have f3872 : (False ∨ ((¬ spl0_3) ∨ (¬ spl0_20))) := by
    clear * - f3871 f2492
    first | exact resolve f3871 f2492 | exact resolve f2492 f3871 | grind (instances := 3000) only
  have f3873 : ((¬ spl0_3) ∨ (¬ spl0_20)) := by
    clear * - f3872
    grind (instances := 3000) only
  have s1 : (spl0_1 ∨ (spl0_2 ∨ (spl0_3 ∨ (spl0_4 ∨ (spl0_5 ∨ (spl0_6 ∨ (spl0_7 ∨ spl0_8))))))) := by
    clear * - f179
    grind (splits := 100) only
  have s3 : (¬ spl0_1) := by
    clear * - f232
    grind (splits := 100) only
  have s5 : ((¬ spl0_2) ∨ (spl0_11 ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ (spl0_16 ∨ spl0_17))))))) := by
    clear * - f333
    grind (splits := 100) only
  have s9 : ((¬ spl0_2) ∨ (¬ spl0_11)) := by
    clear * - f378
    grind (splits := 100) only
  have s10 : (¬ spl0_17) := by
    clear * - f383
    grind (splits := 100) only
  have s11 : ((¬ spl0_2) ∨ (¬ spl0_12)) := by
    clear * - f399
    grind (splits := 100) only
  have s12 : ((¬ spl0_2) ∨ (¬ spl0_16)) := by
    clear * - f412
    grind (splits := 100) only
  have s13 : (¬ spl0_13) := by
    clear * - f421
    grind (splits := 100) only
  have s14 : (¬ spl0_14) := by
    clear * - f430
    grind (splits := 100) only
  have s15 : (¬ spl0_15) := by
    clear * - f438
    grind (splits := 100) only
  have s16 : (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (spl0_21 ∨ (spl0_22 ∨ (spl0_23 ∨ (spl0_24 ∨ spl0_25))))))) := by
    clear * - f466
    grind (splits := 100) only
  have s17 : ((¬ spl0_8) ∨ (¬ spl0_25)) := by
    clear * - f471
    grind (splits := 100) only
  have s18 : ((¬ spl0_8) ∨ (¬ spl0_24)) := by
    clear * - f496
    grind (splits := 100) only
  have s19 : ((¬ spl0_8) ∨ (¬ spl0_23)) := by
    clear * - f519
    grind (splits := 100) only
  have s20 : ((¬ spl0_8) ∨ (¬ spl0_22)) := by
    clear * - f548
    grind (splits := 100) only
  have s21 : ((¬ spl0_8) ∨ (¬ spl0_21)) := by
    clear * - f568
    grind (splits := 100) only
  have s22 : ((¬ spl0_8) ∨ (¬ spl0_20)) := by
    clear * - f583
    grind (splits := 100) only
  have s23 : ((¬ spl0_8) ∨ (¬ spl0_19)) := by
    clear * - f611
    grind (splits := 100) only
  have s24 : ((¬ spl0_8) ∨ (¬ spl0_18)) := by
    clear * - f633
    grind (splits := 100) only
  have s26 : ((¬ spl0_3) ∨ (¬ spl0_18)) := by
    clear * - f663
    grind (splits := 100) only
  have s28 : ((¬ spl0_4) ∨ (¬ spl0_18)) := by
    clear * - f675
    grind (splits := 100) only
  have s33 : ((¬ spl0_5) ∨ (¬ spl0_18)) := by
    clear * - f697
    grind (splits := 100) only
  have s36 : ((¬ spl0_6) ∨ (¬ spl0_18)) := by
    clear * - f709
    grind (splits := 100) only
  have s38 : ((¬ spl0_7) ∨ (¬ spl0_18)) := by
    clear * - f718
    grind (splits := 100) only
  have s39 : ((¬ spl0_7) ∨ (¬ spl0_19)) := by
    clear * - f748
    grind (splits := 100) only
  have s41 : ((¬ spl0_7) ∨ (¬ spl0_25)) := by
    clear * - f785
    grind (splits := 100) only
  have s42 : ((¬ spl0_7) ∨ (¬ spl0_24)) := by
    clear * - f792
    grind (splits := 100) only
  have s43 : ((¬ spl0_7) ∨ (¬ spl0_23)) := by
    clear * - f804
    grind (splits := 100) only
  have s44 : ((¬ spl0_7) ∨ (¬ spl0_22)) := by
    clear * - f813
    grind (splits := 100) only
  have s45 : ((¬ spl0_7) ∨ (¬ spl0_21)) := by
    clear * - f824
    grind (splits := 100) only
  have s46 : ((¬ spl0_7) ∨ (¬ spl0_20)) := by
    clear * - f836
    grind (splits := 100) only
  have s47 : ((¬ spl0_6) ∨ (¬ spl0_25)) := by
    clear * - f858
    grind (splits := 100) only
  have s49 : ((¬ spl0_6) ∨ (¬ spl0_24)) := by
    clear * - f882
    grind (splits := 100) only
  have s50 : ((¬ spl0_6) ∨ (¬ spl0_23)) := by
    clear * - f889
    grind (splits := 100) only
  have s52 : ((¬ spl0_6) ∨ (¬ spl0_22)) := by
    clear * - f912
    grind (splits := 100) only
  have s54 : ((¬ spl0_6) ∨ (¬ spl0_21)) := by
    clear * - f930
    grind (splits := 100) only
  have s55 : ((¬ spl0_6) ∨ (¬ spl0_20)) := by
    clear * - f940
    grind (splits := 100) only
  have s56 : ((¬ spl0_6) ∨ (¬ spl0_19)) := by
    clear * - f945
    grind (splits := 100) only
  have s58 : ((¬ spl0_5) ∨ (¬ spl0_25)) := by
    clear * - f985
    grind (splits := 100) only
  have s60 : ((¬ spl0_5) ∨ (¬ spl0_24)) := by
    clear * - f1026
    grind (splits := 100) only
  have s61 : ((¬ spl0_5) ∨ (¬ spl0_23)) := by
    clear * - f1044
    grind (splits := 100) only
  have s63 : ((¬ spl0_5) ∨ (¬ spl0_22)) := by
    clear * - f1053
    grind (splits := 100) only
  have s69 : ((¬ spl0_5) ∨ ((¬ spl0_21) ∨ (spl0_36 ∨ spl0_37))) := by
    clear * - f1229
    grind (splits := 100) only
  have s70 : ((¬ spl0_5) ∨ ((¬ spl0_21) ∨ (¬ spl0_37))) := by
    clear * - f1234
    grind (splits := 100) only
  have s73 : ((¬ spl0_5) ∨ (¬ spl0_36)) := by
    clear * - f1265
    grind (splits := 100) only
  have s102 : ((¬ spl0_5) ∨ ((¬ spl0_20) ∨ (spl0_36 ∨ spl0_85))) := by
    clear * - f1648
    grind (splits := 100) only
  have s103 : ((¬ spl0_5) ∨ ((¬ spl0_20) ∨ (¬ spl0_85))) := by
    clear * - f1655
    grind (splits := 100) only
  have s104 : ((¬ spl0_5) ∨ (¬ spl0_19)) := by
    clear * - f1666
    grind (splits := 100) only
  have s107 : ((¬ spl0_4) ∨ (¬ spl0_25)) := by
    clear * - f1703
    grind (splits := 100) only
  have s109 : ((¬ spl0_4) ∨ (¬ spl0_24)) := by
    clear * - f1751
    grind (splits := 100) only
  have s110 : ((¬ spl0_4) ∨ (¬ spl0_23)) := by
    clear * - f1761
    grind (splits := 100) only
  have s119 : ((¬ spl0_4) ∨ (¬ spl0_22)) := by
    clear * - f1943
    grind (splits := 100) only
  have s123 : ((¬ spl0_4) ∨ (¬ spl0_21)) := by
    clear * - f2018
    grind (splits := 100) only
  have s154 : ((¬ spl0_4) ∨ (¬ spl0_20)) := by
    clear * - f2458
    grind (splits := 100) only
  have s155 : ((¬ spl0_4) ∨ (¬ spl0_19)) := by
    clear * - f2466
    grind (splits := 100) only
  have s157 : ((¬ spl0_3) ∨ (¬ spl0_19)) := by
    clear * - f2502
    grind (splits := 100) only
  have s158 : ((¬ spl0_3) ∨ (¬ spl0_25)) := by
    clear * - f2510
    grind (splits := 100) only
  have s160 : ((¬ spl0_3) ∨ (¬ spl0_24)) := by
    clear * - f2572
    grind (splits := 100) only
  have s162 : ((¬ spl0_3) ∨ (¬ spl0_23)) := by
    clear * - f2614
    grind (splits := 100) only
  have s195 : ((¬ spl0_3) ∨ (¬ spl0_22)) := by
    clear * - f3200
    grind (splits := 100) only
  have s225 : ((¬ spl0_3) ∨ (¬ spl0_21)) := by
    clear * - f3788
    grind (splits := 100) only
  have s226 : ((¬ spl0_3) ∨ (¬ spl0_20)) := by
    clear * - f3873
    grind (splits := 100) only
  have s227 : ((¬ spl0_2) ∨ (spl0_11 ∨ (spl0_12 ∨ spl0_16))) := by
    clear * - s5 s10 s15 s14 s13
    grind (splits := 100) only
  have s228 : (spl0_2 ∨ (spl0_3 ∨ (spl0_4 ∨ (spl0_5 ∨ (spl0_6 ∨ (spl0_7 ∨ spl0_8)))))) := by
    clear * - s1 s3
    grind (splits := 100) only
  have s229 : (¬ spl0_8) := by
    clear * - s16 s17 s18 s19 s20 s21 s22 s23 s24
    grind (splits := 100) only
  have s230 : (¬ spl0_7) := by
    clear * - s16 s38 s39 s41 s42 s43 s44 s45 s46
    grind (splits := 100) only
  have s231 : (¬ spl0_6) := by
    clear * - s16 s36 s47 s49 s50 s52 s54 s55 s56
    grind (splits := 100) only
  have s232 : ((¬ spl0_21) ∨ (¬ spl0_5)) := by
    clear * - s69 s70 s73
    grind (splits := 100) only
  have s233 : (¬ spl0_5) := by
    clear * - s102 s103 s16 s232 s33 s58 s60 s61 s63 s73 s104
    grind (splits := 100) only
  have s234 : (¬ spl0_4) := by
    clear * - s16 s28 s107 s109 s110 s119 s123 s154 s155
    grind (splits := 100) only
  have s235 : (¬ spl0_3) := by
    clear * - s16 s26 s157 s158 s160 s162 s195 s225 s226
    grind (splits := 100) only
  have s236 : spl0_2 := by
    clear * - s228 s230 s233 s231 s229 s234 s235
    grind (splits := 100) only
  have s237 : (¬ spl0_16) := by
    clear * - s12 s236
    grind (splits := 100) only
  have s238 : (¬ spl0_12) := by
    clear * - s11 s236
    grind (splits := 100) only
  have s239 : (¬ spl0_11) := by
    clear * - s9 s236
    grind (splits := 100) only
  have s240 : False := by
    clear * - s227 s237 s238 s239 s236
    grind (splits := 100) only
  exact s240


set_option maxHeartbeats 8000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X0 X4 ∨ old X2 X4 X0)) (old_2 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X1 ∨ X0 = X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X1, c ≠ Y ∨ b ≠ Z ∨ ¬ old b b X1 ∨ ¬ old X1 X a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old b a a ∨ ¬sP2 X Y Z) (rule_def_2_5 : ∀ (X Y Z : G), old b b b ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b Z a ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z X3 X6, c ≠ X ∨ ¬ old b b X3 ∨ ¬ old b Z Y ∨ ¬ old X3 X6 a ∨ ¬ old Z Z X6 ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a (sF4 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_4 : ∀ (X Y Z : G), old (sF4 X Y Z) (sF5 X Y Z) (sF3 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_5 : ∀ (X Y Z : G), old b b (sF5 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_4 : ∀ (X Y Z : G), old a a (sF6 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X0 X1 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X0 X4 ∨ new X2 X4 X0) := by
  classical
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have f1 : (a ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using ac
  have f2 : (b ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using bc
  have f3 : (∀ (X0 : G), (¬ (old a b X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p3
  have f4 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XY
  have f5 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XZ
  have f6 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4YZ
  have f8 : (∀ (X0 X1 X2 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X2 X2 X1)) ∨ (X0 = X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_2
  have f9 : (∀ (X0 X1 X2 X3 X4 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X1 X2 X3)) ∨ ((¬ (old X3 X0 X4)) ∨ (old X2 X4 X0))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_1
  have f20 : (∀ (X0 X1 X2 : G), ((¬ (old X0 X1 X2)) ∨ (new X0 X1 X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using imp_new_0
  have f22 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_0
  have f23 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_1
  have f24 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_2
  have f25 : (∀ (X0 X1 X2 X3 : G), ((c ≠ X1) ∨ ((b ≠ X2) ∨ ((¬ (old b b X3)) ∨ ((¬ (old X3 X0 a)) ∨ (new X0 X1 X2)))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using imp_new_2
  have f26 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_0
  have f27 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_1
  have f28 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old b b (sF0 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_2
  have f29 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_3
  have f31 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_0
  have f32 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_1
  have f33 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_2
  have f34 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old a a a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_3
  have f35 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b a a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_4
  have f36 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_5
  have f38 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_0
  have f39 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_1
  have f40 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_2
  have f41 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b X2 a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_3
  have f43 : (∀ (X0 X1 X2 X3 X4 : G), ((c ≠ X0) ∨ ((¬ (old b b X3)) ∨ ((¬ (old b X2 X1)) ∨ ((¬ (old X3 X4 a)) ∨ ((¬ (old X2 X2 X4)) ∨ (new X0 X1 X2))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using imp_new_5
  have f44 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_0
  have f45 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_1
  have f46 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_2
  have f50 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_0
  have f51 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_1
  have f52 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_2
  have f53 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old a a (sF4 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_3
  have f54 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF4 X0 X1 X2) (sF5 X0 X1 X2) (sF3 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_4
  have f55 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old b b (sF5 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_5
  have f57 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_0
  have f61 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old a a (sF6 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_4
  have f65 : (∀ (X0 X1 X2 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using new_imp
  have f66 : (new sk0 sk0 sk1) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_0
  have f67 : (new sk1 sk2 sk3) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_1
  have f68 : (new sk3 sk0 sk4) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_2
  have f69 : (¬ (new sk2 sk4 sk0)) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_3
  have f70 : (a ≠ c) := by
    clear * - f1
    grind (instances := 3000) only
  have f71 : (c ≠ b) := by
    clear * - f2
    grind (instances := 3000) only
  have f72 : (∀ (X0 : G), (¬ (old a b X0))) := by
    clear * - f3
    grind (instances := 3000) only
  have f73 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by
    clear * - f4
    grind (instances := 3000) only
  have f74 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by
    clear * - f5
    grind (instances := 3000) only
  have f75 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by
    clear * - f6
    grind (instances := 3000) only
  have f77 : (∀ (X2 X0 X1 : G), ((¬ (old X2 X2 X1)) ∨ ((¬ (old X0 X0 X1)) ∨ (X0 = X2)))) := by
    clear * - f8
    grind (instances := 3000) only
  have f78 : (∀ (X2 X3 X0 X1 X4 : G), ((¬ (old X3 X0 X4)) ∨ ((¬ (old X1 X2 X3)) ∨ ((¬ (old X0 X0 X1)) ∨ (old X2 X4 X0))))) := by
    clear * - f9
    grind (instances := 3000) only
  have f89 : (∀ (X2 X0 X1 : G), ((¬ (old X0 X1 X2)) ∨ (new X0 X1 X2))) := by
    clear * - f20
    grind (instances := 3000) only
  have f91 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by
    clear * - f22
    grind (instances := 3000) only
  have f92 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by
    clear * - f23
    grind (instances := 3000) only
  have f93 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by
    clear * - f24
    grind (instances := 3000) only
  have f94 : (∀ (X2 X3 X0 X1 : G), ((c ≠ X1) ∨ ((b ≠ X2) ∨ ((¬ (old b b X3)) ∨ ((¬ (old X3 X0 a)) ∨ (new X0 X1 X2)))))) := by
    clear * - f25
    grind (instances := 3000) only
  have f95 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f26
    grind (instances := 3000) only
  have f96 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f27
    grind (instances := 3000) only
  have f97 : (∀ (X2 X0 X1 : G), ((old b b (sF0 X0 X1 X2)) ∨ (¬ (sP1 X0 X1 X2)))) := by
    clear * - f28
    grind (instances := 3000) only
  have f98 : (∀ (X2 X0 X1 : G), ((old (sF0 X0 X1 X2) X0 a) ∨ (¬ (sP1 X0 X1 X2)))) := by
    clear * - f29
    grind (instances := 3000) only
  have f100 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f31
    grind (instances := 3000) only
  have f101 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f32
    grind (instances := 3000) only
  have f102 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by
    clear * - f33
    grind (instances := 3000) only
  have f103 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old a a a))) := by
    clear * - f34
    grind (instances := 3000) only
  have f104 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b a a))) := by
    clear * - f35
    grind (instances := 3000) only
  have f105 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f36
    grind (instances := 3000) only
  have f107 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f38
    grind (instances := 3000) only
  have f108 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f39
    grind (instances := 3000) only
  have f109 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f40
    grind (instances := 3000) only
  have f110 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b X2 a))) := by
    clear * - f41
    grind (instances := 3000) only
  have f112 : (∀ (X2 X3 X0 X1 X4 : G), ((c ≠ X0) ∨ ((¬ (old b b X3)) ∨ ((¬ (old b X2 X1)) ∨ ((¬ (old X3 X4 a)) ∨ ((¬ (old X2 X2 X4)) ∨ (new X0 X1 X2))))))) := by
    clear * - f43
    grind (instances := 3000) only
  have f113 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f44
    grind (instances := 3000) only
  have f114 : (∀ (X2 X0 X1 : G), ((old b b (sF1 X0 X1 X2)) ∨ (¬ (sP4 X0 X1 X2)))) := by
    clear * - f45
    grind (instances := 3000) only
  have f115 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by
    clear * - f46
    grind (instances := 3000) only
  have f119 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f50
    grind (instances := 3000) only
  have f120 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f51
    grind (instances := 3000) only
  have f121 : (∀ (X2 X0 X1 : G), ((old (sF3 X0 X1 X2) a X0) ∨ (¬ (sP5 X0 X1 X2)))) := by
    clear * - f52
    grind (instances := 3000) only
  have f122 : (∀ (X2 X0 X1 : G), ((old a a (sF4 X0 X1 X2)) ∨ (¬ (sP5 X0 X1 X2)))) := by
    clear * - f53
    grind (instances := 3000) only
  have f123 : (∀ (X2 X0 X1 : G), ((old (sF4 X0 X1 X2) (sF5 X0 X1 X2) (sF3 X0 X1 X2)) ∨ (¬ (sP5 X0 X1 X2)))) := by
    clear * - f54
    grind (instances := 3000) only
  have f124 : (∀ (X2 X0 X1 : G), ((old b b (sF5 X0 X1 X2)) ∨ (¬ (sP5 X0 X1 X2)))) := by
    clear * - f55
    grind (instances := 3000) only
  have f126 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by
    clear * - f57
    grind (instances := 3000) only
  have f130 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old a a (sF6 X0 X1 X2)))) := by
    clear * - f61
    grind (instances := 3000) only
  have f134 : (∀ (X2 X0 X1 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by
    clear * - f65
    grind (instances := 3000) only
  have f135 : (new sk0 sk0 sk1) := by
    clear * - f66
    grind (instances := 3000) only
  have f136 : (new sk1 sk2 sk3) := by
    clear * - f67
    grind (instances := 3000) only
  have f137 : (new sk3 sk0 sk4) := by
    clear * - f68
    grind (instances := 3000) only
  have f138 : (¬ (new sk2 sk4 sk0)) := by
    clear * - f69
    grind (instances := 3000) only
  have f142 : (∀ (X2 X3 X0 : G), ((b ≠ X2) ∨ ((¬ (old b b X3)) ∨ ((¬ (old X3 X0 a)) ∨ (new X0 c X2))))) := by
    clear * - f94
    grind (instances := 3000) only
  have f143 : (∀ (X3 X0 : G), ((¬ (old b b X3)) ∨ ((¬ (old X3 X0 a)) ∨ (new X0 c b)))) := by
    clear * - f142
    grind (instances := 3000) only
  have f149 : (∀ (X2 X3 X1 X4 : G), ((¬ (old b b X3)) ∨ ((¬ (old b X2 X1)) ∨ ((¬ (old X3 X4 a)) ∨ ((¬ (old X2 X2 X4)) ∨ (new c X1 X2)))))) := by
    clear * - f112
    grind (instances := 3000) only
  let spl0_1 : Prop := (a = b)
  have f156 : (spl0_1 ↔ (a = b)) := Iff.rfl
  clear_value spl0_1
  have f157 : ((a ≠ b) ∨ spl0_1) := by
    clear * - f156
    grind (instances := 3000) only
  have f158 : ((a = b) ∨ (¬ spl0_1)) := by
    clear * - f156
    grind (instances := 3000) only
  let spl0_2 : Prop := (∀ (X2 X0 X1 : G), (¬ (sP6 X0 X1 X2)))
  have f160 : (spl0_2 ↔ (∀ (X2 X0 X1 : G), (¬ (sP6 X0 X1 X2)))) := Iff.rfl
  clear_value spl0_2
  have f161 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (¬ spl0_2))) := by
    clear * - f160
    grind (instances := 3000) only
  have f162 : (spl0_1 ∨ spl0_2) := by
    clear * - f126 f160 f156
    grind (instances := 3000) only
  let spl0_3 : Prop := (new c c b)
  have f164 : (spl0_3 ↔ (new c c b)) := Iff.rfl
  clear_value spl0_3
  have f165 : ((¬ (new c c b)) ∨ spl0_3) := by
    clear * - f164
    grind (instances := 3000) only
  have f166 : ((new c c b) ∨ (¬ spl0_3)) := by
    clear * - f164
    grind (instances := 3000) only
  let spl0_5 : Prop := (old b b b)
  have f172 : (spl0_5 ↔ (old b b b)) := Iff.rfl
  clear_value spl0_5
  have f174 : ((old b b b) ∨ (¬ spl0_5)) := by
    clear * - f172
    grind (instances := 3000) only
  let spl0_6 : Prop := (∀ (X2 X0 X1 : G), (¬ (sP3 X0 X1 X2)))
  have f176 : (spl0_6 ↔ (∀ (X2 X0 X1 : G), (¬ (sP3 X0 X1 X2)))) := Iff.rfl
  clear_value spl0_6
  have f177 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (¬ spl0_6))) := by
    clear * - f176
    grind (instances := 3000) only
  have f178 : (spl0_5 ∨ spl0_6) := by
    clear * - f109 f176 f172
    grind (instances := 3000) only
  let spl0_8 : Prop := (∀ (X2 X0 X1 : G), (¬ (sP2 X0 X1 X2)))
  have f184 : (spl0_8 ↔ (∀ (X2 X0 X1 : G), (¬ (sP2 X0 X1 X2)))) := Iff.rfl
  clear_value spl0_8
  have f185 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (¬ spl0_8))) := by
    clear * - f184
    grind (instances := 3000) only
  have f186 : (spl0_5 ∨ spl0_8) := by
    clear * - f105 f184 f172
    grind (instances := 3000) only
  let spl0_9 : Prop := (old b a a)
  have f188 : (spl0_9 ↔ (old b a a)) := Iff.rfl
  clear_value spl0_9
  have f190 : ((old b a a) ∨ (¬ spl0_9)) := by
    clear * - f188
    grind (instances := 3000) only
  have f191 : (spl0_9 ∨ spl0_8) := by
    clear * - f104 f184 f188
    grind (instances := 3000) only
  let spl0_10 : Prop := (old a a a)
  have f193 : (spl0_10 ↔ (old a a a)) := Iff.rfl
  clear_value spl0_10
  have f195 : ((old a a a) ∨ (¬ spl0_10)) := by
    clear * - f193
    grind (instances := 3000) only
  have f196 : (spl0_10 ∨ spl0_8) := by
    clear * - f103 f184 f193
    grind (instances := 3000) only
  have f202 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ (sP5 X0 X1 X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f134 f161
    grind (instances := 3000) only
  have f203 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ (sP5 X0 X1 X2))))))) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))) := by
    clear * - f202 f185
    first | exact resolve f202 f185 | exact resolve f185 f202 | grind (instances := 3000) only
  let spl0_12 : Prop := (sP5 sk3 sk0 sk4)
  have f209 : (spl0_12 ↔ (sP5 sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_12
  have f210 : ((¬ (sP5 sk3 sk0 sk4)) ∨ spl0_12) := by
    clear * - f209
    grind (instances := 3000) only
  have f211 : ((sP5 sk3 sk0 sk4) ∨ (¬ spl0_12)) := by
    clear * - f209
    grind (instances := 3000) only
  let spl0_13 : Prop := (sP4 sk3 sk0 sk4)
  have f213 : (spl0_13 ↔ (sP4 sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_13
  have f214 : ((¬ (sP4 sk3 sk0 sk4)) ∨ spl0_13) := by
    clear * - f213
    grind (instances := 3000) only
  have f215 : ((sP4 sk3 sk0 sk4) ∨ (¬ spl0_13)) := by
    clear * - f213
    grind (instances := 3000) only
  let spl0_14 : Prop := (sP1 sk3 sk0 sk4)
  have f217 : (spl0_14 ↔ (sP1 sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_14
  have f218 : ((¬ (sP1 sk3 sk0 sk4)) ∨ spl0_14) := by
    clear * - f217
    grind (instances := 3000) only
  have f219 : ((sP1 sk3 sk0 sk4) ∨ (¬ spl0_14)) := by
    clear * - f217
    grind (instances := 3000) only
  let spl0_15 : Prop := (sP0 sk3 sk0 sk4)
  have f221 : (spl0_15 ↔ (sP0 sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_15
  have f222 : ((¬ (sP0 sk3 sk0 sk4)) ∨ spl0_15) := by
    clear * - f221
    grind (instances := 3000) only
  have f223 : ((sP0 sk3 sk0 sk4) ∨ (¬ spl0_15)) := by
    clear * - f221
    grind (instances := 3000) only
  let spl0_16 : Prop := (old sk3 sk0 sk4)
  have f225 : (spl0_16 ↔ (old sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_16
  have f227 : ((old sk3 sk0 sk4) ∨ (¬ spl0_16)) := by
    clear * - f225
    grind (instances := 3000) only
  let spl0_17 : Prop := (sP5 sk1 sk2 sk3)
  have f230 : (spl0_17 ↔ (sP5 sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_17
  have f231 : ((¬ (sP5 sk1 sk2 sk3)) ∨ spl0_17) := by
    clear * - f230
    grind (instances := 3000) only
  have f232 : ((sP5 sk1 sk2 sk3) ∨ (¬ spl0_17)) := by
    clear * - f230
    grind (instances := 3000) only
  let spl0_18 : Prop := (sP4 sk1 sk2 sk3)
  have f234 : (spl0_18 ↔ (sP4 sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_18
  have f235 : ((¬ (sP4 sk1 sk2 sk3)) ∨ spl0_18) := by
    clear * - f234
    grind (instances := 3000) only
  have f236 : ((sP4 sk1 sk2 sk3) ∨ (¬ spl0_18)) := by
    clear * - f234
    grind (instances := 3000) only
  let spl0_19 : Prop := (sP1 sk1 sk2 sk3)
  have f238 : (spl0_19 ↔ (sP1 sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_19
  have f239 : ((¬ (sP1 sk1 sk2 sk3)) ∨ spl0_19) := by
    clear * - f238
    grind (instances := 3000) only
  have f240 : ((sP1 sk1 sk2 sk3) ∨ (¬ spl0_19)) := by
    clear * - f238
    grind (instances := 3000) only
  let spl0_20 : Prop := (sP0 sk1 sk2 sk3)
  have f242 : (spl0_20 ↔ (sP0 sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_20
  have f243 : ((¬ (sP0 sk1 sk2 sk3)) ∨ spl0_20) := by
    clear * - f242
    grind (instances := 3000) only
  have f244 : ((sP0 sk1 sk2 sk3) ∨ (¬ spl0_20)) := by
    clear * - f242
    grind (instances := 3000) only
  let spl0_21 : Prop := (old sk1 sk2 sk3)
  have f246 : (spl0_21 ↔ (old sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_21
  have f247 : ((¬ (old sk1 sk2 sk3)) ∨ spl0_21) := by
    clear * - f246
    grind (instances := 3000) only
  have f248 : ((old sk1 sk2 sk3) ∨ (¬ spl0_21)) := by
    clear * - f246
    grind (instances := 3000) only
  let spl0_22 : Prop := (sP5 sk0 sk0 sk1)
  have f251 : (spl0_22 ↔ (sP5 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_22
  have f252 : ((¬ (sP5 sk0 sk0 sk1)) ∨ spl0_22) := by
    clear * - f251
    grind (instances := 3000) only
  have f253 : ((sP5 sk0 sk0 sk1) ∨ (¬ spl0_22)) := by
    clear * - f251
    grind (instances := 3000) only
  let spl0_23 : Prop := (sP4 sk0 sk0 sk1)
  have f255 : (spl0_23 ↔ (sP4 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_23
  have f257 : ((sP4 sk0 sk0 sk1) ∨ (¬ spl0_23)) := by
    clear * - f255
    grind (instances := 3000) only
  let spl0_24 : Prop := (sP1 sk0 sk0 sk1)
  have f259 : (spl0_24 ↔ (sP1 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_24
  have f261 : ((sP1 sk0 sk0 sk1) ∨ (¬ spl0_24)) := by
    clear * - f259
    grind (instances := 3000) only
  let spl0_25 : Prop := (sP0 sk0 sk0 sk1)
  have f263 : (spl0_25 ↔ (sP0 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_25
  have f265 : ((sP0 sk0 sk0 sk1) ∨ (¬ spl0_25)) := by
    clear * - f263
    grind (instances := 3000) only
  let spl0_26 : Prop := (old sk0 sk0 sk1)
  have f267 : (spl0_26 ↔ (old sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_26
  have f268 : ((¬ (old sk0 sk0 sk1)) ∨ spl0_26) := by
    clear * - f267
    grind (instances := 3000) only
  have f269 : ((old sk0 sk0 sk1) ∨ (¬ spl0_26)) := by
    clear * - f267
    grind (instances := 3000) only
  have f271 : ((old sk0 sk0 sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f203 f135
    first | exact resolve f203 f135 | exact resolve f135 f203 | grind (instances := 3000) only
  have f273 : ((old sk3 sk0 sk4) ∨ ((sP0 sk3 sk0 sk4) ∨ ((sP1 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f203 f137
    first | exact resolve f203 f137 | exact resolve f137 f203 | grind (instances := 3000) only
  let spl0_27 : Prop := (sP3 sk3 sk0 sk4)
  have f275 : (spl0_27 ↔ (sP3 sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_27
  have f276 : ((¬ (sP3 sk3 sk0 sk4)) ∨ spl0_27) := by
    clear * - f275
    grind (instances := 3000) only
  have f277 : ((sP3 sk3 sk0 sk4) ∨ (¬ spl0_27)) := by
    clear * - f275
    grind (instances := 3000) only
  have f278 : (spl0_12 ∨ (spl0_13 ∨ (spl0_27 ∨ (spl0_14 ∨ (spl0_15 ∨ (spl0_16 ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f273 f184 f160 f225 f221 f217 f275 f213 f209
    grind (instances := 3000) only
  let spl0_28 : Prop := (sP3 sk1 sk2 sk3)
  have f280 : (spl0_28 ↔ (sP3 sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_28
  have f281 : ((¬ (sP3 sk1 sk2 sk3)) ∨ spl0_28) := by
    clear * - f280
    grind (instances := 3000) only
  have f282 : ((sP3 sk1 sk2 sk3) ∨ (¬ spl0_28)) := by
    clear * - f280
    grind (instances := 3000) only
  let spl0_29 : Prop := (sP3 sk0 sk0 sk1)
  have f285 : (spl0_29 ↔ (sP3 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_29
  have f286 : ((¬ (sP3 sk0 sk0 sk1)) ∨ spl0_29) := by
    clear * - f285
    grind (instances := 3000) only
  have f287 : ((sP3 sk0 sk0 sk1) ∨ (¬ spl0_29)) := by
    clear * - f285
    grind (instances := 3000) only
  have f288 : (spl0_22 ∨ (spl0_23 ∨ (spl0_29 ∨ (spl0_24 ∨ (spl0_25 ∨ (spl0_26 ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f271 f184 f160 f267 f263 f259 f285 f255 f251
    grind (instances := 3000) only
  have f292 : ((old sk0 sk0 sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP2 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ (¬ spl0_2)))))))) := by
    clear * - f202 f135
    first | exact resolve f202 f135 | exact resolve f135 f202 | grind (instances := 3000) only
  have f293 : ((old sk1 sk2 sk3) ∨ ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((sP2 sk1 sk2 sk3) ∨ ((sP3 sk1 sk2 sk3) ∨ ((sP4 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ (¬ spl0_2)))))))) := by
    clear * - f202 f136
    first | exact resolve f202 f136 | exact resolve f136 f202 | grind (instances := 3000) only
  have f294 : ((old sk3 sk0 sk4) ∨ ((sP0 sk3 sk0 sk4) ∨ ((sP1 sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ (¬ spl0_2)))))))) := by
    clear * - f202 f137
    first | exact resolve f202 f137 | exact resolve f137 f202 | grind (instances := 3000) only
  let spl0_30 : Prop := (sP2 sk3 sk0 sk4)
  have f296 : (spl0_30 ↔ (sP2 sk3 sk0 sk4)) := Iff.rfl
  clear_value spl0_30
  have f297 : ((¬ (sP2 sk3 sk0 sk4)) ∨ spl0_30) := by
    clear * - f296
    grind (instances := 3000) only
  have f298 : ((sP2 sk3 sk0 sk4) ∨ (¬ spl0_30)) := by
    clear * - f296
    grind (instances := 3000) only
  have f299 : (spl0_12 ∨ (spl0_13 ∨ (spl0_27 ∨ (spl0_30 ∨ (spl0_14 ∨ (spl0_15 ∨ (spl0_16 ∨ (¬ spl0_2)))))))) := by
    clear * - f294 f160 f225 f221 f217 f296 f275 f213 f209
    grind (instances := 3000) only
  let spl0_31 : Prop := (sP2 sk1 sk2 sk3)
  have f301 : (spl0_31 ↔ (sP2 sk1 sk2 sk3)) := Iff.rfl
  clear_value spl0_31
  have f303 : ((sP2 sk1 sk2 sk3) ∨ (¬ spl0_31)) := by
    clear * - f301
    grind (instances := 3000) only
  have f304 : (spl0_17 ∨ (spl0_18 ∨ (spl0_28 ∨ (spl0_31 ∨ (spl0_19 ∨ (spl0_20 ∨ (spl0_21 ∨ (¬ spl0_2)))))))) := by
    clear * - f293 f160 f246 f242 f238 f301 f280 f234 f230
    grind (instances := 3000) only
  let spl0_32 : Prop := (sP2 sk0 sk0 sk1)
  have f306 : (spl0_32 ↔ (sP2 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_32
  have f308 : ((sP2 sk0 sk0 sk1) ∨ (¬ spl0_32)) := by
    clear * - f306
    grind (instances := 3000) only
  have f309 : (spl0_22 ∨ (spl0_23 ∨ (spl0_29 ∨ (spl0_32 ∨ (spl0_24 ∨ (spl0_25 ∨ (spl0_26 ∨ (¬ spl0_2)))))))) := by
    clear * - f292 f160 f267 f263 f259 f306 f285 f255 f251
    grind (instances := 3000) only
  have f363 : (∀ (X2 X0 X1 : G), (((old b b (sF6 X0 X1 X2)) ∨ (¬ (sP6 X0 X1 X2))) ∨ (¬ spl0_1))) := by
    clear * - f130 f158
    grind (instances := 3000) only
  have f364 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_1))) := by
    clear * - f72 f158
    first | exact superpose f72 f158 | exact superpose f158 f72 | grind (instances := 3000) only
  have f370 : (False ∨ ((¬ spl0_1) ∨ (¬ spl0_5))) := by
    clear * - f174 f364
    grind (instances := 3000) only
  have f374 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (¬ spl0_1))) := by
    clear * - f363 f364
    grind (instances := 3000) only
  have f376 : ((¬ spl0_1) ∨ (¬ spl0_5)) := by
    clear * - f370
    grind (instances := 3000) only
  have f378 : (spl0_2 ∨ (¬ spl0_1)) := by
    clear * - f374 f156 f160
    grind (instances := 3000) only
  have f381 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))) ∨ (¬ spl0_8))) := by
    clear * - f134 f185
    first | exact resolve f134 f185 | exact resolve f185 f134 | grind (instances := 3000) only
  have f382 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ (sP5 X0 X1 X2))))))) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))) := by
    clear * - f381 f161
    first | exact resolve f381 f161 | exact resolve f161 f381 | grind (instances := 3000) only
  have f383 : ((c = sk4) ∨ (¬ spl0_15)) := by
    clear * - f223 f93
    first | exact resolve f223 f93 | exact resolve f93 f223 | grind (instances := 3000) only
  have f384 : ((b = sk0) ∨ (¬ spl0_15)) := by
    clear * - f223 f92
    first | exact resolve f223 f92 | exact resolve f92 f223 | grind (instances := 3000) only
  have f385 : ((a = sk3) ∨ (¬ spl0_15)) := by
    clear * - f223 f91
    first | exact resolve f223 f91 | exact resolve f91 f223 | grind (instances := 3000) only
  have f390 : ((old sk0 sk0 sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f382 f135
    first | exact resolve f382 f135 | exact resolve f135 f382 | grind (instances := 3000) only
  have f392 : ((old sk3 sk0 sk4) ∨ ((sP0 sk3 sk0 sk4) ∨ ((sP1 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f382 f137
    first | exact resolve f382 f137 | exact resolve f137 f382 | grind (instances := 3000) only
  let spl0_46 : Prop := (sP4 c c b)
  have f399 : (spl0_46 ↔ (sP4 c c b)) := Iff.rfl
  clear_value spl0_46
  have f400 : ((¬ (sP4 c c b)) ∨ spl0_46) := by
    clear * - f399
    grind (instances := 3000) only
  have f401 : ((sP4 c c b) ∨ (¬ spl0_46)) := by
    clear * - f399
    grind (instances := 3000) only
  let spl0_47 : Prop := (sP3 c c b)
  have f403 : (spl0_47 ↔ (sP3 c c b)) := Iff.rfl
  clear_value spl0_47
  have f404 : ((¬ (sP3 c c b)) ∨ spl0_47) := by
    clear * - f403
    grind (instances := 3000) only
  have f405 : ((sP3 c c b) ∨ (¬ spl0_47)) := by
    clear * - f403
    grind (instances := 3000) only
  let spl0_49 : Prop := (sP0 c c b)
  have f411 : (spl0_49 ↔ (sP0 c c b)) := Iff.rfl
  clear_value spl0_49
  have f412 : ((¬ (sP0 c c b)) ∨ spl0_49) := by
    clear * - f411
    grind (instances := 3000) only
  have f413 : ((sP0 c c b) ∨ (¬ spl0_49)) := by
    clear * - f411
    grind (instances := 3000) only
  have f415 : ((c = sk1) ∨ (¬ spl0_18)) := by
    clear * - f236 f113
    first | exact resolve f236 f113 | exact resolve f113 f236 | grind (instances := 3000) only
  have f418 : ((b = sk1) ∨ (¬ spl0_22)) := by
    clear * - f253 f120
    first | exact resolve f253 f120 | exact resolve f120 f253 | grind (instances := 3000) only
  have f419 : ((c = sk0) ∨ (¬ spl0_22)) := by
    clear * - f253 f119
    first | exact resolve f253 f119 | exact resolve f119 f253 | grind (instances := 3000) only
  have f426 : ((c = sk0) ∨ (¬ spl0_14)) := by
    clear * - f219 f95
    first | exact resolve f219 f95 | exact resolve f95 f219 | grind (instances := 3000) only
  have f440 : (∀ (X0 X1 : G), (¬ (sP1 c X0 X1))) := by
    clear * - f98 f74
    first | exact resolve f98 f74 | exact resolve f74 f98 | grind (instances := 3000) only
  have f474 : (∀ (X0 X1 : G), (¬ (sP5 c X0 X1))) := by
    clear * - f121 f73
    first | exact resolve f121 f73 | exact resolve f73 f121 | grind (instances := 3000) only
  have f490 : ((sP4 c sk2 sk3) ∨ (¬ spl0_18)) := by
    clear * - f236 f415
    first | exact superpose f236 f415 | exact superpose f415 f236 | grind (instances := 3000) only
  have f498 : ((old sk0 sk0 c) ∨ ((¬ spl0_18) ∨ (¬ spl0_26))) := by
    clear * - f269 f415
    grind (instances := 3000) only
  have f502 : (False ∨ ((¬ spl0_18) ∨ (¬ spl0_26))) := by
    clear * - f498 f73
    first | exact resolve f498 f73 | exact resolve f73 f498 | grind (instances := 3000) only
  have f503 : ((¬ spl0_18) ∨ (¬ spl0_26)) := by
    clear * - f502
    grind (instances := 3000) only
  have f527 : ((old c c sk1) ∨ ((¬ spl0_14) ∨ (¬ spl0_26))) := by
    clear * - f269 f426
    grind (instances := 3000) only
  have f528 : ((old c c sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14))))))))) := by
    clear * - f390 f426
    grind (instances := 3000) only
  have f529 : (False ∨ ((¬ spl0_14) ∨ (¬ spl0_26))) := by
    clear * - f527 f74
    first | exact resolve f527 f74 | exact resolve f74 f527 | grind (instances := 3000) only
  have f530 : ((¬ spl0_14) ∨ (¬ spl0_26)) := by
    clear * - f529
    grind (instances := 3000) only
  have f531 : ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14)))))))) := by
    clear * - f528 f74
    first | exact resolve f528 f74 | exact resolve f74 f528 | grind (instances := 3000) only
  have f532 : ((sP0 c c sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14)))))))) := by
    clear * - f531 f426
    grind (instances := 3000) only
  have f533 : ((sP1 c c sk1) ∨ ((sP0 c c sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14)))))))) := by
    clear * - f532 f426
    grind (instances := 3000) only
  have f534 : ((sP0 c c sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14))))))) := by
    clear * - f533 f440
    first | exact resolve f533 f440 | exact resolve f440 f533 | grind (instances := 3000) only
  have f535 : ((sP3 c c sk1) ∨ ((sP0 c c sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14))))))) := by
    clear * - f534 f426
    grind (instances := 3000) only
  have f536 : ((sP4 c c sk1) ∨ ((sP3 c c sk1) ∨ ((sP0 c c sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14))))))) := by
    clear * - f535 f426
    grind (instances := 3000) only
  have f537 : ((sP5 c c sk1) ∨ ((sP4 c c sk1) ∨ ((sP3 c c sk1) ∨ ((sP0 c c sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14))))))) := by
    clear * - f536 f426
    grind (instances := 3000) only
  have f538 : ((sP4 c c sk1) ∨ ((sP3 c c sk1) ∨ ((sP0 c c sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14)))))) := by
    clear * - f537 f474
    first | exact resolve f537 f474 | exact resolve f474 f537 | grind (instances := 3000) only
  let spl0_52 : Prop := (sP0 c c sk1)
  have f540 : (spl0_52 ↔ (sP0 c c sk1)) := Iff.rfl
  clear_value spl0_52
  have f541 : ((¬ (sP0 c c sk1)) ∨ spl0_52) := by
    clear * - f540
    grind (instances := 3000) only
  have f542 : ((sP0 c c sk1) ∨ (¬ spl0_52)) := by
    clear * - f540
    grind (instances := 3000) only
  let spl0_53 : Prop := (sP3 c c sk1)
  have f544 : (spl0_53 ↔ (sP3 c c sk1)) := Iff.rfl
  clear_value spl0_53
  have f545 : ((¬ (sP3 c c sk1)) ∨ spl0_53) := by
    clear * - f544
    grind (instances := 3000) only
  have f546 : ((sP3 c c sk1) ∨ (¬ spl0_53)) := by
    clear * - f544
    grind (instances := 3000) only
  let spl0_54 : Prop := (sP4 c c sk1)
  have f548 : (spl0_54 ↔ (sP4 c c sk1)) := Iff.rfl
  clear_value spl0_54
  have f549 : ((¬ (sP4 c c sk1)) ∨ spl0_54) := by
    clear * - f548
    grind (instances := 3000) only
  have f550 : ((sP4 c c sk1) ∨ (¬ spl0_54)) := by
    clear * - f548
    grind (instances := 3000) only
  have f551 : (spl0_52 ∨ (spl0_53 ∨ (spl0_54 ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14)))))) := by
    clear * - f538 f217 f184 f160 f548 f544 f540
    grind (instances := 3000) only
  have f555 : (∀ (X2 X3 X0 X1 : G), ((¬ (old (sF5 X0 X1 X2) X3 a)) ∨ ((new X3 c b) ∨ (¬ (sP5 X0 X1 X2))))) := by
    clear * - f143 f124
    first | exact resolve f143 f124 | exact resolve f124 f143 | grind (instances := 3000) only
  have f559 : ((b = sk3) ∨ (¬ spl0_17)) := by
    clear * - f232 f120
    first | exact resolve f232 f120 | exact resolve f120 f232 | grind (instances := 3000) only
  have f560 : ((c = sk2) ∨ (¬ spl0_17)) := by
    clear * - f232 f119
    first | exact resolve f232 f119 | exact resolve f119 f232 | grind (instances := 3000) only
  have f570 : (∀ (X2 X3 X0 X1 X4 : G), ((¬ (old X0 X1 (sF3 X2 X3 X4))) ∨ ((¬ (old a a X0)) ∨ ((old X1 X2 a) ∨ (¬ (sP5 X2 X3 X4)))))) := by
    clear * - f78 f121
    first | exact resolve f78 f121 | exact resolve f121 f78 | grind (instances := 3000) only
  have f585 : ((old b sk4 a) ∨ (¬ spl0_27)) := by
    clear * - f277 f110
    first | exact resolve f277 f110 | exact resolve f110 f277 | grind (instances := 3000) only
  have f586 : ((a = sk0) ∨ (¬ spl0_27)) := by
    clear * - f277 f108
    first | exact resolve f277 f108 | exact resolve f108 f277 | grind (instances := 3000) only
  have f587 : ((c = sk3) ∨ (¬ spl0_27)) := by
    clear * - f277 f107
    first | exact resolve f277 f107 | exact resolve f107 f277 | grind (instances := 3000) only
  have f588 : ((c = b) ∨ ((¬ spl0_17) ∨ (¬ spl0_27))) := by
    clear * - f587 f559
    grind (instances := 3000) only
  have f589 : (False ∨ ((¬ spl0_17) ∨ (¬ spl0_27))) := by
    clear * - f588 f71
    first | exact resolve f588 f71 | exact resolve f71 f588 | grind (instances := 3000) only
  have f590 : ((¬ spl0_17) ∨ (¬ spl0_27)) := by
    clear * - f589
    grind (instances := 3000) only
  have f601 : (∀ (X2 X3 X0 X1 X4 X5 : G), ((¬ (old (sF0 X2 X3 X4) X5 a)) ∨ ((¬ (old b X0 X1)) ∨ ((¬ (old X0 X0 X5)) ∨ ((new c X1 X0) ∨ (¬ (sP1 X2 X3 X4))))))) := by
    clear * - f149 f97
    first | exact resolve f149 f97 | exact resolve f97 f149 | grind (instances := 3000) only
  have f603 : (∀ (X2 X3 X0 X1 X4 X5 : G), ((¬ (old (sF5 X2 X3 X4) X5 a)) ∨ ((¬ (old b X0 X1)) ∨ ((¬ (old X0 X0 X5)) ∨ ((new c X1 X0) ∨ (¬ (sP5 X2 X3 X4))))))) := by
    clear * - f149 f124
    first | exact resolve f149 f124 | exact resolve f124 f149 | grind (instances := 3000) only
  have f640 : ((c = b) ∨ (¬ spl0_49)) := by
    clear * - f413 f93
    first | exact resolve f413 f93 | exact resolve f93 f413 | grind (instances := 3000) only
  have f647 : (False ∨ (¬ spl0_49)) := by
    clear * - f640 f71
    first | exact resolve f640 f71 | exact resolve f71 f640 | grind (instances := 3000) only
  have f648 : (¬ spl0_49) := by
    clear * - f647
    grind (instances := 3000) only
  have f681 : ((sP5 sk1 sk2 b) ∨ (¬ spl0_17)) := by
    clear * - f232 f559
    first | exact superpose f232 f559 | exact superpose f559 f232 | grind (instances := 3000) only
  have f684 : ((sP5 sk1 c b) ∨ (¬ spl0_17)) := by
    clear * - f681 f560
    grind (instances := 3000) only
  have f850 : ((¬ (new c sk4 sk0)) ∨ (¬ spl0_17)) := by
    clear * - f138 f560
    first | exact superpose f138 f560 | exact superpose f560 f138 | grind (instances := 3000) only
  have f955 : ((sP4 b sk0 sk4) ∨ ((¬ spl0_13) ∨ (¬ spl0_17))) := by
    clear * - f215 f559
    grind (instances := 3000) only
  let spl0_71 : Prop := (old b sk0 sk4)
  have f957 : (spl0_71 ↔ (old b sk0 sk4)) := Iff.rfl
  clear_value spl0_71
  have f958 : ((¬ (old b sk0 sk4)) ∨ spl0_71) := by
    clear * - f957
    grind (instances := 3000) only
  have f959 : ((old b sk0 sk4) ∨ (¬ spl0_71)) := by
    clear * - f957
    grind (instances := 3000) only
  let spl0_72 : Prop := (sP4 b sk0 sk4)
  have f961 : (spl0_72 ↔ (sP4 b sk0 sk4)) := Iff.rfl
  clear_value spl0_72
  have f962 : ((¬ (sP4 b sk0 sk4)) ∨ spl0_72) := by
    clear * - f961
    grind (instances := 3000) only
  have f963 : ((sP4 b sk0 sk4) ∨ (¬ spl0_72)) := by
    clear * - f961
    grind (instances := 3000) only
  have f1014 : (spl0_72 ∨ ((¬ spl0_13) ∨ (¬ spl0_17))) := by
    clear * - f955 f230 f213 f961
    grind (instances := 3000) only
  have f1017 : ((a = b) ∨ ((¬ spl0_15) ∨ (¬ spl0_17))) := by
    clear * - f385 f559
    grind (instances := 3000) only
  have f1026 : (False ∨ (spl0_1 ∨ ((¬ spl0_15) ∨ (¬ spl0_17)))) := by
    clear * - f1017 f157
    first | exact resolve f1017 f157 | exact resolve f157 f1017 | grind (instances := 3000) only
  have f1027 : (spl0_1 ∨ ((¬ spl0_15) ∨ (¬ spl0_17))) := by
    clear * - f1026
    grind (instances := 3000) only
  have f1044 : ((old sk0 sk0 sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ spl0_22))))))) := by
    clear * - f390 f252
    first | exact resolve f390 f252 | exact resolve f252 f390 | grind (instances := 3000) only
  have f1078 : ((c = b) ∨ (¬ spl0_52)) := by
    clear * - f542 f92
    first | exact resolve f542 f92 | exact resolve f92 f542 | grind (instances := 3000) only
  have f1082 : (False ∨ (¬ spl0_52)) := by
    clear * - f1078 f71
    first | exact resolve f1078 f71 | exact resolve f71 f1078 | grind (instances := 3000) only
  have f1083 : (¬ spl0_52) := by
    clear * - f1082
    grind (instances := 3000) only
  have f1096 : ((c = sk0) ∨ (¬ spl0_12)) := by
    clear * - f211 f119
    first | exact resolve f211 f119 | exact resolve f119 f211 | grind (instances := 3000) only
  have f1121 : (∀ (X2 X0 X1 : G), ((¬ (old a a (sF4 X0 X1 X2))) ∨ ((old (sF5 X0 X1 X2) X0 a) ∨ ((¬ (sP5 X0 X1 X2)) ∨ (¬ (sP5 X0 X1 X2)))))) := by
    clear * - f570 f123
    first | exact resolve f570 f123 | exact resolve f123 f570 | grind (instances := 3000) only
  have f1122 : (∀ (X2 X0 X1 : G), ((¬ (old a a (sF4 X0 X1 X2))) ∨ ((old (sF5 X0 X1 X2) X0 a) ∨ (¬ (sP5 X0 X1 X2))))) := by
    clear * - f1121
    grind (instances := 3000) only
  have f1123 : (∀ (X2 X0 X1 : G), ((old (sF5 X0 X1 X2) X0 a) ∨ (¬ (sP5 X0 X1 X2)))) := by
    clear * - f1122 f122
    first | exact resolve f1122 f122 | exact resolve f122 f1122 | grind (instances := 3000) only
  have f1131 : (∀ (X2 X3 X0 X1 X4 : G), ((¬ (old b X0 X1)) ∨ ((¬ (old X0 X0 X2)) ∨ ((new c X1 X0) ∨ ((¬ (sP1 X2 X3 X4)) ∨ (¬ (sP1 X2 X3 X4))))))) := by
    clear * - f601 f98
    first | exact resolve f601 f98 | exact resolve f98 f601 | grind (instances := 3000) only
  have f1132 : (∀ (X2 X3 X0 X1 X4 : G), ((¬ (sP1 X2 X3 X4)) ∨ ((¬ (old X0 X0 X2)) ∨ ((new c X1 X0) ∨ (¬ (old b X0 X1)))))) := by
    clear * - f1131
    grind (instances := 3000) only
  have f1135 : ((a = c) ∨ (¬ spl0_53)) := by
    clear * - f546 f108
    first | exact resolve f546 f108 | exact resolve f108 f546 | grind (instances := 3000) only
  have f1139 : (False ∨ (¬ spl0_53)) := by
    clear * - f1135 f70
    first | exact resolve f1135 f70 | exact resolve f70 f1135 | grind (instances := 3000) only
  have f1140 : (¬ spl0_53) := by
    clear * - f1139
    grind (instances := 3000) only
  have f1250 : ((old c c sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ spl0_22)))))))) := by
    clear * - f1044 f1096
    grind (instances := 3000) only
  have f1253 : ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ spl0_22))))))) := by
    clear * - f1250 f74
    first | exact resolve f1250 f74 | exact resolve f74 f1250 | grind (instances := 3000) only
  have f1254 : ((sP0 c c sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ spl0_22))))))) := by
    clear * - f1253 f1096
    grind (instances := 3000) only
  have f1255 : ((sP1 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ spl0_52))))))) := by
    clear * - f1254 f541
    first | exact resolve f1254 f541 | exact resolve f541 f1254 | grind (instances := 3000) only
  have f1256 : ((sP1 c c sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ spl0_52))))))) := by
    clear * - f1255 f1096
    grind (instances := 3000) only
  have f1257 : ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ spl0_52)))))) := by
    clear * - f1256 f440
    first | exact resolve f1256 f440 | exact resolve f440 f1256 | grind (instances := 3000) only
  have f1258 : ((sP3 c c sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ spl0_52)))))) := by
    clear * - f1257 f1096
    grind (instances := 3000) only
  have f1259 : ((sP4 sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ (spl0_52 ∨ spl0_53)))))) := by
    clear * - f1258 f545
    first | exact resolve f1258 f545 | exact resolve f545 f1258 | grind (instances := 3000) only
  have f1260 : ((sP4 c c sk1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ (spl0_52 ∨ spl0_53)))))) := by
    clear * - f1259 f1096
    grind (instances := 3000) only
  have f1261 : (spl0_54 ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ (spl0_52 ∨ spl0_53)))))) := by
    clear * - f1260 f544 f540 f251 f209 f184 f160 f548
    grind (instances := 3000) only
  have f1285 : ((old c c sk1) ∨ ((¬ spl0_12) ∨ (¬ spl0_26))) := by
    clear * - f269 f1096
    grind (instances := 3000) only
  have f1288 : (False ∨ ((¬ spl0_12) ∨ (¬ spl0_26))) := by
    clear * - f1285 f74
    first | exact resolve f1285 f74 | exact resolve f74 f1285 | grind (instances := 3000) only
  have f1289 : ((¬ spl0_12) ∨ (¬ spl0_26)) := by
    clear * - f1288
    grind (instances := 3000) only
  have f1324 : ((c = sk3) ∨ (¬ spl0_20)) := by
    clear * - f244 f93
    first | exact resolve f244 f93 | exact resolve f93 f244 | grind (instances := 3000) only
  have f1325 : ((b = sk2) ∨ (¬ spl0_20)) := by
    clear * - f244 f92
    first | exact resolve f244 f92 | exact resolve f92 f244 | grind (instances := 3000) only
  have f1326 : ((a = sk1) ∨ (¬ spl0_20)) := by
    clear * - f244 f91
    first | exact resolve f244 f91 | exact resolve f91 f244 | grind (instances := 3000) only
  have f1339 : ((old b sk1 c) ∨ (¬ spl0_54)) := by
    clear * - f550 f115
    first | exact resolve f550 f115 | exact resolve f115 f550 | grind (instances := 3000) only
  have f1341 : (False ∨ (¬ spl0_54)) := by
    clear * - f1339 f73
    first | exact resolve f1339 f73 | exact resolve f73 f1339 | grind (instances := 3000) only
  have f1342 : (¬ spl0_54) := by
    clear * - f1341
    grind (instances := 3000) only
  have f1351 : ((sP0 c sk0 sk4) ∨ ((¬ spl0_15) ∨ (¬ spl0_20))) := by
    clear * - f223 f1324
    grind (instances := 3000) only
  have f1355 : ((old sk3 sk0 sk4) ∨ ((sP0 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ spl0_14))))))) := by
    clear * - f392 f218
    first | exact resolve f392 f218 | exact resolve f218 f392 | grind (instances := 3000) only
  have f1363 : ((sP0 c sk0 c) ∨ ((¬ spl0_15) ∨ (¬ spl0_20))) := by
    clear * - f1351 f383
    grind (instances := 3000) only
  have f1372 : ((sP0 c b c) ∨ ((¬ spl0_15) ∨ (¬ spl0_20))) := by
    clear * - f1363 f384
    grind (instances := 3000) only
  have f1394 : ((¬ (new sk2 c sk0)) ∨ (¬ spl0_15)) := by
    clear * - f138 f383
    first | exact superpose f138 f383 | exact superpose f383 f138 | grind (instances := 3000) only
  have f1400 : ((¬ (new sk2 c b)) ∨ (¬ spl0_15)) := by
    clear * - f1394 f384
    grind (instances := 3000) only
  have f1425 : ((old sk0 sk0 a) ∨ ((¬ spl0_20) ∨ (¬ spl0_26))) := by
    clear * - f269 f1326
    grind (instances := 3000) only
  have f1452 : ((a = c) ∨ ((¬ spl0_15) ∨ (¬ spl0_20))) := by
    clear * - f1372 f91
    first | exact resolve f1372 f91 | exact resolve f91 f1372 | grind (instances := 3000) only
  have f1453 : (False ∨ ((¬ spl0_15) ∨ (¬ spl0_20))) := by
    clear * - f1452 f70
    first | exact resolve f1452 f70 | exact resolve f70 f1452 | grind (instances := 3000) only
  have f1454 : ((¬ spl0_15) ∨ (¬ spl0_20)) := by
    clear * - f1453
    grind (instances := 3000) only
  have f1455 : ((¬ (sP0 sk1 sk2 a)) ∨ ((¬ spl0_15) ∨ spl0_20)) := by
    clear * - f243 f385
    grind (instances := 3000) only
  have f1456 : ((old sk1 sk2 a) ∨ ((¬ spl0_15) ∨ (¬ spl0_21))) := by
    clear * - f248 f385
    grind (instances := 3000) only
  have f1560 : (∀ (X2 X3 X0 X1 X4 : G), ((¬ (sP5 X0 X1 X2)) ∨ ((¬ (old b X3 X4)) ∨ ((¬ (old X3 X3 X0)) ∨ ((new c X4 X3) ∨ (¬ (sP5 X0 X1 X2))))))) := by
    clear * - f1123 f603
    first | exact resolve f1123 f603 | exact resolve f603 f1123 | grind (instances := 3000) only
  have f1561 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ ((new X0 c b) ∨ (¬ (sP5 X0 X1 X2))))) := by
    clear * - f1123 f555
    first | exact resolve f1123 f555 | exact resolve f555 f1123 | grind (instances := 3000) only
  have f1587 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (new X0 c b))) := by
    clear * - f1561
    grind (instances := 3000) only
  have f1588 : (∀ (X2 X3 X0 X1 X4 : G), ((¬ (sP5 X0 X1 X2)) ∨ ((¬ (old b X3 X4)) ∨ ((¬ (old X3 X3 X0)) ∨ (new c X4 X3))))) := by
    clear * - f1560
    grind (instances := 3000) only
  have f1613 : ((old b b sk1) ∨ ((¬ spl0_15) ∨ (¬ spl0_26))) := by
    clear * - f269 f384
    grind (instances := 3000) only
  have f1622 : (∀ (X0 : G), (((¬ (old sk1 X0 a)) ∨ (new X0 c b)) ∨ ((¬ spl0_15) ∨ (¬ spl0_26)))) := by
    clear * - f1613 f143
    first | exact resolve f1613 f143 | exact resolve f143 f1613 | grind (instances := 3000) only
  have f1759 : ((new sk2 c b) ∨ ((¬ spl0_15) ∨ ((¬ spl0_21) ∨ (¬ spl0_26)))) := by
    clear * - f1622 f1456
    first | exact resolve f1622 f1456 | exact resolve f1456 f1622 | grind (instances := 3000) only
  have f1761 : (False ∨ ((¬ spl0_15) ∨ ((¬ spl0_21) ∨ (¬ spl0_26)))) := by
    clear * - f1759 f1400
    first | exact resolve f1759 f1400 | exact resolve f1400 f1759 | grind (instances := 3000) only
  have f1762 : ((¬ spl0_15) ∨ ((¬ spl0_21) ∨ (¬ spl0_26))) := by
    clear * - f1761
    grind (instances := 3000) only
  have f1763 : ((¬ (old sk1 sk2 a)) ∨ ((¬ spl0_15) ∨ spl0_21)) := by
    clear * - f247 f385
    grind (instances := 3000) only
  have f1786 : ((sP1 sk1 sk2 a) ∨ ((¬ spl0_15) ∨ (¬ spl0_19))) := by
    clear * - f240 f385
    grind (instances := 3000) only
  have f1814 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ (sP5 X0 X1 X2)))))) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ (¬ spl0_8))))) := by
    clear * - f382 f177
    grind (instances := 3000) only
  have f1866 : ((old sk1 sk2 sk3) ∨ ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((sP4 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ (¬ spl0_8)))))))) := by
    clear * - f1814 f136
    first | exact resolve f1814 f136 | exact resolve f136 f1814 | grind (instances := 3000) only
  have f1869 : ((old sk1 sk2 sk3) ∨ ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ spl0_18))))))) := by
    clear * - f1866 f235
    first | exact resolve f1866 f235 | exact resolve f235 f1866 | grind (instances := 3000) only
  have f1872 : ((old sk1 sk2 sk3) ∨ ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ spl0_18))))))) := by
    clear * - f1869 f231
    first | exact resolve f1869 f231 | exact resolve f231 f1869 | grind (instances := 3000) only
  have f1874 : ((old sk1 sk2 a) ∨ ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ spl0_18)))))))) := by
    clear * - f1872 f385
    grind (instances := 3000) only
  have f1876 : ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ spl0_21)))))))) := by
    clear * - f1874 f1763
    first | exact resolve f1874 f1763 | exact resolve f1763 f1874 | grind (instances := 3000) only
  have f1878 : ((sP0 sk1 sk2 a) ∨ ((sP1 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ spl0_21)))))))) := by
    clear * - f1876 f385
    grind (instances := 3000) only
  have f1880 : ((sP1 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_20 ∨ spl0_21)))))))) := by
    clear * - f1878 f1455
    first | exact resolve f1878 f1455 | exact resolve f1455 f1878 | grind (instances := 3000) only
  have f1882 : ((sP1 sk1 sk2 a) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_20 ∨ spl0_21)))))))) := by
    clear * - f1880 f385
    grind (instances := 3000) only
  have f1888 : ((a = b) ∨ ((¬ spl0_15) ∨ (¬ spl0_19))) := by
    clear * - f1786 f96
    first | exact resolve f1786 f96 | exact resolve f96 f1786 | grind (instances := 3000) only
  have f1895 : (False ∨ (spl0_1 ∨ ((¬ spl0_15) ∨ (¬ spl0_19)))) := by
    clear * - f1888 f157
    first | exact resolve f1888 f157 | exact resolve f157 f1888 | grind (instances := 3000) only
  have f1896 : (spl0_1 ∨ ((¬ spl0_15) ∨ (¬ spl0_19))) := by
    clear * - f1895
    grind (instances := 3000) only
  have f1930 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_1))) := by
    clear * - f72 f158
    first | exact superpose f72 f158 | exact superpose f158 f72 | grind (instances := 3000) only
  have f1934 : (∀ (X2 X0 X1 : G), (((old b b (sF4 X0 X1 X2)) ∨ (¬ (sP5 X0 X1 X2))) ∨ (¬ spl0_1))) := by
    clear * - f122 f158
    first | exact superpose f122 f158 | exact superpose f158 f122 | grind (instances := 3000) only
  have f1983 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (¬ spl0_1))) := by
    clear * - f97 f1930
    grind (instances := 3000) only
  have f1984 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (¬ spl0_1))) := by
    clear * - f114 f1930
    grind (instances := 3000) only
  have f1985 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (¬ spl0_1))) := by
    clear * - f1934 f1930
    grind (instances := 3000) only
  have f1993 : (False ∨ ((¬ spl0_1) ∨ (¬ spl0_19))) := by
    clear * - f240 f1983
    first | exact resolve f240 f1983 | exact resolve f1983 f240 | grind (instances := 3000) only
  have f1994 : ((¬ spl0_1) ∨ (¬ spl0_19)) := by
    clear * - f1993
    grind (instances := 3000) only
  have f2003 : (False ∨ ((¬ spl0_1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_20 ∨ spl0_21))))))))) := by
    clear * - f1882 f1983
    first | exact resolve f1882 f1983 | exact resolve f1983 f1882 | grind (instances := 3000) only
  have f2004 : ((¬ spl0_1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_20 ∨ spl0_21)))))))) := by
    clear * - f2003
    grind (instances := 3000) only
  have f2030 : (False ∨ ((¬ spl0_1) ∨ (¬ spl0_17))) := by
    clear * - f684 f1985
    first | exact resolve f684 f1985 | exact resolve f1985 f684 | grind (instances := 3000) only
  have f2031 : ((¬ spl0_1) ∨ (¬ spl0_17)) := by
    clear * - f2030
    grind (instances := 3000) only
  have f2062 : (False ∨ ((¬ spl0_1) ∨ (¬ spl0_18))) := by
    clear * - f490 f1984
    first | exact resolve f490 f1984 | exact resolve f1984 f490 | grind (instances := 3000) only
  have f2063 : ((¬ spl0_1) ∨ (¬ spl0_18)) := by
    clear * - f2062
    grind (instances := 3000) only
  have f2163 : ((b = sk3) ∨ (¬ spl0_19)) := by
    clear * - f240 f96
    first | exact resolve f240 f96 | exact resolve f96 f240 | grind (instances := 3000) only
  have f2164 : ((c = sk2) ∨ (¬ spl0_19)) := by
    clear * - f240 f95
    first | exact resolve f240 f95 | exact resolve f95 f240 | grind (instances := 3000) only
  have f2175 : ((old b sk0 sk4) ∨ ((¬ spl0_16) ∨ (¬ spl0_19))) := by
    clear * - f227 f2163
    first | exact superpose f227 f2163 | exact superpose f2163 f227 | grind (instances := 3000) only
  have f2178 : ((sP1 sk1 sk2 b) ∨ (¬ spl0_19)) := by
    clear * - f240 f2163
    first | exact superpose f240 f2163 | exact superpose f2163 f240 | grind (instances := 3000) only
  have f2181 : ((sP1 sk1 c b) ∨ (¬ spl0_19)) := by
    clear * - f2178 f2164
    grind (instances := 3000) only
  have f2184 : (spl0_71 ∨ ((¬ spl0_16) ∨ (¬ spl0_19))) := by
    clear * - f2175 f238 f225 f957
    grind (instances := 3000) only
  have f2238 : ((¬ (new c sk4 sk0)) ∨ (¬ spl0_19)) := by
    clear * - f138 f2164
    first | exact superpose f138 f2164 | exact superpose f2164 f138 | grind (instances := 3000) only
  have f2548 : (∀ (X0 X1 : G), (((¬ (old b X0 X1)) ∨ ((new c X1 X0) ∨ (¬ (old X0 X0 sk1)))) ∨ (¬ spl0_19))) := by
    clear * - f1132 f2181
    first | exact resolve f1132 f2181 | exact resolve f2181 f1132 | grind (instances := 3000) only
  have f2829 : ((new c sk4 sk0) ∨ ((¬ (old sk0 sk0 sk1)) ∨ ((¬ spl0_19) ∨ (¬ spl0_71)))) := by
    clear * - f2548 f959
    first | exact resolve f2548 f959 | exact resolve f959 f2548 | grind (instances := 3000) only
  have f2831 : ((¬ (old sk0 sk0 sk1)) ∨ ((¬ spl0_19) ∨ (¬ spl0_71))) := by
    clear * - f2829 f2238
    first | exact resolve f2829 f2238 | exact resolve f2238 f2829 | grind (instances := 3000) only
  have f2834 : ((sP4 b sk0 sk4) ∨ ((¬ spl0_13) ∨ (¬ spl0_19))) := by
    clear * - f215 f2163
    grind (instances := 3000) only
  have f2838 : ((old sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_14 ∨ spl0_15))))))) := by
    clear * - f1355 f222
    first | exact resolve f1355 f222 | exact resolve f222 f1355 | grind (instances := 3000) only
  have f2840 : (False ∨ ((¬ spl0_13) ∨ ((¬ spl0_19) ∨ spl0_72))) := by
    clear * - f2834 f962
    first | exact resolve f2834 f962 | exact resolve f962 f2834 | grind (instances := 3000) only
  have f2841 : ((¬ spl0_13) ∨ ((¬ spl0_19) ∨ spl0_72)) := by
    clear * - f2840
    grind (instances := 3000) only
  have f2844 : ((old sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_14 ∨ spl0_15))))))) := by
    clear * - f2838 f177
    first | exact resolve f2838 f177 | exact resolve f177 f2838 | grind (instances := 3000) only
  have f2848 : ((old sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_12 ∨ (spl0_14 ∨ spl0_15))))))) := by
    clear * - f2844 f210
    first | exact resolve f2844 f210 | exact resolve f210 f2844 | grind (instances := 3000) only
  have f2867 : ((c = b) ∨ (¬ spl0_72)) := by
    clear * - f963 f113
    first | exact resolve f963 f113 | exact resolve f113 f963 | grind (instances := 3000) only
  have f2885 : (False ∨ (¬ spl0_72)) := by
    clear * - f2867 f71
    first | exact resolve f2867 f71 | exact resolve f71 f2867 | grind (instances := 3000) only
  have f2886 : (¬ spl0_72) := by
    clear * - f2885
    grind (instances := 3000) only
  have f2889 : ((c = sk0) ∨ (¬ spl0_24)) := by
    clear * - f261 f95
    first | exact resolve f261 f95 | exact resolve f95 f261 | grind (instances := 3000) only
  have f2909 : ((sP1 c c sk1) ∨ (¬ spl0_24)) := by
    clear * - f261 f2889
    first | exact superpose f261 f2889 | exact superpose f2889 f261 | grind (instances := 3000) only
  have f2947 : (False ∨ (¬ spl0_24)) := by
    clear * - f2909 f440
    first | exact resolve f2909 f440 | exact resolve f440 f2909 | grind (instances := 3000) only
  have f2948 : (¬ spl0_24) := by
    clear * - f2947
    grind (instances := 3000) only
  have f2958 : ((c = sk0) ∨ (¬ spl0_23)) := by
    clear * - f257 f113
    first | exact resolve f257 f113 | exact resolve f113 f257 | grind (instances := 3000) only
  have f2984 : ((sP4 c c sk1) ∨ (¬ spl0_23)) := by
    clear * - f257 f2958
    first | exact superpose f257 f2958 | exact superpose f2958 f257 | grind (instances := 3000) only
  have f3027 : (False ∨ ((¬ spl0_23) ∨ spl0_54)) := by
    clear * - f2984 f549
    first | exact resolve f2984 f549 | exact resolve f549 f2984 | grind (instances := 3000) only
  have f3028 : ((¬ spl0_23) ∨ spl0_54) := by
    clear * - f3027
    grind (instances := 3000) only
  have f3044 : ((new sk0 c b) ∨ (¬ spl0_22)) := by
    clear * - f253 f1587
    first | exact resolve f253 f1587 | exact resolve f1587 f253 | grind (instances := 3000) only
  have f3051 : ((new c c b) ∨ (¬ spl0_22)) := by
    clear * - f3044 f419
    grind (instances := 3000) only
  have f3058 : (False ∨ (spl0_3 ∨ (¬ spl0_22))) := by
    clear * - f3051 f165
    first | exact resolve f3051 f165 | exact resolve f165 f3051 | grind (instances := 3000) only
  have f3059 : (spl0_3 ∨ (¬ spl0_22)) := by
    clear * - f3058
    grind (instances := 3000) only
  have f3068 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_47))) := by
    clear * - f405 f177
    first | exact resolve f405 f177 | exact resolve f177 f405 | grind (instances := 3000) only
  have f3069 : ((¬ spl0_6) ∨ (¬ spl0_47)) := by
    clear * - f3068
    grind (instances := 3000) only
  have f3089 : (∀ (X0 X1 : G), (((¬ (old b X0 X1)) ∨ ((¬ (old X0 X0 sk1)) ∨ (new c X1 X0))) ∨ (¬ spl0_17))) := by
    clear * - f232 f1588
    first | exact resolve f232 f1588 | exact resolve f1588 f232 | grind (instances := 3000) only
  have f3216 : ((¬ (old sk0 sk0 sk1)) ∨ ((new c sk4 sk0) ∨ ((¬ spl0_17) ∨ (¬ spl0_71)))) := by
    clear * - f3089 f959
    first | exact resolve f3089 f959 | exact resolve f959 f3089 | grind (instances := 3000) only
  have f3218 : ((new c sk4 sk0) ∨ ((¬ spl0_17) ∨ ((¬ spl0_26) ∨ (¬ spl0_71)))) := by
    clear * - f3216 f269
    first | exact resolve f3216 f269 | exact resolve f269 f3216 | grind (instances := 3000) only
  have f3219 : (False ∨ ((¬ spl0_17) ∨ ((¬ spl0_26) ∨ (¬ spl0_71)))) := by
    clear * - f3218 f850
    first | exact resolve f3218 f850 | exact resolve f850 f3218 | grind (instances := 3000) only
  have f3220 : ((¬ spl0_17) ∨ ((¬ spl0_26) ∨ (¬ spl0_71))) := by
    clear * - f3219
    grind (instances := 3000) only
  have f3223 : (spl0_13 ∨ (spl0_16 ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_12 ∨ (spl0_14 ∨ spl0_15))))))) := by
    clear * - f2848 f221 f217 f209 f184 f176 f160 f225 f213
    grind (instances := 3000) only
  have f3226 : (∀ (X0 X1 : G), (((¬ (old sk0 sk0 X0)) ∨ ((¬ (old X0 X1 sk3)) ∨ (old X1 sk4 sk0))) ∨ (¬ spl0_16))) := by
    clear * - f227 f78
    first | exact resolve f227 f78 | exact resolve f78 f227 | grind (instances := 3000) only
  have f3260 : (∀ (X0 : G), (((¬ (old sk1 X0 sk3)) ∨ (old X0 sk4 sk0)) ∨ ((¬ spl0_16) ∨ (¬ spl0_26)))) := by
    clear * - f3226 f269
    first | exact resolve f3226 f269 | exact resolve f269 f3226 | grind (instances := 3000) only
  have f3266 : ((old sk2 sk4 sk0) ∨ ((¬ spl0_16) ∨ ((¬ spl0_21) ∨ (¬ spl0_26)))) := by
    clear * - f3260 f248
    first | exact resolve f3260 f248 | exact resolve f248 f3260 | grind (instances := 3000) only
  have f3269 : ((new sk2 sk4 sk0) ∨ ((¬ spl0_16) ∨ ((¬ spl0_21) ∨ (¬ spl0_26)))) := by
    clear * - f3266 f89
    first | exact resolve f3266 f89 | exact resolve f89 f3266 | grind (instances := 3000) only
  have f3283 : (False ∨ ((¬ spl0_16) ∨ ((¬ spl0_21) ∨ (¬ spl0_26)))) := by
    clear * - f3269 f138
    first | exact resolve f3269 f138 | exact resolve f138 f3269 | grind (instances := 3000) only
  have f3284 : ((¬ spl0_16) ∨ ((¬ spl0_21) ∨ (¬ spl0_26))) := by
    clear * - f3283
    grind (instances := 3000) only
  have f3285 : ((c = sk3) ∨ (¬ spl0_13)) := by
    clear * - f215 f113
    first | exact resolve f215 f113 | exact resolve f113 f215 | grind (instances := 3000) only
  have f3286 : ((old b sk4 sk0) ∨ (¬ spl0_13)) := by
    clear * - f215 f115
    first | exact resolve f215 f115 | exact resolve f115 f215 | grind (instances := 3000) only
  have f3308 : ((old sk1 sk2 c) ∨ ((¬ spl0_13) ∨ (¬ spl0_21))) := by
    clear * - f248 f3285
    first | exact superpose f248 f3285 | exact superpose f3285 f248 | grind (instances := 3000) only
  have f3310 : (False ∨ ((¬ spl0_13) ∨ (¬ spl0_21))) := by
    clear * - f3308 f73
    first | exact resolve f3308 f73 | exact resolve f73 f3308 | grind (instances := 3000) only
  have f3311 : ((¬ spl0_13) ∨ (¬ spl0_21)) := by
    clear * - f3310
    grind (instances := 3000) only
  have f3372 : ((old c sk0 sk4) ∨ ((¬ spl0_16) ∨ (¬ spl0_20))) := by
    clear * - f227 f1324
    first | exact superpose f227 f1324 | exact superpose f1324 f227 | grind (instances := 3000) only
  have f3381 : (False ∨ ((¬ spl0_16) ∨ (¬ spl0_20))) := by
    clear * - f3372 f75
    first | exact resolve f3372 f75 | exact resolve f75 f3372 | grind (instances := 3000) only
  have f3382 : ((¬ spl0_16) ∨ (¬ spl0_20)) := by
    clear * - f3381
    grind (instances := 3000) only
  have f3397 : ((¬ (new b sk4 sk0)) ∨ (¬ spl0_20)) := by
    clear * - f138 f1325
    first | exact superpose f138 f1325 | exact superpose f1325 f138 | grind (instances := 3000) only
  have f3492 : ((new b sk4 sk0) ∨ (¬ spl0_13)) := by
    clear * - f3286 f89
    first | exact resolve f3286 f89 | exact resolve f89 f3286 | grind (instances := 3000) only
  have f3497 : (False ∨ ((¬ spl0_13) ∨ (¬ spl0_20))) := by
    clear * - f3492 f3397
    first | exact resolve f3492 f3397 | exact resolve f3397 f3492 | grind (instances := 3000) only
  have f3498 : ((¬ spl0_13) ∨ (¬ spl0_20)) := by
    clear * - f3497
    grind (instances := 3000) only
  have f3563 : ((¬ (new sk2 sk4 a)) ∨ (¬ spl0_27)) := by
    clear * - f138 f586
    first | exact superpose f138 f586 | exact superpose f586 f138 | grind (instances := 3000) only
  have f3655 : ((¬ (new b sk4 a)) ∨ ((¬ spl0_20) ∨ (¬ spl0_27))) := by
    clear * - f3563 f1325
    grind (instances := 3000) only
  have f3724 : (∀ (X0 : G), (((¬ (old X0 X0 a)) ∨ (a = X0)) ∨ (¬ spl0_10))) := by
    clear * - f195 f77
    first | exact resolve f195 f77 | exact resolve f77 f195 | grind (instances := 3000) only
  have f3765 : ((old sk1 sk2 sk3) ∨ ((sP0 sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((sP3 sk1 sk2 sk3) ∨ ((sP4 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ (¬ spl0_8)))))))) := by
    clear * - f382 f136
    first | exact resolve f382 f136 | exact resolve f136 f382 | grind (instances := 3000) only
  have f3788 : ((a = sk0) ∨ ((¬ spl0_10) ∨ ((¬ spl0_20) ∨ (¬ spl0_26)))) := by
    clear * - f3724 f1425
    first | exact resolve f3724 f1425 | exact resolve f1425 f3724 | grind (instances := 3000) only
  let spl0_169 : Prop := (a = sk4)
  have f3910 : (spl0_169 ↔ (a = sk4)) := Iff.rfl
  clear_value spl0_169
  have f3911 : ((a ≠ sk4) ∨ spl0_169) := by
    clear * - f3910
    grind (instances := 3000) only
  have f3912 : ((a = sk4) ∨ (¬ spl0_169)) := by
    clear * - f3910
    grind (instances := 3000) only
  have f3996 : ((new b sk4 a) ∨ (¬ spl0_27)) := by
    clear * - f585 f89
    first | exact resolve f585 f89 | exact resolve f89 f585 | grind (instances := 3000) only
  have f4007 : (False ∨ ((¬ spl0_20) ∨ (¬ spl0_27))) := by
    clear * - f3996 f3655
    first | exact resolve f3996 f3655 | exact resolve f3655 f3996 | grind (instances := 3000) only
  have f4008 : ((¬ spl0_20) ∨ (¬ spl0_27)) := by
    clear * - f4007
    grind (instances := 3000) only
  have f4176 : ((a = sk2) ∨ (¬ spl0_28)) := by
    clear * - f282 f108
    first | exact resolve f282 f108 | exact resolve f108 f282 | grind (instances := 3000) only
  have f4177 : ((c = sk1) ∨ (¬ spl0_28)) := by
    clear * - f282 f107
    first | exact resolve f282 f107 | exact resolve f107 f282 | grind (instances := 3000) only
  have f4185 : ((sP1 sk1 sk2 c) ∨ ((¬ spl0_19) ∨ (¬ spl0_27))) := by
    clear * - f240 f587
    grind (instances := 3000) only
  have f4191 : ((¬ (sP3 sk1 sk2 c)) ∨ ((¬ spl0_27) ∨ spl0_28)) := by
    clear * - f281 f587
    grind (instances := 3000) only
  have f4195 : ((sP1 sk1 c c) ∨ ((¬ spl0_19) ∨ (¬ spl0_27))) := by
    clear * - f4185 f2164
    grind (instances := 3000) only
  have f4212 : ((c = b) ∨ ((¬ spl0_19) ∨ (¬ spl0_27))) := by
    clear * - f4195 f96
    first | exact resolve f4195 f96 | exact resolve f96 f4195 | grind (instances := 3000) only
  have f4218 : (False ∨ ((¬ spl0_19) ∨ (¬ spl0_27))) := by
    clear * - f4212 f71
    first | exact resolve f4212 f71 | exact resolve f71 f4212 | grind (instances := 3000) only
  have f4219 : ((¬ spl0_19) ∨ (¬ spl0_27)) := by
    clear * - f4218
    grind (instances := 3000) only
  have f4272 : ((sP3 sk1 a sk3) ∨ (¬ spl0_28)) := by
    clear * - f282 f4176
    grind (instances := 3000) only
  have f4276 : ((sP3 c a sk3) ∨ (¬ spl0_28)) := by
    clear * - f4272 f4177
    grind (instances := 3000) only
  have f4348 : ((old sk0 sk0 c) ∨ ((¬ spl0_26) ∨ (¬ spl0_28))) := by
    clear * - f269 f4177
    first | exact superpose f269 f4177 | exact superpose f4177 f269 | grind (instances := 3000) only
  have f4377 : (False ∨ ((¬ spl0_26) ∨ (¬ spl0_28))) := by
    clear * - f4348 f73
    first | exact resolve f4348 f73 | exact resolve f73 f4348 | grind (instances := 3000) only
  have f4378 : ((¬ spl0_26) ∨ (¬ spl0_28)) := by
    clear * - f4377
    grind (instances := 3000) only
  have f4382 : ((¬ spl0_26) ∨ ((¬ spl0_19) ∨ (¬ spl0_71))) := by
    clear * - f2831 f957 f238 f267
    grind (instances := 3000) only
  have f4396 : ((a = sk0) ∨ (¬ spl0_29)) := by
    clear * - f287 f108
    first | exact resolve f287 f108 | exact resolve f108 f287 | grind (instances := 3000) only
  have f4397 : ((c = sk0) ∨ (¬ spl0_29)) := by
    clear * - f287 f107
    first | exact resolve f287 f107 | exact resolve f107 f287 | grind (instances := 3000) only
  have f4490 : ((a = c) ∨ (¬ spl0_29)) := by
    clear * - f4397 f4396
    first | exact superpose f4397 f4396 | exact superpose f4396 f4397 | grind (instances := 3000) only
  have f4538 : (False ∨ (¬ spl0_29)) := by
    clear * - f4490 f70
    first | exact resolve f4490 f70 | exact resolve f70 f4490 | grind (instances := 3000) only
  have f4539 : (¬ spl0_29) := by
    clear * - f4538
    grind (instances := 3000) only
  have f4548 : ((c = sk1) ∨ (¬ spl0_25)) := by
    clear * - f265 f93
    first | exact resolve f265 f93 | exact resolve f93 f265 | grind (instances := 3000) only
  have f4549 : ((b = sk0) ∨ (¬ spl0_25)) := by
    clear * - f265 f92
    first | exact resolve f265 f92 | exact resolve f92 f265 | grind (instances := 3000) only
  have f4550 : ((a = sk0) ∨ (¬ spl0_25)) := by
    clear * - f265 f91
    first | exact resolve f265 f91 | exact resolve f91 f265 | grind (instances := 3000) only
  have f4610 : ((¬ (sP3 sk0 sk0 b)) ∨ ((¬ spl0_22) ∨ spl0_29)) := by
    clear * - f286 f418
    first | exact superpose f286 f418 | exact superpose f418 f286 | grind (instances := 3000) only
  have f4637 : ((¬ (sP3 c c b)) ∨ ((¬ spl0_22) ∨ spl0_29)) := by
    clear * - f4610 f419
    grind (instances := 3000) only
  have f4650 : (False ∨ ((¬ spl0_22) ∨ (spl0_29 ∨ (¬ spl0_47)))) := by
    clear * - f4637 f405
    first | exact resolve f4637 f405 | exact resolve f405 f4637 | grind (instances := 3000) only
  have f4651 : ((¬ spl0_22) ∨ (spl0_29 ∨ (¬ spl0_47))) := by
    clear * - f4650
    grind (instances := 3000) only
  have f4658 : ((a = b) ∨ (¬ spl0_25)) := by
    clear * - f4550 f4549
    grind (instances := 3000) only
  have f4669 : (False ∨ (spl0_1 ∨ (¬ spl0_25))) := by
    clear * - f4658 f157
    first | exact resolve f4658 f157 | exact resolve f157 f4658 | grind (instances := 3000) only
  have f4670 : (spl0_1 ∨ (¬ spl0_25)) := by
    clear * - f4669
    grind (instances := 3000) only
  have f4681 : (False ∨ ((¬ spl0_6) ∨ (¬ spl0_28))) := by
    clear * - f4276 f177
    grind (instances := 3000) only
  have f4684 : ((¬ spl0_6) ∨ (¬ spl0_28)) := by
    clear * - f4681
    grind (instances := 3000) only
  have f4688 : ((old sk1 sk2 sk3) ∨ ((sP1 sk1 sk2 sk3) ∨ ((sP3 sk1 sk2 sk3) ∨ ((sP4 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ spl0_20))))))) := by
    clear * - f3765 f243
    first | exact resolve f3765 f243 | exact resolve f243 f3765 | grind (instances := 3000) only
  have f4691 : ((old sk1 sk2 sk3) ∨ ((sP3 sk1 sk2 sk3) ∨ ((sP4 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_19 ∨ spl0_20))))))) := by
    clear * - f4688 f239
    first | exact resolve f4688 f239 | exact resolve f239 f4688 | grind (instances := 3000) only
  have f4694 : ((old sk1 sk2 sk3) ∨ ((sP4 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_19 ∨ spl0_20))))))) := by
    clear * - f4691 f177
    first | exact resolve f4691 f177 | exact resolve f177 f4691 | grind (instances := 3000) only
  have f4698 : ((old sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_18 ∨ (spl0_19 ∨ spl0_20))))))) := by
    clear * - f4694 f235
    first | exact resolve f4694 f235 | exact resolve f235 f4694 | grind (instances := 3000) only
  have f4700 : ((old sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ spl0_20))))))) := by
    clear * - f4698 f231
    first | exact resolve f4698 f231 | exact resolve f231 f4698 | grind (instances := 3000) only
  have f4713 : ((old c sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_25))))))))) := by
    clear * - f4700 f4548
    grind (instances := 3000) only
  have f4718 : (False ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_25))))))))) := by
    clear * - f4713 f75
    first | exact resolve f4713 f75 | exact resolve f75 f4713 | grind (instances := 3000) only
  have f4719 : ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_25)))))))) := by
    clear * - f4718
    grind (instances := 3000) only
  have f4729 : ((old sk1 sk2 c) ∨ ((¬ spl0_21) ∨ (¬ spl0_27))) := by
    clear * - f248 f587
    grind (instances := 3000) only
  have f4732 : ((old sk1 sk2 sk3) ∨ ((sP3 sk1 sk2 sk3) ∨ ((sP5 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_18 ∨ (spl0_19 ∨ spl0_20))))))) := by
    clear * - f4691 f235
    first | exact resolve f4691 f235 | exact resolve f235 f4691 | grind (instances := 3000) only
  have f4735 : (False ∨ ((¬ spl0_21) ∨ (¬ spl0_27))) := by
    clear * - f4729 f73
    first | exact resolve f4729 f73 | exact resolve f73 f4729 | grind (instances := 3000) only
  have f4736 : ((¬ spl0_21) ∨ (¬ spl0_27)) := by
    clear * - f4735
    grind (instances := 3000) only
  have f4738 : ((old sk1 sk2 sk3) ∨ ((sP3 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ spl0_20))))))) := by
    clear * - f4732 f231
    first | exact resolve f4732 f231 | exact resolve f231 f4732 | grind (instances := 3000) only
  have f4740 : ((old sk1 sk2 c) ∨ ((sP3 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_27))))))))) := by
    clear * - f4738 f587
    grind (instances := 3000) only
  have f4742 : ((sP3 sk1 sk2 sk3) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_27)))))))) := by
    clear * - f4740 f73
    first | exact resolve f4740 f73 | exact resolve f73 f4740 | grind (instances := 3000) only
  have f4744 : ((sP3 sk1 sk2 c) ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_27)))))))) := by
    clear * - f4742 f587
    grind (instances := 3000) only
  have f4747 : (False ∨ ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ ((¬ spl0_27) ∨ spl0_28)))))))) := by
    clear * - f4744 f4191
    first | exact resolve f4744 f4191 | exact resolve f4191 f4744 | grind (instances := 3000) only
  have f4748 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ ((¬ spl0_27) ∨ spl0_28))))))) := by
    clear * - f4747
    grind (instances := 3000) only
  have f4750 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ (sP5 X0 X1 X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f134 f161
    first | exact resolve f134 f161 | exact resolve f161 f134 | grind (instances := 3000) only
  have f4776 : ((new b a a) ∨ (¬ spl0_9)) := by
    clear * - f190 f89
    first | exact resolve f190 f89 | exact resolve f89 f190 | grind (instances := 3000) only
  have f4794 : ((old c c b) ∨ ((sP0 c c b) ∨ ((sP1 c c b) ∨ ((sP2 c c b) ∨ ((sP3 c c b) ∨ ((sP4 c c b) ∨ ((sP5 c c b) ∨ ((¬ spl0_2) ∨ (¬ spl0_3))))))))) := by
    clear * - f4750 f166
    first | exact resolve f4750 f166 | exact resolve f166 f4750 | grind (instances := 3000) only
  have f4808 : ((old sk3 sk0 sk4) ∨ ((sP0 sk3 sk0 sk4) ∨ ((sP1 sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ (¬ spl0_2)))))))) := by
    clear * - f4750 f137
    first | exact resolve f4750 f137 | exact resolve f137 f4750 | grind (instances := 3000) only
  have f4825 : ((a = sk4) ∨ (¬ spl0_30)) := by
    clear * - f298 f102
    first | exact resolve f298 f102 | exact resolve f102 f298 | grind (instances := 3000) only
  have f4826 : ((a = sk0) ∨ (¬ spl0_30)) := by
    clear * - f298 f101
    first | exact resolve f298 f101 | exact resolve f101 f298 | grind (instances := 3000) only
  have f4827 : ((c = sk3) ∨ (¬ spl0_30)) := by
    clear * - f298 f100
    first | exact resolve f298 f100 | exact resolve f100 f298 | grind (instances := 3000) only
  have f4828 : (False ∨ ((¬ spl0_30) ∨ spl0_169)) := by
    clear * - f4825 f3911
    first | exact resolve f4825 f3911 | exact resolve f3911 f4825 | grind (instances := 3000) only
  have f4829 : ((¬ spl0_30) ∨ spl0_169) := by
    clear * - f4828
    grind (instances := 3000) only
  have f4842 : ((old b b c) ∨ (¬ spl0_46)) := by
    clear * - f401 f115
    first | exact resolve f401 f115 | exact resolve f115 f401 | grind (instances := 3000) only
  have f4848 : (False ∨ (¬ spl0_46)) := by
    clear * - f4842 f73
    first | exact resolve f4842 f73 | exact resolve f73 f4842 | grind (instances := 3000) only
  have f4849 : (¬ spl0_46) := by
    clear * - f4848
    grind (instances := 3000) only
  have f4850 : ((sP0 c c b) ∨ ((sP1 c c b) ∨ ((sP2 c c b) ∨ ((sP3 c c b) ∨ ((sP4 c c b) ∨ ((sP5 c c b) ∨ ((¬ spl0_2) ∨ (¬ spl0_3)))))))) := by
    clear * - f4794 f74
    first | exact resolve f4794 f74 | exact resolve f74 f4794 | grind (instances := 3000) only
  have f4851 : ((sP1 c c b) ∨ ((sP2 c c b) ∨ ((sP3 c c b) ∨ ((sP4 c c b) ∨ ((sP5 c c b) ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ spl0_49))))))) := by
    clear * - f4850 f412
    first | exact resolve f4850 f412 | exact resolve f412 f4850 | grind (instances := 3000) only
  have f4852 : ((sP2 c c b) ∨ ((sP3 c c b) ∨ ((sP4 c c b) ∨ ((sP5 c c b) ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ spl0_49)))))) := by
    clear * - f4851 f440
    first | exact resolve f4851 f440 | exact resolve f440 f4851 | grind (instances := 3000) only
  have f4853 : ((sP2 c c b) ∨ ((sP4 c c b) ∨ ((sP5 c c b) ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_47 ∨ spl0_49)))))) := by
    clear * - f4852 f404
    first | exact resolve f4852 f404 | exact resolve f404 f4852 | grind (instances := 3000) only
  have f4854 : ((sP2 c c b) ∨ ((sP5 c c b) ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_46 ∨ (spl0_47 ∨ spl0_49)))))) := by
    clear * - f4853 f400
    first | exact resolve f4853 f400 | exact resolve f400 f4853 | grind (instances := 3000) only
  have f4855 : ((sP2 c c b) ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_46 ∨ (spl0_47 ∨ spl0_49))))) := by
    clear * - f4854 f474
    first | exact resolve f4854 f474 | exact resolve f474 f4854 | grind (instances := 3000) only
  have f4859 : ((a = c) ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_46 ∨ (spl0_47 ∨ spl0_49))))) := by
    clear * - f4855 f101
    first | exact resolve f4855 f101 | exact resolve f101 f4855 | grind (instances := 3000) only
  have f4861 : (False ∨ ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_46 ∨ (spl0_47 ∨ spl0_49))))) := by
    clear * - f4859 f70
    first | exact resolve f4859 f70 | exact resolve f70 f4859 | grind (instances := 3000) only
  have f4862 : ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_46 ∨ (spl0_47 ∨ spl0_49)))) := by
    clear * - f4861
    grind (instances := 3000) only
  have f4985 : ((old sk1 sk2 c) ∨ ((¬ spl0_21) ∨ (¬ spl0_30))) := by
    clear * - f248 f4827
    first | exact superpose f248 f4827 | exact superpose f4827 f248 | grind (instances := 3000) only
  have f4991 : (False ∨ ((¬ spl0_21) ∨ (¬ spl0_30))) := by
    clear * - f4985 f73
    first | exact resolve f4985 f73 | exact resolve f73 f4985 | grind (instances := 3000) only
  have f4992 : ((¬ spl0_21) ∨ (¬ spl0_30)) := by
    clear * - f4991
    grind (instances := 3000) only
  have f5003 : ((old sk3 sk0 sk4) ∨ ((sP1 sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ spl0_15))))))) := by
    clear * - f4808 f222
    first | exact resolve f4808 f222 | exact resolve f222 f4808 | grind (instances := 3000) only
  have f5004 : ((old sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((sP3 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_14 ∨ spl0_15))))))) := by
    clear * - f5003 f218
    first | exact resolve f5003 f218 | exact resolve f218 f5003 | grind (instances := 3000) only
  have f5005 : ((old sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((sP4 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_14 ∨ (spl0_15 ∨ spl0_27))))))) := by
    clear * - f5004 f276
    first | exact resolve f5004 f276 | exact resolve f276 f5004 | grind (instances := 3000) only
  have f5006 : ((old sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((sP5 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ spl0_27))))))) := by
    clear * - f5005 f214
    first | exact resolve f5005 f214 | exact resolve f214 f5005 | grind (instances := 3000) only
  have f5007 : ((old sk3 sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ spl0_27))))))) := by
    clear * - f5006 f210
    first | exact resolve f5006 f210 | exact resolve f210 f5006 | grind (instances := 3000) only
  have f5009 : ((a = sk1) ∨ (¬ spl0_32)) := by
    clear * - f308 f102
    first | exact resolve f308 f102 | exact resolve f102 f308 | grind (instances := 3000) only
  have f5010 : ((a = sk0) ∨ (¬ spl0_32)) := by
    clear * - f308 f101
    first | exact resolve f308 f101 | exact resolve f101 f308 | grind (instances := 3000) only
  have f5184 : ((¬ (old a a sk1)) ∨ (spl0_26 ∨ (¬ spl0_32))) := by
    clear * - f268 f5010
    first | exact superpose f268 f5010 | exact superpose f5010 f268 | grind (instances := 3000) only
  have f5217 : ((¬ (old a a a)) ∨ (spl0_26 ∨ (¬ spl0_32))) := by
    clear * - f5184 f5009
    grind (instances := 3000) only
  have f5231 : (False ∨ ((¬ spl0_10) ∨ (spl0_26 ∨ (¬ spl0_32)))) := by
    clear * - f5217 f195
    first | exact resolve f5217 f195 | exact resolve f195 f5217 | grind (instances := 3000) only
  have f5232 : ((¬ spl0_10) ∨ (spl0_26 ∨ (¬ spl0_32))) := by
    clear * - f5231
    grind (instances := 3000) only
  have f5251 : ((c = sk1) ∨ (¬ spl0_31)) := by
    clear * - f303 f100
    first | exact resolve f303 f100 | exact resolve f100 f303 | grind (instances := 3000) only
  have f5337 : ((old sk0 sk0 c) ∨ ((¬ spl0_26) ∨ (¬ spl0_31))) := by
    clear * - f269 f5251
    first | exact superpose f269 f5251 | exact superpose f5251 f269 | grind (instances := 3000) only
  have f5357 : (False ∨ ((¬ spl0_26) ∨ (¬ spl0_31))) := by
    clear * - f5337 f73
    first | exact resolve f5337 f73 | exact resolve f73 f5337 | grind (instances := 3000) only
  have f5358 : ((¬ spl0_26) ∨ (¬ spl0_31)) := by
    clear * - f5357
    grind (instances := 3000) only
  have f5376 : ((c = b) ∨ ((¬ spl0_19) ∨ (¬ spl0_30))) := by
    clear * - f4827 f2163
    grind (instances := 3000) only
  have f5398 : ((¬ (old b sk0 a)) ∨ (spl0_71 ∨ (¬ spl0_169))) := by
    clear * - f958 f3912
    grind (instances := 3000) only
  have f5408 : (False ∨ ((¬ spl0_19) ∨ (¬ spl0_30))) := by
    clear * - f5376 f71
    first | exact resolve f5376 f71 | exact resolve f71 f5376 | grind (instances := 3000) only
  have f5409 : ((¬ spl0_19) ∨ (¬ spl0_30)) := by
    clear * - f5408
    grind (instances := 3000) only
  have f5426 : ((¬ (old b a a)) ∨ ((¬ spl0_30) ∨ (spl0_71 ∨ (¬ spl0_169)))) := by
    clear * - f5398 f4826
    grind (instances := 3000) only
  have f5437 : (False ∨ ((¬ spl0_9) ∨ ((¬ spl0_30) ∨ (spl0_71 ∨ (¬ spl0_169))))) := by
    clear * - f5426 f190
    first | exact resolve f5426 f190 | exact resolve f190 f5426 | grind (instances := 3000) only
  have f5438 : ((¬ spl0_9) ∨ ((¬ spl0_30) ∨ (spl0_71 ∨ (¬ spl0_169)))) := by
    clear * - f5437
    grind (instances := 3000) only
  have f5457 : ((old b sk0 sk4) ∨ ((sP2 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_17) ∨ spl0_27)))))))) := by
    clear * - f5007 f559
    grind (instances := 3000) only
  have f5458 : ((old b sk0 sk4) ∨ ((¬ spl0_16) ∨ (¬ spl0_17))) := by
    clear * - f227 f559
    grind (instances := 3000) only
  have f5461 : ((¬ (sP2 b sk0 sk4)) ∨ ((¬ spl0_17) ∨ spl0_30)) := by
    clear * - f297 f559
    grind (instances := 3000) only
  have f5462 : ((sP2 sk3 sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_17) ∨ (spl0_27 ∨ spl0_71)))))))) := by
    clear * - f5457 f958
    first | exact resolve f5457 f958 | exact resolve f958 f5457 | grind (instances := 3000) only
  have f5463 : (False ∨ ((¬ spl0_16) ∨ ((¬ spl0_17) ∨ spl0_71))) := by
    clear * - f5458 f958
    first | exact resolve f5458 f958 | exact resolve f958 f5458 | grind (instances := 3000) only
  have f5464 : ((¬ spl0_16) ∨ ((¬ spl0_17) ∨ spl0_71)) := by
    clear * - f5463
    grind (instances := 3000) only
  have f5465 : ((sP2 b sk0 sk4) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_17) ∨ (spl0_27 ∨ spl0_71)))))))) := by
    clear * - f5462 f559
    grind (instances := 3000) only
  have f5466 : (False ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_17) ∨ (spl0_27 ∨ (spl0_30 ∨ spl0_71))))))))) := by
    clear * - f5465 f5461
    first | exact resolve f5465 f5461 | exact resolve f5461 f5465 | grind (instances := 3000) only
  have f5467 : ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_17) ∨ (spl0_27 ∨ (spl0_30 ∨ spl0_71)))))))) := by
    clear * - f5466
    grind (instances := 3000) only
  have f5476 : ((¬ (new b sk4 a)) ∨ ((¬ spl0_10) ∨ ((¬ spl0_20) ∨ (¬ spl0_26)))) := by
    clear * - f3397 f3788
    grind (instances := 3000) only
  have f5480 : (spl0_169 ∨ (¬ spl0_30)) := by
    clear * - f4825 f296 f3910
    grind (instances := 3000) only
  have f5527 : ((¬ (new b a a)) ∨ ((¬ spl0_10) ∨ ((¬ spl0_20) ∨ ((¬ spl0_26) ∨ (¬ spl0_169))))) := by
    clear * - f5476 f3912
    grind (instances := 3000) only
  have f5557 : (False ∨ ((¬ spl0_9) ∨ ((¬ spl0_10) ∨ ((¬ spl0_20) ∨ ((¬ spl0_26) ∨ (¬ spl0_169)))))) := by
    clear * - f5527 f4776
    first | exact resolve f5527 f4776 | exact resolve f4776 f5527 | grind (instances := 3000) only
  have f5558 : ((¬ spl0_9) ∨ ((¬ spl0_10) ∨ ((¬ spl0_20) ∨ ((¬ spl0_26) ∨ (¬ spl0_169))))) := by
    clear * - f5557
    grind (instances := 3000) only
  have s1 : (spl0_1 ∨ spl0_2) := by
    clear * - f162
    grind (splits := 100) only
  have s3 : (spl0_5 ∨ spl0_6) := by
    clear * - f178
    grind (splits := 100) only
  have s5 : (spl0_5 ∨ spl0_8) := by
    clear * - f186
    grind (splits := 100) only
  have s6 : (spl0_8 ∨ spl0_9) := by
    clear * - f191
    grind (splits := 100) only
  have s7 : (spl0_8 ∨ spl0_10) := by
    clear * - f196
    grind (splits := 100) only
  have s12 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ (spl0_16 ∨ spl0_27))))))) := by
    clear * - f278
    grind (splits := 100) only
  have s14 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_22 ∨ (spl0_23 ∨ (spl0_24 ∨ (spl0_25 ∨ (spl0_26 ∨ spl0_29))))))) := by
    clear * - f288
    grind (splits := 100) only
  have s15 : ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ (spl0_16 ∨ (spl0_27 ∨ spl0_30))))))) := by
    clear * - f299
    grind (splits := 100) only
  have s16 : ((¬ spl0_2) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (spl0_21 ∨ (spl0_28 ∨ spl0_31))))))) := by
    clear * - f304
    grind (splits := 100) only
  have s17 : ((¬ spl0_2) ∨ (spl0_22 ∨ (spl0_23 ∨ (spl0_24 ∨ (spl0_25 ∨ (spl0_26 ∨ (spl0_29 ∨ spl0_32))))))) := by
    clear * - f309
    grind (splits := 100) only
  have s20 : ((¬ spl0_1) ∨ (¬ spl0_5)) := by
    clear * - f376
    grind (splits := 100) only
  have s21 : ((¬ spl0_1) ∨ spl0_2) := by
    clear * - f378
    grind (splits := 100) only
  have s38 : ((¬ spl0_18) ∨ (¬ spl0_26)) := by
    clear * - f503
    grind (splits := 100) only
  have s40 : ((¬ spl0_14) ∨ (¬ spl0_26)) := by
    clear * - f530
    grind (splits := 100) only
  have s41 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_14) ∨ (spl0_52 ∨ (spl0_53 ∨ spl0_54))))) := by
    clear * - f551
    grind (splits := 100) only
  have s42 : ((¬ spl0_17) ∨ (¬ spl0_27)) := by
    clear * - f590
    grind (splits := 100) only
  have s45 : (¬ spl0_49) := by
    clear * - f648
    grind (splits := 100) only
  have s66 : ((¬ spl0_13) ∨ ((¬ spl0_17) ∨ spl0_72)) := by
    clear * - f1014
    grind (splits := 100) only
  have s67 : (spl0_1 ∨ ((¬ spl0_15) ∨ (¬ spl0_17))) := by
    clear * - f1027
    grind (splits := 100) only
  have s71 : (¬ spl0_52) := by
    clear * - f1083
    grind (splits := 100) only
  have s74 : (¬ spl0_53) := by
    clear * - f1140
    grind (splits := 100) only
  have s83 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ (spl0_52 ∨ (spl0_53 ∨ spl0_54)))))) := by
    clear * - f1261
    grind (splits := 100) only
  have s87 : ((¬ spl0_12) ∨ (¬ spl0_26)) := by
    clear * - f1289
    grind (splits := 100) only
  have s89 : (¬ spl0_54) := by
    clear * - f1342
    grind (splits := 100) only
  have s95 : ((¬ spl0_15) ∨ (¬ spl0_20)) := by
    clear * - f1454
    grind (splits := 100) only
  have s107 : ((¬ spl0_15) ∨ ((¬ spl0_21) ∨ (¬ spl0_26))) := by
    clear * - f1762
    grind (splits := 100) only
  have s122 : (spl0_1 ∨ ((¬ spl0_15) ∨ (¬ spl0_19))) := by
    clear * - f1896
    grind (splits := 100) only
  have s126 : ((¬ spl0_1) ∨ (¬ spl0_19)) := by
    clear * - f1994
    grind (splits := 100) only
  have s129 : ((¬ spl0_1) ∨ ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ ((¬ spl0_15) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_20 ∨ spl0_21)))))))) := by
    clear * - f2004
    grind (splits := 100) only
  have s135 : ((¬ spl0_1) ∨ (¬ spl0_17)) := by
    clear * - f2031
    grind (splits := 100) only
  have s140 : ((¬ spl0_1) ∨ (¬ spl0_18)) := by
    clear * - f2063
    grind (splits := 100) only
  have s145 : ((¬ spl0_16) ∨ ((¬ spl0_19) ∨ spl0_71)) := by
    clear * - f2184
    grind (splits := 100) only
  have s182 : ((¬ spl0_13) ∨ ((¬ spl0_19) ∨ spl0_72)) := by
    clear * - f2841
    grind (splits := 100) only
  have s188 : (¬ spl0_72) := by
    clear * - f2886
    grind (splits := 100) only
  have s192 : (¬ spl0_24) := by
    clear * - f2948
    grind (splits := 100) only
  have s196 : ((¬ spl0_23) ∨ spl0_54) := by
    clear * - f3028
    grind (splits := 100) only
  have s197 : (spl0_3 ∨ (¬ spl0_22)) := by
    clear * - f3059
    grind (splits := 100) only
  have s199 : ((¬ spl0_6) ∨ (¬ spl0_47)) := by
    clear * - f3069
    grind (splits := 100) only
  have s202 : ((¬ spl0_17) ∨ ((¬ spl0_26) ∨ (¬ spl0_71))) := by
    clear * - f3220
    grind (splits := 100) only
  have s205 : ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ spl0_16))))))) := by
    clear * - f3223
    grind (splits := 100) only
  have s212 : ((¬ spl0_16) ∨ ((¬ spl0_21) ∨ (¬ spl0_26))) := by
    clear * - f3284
    grind (splits := 100) only
  have s214 : ((¬ spl0_13) ∨ (¬ spl0_21)) := by
    clear * - f3311
    grind (splits := 100) only
  have s218 : ((¬ spl0_16) ∨ (¬ spl0_20)) := by
    clear * - f3382
    grind (splits := 100) only
  have s222 : ((¬ spl0_13) ∨ (¬ spl0_20)) := by
    clear * - f3498
    grind (splits := 100) only
  have s246 : ((¬ spl0_20) ∨ (¬ spl0_27)) := by
    clear * - f4008
    grind (splits := 100) only
  have s267 : ((¬ spl0_19) ∨ (¬ spl0_27)) := by
    clear * - f4219
    grind (splits := 100) only
  have s277 : ((¬ spl0_26) ∨ (¬ spl0_28)) := by
    clear * - f4378
    grind (splits := 100) only
  have s279 : ((¬ spl0_19) ∨ ((¬ spl0_26) ∨ (¬ spl0_71))) := by
    clear * - f4382
    grind (splits := 100) only
  have s285 : (¬ spl0_29) := by
    clear * - f4539
    grind (splits := 100) only
  have s295 : ((¬ spl0_22) ∨ (spl0_29 ∨ (¬ spl0_47))) := by
    clear * - f4651
    grind (splits := 100) only
  have s296 : (spl0_1 ∨ (¬ spl0_25)) := by
    clear * - f4670
    grind (splits := 100) only
  have s299 : ((¬ spl0_6) ∨ (¬ spl0_28)) := by
    clear * - f4684
    grind (splits := 100) only
  have s305 : ((¬ spl0_2) ∨ ((¬ spl0_6) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (¬ spl0_25)))))))) := by
    clear * - f4719
    grind (splits := 100) only
  have s310 : ((¬ spl0_21) ∨ (¬ spl0_27)) := by
    clear * - f4736
    grind (splits := 100) only
  have s312 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_17 ∨ (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ ((¬ spl0_27) ∨ spl0_28))))))) := by
    clear * - f4748
    grind (splits := 100) only
  have s314 : ((¬ spl0_30) ∨ spl0_169) := by
    clear * - f4829
    grind (splits := 100) only
  have s316 : (¬ spl0_46) := by
    clear * - f4849
    grind (splits := 100) only
  have s317 : ((¬ spl0_2) ∨ ((¬ spl0_3) ∨ (spl0_46 ∨ (spl0_47 ∨ spl0_49)))) := by
    clear * - f4862
    grind (splits := 100) only
  have s322 : ((¬ spl0_21) ∨ (¬ spl0_30)) := by
    clear * - f4992
    grind (splits := 100) only
  have s326 : ((¬ spl0_10) ∨ (spl0_26 ∨ (¬ spl0_32))) := by
    clear * - f5232
    grind (splits := 100) only
  have s327 : ((¬ spl0_26) ∨ (¬ spl0_31)) := by
    clear * - f5358
    grind (splits := 100) only
  have s328 : ((¬ spl0_19) ∨ (¬ spl0_30)) := by
    clear * - f5409
    grind (splits := 100) only
  have s334 : ((¬ spl0_9) ∨ ((¬ spl0_30) ∨ (spl0_71 ∨ (¬ spl0_169)))) := by
    clear * - f5438
    grind (splits := 100) only
  have s337 : ((¬ spl0_16) ∨ ((¬ spl0_17) ∨ spl0_71)) := by
    clear * - f5464
    grind (splits := 100) only
  have s338 : ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_17) ∨ (spl0_27 ∨ (spl0_30 ∨ spl0_71)))))))) := by
    clear * - f5467
    grind (splits := 100) only
  have s341 : ((¬ spl0_30) ∨ spl0_169) := by
    clear * - f5480
    grind (splits := 100) only
  have s345 : ((¬ spl0_9) ∨ ((¬ spl0_10) ∨ ((¬ spl0_20) ∨ ((¬ spl0_26) ∨ (¬ spl0_169))))) := by
    clear * - f5558
    grind (splits := 100) only
  have s351 : ((¬ spl0_13) ∨ (¬ spl0_19)) := by
    clear * - s182 s188
    grind (splits := 100) only
  have s352 : (¬ spl0_23) := by
    clear * - s196 s89
    grind (splits := 100) only
  have s354 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ ((¬ spl0_12) ∨ (spl0_22 ∨ (spl0_52 ∨ spl0_53))))) := by
    clear * - s83 s89
    grind (splits := 100) only
  have s356 : ((¬ spl0_13) ∨ (¬ spl0_17)) := by
    clear * - s66 s188
    grind (splits := 100) only
  have s358 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (¬ spl0_14))) := by
    clear * - s41 s89 s74 s71
    grind (splits := 100) only
  have s362 : ((¬ spl0_2) ∨ (spl0_22 ∨ (spl0_25 ∨ (spl0_26 ∨ spl0_32)))) := by
    clear * - s17 s285 s192 s352
    grind (splits := 100) only
  have s363 : ((¬ spl0_2) ∨ ((¬ spl0_8) ∨ (spl0_22 ∨ (spl0_25 ∨ spl0_26)))) := by
    clear * - s14 s285 s192 s352
    grind (splits := 100) only
  have s365 : ((¬ spl0_19) ∨ ((¬ spl0_16) ∨ (¬ spl0_26))) := by
    clear * - s145 s279
    grind (splits := 100) only
  have s366 : ((¬ spl0_16) ∨ (spl0_28 ∨ ((¬ spl0_26) ∨ (¬ spl0_2)))) := by
    clear * - s202 s337 s16 s365 s212 s218 s327 s38
    grind (splits := 100) only
  have s367 : ((¬ spl0_15) ∨ (spl0_28 ∨ ((¬ spl0_26) ∨ spl0_1))) := by
    clear * - s16 s67 s95 s107 s122 s1 s327 s38
    grind (splits := 100) only
  have s370 : (spl0_26 ∨ ((¬ spl0_10) ∨ (spl0_22 ∨ spl0_1))) := by
    clear * - s326 s362 s296 s1
    grind (splits := 100) only
  have s371 : ((¬ spl0_19) ∨ (spl0_15 ∨ (spl0_14 ∨ (spl0_13 ∨ (spl0_12 ∨ (spl0_16 ∨ (¬ spl0_2))))))) := by
    clear * - s15 s267 s328
    grind (splits := 100) only
  have s372 : ((¬ spl0_21) ∨ (spl0_15 ∨ (spl0_14 ∨ (spl0_13 ∨ (spl0_12 ∨ (spl0_16 ∨ (¬ spl0_2))))))) := by
    clear * - s15 s310 s322
    grind (splits := 100) only
  have s373 : ((¬ spl0_20) ∨ (spl0_15 ∨ (spl0_14 ∨ (spl0_13 ∨ (spl0_12 ∨ (spl0_16 ∨ ((¬ spl0_26) ∨ ((¬ spl0_9) ∨ ((¬ spl0_10) ∨ (¬ spl0_2)))))))))) := by
    clear * - s314 s15 s345 s246
    grind (splits := 100) only
  have s374 : (spl0_15 ∨ (spl0_14 ∨ (spl0_13 ∨ (spl0_12 ∨ ((¬ spl0_26) ∨ ((¬ spl0_9) ∨ ((¬ spl0_10) ∨ (spl0_28 ∨ (¬ spl0_2))))))))) := by
    clear * - s334 s341 s338 s42 s202 s16 s373 s372 s371 s327 s38 s366
    grind (splits := 100) only
  have s375 : ((¬ spl0_13) ∨ (spl0_18 ∨ (spl0_31 ∨ (spl0_28 ∨ (¬ spl0_2))))) := by
    clear * - s16 s356 s351 s214 s222
    grind (splits := 100) only
  have s377 : (spl0_8 ∨ (spl0_15 ∨ ((¬ spl0_26) ∨ (¬ spl0_2)))) := by
    clear * - s374 s6 s7 s87 s40 s375 s38 s327 s277
    grind (splits := 100) only
  have s378 : ((¬ spl0_26) ∨ spl0_1) := by
    clear * - s312 s42 s246 s12 s377 s371 s375 s367 s366 s38 s40 s87 s277 s327 s1
    grind (splits := 100) only
  have s379 : (spl0_22 ∨ spl0_1) := by
    clear * - s7 s370 s363 s296 s1 s378
    grind (splits := 100) only
  have s380 : spl0_1 := by
    clear * - s317 s197 s295 s379 s1 s316 s45 s285
    grind (splits := 100) only
  have s381 : (¬ spl0_18) := by
    clear * - s140 s380
    grind (splits := 100) only
  have s382 : (¬ spl0_17) := by
    clear * - s135 s380
    grind (splits := 100) only
  have s383 : (¬ spl0_19) := by
    clear * - s126 s380
    grind (splits := 100) only
  have s384 : spl0_2 := by
    clear * - s21 s380
    grind (splits := 100) only
  have s385 : (¬ spl0_5) := by
    clear * - s20 s380
    grind (splits := 100) only
  have s387 : spl0_8 := by
    clear * - s5 s385
    grind (splits := 100) only
  have s388 : spl0_6 := by
    clear * - s3 s385
    grind (splits := 100) only
  have s390 : (¬ spl0_14) := by
    clear * - s358 s384 s387
    grind (splits := 100) only
  have s392 : (¬ spl0_28) := by
    clear * - s299 s388
    grind (splits := 100) only
  have s393 : (¬ spl0_47) := by
    clear * - s199 s388
    grind (splits := 100) only
  have s394 : (¬ spl0_3) := by
    clear * - s317 s45 s384 s316 s393
    grind (splits := 100) only
  have s395 : (¬ spl0_22) := by
    clear * - s197 s394
    grind (splits := 100) only
  have s397 : (¬ spl0_12) := by
    clear * - s354 s74 s71 s387 s384 s395
    grind (splits := 100) only
  have s399 : ((¬ spl0_15) ∨ (¬ spl0_26)) := by
    clear * - s129 s95 s107 s388 s381 s382 s387 s384 s380
    grind (splits := 100) only
  have s400 : (¬ spl0_26) := by
    clear * - s399 s205 s375 s366 s327 s384 s388 s390 s387 s397 s381 s392
    grind (splits := 100) only
  have s401 : spl0_25 := by
    clear * - s363 s387 s384 s395 s400
    grind (splits := 100) only
  have s403 : spl0_20 := by
    clear * - s305 s388 s387 s383 s381 s382 s384 s401
    grind (splits := 100) only
  have s404 : (¬ spl0_27) := by
    clear * - s246 s403
    grind (splits := 100) only
  have s405 : (¬ spl0_13) := by
    clear * - s222 s403
    grind (splits := 100) only
  have s406 : (¬ spl0_16) := by
    clear * - s218 s403
    grind (splits := 100) only
  have s407 : (¬ spl0_15) := by
    clear * - s95 s403
    grind (splits := 100) only
  have s409 : False := by
    clear * - s12 s406 s405 s397 s390 s387 s384 s407 s404
    grind (splits := 100) only
  exact s409


set_option maxHeartbeats 8000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X1 ∨ X0 = X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_5 : ∀ (X Y Z : G), old b b b ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z Z Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old Z Z (sF2 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_5_5 : ∀ (X Y Z : G), old b b (sF5 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_6_6 : ∀ (X Y Z : G), old b b (sF7 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X2 X1 ∨ X0 = X2) := by
  classical
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have f1 : (a ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using ac
  have f2 : (b ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using bc
  have f3 : (∀ (X0 : G), (¬ (old a b X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p3
  have f4 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XY
  have f5 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XZ
  have f6 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4YZ
  have f8 : (∀ (X0 X1 X2 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X2 X2 X1)) ∨ (X0 = X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_2
  have f22 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_0
  have f23 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_1
  have f24 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_2
  have f26 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_0
  have f27 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_1
  have f28 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old b b (sF0 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_2
  have f29 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_3
  have f31 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_0
  have f32 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_1
  have f33 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_2
  have f36 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_5
  have f38 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_0
  have f39 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_1
  have f40 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_2
  have f42 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old X2 X2 X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_4
  have f44 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_0
  have f45 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_1
  have f46 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_2
  have f48 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old X2 X2 (sF2 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_4
  have f50 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_0
  have f51 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_1
  have f52 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_2
  have f55 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old b b (sF5 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_5
  have f57 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_0
  have f59 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_2
  have f60 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_3
  have f63 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old b b (sF7 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_6
  have f65 : (∀ (X0 X1 X2 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using new_imp
  have f66 : (new sk0 sk0 sk1) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_0
  have f67 : (new sk2 sk2 sk1) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_1
  have f68 : (sk0 ≠ sk2) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_2
  have f69 : (new sk0 sk0 sk1) := by
    clear * - f66
    grind (instances := 3000) only
  have f70 : (new sk2 sk2 sk1) := by
    clear * - f67
    grind (instances := 3000) only
  have f71 : (sk0 ≠ sk2) := by
    clear * - f68
    grind (instances := 3000) only
  have f72 : (∀ (X2 X0 X1 : G), ((sP0 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by
    clear * - f65
    grind (instances := 3000) only
  have f89 : (∀ (X2 X0 X1 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X2 X2 X1)) ∨ (X0 = X2)))) := by
    clear * - f8
    grind (instances := 3000) only
  have f95 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by
    clear * - f24
    grind (instances := 3000) only
  have f96 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by
    clear * - f23
    grind (instances := 3000) only
  have f97 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by
    clear * - f22
    grind (instances := 3000) only
  have f98 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by
    clear * - f29
    grind (instances := 3000) only
  have f99 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old b b (sF0 X0 X1 X2)))) := by
    clear * - f28
    grind (instances := 3000) only
  have f100 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f27
    grind (instances := 3000) only
  have f101 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f26
    grind (instances := 3000) only
  have f102 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f36
    grind (instances := 3000) only
  have f105 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by
    clear * - f33
    grind (instances := 3000) only
  have f106 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f32
    grind (instances := 3000) only
  have f107 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f31
    grind (instances := 3000) only
  have f108 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old X2 X2 X2))) := by
    clear * - f42
    grind (instances := 3000) only
  have f110 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f40
    grind (instances := 3000) only
  have f111 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f39
    grind (instances := 3000) only
  have f112 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f38
    grind (instances := 3000) only
  have f113 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old X2 X2 (sF2 X0 X1 X2)))) := by
    clear * - f48
    grind (instances := 3000) only
  have f115 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by
    clear * - f46
    grind (instances := 3000) only
  have f116 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by
    clear * - f45
    grind (instances := 3000) only
  have f117 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f44
    grind (instances := 3000) only
  have f118 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old b b (sF5 X0 X1 X2)))) := by
    clear * - f55
    grind (instances := 3000) only
  have f121 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by
    clear * - f52
    grind (instances := 3000) only
  have f122 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f51
    grind (instances := 3000) only
  have f123 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f50
    grind (instances := 3000) only
  have f124 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old b b (sF7 X0 X1 X2)))) := by
    clear * - f63
    grind (instances := 3000) only
  have f127 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f60
    grind (instances := 3000) only
  have f128 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f59
    grind (instances := 3000) only
  have f130 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by
    clear * - f57
    grind (instances := 3000) only
  have f131 : (∀ (X0 : G), (¬ (old a b X0))) := by
    clear * - f3
    grind (instances := 3000) only
  have f132 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by
    clear * - f6
    grind (instances := 3000) only
  have f133 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by
    clear * - f5
    grind (instances := 3000) only
  have f134 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by
    clear * - f4
    grind (instances := 3000) only
  have f135 : (c ≠ b) := by
    clear * - f2
    grind (instances := 3000) only
  have f136 : (a ≠ c) := by
    clear * - f1
    grind (instances := 3000) only
  let spl0_1 : Prop := (a = b)
  have f154 : (spl0_1 ↔ (a = b)) := Iff.rfl
  clear_value spl0_1
  have f155 : ((a ≠ b) ∨ spl0_1) := by
    clear * - f154
    grind (instances := 3000) only
  have f156 : ((a = b) ∨ (¬ spl0_1)) := by
    clear * - f154
    grind (instances := 3000) only
  let spl0_2 : Prop := (∀ (X2 X0 X1 : G), (¬ (sP6 X0 X1 X2)))
  have f158 : (spl0_2 ↔ (∀ (X2 X0 X1 : G), (¬ (sP6 X0 X1 X2)))) := Iff.rfl
  clear_value spl0_2
  have f159 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (¬ spl0_2))) := by
    clear * - f158
    grind (instances := 3000) only
  have f160 : (spl0_1 ∨ spl0_2) := by
    clear * - f130 f158 f154
    grind (instances := 3000) only
  let spl0_3 : Prop := (old b b b)
  have f162 : (spl0_3 ↔ (old b b b)) := Iff.rfl
  clear_value spl0_3
  have f164 : ((old b b b) ∨ (¬ spl0_3)) := by
    clear * - f162
    grind (instances := 3000) only
  let spl0_4 : Prop := (∀ (X2 X0 X1 : G), (¬ (sP3 X0 X1 X2)))
  have f166 : (spl0_4 ↔ (∀ (X2 X0 X1 : G), (¬ (sP3 X0 X1 X2)))) := Iff.rfl
  clear_value spl0_4
  have f167 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (¬ spl0_4))) := by
    clear * - f166
    grind (instances := 3000) only
  have f168 : (spl0_3 ∨ spl0_4) := by
    clear * - f110 f166 f162
    grind (instances := 3000) only
  let spl0_6 : Prop := (∀ (X2 X0 X1 : G), (¬ (sP2 X0 X1 X2)))
  have f174 : (spl0_6 ↔ (∀ (X2 X0 X1 : G), (¬ (sP2 X0 X1 X2)))) := Iff.rfl
  clear_value spl0_6
  have f175 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (¬ spl0_6))) := by
    clear * - f174
    grind (instances := 3000) only
  have f182 : (spl0_3 ∨ spl0_6) := by
    clear * - f102 f174 f162
    grind (instances := 3000) only
  let spl0_10 : Prop := (new c c b)
  have f193 : (spl0_10 ↔ (new c c b)) := Iff.rfl
  clear_value spl0_10
  have f194 : ((¬ (new c c b)) ∨ spl0_10) := by
    clear * - f193
    grind (instances := 3000) only
  have f195 : ((new c c b) ∨ (¬ spl0_10)) := by
    clear * - f193
    grind (instances := 3000) only
  have f200 : (∀ (X2 X0 X1 : G), ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (a = X0)))))))))) := by
    clear * - f72 f97
    first | exact resolve f72 f97 | exact resolve f97 f72 | grind (instances := 3000) only
  have f201 : (∀ (X2 X0 X1 : G), ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (b = X1)))))))))) := by
    clear * - f72 f96
    first | exact resolve f72 f96 | exact resolve f96 f72 | grind (instances := 3000) only
  have f202 : (∀ (X2 X0 X1 : G), ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (c = X2)))))))))) := by
    clear * - f72 f95
    first | exact resolve f72 f95 | exact resolve f95 f72 | grind (instances := 3000) only
  have f203 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (c = X2)))))))) ∨ (¬ spl0_6))) := by
    clear * - f202 f175
    first | exact resolve f202 f175 | exact resolve f175 f202 | grind (instances := 3000) only
  let spl0_12 : Prop := (c = sk2)
  have f242 : (spl0_12 ↔ (c = sk2)) := Iff.rfl
  clear_value spl0_12
  have f243 : ((c ≠ sk2) ∨ spl0_12) := by
    clear * - f242
    grind (instances := 3000) only
  have f244 : ((c = sk2) ∨ (¬ spl0_12)) := by
    clear * - f242
    grind (instances := 3000) only
  let spl0_13 : Prop := (b = sk1)
  have f246 : (spl0_13 ↔ (b = sk1)) := Iff.rfl
  clear_value spl0_13
  have f247 : ((b ≠ sk1) ∨ spl0_13) := by
    clear * - f246
    grind (instances := 3000) only
  have f248 : ((b = sk1) ∨ (¬ spl0_13)) := by
    clear * - f246
    grind (instances := 3000) only
  let spl0_14 : Prop := (c = sk1)
  have f250 : (spl0_14 ↔ (c = sk1)) := Iff.rfl
  clear_value spl0_14
  have f251 : ((c ≠ sk1) ∨ spl0_14) := by
    clear * - f250
    grind (instances := 3000) only
  have f252 : ((c = sk1) ∨ (¬ spl0_14)) := by
    clear * - f250
    grind (instances := 3000) only
  let spl0_15 : Prop := (old sk2 sk2 sk1)
  have f254 : (spl0_15 ↔ (old sk2 sk2 sk1)) := Iff.rfl
  clear_value spl0_15
  have f255 : ((¬ (old sk2 sk2 sk1)) ∨ spl0_15) := by
    clear * - f254
    grind (instances := 3000) only
  have f256 : ((old sk2 sk2 sk1) ∨ (¬ spl0_15)) := by
    clear * - f254
    grind (instances := 3000) only
  let spl0_16 : Prop := (c = sk0)
  have f259 : (spl0_16 ↔ (c = sk0)) := Iff.rfl
  clear_value spl0_16
  have f260 : ((c ≠ sk0) ∨ spl0_16) := by
    clear * - f259
    grind (instances := 3000) only
  have f261 : ((c = sk0) ∨ (¬ spl0_16)) := by
    clear * - f259
    grind (instances := 3000) only
  let spl0_17 : Prop := (old sk0 sk0 sk1)
  have f263 : (spl0_17 ↔ (old sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_17
  have f264 : ((¬ (old sk0 sk0 sk1)) ∨ spl0_17) := by
    clear * - f263
    grind (instances := 3000) only
  have f265 : ((old sk0 sk0 sk1) ∨ (¬ spl0_17)) := by
    clear * - f263
    grind (instances := 3000) only
  have f331 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_1))) := by
    clear * - f131 f156
    first | exact superpose f131 f156 | exact superpose f156 f131 | grind (instances := 3000) only
  have f332 : (False ∨ ((¬ spl0_1) ∨ (¬ spl0_3))) := by
    clear * - f331 f164
    first | exact resolve f331 f164 | exact resolve f164 f331 | grind (instances := 3000) only
  have f333 : ((¬ spl0_1) ∨ (¬ spl0_3)) := by
    clear * - f332
    grind (instances := 3000) only
  have f337 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (b = X2)))))))) ∨ (¬ spl0_6))) := by
    clear * - f203 f100
    first | exact resolve f203 f100 | exact resolve f100 f203 | grind (instances := 3000) only
  have f338 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (b = X2))))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f337 f167
    first | exact resolve f337 f167 | exact resolve f167 f337 | grind (instances := 3000) only
  have f342 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (b = X2)))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f338 f122
    first | exact resolve f338 f122 | exact resolve f122 f338 | grind (instances := 3000) only
  have f346 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((c = X2) ∨ (b = X2))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f342 f127
    first | exact resolve f342 f127 | exact resolve f127 f342 | grind (instances := 3000) only
  have f349 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((c = X2) ∨ ((b = X2) ∨ (old b b (sF1 X0 X1 X2)))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f346 f116
    first | exact resolve f346 f116 | exact resolve f116 f346 | grind (instances := 3000) only
  have f353 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ (b = X2)))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f349 f331
    first | exact resolve f349 f331 | exact resolve f331 f349 | grind (instances := 3000) only
  have f377 : ((old sk0 sk0 sk1) ∨ ((c = sk1) ∨ ((b = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f353 f69
    first | exact resolve f353 f69 | exact resolve f69 f353 | grind (instances := 3000) only
  have f378 : ((old sk2 sk2 sk1) ∨ ((c = sk1) ∨ ((b = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f353 f70
    first | exact resolve f353 f70 | exact resolve f70 f353 | grind (instances := 3000) only
  have f379 : (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f378 f174 f166 f154 f254 f250 f246
    grind (instances := 3000) only
  have f380 : (spl0_13 ∨ (spl0_14 ∨ (spl0_17 ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f377 f174 f166 f154 f263 f250 f246
    grind (instances := 3000) only
  let spl0_18 : Prop := (old sk0 sk0 b)
  have f484 : (spl0_18 ↔ (old sk0 sk0 b)) := Iff.rfl
  clear_value spl0_18
  have f485 : ((¬ (old sk0 sk0 b)) ∨ spl0_18) := by
    clear * - f484
    grind (instances := 3000) only
  let spl0_19 : Prop := (old sk2 sk2 b)
  have f489 : (spl0_19 ↔ (old sk2 sk2 b)) := Iff.rfl
  clear_value spl0_19
  have f490 : ((¬ (old sk2 sk2 b)) ∨ spl0_19) := by
    clear * - f489
    grind (instances := 3000) only
  have f491 : ((old sk2 sk2 b) ∨ (¬ spl0_19)) := by
    clear * - f489
    grind (instances := 3000) only
  have f503 : ((new c c sk1) ∨ (¬ spl0_12)) := by
    clear * - f70 f244
    first | exact superpose f70 f244 | exact superpose f244 f70 | grind (instances := 3000) only
  have f506 : ((new c c b) ∨ ((¬ spl0_12) ∨ (¬ spl0_13))) := by
    clear * - f503 f248
    grind (instances := 3000) only
  let spl0_20 : Prop := (b = sk0)
  have f522 : (spl0_20 ↔ (b = sk0)) := Iff.rfl
  clear_value spl0_20
  have f523 : ((b ≠ sk0) ∨ spl0_20) := by
    clear * - f522
    grind (instances := 3000) only
  have f524 : ((b = sk0) ∨ (¬ spl0_20)) := by
    clear * - f522
    grind (instances := 3000) only
  have f2779 : (False ∨ (spl0_10 ∨ ((¬ spl0_12) ∨ (¬ spl0_13)))) := by
    clear * - f506 f194
    first | exact resolve f506 f194 | exact resolve f194 f506 | grind (instances := 3000) only
  have f2780 : (spl0_10 ∨ ((¬ spl0_12) ∨ (¬ spl0_13))) := by
    clear * - f2779
    grind (instances := 3000) only
  have f2905 : ((new c c sk1) ∨ (¬ spl0_16)) := by
    clear * - f69 f261
    first | exact superpose f69 f261 | exact superpose f261 f69 | grind (instances := 3000) only
  have f2906 : ((new c c b) ∨ ((¬ spl0_13) ∨ (¬ spl0_16))) := by
    clear * - f2905 f248
    grind (instances := 3000) only
  have f2909 : (False ∨ (spl0_10 ∨ ((¬ spl0_13) ∨ (¬ spl0_16)))) := by
    clear * - f2906 f194
    first | exact resolve f2906 f194 | exact resolve f194 f2906 | grind (instances := 3000) only
  have f2910 : (spl0_10 ∨ ((¬ spl0_13) ∨ (¬ spl0_16))) := by
    clear * - f2909
    grind (instances := 3000) only
  have f2915 : (∀ (X0 : G), (((¬ (old X0 X0 sk1)) ∨ (sk2 = X0)) ∨ (¬ spl0_15))) := by
    clear * - f256 f89
    first | exact resolve f256 f89 | exact resolve f89 f256 | grind (instances := 3000) only
  have f2948 : ((sk0 = sk2) ∨ ((¬ spl0_15) ∨ (¬ spl0_17))) := by
    clear * - f2915 f265
    first | exact resolve f2915 f265 | exact resolve f265 f2915 | grind (instances := 3000) only
  have f2950 : (False ∨ ((¬ spl0_15) ∨ (¬ spl0_17))) := by
    clear * - f2948 f71
    first | exact resolve f2948 f71 | exact resolve f71 f2948 | grind (instances := 3000) only
  have f2951 : ((¬ spl0_15) ∨ (¬ spl0_17)) := by
    clear * - f2950
    grind (instances := 3000) only
  let spl0_61 : Prop := (b = sk2)
  have f6286 : (spl0_61 ↔ (b = sk2)) := Iff.rfl
  clear_value spl0_61
  have f6287 : ((b ≠ sk2) ∨ spl0_61) := by
    clear * - f6286
    grind (instances := 3000) only
  have f6288 : ((b = sk2) ∨ (¬ spl0_61)) := by
    clear * - f6286
    grind (instances := 3000) only
  have f6340 : ((b ≠ sk0) ∨ (¬ spl0_61)) := by
    clear * - f71 f6288
    first | exact superpose f71 f6288 | exact superpose f6288 f71 | grind (instances := 3000) only
  have f6736 : ((¬ (old sk0 sk0 b)) ∨ ((¬ spl0_13) ∨ spl0_17)) := by
    clear * - f264 f248
    grind (instances := 3000) only
  have f6815 : ((¬ (old sk2 sk2 b)) ∨ ((¬ spl0_13) ∨ spl0_15)) := by
    clear * - f255 f248
    grind (instances := 3000) only
  have f6863 : (False ∨ ((¬ spl0_13) ∨ (spl0_15 ∨ (¬ spl0_19)))) := by
    clear * - f6815 f491
    first | exact resolve f6815 f491 | exact resolve f491 f6815 | grind (instances := 3000) only
  have f6864 : ((¬ spl0_13) ∨ (spl0_15 ∨ (¬ spl0_19))) := by
    clear * - f6863
    grind (instances := 3000) only
  have f7134 : (∀ (X2 X0 X1 : G), (((sP2 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (c = X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f202 f159
    first | exact resolve f202 f159 | exact resolve f159 f202 | grind (instances := 3000) only
  have f7135 : (∀ (X2 X0 X1 : G), (((sP2 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (b = X1)))))))) ∨ (¬ spl0_2))) := by
    clear * - f201 f159
    first | exact resolve f201 f159 | exact resolve f159 f201 | grind (instances := 3000) only
  have f7136 : (∀ (X2 X0 X1 : G), (((sP2 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (a = X0)))))))) ∨ (¬ spl0_2))) := by
    clear * - f200 f159
    first | exact resolve f200 f159 | exact resolve f159 f200 | grind (instances := 3000) only
  have f7137 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ (c = X0)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7134 f107
    first | exact resolve f7134 f107 | exact resolve f107 f7134 | grind (instances := 3000) only
  have f7138 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ (a = X1)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7134 f106
    first | exact resolve f7134 f106 | exact resolve f106 f7134 | grind (instances := 3000) only
  have f7140 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ (a = X1))))))) ∨ (¬ spl0_2))) := by
    clear * - f7138 f111
    first | exact resolve f7138 f111 | exact resolve f111 f7138 | grind (instances := 3000) only
  have f7141 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ (c = X0))))))) ∨ (¬ spl0_2))) := by
    clear * - f7137 f112
    first | exact resolve f7137 f112 | exact resolve f112 f7137 | grind (instances := 3000) only
  have f7142 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ (c = X0)))))) ∨ (¬ spl0_2))) := by
    clear * - f7141 f117
    first | exact resolve f7141 f117 | exact resolve f117 f7141 | grind (instances := 3000) only
  have f7145 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ ((c = X0) ∨ (c = X1)))))) ∨ (¬ spl0_2))) := by
    clear * - f7142 f101
    first | exact resolve f7142 f101 | exact resolve f101 f7142 | grind (instances := 3000) only
  have f7148 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ ((c = X0) ∨ (c = X1))))) ∨ (¬ spl0_2))) := by
    clear * - f7145 f123
    first | exact resolve f7145 f123 | exact resolve f123 f7145 | grind (instances := 3000) only
  have f7151 : (∀ (X2 X0 X1 : G), (((sP3 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((b = X1) ∨ (a = X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7135 f105
    first | exact resolve f7135 f105 | exact resolve f105 f7135 | grind (instances := 3000) only
  have f7168 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ (c = X0)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7136 f107
    first | exact resolve f7136 f107 | exact resolve f107 f7136 | grind (instances := 3000) only
  have f7169 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ (a = X1)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7136 f106
    first | exact resolve f7136 f106 | exact resolve f106 f7136 | grind (instances := 3000) only
  have f7171 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ (a = X1))))))) ∨ (¬ spl0_2))) := by
    clear * - f7169 f111
    first | exact resolve f7169 f111 | exact resolve f111 f7169 | grind (instances := 3000) only
  have f7172 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ (c = X0))))))) ∨ (¬ spl0_2))) := by
    clear * - f7168 f112
    first | exact resolve f7168 f112 | exact resolve f112 f7168 | grind (instances := 3000) only
  have f7173 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ (c = X0)))))) ∨ (¬ spl0_2))) := by
    clear * - f7172 f117
    first | exact resolve f7172 f117 | exact resolve f117 f7172 | grind (instances := 3000) only
  have f7184 : ((old sk0 sk0 sk1) ∨ ((c = sk1) ∨ ((c = sk0) ∨ ((c = sk0) ∨ (¬ spl0_2))))) := by
    clear * - f7148 f69
    first | exact resolve f7148 f69 | exact resolve f69 f7148 | grind (instances := 3000) only
  have f7185 : ((old sk2 sk2 sk1) ∨ ((c = sk1) ∨ ((c = sk2) ∨ ((c = sk2) ∨ (¬ spl0_2))))) := by
    clear * - f7148 f70
    first | exact resolve f7148 f70 | exact resolve f70 f7148 | grind (instances := 3000) only
  have f7186 : ((old sk2 sk2 sk1) ∨ ((c = sk1) ∨ ((c = sk2) ∨ (¬ spl0_2)))) := by
    clear * - f7185
    grind (instances := 3000) only
  have f7187 : ((old sk0 sk0 sk1) ∨ ((c = sk1) ∨ ((c = sk0) ∨ (¬ spl0_2)))) := by
    clear * - f7184
    grind (instances := 3000) only
  have f7192 : ((old sk2 sk2 sk1) ∨ ((c = sk2) ∨ ((¬ spl0_2) ∨ spl0_14))) := by
    clear * - f7186 f251
    first | exact resolve f7186 f251 | exact resolve f251 f7186 | grind (instances := 3000) only
  have f7216 : (False ∨ ((¬ spl0_20) ∨ (¬ spl0_61))) := by
    clear * - f6340 f524
    first | exact resolve f6340 f524 | exact resolve f524 f6340 | grind (instances := 3000) only
  have f7217 : ((¬ spl0_20) ∨ (¬ spl0_61)) := by
    clear * - f7216
    grind (instances := 3000) only
  have f7234 : ((¬ spl0_18) ∨ ((¬ spl0_13) ∨ spl0_17)) := by
    clear * - f6736 f263 f246 f484
    grind (instances := 3000) only
  have f7271 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ ((c = X0) ∨ (b = X2)))))) ∨ (¬ spl0_2))) := by
    clear * - f7173 f100
    first | exact resolve f7173 f100 | exact resolve f100 f7173 | grind (instances := 3000) only
  have f7272 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((a = X0) ∨ ((c = X0) ∨ (b = X2))))) ∨ (¬ spl0_2))) := by
    clear * - f7271 f122
    first | exact resolve f7271 f122 | exact resolve f122 f7271 | grind (instances := 3000) only
  have f7335 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP5 X0 X1 X2) ∨ ((c = X2) ∨ ((a = X1) ∨ (old (sF0 X0 X1 X2) X0 a))))))) ∨ (¬ spl0_2))) := by
    clear * - f7140 f98
    first | exact resolve f7140 f98 | exact resolve f98 f7140 | grind (instances := 3000) only
  have f7352 : ((old sk2 sk2 sk1) ∨ ((a = sk2) ∨ ((c = sk2) ∨ ((b = sk1) ∨ (¬ spl0_2))))) := by
    clear * - f7272 f70
    first | exact resolve f7272 f70 | exact resolve f70 f7272 | grind (instances := 3000) only
  have f7385 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((a = X0) ∨ ((a = X1) ∨ (b = X2))))))) ∨ (¬ spl0_2))) := by
    clear * - f7171 f100
    first | exact resolve f7171 f100 | exact resolve f100 f7171 | grind (instances := 3000) only
  have f7386 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((a = X0) ∨ ((a = X1) ∨ (b = X2)))))) ∨ (¬ spl0_2))) := by
    clear * - f7385 f122
    first | exact resolve f7385 f122 | exact resolve f122 f7385 | grind (instances := 3000) only
  have f7395 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((b = X1) ∨ ((a = X2) ∨ (old X2 X2 X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7151 f108
    first | exact resolve f7151 f108 | exact resolve f108 f7151 | grind (instances := 3000) only
  have f7429 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((a = X0) ∨ ((a = X1) ∨ ((b = X2) ∨ (old b X2 X1)))))) ∨ (¬ spl0_2))) := by
    clear * - f7386 f115
    first | exact resolve f7386 f115 | exact resolve f115 f7386 | grind (instances := 3000) only
  have f7538 : ((old sk0 sk0 sk1) ∨ ((a = sk0) ∨ ((a = sk0) ∨ ((b = sk1) ∨ ((old b sk1 sk0) ∨ (¬ spl0_2)))))) := by
    clear * - f7429 f69
    first | exact resolve f7429 f69 | exact resolve f69 f7429 | grind (instances := 3000) only
  have f7539 : ((old sk2 sk2 sk1) ∨ ((a = sk2) ∨ ((a = sk2) ∨ ((b = sk1) ∨ ((old b sk1 sk2) ∨ (¬ spl0_2)))))) := by
    clear * - f7429 f70
    first | exact resolve f7429 f70 | exact resolve f70 f7429 | grind (instances := 3000) only
  have f7540 : ((old sk2 sk2 sk1) ∨ ((a = sk2) ∨ ((b = sk1) ∨ ((old b sk1 sk2) ∨ (¬ spl0_2))))) := by
    clear * - f7539
    grind (instances := 3000) only
  have f7541 : ((old sk0 sk0 sk1) ∨ ((a = sk0) ∨ ((b = sk1) ∨ ((old b sk1 sk0) ∨ (¬ spl0_2))))) := by
    clear * - f7538
    grind (instances := 3000) only
  have f7596 : (∀ (X2 X0 X1 : G), (((sP5 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ ((a = X1) ∨ ((old (sF0 X0 X1 X2) X0 a) ∨ (old b X2 X1))))))) ∨ (¬ spl0_2))) := by
    clear * - f7335 f115
    first | exact resolve f7335 f115 | exact resolve f115 f7335 | grind (instances := 3000) only
  have f7762 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((b = X1) ∨ ((a = X2) ∨ ((old X2 X2 X2) ∨ (c = X1)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7395 f101
    first | exact resolve f7395 f101 | exact resolve f101 f7395 | grind (instances := 3000) only
  have f7765 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((b = X1) ∨ ((a = X2) ∨ ((old X2 X2 X2) ∨ (c = X1))))))) ∨ (¬ spl0_2))) := by
    clear * - f7762 f123
    first | exact resolve f7762 f123 | exact resolve f123 f7762 | grind (instances := 3000) only
  have f7880 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((b = X1) ∨ ((a = X2) ∨ ((old X2 X2 X2) ∨ ((c = X1) ∨ (old X2 X2 (sF2 X0 X1 X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7765 f113
    first | exact resolve f7765 f113 | exact resolve f113 f7765 | grind (instances := 3000) only
  have f8449 : (∀ (X2 X0 X1 : G), (((old (sF3 X0 X1 X2) a X0) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ ((a = X1) ∨ ((old (sF0 X0 X1 X2) X0 a) ∨ ((old b X2 X1) ∨ (¬ (new X0 X1 X2)))))))) ∨ (¬ spl0_2))) := by
    clear * - f7596 f121
    first | exact resolve f7596 f121 | exact resolve f121 f7596 | grind (instances := 3000) only
  have f8888 : ((old sk2 sk2 sk1) ∨ ((b = sk2) ∨ ((a = sk1) ∨ ((old sk1 sk1 sk1) ∨ ((c = sk2) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ (¬ spl0_2))))))) := by
    clear * - f7880 f70
    first | exact resolve f7880 f70 | exact resolve f70 f7880 | grind (instances := 3000) only
  have f9539 : (∀ (X0 X1 : G), (((old c X0 X1) ∨ ((c = X1) ∨ ((a = X0) ∨ ((old (sF0 c X0 X1) c a) ∨ ((old b X1 X0) ∨ (¬ (new c X0 X1))))))) ∨ (¬ spl0_2))) := by
    clear * - f8449 f134
    first | exact resolve f8449 f134 | exact resolve f134 f8449 | grind (instances := 3000) only
  have f9549 : (∀ (X0 X1 : G), (((c = X1) ∨ ((a = X0) ∨ ((old (sF0 c X0 X1) c a) ∨ ((old b X1 X0) ∨ (¬ (new c X0 X1)))))) ∨ (¬ spl0_2))) := by
    clear * - f9539 f132
    first | exact resolve f9539 f132 | exact resolve f132 f9539 | grind (instances := 3000) only
  have f9550 : (∀ (X0 X1 : G), (((¬ (new c X0 X1)) ∨ ((a = X0) ∨ ((old b X1 X0) ∨ (c = X1)))) ∨ (¬ spl0_2))) := by
    clear * - f9549 f133
    first | exact resolve f9549 f133 | exact resolve f133 f9549 | grind (instances := 3000) only
  have f9555 : ((a = c) ∨ ((old b b c) ∨ ((c = b) ∨ ((¬ spl0_2) ∨ (¬ spl0_10))))) := by
    clear * - f9550 f195
    first | exact resolve f9550 f195 | exact resolve f195 f9550 | grind (instances := 3000) only
  have f9559 : ((old b b c) ∨ ((c = b) ∨ ((¬ spl0_2) ∨ (¬ spl0_10)))) := by
    clear * - f9555 f136
    first | exact resolve f9555 f136 | exact resolve f136 f9555 | grind (instances := 3000) only
  have f9560 : ((c = b) ∨ ((¬ spl0_2) ∨ (¬ spl0_10))) := by
    clear * - f9559 f134
    first | exact resolve f9559 f134 | exact resolve f134 f9559 | grind (instances := 3000) only
  have f9561 : (False ∨ ((¬ spl0_2) ∨ (¬ spl0_10))) := by
    clear * - f9560 f135
    first | exact resolve f9560 f135 | exact resolve f135 f9560 | grind (instances := 3000) only
  have f9562 : ((¬ spl0_2) ∨ (¬ spl0_10)) := by
    clear * - f9561
    grind (instances := 3000) only
  have f9575 : ((old sk0 sk0 sk1) ∨ ((a = sk0) ∨ ((old b sk1 sk0) ∨ ((¬ spl0_2) ∨ spl0_13)))) := by
    clear * - f7541 f247
    first | exact resolve f7541 f247 | exact resolve f247 f7541 | grind (instances := 3000) only
  have f9645 : ((c = sk2) ∨ ((¬ spl0_2) ∨ (spl0_14 ∨ spl0_15))) := by
    clear * - f7192 f255
    first | exact resolve f7192 f255 | exact resolve f255 f7192 | grind (instances := 3000) only
  have f9648 : ((a = sk2) ∨ ((c = sk2) ∨ ((b = sk1) ∨ ((¬ spl0_2) ∨ spl0_15)))) := by
    clear * - f7352 f255
    first | exact resolve f7352 f255 | exact resolve f255 f7352 | grind (instances := 3000) only
  let spl0_70 : Prop := (a = sk2)
  have f9752 : (spl0_70 ↔ (a = sk2)) := Iff.rfl
  clear_value spl0_70
  have f9753 : ((a ≠ sk2) ∨ spl0_70) := by
    clear * - f9752
    grind (instances := 3000) only
  have f9754 : ((a = sk2) ∨ (¬ spl0_70)) := by
    clear * - f9752
    grind (instances := 3000) only
  have f9761 : (spl0_12 ∨ ((¬ spl0_2) ∨ (spl0_14 ∨ spl0_15))) := by
    clear * - f9645 f254 f250 f158 f242
    grind (instances := 3000) only
  have f9764 : ((a = sk2) ∨ ((c = sk2) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ spl0_15)))) := by
    clear * - f9648 f247
    first | exact resolve f9648 f247 | exact resolve f247 f9648 | grind (instances := 3000) only
  have f9862 : (spl0_12 ∨ (spl0_70 ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ spl0_15)))) := by
    clear * - f9764 f254 f246 f158 f9752 f242
    grind (instances := 3000) only
  have f9911 : ((a = b) ∨ ((¬ spl0_61) ∨ (¬ spl0_70))) := by
    clear * - f9754 f6288
    grind (instances := 3000) only
  have f9961 : (False ∨ (spl0_1 ∨ ((¬ spl0_61) ∨ (¬ spl0_70)))) := by
    clear * - f9911 f155
    first | exact resolve f9911 f155 | exact resolve f155 f9911 | grind (instances := 3000) only
  have f9962 : (spl0_1 ∨ ((¬ spl0_61) ∨ (¬ spl0_70))) := by
    clear * - f9961
    grind (instances := 3000) only
  have f10178 : ((old sk2 sk2 c) ∨ ((¬ spl0_14) ∨ (¬ spl0_15))) := by
    clear * - f256 f252
    grind (instances := 3000) only
  have f10199 : ((old sk2 sk2 sk1) ∨ ((a = sk1) ∨ ((old sk1 sk1 sk1) ∨ ((c = sk2) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ spl0_61)))))) := by
    clear * - f8888 f6287
    first | exact resolve f8888 f6287 | exact resolve f6287 f8888 | grind (instances := 3000) only
  have f10200 : (False ∨ ((¬ spl0_14) ∨ (¬ spl0_15))) := by
    clear * - f10178 f134
    first | exact resolve f10178 f134 | exact resolve f134 f10178 | grind (instances := 3000) only
  have f10201 : ((¬ spl0_14) ∨ (¬ spl0_15)) := by
    clear * - f10200
    grind (instances := 3000) only
  have f10219 : ((old sk2 sk2 sk1) ∨ ((a = sk1) ∨ ((old sk1 sk1 sk1) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ spl0_61)))))) := by
    clear * - f10199 f243
    first | exact resolve f10199 f243 | exact resolve f243 f10199 | grind (instances := 3000) only
  have f10237 : ((old sk2 sk2 c) ∨ ((a = sk1) ∨ ((old sk1 sk1 sk1) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61))))))) := by
    clear * - f10219 f252
    grind (instances := 3000) only
  have f10256 : ((a = sk1) ∨ ((old sk1 sk1 sk1) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61)))))) := by
    clear * - f10237 f134
    first | exact resolve f10237 f134 | exact resolve f134 f10237 | grind (instances := 3000) only
  have f10274 : ((a = c) ∨ ((old sk1 sk1 sk1) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61)))))) := by
    clear * - f10256 f252
    grind (instances := 3000) only
  have f10290 : ((old sk1 sk1 sk1) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61))))) := by
    clear * - f10274 f136
    first | exact resolve f10274 f136 | exact resolve f136 f10274 | grind (instances := 3000) only
  have f10306 : ((old c c c) ∨ ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61))))) := by
    clear * - f10290 f252
    grind (instances := 3000) only
  have f10322 : ((old sk1 sk1 (sF2 sk2 sk2 sk1)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61)))) := by
    clear * - f10306 f134
    first | exact resolve f10306 f134 | exact resolve f134 f10306 | grind (instances := 3000) only
  have f10338 : ((old c c (sF2 sk2 sk2 c)) ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61)))) := by
    clear * - f10322 f252
    grind (instances := 3000) only
  have f10353 : (False ∨ ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61)))) := by
    clear * - f10338 f133
    first | exact resolve f10338 f133 | exact resolve f133 f10338 | grind (instances := 3000) only
  have f10354 : ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61))) := by
    clear * - f10353
    grind (instances := 3000) only
  have f10392 : ((old sk0 sk0 sk1) ∨ ((c = sk0) ∨ ((¬ spl0_2) ∨ spl0_14))) := by
    clear * - f7187 f251
    first | exact resolve f7187 f251 | exact resolve f251 f7187 | grind (instances := 3000) only
  have f10460 : ((old sk0 sk0 sk1) ∨ ((¬ spl0_2) ∨ (spl0_14 ∨ spl0_16))) := by
    clear * - f10392 f260
    first | exact resolve f10392 f260 | exact resolve f260 f10392 | grind (instances := 3000) only
  have f10589 : ((a = sk0) ∨ ((old b sk1 sk0) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ spl0_17)))) := by
    clear * - f9575 f264
    first | exact resolve f9575 f264 | exact resolve f264 f9575 | grind (instances := 3000) only
  have f10601 : (False ∨ ((¬ spl0_2) ∨ (spl0_14 ∨ (spl0_16 ∨ spl0_17)))) := by
    clear * - f10460 f264
    first | exact resolve f10460 f264 | exact resolve f264 f10460 | grind (instances := 3000) only
  have f10602 : ((¬ spl0_2) ∨ (spl0_14 ∨ (spl0_16 ∨ spl0_17))) := by
    clear * - f10601
    grind (instances := 3000) only
  have f10772 : ((a = c) ∨ ((old b sk1 sk0) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ ((¬ spl0_16) ∨ spl0_17))))) := by
    clear * - f10589 f261
    grind (instances := 3000) only
  have f10801 : ((old b sk1 sk0) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ ((¬ spl0_16) ∨ spl0_17)))) := by
    clear * - f10772 f136
    first | exact resolve f10772 f136 | exact resolve f136 f10772 | grind (instances := 3000) only
  have f10830 : ((old b sk1 c) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ ((¬ spl0_16) ∨ spl0_17)))) := by
    clear * - f10801 f261
    grind (instances := 3000) only
  have f10851 : (False ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ ((¬ spl0_16) ∨ spl0_17)))) := by
    clear * - f10830 f134
    first | exact resolve f10830 f134 | exact resolve f134 f10830 | grind (instances := 3000) only
  have f10852 : ((¬ spl0_2) ∨ (spl0_13 ∨ ((¬ spl0_16) ∨ spl0_17))) := by
    clear * - f10851
    grind (instances := 3000) only
  have f10894 : ((a = c) ∨ ((¬ spl0_12) ∨ (¬ spl0_70))) := by
    clear * - f244 f9754
    grind (instances := 3000) only
  have f10913 : (False ∨ ((¬ spl0_12) ∨ (¬ spl0_70))) := by
    clear * - f10894 f136
    first | exact resolve f10894 f136 | exact resolve f136 f10894 | grind (instances := 3000) only
  have f10914 : ((¬ spl0_12) ∨ (¬ spl0_70)) := by
    clear * - f10913
    grind (instances := 3000) only
  have f10944 : ((old sk2 sk2 sk1) ∨ ((b = sk1) ∨ ((old b sk1 sk2) ∨ ((¬ spl0_2) ∨ spl0_70)))) := by
    clear * - f7540 f9753
    first | exact resolve f7540 f9753 | exact resolve f9753 f7540 | grind (instances := 3000) only
  have f10975 : ((old sk2 sk2 sk1) ∨ ((old b sk1 sk2) ∨ ((¬ spl0_2) ∨ (spl0_13 ∨ spl0_70)))) := by
    clear * - f10944 f247
    first | exact resolve f10944 f247 | exact resolve f247 f10944 | grind (instances := 3000) only
  have f11098 : ((old c c sk1) ∨ ((old b sk1 sk2) ∨ ((¬ spl0_2) ∨ ((¬ spl0_12) ∨ (spl0_13 ∨ spl0_70))))) := by
    clear * - f10975 f244
    grind (instances := 3000) only
  have f11131 : ((old b sk1 sk2) ∨ ((¬ spl0_2) ∨ ((¬ spl0_12) ∨ (spl0_13 ∨ spl0_70)))) := by
    clear * - f11098 f133
    first | exact resolve f11098 f133 | exact resolve f133 f11098 | grind (instances := 3000) only
  have f11160 : ((old b sk1 c) ∨ ((¬ spl0_2) ∨ ((¬ spl0_12) ∨ (spl0_13 ∨ spl0_70)))) := by
    clear * - f11131 f244
    grind (instances := 3000) only
  have f11189 : (False ∨ ((¬ spl0_2) ∨ ((¬ spl0_12) ∨ (spl0_13 ∨ spl0_70)))) := by
    clear * - f11160 f134
    first | exact resolve f11160 f134 | exact resolve f134 f11160 | grind (instances := 3000) only
  have f11190 : ((¬ spl0_2) ∨ ((¬ spl0_12) ∨ (spl0_13 ∨ spl0_70))) := by
    clear * - f11189
    grind (instances := 3000) only
  have f11268 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (c = X2)))))))) ∨ (¬ spl0_6))) := by
    clear * - f202 f175
    first | exact resolve f202 f175 | exact resolve f175 f202 | grind (instances := 3000) only
  have f11269 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP1 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (b = X1)))))))) ∨ (¬ spl0_6))) := by
    clear * - f201 f175
    first | exact resolve f201 f175 | exact resolve f175 f201 | grind (instances := 3000) only
  have f11275 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (c = X2))))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11268 f167
    first | exact resolve f11268 f167 | exact resolve f167 f11268 | grind (instances := 3000) only
  have f11276 : (∀ (X2 X0 X1 : G), (((sP1 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (b = X1))))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11269 f167
    first | exact resolve f11269 f167 | exact resolve f167 f11269 | grind (instances := 3000) only
  have f11284 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_1))) := by
    clear * - f131 f156
    first | exact superpose f131 f156 | exact superpose f156 f131 | grind (instances := 3000) only
  have f11343 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (old b b (sF0 X0 X1 X2)))))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11275 f99
    first | exact resolve f11275 f99 | exact resolve f99 f11275 | grind (instances := 3000) only
  have f11345 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (c = X1))))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11275 f101
    first | exact resolve f11275 f101 | exact resolve f101 f11275 | grind (instances := 3000) only
  have f11348 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (c = X1)))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11345 f123
    first | exact resolve f11345 f123 | exact resolve f123 f11345 | grind (instances := 3000) only
  have f11350 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ (c = X2)))))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11343 f11284
    first | exact resolve f11343 f11284 | exact resolve f11284 f11343 | grind (instances := 3000) only
  have f11352 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((c = X2) ∨ (c = X1))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11348 f128
    first | exact resolve f11348 f128 | exact resolve f128 f11348 | grind (instances := 3000) only
  have f11356 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((b = X1) ∨ (b = X2))))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11276 f100
    first | exact resolve f11276 f100 | exact resolve f100 f11276 | grind (instances := 3000) only
  have f11357 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((b = X1) ∨ (b = X2)))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11356 f122
    first | exact resolve f11356 f122 | exact resolve f122 f11356 | grind (instances := 3000) only
  have f11361 : (∀ (X2 X0 X1 : G), (((sP4 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((b = X1) ∨ (b = X2))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11357 f127
    first | exact resolve f11357 f127 | exact resolve f127 f11357 | grind (instances := 3000) only
  have f11404 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((c = X2) ∨ ((c = X1) ∨ (old b b (sF1 X0 X1 X2)))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11352 f116
    first | exact resolve f11352 f116 | exact resolve f116 f11352 | grind (instances := 3000) only
  have f11408 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ (c = X1)))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11404 f11284
    first | exact resolve f11404 f11284 | exact resolve f11284 f11404 | grind (instances := 3000) only
  have f11411 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((b = X1) ∨ ((b = X2) ∨ (old b b (sF1 X0 X1 X2)))))) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))) := by
    clear * - f11361 f116
    first | exact resolve f11361 f116 | exact resolve f116 f11361 | grind (instances := 3000) only
  have f11415 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((b = X1) ∨ (b = X2)))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11411 f11284
    first | exact resolve f11411 f11284 | exact resolve f11284 f11411 | grind (instances := 3000) only
  have f11446 : ((old sk2 sk2 sk1) ∨ ((c = sk1) ∨ ((c = sk2) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f11408 f70
    first | exact resolve f11408 f70 | exact resolve f70 f11408 | grind (instances := 3000) only
  have f11475 : ((old sk0 sk0 sk1) ∨ ((b = sk0) ∨ ((b = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f11415 f69
    first | exact resolve f11415 f69 | exact resolve f69 f11415 | grind (instances := 3000) only
  have f11476 : ((old sk2 sk2 sk1) ∨ ((b = sk2) ∨ ((b = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6)))))) := by
    clear * - f11415 f70
    first | exact resolve f11415 f70 | exact resolve f70 f11415 | grind (instances := 3000) only
  have f11478 : ((old sk2 sk2 sk1) ∨ ((b = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ spl0_61))))) := by
    clear * - f11476 f6287
    first | exact resolve f11476 f6287 | exact resolve f6287 f11476 | grind (instances := 3000) only
  have f11480 : ((old sk2 sk2 sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ spl0_61))))) := by
    clear * - f11478 f247
    first | exact resolve f11478 f247 | exact resolve f247 f11478 | grind (instances := 3000) only
  have f11483 : ((old sk2 sk2 c) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_61)))))) := by
    clear * - f11480 f252
    grind (instances := 3000) only
  have f11484 : (False ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_61)))))) := by
    clear * - f11483 f134
    first | exact resolve f11483 f134 | exact resolve f134 f11483 | grind (instances := 3000) only
  have f11485 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_61))))) := by
    clear * - f11484
    grind (instances := 3000) only
  have f11489 : ((old sk0 sk0 sk1) ∨ ((b = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ spl0_20))))) := by
    clear * - f11475 f523
    first | exact resolve f11475 f523 | exact resolve f523 f11475 | grind (instances := 3000) only
  have f11497 : ((old sk0 sk0 sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ spl0_20))))) := by
    clear * - f11489 f247
    first | exact resolve f11489 f247 | exact resolve f247 f11489 | grind (instances := 3000) only
  have f11502 : ((old sk0 sk0 c) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_20)))))) := by
    clear * - f11497 f252
    grind (instances := 3000) only
  have f11503 : (False ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_20)))))) := by
    clear * - f11502 f134
    first | exact resolve f11502 f134 | exact resolve f134 f11502 | grind (instances := 3000) only
  have f11504 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_20))))) := by
    clear * - f11503
    grind (instances := 3000) only
  have f11509 : (∀ (X2 X0 X1 : G), (((old X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP5 X0 X1 X2) ∨ ((sP6 X0 X1 X2) ∨ ((c = X2) ∨ (old b b (sF1 X0 X1 X2))))))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11350 f116
    first | exact resolve f11350 f116 | exact resolve f116 f11350 | grind (instances := 3000) only
  have f11514 : (∀ (X2 X0 X1 : G), (((sP6 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((sP5 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ (c = X2))))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11509 f11284
    first | exact resolve f11509 f11284 | exact resolve f11284 f11509 | grind (instances := 3000) only
  have f11524 : ((c = b) ∨ ((¬ spl0_13) ∨ (¬ spl0_14))) := by
    clear * - f248 f252
    first | exact superpose f248 f252 | exact superpose f252 f248 | grind (instances := 3000) only
  have f11535 : (False ∨ ((¬ spl0_13) ∨ (¬ spl0_14))) := by
    clear * - f11524 f135
    first | exact resolve f11524 f135 | exact resolve f135 f11524 | grind (instances := 3000) only
  have f11536 : ((¬ spl0_13) ∨ (¬ spl0_14)) := by
    clear * - f11535
    grind (instances := 3000) only
  have f11547 : ((old sk2 sk2 sk1) ∨ ((c = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ spl0_12))))) := by
    clear * - f11446 f243
    first | exact resolve f11446 f243 | exact resolve f243 f11446 | grind (instances := 3000) only
  have f11555 : ((old sk2 sk2 b) ∨ ((c = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_12 ∨ (¬ spl0_13))))))) := by
    clear * - f11547 f248
    grind (instances := 3000) only
  have f11560 : ((c = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_12 ∨ ((¬ spl0_13) ∨ spl0_19)))))) := by
    clear * - f11555 f490
    first | exact resolve f11555 f490 | exact resolve f490 f11555 | grind (instances := 3000) only
  have f11563 : ((c = b) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_12 ∨ ((¬ spl0_13) ∨ spl0_19)))))) := by
    clear * - f11560 f248
    grind (instances := 3000) only
  have f11565 : (False ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_12 ∨ ((¬ spl0_13) ∨ spl0_19)))))) := by
    clear * - f11563 f135
    first | exact resolve f11563 f135 | exact resolve f135 f11563 | grind (instances := 3000) only
  have f11566 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_12 ∨ ((¬ spl0_13) ∨ spl0_19))))) := by
    clear * - f11565
    grind (instances := 3000) only
  have f11932 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((sP5 X0 X1 X2) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ (old b b (sF7 X0 X1 X2)))))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11514 f124
    first | exact resolve f11514 f124 | exact resolve f124 f11514 | grind (instances := 3000) only
  have f11940 : (∀ (X2 X0 X1 : G), (((sP5 X0 X1 X2) ∨ ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ (c = X2)))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11932 f11284
    first | exact resolve f11932 f11284 | exact resolve f11284 f11932 | grind (instances := 3000) only
  have f11945 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((c = X2) ∨ (old b b (sF5 X0 X1 X2))))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11940 f118
    first | exact resolve f11940 f118 | exact resolve f118 f11940 | grind (instances := 3000) only
  have f11948 : (∀ (X2 X0 X1 : G), (((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ (c = X2))) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11945 f11284
    first | exact resolve f11945 f11284 | exact resolve f11284 f11945 | grind (instances := 3000) only
  have f11968 : ((old c c b) ∨ ((c = b) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (¬ spl0_10)))))) := by
    clear * - f11948 f195
    first | exact resolve f11948 f195 | exact resolve f195 f11948 | grind (instances := 3000) only
  have f11971 : ((old sk0 sk0 sk1) ∨ ((c = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ (¬ spl0_6))))) := by
    clear * - f11948 f69
    first | exact resolve f11948 f69 | exact resolve f69 f11948 | grind (instances := 3000) only
  have f11974 : ((old sk0 sk0 b) ∨ ((c = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (¬ spl0_13)))))) := by
    clear * - f11971 f248
    grind (instances := 3000) only
  have f11976 : ((c = b) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (¬ spl0_10))))) := by
    clear * - f11968 f133
    first | exact resolve f11968 f133 | exact resolve f133 f11968 | grind (instances := 3000) only
  have f11978 : ((c = sk1) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ ((¬ spl0_13) ∨ spl0_18))))) := by
    clear * - f11974 f485
    first | exact resolve f11974 f485 | exact resolve f485 f11974 | grind (instances := 3000) only
  have f11981 : (False ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (¬ spl0_10))))) := by
    clear * - f11976 f135
    first | exact resolve f11976 f135 | exact resolve f135 f11976 | grind (instances := 3000) only
  have f11982 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (¬ spl0_10)))) := by
    clear * - f11981
    grind (instances := 3000) only
  have f11984 : ((c = b) ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ ((¬ spl0_13) ∨ spl0_18))))) := by
    clear * - f11978 f248
    grind (instances := 3000) only
  have f11985 : (False ∨ ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ ((¬ spl0_13) ∨ spl0_18))))) := by
    clear * - f11984 f135
    first | exact resolve f11984 f135 | exact resolve f135 f11984 | grind (instances := 3000) only
  have f11986 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ ((¬ spl0_13) ∨ spl0_18)))) := by
    clear * - f11985
    grind (instances := 3000) only
  have s1 : (spl0_1 ∨ spl0_2) := by
    clear * - f160
    grind (splits := 100) only
  have s2 : (spl0_3 ∨ spl0_4) := by
    clear * - f168
    grind (splits := 100) only
  have s5 : (spl0_3 ∨ spl0_6) := by
    clear * - f182
    grind (splits := 100) only
  have s13 : ((¬ spl0_1) ∨ (¬ spl0_3)) := by
    clear * - f333
    grind (splits := 100) only
  have s14 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ (spl0_14 ∨ spl0_15))))) := by
    clear * - f379
    grind (splits := 100) only
  have s15 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ (spl0_14 ∨ spl0_17))))) := by
    clear * - f380
    grind (splits := 100) only
  have s33 : (spl0_10 ∨ ((¬ spl0_12) ∨ (¬ spl0_13))) := by
    clear * - f2780
    grind (splits := 100) only
  have s36 : (spl0_10 ∨ ((¬ spl0_13) ∨ (¬ spl0_16))) := by
    clear * - f2910
    grind (splits := 100) only
  have s38 : ((¬ spl0_15) ∨ (¬ spl0_17)) := by
    clear * - f2951
    grind (splits := 100) only
  have s267 : ((¬ spl0_13) ∨ (spl0_15 ∨ (¬ spl0_19))) := by
    clear * - f6864
    grind (splits := 100) only
  have s282 : ((¬ spl0_20) ∨ (¬ spl0_61)) := by
    clear * - f7217
    grind (splits := 100) only
  have s288 : ((¬ spl0_13) ∨ (spl0_17 ∨ (¬ spl0_18))) := by
    clear * - f7234
    grind (splits := 100) only
  have s299 : ((¬ spl0_2) ∨ (¬ spl0_10)) := by
    clear * - f9562
    grind (splits := 100) only
  have s303 : ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_14 ∨ spl0_15))) := by
    clear * - f9761
    grind (splits := 100) only
  have s328 : ((¬ spl0_2) ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_15 ∨ spl0_70)))) := by
    clear * - f9862
    grind (splits := 100) only
  have s375 : (spl0_1 ∨ ((¬ spl0_61) ∨ (¬ spl0_70))) := by
    clear * - f9962
    grind (splits := 100) only
  have s395 : ((¬ spl0_14) ∨ (¬ spl0_15)) := by
    clear * - f10201
    grind (splits := 100) only
  have s405 : ((¬ spl0_2) ∨ (spl0_12 ∨ ((¬ spl0_14) ∨ spl0_61))) := by
    clear * - f10354
    grind (splits := 100) only
  have s415 : ((¬ spl0_2) ∨ (spl0_14 ∨ (spl0_16 ∨ spl0_17))) := by
    clear * - f10602
    grind (splits := 100) only
  have s463 : ((¬ spl0_2) ∨ (spl0_13 ∨ ((¬ spl0_16) ∨ spl0_17))) := by
    clear * - f10852
    grind (splits := 100) only
  have s490 : ((¬ spl0_12) ∨ (¬ spl0_70)) := by
    clear * - f10914
    grind (splits := 100) only
  have s505 : ((¬ spl0_2) ∨ ((¬ spl0_12) ∨ (spl0_13 ∨ spl0_70))) := by
    clear * - f11190
    grind (splits := 100) only
  have s546 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_61))))) := by
    clear * - f11485
    grind (splits := 100) only
  have s551 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_13 ∨ ((¬ spl0_14) ∨ spl0_20))))) := by
    clear * - f11504
    grind (splits := 100) only
  have s557 : ((¬ spl0_13) ∨ (¬ spl0_14)) := by
    clear * - f11536
    grind (splits := 100) only
  have s558 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (spl0_12 ∨ ((¬ spl0_13) ∨ spl0_19))))) := by
    clear * - f11566
    grind (splits := 100) only
  have s563 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ (¬ spl0_10)))) := by
    clear * - f11982
    grind (splits := 100) only
  have s564 : ((¬ spl0_1) ∨ ((¬ spl0_4) ∨ ((¬ spl0_6) ∨ ((¬ spl0_13) ∨ spl0_18)))) := by
    clear * - f11986
    grind (splits := 100) only
  have s567 : (spl0_14 ∨ (spl0_13 ∨ (spl0_12 ∨ (¬ spl0_2)))) := by
    clear * - s463 s415 s38 s303
    grind (splits := 100) only
  have s568 : (spl0_13 ∨ (spl0_12 ∨ spl0_1)) := by
    clear * - s375 s328 s405 s395 s567 s1
    grind (splits := 100) only
  have s569 : (spl0_12 ∨ spl0_1) := by
    clear * - s38 s415 s303 s36 s557 s568 s299 s1
    grind (splits := 100) only
  have s570 : spl0_1 := by
    clear * - s505 s33 s490 s569 s299 s1
    grind (splits := 100) only
  have s571 : (¬ spl0_3) := by
    clear * - s13 s570
    grind (splits := 100) only
  have s574 : spl0_6 := by
    clear * - s5 s571
    grind (splits := 100) only
  have s575 : spl0_4 := by
    clear * - s2 s571
    grind (splits := 100) only
  have s576 : (¬ spl0_10) := by
    clear * - s563 s574 s570 s575
    grind (splits := 100) only
  have s581 : (spl0_14 ∨ spl0_13) := by
    clear * - s38 s15 s14 s574 s575 s570
    grind (splits := 100) only
  have s582 : ((¬ spl0_14) ∨ spl0_13) := by
    clear * - s282 s546 s551 s575 s574 s570
    grind (splits := 100) only
  have s583 : spl0_13 := by
    clear * - s582 s581
    grind (splits := 100) only
  have s587 : spl0_18 := by
    clear * - s564 s575 s574 s570 s583
    grind (splits := 100) only
  have s589 : spl0_17 := by
    clear * - s288 s583 s587
    grind (splits := 100) only
  have s592 : (¬ spl0_15) := by
    clear * - s38 s589
    grind (splits := 100) only
  have s593 : (¬ spl0_12) := by
    clear * - s33 s576 s583
    grind (splits := 100) only
  have s595 : (¬ spl0_19) := by
    clear * - s267 s583 s592
    grind (splits := 100) only
  have s596 : False := by
    clear * - s558 s583 s575 s574 s570 s593 s595
    grind (splits := 100) only
  exact s596


set_option maxHeartbeats 8000000 in
theorem rule_12_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X1 ∨ X0 = X2)) (old_12 : (∀ X0 X1 X2 X3 X4 X5 X6 X7, ¬ old X0 X0 X1 ∨ ¬ old X2 X0 X3 ∨ ¬ old X2 X2 X4 ∨ ¬ old X2 X5 X3 ∨ ¬ old X4 X1 X6 ∨ ¬ old X4 X7 X6 ∨ ¬ old X5 X5 X7 ∨ X0 = X5)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old Z Z (sF2 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a (sF4 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_6_4 : ∀ (X Y Z : G), old a a (sF6 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) : (∀ X0 X1 X2 X3 X4 X5 X6 X7, ¬ new X0 X0 X1 ∨ ¬ new X2 X0 X3 ∨ ¬ new X2 X2 X4 ∨ ¬ new X2 X5 X3 ∨ ¬ new X4 X1 X6 ∨ ¬ new X4 X7 X6 ∨ ¬ new X5 X5 X7 ∨ X0 = X5) := by
  classical
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4, preserve_5, preserve_6, preserve_7⟩ := nh
  have f1 : (a ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using ac
  have f2 : (b ≠ c) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using bc
  have f3 : (∀ (X0 : G), (¬ (old a b X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p3
  have f4 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XY
  have f5 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4XZ
  have f6 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using p4YZ
  have f8 : (∀ (X0 X1 X2 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X2 X2 X1)) ∨ (X0 = X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_2
  have f19 : (∀ (X0 X1 X2 X3 X4 X5 X6 X7 : G), ((¬ (old X0 X0 X1)) ∨ ((¬ (old X2 X0 X3)) ∨ ((¬ (old X2 X2 X4)) ∨ ((¬ (old X2 X5 X3)) ∨ ((¬ (old X4 X1 X6)) ∨ ((¬ (old X4 X7 X6)) ∨ ((¬ (old X5 X5 X7)) ∨ (X0 = X5))))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using old_12
  have f22 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_0
  have f23 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_1
  have f24 : (∀ (X0 X1 X2 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_0_2
  have f26 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_0
  have f27 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_1
  have f28 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old b b (sF0 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_2
  have f29 : (∀ (X0 X1 X2 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_1_3
  have f31 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_0
  have f32 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_1
  have f33 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_2
  have f34 : (∀ (X0 X1 X2 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old a a a))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_2_3
  have f38 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_0
  have f39 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_1
  have f40 : (∀ (X0 X1 X2 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_3_2
  have f44 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_0
  have f45 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_1
  have f46 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_2
  have f48 : (∀ (X0 X1 X2 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old X2 X2 (sF2 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_4_4
  have f50 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_0
  have f51 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_1
  have f52 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_2
  have f53 : (∀ (X0 X1 X2 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old a a (sF4 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_5_3
  have f57 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_0
  have f58 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X0))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_1
  have f59 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X1))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_2
  have f60 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (b = X2))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_3
  have f61 : (∀ (X0 X1 X2 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old a a (sF6 X0 X1 X2)))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using rule_def_6_4
  have f65 : (∀ (X0 X1 X2 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using new_imp
  have f66 : (new sk0 sk0 sk1) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_0
  have f67 : (new sk2 sk0 sk3) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_1
  have f68 : (new sk2 sk2 sk4) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_2
  have f69 : (new sk2 sk5 sk3) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_3
  have f70 : (new sk4 sk1 sk6) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_4
  have f71 : (new sk4 sk7 sk6) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_5
  have f72 : (new sk5 sk5 sk7) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_6
  have f73 : (sk0 ≠ sk5) := by simpa only [or_comm, or_left_comm, or_assoc, eq_comm, ne_comm, not_not] using preserve_7
  have f74 : (a ≠ c) := by
    clear * - f1
    grind (instances := 3000) only
  have f75 : (c ≠ b) := by
    clear * - f2
    grind (instances := 3000) only
  have f76 : (∀ (X0 : G), (¬ (old a b X0))) := by
    clear * - f3
    grind (instances := 3000) only
  have f77 : (∀ (X0 X1 : G), (¬ (old X0 X1 c))) := by
    clear * - f4
    grind (instances := 3000) only
  have f78 : (∀ (X0 X1 : G), (¬ (old X0 c X1))) := by
    clear * - f5
    grind (instances := 3000) only
  have f79 : (∀ (X0 X1 : G), (¬ (old c X0 X1))) := by
    clear * - f6
    grind (instances := 3000) only
  have f81 : (∀ (X2 X0 X1 : G), ((¬ (old X2 X2 X1)) ∨ ((¬ (old X0 X0 X1)) ∨ (X0 = X2)))) := by
    clear * - f8
    grind (instances := 3000) only
  have f92 : (∀ (X2 X3 X0 X1 X6 X7 X4 X5 : G), ((¬ (old X5 X5 X7)) ∨ ((¬ (old X2 X0 X3)) ∨ ((¬ (old X2 X2 X4)) ∨ ((¬ (old X2 X5 X3)) ∨ ((¬ (old X4 X1 X6)) ∨ ((¬ (old X4 X7 X6)) ∨ ((¬ (old X0 X0 X1)) ∨ (X0 = X5))))))))) := by
    clear * - f19
    grind (instances := 3000) only
  have f95 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (a = X0))) := by
    clear * - f22
    grind (instances := 3000) only
  have f96 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (b = X1))) := by
    clear * - f23
    grind (instances := 3000) only
  have f97 : (∀ (X2 X0 X1 : G), ((¬ (sP0 X0 X1 X2)) ∨ (c = X2))) := by
    clear * - f24
    grind (instances := 3000) only
  have f99 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f26
    grind (instances := 3000) only
  have f100 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f27
    grind (instances := 3000) only
  have f101 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old b b (sF0 X0 X1 X2)))) := by
    clear * - f28
    grind (instances := 3000) only
  have f102 : (∀ (X2 X0 X1 : G), ((¬ (sP1 X0 X1 X2)) ∨ (old (sF0 X0 X1 X2) X0 a))) := by
    clear * - f29
    grind (instances := 3000) only
  have f104 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f31
    grind (instances := 3000) only
  have f105 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f32
    grind (instances := 3000) only
  have f106 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (a = X2))) := by
    clear * - f33
    grind (instances := 3000) only
  have f107 : (∀ (X2 X0 X1 : G), ((¬ (sP2 X0 X1 X2)) ∨ (old a a a))) := by
    clear * - f34
    grind (instances := 3000) only
  have f111 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f38
    grind (instances := 3000) only
  have f112 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (a = X1))) := by
    clear * - f39
    grind (instances := 3000) only
  have f113 : (∀ (X2 X0 X1 : G), ((¬ (sP3 X0 X1 X2)) ∨ (old b b b))) := by
    clear * - f40
    grind (instances := 3000) only
  have f117 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f44
    grind (instances := 3000) only
  have f118 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b b (sF1 X0 X1 X2)))) := by
    clear * - f45
    grind (instances := 3000) only
  have f119 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old b X2 X1))) := by
    clear * - f46
    grind (instances := 3000) only
  have f121 : (∀ (X2 X0 X1 : G), ((¬ (sP4 X0 X1 X2)) ∨ (old X2 X2 (sF2 X0 X1 X2)))) := by
    clear * - f48
    grind (instances := 3000) only
  have f123 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f50
    grind (instances := 3000) only
  have f124 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f51
    grind (instances := 3000) only
  have f125 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old (sF3 X0 X1 X2) a X0))) := by
    clear * - f52
    grind (instances := 3000) only
  have f126 : (∀ (X2 X0 X1 : G), ((¬ (sP5 X0 X1 X2)) ∨ (old a a (sF4 X0 X1 X2)))) := by
    clear * - f53
    grind (instances := 3000) only
  have f130 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (a = b))) := by
    clear * - f57
    grind (instances := 3000) only
  have f131 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X0))) := by
    clear * - f58
    grind (instances := 3000) only
  have f132 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (c = X1))) := by
    clear * - f59
    grind (instances := 3000) only
  have f133 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (b = X2))) := by
    clear * - f60
    grind (instances := 3000) only
  have f134 : (∀ (X2 X0 X1 : G), ((¬ (sP6 X0 X1 X2)) ∨ (old a a (sF6 X0 X1 X2)))) := by
    clear * - f61
    grind (instances := 3000) only
  have f138 : (∀ (X2 X0 X1 : G), ((¬ (new X0 X1 X2)) ∨ ((old X0 X1 X2) ∨ ((sP0 X0 X1 X2) ∨ ((sP1 X0 X1 X2) ∨ ((sP2 X0 X1 X2) ∨ ((sP3 X0 X1 X2) ∨ ((sP4 X0 X1 X2) ∨ ((sP5 X0 X1 X2) ∨ (sP6 X0 X1 X2)))))))))) := by
    clear * - f65
    grind (instances := 3000) only
  have f139 : (new sk0 sk0 sk1) := by
    clear * - f66
    grind (instances := 3000) only
  have f140 : (new sk2 sk0 sk3) := by
    clear * - f67
    grind (instances := 3000) only
  have f141 : (new sk2 sk2 sk4) := by
    clear * - f68
    grind (instances := 3000) only
  have f142 : (new sk2 sk5 sk3) := by
    clear * - f69
    grind (instances := 3000) only
  have f143 : (new sk4 sk1 sk6) := by
    clear * - f70
    grind (instances := 3000) only
  have f144 : (new sk4 sk7 sk6) := by
    clear * - f71
    grind (instances := 3000) only
  have f145 : (new sk5 sk5 sk7) := by
    clear * - f72
    grind (instances := 3000) only
  have f146 : (sk0 ≠ sk5) := by
    clear * - f73
    grind (instances := 3000) only
  have f163 : ((old sk0 sk0 sk1) ∨ ((sP0 sk0 sk0 sk1) ∨ ((sP1 sk0 sk0 sk1) ∨ ((sP2 sk0 sk0 sk1) ∨ ((sP3 sk0 sk0 sk1) ∨ ((sP4 sk0 sk0 sk1) ∨ ((sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1)))))))) := by
    clear * - f139 f138
    first | exact resolve f139 f138 | exact resolve f138 f139 | grind (instances := 3000) only
  have f164 : ((old sk2 sk0 sk3) ∨ ((sP0 sk2 sk0 sk3) ∨ ((sP1 sk2 sk0 sk3) ∨ ((sP2 sk2 sk0 sk3) ∨ ((sP3 sk2 sk0 sk3) ∨ ((sP4 sk2 sk0 sk3) ∨ ((sP5 sk2 sk0 sk3) ∨ (sP6 sk2 sk0 sk3)))))))) := by
    clear * - f140 f138
    first | exact resolve f140 f138 | exact resolve f138 f140 | grind (instances := 3000) only
  have f165 : ((old sk2 sk2 sk4) ∨ ((sP0 sk2 sk2 sk4) ∨ ((sP1 sk2 sk2 sk4) ∨ ((sP2 sk2 sk2 sk4) ∨ ((sP3 sk2 sk2 sk4) ∨ ((sP4 sk2 sk2 sk4) ∨ ((sP5 sk2 sk2 sk4) ∨ (sP6 sk2 sk2 sk4)))))))) := by
    clear * - f141 f138
    first | exact resolve f141 f138 | exact resolve f138 f141 | grind (instances := 3000) only
  have f166 : ((old sk2 sk5 sk3) ∨ ((sP0 sk2 sk5 sk3) ∨ ((sP1 sk2 sk5 sk3) ∨ ((sP2 sk2 sk5 sk3) ∨ ((sP3 sk2 sk5 sk3) ∨ ((sP4 sk2 sk5 sk3) ∨ ((sP5 sk2 sk5 sk3) ∨ (sP6 sk2 sk5 sk3)))))))) := by
    clear * - f142 f138
    first | exact resolve f142 f138 | exact resolve f138 f142 | grind (instances := 3000) only
  have f167 : ((old sk4 sk1 sk6) ∨ ((sP0 sk4 sk1 sk6) ∨ ((sP1 sk4 sk1 sk6) ∨ ((sP2 sk4 sk1 sk6) ∨ ((sP3 sk4 sk1 sk6) ∨ ((sP4 sk4 sk1 sk6) ∨ ((sP5 sk4 sk1 sk6) ∨ (sP6 sk4 sk1 sk6)))))))) := by
    clear * - f143 f138
    first | exact resolve f143 f138 | exact resolve f138 f143 | grind (instances := 3000) only
  have f168 : ((old sk4 sk7 sk6) ∨ ((sP0 sk4 sk7 sk6) ∨ ((sP1 sk4 sk7 sk6) ∨ ((sP2 sk4 sk7 sk6) ∨ ((sP3 sk4 sk7 sk6) ∨ ((sP4 sk4 sk7 sk6) ∨ ((sP5 sk4 sk7 sk6) ∨ (sP6 sk4 sk7 sk6)))))))) := by
    clear * - f144 f138
    first | exact resolve f144 f138 | exact resolve f138 f144 | grind (instances := 3000) only
  have f169 : ((old sk5 sk5 sk7) ∨ ((sP0 sk5 sk5 sk7) ∨ ((sP1 sk5 sk5 sk7) ∨ ((sP2 sk5 sk5 sk7) ∨ ((sP3 sk5 sk5 sk7) ∨ ((sP4 sk5 sk5 sk7) ∨ ((sP5 sk5 sk5 sk7) ∨ (sP6 sk5 sk5 sk7)))))))) := by
    clear * - f145 f138
    first | exact resolve f145 f138 | exact resolve f138 f145 | grind (instances := 3000) only
  let spl0_1 : Prop := (sP6 sk0 sk0 sk1)
  have f171 : (spl0_1 ↔ (sP6 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_1
  have f172 : ((sP6 sk0 sk0 sk1) ∨ (¬ spl0_1)) := by
    clear * - f171
    grind (instances := 3000) only
  let spl0_2 : Prop := (sP5 sk0 sk0 sk1)
  have f174 : (spl0_2 ↔ (sP5 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_2
  have f175 : ((sP5 sk0 sk0 sk1) ∨ (¬ spl0_2)) := by
    clear * - f174
    grind (instances := 3000) only
  let spl0_3 : Prop := (sP4 sk0 sk0 sk1)
  have f177 : (spl0_3 ↔ (sP4 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_3
  have f178 : ((sP4 sk0 sk0 sk1) ∨ (¬ spl0_3)) := by
    clear * - f177
    grind (instances := 3000) only
  let spl0_4 : Prop := (sP3 sk0 sk0 sk1)
  have f180 : (spl0_4 ↔ (sP3 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_4
  have f181 : ((sP3 sk0 sk0 sk1) ∨ (¬ spl0_4)) := by
    clear * - f180
    grind (instances := 3000) only
  let spl0_5 : Prop := (sP2 sk0 sk0 sk1)
  have f183 : (spl0_5 ↔ (sP2 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_5
  have f184 : ((sP2 sk0 sk0 sk1) ∨ (¬ spl0_5)) := by
    clear * - f183
    grind (instances := 3000) only
  let spl0_6 : Prop := (sP1 sk0 sk0 sk1)
  have f186 : (spl0_6 ↔ (sP1 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_6
  have f187 : ((sP1 sk0 sk0 sk1) ∨ (¬ spl0_6)) := by
    clear * - f186
    grind (instances := 3000) only
  let spl0_7 : Prop := (sP0 sk0 sk0 sk1)
  have f189 : (spl0_7 ↔ (sP0 sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_7
  have f190 : ((sP0 sk0 sk0 sk1) ∨ (¬ spl0_7)) := by
    clear * - f189
    grind (instances := 3000) only
  let spl0_8 : Prop := (old sk0 sk0 sk1)
  have f192 : (spl0_8 ↔ (old sk0 sk0 sk1)) := Iff.rfl
  clear_value spl0_8
  have f193 : ((old sk0 sk0 sk1) ∨ (¬ spl0_8)) := by
    clear * - f192
    grind (instances := 3000) only
  have f194 : (spl0_1 ∨ (spl0_2 ∨ (spl0_3 ∨ (spl0_4 ∨ (spl0_5 ∨ (spl0_6 ∨ (spl0_7 ∨ spl0_8))))))) := by
    clear * - f163 f192 f189 f186 f183 f180 f177 f174 f171
    grind (instances := 3000) only
  have f195 : ((a = b) ∨ (¬ spl0_1)) := by
    clear * - f172 f130
    first | exact resolve f172 f130 | exact resolve f130 f172 | grind (instances := 3000) only
  have f197 : ((c = sk0) ∨ (¬ spl0_1)) := by
    clear * - f172 f132
    first | exact resolve f172 f132 | exact resolve f132 f172 | grind (instances := 3000) only
  have f198 : ((b = sk1) ∨ (¬ spl0_1)) := by
    clear * - f172 f133
    first | exact resolve f172 f133 | exact resolve f133 f172 | grind (instances := 3000) only
  have f206 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_1))) := by
    clear * - f76 f195
    first | exact superpose f76 f195 | exact superpose f195 f76 | grind (instances := 3000) only
  have f208 : ((sP6 c c sk1) ∨ (¬ spl0_1)) := by
    clear * - f172 f197
    first | exact superpose f172 f197 | exact superpose f197 f172 | grind (instances := 3000) only
  have f212 : ((sP6 c c b) ∨ (¬ spl0_1)) := by
    clear * - f208 f198
    grind (instances := 3000) only
  have f227 : ((old a a (sF6 c c b)) ∨ (¬ spl0_1)) := by
    clear * - f212 f134
    first | exact resolve f212 f134 | exact resolve f134 f212 | grind (instances := 3000) only
  have f233 : ((old b b (sF6 c c b)) ∨ (¬ spl0_1)) := by
    clear * - f227 f195
    grind (instances := 3000) only
  have f234 : (False ∨ (¬ spl0_1)) := by
    clear * - f233 f206
    first | exact resolve f233 f206 | exact resolve f206 f233 | grind (instances := 3000) only
  have f235 : (¬ spl0_1) := by
    clear * - f234
    grind (instances := 3000) only
  have f239 : ((old (sF3 sk0 sk0 sk1) a sk0) ∨ (¬ spl0_2)) := by
    clear * - f175 f125
    first | exact resolve f175 f125 | exact resolve f125 f175 | grind (instances := 3000) only
  have f241 : ((c = sk0) ∨ (¬ spl0_2)) := by
    clear * - f175 f123
    first | exact resolve f175 f123 | exact resolve f123 f175 | grind (instances := 3000) only
  have f242 : ((old (sF3 c c sk1) a c) ∨ (¬ spl0_2)) := by
    clear * - f239 f241
    grind (instances := 3000) only
  have f246 : (False ∨ (¬ spl0_2)) := by
    clear * - f242 f77
    first | exact resolve f242 f77 | exact resolve f77 f242 | grind (instances := 3000) only
  have f247 : (¬ spl0_2) := by
    clear * - f246
    grind (instances := 3000) only
  have f253 : ((old b sk1 sk0) ∨ (¬ spl0_3)) := by
    clear * - f178 f119
    first | exact resolve f178 f119 | exact resolve f119 f178 | grind (instances := 3000) only
  have f255 : ((c = sk0) ∨ (¬ spl0_3)) := by
    clear * - f178 f117
    first | exact resolve f178 f117 | exact resolve f117 f178 | grind (instances := 3000) only
  have f257 : ((old b sk1 c) ∨ (¬ spl0_3)) := by
    clear * - f253 f255
    grind (instances := 3000) only
  have f260 : (False ∨ (¬ spl0_3)) := by
    clear * - f257 f77
    first | exact resolve f257 f77 | exact resolve f77 f257 | grind (instances := 3000) only
  have f261 : (¬ spl0_3) := by
    clear * - f260
    grind (instances := 3000) only
  have f265 : ((a = sk0) ∨ (¬ spl0_4)) := by
    clear * - f181 f112
    first | exact resolve f181 f112 | exact resolve f112 f181 | grind (instances := 3000) only
  have f266 : ((c = sk0) ∨ (¬ spl0_4)) := by
    clear * - f181 f111
    first | exact resolve f181 f111 | exact resolve f111 f181 | grind (instances := 3000) only
  have f270 : ((a = c) ∨ (¬ spl0_4)) := by
    clear * - f266 f265
    first | exact superpose f266 f265 | exact superpose f265 f266 | grind (instances := 3000) only
  have f277 : (False ∨ (¬ spl0_4)) := by
    clear * - f270 f74
    first | exact resolve f270 f74 | exact resolve f74 f270 | grind (instances := 3000) only
  have f278 : (¬ spl0_4) := by
    clear * - f277
    grind (instances := 3000) only
  have f283 : ((a = sk0) ∨ (¬ spl0_5)) := by
    clear * - f184 f105
    first | exact resolve f184 f105 | exact resolve f105 f184 | grind (instances := 3000) only
  have f284 : ((c = sk0) ∨ (¬ spl0_5)) := by
    clear * - f184 f104
    first | exact resolve f184 f104 | exact resolve f104 f184 | grind (instances := 3000) only
  have f295 : ((a = c) ∨ (¬ spl0_5)) := by
    clear * - f284 f283
    first | exact superpose f284 f283 | exact superpose f283 f284 | grind (instances := 3000) only
  have f304 : (False ∨ (¬ spl0_5)) := by
    clear * - f295 f74
    first | exact resolve f295 f74 | exact resolve f74 f295 | grind (instances := 3000) only
  have f305 : (¬ spl0_5) := by
    clear * - f304
    grind (instances := 3000) only
  have f306 : ((old (sF0 sk0 sk0 sk1) sk0 a) ∨ (¬ spl0_6)) := by
    clear * - f187 f102
    first | exact resolve f187 f102 | exact resolve f102 f187 | grind (instances := 3000) only
  have f309 : ((c = sk0) ∨ (¬ spl0_6)) := by
    clear * - f187 f99
    first | exact resolve f187 f99 | exact resolve f99 f187 | grind (instances := 3000) only
  have f311 : ((old (sF0 c c sk1) c a) ∨ (¬ spl0_6)) := by
    clear * - f306 f309
    grind (instances := 3000) only
  have f313 : (False ∨ (¬ spl0_6)) := by
    clear * - f311 f78
    first | exact resolve f311 f78 | exact resolve f78 f311 | grind (instances := 3000) only
  have f314 : (¬ spl0_6) := by
    clear * - f313
    grind (instances := 3000) only
  have f315 : ((c = sk1) ∨ (¬ spl0_7)) := by
    clear * - f190 f97
    first | exact resolve f190 f97 | exact resolve f97 f190 | grind (instances := 3000) only
  have f316 : ((b = sk0) ∨ (¬ spl0_7)) := by
    clear * - f190 f96
    first | exact resolve f190 f96 | exact resolve f96 f190 | grind (instances := 3000) only
  have f317 : ((a = sk0) ∨ (¬ spl0_7)) := by
    clear * - f190 f95
    first | exact resolve f190 f95 | exact resolve f95 f190 | grind (instances := 3000) only
  have f319 : ((new sk4 c sk6) ∨ (¬ spl0_7)) := by
    clear * - f143 f315
    first | exact superpose f143 f315 | exact superpose f315 f143 | grind (instances := 3000) only
  have f329 : ((a = b) ∨ (¬ spl0_7)) := by
    clear * - f316 f317
    first | exact superpose f316 f317 | exact superpose f317 f316 | grind (instances := 3000) only
  have f339 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_7))) := by
    clear * - f76 f329
    first | exact superpose f76 f329 | exact superpose f329 f76 | grind (instances := 3000) only
  have f341 : ((old sk4 c sk6) ∨ ((sP0 sk4 c sk6) ∨ ((sP1 sk4 c sk6) ∨ ((sP2 sk4 c sk6) ∨ ((sP3 sk4 c sk6) ∨ ((sP4 sk4 c sk6) ∨ ((sP5 sk4 c sk6) ∨ ((sP6 sk4 c sk6) ∨ (¬ spl0_7))))))))) := by
    clear * - f319 f138
    first | exact resolve f319 f138 | exact resolve f138 f319 | grind (instances := 3000) only
  have f342 : ((sP0 sk4 c sk6) ∨ ((sP1 sk4 c sk6) ∨ ((sP2 sk4 c sk6) ∨ ((sP3 sk4 c sk6) ∨ ((sP4 sk4 c sk6) ∨ ((sP5 sk4 c sk6) ∨ ((sP6 sk4 c sk6) ∨ (¬ spl0_7)))))))) := by
    clear * - f341 f78
    first | exact resolve f341 f78 | exact resolve f78 f341 | grind (instances := 3000) only
  let spl0_9 : Prop := (sP6 sk4 c sk6)
  have f365 : (spl0_9 ↔ (sP6 sk4 c sk6)) := Iff.rfl
  clear_value spl0_9
  have f366 : ((sP6 sk4 c sk6) ∨ (¬ spl0_9)) := by
    clear * - f365
    grind (instances := 3000) only
  let spl0_10 : Prop := (sP5 sk4 c sk6)
  have f368 : (spl0_10 ↔ (sP5 sk4 c sk6)) := Iff.rfl
  clear_value spl0_10
  have f369 : ((sP5 sk4 c sk6) ∨ (¬ spl0_10)) := by
    clear * - f368
    grind (instances := 3000) only
  let spl0_11 : Prop := (sP4 sk4 c sk6)
  have f371 : (spl0_11 ↔ (sP4 sk4 c sk6)) := Iff.rfl
  clear_value spl0_11
  have f372 : ((sP4 sk4 c sk6) ∨ (¬ spl0_11)) := by
    clear * - f371
    grind (instances := 3000) only
  let spl0_12 : Prop := (sP3 sk4 c sk6)
  have f374 : (spl0_12 ↔ (sP3 sk4 c sk6)) := Iff.rfl
  clear_value spl0_12
  have f375 : ((sP3 sk4 c sk6) ∨ (¬ spl0_12)) := by
    clear * - f374
    grind (instances := 3000) only
  let spl0_13 : Prop := (sP2 sk4 c sk6)
  have f377 : (spl0_13 ↔ (sP2 sk4 c sk6)) := Iff.rfl
  clear_value spl0_13
  have f378 : ((sP2 sk4 c sk6) ∨ (¬ spl0_13)) := by
    clear * - f377
    grind (instances := 3000) only
  let spl0_14 : Prop := (sP1 sk4 c sk6)
  have f380 : (spl0_14 ↔ (sP1 sk4 c sk6)) := Iff.rfl
  clear_value spl0_14
  have f381 : ((sP1 sk4 c sk6) ∨ (¬ spl0_14)) := by
    clear * - f380
    grind (instances := 3000) only
  let spl0_15 : Prop := (sP0 sk4 c sk6)
  have f383 : (spl0_15 ↔ (sP0 sk4 c sk6)) := Iff.rfl
  clear_value spl0_15
  have f384 : ((sP0 sk4 c sk6) ∨ (¬ spl0_15)) := by
    clear * - f383
    grind (instances := 3000) only
  have f385 : (spl0_9 ∨ (spl0_10 ∨ (spl0_11 ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ (spl0_15 ∨ (¬ spl0_7)))))))) := by
    clear * - f342 f189 f383 f380 f377 f374 f371 f368 f365
    grind (instances := 3000) only
  have f390 : ((old a a (sF6 sk4 c sk6)) ∨ (¬ spl0_9)) := by
    clear * - f366 f134
    first | exact resolve f366 f134 | exact resolve f134 f366 | grind (instances := 3000) only
  have f396 : ((old b b (sF6 sk4 c sk6)) ∨ ((¬ spl0_7) ∨ (¬ spl0_9))) := by
    clear * - f390 f329
    grind (instances := 3000) only
  have f398 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_9))) := by
    clear * - f396 f339
    first | exact resolve f396 f339 | exact resolve f339 f396 | grind (instances := 3000) only
  have f399 : ((¬ spl0_7) ∨ (¬ spl0_9)) := by
    clear * - f398
    grind (instances := 3000) only
  have f402 : ((c = b) ∨ (¬ spl0_15)) := by
    clear * - f384 f96
    first | exact resolve f384 f96 | exact resolve f96 f384 | grind (instances := 3000) only
  have f405 : (False ∨ (¬ spl0_15)) := by
    clear * - f402 f75
    first | exact resolve f402 f75 | exact resolve f75 f402 | grind (instances := 3000) only
  have f406 : (¬ spl0_15) := by
    clear * - f405
    grind (instances := 3000) only
  have f409 : ((old a a (sF4 sk4 c sk6)) ∨ (¬ spl0_10)) := by
    clear * - f369 f126
    first | exact resolve f369 f126 | exact resolve f126 f369 | grind (instances := 3000) only
  have f411 : ((b = sk6) ∨ (¬ spl0_10)) := by
    clear * - f369 f124
    first | exact resolve f369 f124 | exact resolve f124 f369 | grind (instances := 3000) only
  have f414 : ((old a a (sF4 sk4 c b)) ∨ (¬ spl0_10)) := by
    clear * - f409 f411
    grind (instances := 3000) only
  have f419 : ((old b b (sF4 sk4 c b)) ∨ ((¬ spl0_7) ∨ (¬ spl0_10))) := by
    clear * - f414 f329
    grind (instances := 3000) only
  have f420 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_10))) := by
    clear * - f419 f339
    first | exact resolve f419 f339 | exact resolve f339 f419 | grind (instances := 3000) only
  have f421 : ((¬ spl0_7) ∨ (¬ spl0_10)) := by
    clear * - f420
    grind (instances := 3000) only
  have f423 : ((old b b (sF0 sk4 c sk6)) ∨ (¬ spl0_14)) := by
    clear * - f381 f101
    first | exact resolve f381 f101 | exact resolve f101 f381 | grind (instances := 3000) only
  have f426 : (False ∨ ((¬ spl0_7) ∨ (¬ spl0_14))) := by
    clear * - f423 f339
    first | exact resolve f423 f339 | exact resolve f339 f423 | grind (instances := 3000) only
  have f427 : ((¬ spl0_7) ∨ (¬ spl0_14)) := by
    clear * - f426
    grind (instances := 3000) only
  have f432 : ((old b sk6 c) ∨ (¬ spl0_11)) := by
    clear * - f372 f119
    first | exact resolve f372 f119 | exact resolve f119 f372 | grind (instances := 3000) only
  have f437 : (False ∨ (¬ spl0_11)) := by
    clear * - f432 f77
    first | exact resolve f432 f77 | exact resolve f77 f432 | grind (instances := 3000) only
  have f438 : (¬ spl0_11) := by
    clear * - f437
    grind (instances := 3000) only
  have f445 : ((a = c) ∨ (¬ spl0_12)) := by
    clear * - f375 f112
    first | exact resolve f375 f112 | exact resolve f112 f375 | grind (instances := 3000) only
  have f447 : (False ∨ (¬ spl0_12)) := by
    clear * - f445 f74
    first | exact resolve f445 f74 | exact resolve f74 f445 | grind (instances := 3000) only
  have f448 : (¬ spl0_12) := by
    clear * - f447
    grind (instances := 3000) only
  have f456 : ((a = c) ∨ (¬ spl0_13)) := by
    clear * - f378 f105
    first | exact resolve f378 f105 | exact resolve f105 f378 | grind (instances := 3000) only
  have f458 : (False ∨ (¬ spl0_13)) := by
    clear * - f456 f74
    first | exact resolve f456 f74 | exact resolve f74 f456 | grind (instances := 3000) only
  have f459 : (¬ spl0_13) := by
    clear * - f458
    grind (instances := 3000) only
  have f471 : (∀ (X2 X3 X0 X1 X4 X5 : G), (((¬ (old X3 sk1 X5)) ∨ ((¬ (old X0 X0 X3)) ∨ ((¬ (old X0 sk0 X2)) ∨ ((¬ (old X3 X4 X5)) ∨ ((¬ (old X0 X1 X2)) ∨ ((¬ (old X1 X1 X4)) ∨ (sk0 = X1))))))) ∨ (¬ spl0_8))) := by
    clear * - f193 f92
    first | exact resolve f193 f92 | exact resolve f92 f193 | grind (instances := 3000) only
  let spl0_18 : Prop := (sP6 sk2 sk0 sk3)
  have f489 : (spl0_18 ↔ (sP6 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_18
  have f490 : ((sP6 sk2 sk0 sk3) ∨ (¬ spl0_18)) := by
    clear * - f489
    grind (instances := 3000) only
  let spl0_19 : Prop := (sP5 sk2 sk0 sk3)
  have f492 : (spl0_19 ↔ (sP5 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_19
  have f493 : ((sP5 sk2 sk0 sk3) ∨ (¬ spl0_19)) := by
    clear * - f492
    grind (instances := 3000) only
  let spl0_20 : Prop := (sP4 sk2 sk0 sk3)
  have f495 : (spl0_20 ↔ (sP4 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_20
  have f496 : ((sP4 sk2 sk0 sk3) ∨ (¬ spl0_20)) := by
    clear * - f495
    grind (instances := 3000) only
  let spl0_21 : Prop := (sP3 sk2 sk0 sk3)
  have f498 : (spl0_21 ↔ (sP3 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_21
  have f499 : ((sP3 sk2 sk0 sk3) ∨ (¬ spl0_21)) := by
    clear * - f498
    grind (instances := 3000) only
  let spl0_22 : Prop := (sP2 sk2 sk0 sk3)
  have f501 : (spl0_22 ↔ (sP2 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_22
  have f502 : ((sP2 sk2 sk0 sk3) ∨ (¬ spl0_22)) := by
    clear * - f501
    grind (instances := 3000) only
  let spl0_23 : Prop := (sP1 sk2 sk0 sk3)
  have f504 : (spl0_23 ↔ (sP1 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_23
  have f505 : ((sP1 sk2 sk0 sk3) ∨ (¬ spl0_23)) := by
    clear * - f504
    grind (instances := 3000) only
  let spl0_24 : Prop := (sP0 sk2 sk0 sk3)
  have f507 : (spl0_24 ↔ (sP0 sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_24
  have f508 : ((sP0 sk2 sk0 sk3) ∨ (¬ spl0_24)) := by
    clear * - f507
    grind (instances := 3000) only
  let spl0_25 : Prop := (old sk2 sk0 sk3)
  have f510 : (spl0_25 ↔ (old sk2 sk0 sk3)) := Iff.rfl
  clear_value spl0_25
  have f511 : ((old sk2 sk0 sk3) ∨ (¬ spl0_25)) := by
    clear * - f510
    grind (instances := 3000) only
  have f512 : (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (spl0_21 ∨ (spl0_22 ∨ (spl0_23 ∨ (spl0_24 ∨ spl0_25))))))) := by
    clear * - f164 f510 f507 f504 f501 f498 f495 f492 f489
    grind (instances := 3000) only
  let spl0_28 : Prop := (sP6 sk2 sk2 sk4)
  have f539 : (spl0_28 ↔ (sP6 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_28
  have f540 : ((sP6 sk2 sk2 sk4) ∨ (¬ spl0_28)) := by
    clear * - f539
    grind (instances := 3000) only
  let spl0_29 : Prop := (sP5 sk2 sk2 sk4)
  have f542 : (spl0_29 ↔ (sP5 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_29
  have f543 : ((sP5 sk2 sk2 sk4) ∨ (¬ spl0_29)) := by
    clear * - f542
    grind (instances := 3000) only
  let spl0_30 : Prop := (sP4 sk2 sk2 sk4)
  have f545 : (spl0_30 ↔ (sP4 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_30
  have f546 : ((sP4 sk2 sk2 sk4) ∨ (¬ spl0_30)) := by
    clear * - f545
    grind (instances := 3000) only
  let spl0_31 : Prop := (sP3 sk2 sk2 sk4)
  have f548 : (spl0_31 ↔ (sP3 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_31
  have f549 : ((sP3 sk2 sk2 sk4) ∨ (¬ spl0_31)) := by
    clear * - f548
    grind (instances := 3000) only
  let spl0_32 : Prop := (sP2 sk2 sk2 sk4)
  have f551 : (spl0_32 ↔ (sP2 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_32
  have f552 : ((sP2 sk2 sk2 sk4) ∨ (¬ spl0_32)) := by
    clear * - f551
    grind (instances := 3000) only
  let spl0_33 : Prop := (sP1 sk2 sk2 sk4)
  have f554 : (spl0_33 ↔ (sP1 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_33
  have f555 : ((sP1 sk2 sk2 sk4) ∨ (¬ spl0_33)) := by
    clear * - f554
    grind (instances := 3000) only
  let spl0_34 : Prop := (sP0 sk2 sk2 sk4)
  have f557 : (spl0_34 ↔ (sP0 sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_34
  have f558 : ((sP0 sk2 sk2 sk4) ∨ (¬ spl0_34)) := by
    clear * - f557
    grind (instances := 3000) only
  let spl0_35 : Prop := (old sk2 sk2 sk4)
  have f560 : (spl0_35 ↔ (old sk2 sk2 sk4)) := Iff.rfl
  clear_value spl0_35
  have f561 : ((old sk2 sk2 sk4) ∨ (¬ spl0_35)) := by
    clear * - f560
    grind (instances := 3000) only
  have f562 : (spl0_28 ∨ (spl0_29 ∨ (spl0_30 ∨ (spl0_31 ∨ (spl0_32 ∨ (spl0_33 ∨ (spl0_34 ∨ spl0_35))))))) := by
    clear * - f165 f560 f557 f554 f551 f548 f545 f542 f539
    grind (instances := 3000) only
  let spl0_75 : Prop := (sP6 sk2 sk5 sk3)
  have f784 : (spl0_75 ↔ (sP6 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_75
  have f785 : ((sP6 sk2 sk5 sk3) ∨ (¬ spl0_75)) := by
    clear * - f784
    grind (instances := 3000) only
  let spl0_76 : Prop := (sP5 sk2 sk5 sk3)
  have f787 : (spl0_76 ↔ (sP5 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_76
  have f788 : ((sP5 sk2 sk5 sk3) ∨ (¬ spl0_76)) := by
    clear * - f787
    grind (instances := 3000) only
  let spl0_77 : Prop := (sP4 sk2 sk5 sk3)
  have f790 : (spl0_77 ↔ (sP4 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_77
  have f791 : ((sP4 sk2 sk5 sk3) ∨ (¬ spl0_77)) := by
    clear * - f790
    grind (instances := 3000) only
  let spl0_78 : Prop := (sP3 sk2 sk5 sk3)
  have f793 : (spl0_78 ↔ (sP3 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_78
  have f794 : ((sP3 sk2 sk5 sk3) ∨ (¬ spl0_78)) := by
    clear * - f793
    grind (instances := 3000) only
  let spl0_79 : Prop := (sP2 sk2 sk5 sk3)
  have f796 : (spl0_79 ↔ (sP2 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_79
  have f797 : ((sP2 sk2 sk5 sk3) ∨ (¬ spl0_79)) := by
    clear * - f796
    grind (instances := 3000) only
  let spl0_80 : Prop := (sP1 sk2 sk5 sk3)
  have f799 : (spl0_80 ↔ (sP1 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_80
  have f800 : ((sP1 sk2 sk5 sk3) ∨ (¬ spl0_80)) := by
    clear * - f799
    grind (instances := 3000) only
  let spl0_81 : Prop := (sP0 sk2 sk5 sk3)
  have f802 : (spl0_81 ↔ (sP0 sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_81
  have f803 : ((sP0 sk2 sk5 sk3) ∨ (¬ spl0_81)) := by
    clear * - f802
    grind (instances := 3000) only
  let spl0_82 : Prop := (old sk2 sk5 sk3)
  have f805 : (spl0_82 ↔ (old sk2 sk5 sk3)) := Iff.rfl
  clear_value spl0_82
  have f806 : ((old sk2 sk5 sk3) ∨ (¬ spl0_82)) := by
    clear * - f805
    grind (instances := 3000) only
  have f807 : (spl0_75 ∨ (spl0_76 ∨ (spl0_77 ∨ (spl0_78 ∨ (spl0_79 ∨ (spl0_80 ∨ (spl0_81 ∨ spl0_82))))))) := by
    clear * - f166 f805 f802 f799 f796 f793 f790 f787 f784
    grind (instances := 3000) only
  let spl0_119 : Prop := (sP6 sk4 sk1 sk6)
  have f1000 : (spl0_119 ↔ (sP6 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_119
  have f1001 : ((sP6 sk4 sk1 sk6) ∨ (¬ spl0_119)) := by
    clear * - f1000
    grind (instances := 3000) only
  let spl0_120 : Prop := (sP5 sk4 sk1 sk6)
  have f1003 : (spl0_120 ↔ (sP5 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_120
  have f1004 : ((sP5 sk4 sk1 sk6) ∨ (¬ spl0_120)) := by
    clear * - f1003
    grind (instances := 3000) only
  let spl0_121 : Prop := (sP4 sk4 sk1 sk6)
  have f1006 : (spl0_121 ↔ (sP4 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_121
  have f1007 : ((sP4 sk4 sk1 sk6) ∨ (¬ spl0_121)) := by
    clear * - f1006
    grind (instances := 3000) only
  let spl0_122 : Prop := (sP3 sk4 sk1 sk6)
  have f1009 : (spl0_122 ↔ (sP3 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_122
  have f1010 : ((sP3 sk4 sk1 sk6) ∨ (¬ spl0_122)) := by
    clear * - f1009
    grind (instances := 3000) only
  let spl0_123 : Prop := (sP2 sk4 sk1 sk6)
  have f1012 : (spl0_123 ↔ (sP2 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_123
  have f1013 : ((sP2 sk4 sk1 sk6) ∨ (¬ spl0_123)) := by
    clear * - f1012
    grind (instances := 3000) only
  let spl0_124 : Prop := (sP1 sk4 sk1 sk6)
  have f1015 : (spl0_124 ↔ (sP1 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_124
  have f1016 : ((sP1 sk4 sk1 sk6) ∨ (¬ spl0_124)) := by
    clear * - f1015
    grind (instances := 3000) only
  let spl0_125 : Prop := (sP0 sk4 sk1 sk6)
  have f1018 : (spl0_125 ↔ (sP0 sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_125
  have f1019 : ((sP0 sk4 sk1 sk6) ∨ (¬ spl0_125)) := by
    clear * - f1018
    grind (instances := 3000) only
  let spl0_126 : Prop := (old sk4 sk1 sk6)
  have f1021 : (spl0_126 ↔ (old sk4 sk1 sk6)) := Iff.rfl
  clear_value spl0_126
  have f1022 : ((old sk4 sk1 sk6) ∨ (¬ spl0_126)) := by
    clear * - f1021
    grind (instances := 3000) only
  have f1023 : (spl0_119 ∨ (spl0_120 ∨ (spl0_121 ∨ (spl0_122 ∨ (spl0_123 ∨ (spl0_124 ∨ (spl0_125 ∨ spl0_126))))))) := by
    clear * - f167 f1021 f1018 f1015 f1012 f1009 f1006 f1003 f1000
    grind (instances := 3000) only
  have f1025 : (∀ (X2 X3 X0 X1 : G), (((¬ (old sk4 X2 sk6)) ∨ ((¬ (old X0 sk0 X1)) ∨ ((¬ (old X0 X0 sk4)) ∨ ((¬ (old X0 X3 X1)) ∨ ((¬ (old X3 X3 X2)) ∨ (sk0 = X3)))))) ∨ ((¬ spl0_8) ∨ (¬ spl0_126)))) := by
    clear * - f1022 f471
    first | exact resolve f1022 f471 | exact resolve f471 f1022 | grind (instances := 3000) only
  let spl0_168 : Prop := (sP6 sk4 sk7 sk6)
  have f1229 : (spl0_168 ↔ (sP6 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_168
  have f1230 : ((sP6 sk4 sk7 sk6) ∨ (¬ spl0_168)) := by
    clear * - f1229
    grind (instances := 3000) only
  let spl0_169 : Prop := (sP5 sk4 sk7 sk6)
  have f1232 : (spl0_169 ↔ (sP5 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_169
  have f1233 : ((sP5 sk4 sk7 sk6) ∨ (¬ spl0_169)) := by
    clear * - f1232
    grind (instances := 3000) only
  let spl0_170 : Prop := (sP4 sk4 sk7 sk6)
  have f1235 : (spl0_170 ↔ (sP4 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_170
  have f1236 : ((sP4 sk4 sk7 sk6) ∨ (¬ spl0_170)) := by
    clear * - f1235
    grind (instances := 3000) only
  let spl0_171 : Prop := (sP3 sk4 sk7 sk6)
  have f1238 : (spl0_171 ↔ (sP3 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_171
  have f1239 : ((sP3 sk4 sk7 sk6) ∨ (¬ spl0_171)) := by
    clear * - f1238
    grind (instances := 3000) only
  let spl0_172 : Prop := (sP2 sk4 sk7 sk6)
  have f1241 : (spl0_172 ↔ (sP2 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_172
  have f1242 : ((sP2 sk4 sk7 sk6) ∨ (¬ spl0_172)) := by
    clear * - f1241
    grind (instances := 3000) only
  let spl0_173 : Prop := (sP1 sk4 sk7 sk6)
  have f1244 : (spl0_173 ↔ (sP1 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_173
  have f1245 : ((sP1 sk4 sk7 sk6) ∨ (¬ spl0_173)) := by
    clear * - f1244
    grind (instances := 3000) only
  let spl0_174 : Prop := (sP0 sk4 sk7 sk6)
  have f1247 : (spl0_174 ↔ (sP0 sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_174
  have f1248 : ((sP0 sk4 sk7 sk6) ∨ (¬ spl0_174)) := by
    clear * - f1247
    grind (instances := 3000) only
  let spl0_175 : Prop := (old sk4 sk7 sk6)
  have f1250 : (spl0_175 ↔ (old sk4 sk7 sk6)) := Iff.rfl
  clear_value spl0_175
  have f1251 : ((old sk4 sk7 sk6) ∨ (¬ spl0_175)) := by
    clear * - f1250
    grind (instances := 3000) only
  have f1252 : (spl0_168 ∨ (spl0_169 ∨ (spl0_170 ∨ (spl0_171 ∨ (spl0_172 ∨ (spl0_173 ∨ (spl0_174 ∨ spl0_175))))))) := by
    clear * - f168 f1250 f1247 f1244 f1241 f1238 f1235 f1232 f1229
    grind (instances := 3000) only
  have f1253 : (∀ (X2 X0 X1 : G), (((¬ (old X2 X2 sk7)) ∨ ((¬ (old X0 X0 sk4)) ∨ ((¬ (old X0 X2 X1)) ∨ ((¬ (old X0 sk0 X1)) ∨ (sk0 = X2))))) ∨ ((¬ spl0_8) ∨ ((¬ spl0_126) ∨ (¬ spl0_175))))) := by
    clear * - f1251 f1025
    first | exact resolve f1251 f1025 | exact resolve f1025 f1251 | grind (instances := 3000) only
  let spl0_182 : Prop := (sP6 sk5 sk5 sk7)
  have f1283 : (spl0_182 ↔ (sP6 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_182
  have f1284 : ((sP6 sk5 sk5 sk7) ∨ (¬ spl0_182)) := by
    clear * - f1283
    grind (instances := 3000) only
  let spl0_183 : Prop := (sP5 sk5 sk5 sk7)
  have f1286 : (spl0_183 ↔ (sP5 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_183
  have f1287 : ((sP5 sk5 sk5 sk7) ∨ (¬ spl0_183)) := by
    clear * - f1286
    grind (instances := 3000) only
  let spl0_184 : Prop := (sP4 sk5 sk5 sk7)
  have f1289 : (spl0_184 ↔ (sP4 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_184
  have f1290 : ((sP4 sk5 sk5 sk7) ∨ (¬ spl0_184)) := by
    clear * - f1289
    grind (instances := 3000) only
  let spl0_185 : Prop := (sP3 sk5 sk5 sk7)
  have f1292 : (spl0_185 ↔ (sP3 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_185
  have f1293 : ((sP3 sk5 sk5 sk7) ∨ (¬ spl0_185)) := by
    clear * - f1292
    grind (instances := 3000) only
  let spl0_186 : Prop := (sP2 sk5 sk5 sk7)
  have f1295 : (spl0_186 ↔ (sP2 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_186
  have f1296 : ((sP2 sk5 sk5 sk7) ∨ (¬ spl0_186)) := by
    clear * - f1295
    grind (instances := 3000) only
  let spl0_187 : Prop := (sP1 sk5 sk5 sk7)
  have f1298 : (spl0_187 ↔ (sP1 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_187
  have f1299 : ((sP1 sk5 sk5 sk7) ∨ (¬ spl0_187)) := by
    clear * - f1298
    grind (instances := 3000) only
  let spl0_188 : Prop := (sP0 sk5 sk5 sk7)
  have f1301 : (spl0_188 ↔ (sP0 sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_188
  have f1302 : ((sP0 sk5 sk5 sk7) ∨ (¬ spl0_188)) := by
    clear * - f1301
    grind (instances := 3000) only
  let spl0_189 : Prop := (old sk5 sk5 sk7)
  have f1304 : (spl0_189 ↔ (old sk5 sk5 sk7)) := Iff.rfl
  clear_value spl0_189
  have f1305 : ((old sk5 sk5 sk7) ∨ (¬ spl0_189)) := by
    clear * - f1304
    grind (instances := 3000) only
  have f1306 : (spl0_182 ∨ (spl0_183 ∨ (spl0_184 ∨ (spl0_185 ∨ (spl0_186 ∨ (spl0_187 ∨ (spl0_188 ∨ spl0_189))))))) := by
    clear * - f169 f1304 f1301 f1298 f1295 f1292 f1289 f1286 f1283
    grind (instances := 3000) only
  have f1308 : (∀ (X0 X1 : G), (((¬ (old X0 X0 sk4)) ∨ ((¬ (old X0 sk5 X1)) ∨ ((¬ (old X0 sk0 X1)) ∨ (sk0 = sk5)))) ∨ ((¬ spl0_8) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189)))))) := by
    clear * - f1305 f1253
    first | exact resolve f1305 f1253 | exact resolve f1253 f1305 | grind (instances := 3000) only
  have f1318 : (∀ (X0 X1 : G), (((¬ (old X0 sk5 X1)) ∨ ((¬ (old X0 X0 sk4)) ∨ (¬ (old X0 sk0 X1)))) ∨ ((¬ spl0_8) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189)))))) := by
    clear * - f1308 f146
    first | exact resolve f1308 f146 | exact resolve f146 f1308 | grind (instances := 3000) only
  have f1322 : ((¬ (old sk2 sk2 sk4)) ∨ ((¬ (old sk2 sk0 sk3)) ∨ ((¬ spl0_8) ∨ ((¬ spl0_82) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189))))))) := by
    clear * - f1318 f806
    first | exact resolve f1318 f806 | exact resolve f806 f1318 | grind (instances := 3000) only
  have f1332 : ((¬ (old sk2 sk0 sk3)) ∨ ((¬ spl0_8) ∨ ((¬ spl0_35) ∨ ((¬ spl0_82) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189))))))) := by
    clear * - f1322 f561
    first | exact resolve f1322 f561 | exact resolve f561 f1322 | grind (instances := 3000) only
  have f1333 : (False ∨ ((¬ spl0_8) ∨ ((¬ spl0_25) ∨ ((¬ spl0_35) ∨ ((¬ spl0_82) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189)))))))) := by
    clear * - f1332 f511
    first | exact resolve f1332 f511 | exact resolve f511 f1332 | grind (instances := 3000) only
  have f1334 : ((¬ spl0_8) ∨ ((¬ spl0_25) ∨ ((¬ spl0_35) ∨ ((¬ spl0_82) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189))))))) := by
    clear * - f1333
    grind (instances := 3000) only
  have f1335 : ((c = sk7) ∨ (¬ spl0_188)) := by
    clear * - f1302 f97
    first | exact resolve f1302 f97 | exact resolve f97 f1302 | grind (instances := 3000) only
  have f1336 : ((b = sk5) ∨ (¬ spl0_188)) := by
    clear * - f1302 f96
    first | exact resolve f1302 f96 | exact resolve f96 f1302 | grind (instances := 3000) only
  have f1337 : ((a = sk5) ∨ (¬ spl0_188)) := by
    clear * - f1302 f95
    first | exact resolve f1302 f95 | exact resolve f95 f1302 | grind (instances := 3000) only
  have f1340 : ((old sk4 c sk6) ∨ ((¬ spl0_175) ∨ (¬ spl0_188))) := by
    clear * - f1251 f1335
    first | exact superpose f1251 f1335 | exact superpose f1335 f1251 | grind (instances := 3000) only
  have f1349 : (False ∨ ((¬ spl0_175) ∨ (¬ spl0_188))) := by
    clear * - f1340 f78
    first | exact resolve f1340 f78 | exact resolve f78 f1340 | grind (instances := 3000) only
  have f1350 : ((¬ spl0_175) ∨ (¬ spl0_188)) := by
    clear * - f1349
    grind (instances := 3000) only
  have f1352 : ((old (sF0 sk5 sk5 sk7) sk5 a) ∨ (¬ spl0_187)) := by
    clear * - f1299 f102
    first | exact resolve f1299 f102 | exact resolve f102 f1299 | grind (instances := 3000) only
  have f1355 : ((c = sk5) ∨ (¬ spl0_187)) := by
    clear * - f1299 f99
    first | exact resolve f1299 f99 | exact resolve f99 f1299 | grind (instances := 3000) only
  have f1357 : ((old (sF0 c c sk7) c a) ∨ (¬ spl0_187)) := by
    clear * - f1352 f1355
    grind (instances := 3000) only
  have f1359 : (False ∨ (¬ spl0_187)) := by
    clear * - f1357 f78
    first | exact resolve f1357 f78 | exact resolve f78 f1357 | grind (instances := 3000) only
  have f1360 : (¬ spl0_187) := by
    clear * - f1359
    grind (instances := 3000) only
  have f1365 : ((a = sk5) ∨ (¬ spl0_186)) := by
    clear * - f1296 f105
    first | exact resolve f1296 f105 | exact resolve f105 f1296 | grind (instances := 3000) only
  have f1366 : ((c = sk5) ∨ (¬ spl0_186)) := by
    clear * - f1296 f104
    first | exact resolve f1296 f104 | exact resolve f104 f1296 | grind (instances := 3000) only
  have f1406 : ((a = c) ∨ (¬ spl0_186)) := by
    clear * - f1366 f1365
    first | exact superpose f1366 f1365 | exact superpose f1365 f1366 | grind (instances := 3000) only
  have f1439 : (False ∨ (¬ spl0_186)) := by
    clear * - f1406 f74
    first | exact resolve f1406 f74 | exact resolve f74 f1406 | grind (instances := 3000) only
  have f1440 : (¬ spl0_186) := by
    clear * - f1439
    grind (instances := 3000) only
  have f1444 : ((a = sk5) ∨ (¬ spl0_185)) := by
    clear * - f1293 f112
    first | exact resolve f1293 f112 | exact resolve f112 f1293 | grind (instances := 3000) only
  have f1445 : ((c = sk5) ∨ (¬ spl0_185)) := by
    clear * - f1293 f111
    first | exact resolve f1293 f111 | exact resolve f111 f1293 | grind (instances := 3000) only
  have f1471 : ((a = c) ∨ (¬ spl0_185)) := by
    clear * - f1445 f1444
    first | exact superpose f1445 f1444 | exact superpose f1444 f1445 | grind (instances := 3000) only
  have f1502 : (False ∨ (¬ spl0_185)) := by
    clear * - f1471 f74
    first | exact resolve f1471 f74 | exact resolve f74 f1471 | grind (instances := 3000) only
  have f1503 : (¬ spl0_185) := by
    clear * - f1502
    grind (instances := 3000) only
  have f1506 : ((old b sk7 sk5) ∨ (¬ spl0_184)) := by
    clear * - f1290 f119
    first | exact resolve f1290 f119 | exact resolve f119 f1290 | grind (instances := 3000) only
  have f1508 : ((c = sk5) ∨ (¬ spl0_184)) := by
    clear * - f1290 f117
    first | exact resolve f1290 f117 | exact resolve f117 f1290 | grind (instances := 3000) only
  have f1510 : ((old b sk7 c) ∨ (¬ spl0_184)) := by
    clear * - f1506 f1508
    grind (instances := 3000) only
  have f1513 : (False ∨ (¬ spl0_184)) := by
    clear * - f1510 f77
    first | exact resolve f1510 f77 | exact resolve f77 f1510 | grind (instances := 3000) only
  have f1514 : (¬ spl0_184) := by
    clear * - f1513
    grind (instances := 3000) only
  have f1518 : ((old (sF3 sk5 sk5 sk7) a sk5) ∨ (¬ spl0_183)) := by
    clear * - f1287 f125
    first | exact resolve f1287 f125 | exact resolve f125 f1287 | grind (instances := 3000) only
  have f1520 : ((c = sk5) ∨ (¬ spl0_183)) := by
    clear * - f1287 f123
    first | exact resolve f1287 f123 | exact resolve f123 f1287 | grind (instances := 3000) only
  have f1521 : ((old (sF3 c c sk7) a c) ∨ (¬ spl0_183)) := by
    clear * - f1518 f1520
    grind (instances := 3000) only
  have f1525 : (False ∨ (¬ spl0_183)) := by
    clear * - f1521 f77
    first | exact resolve f1521 f77 | exact resolve f77 f1521 | grind (instances := 3000) only
  have f1526 : (¬ spl0_183) := by
    clear * - f1525
    grind (instances := 3000) only
  have f1530 : ((a = b) ∨ (¬ spl0_182)) := by
    clear * - f1284 f130
    first | exact resolve f1284 f130 | exact resolve f130 f1284 | grind (instances := 3000) only
  have f1532 : ((c = sk5) ∨ (¬ spl0_182)) := by
    clear * - f1284 f132
    first | exact resolve f1284 f132 | exact resolve f132 f1284 | grind (instances := 3000) only
  have f1533 : ((b = sk7) ∨ (¬ spl0_182)) := by
    clear * - f1284 f133
    first | exact resolve f1284 f133 | exact resolve f133 f1284 | grind (instances := 3000) only
  have f1537 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_182))) := by
    clear * - f76 f1530
    first | exact superpose f76 f1530 | exact superpose f1530 f76 | grind (instances := 3000) only
  have f1567 : ((sP6 c c sk7) ∨ (¬ spl0_182)) := by
    clear * - f1284 f1532
    first | exact superpose f1284 f1532 | exact superpose f1532 f1284 | grind (instances := 3000) only
  have f1568 : ((sP6 c c b) ∨ (¬ spl0_182)) := by
    clear * - f1567 f1533
    grind (instances := 3000) only
  have f1583 : ((c = sk0) ∨ (¬ spl0_18)) := by
    clear * - f490 f132
    first | exact resolve f490 f132 | exact resolve f132 f490 | grind (instances := 3000) only
  have f1603 : ((c = sk0) ∨ (¬ spl0_19)) := by
    clear * - f493 f123
    first | exact resolve f493 f123 | exact resolve f123 f493 | grind (instances := 3000) only
  have f1619 : ((c = sk2) ∨ (¬ spl0_20)) := by
    clear * - f496 f117
    first | exact resolve f496 f117 | exact resolve f117 f496 | grind (instances := 3000) only
  have f1627 : ((old b b b) ∨ (¬ spl0_21)) := by
    clear * - f499 f113
    first | exact resolve f499 f113 | exact resolve f113 f499 | grind (instances := 3000) only
  have f1629 : ((c = sk2) ∨ (¬ spl0_21)) := by
    clear * - f499 f111
    first | exact resolve f499 f111 | exact resolve f111 f499 | grind (instances := 3000) only
  have f1636 : ((old a a a) ∨ (¬ spl0_22)) := by
    clear * - f502 f107
    first | exact resolve f502 f107 | exact resolve f107 f502 | grind (instances := 3000) only
  have f1639 : ((c = sk2) ∨ (¬ spl0_22)) := by
    clear * - f502 f104
    first | exact resolve f502 f104 | exact resolve f104 f502 | grind (instances := 3000) only
  have f1653 : ((c = sk0) ∨ (¬ spl0_23)) := by
    clear * - f505 f99
    first | exact resolve f505 f99 | exact resolve f99 f505 | grind (instances := 3000) only
  have f1660 : ((c = sk3) ∨ (¬ spl0_24)) := by
    clear * - f508 f97
    first | exact resolve f508 f97 | exact resolve f97 f508 | grind (instances := 3000) only
  have f1661 : ((b = sk0) ∨ (¬ spl0_24)) := by
    clear * - f508 f96
    first | exact resolve f508 f96 | exact resolve f96 f508 | grind (instances := 3000) only
  have f1662 : ((a = sk2) ∨ (¬ spl0_24)) := by
    clear * - f508 f95
    first | exact resolve f508 f95 | exact resolve f95 f508 | grind (instances := 3000) only
  have f1746 : ((c = sk6) ∨ (¬ spl0_174)) := by
    clear * - f1248 f97
    first | exact resolve f1248 f97 | exact resolve f97 f1248 | grind (instances := 3000) only
  have f1747 : ((b = sk7) ∨ (¬ spl0_174)) := by
    clear * - f1248 f96
    first | exact resolve f1248 f96 | exact resolve f96 f1248 | grind (instances := 3000) only
  have f1748 : ((a = sk4) ∨ (¬ spl0_174)) := by
    clear * - f1248 f95
    first | exact resolve f1248 f95 | exact resolve f95 f1248 | grind (instances := 3000) only
  have f1751 : ((old sk4 sk1 c) ∨ ((¬ spl0_126) ∨ (¬ spl0_174))) := by
    clear * - f1022 f1746
    first | exact superpose f1022 f1746 | exact superpose f1746 f1022 | grind (instances := 3000) only
  have f1758 : (False ∨ ((¬ spl0_126) ∨ (¬ spl0_174))) := by
    clear * - f1751 f77
    first | exact resolve f1751 f77 | exact resolve f77 f1751 | grind (instances := 3000) only
  have f1759 : ((¬ spl0_126) ∨ (¬ spl0_174)) := by
    clear * - f1758
    grind (instances := 3000) only
  have f1765 : ((old b b (sF0 sk4 sk7 sk6)) ∨ (¬ spl0_173)) := by
    clear * - f1245 f101
    first | exact resolve f1245 f101 | exact resolve f101 f1245 | grind (instances := 3000) only
  have f1766 : ((b = sk6) ∨ (¬ spl0_173)) := by
    clear * - f1245 f100
    first | exact resolve f1245 f100 | exact resolve f100 f1245 | grind (instances := 3000) only
  have f1767 : ((c = sk7) ∨ (¬ spl0_173)) := by
    clear * - f1245 f99
    first | exact resolve f1245 f99 | exact resolve f99 f1245 | grind (instances := 3000) only
  have f1768 : ((old b b (sF0 sk4 sk7 b)) ∨ (¬ spl0_173)) := by
    clear * - f1765 f1766
    grind (instances := 3000) only
  have f1770 : ((old b b (sF0 sk4 c b)) ∨ (¬ spl0_173)) := by
    clear * - f1768 f1767
    grind (instances := 3000) only
  have f1796 : ((old sk5 sk5 c) ∨ ((¬ spl0_173) ∨ (¬ spl0_189))) := by
    clear * - f1305 f1767
    first | exact superpose f1305 f1767 | exact superpose f1767 f1305 | grind (instances := 3000) only
  have f1797 : (False ∨ ((¬ spl0_173) ∨ (¬ spl0_189))) := by
    clear * - f1796 f77
    first | exact resolve f1796 f77 | exact resolve f77 f1796 | grind (instances := 3000) only
  have f1798 : ((¬ spl0_173) ∨ (¬ spl0_189)) := by
    clear * - f1797
    grind (instances := 3000) only
  have f1810 : ((a = b) ∨ (¬ spl0_188)) := by
    clear * - f1337 f1336
    grind (instances := 3000) only
  have f1816 : ((old sk2 b sk3) ∨ ((¬ spl0_82) ∨ (¬ spl0_188))) := by
    clear * - f806 f1336
    first | exact superpose f806 f1336 | exact superpose f1336 f806 | grind (instances := 3000) only
  have f1824 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_188))) := by
    clear * - f76 f1810
    first | exact superpose f76 f1810 | exact superpose f1810 f76 | grind (instances := 3000) only
  have f1867 : (False ∨ ((¬ spl0_173) ∨ (¬ spl0_188))) := by
    clear * - f1770 f1824
    first | exact resolve f1770 f1824 | exact resolve f1824 f1770 | grind (instances := 3000) only
  have f1876 : ((¬ spl0_173) ∨ (¬ spl0_188)) := by
    clear * - f1867
    grind (instances := 3000) only
  have f1879 : ((old a a a) ∨ (¬ spl0_172)) := by
    clear * - f1242 f107
    first | exact resolve f1242 f107 | exact resolve f107 f1242 | grind (instances := 3000) only
  have f1880 : ((a = sk6) ∨ (¬ spl0_172)) := by
    clear * - f1242 f106
    first | exact resolve f1242 f106 | exact resolve f106 f1242 | grind (instances := 3000) only
  have f1882 : ((c = sk4) ∨ (¬ spl0_172)) := by
    clear * - f1242 f104
    first | exact resolve f1242 f104 | exact resolve f104 f1242 | grind (instances := 3000) only
  have f1885 : ((old sk4 sk1 a) ∨ ((¬ spl0_126) ∨ (¬ spl0_172))) := by
    clear * - f1022 f1880
    first | exact superpose f1022 f1880 | exact superpose f1880 f1022 | grind (instances := 3000) only
  have f1892 : ((old c sk1 a) ∨ ((¬ spl0_126) ∨ (¬ spl0_172))) := by
    clear * - f1885 f1882
    grind (instances := 3000) only
  have f1896 : (False ∨ ((¬ spl0_126) ∨ (¬ spl0_172))) := by
    clear * - f1892 f79
    first | exact resolve f1892 f79 | exact resolve f79 f1892 | grind (instances := 3000) only
  have f1897 : ((¬ spl0_126) ∨ (¬ spl0_172)) := by
    clear * - f1896
    grind (instances := 3000) only
  have f1901 : ((old b b b) ∨ (¬ spl0_171)) := by
    clear * - f1239 f113
    first | exact resolve f1239 f113 | exact resolve f113 f1239 | grind (instances := 3000) only
  have f1903 : ((c = sk4) ∨ (¬ spl0_171)) := by
    clear * - f1239 f111
    first | exact resolve f1239 f111 | exact resolve f111 f1239 | grind (instances := 3000) only
  have f1913 : ((old sk2 sk2 c) ∨ ((¬ spl0_35) ∨ (¬ spl0_171))) := by
    clear * - f561 f1903
    first | exact superpose f561 f1903 | exact superpose f1903 f561 | grind (instances := 3000) only
  have f1932 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_171))) := by
    clear * - f1913 f77
    first | exact resolve f1913 f77 | exact resolve f77 f1913 | grind (instances := 3000) only
  have f1933 : ((¬ spl0_35) ∨ (¬ spl0_171)) := by
    clear * - f1932
    grind (instances := 3000) only
  have f1939 : ((c = sk4) ∨ (¬ spl0_170)) := by
    clear * - f1236 f117
    first | exact resolve f1236 f117 | exact resolve f117 f1236 | grind (instances := 3000) only
  have f1946 : ((old sk2 sk2 c) ∨ ((¬ spl0_35) ∨ (¬ spl0_170))) := by
    clear * - f561 f1939
    first | exact superpose f561 f1939 | exact superpose f1939 f561 | grind (instances := 3000) only
  have f1959 : ((sP4 c sk7 sk6) ∨ (¬ spl0_170)) := by
    clear * - f1236 f1939
    first | exact superpose f1236 f1939 | exact superpose f1939 f1236 | grind (instances := 3000) only
  have f1964 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_170))) := by
    clear * - f1946 f77
    first | exact resolve f1946 f77 | exact resolve f77 f1946 | grind (instances := 3000) only
  have f1965 : ((¬ spl0_35) ∨ (¬ spl0_170)) := by
    clear * - f1964
    grind (instances := 3000) only
  have f1968 : ((old a a (sF4 sk4 sk7 sk6)) ∨ (¬ spl0_169)) := by
    clear * - f1233 f126
    first | exact resolve f1233 f126 | exact resolve f126 f1233 | grind (instances := 3000) only
  have f1970 : ((b = sk6) ∨ (¬ spl0_169)) := by
    clear * - f1233 f124
    first | exact resolve f1233 f124 | exact resolve f124 f1233 | grind (instances := 3000) only
  have f1971 : ((c = sk7) ∨ (¬ spl0_169)) := by
    clear * - f1233 f123
    first | exact resolve f1233 f123 | exact resolve f123 f1233 | grind (instances := 3000) only
  have f1973 : ((old a a (sF4 sk4 sk7 b)) ∨ (¬ spl0_169)) := by
    clear * - f1968 f1970
    grind (instances := 3000) only
  have f1977 : ((old a a (sF4 sk4 c b)) ∨ (¬ spl0_169)) := by
    clear * - f1973 f1971
    grind (instances := 3000) only
  have f2004 : ((old sk5 sk5 c) ∨ ((¬ spl0_169) ∨ (¬ spl0_189))) := by
    clear * - f1305 f1971
    first | exact superpose f1305 f1971 | exact superpose f1971 f1305 | grind (instances := 3000) only
  have f2005 : (False ∨ ((¬ spl0_169) ∨ (¬ spl0_189))) := by
    clear * - f2004 f77
    first | exact resolve f2004 f77 | exact resolve f77 f2004 | grind (instances := 3000) only
  have f2006 : ((¬ spl0_169) ∨ (¬ spl0_189)) := by
    clear * - f2005
    grind (instances := 3000) only
  have f2087 : ((old b b (sF4 sk4 c b)) ∨ ((¬ spl0_169) ∨ (¬ spl0_188))) := by
    clear * - f1977 f1810
    first | exact superpose f1977 f1810 | exact superpose f1810 f1977 | grind (instances := 3000) only
  have f2088 : (False ∨ ((¬ spl0_169) ∨ (¬ spl0_188))) := by
    clear * - f2087 f1824
    first | exact resolve f2087 f1824 | exact resolve f1824 f2087 | grind (instances := 3000) only
  have f2089 : ((¬ spl0_169) ∨ (¬ spl0_188)) := by
    clear * - f2088
    grind (instances := 3000) only
  have f2109 : ((a = b) ∨ (¬ spl0_168)) := by
    clear * - f1230 f130
    first | exact resolve f1230 f130 | exact resolve f130 f1230 | grind (instances := 3000) only
  have f2110 : ((c = sk4) ∨ (¬ spl0_168)) := by
    clear * - f1230 f131
    first | exact resolve f1230 f131 | exact resolve f131 f1230 | grind (instances := 3000) only
  have f2111 : ((c = sk7) ∨ (¬ spl0_168)) := by
    clear * - f1230 f132
    first | exact resolve f1230 f132 | exact resolve f132 f1230 | grind (instances := 3000) only
  have f2112 : ((b = sk6) ∨ (¬ spl0_168)) := by
    clear * - f1230 f133
    first | exact resolve f1230 f133 | exact resolve f133 f1230 | grind (instances := 3000) only
  have f2116 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_168))) := by
    clear * - f76 f2109
    first | exact superpose f76 f2109 | exact superpose f2109 f76 | grind (instances := 3000) only
  have f2125 : ((old sk2 sk2 c) ∨ ((¬ spl0_35) ∨ (¬ spl0_168))) := by
    clear * - f561 f2110
    first | exact superpose f561 f2110 | exact superpose f2110 f561 | grind (instances := 3000) only
  have f2144 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_168))) := by
    clear * - f2125 f77
    first | exact resolve f2125 f77 | exact resolve f77 f2125 | grind (instances := 3000) only
  have f2145 : ((¬ spl0_35) ∨ (¬ spl0_168)) := by
    clear * - f2144
    grind (instances := 3000) only
  have f2183 : ((c = sk6) ∨ (¬ spl0_125)) := by
    clear * - f1019 f97
    first | exact resolve f1019 f97 | exact resolve f97 f1019 | grind (instances := 3000) only
  have f2184 : ((b = sk1) ∨ (¬ spl0_125)) := by
    clear * - f1019 f96
    first | exact resolve f1019 f96 | exact resolve f96 f1019 | grind (instances := 3000) only
  have f2185 : ((a = sk4) ∨ (¬ spl0_125)) := by
    clear * - f1019 f95
    first | exact resolve f1019 f95 | exact resolve f95 f1019 | grind (instances := 3000) only
  have f2194 : ((old sk0 sk0 b) ∨ ((¬ spl0_8) ∨ (¬ spl0_125))) := by
    clear * - f193 f2184
    first | exact superpose f193 f2184 | exact superpose f2184 f193 | grind (instances := 3000) only
  have f2235 : (∀ (X0 : G), (((¬ (old X0 X0 sk7)) ∨ (sk5 = X0)) ∨ (¬ spl0_189))) := by
    clear * - f1305 f81
    first | exact resolve f1305 f81 | exact resolve f81 f1305 | grind (instances := 3000) only
  have f2243 : (∀ (X0 : G), (((¬ (old X0 X0 b)) ∨ (sk5 = X0)) ∨ ((¬ spl0_174) ∨ (¬ spl0_189)))) := by
    clear * - f2235 f1747
    grind (instances := 3000) only
  have f2297 : ((sk0 = sk5) ∨ ((¬ spl0_8) ∨ ((¬ spl0_125) ∨ ((¬ spl0_174) ∨ (¬ spl0_189))))) := by
    clear * - f2243 f2194
    first | exact resolve f2243 f2194 | exact resolve f2194 f2243 | grind (instances := 3000) only
  have f2299 : (False ∨ ((¬ spl0_8) ∨ ((¬ spl0_125) ∨ ((¬ spl0_174) ∨ (¬ spl0_189))))) := by
    clear * - f2297 f146
    first | exact resolve f2297 f146 | exact resolve f146 f2297 | grind (instances := 3000) only
  have f2300 : ((¬ spl0_8) ∨ ((¬ spl0_125) ∨ ((¬ spl0_174) ∨ (¬ spl0_189)))) := by
    clear * - f2299
    grind (instances := 3000) only
  have f2348 : ((old a sk7 sk6) ∨ ((¬ spl0_125) ∨ (¬ spl0_175))) := by
    clear * - f1251 f2185
    first | exact superpose f1251 f2185 | exact superpose f2185 f1251 | grind (instances := 3000) only
  have f2352 : ((old a sk7 c) ∨ ((¬ spl0_125) ∨ (¬ spl0_175))) := by
    clear * - f2348 f2183
    grind (instances := 3000) only
  have f2355 : (False ∨ ((¬ spl0_125) ∨ (¬ spl0_175))) := by
    clear * - f2352 f77
    first | exact resolve f2352 f77 | exact resolve f77 f2352 | grind (instances := 3000) only
  have f2356 : ((¬ spl0_125) ∨ (¬ spl0_175)) := by
    clear * - f2355
    grind (instances := 3000) only
  have f2365 : ((c = b) ∨ ((¬ spl0_174) ∨ (¬ spl0_188))) := by
    clear * - f1335 f1747
    grind (instances := 3000) only
  have f2374 : (False ∨ ((¬ spl0_174) ∨ (¬ spl0_188))) := by
    clear * - f2365 f75
    first | exact resolve f2365 f75 | exact resolve f75 f2365 | grind (instances := 3000) only
  have f2375 : ((¬ spl0_174) ∨ (¬ spl0_188)) := by
    clear * - f2374
    grind (instances := 3000) only
  have f2419 : ((c = sk1) ∨ (¬ spl0_124)) := by
    clear * - f1016 f99
    first | exact resolve f1016 f99 | exact resolve f99 f1016 | grind (instances := 3000) only
  have f2478 : ((sP4 sk4 sk1 c) ∨ ((¬ spl0_121) ∨ (¬ spl0_174))) := by
    clear * - f1007 f1746
    grind (instances := 3000) only
  have f2479 : ((sP4 a sk1 c) ∨ ((¬ spl0_121) ∨ (¬ spl0_174))) := by
    clear * - f2478 f1748
    grind (instances := 3000) only
  have f2480 : ((old c c (sF2 a sk1 c)) ∨ ((¬ spl0_121) ∨ (¬ spl0_174))) := by
    clear * - f2479 f121
    first | exact resolve f2479 f121 | exact resolve f121 f2479 | grind (instances := 3000) only
  have f2489 : (False ∨ ((¬ spl0_121) ∨ (¬ spl0_174))) := by
    clear * - f2480 f79
    first | exact resolve f2480 f79 | exact resolve f79 f2480 | grind (instances := 3000) only
  have f2490 : ((¬ spl0_121) ∨ (¬ spl0_174)) := by
    clear * - f2489
    grind (instances := 3000) only
  have f2532 : ((old sk0 sk0 c) ∨ ((¬ spl0_8) ∨ (¬ spl0_124))) := by
    clear * - f193 f2419
    first | exact superpose f193 f2419 | exact superpose f2419 f193 | grind (instances := 3000) only
  have f2548 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_124))) := by
    clear * - f2532 f77
    first | exact resolve f2532 f77 | exact resolve f77 f2532 | grind (instances := 3000) only
  have f2549 : ((¬ spl0_8) ∨ (¬ spl0_124)) := by
    clear * - f2548
    grind (instances := 3000) only
  have f2552 : ((a = c) ∨ ((¬ spl0_125) ∨ (¬ spl0_172))) := by
    clear * - f1882 f2185
    grind (instances := 3000) only
  have f2557 : (False ∨ ((¬ spl0_125) ∨ (¬ spl0_172))) := by
    clear * - f2552 f74
    first | exact resolve f2552 f74 | exact resolve f74 f2552 | grind (instances := 3000) only
  have f2558 : ((¬ spl0_125) ∨ (¬ spl0_172)) := by
    clear * - f2557
    grind (instances := 3000) only
  have f2562 : ((old a a a) ∨ (¬ spl0_123)) := by
    clear * - f1013 f107
    first | exact resolve f1013 f107 | exact resolve f107 f1013 | grind (instances := 3000) only
  have f2565 : ((c = sk4) ∨ (¬ spl0_123)) := by
    clear * - f1013 f104
    first | exact resolve f1013 f104 | exact resolve f104 f1013 | grind (instances := 3000) only
  have f2610 : ((old sk2 sk2 c) ∨ ((¬ spl0_35) ∨ (¬ spl0_123))) := by
    clear * - f561 f2565
    first | exact superpose f561 f2565 | exact superpose f2565 f561 | grind (instances := 3000) only
  have f2625 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_123))) := by
    clear * - f2610 f77
    first | exact resolve f2610 f77 | exact resolve f77 f2610 | grind (instances := 3000) only
  have f2626 : ((¬ spl0_35) ∨ (¬ spl0_123)) := by
    clear * - f2625
    grind (instances := 3000) only
  have f2633 : ((old b b b) ∨ (¬ spl0_122)) := by
    clear * - f1010 f113
    first | exact resolve f1010 f113 | exact resolve f113 f1010 | grind (instances := 3000) only
  have f2635 : ((c = sk4) ∨ (¬ spl0_122)) := by
    clear * - f1010 f111
    first | exact resolve f1010 f111 | exact resolve f111 f1010 | grind (instances := 3000) only
  have f2662 : ((old sk2 sk2 c) ∨ ((¬ spl0_35) ∨ (¬ spl0_122))) := by
    clear * - f561 f2635
    first | exact superpose f561 f2635 | exact superpose f2635 f561 | grind (instances := 3000) only
  have f2677 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_122))) := by
    clear * - f2662 f77
    first | exact resolve f2662 f77 | exact resolve f77 f2662 | grind (instances := 3000) only
  have f2678 : ((¬ spl0_35) ∨ (¬ spl0_122)) := by
    clear * - f2677
    grind (instances := 3000) only
  have f2684 : ((c = sk4) ∨ (¬ spl0_121)) := by
    clear * - f1007 f117
    first | exact resolve f1007 f117 | exact resolve f117 f1007 | grind (instances := 3000) only
  have f2691 : ((old sk2 sk2 c) ∨ ((¬ spl0_35) ∨ (¬ spl0_121))) := by
    clear * - f561 f2684
    first | exact superpose f561 f2684 | exact superpose f2684 f561 | grind (instances := 3000) only
  have f2705 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_121))) := by
    clear * - f2691 f77
    first | exact resolve f2691 f77 | exact resolve f77 f2691 | grind (instances := 3000) only
  have f2706 : ((¬ spl0_35) ∨ (¬ spl0_121)) := by
    clear * - f2705
    grind (instances := 3000) only
  have f2712 : ((c = sk1) ∨ (¬ spl0_120)) := by
    clear * - f1004 f123
    first | exact resolve f1004 f123 | exact resolve f123 f1004 | grind (instances := 3000) only
  have f2734 : ((old sk0 sk0 c) ∨ ((¬ spl0_8) ∨ (¬ spl0_120))) := by
    clear * - f193 f2712
    first | exact superpose f193 f2712 | exact superpose f2712 f193 | grind (instances := 3000) only
  have f2752 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_120))) := by
    clear * - f2734 f77
    first | exact resolve f2734 f77 | exact resolve f77 f2734 | grind (instances := 3000) only
  have f2753 : ((¬ spl0_8) ∨ (¬ spl0_120)) := by
    clear * - f2752
    grind (instances := 3000) only
  have f2757 : ((c = sk1) ∨ (¬ spl0_119)) := by
    clear * - f1001 f132
    first | exact resolve f1001 f132 | exact resolve f132 f1001 | grind (instances := 3000) only
  have f2792 : ((c = sk3) ∨ (¬ spl0_81)) := by
    clear * - f803 f97
    first | exact resolve f803 f97 | exact resolve f97 f803 | grind (instances := 3000) only
  have f2793 : ((b = sk5) ∨ (¬ spl0_81)) := by
    clear * - f803 f96
    first | exact resolve f803 f96 | exact resolve f96 f803 | grind (instances := 3000) only
  have f2797 : ((old sk2 sk0 c) ∨ ((¬ spl0_25) ∨ (¬ spl0_81))) := by
    clear * - f511 f2792
    first | exact superpose f511 f2792 | exact superpose f2792 f511 | grind (instances := 3000) only
  have f2806 : (False ∨ ((¬ spl0_25) ∨ (¬ spl0_81))) := by
    clear * - f2797 f77
    first | exact resolve f2797 f77 | exact resolve f77 f2797 | grind (instances := 3000) only
  have f2807 : ((¬ spl0_25) ∨ (¬ spl0_81)) := by
    clear * - f2806
    grind (instances := 3000) only
  have f2815 : ((c = sk5) ∨ (¬ spl0_80)) := by
    clear * - f800 f99
    first | exact resolve f800 f99 | exact resolve f99 f800 | grind (instances := 3000) only
  have f2862 : ((old c c sk7) ∨ ((¬ spl0_80) ∨ (¬ spl0_189))) := by
    clear * - f1305 f2815
    first | exact superpose f1305 f2815 | exact superpose f2815 f1305 | grind (instances := 3000) only
  have f2863 : (False ∨ ((¬ spl0_80) ∨ (¬ spl0_189))) := by
    clear * - f2862 f79
    first | exact resolve f2862 f79 | exact resolve f79 f2862 | grind (instances := 3000) only
  have f2864 : ((¬ spl0_80) ∨ (¬ spl0_189)) := by
    clear * - f2863
    grind (instances := 3000) only
  have f2905 : ((old a a (sF6 c c b)) ∨ (¬ spl0_182)) := by
    clear * - f1568 f134
    first | exact resolve f1568 f134 | exact resolve f134 f1568 | grind (instances := 3000) only
  have f2911 : ((old b b (sF6 c c b)) ∨ (¬ spl0_182)) := by
    clear * - f2905 f1530
    grind (instances := 3000) only
  have f2912 : (False ∨ (¬ spl0_182)) := by
    clear * - f2911 f1537
    first | exact resolve f2911 f1537 | exact resolve f1537 f2911 | grind (instances := 3000) only
  have f2913 : (¬ spl0_182) := by
    clear * - f2912
    grind (instances := 3000) only
  have f3003 : ((old c c sk1) ∨ ((¬ spl0_8) ∨ (¬ spl0_18))) := by
    clear * - f193 f1583
    first | exact superpose f193 f1583 | exact superpose f1583 f193 | grind (instances := 3000) only
  have f3029 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_18))) := by
    clear * - f3003 f79
    first | exact resolve f3003 f79 | exact resolve f79 f3003 | grind (instances := 3000) only
  have f3030 : ((¬ spl0_8) ∨ (¬ spl0_18)) := by
    clear * - f3029
    grind (instances := 3000) only
  have f3048 : ((a = sk3) ∨ (¬ spl0_79)) := by
    clear * - f797 f106
    first | exact resolve f797 f106 | exact resolve f106 f797 | grind (instances := 3000) only
  have f3050 : ((c = sk2) ∨ (¬ spl0_79)) := by
    clear * - f797 f104
    first | exact resolve f797 f104 | exact resolve f104 f797 | grind (instances := 3000) only
  have f3053 : ((old sk2 sk0 a) ∨ ((¬ spl0_25) ∨ (¬ spl0_79))) := by
    clear * - f511 f3048
    first | exact superpose f511 f3048 | exact superpose f3048 f511 | grind (instances := 3000) only
  have f3066 : ((old c sk0 a) ∨ ((¬ spl0_25) ∨ (¬ spl0_79))) := by
    clear * - f3053 f3050
    grind (instances := 3000) only
  have f3070 : (False ∨ ((¬ spl0_25) ∨ (¬ spl0_79))) := by
    clear * - f3066 f79
    first | exact resolve f3066 f79 | exact resolve f79 f3066 | grind (instances := 3000) only
  have f3071 : ((¬ spl0_25) ∨ (¬ spl0_79)) := by
    clear * - f3070
    grind (instances := 3000) only
  have f3077 : ((c = sk2) ∨ (¬ spl0_78)) := by
    clear * - f794 f111
    first | exact resolve f794 f111 | exact resolve f111 f794 | grind (instances := 3000) only
  have f3098 : ((old c sk0 sk3) ∨ ((¬ spl0_25) ∨ (¬ spl0_78))) := by
    clear * - f511 f3077
    first | exact superpose f511 f3077 | exact superpose f3077 f511 | grind (instances := 3000) only
  have f3099 : ((old c c sk4) ∨ ((¬ spl0_35) ∨ (¬ spl0_78))) := by
    clear * - f561 f3077
    first | exact superpose f561 f3077 | exact superpose f3077 f561 | grind (instances := 3000) only
  have f3121 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_78))) := by
    clear * - f3099 f79
    first | exact resolve f3099 f79 | exact resolve f79 f3099 | grind (instances := 3000) only
  have f3122 : ((¬ spl0_35) ∨ (¬ spl0_78)) := by
    clear * - f3121
    grind (instances := 3000) only
  have f3123 : (False ∨ ((¬ spl0_25) ∨ (¬ spl0_78))) := by
    clear * - f3098 f79
    first | exact resolve f3098 f79 | exact resolve f79 f3098 | grind (instances := 3000) only
  have f3124 : ((¬ spl0_25) ∨ (¬ spl0_78)) := by
    clear * - f3123
    grind (instances := 3000) only
  have f3130 : ((c = sk2) ∨ (¬ spl0_77)) := by
    clear * - f791 f117
    first | exact resolve f791 f117 | exact resolve f117 f791 | grind (instances := 3000) only
  have f3137 : ((old c sk0 sk3) ∨ ((¬ spl0_25) ∨ (¬ spl0_77))) := by
    clear * - f511 f3130
    first | exact superpose f511 f3130 | exact superpose f3130 f511 | grind (instances := 3000) only
  have f3138 : ((old c c sk4) ∨ ((¬ spl0_35) ∨ (¬ spl0_77))) := by
    clear * - f561 f3130
    first | exact superpose f561 f3130 | exact superpose f3130 f561 | grind (instances := 3000) only
  have f3159 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_77))) := by
    clear * - f3138 f79
    first | exact resolve f3138 f79 | exact resolve f79 f3138 | grind (instances := 3000) only
  have f3160 : ((¬ spl0_35) ∨ (¬ spl0_77)) := by
    clear * - f3159
    grind (instances := 3000) only
  have f3161 : (False ∨ ((¬ spl0_25) ∨ (¬ spl0_77))) := by
    clear * - f3137 f79
    first | exact resolve f3137 f79 | exact resolve f79 f3137 | grind (instances := 3000) only
  have f3162 : ((¬ spl0_25) ∨ (¬ spl0_77)) := by
    clear * - f3161
    grind (instances := 3000) only
  have f3168 : ((c = sk5) ∨ (¬ spl0_76)) := by
    clear * - f788 f123
    first | exact resolve f788 f123 | exact resolve f123 f788 | grind (instances := 3000) only
  have f3219 : ((old c c sk7) ∨ ((¬ spl0_76) ∨ (¬ spl0_189))) := by
    clear * - f1305 f3168
    first | exact superpose f1305 f3168 | exact superpose f3168 f1305 | grind (instances := 3000) only
  have f3220 : (False ∨ ((¬ spl0_76) ∨ (¬ spl0_189))) := by
    clear * - f3219 f79
    first | exact resolve f3219 f79 | exact resolve f79 f3219 | grind (instances := 3000) only
  have f3221 : ((¬ spl0_76) ∨ (¬ spl0_189)) := by
    clear * - f3220
    grind (instances := 3000) only
  have f3231 : ((c = sk2) ∨ (¬ spl0_75)) := by
    clear * - f785 f131
    first | exact resolve f785 f131 | exact resolve f131 f785 | grind (instances := 3000) only
  have f3246 : ((old c sk0 sk3) ∨ ((¬ spl0_25) ∨ (¬ spl0_75))) := by
    clear * - f511 f3231
    first | exact superpose f511 f3231 | exact superpose f3231 f511 | grind (instances := 3000) only
  have f3247 : ((old c c sk4) ∨ ((¬ spl0_35) ∨ (¬ spl0_75))) := by
    clear * - f561 f3231
    first | exact superpose f561 f3231 | exact superpose f3231 f561 | grind (instances := 3000) only
  have f3269 : (False ∨ ((¬ spl0_35) ∨ (¬ spl0_75))) := by
    clear * - f3247 f79
    first | exact resolve f3247 f79 | exact resolve f79 f3247 | grind (instances := 3000) only
  have f3270 : ((¬ spl0_35) ∨ (¬ spl0_75)) := by
    clear * - f3269
    grind (instances := 3000) only
  have f3271 : (False ∨ ((¬ spl0_25) ∨ (¬ spl0_75))) := by
    clear * - f3246 f79
    first | exact resolve f3246 f79 | exact resolve f79 f3246 | grind (instances := 3000) only
  have f3272 : ((¬ spl0_25) ∨ (¬ spl0_75)) := by
    clear * - f3271
    grind (instances := 3000) only
  have f3341 : ((c = sk4) ∨ (¬ spl0_34)) := by
    clear * - f558 f97
    first | exact resolve f558 f97 | exact resolve f97 f558 | grind (instances := 3000) only
  have f3342 : ((b = sk2) ∨ (¬ spl0_34)) := by
    clear * - f558 f96
    first | exact resolve f558 f96 | exact resolve f96 f558 | grind (instances := 3000) only
  have f3343 : ((a = sk2) ∨ (¬ spl0_34)) := by
    clear * - f558 f95
    first | exact resolve f558 f95 | exact resolve f95 f558 | grind (instances := 3000) only
  have f3410 : ((a = b) ∨ (¬ spl0_34)) := by
    clear * - f3342 f3343
    first | exact superpose f3342 f3343 | exact superpose f3343 f3342 | grind (instances := 3000) only
  have f3488 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_34))) := by
    clear * - f76 f3410
    first | exact superpose f76 f3410 | exact superpose f3410 f76 | grind (instances := 3000) only
  have f3508 : ((old c sk1 sk6) ∨ ((¬ spl0_34) ∨ (¬ spl0_126))) := by
    clear * - f1022 f3341
    first | exact superpose f1022 f3341 | exact superpose f3341 f1022 | grind (instances := 3000) only
  have f3509 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_126))) := by
    clear * - f3508 f79
    first | exact resolve f3508 f79 | exact resolve f79 f3508 | grind (instances := 3000) only
  have f3510 : ((¬ spl0_34) ∨ (¬ spl0_126)) := by
    clear * - f3509
    grind (instances := 3000) only
  have f3537 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_171))) := by
    clear * - f1901 f3488
    first | exact resolve f1901 f3488 | exact resolve f3488 f1901 | grind (instances := 3000) only
  have f3538 : ((¬ spl0_34) ∨ (¬ spl0_171)) := by
    clear * - f3537
    grind (instances := 3000) only
  have f3581 : ((old b b b) ∨ ((¬ spl0_34) ∨ (¬ spl0_123))) := by
    clear * - f2562 f3410
    grind (instances := 3000) only
  have f3615 : ((old c sk7 sk6) ∨ ((¬ spl0_34) ∨ (¬ spl0_175))) := by
    clear * - f1251 f3341
    grind (instances := 3000) only
  have f3618 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_123))) := by
    clear * - f3581 f3488
    first | exact resolve f3581 f3488 | exact resolve f3488 f3581 | grind (instances := 3000) only
  have f3619 : ((¬ spl0_34) ∨ (¬ spl0_123)) := by
    clear * - f3618
    grind (instances := 3000) only
  have f3632 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_175))) := by
    clear * - f3615 f79
    first | exact resolve f3615 f79 | exact resolve f79 f3615 | grind (instances := 3000) only
  have f3633 : ((¬ spl0_34) ∨ (¬ spl0_175)) := by
    clear * - f3632
    grind (instances := 3000) only
  have f3642 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_122))) := by
    clear * - f2633 f3488
    first | exact resolve f2633 f3488 | exact resolve f3488 f2633 | grind (instances := 3000) only
  have f3643 : ((¬ spl0_34) ∨ (¬ spl0_122)) := by
    clear * - f3642
    grind (instances := 3000) only
  have f3662 : ((old b b b) ∨ ((¬ spl0_34) ∨ (¬ spl0_172))) := by
    clear * - f1879 f3410
    grind (instances := 3000) only
  have f3683 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_172))) := by
    clear * - f3662 f3488
    first | exact resolve f3662 f3488 | exact resolve f3488 f3662 | grind (instances := 3000) only
  have f3684 : ((¬ spl0_34) ∨ (¬ spl0_172)) := by
    clear * - f3683
    grind (instances := 3000) only
  have f3711 : ((old b b (sF1 c sk7 sk6)) ∨ (¬ spl0_170)) := by
    clear * - f1959 f118
    first | exact resolve f1959 f118 | exact resolve f118 f1959 | grind (instances := 3000) only
  have f3713 : (False ∨ ((¬ spl0_34) ∨ (¬ spl0_170))) := by
    clear * - f3711 f3488
    first | exact resolve f3711 f3488 | exact resolve f3488 f3711 | grind (instances := 3000) only
  have f3714 : ((¬ spl0_34) ∨ (¬ spl0_170)) := by
    clear * - f3713
    grind (instances := 3000) only
  have f3723 : ((old sk5 sk5 c) ∨ ((¬ spl0_168) ∨ (¬ spl0_189))) := by
    clear * - f1305 f2111
    first | exact superpose f1305 f2111 | exact superpose f2111 f1305 | grind (instances := 3000) only
  have f3724 : (False ∨ ((¬ spl0_168) ∨ (¬ spl0_189))) := by
    clear * - f3723 f77
    first | exact resolve f3723 f77 | exact resolve f77 f3723 | grind (instances := 3000) only
  have f3725 : ((¬ spl0_168) ∨ (¬ spl0_189)) := by
    clear * - f3724
    grind (instances := 3000) only
  have f3734 : ((old a b sk3) ∨ ((¬ spl0_34) ∨ ((¬ spl0_82) ∨ (¬ spl0_188)))) := by
    clear * - f1816 f3343
    grind (instances := 3000) only
  have f3755 : (False ∨ ((¬ spl0_34) ∨ ((¬ spl0_82) ∨ (¬ spl0_188)))) := by
    clear * - f3734 f76
    first | exact resolve f3734 f76 | exact resolve f76 f3734 | grind (instances := 3000) only
  have f3756 : ((¬ spl0_34) ∨ ((¬ spl0_82) ∨ (¬ spl0_188))) := by
    clear * - f3755
    grind (instances := 3000) only
  have f3766 : ((c = b) ∨ ((¬ spl0_80) ∨ (¬ spl0_188))) := by
    clear * - f2815 f1336
    grind (instances := 3000) only
  have f3774 : (False ∨ ((¬ spl0_80) ∨ (¬ spl0_188))) := by
    clear * - f3766 f75
    first | exact resolve f3766 f75 | exact resolve f75 f3766 | grind (instances := 3000) only
  have f3775 : ((¬ spl0_80) ∨ (¬ spl0_188)) := by
    clear * - f3774
    grind (instances := 3000) only
  have f3786 : ((c = b) ∨ ((¬ spl0_76) ∨ (¬ spl0_188))) := by
    clear * - f3168 f1336
    grind (instances := 3000) only
  have f3793 : (False ∨ ((¬ spl0_76) ∨ (¬ spl0_188))) := by
    clear * - f3786 f75
    first | exact resolve f3786 f75 | exact resolve f75 f3786 | grind (instances := 3000) only
  have f3794 : ((¬ spl0_76) ∨ (¬ spl0_188)) := by
    clear * - f3793
    grind (instances := 3000) only
  have f3869 : ((old (sF0 sk2 sk2 sk4) sk2 a) ∨ (¬ spl0_33)) := by
    clear * - f555 f102
    first | exact resolve f555 f102 | exact resolve f102 f555 | grind (instances := 3000) only
  have f3872 : ((c = sk2) ∨ (¬ spl0_33)) := by
    clear * - f555 f99
    first | exact resolve f555 f99 | exact resolve f99 f555 | grind (instances := 3000) only
  have f3875 : ((old (sF0 c c sk4) c a) ∨ (¬ spl0_33)) := by
    clear * - f3869 f3872
    grind (instances := 3000) only
  have f3877 : (False ∨ (¬ spl0_33)) := by
    clear * - f3875 f78
    first | exact resolve f3875 f78 | exact resolve f78 f3875 | grind (instances := 3000) only
  have f3878 : (¬ spl0_33) := by
    clear * - f3877
    grind (instances := 3000) only
  have f3962 : ((old c c sk1) ∨ ((¬ spl0_8) ∨ (¬ spl0_19))) := by
    clear * - f193 f1603
    first | exact superpose f193 f1603 | exact superpose f1603 f193 | grind (instances := 3000) only
  have f3987 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_19))) := by
    clear * - f3962 f79
    first | exact resolve f3962 f79 | exact resolve f79 f3962 | grind (instances := 3000) only
  have f3988 : ((¬ spl0_8) ∨ (¬ spl0_19)) := by
    clear * - f3987
    grind (instances := 3000) only
  have f4041 : ((old sk0 sk0 c) ∨ ((¬ spl0_8) ∨ (¬ spl0_119))) := by
    clear * - f193 f2757
    first | exact superpose f193 f2757 | exact superpose f2757 f193 | grind (instances := 3000) only
  have f4056 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_119))) := by
    clear * - f4041 f77
    first | exact resolve f4041 f77 | exact resolve f77 f4041 | grind (instances := 3000) only
  have f4057 : ((¬ spl0_8) ∨ (¬ spl0_119)) := by
    clear * - f4056
    grind (instances := 3000) only
  have f4216 : ((a = b) ∨ (¬ spl0_28)) := by
    clear * - f540 f130
    first | exact resolve f540 f130 | exact resolve f130 f540 | grind (instances := 3000) only
  have f4217 : ((c = sk2) ∨ (¬ spl0_28)) := by
    clear * - f540 f131
    first | exact resolve f540 f131 | exact resolve f131 f540 | grind (instances := 3000) only
  have f4219 : ((b = sk4) ∨ (¬ spl0_28)) := by
    clear * - f540 f133
    first | exact resolve f540 f133 | exact resolve f133 f540 | grind (instances := 3000) only
  have f4239 : ((old sk6 sk6 (sF2 sk4 sk1 sk6)) ∨ (¬ spl0_121)) := by
    clear * - f1007 f121
    first | exact resolve f1007 f121 | exact resolve f121 f1007 | grind (instances := 3000) only
  have f4250 : ((old b b (sF2 sk4 sk1 b)) ∨ ((¬ spl0_121) ∨ (¬ spl0_168))) := by
    clear * - f4239 f2112
    grind (instances := 3000) only
  have f4252 : (False ∨ ((¬ spl0_121) ∨ (¬ spl0_168))) := by
    clear * - f4250 f2116
    first | exact resolve f4250 f2116 | exact resolve f2116 f4250 | grind (instances := 3000) only
  have f4253 : ((¬ spl0_121) ∨ (¬ spl0_168)) := by
    clear * - f4252
    grind (instances := 3000) only
  have f4382 : ((c = b) ∨ ((¬ spl0_125) ∨ (¬ spl0_168))) := by
    clear * - f2183 f2112
    grind (instances := 3000) only
  have f4422 : (False ∨ ((¬ spl0_125) ∨ (¬ spl0_168))) := by
    clear * - f4382 f75
    first | exact resolve f4382 f75 | exact resolve f75 f4382 | grind (instances := 3000) only
  have f4423 : ((¬ spl0_125) ∨ (¬ spl0_168)) := by
    clear * - f4422
    grind (instances := 3000) only
  have f4796 : ((a = sk2) ∨ (¬ spl0_32)) := by
    clear * - f552 f105
    first | exact resolve f552 f105 | exact resolve f105 f552 | grind (instances := 3000) only
  have f4797 : ((c = sk2) ∨ (¬ spl0_32)) := by
    clear * - f552 f104
    first | exact resolve f552 f104 | exact resolve f104 f552 | grind (instances := 3000) only
  have f4893 : (∀ (X0 : G), ((¬ (old b b X0)) ∨ (¬ spl0_28))) := by
    clear * - f76 f4216
    first | exact superpose f76 f4216 | exact superpose f4216 f76 | grind (instances := 3000) only
  have f4904 : ((old c sk0 sk3) ∨ ((¬ spl0_25) ∨ (¬ spl0_28))) := by
    clear * - f511 f4217
    first | exact superpose f511 f4217 | exact superpose f4217 f511 | grind (instances := 3000) only
  have f4908 : (False ∨ ((¬ spl0_25) ∨ (¬ spl0_28))) := by
    clear * - f4904 f79
    first | exact resolve f4904 f79 | exact resolve f79 f4904 | grind (instances := 3000) only
  have f4909 : ((¬ spl0_25) ∨ (¬ spl0_28)) := by
    clear * - f4908
    grind (instances := 3000) only
  have f4911 : ((a = c) ∨ (¬ spl0_32)) := by
    clear * - f4797 f4796
    grind (instances := 3000) only
  have f4937 : (False ∨ (¬ spl0_32)) := by
    clear * - f4911 f74
    first | exact resolve f4911 f74 | exact resolve f74 f4911 | grind (instances := 3000) only
  have f4938 : (¬ spl0_32) := by
    clear * - f4937
    grind (instances := 3000) only
  have f5011 : ((a = sk2) ∨ (¬ spl0_31)) := by
    clear * - f549 f112
    first | exact resolve f549 f112 | exact resolve f112 f549 | grind (instances := 3000) only
  have f5012 : ((c = sk2) ∨ (¬ spl0_31)) := by
    clear * - f549 f111
    first | exact resolve f549 f111 | exact resolve f111 f549 | grind (instances := 3000) only
  have f5074 : ((a = c) ∨ (¬ spl0_31)) := by
    clear * - f5012 f5011
    grind (instances := 3000) only
  have f5089 : (False ∨ (¬ spl0_31)) := by
    clear * - f5074 f74
    first | exact resolve f5074 f74 | exact resolve f74 f5074 | grind (instances := 3000) only
  have f5090 : (¬ spl0_31) := by
    clear * - f5089
    grind (instances := 3000) only
  have f5116 : ((old b sk4 sk2) ∨ (¬ spl0_30)) := by
    clear * - f546 f119
    first | exact resolve f546 f119 | exact resolve f119 f546 | grind (instances := 3000) only
  have f5118 : ((c = sk2) ∨ (¬ spl0_30)) := by
    clear * - f546 f117
    first | exact resolve f546 f117 | exact resolve f117 f546 | grind (instances := 3000) only
  have f5121 : ((old b sk4 c) ∨ (¬ spl0_30)) := by
    clear * - f5116 f5118
    grind (instances := 3000) only
  have f5125 : (False ∨ (¬ spl0_30)) := by
    clear * - f5121 f77
    first | exact resolve f5121 f77 | exact resolve f77 f5121 | grind (instances := 3000) only
  have f5126 : (¬ spl0_30) := by
    clear * - f5125
    grind (instances := 3000) only
  have f5143 : ((a = c) ∨ ((¬ spl0_24) ∨ (¬ spl0_28))) := by
    clear * - f4217 f1662
    grind (instances := 3000) only
  have f5209 : (False ∨ ((¬ spl0_24) ∨ (¬ spl0_28))) := by
    clear * - f5143 f74
    first | exact resolve f5143 f74 | exact resolve f74 f5143 | grind (instances := 3000) only
  have f5210 : ((¬ spl0_24) ∨ (¬ spl0_28)) := by
    clear * - f5209
    grind (instances := 3000) only
  have f5292 : ((old sk2 sk5 c) ∨ ((¬ spl0_24) ∨ (¬ spl0_82))) := by
    clear * - f806 f1660
    grind (instances := 3000) only
  have f5331 : (False ∨ ((¬ spl0_24) ∨ (¬ spl0_82))) := by
    clear * - f5292 f77
    first | exact resolve f5292 f77 | exact resolve f77 f5292 | grind (instances := 3000) only
  have f5332 : ((¬ spl0_24) ∨ (¬ spl0_82)) := by
    clear * - f5331
    grind (instances := 3000) only
  have f5387 : ((old (sF3 sk2 sk2 sk4) a sk2) ∨ (¬ spl0_29)) := by
    clear * - f543 f125
    first | exact resolve f543 f125 | exact resolve f125 f543 | grind (instances := 3000) only
  have f5389 : ((c = sk2) ∨ (¬ spl0_29)) := by
    clear * - f543 f123
    first | exact resolve f543 f123 | exact resolve f123 f543 | grind (instances := 3000) only
  have f5390 : ((old (sF3 c c sk4) a c) ∨ (¬ spl0_29)) := by
    clear * - f5387 f5389
    grind (instances := 3000) only
  have f5394 : (False ∨ (¬ spl0_29)) := by
    clear * - f5390 f77
    first | exact resolve f5390 f77 | exact resolve f77 f5390 | grind (instances := 3000) only
  have f5395 : (¬ spl0_29) := by
    clear * - f5394
    grind (instances := 3000) only
  have f5472 : ((old b b b) ∨ ((¬ spl0_22) ∨ (¬ spl0_28))) := by
    clear * - f1636 f4216
    grind (instances := 3000) only
  have f5511 : (False ∨ ((¬ spl0_22) ∨ (¬ spl0_28))) := by
    clear * - f5472 f4893
    first | exact resolve f5472 f4893 | exact resolve f4893 f5472 | grind (instances := 3000) only
  have f5512 : ((¬ spl0_22) ∨ (¬ spl0_28)) := by
    clear * - f5511
    grind (instances := 3000) only
  have f5579 : ((old c c sk1) ∨ ((¬ spl0_8) ∨ (¬ spl0_23))) := by
    clear * - f193 f1653
    first | exact superpose f193 f1653 | exact superpose f1653 f193 | grind (instances := 3000) only
  have f5584 : (False ∨ ((¬ spl0_8) ∨ (¬ spl0_23))) := by
    clear * - f5579 f79
    first | exact resolve f5579 f79 | exact resolve f79 f5579 | grind (instances := 3000) only
  have f5585 : ((¬ spl0_8) ∨ (¬ spl0_23)) := by
    clear * - f5584
    grind (instances := 3000) only
  have f5698 : ((old c c sk4) ∨ ((¬ spl0_20) ∨ (¬ spl0_35))) := by
    clear * - f561 f1619
    first | exact superpose f561 f1619 | exact superpose f1619 f561 | grind (instances := 3000) only
  have f5699 : (False ∨ ((¬ spl0_20) ∨ (¬ spl0_35))) := by
    clear * - f5698 f79
    first | exact resolve f5698 f79 | exact resolve f79 f5698 | grind (instances := 3000) only
  have f5700 : ((¬ spl0_20) ∨ (¬ spl0_35)) := by
    clear * - f5699
    grind (instances := 3000) only
  have f5709 : ((sP6 c c sk4) ∨ ((¬ spl0_20) ∨ (¬ spl0_28))) := by
    clear * - f540 f1619
    grind (instances := 3000) only
  have f5712 : ((sP6 c c b) ∨ ((¬ spl0_20) ∨ (¬ spl0_28))) := by
    clear * - f5709 f4219
    grind (instances := 3000) only
  have f5758 : ((old a a (sF6 c c b)) ∨ ((¬ spl0_20) ∨ (¬ spl0_28))) := by
    clear * - f5712 f134
    first | exact resolve f5712 f134 | exact resolve f134 f5712 | grind (instances := 3000) only
  have f5764 : ((old b b (sF6 c c b)) ∨ ((¬ spl0_20) ∨ (¬ spl0_28))) := by
    clear * - f5758 f4216
    grind (instances := 3000) only
  have f5765 : (False ∨ ((¬ spl0_20) ∨ (¬ spl0_28))) := by
    clear * - f5764 f4893
    first | exact resolve f5764 f4893 | exact resolve f4893 f5764 | grind (instances := 3000) only
  have f5766 : ((¬ spl0_20) ∨ (¬ spl0_28)) := by
    clear * - f5765
    grind (instances := 3000) only
  have f5768 : (False ∨ ((¬ spl0_21) ∨ (¬ spl0_28))) := by
    clear * - f1627 f4893
    first | exact resolve f1627 f4893 | exact resolve f4893 f1627 | grind (instances := 3000) only
  have f5769 : ((¬ spl0_21) ∨ (¬ spl0_28)) := by
    clear * - f5768
    grind (instances := 3000) only
  have f5790 : ((old c c sk4) ∨ ((¬ spl0_22) ∨ (¬ spl0_35))) := by
    clear * - f561 f1639
    grind (instances := 3000) only
  have f5841 : (False ∨ ((¬ spl0_22) ∨ (¬ spl0_35))) := by
    clear * - f5790 f79
    first | exact resolve f5790 f79 | exact resolve f79 f5790 | grind (instances := 3000) only
  have f5842 : ((¬ spl0_22) ∨ (¬ spl0_35)) := by
    clear * - f5841
    grind (instances := 3000) only
  have f5881 : ((old c c sk4) ∨ ((¬ spl0_21) ∨ (¬ spl0_35))) := by
    clear * - f561 f1629
    grind (instances := 3000) only
  have f5931 : (False ∨ ((¬ spl0_21) ∨ (¬ spl0_35))) := by
    clear * - f5881 f79
    first | exact resolve f5881 f79 | exact resolve f79 f5881 | grind (instances := 3000) only
  have f5932 : ((¬ spl0_21) ∨ (¬ spl0_35)) := by
    clear * - f5931
    grind (instances := 3000) only
  have f6088 : ((b ≠ sk0) ∨ (¬ spl0_81)) := by
    clear * - f146 f2793
    first | exact superpose f146 f2793 | exact superpose f2793 f146 | grind (instances := 3000) only
  have f6092 : (False ∨ ((¬ spl0_24) ∨ (¬ spl0_81))) := by
    clear * - f6088 f1661
    first | exact resolve f6088 f1661 | exact resolve f1661 f6088 | grind (instances := 3000) only
  have f6093 : ((¬ spl0_24) ∨ (¬ spl0_81)) := by
    clear * - f6092
    grind (instances := 3000) only
  have f6099 : ((a = c) ∨ ((¬ spl0_24) ∨ (¬ spl0_79))) := by
    clear * - f3050 f1662
    grind (instances := 3000) only
  have f6118 : (False ∨ ((¬ spl0_24) ∨ (¬ spl0_79))) := by
    clear * - f6099 f74
    first | exact resolve f6099 f74 | exact resolve f74 f6099 | grind (instances := 3000) only
  have f6119 : ((¬ spl0_24) ∨ (¬ spl0_79)) := by
    clear * - f6118
    grind (instances := 3000) only
  have s1 : (spl0_1 ∨ (spl0_2 ∨ (spl0_3 ∨ (spl0_4 ∨ (spl0_5 ∨ (spl0_6 ∨ (spl0_7 ∨ spl0_8))))))) := by
    clear * - f194
    grind (splits := 100) only
  have s3 : (¬ spl0_1) := by
    clear * - f235
    grind (splits := 100) only
  have s4 : (¬ spl0_2) := by
    clear * - f247
    grind (splits := 100) only
  have s5 : (¬ spl0_3) := by
    clear * - f261
    grind (splits := 100) only
  have s7 : (¬ spl0_4) := by
    clear * - f278
    grind (splits := 100) only
  have s9 : (¬ spl0_5) := by
    clear * - f305
    grind (splits := 100) only
  have s10 : (¬ spl0_6) := by
    clear * - f314
    grind (splits := 100) only
  have s11 : ((¬ spl0_7) ∨ (spl0_9 ∨ (spl0_10 ∨ (spl0_11 ∨ (spl0_12 ∨ (spl0_13 ∨ (spl0_14 ∨ spl0_15))))))) := by
    clear * - f385
    grind (splits := 100) only
  have s13 : ((¬ spl0_7) ∨ (¬ spl0_9)) := by
    clear * - f399
    grind (splits := 100) only
  have s14 : (¬ spl0_15) := by
    clear * - f406
    grind (splits := 100) only
  have s16 : ((¬ spl0_7) ∨ (¬ spl0_10)) := by
    clear * - f421
    grind (splits := 100) only
  have s17 : ((¬ spl0_7) ∨ (¬ spl0_14)) := by
    clear * - f427
    grind (splits := 100) only
  have s19 : (¬ spl0_11) := by
    clear * - f438
    grind (splits := 100) only
  have s20 : (¬ spl0_12) := by
    clear * - f448
    grind (splits := 100) only
  have s22 : (¬ spl0_13) := by
    clear * - f459
    grind (splits := 100) only
  have s27 : (spl0_18 ∨ (spl0_19 ∨ (spl0_20 ∨ (spl0_21 ∨ (spl0_22 ∨ (spl0_23 ∨ (spl0_24 ∨ spl0_25))))))) := by
    clear * - f512
    grind (splits := 100) only
  have s29 : (spl0_28 ∨ (spl0_29 ∨ (spl0_30 ∨ (spl0_31 ∨ (spl0_32 ∨ (spl0_33 ∨ (spl0_34 ∨ spl0_35))))))) := by
    clear * - f562
    grind (splits := 100) only
  have s51 : (spl0_75 ∨ (spl0_76 ∨ (spl0_77 ∨ (spl0_78 ∨ (spl0_79 ∨ (spl0_80 ∨ (spl0_81 ∨ spl0_82))))))) := by
    clear * - f807
    grind (splits := 100) only
  have s85 : (spl0_119 ∨ (spl0_120 ∨ (spl0_121 ∨ (spl0_122 ∨ (spl0_123 ∨ (spl0_124 ∨ (spl0_125 ∨ spl0_126))))))) := by
    clear * - f1023
    grind (splits := 100) only
  have s115 : (spl0_168 ∨ (spl0_169 ∨ (spl0_170 ∨ (spl0_171 ∨ (spl0_172 ∨ (spl0_173 ∨ (spl0_174 ∨ spl0_175))))))) := by
    clear * - f1252
    grind (splits := 100) only
  have s119 : (spl0_182 ∨ (spl0_183 ∨ (spl0_184 ∨ (spl0_185 ∨ (spl0_186 ∨ (spl0_187 ∨ (spl0_188 ∨ spl0_189))))))) := by
    clear * - f1306
    grind (splits := 100) only
  have s120 : ((¬ spl0_8) ∨ ((¬ spl0_25) ∨ ((¬ spl0_35) ∨ ((¬ spl0_82) ∨ ((¬ spl0_126) ∨ ((¬ spl0_175) ∨ (¬ spl0_189))))))) := by
    clear * - f1334
    grind (splits := 100) only
  have s121 : ((¬ spl0_175) ∨ (¬ spl0_188)) := by
    clear * - f1350
    grind (splits := 100) only
  have s122 : (¬ spl0_187) := by
    clear * - f1360
    grind (splits := 100) only
  have s125 : (¬ spl0_186) := by
    clear * - f1440
    grind (splits := 100) only
  have s128 : (¬ spl0_185) := by
    clear * - f1503
    grind (splits := 100) only
  have s129 : (¬ spl0_184) := by
    clear * - f1514
    grind (splits := 100) only
  have s130 : (¬ spl0_183) := by
    clear * - f1526
    grind (splits := 100) only
  have s146 : ((¬ spl0_126) ∨ (¬ spl0_174)) := by
    clear * - f1759
    grind (splits := 100) only
  have s147 : ((¬ spl0_173) ∨ (¬ spl0_189)) := by
    clear * - f1798
    grind (splits := 100) only
  have s149 : ((¬ spl0_173) ∨ (¬ spl0_188)) := by
    clear * - f1876
    grind (splits := 100) only
  have s150 : ((¬ spl0_126) ∨ (¬ spl0_172)) := by
    clear * - f1897
    grind (splits := 100) only
  have s152 : ((¬ spl0_35) ∨ (¬ spl0_171)) := by
    clear * - f1933
    grind (splits := 100) only
  have s154 : ((¬ spl0_35) ∨ (¬ spl0_170)) := by
    clear * - f1965
    grind (splits := 100) only
  have s155 : ((¬ spl0_169) ∨ (¬ spl0_189)) := by
    clear * - f2006
    grind (splits := 100) only
  have s156 : ((¬ spl0_169) ∨ (¬ spl0_188)) := by
    clear * - f2089
    grind (splits := 100) only
  have s158 : ((¬ spl0_35) ∨ (¬ spl0_168)) := by
    clear * - f2145
    grind (splits := 100) only
  have s159 : ((¬ spl0_8) ∨ ((¬ spl0_125) ∨ ((¬ spl0_174) ∨ (¬ spl0_189)))) := by
    clear * - f2300
    grind (splits := 100) only
  have s161 : ((¬ spl0_125) ∨ (¬ spl0_175)) := by
    clear * - f2356
    grind (splits := 100) only
  have s162 : ((¬ spl0_174) ∨ (¬ spl0_188)) := by
    clear * - f2375
    grind (splits := 100) only
  have s172 : ((¬ spl0_121) ∨ (¬ spl0_174)) := by
    clear * - f2490
    grind (splits := 100) only
  have s176 : ((¬ spl0_8) ∨ (¬ spl0_124)) := by
    clear * - f2549
    grind (splits := 100) only
  have s177 : ((¬ spl0_125) ∨ (¬ spl0_172)) := by
    clear * - f2558
    grind (splits := 100) only
  have s178 : ((¬ spl0_35) ∨ (¬ spl0_123)) := by
    clear * - f2626
    grind (splits := 100) only
  have s179 : ((¬ spl0_35) ∨ (¬ spl0_122)) := by
    clear * - f2678
    grind (splits := 100) only
  have s180 : ((¬ spl0_35) ∨ (¬ spl0_121)) := by
    clear * - f2706
    grind (splits := 100) only
  have s181 : ((¬ spl0_8) ∨ (¬ spl0_120)) := by
    clear * - f2753
    grind (splits := 100) only
  have s183 : ((¬ spl0_25) ∨ (¬ spl0_81)) := by
    clear * - f2807
    grind (splits := 100) only
  have s184 : ((¬ spl0_80) ∨ (¬ spl0_189)) := by
    clear * - f2864
    grind (splits := 100) only
  have s187 : (¬ spl0_182) := by
    clear * - f2913
    grind (splits := 100) only
  have s188 : ((¬ spl0_8) ∨ (¬ spl0_18)) := by
    clear * - f3030
    grind (splits := 100) only
  have s189 : ((¬ spl0_25) ∨ (¬ spl0_79)) := by
    clear * - f3071
    grind (splits := 100) only
  have s190 : ((¬ spl0_35) ∨ (¬ spl0_78)) := by
    clear * - f3122
    grind (splits := 100) only
  have s191 : ((¬ spl0_25) ∨ (¬ spl0_78)) := by
    clear * - f3124
    grind (splits := 100) only
  have s192 : ((¬ spl0_35) ∨ (¬ spl0_77)) := by
    clear * - f3160
    grind (splits := 100) only
  have s193 : ((¬ spl0_25) ∨ (¬ spl0_77)) := by
    clear * - f3162
    grind (splits := 100) only
  have s194 : ((¬ spl0_76) ∨ (¬ spl0_189)) := by
    clear * - f3221
    grind (splits := 100) only
  have s195 : ((¬ spl0_35) ∨ (¬ spl0_75)) := by
    clear * - f3270
    grind (splits := 100) only
  have s196 : ((¬ spl0_25) ∨ (¬ spl0_75)) := by
    clear * - f3272
    grind (splits := 100) only
  have s198 : ((¬ spl0_34) ∨ (¬ spl0_126)) := by
    clear * - f3510
    grind (splits := 100) only
  have s199 : ((¬ spl0_34) ∨ (¬ spl0_171)) := by
    clear * - f3538
    grind (splits := 100) only
  have s205 : ((¬ spl0_34) ∨ (¬ spl0_123)) := by
    clear * - f3619
    grind (splits := 100) only
  have s206 : ((¬ spl0_34) ∨ (¬ spl0_175)) := by
    clear * - f3633
    grind (splits := 100) only
  have s207 : ((¬ spl0_34) ∨ (¬ spl0_122)) := by
    clear * - f3643
    grind (splits := 100) only
  have s210 : ((¬ spl0_34) ∨ (¬ spl0_172)) := by
    clear * - f3684
    grind (splits := 100) only
  have s211 : ((¬ spl0_34) ∨ (¬ spl0_170)) := by
    clear * - f3714
    grind (splits := 100) only
  have s212 : ((¬ spl0_168) ∨ (¬ spl0_189)) := by
    clear * - f3725
    grind (splits := 100) only
  have s215 : ((¬ spl0_34) ∨ ((¬ spl0_82) ∨ (¬ spl0_188))) := by
    clear * - f3756
    grind (splits := 100) only
  have s216 : ((¬ spl0_80) ∨ (¬ spl0_188)) := by
    clear * - f3775
    grind (splits := 100) only
  have s217 : ((¬ spl0_76) ∨ (¬ spl0_188)) := by
    clear * - f3794
    grind (splits := 100) only
  have s218 : (¬ spl0_33) := by
    clear * - f3878
    grind (splits := 100) only
  have s219 : ((¬ spl0_8) ∨ (¬ spl0_19)) := by
    clear * - f3988
    grind (splits := 100) only
  have s220 : ((¬ spl0_8) ∨ (¬ spl0_119)) := by
    clear * - f4057
    grind (splits := 100) only
  have s226 : ((¬ spl0_121) ∨ (¬ spl0_168)) := by
    clear * - f4253
    grind (splits := 100) only
  have s233 : ((¬ spl0_125) ∨ (¬ spl0_168)) := by
    clear * - f4423
    grind (splits := 100) only
  have s260 : ((¬ spl0_25) ∨ (¬ spl0_28)) := by
    clear * - f4909
    grind (splits := 100) only
  have s261 : (¬ spl0_32) := by
    clear * - f4938
    grind (splits := 100) only
  have s278 : (¬ spl0_31) := by
    clear * - f5090
    grind (splits := 100) only
  have s281 : (¬ spl0_30) := by
    clear * - f5126
    grind (splits := 100) only
  have s285 : ((¬ spl0_24) ∨ (¬ spl0_28)) := by
    clear * - f5210
    grind (splits := 100) only
  have s293 : ((¬ spl0_24) ∨ (¬ spl0_82)) := by
    clear * - f5332
    grind (splits := 100) only
  have s294 : (¬ spl0_29) := by
    clear * - f5395
    grind (splits := 100) only
  have s303 : ((¬ spl0_22) ∨ (¬ spl0_28)) := by
    clear * - f5512
    grind (splits := 100) only
  have s309 : ((¬ spl0_8) ∨ (¬ spl0_23)) := by
    clear * - f5585
    grind (splits := 100) only
  have s310 : ((¬ spl0_20) ∨ (¬ spl0_35)) := by
    clear * - f5700
    grind (splits := 100) only
  have s312 : ((¬ spl0_20) ∨ (¬ spl0_28)) := by
    clear * - f5766
    grind (splits := 100) only
  have s313 : ((¬ spl0_21) ∨ (¬ spl0_28)) := by
    clear * - f5769
    grind (splits := 100) only
  have s315 : ((¬ spl0_22) ∨ (¬ spl0_35)) := by
    clear * - f5842
    grind (splits := 100) only
  have s319 : ((¬ spl0_21) ∨ (¬ spl0_35)) := by
    clear * - f5932
    grind (splits := 100) only
  have s322 : ((¬ spl0_24) ∨ (¬ spl0_81)) := by
    clear * - f6093
    grind (splits := 100) only
  have s324 : ((¬ spl0_24) ∨ (¬ spl0_79)) := by
    clear * - f6119
    grind (splits := 100) only
  have s326 : (spl0_188 ∨ spl0_189) := by
    clear * - s119 s122 s125 s128 s129 s130 s187
    grind (splits := 100) only
  have s327 : (spl0_28 ∨ (spl0_34 ∨ spl0_35)) := by
    clear * - s29 s218 s261 s278 s281 s294
    grind (splits := 100) only
  have s328 : ((¬ spl0_7) ∨ (spl0_9 ∨ (spl0_10 ∨ spl0_14))) := by
    clear * - s11 s14 s22 s20 s19
    grind (splits := 100) only
  have s329 : (spl0_7 ∨ spl0_8) := by
    clear * - s1 s10 s9 s7 s5 s4 s3
    grind (splits := 100) only
  have s330 : ((¬ spl0_175) ∨ ((¬ spl0_126) ∨ ((¬ spl0_82) ∨ ((¬ spl0_35) ∨ ((¬ spl0_25) ∨ (¬ spl0_8)))))) := by
    clear * - s326 s120 s121
    grind (splits := 100) only
  have s331 : (¬ spl0_173) := by
    clear * - s326 s147 s149
    grind (splits := 100) only
  have s332 : (¬ spl0_169) := by
    clear * - s326 s155 s156
    grind (splits := 100) only
  have s333 : ((¬ spl0_126) ∨ ((¬ spl0_82) ∨ ((¬ spl0_35) ∨ ((¬ spl0_25) ∨ (¬ spl0_8))))) := by
    clear * - s115 s330 s146 s150 s158 s154 s152 s331 s332
    grind (splits := 100) only
  have s334 : ((¬ spl0_125) ∨ ((¬ spl0_35) ∨ (¬ spl0_8))) := by
    clear * - s326 s159 s162 s115 s161 s177 s158 s154 s152 s331 s332
    grind (splits := 100) only
  have s335 : ((¬ spl0_35) ∨ ((¬ spl0_25) ∨ (¬ spl0_8))) := by
    clear * - s51 s184 s194 s326 s121 s115 s333 s146 s150 s85 s334 s152 s154 s158 s178 s179 s180 s220 s181 s176 s196 s193 s191 s189 s183 s331 s332
    grind (splits := 100) only
  have s336 : ((¬ spl0_189) ∨ ((¬ spl0_34) ∨ (¬ spl0_8))) := by
    clear * - s85 s159 s172 s115 s212 s220 s181 s176 s211 s210 s207 s206 s205 s199 s198 s331 s332
    grind (splits := 100) only
  have s337 : ((¬ spl0_25) ∨ (¬ spl0_8)) := by
    clear * - s51 s215 s216 s217 s326 s336 s327 s335 s183 s189 s191 s193 s196 s260
    grind (splits := 100) only
  have s338 : ((¬ spl0_35) ∨ ((¬ spl0_24) ∨ (¬ spl0_8))) := by
    clear * - s51 s184 s194 s326 s121 s115 s146 s150 s85 s334 s152 s154 s158 s178 s179 s180 s190 s192 s195 s220 s181 s176 s324 s322 s293 s331 s332
    grind (splits := 100) only
  have s339 : ((¬ spl0_34) ∨ (¬ spl0_8)) := by
    clear * - s85 s226 s233 s115 s162 s326 s336 s198 s199 s205 s206 s207 s210 s211 s220 s181 s176 s331 s332
    grind (splits := 100) only
  have s340 : ((¬ spl0_35) ∨ (spl0_21 ∨ (spl0_20 ∨ (¬ spl0_8)))) := by
    clear * - s27 s338 s315 s309 s219 s188 s337
    grind (splits := 100) only
  have s341 : (spl0_21 ∨ (spl0_20 ∨ (¬ spl0_8))) := by
    clear * - s27 s285 s303 s327 s340 s309 s219 s188 s337 s339
    grind (splits := 100) only
  have s342 : ((¬ spl0_21) ∨ spl0_34) := by
    clear * - s327 s313 s319
    grind (splits := 100) only
  have s343 : (¬ spl0_8) := by
    clear * - s327 s310 s312 s341 s342 s339
    grind (splits := 100) only
  have s344 : spl0_7 := by
    clear * - s329 s343
    grind (splits := 100) only
  have s345 : (¬ spl0_14) := by
    clear * - s17 s344
    grind (splits := 100) only
  have s346 : (¬ spl0_10) := by
    clear * - s16 s344
    grind (splits := 100) only
  have s347 : (¬ spl0_9) := by
    clear * - s13 s344
    grind (splits := 100) only
  have s348 : False := by
    clear * - s328 s345 s346 s347 s344
    grind (splits := 100) only
  exact s348


set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old b a a ∨ ¬sP2 X Y Z) (rule_def_2_5 : ∀ (X Y Z : G), old b b b ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b Z a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z Z Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old (sF1 X Y Z) (sF2 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old Z Z (sF2 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a (sF4 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_4 : ∀ (X Y Z : G), old (sF4 X Y Z) (sF5 X Y Z) (sF3 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_5 : ∀ (X Y Z : G), old b b (sF5 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_6_4 : ∀ (X Y Z : G), old a a (sF6 X Y Z) ∨ ¬sP6 X Y Z) (rule_def_6_5 : ∀ (X Y Z : G), old (sF6 X Y Z) (sF7 X Y Z) a ∨ ¬sP6 X Y Z) (rule_def_6_6 : ∀ (X Y Z : G), old b b (sF7 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  grind (instances := 3000) only

set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old b a a ∨ ¬sP2 X Y Z) (rule_def_2_5 : ∀ (X Y Z : G), old b b b ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b Z a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z Z Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old (sF1 X Y Z) (sF2 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old Z Z (sF2 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a (sF4 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_4 : ∀ (X Y Z : G), old (sF4 X Y Z) (sF5 X Y Z) (sF3 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_5 : ∀ (X Y Z : G), old b b (sF5 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_6_4 : ∀ (X Y Z : G), old a a (sF6 X Y Z) ∨ ¬sP6 X Y Z) (rule_def_6_5 : ∀ (X Y Z : G), old (sF6 X Y Z) (sF7 X Y Z) a ∨ ¬sP6 X Y Z) (rule_def_6_6 : ∀ (X Y Z : G), old b b (sF7 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  grind (instances := 3000) only

set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP4 : G → G → G → Prop) (sF3 : G → G → G → G) (sF4 : G → G → G → G) (sF5 : G → G → G → G) (sP5 : G → G → G → Prop) (sF6 : G → G → G → G) (sF7 : G → G → G → G) (sP6 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old b a a ∨ ¬sP2 X Y Z) (rule_def_2_5 : ∀ (X Y Z : G), old b b b ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old b b b ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b Z a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z Z Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), old b Z Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old (sF1 X Y Z) (sF2 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old Z Z (sF2 X Y Z) ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), old (sF3 X Y Z) a X ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a (sF4 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_4 : ∀ (X Y Z : G), old (sF4 X Y Z) (sF5 X Y Z) (sF3 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_5_5 : ∀ (X Y Z : G), old b b (sF5 X Y Z) ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_6_4 : ∀ (X Y Z : G), old a a (sF6 X Y Z) ∨ ¬sP6 X Y Z) (rule_def_6_5 : ∀ (X Y Z : G), old (sF6 X Y Z) (sF7 X Y Z) a ∨ ¬sP6 X Y Z) (rule_def_6_6 : ∀ (X Y Z : G), old b b (sF7 X Y Z) ∨ ¬sP6 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  grind (instances := 3000) only

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X0 X1 ∨ ¬ R X1 X2 X3 ∨ ¬ R X3 X0 X4 ∨ R X2 X4 X0)
  rule_2 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X2 X2 X1 ∨ X0 = X2)
  rule_12 : (∀ X0 X1 X2 X3 X4 X5 X6 X7, ¬ R X0 X0 X1 ∨ ¬ R X2 X0 X3 ∨ ¬ R X2 X2 X4 ∨ ¬ R X2 X5 X3 ∨ ¬ R X4 X1 X6 ∨ ¬ R X4 X7 X6 ∨ ¬ R X5 X5 X7 ∨ X0 = X5)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬R X Y Z ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬R X Y Z ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬R X Y Z ∨ Z ∈ finsupp

variable {G : Type*} (ps : PartialSolution G)

/- The remaining discovered invariants are consequences of these four fields. -/
lemma PartialSolution.rule_3 : (∀ X0 X1 X2, ¬ ps.R X0 X0 X0 ∨ ¬ ps.R X0 X1 X2 ∨ ¬ ps.R X1 X0 X0 ∨ ¬ ps.R X1 X1 X1 ∨ ps.R X2 X0 X0) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_4 : (∀ X0 X1 X2 X3, ¬ ps.R X0 X1 X2 ∨ ¬ ps.R X1 X1 X1 ∨ ¬ ps.R X1 X3 X0 ∨ ¬ ps.R X3 X3 X3 ∨ ps.R X2 X0 X3) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_5 : (∀ X0 X1 X2 X3 X4 X5 X6, ¬ ps.R X0 X1 X2 ∨ ¬ ps.R X1 X1 X3 ∨ ¬ ps.R X1 X4 X5 ∨ ¬ ps.R X3 X6 X0 ∨ ¬ ps.R X4 X4 X6 ∨ ps.R X2 X5 X4) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_6 : (∀ X0 X1 X2 X3, ¬ ps.R X0 X0 X1 ∨ ¬ ps.R X1 X0 X2 ∨ ¬ ps.R X1 X1 X2 ∨ ¬ ps.R X2 X1 X3 ∨ ¬ ps.R X2 X2 X3 ∨ X0 = X1) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_7 : (∀ X0 X1 X2, ¬ ps.R X0 X0 X1 ∨ ¬ ps.R X0 X1 X1 ∨ ¬ ps.R X1 X1 X2 ∨ ¬ ps.R X1 X2 X2 ∨ X0 = X1) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_8 : (∀ X0 X1 X2 X3, ¬ ps.R X0 X0 X0 ∨ ¬ ps.R X1 X1 X1 ∨ ¬ ps.R X1 X2 X0 ∨ ¬ ps.R X2 X0 X3 ∨ ¬ ps.R X2 X1 X3 ∨ ¬ ps.R X2 X2 X2 ∨ X0 = X2) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_9 : (∀ X0 X1 X2 X3 X4, ¬ ps.R X0 X0 X1 ∨ ¬ ps.R X2 X1 X3 ∨ ¬ ps.R X2 X2 X4 ∨ ¬ ps.R X2 X4 X3 ∨ ¬ ps.R X4 X0 X0 ∨ ¬ ps.R X4 X2 X0 ∨ ¬ ps.R X4 X4 X2 ∨ X0 = X4) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_10 : (∀ X0 X1 X2 X3, ¬ ps.R X0 X0 X0 ∨ ¬ ps.R X1 X0 X2 ∨ ¬ ps.R X1 X1 X1 ∨ ¬ ps.R X1 X3 X2 ∨ ¬ ps.R X3 X3 X3 ∨ X0 = X3) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only

lemma PartialSolution.rule_11 : (∀ X0 X1 X2 X3, ¬ ps.R X0 X0 X1 ∨ ¬ ps.R X1 X1 X0 ∨ ¬ ps.R X2 X0 X3 ∨ ¬ ps.R X2 X1 X3 ∨ ¬ ps.R X2 X2 X2 ∨ X0 = X1) := by
  have := ps.rule_0
  have := ps.rule_1
  have := ps.rule_2
  have := ps.rule_12
  grind (instances := 10000) only



set_option linter.all false in
theorem PartialSolution.adjoin (a b c : G) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ ps.R a b X0)
    (p4XY : ∀ X1 X2, ¬ ps.R X1 X2 c) (p4XZ : ∀ X1 X2, ¬ ps.R X1 c X2) (p4YZ : ∀ X1 X2, ¬ ps.R c X1 X2)
    : ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by classical
  let sP0 (X Y Z) := a = X ∧ b = Y ∧ c = Z
  have hsP0 (X Y Z) (h : sP0 X Y Z) : a = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP0
  obtain ⟨rule_def_0_0, rule_def_0_1, rule_def_0_2⟩ := hsP0
  simp_rw [or_comm] at rule_def_0_0 rule_def_0_1 rule_def_0_2
  let sP1 (X Y Z) := ∃ sF0, c = Y ∧ b = Z ∧ ps.R b b sF0 ∧ ps.R sF0 X a
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z) := c = X ∧ a = Y ∧ a = Z ∧ ps.R a a a ∧ ps.R b a a ∧ ps.R b b b
  have hsP2 (X Y Z) (h : sP2 X Y Z) : c = X ∧ a = Y ∧ a = Z ∧ ps.R a a a ∧ ps.R b a a ∧ ps.R b b b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3, rule_def_2_4, rule_def_2_5⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_2_5
  let sP3 (X Y Z) := c = X ∧ a = Y ∧ ps.R b b b ∧ ps.R b Z a ∧ ps.R Z Z Z
  have hsP3 (X Y Z) (h : sP3 X Y Z) : c = X ∧ a = Y ∧ ps.R b b b ∧ ps.R b Z a ∧ ps.R Z Z Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP3
  obtain ⟨rule_def_3_0, rule_def_3_1, rule_def_3_2, rule_def_3_3, rule_def_3_4⟩ := hsP3
  simp_rw [or_comm] at rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4
  let sP4 (X Y Z) := ∃ sF1 sF2, c = X ∧ ps.R b b sF1 ∧ ps.R b Z Y ∧ ps.R sF1 sF2 a ∧ ps.R Z Z sF2
  choose! sF1 sF2 hsP4 using fun (X Y Z) (h : sP4 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP4
  obtain ⟨rule_def_4_0, rule_def_4_1, rule_def_4_2, rule_def_4_3, rule_def_4_4⟩ := hsP4
  simp_rw [or_comm] at rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4
  let sP5 (X Y Z) := ∃ sF3 sF4 sF5, c = Y ∧ b = Z ∧ ps.R sF3 a X ∧ ps.R a a sF4 ∧ ps.R sF4 sF5 sF3 ∧ ps.R b b sF5
  choose! sF3 sF4 sF5 hsP5 using fun (X Y Z) (h : sP5 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP5
  obtain ⟨rule_def_5_0, rule_def_5_1, rule_def_5_2, rule_def_5_3, rule_def_5_4, rule_def_5_5⟩ := hsP5
  simp_rw [or_comm] at rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_5_4 rule_def_5_5
  let sP6 (X Y Z) := ∃ sF6 sF7, a = b ∧ c = X ∧ c = Y ∧ b = Z ∧ ps.R a a sF6 ∧ ps.R sF6 sF7 a ∧ ps.R b b sF7
  choose! sF6 sF7 hsP6 using fun (X Y Z) (h : sP6 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP6
  obtain ⟨rule_def_6_0, rule_def_6_1, rule_def_6_2, rule_def_6_3, rule_def_6_4, rule_def_6_5, rule_def_6_6⟩ := hsP6
  simp_rw [or_comm] at rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_6_4 rule_def_6_5 rule_def_6_6

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_4 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_5 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_6 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_7 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [not_and, not_exists, imp_iff_not_or, sP3, ← forall_or_right, or_assoc] at imp_new_4
  simp only [not_and, not_exists, imp_iff_not_or, sP4, ← forall_or_right, or_assoc] at imp_new_5
  simp only [not_and, not_exists, imp_iff_not_or, sP5, ← forall_or_right, or_assoc] at imp_new_6
  simp only [not_and, not_exists, imp_iff_not_or, sP6, ← forall_or_right, or_assoc] at imp_new_7
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 sP2 sP3 sP4 sP5 sP6 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_10 ps.rule_12 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_2_5 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_6_4 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 ac bc p3 p4XY p4XZ p4YZ ps.rule_1 ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_2_5 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_5_4 rule_def_5_5 rule_def_6_0 rule_def_6_4 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 ac bc p3 p4XY p4XZ p4YZ ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_5 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_4 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_5 rule_def_6_0 rule_def_6_2 rule_def_6_3 rule_def_6_6 new_imp
  have prev_12 := rule_12_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 ac bc p3 p4XY p4XZ p4YZ ps.rule_2 ps.rule_12 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_4 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_6_4 new_imp

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_12 := prev_12
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 (· ∈ ps.finsupp) rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_2_5 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_5_4 rule_def_5_5 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_6_4 rule_def_6_5 rule_def_6_6 new_imp ps.mem_1 ps.mem_2 ps.mem_3
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 (· ∈ ps.finsupp) rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_2_5 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_5_4 rule_def_5_5 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_6_4 rule_def_6_5 rule_def_6_6 new_imp ps.mem_1 ps.mem_2 ps.mem_3
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sF1 sF2 sP4 sF3 sF4 sF5 sP5 sF6 sF7 sP6 (· ∈ ps.finsupp) rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_2_5 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_5_4 rule_def_5_5 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_6_4 rule_def_6_5 rule_def_6_6 new_imp ps.mem_1 ps.mem_2 ps.mem_3
  }, by simp only [new_new, imp_iff_not_or, imp_new_0, implies_true, and_self]⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose_spec
    (ps.adjoin a b c (by simp_all [eq_comm]) (by simp_all)
        (by simpa using h) (fun _ _ h ↦ by have := (ps.mem_3 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_2 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_1 _ _ _).neg_resolve_left h; simp_all)).choose

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

theorem PartialSolution.compl_rule1 (X0 X1 X2 X3 X4 : ℕ) :
    ¬ ps.compl X0 X0 X1 ∨ ¬ ps.compl X1 X2 X3 ∨ ¬ ps.compl X3 X0 X4 ∨ ps.compl X2 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X0) (max (Nat.pair X1 X2) (max (Nat.pair X3 X0) (max (Nat.pair X2 X4) 0)))
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

theorem PartialSolution.toMagma_equation1278 :
    letI := ps.toMagma
    Equation1278 ℕ := by
  simp only [Equation1278]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 (ps.complFun X0 X0) X1 (ps.complFun (ps.complFun X0 X0) X1) (ps.complFun (ps.complFun (ps.complFun X0 X0) X1) X0)

/-- The completion preserves the additional square-injectivity invariant. -/
theorem PartialSolution.compl_square_injective (x y z : ℕ)
    (hx : ps.compl x x z) (hy : ps.compl y y z) : x = y := by
  let i := 1 + max (Nat.pair x x) (Nat.pair y y)
  have hx' := ps.complSeq_of_compl_of_lt x x i (by omega) z hx
  have hy' := ps.complSeq_of_compl_of_lt y y i (by omega) z hy
  have h := (ps.complSeq i).rule_2 x z y
  simp_all

/-- In the resulting total magma, distinct elements have distinct squares. -/
theorem PartialSolution.toMagma_square_injective :
    Function.Injective (fun x => ps.complFun x x) := by
  intro x y h
  apply ps.compl_square_injective x y (ps.complFun x x)
  · exact (ps.complFun_eq_iff x x _).mp rfl
  · exact (ps.complFun_eq_iff y y _).mp h.symm

end Eq1278
