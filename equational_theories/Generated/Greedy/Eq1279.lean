import Mathlib.Tactic.ClearExcept
import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

set_option linter.all false

/-! A countable completion construction for E1279. Six local invariants
make adjoining a fresh product consistent. The clausal preservation arguments
were found by Vampire and are replayed below as kernel-checked deductions.
The external prover is not invoked at build time and supplies no axiom. -/
namespace Eq1279

set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X2 X4 ∨ old X2 X4 X0)) (old_2 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X4 X2 X3 ∨ ¬ old X5 X5 X4 ∨ X0 = X5)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X1, b ≠ X ∨ c ≠ Y ∨ ¬ old Z Z X1 ∨ ¬ old X1 b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old (sF1 X Y Z) b a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq70 (X1 X2 X3 : G) : c ≠ X1 ∨ ¬(old X2 X2 X3) ∨ ¬(old X3 b a) ∨ (new b X1 X2) := by
    clear * - imp_new_2
    first | exact resolve imp_new_2 rfl | grind only
  have eq71 (X2 X3 : G) : ¬(old X3 b a) ∨ ¬(old X2 X2 X3) ∨ (new b c X2) := by
    clear * - eq70
    first | exact resolve eq70 rfl | grind only
  have eq78 (X0 X1 : G) : ¬(sP1 X0 X1 c) := by
    clear * - rule_def_1_2 p4YZ
    first | exact resolve rule_def_1_2 p4YZ | exact resolve p4YZ rule_def_1_2 | grind only
  have eq86 (X0 X1 X2 X3 : G) : ¬(old X0 X0 (sF0 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP1 X1 X2 X3) := by
    clear * - eq71 rule_def_1_3
    first | exact resolve eq71 rule_def_1_3 | exact resolve rule_def_1_3 eq71 | grind only
  have eq91 (X0 X1 X2 X3 X4 : G) : ¬(old X0 b (sF1 X1 X2 X3)) ∨ ¬(old X4 X4 X0) ∨ (old b a X4) ∨ ¬(sP2 X1 X2 X3) := by
    clear * - old_1 rule_def_2_3
    first | exact resolve old_1 rule_def_2_3 | exact resolve rule_def_2_3 old_1 | grind only
  have eq96 (X0 X1 X2 X3 X4 X5 X6 : G) : ¬(old (sF0 X3 X4 X5) X1 X2) ∨ ¬(old X0 X1 X2) ∨ ¬(old X6 X6 X0) ∨ X5 = X6 ∨ ¬(sP1 X3 X4 X5) := by
    clear * - old_2 rule_def_1_2
    first | exact resolve old_2 rule_def_1_2 | exact resolve rule_def_1_2 old_2 | grind only
  have eq110 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq111 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq114 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq110 rule_def_0_2
    first | exact resolve eq110 rule_def_0_2 | exact resolve rule_def_0_2 eq110 | grind only
  have eq115 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq110 rule_def_0_1
    first | exact resolve eq110 rule_def_0_1 | exact resolve rule_def_0_1 eq110 | grind only
  have eq116 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq110 rule_def_0_0
    first | exact resolve eq110 rule_def_0_0 | exact resolve rule_def_0_0 eq110 | grind only
  have eq117 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq115 rule_def_2_1
    first | exact resolve eq115 rule_def_2_1 | exact resolve rule_def_2_1 eq115 | grind only
  have eq118 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ c = sk3 := by
    clear * - eq111 rule_def_0_2
    first | exact resolve eq111 rule_def_0_2 | exact resolve rule_def_0_2 eq111 | grind only
  have eq119 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ b = sk1 := by
    clear * - eq111 rule_def_0_1
    first | exact resolve eq111 rule_def_0_1 | exact resolve rule_def_0_1 eq111 | grind only
  have eq120 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ a = sk0 := by
    clear * - eq111 rule_def_0_0
    first | exact resolve eq111 rule_def_0_0 | exact resolve rule_def_0_0 eq111 | grind only
  have eq121 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := by
    clear * - eq119 rule_def_2_1
    first | exact resolve eq119 rule_def_2_1 | exact resolve rule_def_2_1 eq119 | grind only
  have eq123 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq117 rule_def_1_1
    first | exact resolve eq117 rule_def_1_1 | exact resolve rule_def_1_1 eq117 | grind only
  have eq130 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0 := by
    clear * - eq123 old_0
    first | exact resolve eq123 old_0 | exact resolve old_0 eq123 | grind only
  have eq141 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq121 rule_def_1_1
    first | exact resolve eq121 rule_def_1_1 | exact resolve rule_def_1_1 eq121 | grind only
  have eq142 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq121 rule_def_1_0
    first | exact resolve eq121 rule_def_1_0 | exact resolve rule_def_1_0 eq121 | grind only
  have eq158 : c = sk1 ∨ b = sk1 ∨ sk2 = sk3 ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq130 eq141
    first | exact resolve eq130 eq141 | exact resolve eq141 eq130 | grind only
  have eq159 : c = sk1 ∨ b = sk1 ∨ sk2 = sk3 := by
    clear * - eq158
    first | exact resolve eq158 rfl | grind only
  have eq163 : c = sk1 ∨ b = sk1 := by
    clear * - eq159 preserve_2
    first | exact resolve eq159 preserve_2 | exact resolve preserve_2 eq159 | grind only
  have eq165 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := by
    clear * - eq86 rule_def_1_2
    first | exact resolve eq86 rule_def_1_2 | exact resolve rule_def_1_2 eq86 | grind only
  have eq166 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new b c X0) := by
    clear * - eq165
    first | exact resolve eq165 rfl | grind only
  have eq171 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ c = b ∨ b = sk1 := by
    clear * - eq117 eq163
    first | exact Or.assoc3 (eq163.imp_left (fun h : c = sk1 => superpose h eq117)) | exact superpose eq117 eq163 | exact superpose eq163 eq117 | grind only
  have eq172 : (sP1 sk0 c sk3) ∨ (old sk0 c sk3) ∨ c = b ∨ b = sk1 := by
    clear * - eq121 eq163
    first | exact Or.assoc3 (eq163.imp_left (fun h : c = sk1 => superpose h eq121)) | exact superpose eq121 eq163 | exact superpose eq163 eq121 | grind only
  have eq174 : (old sk0 c sk3) ∨ c = b ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq142 eq163
    first | exact Or.assoc3 (eq163.imp_left (fun h : c = sk1 => superpose h eq142)) | exact superpose eq142 eq163 | exact superpose eq163 eq142 | grind only
  have eq176 : c = b ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq174 p4XZ
    first | exact resolve eq174 p4XZ | exact resolve p4XZ eq174 | grind only
  have eq178 : (sP1 sk0 c sk3) ∨ c = b ∨ b = sk1 := by
    clear * - eq172 p4XZ
    first | exact resolve eq172 p4XZ | exact resolve p4XZ eq172 | grind only
  have eq179 : (sP1 sk0 c sk2) ∨ c = b ∨ b = sk1 := by
    clear * - eq171 p4XZ
    first | exact resolve eq171 p4XZ | exact resolve p4XZ eq171 | grind only
  have eq182 : b = sk1 ∨ b = sk0 := by
    clear * - eq176 bc
    first | exact resolve eq176 bc | exact resolve bc eq176 | grind only
  have eq184 : (sP1 sk0 c sk3) ∨ b = sk1 := by
    clear * - eq178 bc
    first | exact resolve eq178 bc | exact resolve bc eq178 | grind only
  have eq185 : (sP1 sk0 c sk2) ∨ b = sk1 := by
    clear * - eq179 bc
    first | exact resolve eq179 bc | exact resolve bc eq179 | grind only
  have eq209 (X0 X1 X2 X3 : G) : ¬(old X0 X0 b) ∨ (old b a X0) ∨ ¬(sP2 X1 X2 X3) ∨ ¬(sP2 X1 X2 X3) := by
    clear * - eq91 rule_def_2_2
    first | exact resolve eq91 rule_def_2_2 | exact resolve rule_def_2_2 eq91 | grind only
  have eq210 (X0 X1 X2 X3 : G) : ¬(sP2 X1 X2 X3) ∨ (old b a X0) ∨ ¬(old X0 X0 b) := by
    clear * - eq209
    first | exact resolve eq209 rfl | grind only
  have eq212 (X0 X1 X2 X3 X4 : G) : ¬(old X0 b a) ∨ ¬(old X1 X1 X0) ∨ X1 = X2 ∨ ¬(sP1 X3 X4 X2) ∨ ¬(sP1 X3 X4 X2) := by
    clear * - eq96 rule_def_1_3
    first | exact resolve eq96 rule_def_1_3 | exact resolve rule_def_1_3 eq96 | grind only
  have eq214 (X0 X1 X2 X3 X4 : G) : ¬(sP1 X3 X4 X2) ∨ ¬(old X1 X1 X0) ∨ X1 = X2 ∨ ¬(old X0 b a) := by
    clear * - eq212
    first | exact resolve eq212 rfl | grind only
  have eq257 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq114 rule_def_1_1
    first | exact resolve eq114 rule_def_1_1 | exact resolve rule_def_1_1 eq114 | grind only
  have eq264 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq116 rule_def_1_1
    first | exact resolve eq116 rule_def_1_1 | exact resolve rule_def_1_1 eq116 | grind only
  have eq265 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq116 rule_def_1_0
    first | exact resolve eq116 rule_def_1_0 | exact resolve rule_def_1_0 eq116 | grind only
  have eq269 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq257 rule_def_2_0
    first | exact resolve eq257 rule_def_2_0 | exact resolve rule_def_2_0 eq257 | grind only
  have eq279 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq118 rule_def_1_1
    first | exact resolve eq118 rule_def_1_1 | exact resolve rule_def_1_1 eq118 | grind only
  have eq290 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = X0 := by
    clear * - eq269 old_0
    first | exact resolve eq269 old_0 | exact resolve old_0 eq269 | grind only
  have eq292 : (old sk0 b sk2) ∨ c = sk2 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq269 eq182
    first | exact Or.assoc4 (eq182.imp_left (fun h : b = sk1 => superpose h eq269)) | exact superpose eq269 eq182 | exact superpose eq182 eq269 | grind only
  have eq295 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq292 bc
    first | exact resolve eq292 bc | exact resolve bc eq292 | grind only
  have eq298 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq120 rule_def_1_1
    first | exact resolve eq120 rule_def_1_1 | exact resolve rule_def_1_1 eq120 | grind only
  have eq299 : (sP2 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq120 rule_def_1_0
    first | exact resolve eq120 rule_def_1_0 | exact resolve rule_def_1_0 eq120 | grind only
  have eq313 : (new b c sk3) ∨ b = sk1 := by
    clear * - eq166 eq184
    first | exact resolve eq166 eq184 | exact resolve eq184 eq166 | grind only
  have eq314 : (new b c sk2) ∨ b = sk1 := by
    clear * - eq166 eq185
    first | exact resolve eq166 eq185 | exact resolve eq185 eq166 | grind only
  have eq315 : b = sk1 ∨ (old b c sk3) ∨ (sP0 b c sk3) ∨ (sP1 b c sk3) ∨ (sP2 b c sk3) := by
    clear * - eq313 new_imp
    first | exact resolve eq313 new_imp | exact resolve new_imp eq313 | grind only
  have eq316 : (sP0 b c sk3) ∨ b = sk1 ∨ (sP1 b c sk3) ∨ (sP2 b c sk3) := by
    clear * - eq315 p4XZ
    first | exact resolve eq315 p4XZ | exact resolve p4XZ eq315 | grind only
  have eq318 : b = sk1 ∨ (old b c sk2) ∨ (sP0 b c sk2) ∨ (sP1 b c sk2) ∨ (sP2 b c sk2) := by
    clear * - eq314 new_imp
    first | exact resolve eq314 new_imp | exact resolve new_imp eq314 | grind only
  have eq319 : (sP0 b c sk2) ∨ b = sk1 ∨ (sP1 b c sk2) ∨ (sP2 b c sk2) := by
    clear * - eq318 p4XZ
    first | exact resolve eq318 p4XZ | exact resolve p4XZ eq318 | grind only
  have eq346 (X0 X1 : G) : ¬(old X1 b a) ∨ sk2 = X0 ∨ ¬(old X0 X0 X1) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq214 eq116
    first | exact resolve eq214 eq116 | exact resolve eq116 eq214 | grind only
  have eq347 (X0 X1 : G) : ¬(old X1 b a) ∨ sk2 = X0 ∨ ¬(old X0 X0 X1) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq214 eq114
    first | exact resolve eq214 eq114 | exact resolve eq114 eq214 | grind only
  have eq354 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq264 rule_def_2_0
    first | exact resolve eq264 rule_def_2_0 | exact resolve rule_def_2_0 eq264 | grind only
  have eq373 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ sk2 = X0 := by
    clear * - eq354 old_0
    first | exact resolve eq354 old_0 | exact resolve old_0 eq354 | grind only
  have eq396 : (old sk2 sk2 b) ∨ a = sk0 ∨ b = sk0 ∨ (old sk0 sk1 sk2) := by
    clear * - eq265 rule_def_2_4
    first | exact resolve eq265 rule_def_2_4 | exact resolve rule_def_2_4 eq265 | grind only
  have eq402 (X0 : G) : ¬(old X0 X0 b) ∨ a = sk0 ∨ b = sk0 ∨ (old b a X0) ∨ (old sk0 sk1 sk2) := by
    clear * - eq265 eq210
    first | exact resolve eq265 eq210 | exact resolve eq210 eq265 | grind only
  have eq423 : (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq279 rule_def_2_0
    first | exact resolve eq279 rule_def_2_0 | exact resolve rule_def_2_0 eq279 | grind only
  have eq445 : (old sk0 b sk3) ∨ c = sk3 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq423 eq182
    first | exact Or.assoc4 (eq182.imp_left (fun h : b = sk1 => superpose h eq423)) | exact superpose eq423 eq182 | exact superpose eq182 eq423 | grind only
  have eq448 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq445 bc
    first | exact resolve eq445 bc | exact resolve bc eq445 | grind only
  have eq467 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq298 rule_def_2_0
    first | exact resolve eq298 rule_def_2_0 | exact resolve rule_def_2_0 eq298 | grind only
  have eq492 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq299 rule_def_2_0
    first | exact resolve eq299 rule_def_2_0 | exact resolve rule_def_2_0 eq299 | grind only
  have eq494 : (old sk3 sk3 b) ∨ a = sk0 ∨ b = sk0 ∨ (old sk0 sk1 sk3) := by
    clear * - eq299 rule_def_2_4
    first | exact resolve eq299 rule_def_2_4 | exact resolve rule_def_2_4 eq299 | grind only
  have eq500 (X0 : G) : ¬(old X0 X0 b) ∨ a = sk0 ∨ b = sk0 ∨ (old b a X0) ∨ (old sk0 sk1 sk3) := by
    clear * - eq299 eq210
    first | exact resolve eq299 eq210 | exact resolve eq210 eq299 | grind only
  have eq673 (X0 X1 X2 X3 : G) : ¬(old X0 X0 (sF0 X1 X2 X3)) ∨ sk2 = X0 ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ ¬(sP1 X1 X2 X3) := by
    clear * - eq346 rule_def_1_3
    first | exact resolve eq346 rule_def_1_3 | exact resolve rule_def_1_3 eq346 | grind only
  have eq689 (X0 X1 X2 X3 : G) : ¬(old X0 X0 (sF0 X1 X2 X3)) ∨ sk2 = X0 ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ ¬(sP1 X1 X2 X3) := by
    clear * - eq347 rule_def_1_3
    first | exact resolve eq347 rule_def_1_3 | exact resolve rule_def_1_3 eq347 | grind only
  have eq1026 : a = sk0 ∨ b = sk0 ∨ (old b a sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 ∨ (old sk0 sk1 sk2) := by
    clear * - eq402 eq396
    first | exact resolve eq402 eq396 | exact resolve eq396 eq402 | grind only
  have eq1040 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ (old b a sk2) ∨ a = sk0 := by
    clear * - eq1026
    first | exact resolve eq1026 rfl | grind only
  have eq1206 : a = sk0 ∨ b = sk0 ∨ (old b a sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk0 ∨ (old sk0 sk1 sk3) := by
    clear * - eq500 eq494
    first | exact resolve eq500 eq494 | exact resolve eq494 eq500 | grind only
  have eq1213 : (old sk0 sk1 sk3) ∨ b = sk0 ∨ (old b a sk3) ∨ a = sk0 := by
    clear * - eq1206
    first | exact resolve eq1206 rfl | grind only
  have eq1685 : b = sk1 ∨ (sP1 b c sk3) ∨ (sP2 b c sk3) ∨ c = b := by
    clear * - eq316 rule_def_0_1
    first | exact resolve eq316 rule_def_0_1 | exact resolve rule_def_0_1 eq316 | grind only
  have eq1687 : b = sk1 ∨ (sP1 b c sk3) ∨ c = b := by
    clear * - eq1685 rule_def_2_1
    first | exact resolve eq1685 rule_def_2_1 | exact resolve rule_def_2_1 eq1685 | grind only
  have eq1688 : (sP1 b c sk3) ∨ b = sk1 := by
    clear * - eq1687 bc
    first | exact resolve eq1687 bc | exact resolve bc eq1687 | grind only
  have eq1731 : b = sk1 ∨ (sP1 b c sk2) ∨ (sP2 b c sk2) ∨ c = b := by
    clear * - eq319 rule_def_0_1
    first | exact resolve eq319 rule_def_0_1 | exact resolve rule_def_0_1 eq319 | grind only
  have eq1733 : b = sk1 ∨ (sP1 b c sk2) ∨ c = b := by
    clear * - eq1731 rule_def_2_1
    first | exact resolve eq1731 rule_def_2_1 | exact resolve rule_def_2_1 eq1731 | grind only
  have eq1734 : (sP1 b c sk2) ∨ b = sk1 := by
    clear * - eq1733 bc
    first | exact resolve eq1733 bc | exact resolve bc eq1733 | grind only
  have eq1844 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq290 eq423
    first | exact resolve eq290 eq423 | exact resolve eq423 eq290 | grind only
  have eq1846 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq290 eq467
    first | exact resolve eq290 eq467 | exact resolve eq467 eq290 | grind only
  have eq1856 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ a = sk0 := by
    clear * - eq1846
    first | exact resolve eq1846 rfl | grind only
  have eq1858 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ c = sk3 := by
    clear * - eq1844
    first | exact resolve eq1844 rfl | grind only
  have eq1873 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 := by
    clear * - eq1856 preserve_2
    first | exact resolve eq1856 preserve_2 | exact resolve preserve_2 eq1856 | grind only
  have eq1875 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq1858 preserve_2
    first | exact resolve eq1858 preserve_2 | exact resolve preserve_2 eq1858 | grind only
  have eq1898 : (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 := by
    clear * - eq354 eq1873
    first | exact Or.assoc4 (eq1873.imp_left (fun h : c = sk2 => superpose h eq354)) | exact superpose eq354 eq1873 | exact superpose eq1873 eq354 | grind only
  have eq1938 : (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq1898
    first | exact resolve eq1898 rfl | grind only
  have eq1963 : c = sk1 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq1938 p4XY
    first | exact resolve eq1938 p4XY | exact resolve p4XY eq1938 | grind only
  have eq1988 : (sP1 sk0 c sk3) ∨ (old sk0 c sk3) ∨ c = b ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq121 eq1963
    first | exact Or.assoc3 (eq1963.imp_left (fun h : c = sk1 => superpose h eq121)) | exact superpose eq121 eq1963 | exact superpose eq1963 eq121 | grind only
  have eq2007 : (old sk0 c sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq492 eq1963
    first | exact Or.assoc4 (eq1963.imp_left (fun h : c = sk1 => superpose h eq492)) | exact superpose eq492 eq1963 | exact superpose eq1963 eq492 | grind only
  have eq2014 : (old sk0 c sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2007
    first | exact resolve eq2007 rfl | grind only
  have eq2028 : a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2014 p4XZ
    first | exact resolve eq2014 p4XZ | exact resolve p4XZ eq2014 | grind only
  have eq2043 : (sP1 sk0 c sk3) ∨ c = b ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq1988 p4XZ
    first | exact resolve eq1988 p4XZ | exact resolve p4XZ eq1988 | grind only
  have eq2056 : (sP1 sk0 c sk3) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq2043 bc
    first | exact resolve eq2043 bc | exact resolve bc eq2043 | grind only
  have eq2102 : (old a b sk2) ∨ c = sk2 ∨ a = c ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq295 eq2028
    first | exact Or.assoc4 (eq2028.imp_left (fun h : a = sk0 => superpose h eq295)) | exact superpose eq295 eq2028 | exact superpose eq2028 eq295 | grind only
  have eq2107 : (old a b sk3) ∨ c = sk3 ∨ a = c ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq448 eq2028
    first | exact Or.assoc4 (eq2028.imp_left (fun h : a = sk0 => superpose h eq448)) | exact superpose eq448 eq2028 | exact superpose eq2028 eq448 | grind only
  have eq2115 : a ≠ b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2028
    grind only
  have eq2122 : (old a b sk3) ∨ c = sk3 ∨ a = c ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2107 eq2115
    first | exact resolve eq2107 eq2115 | exact resolve eq2115 eq2107 | grind only
  have eq2125 : (old a b sk2) ∨ c = sk2 ∨ a = c ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2102 eq2115
    first | exact resolve eq2102 eq2115 | exact resolve eq2115 eq2102 | grind only
  have eq2139 : c = sk3 ∨ a = c ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2122 p3
    first | exact resolve eq2122 p3 | exact resolve p3 eq2122 | grind only
  have eq2141 : c = sk2 ∨ a = c ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2125 p3
    first | exact resolve eq2125 p3 | exact resolve p3 eq2125 | grind only
  have eq2146 : c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2139 ac
    first | exact resolve eq2139 ac | exact resolve ac eq2139 | grind only
  have eq2147 : c = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq2141 ac
    first | exact resolve eq2141 ac | exact resolve ac eq2141 | grind only
  have eq2172 : c ≠ sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - preserve_2 eq2146
    first | exact (eq2146.imp_left (fun h : c = sk3 => superpose h preserve_2)) | exact superpose preserve_2 eq2146 | exact superpose eq2146 preserve_2 | grind only
  have eq2235 : c = sk0 ∨ b = sk0 := by
    clear * - eq2172 eq2147
    first | exact resolve eq2172 eq2147 | exact resolve eq2147 eq2172 | grind only
  have eq2311 : (old c sk1 sk2) ∨ c = b ∨ (old b a sk2) ∨ a = c ∨ b = sk0 := by
    clear * - eq1040 eq2235
    first | exact Or.assoc4 (eq2235.imp_left (fun h : c = sk0 => superpose h eq1040)) | exact superpose eq1040 eq2235 | exact superpose eq2235 eq1040 | grind only
  have eq2317 : (old c sk1 sk3) ∨ c = b ∨ (old b a sk3) ∨ a = c ∨ b = sk0 := by
    clear * - eq1213 eq2235
    first | exact Or.assoc4 (eq2235.imp_left (fun h : c = sk0 => superpose h eq1213)) | exact superpose eq1213 eq2235 | exact superpose eq2235 eq1213 | grind only
  have eq2319 : c = b ∨ (old b a sk3) ∨ a = c ∨ b = sk0 := by
    clear * - eq2317 p4YZ
    first | exact resolve eq2317 p4YZ | exact resolve p4YZ eq2317 | grind only
  have eq2325 : c = b ∨ (old b a sk2) ∨ a = c ∨ b = sk0 := by
    clear * - eq2311 p4YZ
    first | exact resolve eq2311 p4YZ | exact resolve p4YZ eq2311 | grind only
  have eq2357 : (old b a sk3) ∨ a = c ∨ b = sk0 := by
    clear * - eq2319 bc
    first | exact resolve eq2319 bc | exact resolve bc eq2319 | grind only
  have eq2362 : (old b a sk2) ∨ a = c ∨ b = sk0 := by
    clear * - eq2325 bc
    first | exact resolve eq2325 bc | exact resolve bc eq2325 | grind only
  have eq2383 : (old b a sk3) ∨ b = sk0 := by
    clear * - eq2357 ac
    first | exact resolve eq2357 ac | exact resolve ac eq2357 | grind only
  have eq2385 : (old b a sk2) ∨ b = sk0 := by
    clear * - eq2362 ac
    first | exact resolve eq2362 ac | exact resolve ac eq2362 | grind only
  have eq2454 (X0 : G) : ¬(old b a X0) ∨ b = sk0 ∨ sk3 = X0 := by
    clear * - eq2383 old_0
    first | exact resolve eq2383 old_0 | exact resolve old_0 eq2383 | grind only
  have eq3007 (X0 X1 X2 : G) : sk2 = X0 ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := by
    clear * - eq673 rule_def_1_2
    first | exact resolve eq673 rule_def_1_2 | exact resolve rule_def_1_2 eq673 | grind only
  have eq3008 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ sk2 = X0 := by
    clear * - eq3007
    first | exact resolve eq3007 rfl | grind only
  have eq3023 (X0 X1 X2 : G) : sk2 = X0 ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := by
    clear * - eq689 rule_def_1_2
    first | exact resolve eq689 rule_def_1_2 | exact resolve rule_def_1_2 eq689 | grind only
  have eq3024 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ sk2 = X0 := by
    clear * - eq3023
    first | exact resolve eq3023 rfl | grind only
  have eq3128 : b = sk0 ∨ sk2 = sk3 ∨ b = sk0 := by
    clear * - eq2454 eq2385
    first | exact resolve eq2454 eq2385 | exact resolve eq2385 eq2454 | grind only
  have eq3129 : b = sk0 ∨ sk2 = sk3 := by
    clear * - eq3128
    first | exact resolve eq3128 rfl | grind only
  have eq3135 : b = sk0 := by
    clear * - eq3129 preserve_2
    first | exact resolve eq3129 preserve_2 | exact resolve preserve_2 eq3129 | grind only
  have eq3164 : (old b sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = b := by
    clear * - eq269 eq3135
    first | exact superpose eq269 eq3135 | exact superpose eq3135 eq269 | grind only
  have eq3172 : (old b sk1 sk2) ∨ a = b ∨ c = sk1 ∨ c = b := by
    clear * - eq354 eq3135
    first | exact superpose eq354 eq3135 | exact superpose eq3135 eq354 | grind only
  have eq3173 : (old b sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = b := by
    clear * - eq423 eq3135
    first | exact superpose eq423 eq3135 | exact superpose eq3135 eq423 | grind only
  have eq3174 : (old b sk1 sk3) ∨ a = b ∨ c = sk1 ∨ c = b := by
    clear * - eq467 eq3135
    first | exact superpose eq467 eq3135 | exact superpose eq3135 eq467 | grind only
  have eq3187 : (old b sk1 sk3) ∨ a = b ∨ c = sk1 := by
    clear * - eq3174 bc
    first | exact resolve eq3174 bc | exact resolve bc eq3174 | grind only
  have eq3188 : (old b sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq3173 bc
    first | exact resolve eq3173 bc | exact resolve bc eq3173 | grind only
  have eq3189 : (old b sk1 sk2) ∨ a = b ∨ c = sk1 := by
    clear * - eq3172 bc
    first | exact resolve eq3172 bc | exact resolve bc eq3172 | grind only
  have eq3191 : (old b sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq3164 bc
    first | exact resolve eq3164 bc | exact resolve bc eq3164 | grind only
  have eq3264 (X0 : G) : ¬(old b sk1 X0) ∨ c = sk1 ∨ c = b ∨ a = b ∨ sk2 = X0 := by
    clear * - eq373 eq3135
    first | exact superpose eq373 eq3135 | exact superpose eq3135 eq373 | grind only
  have eq3282 (X0 : G) : ¬(old b sk1 X0) ∨ c = sk1 ∨ a = b ∨ sk2 = X0 := by
    clear * - eq3264 bc
    first | exact resolve eq3264 bc | exact resolve bc eq3264 | grind only
  have eq4305 : (old b sk1 c) ∨ a = b ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq3187 eq1875
    first | exact Or.assoc3 (eq1875.imp_left (fun h : c = sk3 => superpose h eq3187)) | exact superpose eq3187 eq1875 | exact superpose eq1875 eq3187 | grind only
  have eq4306 : (old b sk1 c) ∨ a = b ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
    clear * - eq4305
    first | exact resolve eq4305 rfl | grind only
  have eq4325 : a = b ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 := by
    clear * - eq4306 eq3282
    first | exact resolve eq4306 eq3282 | exact resolve eq3282 eq4306 | grind only
  have eq4331 : c = b ∨ a = b ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq4325 eq3135
    first | simpa only [eq3135, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq4325 | grind only
  have eq4337 : c = sk2 ∨ c = sk1 ∨ a = b := by
    clear * - eq4331 bc
    first | exact resolve eq4331 bc | exact resolve bc eq4331 | grind only
  have eq4450 : (old b sk1 c) ∨ a = b ∨ c = sk1 ∨ c = sk1 ∨ a = b := by
    clear * - eq3189 eq4337
    first | exact Or.assoc3 (eq4337.imp_left (fun h : c = sk2 => superpose h eq3189)) | exact superpose eq3189 eq4337 | exact superpose eq4337 eq3189 | grind only
  have eq4451 : (old b sk1 c) ∨ a = b ∨ c = sk1 := by
    clear * - eq4450
    first | exact resolve eq4450 rfl | grind only
  have eq4465 : c = sk1 ∨ a = b := by
    clear * - eq4451 p4XY
    first | exact resolve eq4451 p4XY | exact resolve p4XY eq4451 | grind only
  have eq4770 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq3008 eq2056
    first | exact resolve eq3008 eq2056 | exact resolve eq2056 eq3008 | grind only
  have eq4796 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ sk2 = sk3 ∨ c = sk0 := by
    clear * - eq4770
    first | exact resolve eq4770 rfl | grind only
  have eq4810 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ sk2 = sk3 ∨ c = sk0 := by
    clear * - eq4796 rule_def_2_0
    first | exact resolve eq4796 rule_def_2_0 | exact resolve rule_def_2_0 eq4796 | grind only
  have eq4823 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq4810 preserve_2
    first | exact resolve eq4810 preserve_2 | exact resolve preserve_2 eq4810 | grind only
  have eq4836 : (old b sk1 sk2) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq4823 eq3135
    first | simpa only [eq3135, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq4823 | grind only
  have eq4851 : a = b ∨ (old b sk1 sk2) ∨ c = sk0 := by
    clear * - eq4836 eq3135
    first | simpa only [eq3135, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq4836 | grind only
  have eq4857 : c = b ∨ a = b ∨ (old b sk1 sk2) := by
    clear * - eq4851 eq3135
    first | simpa only [eq3135, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq4851 | grind only
  have eq4859 : (old b sk1 sk2) ∨ a = b := by
    clear * - eq4857 bc
    first | exact resolve eq4857 bc | exact resolve bc eq4857 | grind only
  have eq4866 : (old b c sk2) ∨ a = b ∨ a = b := by
    clear * - eq4859 eq4465
    first | exact Or.assoc2 (eq4465.imp_left (fun h : c = sk1 => superpose h eq4859)) | exact superpose eq4859 eq4465 | exact superpose eq4465 eq4859 | grind only
  have eq4874 : (old b c sk2) ∨ a = b := by
    clear * - eq4866
    first | exact resolve eq4866 rfl | grind only
  have eq4877 : a = b := by
    clear * - eq4874 p4XZ
    first | exact resolve eq4874 p4XZ | exact resolve p4XZ eq4874 | grind only
  have eq4926 (X0 : G) : ¬(old b b X0) := by
    clear * - p3 eq4877
    first | exact superpose p3 eq4877 | exact superpose eq4877 p3 | grind only
  have eq5016 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 := by
    clear * - eq3024 eq1688
    first | exact resolve eq3024 eq1688 | exact resolve eq1688 eq3024 | grind only
  have eq5030 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ sk2 = sk3 ∨ b = sk1 := by
    clear * - eq5016 rule_def_2_1
    first | exact resolve eq5016 rule_def_2_1 | exact resolve rule_def_2_1 eq5016 | grind only
  have eq5041 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 := by
    clear * - eq5030 preserve_2
    first | exact resolve eq5030 preserve_2 | exact resolve preserve_2 eq5030 | grind only
  have eq5052 : (old b sk1 sk2) ∨ c = sk2 ∨ b = sk1 := by
    clear * - eq5041 eq3135
    first | simpa only [eq3135, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq5041 | grind only
  have eq5568 : (old b c sk2) ∨ c = sk2 ∨ c = b ∨ b = sk1 := by
    clear * - eq5052 eq163
    first | exact Or.assoc3 (eq163.imp_left (fun h : c = sk1 => superpose h eq5052)) | exact superpose eq5052 eq163 | exact superpose eq163 eq5052 | grind only
  have eq5569 : c = sk2 ∨ c = b ∨ b = sk1 := by
    clear * - eq5568 p4XZ
    first | exact resolve eq5568 p4XZ | exact resolve p4XZ eq5568 | grind only
  have eq5571 : c = sk2 ∨ b = sk1 := by
    clear * - eq5569 bc
    first | exact resolve eq5569 bc | exact resolve bc eq5569 | grind only
  have eq5629 : (sP1 b c c) ∨ b = sk1 ∨ b = sk1 := by
    clear * - eq1734 eq5571
    first | exact Or.assoc2 (eq5571.imp_left (fun h : c = sk2 => superpose h eq1734)) | exact superpose eq1734 eq5571 | exact superpose eq5571 eq1734 | grind only
  have eq5661 : (sP1 b c c) ∨ b = sk1 := by
    clear * - eq5629
    first | exact resolve eq5629 rfl | grind only
  have eq5680 : b = sk1 := by
    clear * - eq5661 eq78
    first | exact resolve eq5661 eq78 | exact resolve eq78 eq5661 | grind only
  have eq5798 : (old b b sk3) ∨ c = sk3 ∨ c = b := by
    clear * - eq3188 eq5680
    first | exact superpose eq3188 eq5680 | exact superpose eq5680 eq3188 | grind only
  have eq5800 : (old b b sk2) ∨ c = sk2 ∨ c = b := by
    clear * - eq3191 eq5680
    first | exact superpose eq3191 eq5680 | exact superpose eq5680 eq3191 | grind only
  have eq5808 : c = sk2 ∨ c = b := by
    clear * - eq5800 eq4926
    first | exact resolve eq5800 eq4926 | exact resolve eq4926 eq5800 | grind only
  have eq5809 : c = sk3 ∨ c = b := by
    clear * - eq5798 eq4926
    first | exact resolve eq5798 eq4926 | exact resolve eq4926 eq5798 | grind only
  have eq5842 : c = sk2 := by
    clear * - eq5808 bc
    first | exact resolve eq5808 bc | exact resolve bc eq5808 | grind only
  have eq5843 : c = sk3 := by
    clear * - eq5809 bc
    first | exact resolve eq5809 bc | exact resolve bc eq5809 | grind only
  have eq6106 : c ≠ sk2 := by
    clear * - preserve_2 eq5843
    first | exact superpose preserve_2 eq5843 | exact superpose eq5843 preserve_2 | grind only
  clear * - eq6106 eq5842
  first | subsumption eq6106 eq5842 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X2 X4 ∨ old X2 X4 X0)) (old_5 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X3 ∨ ¬ old X3 X3 X4 ∨ ¬ old X4 X3 X1 ∨ old X3 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X1, b ≠ X ∨ c ≠ Y ∨ ¬ old Z Z X1 ∨ ¬ old X1 b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) b a ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z X3, c ≠ X ∨ b ≠ Y ∨ ¬ old b b X3 ∨ ¬ old X3 b a ∨ ¬ old Z Z b ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old (sF1 X Y Z) b a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X0 X1 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X2 X4 ∨ new X2 X4 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq74 (X1 X2 X3 : G) : c ≠ X1 ∨ ¬(old X2 X2 X3) ∨ ¬(old X3 b a) ∨ (new b X1 X2) := by
    clear * - imp_new_2
    first | exact resolve imp_new_2 rfl | grind only
  have eq75 (X2 X3 : G) : ¬(old X3 b a) ∨ ¬(old X2 X2 X3) ∨ (new b c X2) := by
    clear * - eq74
    first | exact resolve eq74 rfl | grind only
  have eq76 (X1 X2 X3 : G) : b ≠ X1 ∨ ¬(old b b X3) ∨ ¬(old X3 b a) ∨ ¬(old X2 X2 b) ∨ (new c X1 X2) := by
    clear * - imp_new_3
    first | exact resolve imp_new_3 rfl | grind only
  have eq77 (X2 X3 : G) : ¬(old b b X3) ∨ ¬(old X3 b a) ∨ ¬(old X2 X2 b) ∨ (new c b X2) := by
    clear * - eq76
    first | exact resolve eq76 rfl | grind only
  have eq93 (X0 : G) : ¬(new sk3 sk2 X0) ∨ sk4 = X0 := by
    clear * - prev_0 preserve_2
    first | exact resolve prev_0 preserve_2 | exact resolve preserve_2 prev_0 | grind only
  have eq95 (X0 X1 X2 X3 : G) : ¬(old X0 X0 (sF0 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP1 X1 X2 X3) := by
    clear * - eq75 rule_def_1_3
    first | exact resolve eq75 rule_def_1_3 | exact resolve rule_def_1_3 eq75 | grind only
  have eq104 (X0 X1 X2 : G) : ¬(old (sF0 X0 X1 b) b a) ∨ ¬(old X2 X2 b) ∨ (new c b X2) ∨ ¬(sP1 X0 X1 b) := by
    clear * - eq77 rule_def_1_2
    first | exact resolve eq77 rule_def_1_2 | exact resolve rule_def_1_2 eq77 | grind only
  have eq105 (X0 X1 X2 : G) : ¬(sP1 X0 X1 b) ∨ (new c b X2) ∨ ¬(old X2 X2 b) := by
    clear * - eq104 rule_def_1_3
    first | exact resolve eq104 rule_def_1_3 | exact resolve rule_def_1_3 eq104 | grind only
  have eq117 (X0 X1 X2 X3 X4 : G) : ¬(old X0 X0 b) ∨ ¬(old b b (sF1 X1 X2 X3)) ∨ ¬(old X4 X4 a) ∨ (old b X0 X4) ∨ ¬(sP2 X1 X2 X3) := by
    clear * - old_5 rule_def_2_3
    first | exact resolve old_5 rule_def_2_3 | exact resolve rule_def_2_3 old_5 | grind only
  have eq118 (X0 X1 X2 X3 X4 : G) : ¬(sP2 X1 X2 X3) ∨ ¬(old X4 X4 a) ∨ (old b X0 X4) ∨ ¬(old X0 X0 b) := by
    clear * - eq117 rule_def_2_2
    first | exact resolve eq117 rule_def_2_2 | exact resolve rule_def_2_2 eq117 | grind only
  have eq123 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq124 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq125 : (sP0 sk3 sk2 sk4) ∨ (old sk3 sk2 sk4) ∨ (sP1 sk3 sk2 sk4) ∨ (sP2 sk3 sk2 sk4) := by
    clear * - new_imp preserve_2
    first | exact resolve new_imp preserve_2 | exact resolve preserve_2 new_imp | grind only
  have eq128 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq123 rule_def_0_2
    first | exact resolve eq123 rule_def_0_2 | exact resolve rule_def_0_2 eq123 | grind only
  have eq129 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq123 rule_def_0_1
    first | exact resolve eq123 rule_def_0_1 | exact resolve rule_def_0_1 eq123 | grind only
  have eq130 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 := by
    clear * - eq123 rule_def_0_0
    first | exact resolve eq123 rule_def_0_0 | exact resolve rule_def_0_0 eq123 | grind only
  have eq131 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq129 rule_def_1_0
    first | exact resolve eq129 rule_def_1_0 | exact resolve rule_def_1_0 eq129 | grind only
  have eq132 : (old sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq131 rule_def_2_1
    first | exact resolve eq131 rule_def_2_1 | exact resolve rule_def_2_1 eq131 | grind only
  have eq133 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ c = sk3 := by
    clear * - eq124 rule_def_0_2
    first | exact resolve eq124 rule_def_0_2 | exact resolve rule_def_0_2 eq124 | grind only
  have eq134 : (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ b = sk2 := by
    clear * - eq124 rule_def_0_1
    first | exact resolve eq124 rule_def_0_1 | exact resolve rule_def_0_1 eq124 | grind only
  have eq135 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 := by
    clear * - eq124 rule_def_0_0
    first | exact resolve eq124 rule_def_0_0 | exact resolve rule_def_0_0 eq124 | grind only
  have eq136 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk2 := by
    clear * - eq134 rule_def_2_1
    first | exact resolve eq134 rule_def_2_1 | exact resolve rule_def_2_1 eq134 | grind only
  have eq144 : (sP1 sk3 sk2 sk4) ∨ (old sk3 sk2 sk4) ∨ (sP2 sk3 sk2 sk4) ∨ c = sk4 := by
    clear * - eq125 rule_def_0_2
    first | exact resolve eq125 rule_def_0_2 | exact resolve rule_def_0_2 eq125 | grind only
  have eq145 : (old sk3 sk2 sk4) ∨ (sP1 sk3 sk2 sk4) ∨ (sP2 sk3 sk2 sk4) ∨ b = sk2 := by
    clear * - eq125 rule_def_0_1
    first | exact resolve eq125 rule_def_0_1 | exact resolve rule_def_0_1 eq125 | grind only
  have eq146 : (sP1 sk3 sk2 sk4) ∨ (old sk3 sk2 sk4) ∨ (sP2 sk3 sk2 sk4) ∨ a = sk3 := by
    clear * - eq125 rule_def_0_0
    first | exact resolve eq125 rule_def_0_0 | exact resolve rule_def_0_0 eq125 | grind only
  have eq147 : (sP1 sk3 sk2 sk4) ∨ (old sk3 sk2 sk4) ∨ b = sk2 := by
    clear * - eq145 rule_def_2_1
    first | exact resolve eq145 rule_def_2_1 | exact resolve rule_def_2_1 eq145 | grind only
  have eq158 : (old sk1 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq136 rule_def_1_1
    first | exact resolve eq136 rule_def_1_1 | exact resolve rule_def_1_1 eq136 | grind only
  have eq159 : (old sk1 sk2 sk3) ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq136 rule_def_1_0
    first | exact resolve eq136 rule_def_1_0 | exact resolve rule_def_1_0 eq136 | grind only
  have eq170 : (old sk3 sk2 sk4) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq147 rule_def_1_1
    first | exact resolve eq147 rule_def_1_1 | exact resolve rule_def_1_1 eq147 | grind only
  have eq171 : (old sk3 sk2 sk4) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq147 rule_def_1_0
    first | exact resolve eq147 rule_def_1_0 | exact resolve rule_def_1_0 eq147 | grind only
  have eq175 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ c = sk2 ∨ ¬(old X0 sk2 sk3) ∨ b = sk2 ∨ (old sk2 sk4 X1) := by
    clear * - eq170 old_1
    first | exact resolve eq170 old_1 | exact resolve old_1 eq170 | grind only
  have eq206 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := by
    clear * - eq95 rule_def_1_2
    first | exact resolve eq95 rule_def_1_2 | exact resolve rule_def_1_2 eq95 | grind only
  have eq207 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new b c X0) := by
    clear * - eq206
    first | exact resolve eq206 rfl | grind only
  have eq209 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq128 rule_def_1_1
    first | exact resolve eq128 rule_def_1_1 | exact resolve rule_def_1_1 eq128 | grind only
  have eq211 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq209 rule_def_2_0
    first | exact resolve eq209 rule_def_2_0 | exact resolve rule_def_2_0 eq209 | grind only
  have eq235 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq130 rule_def_1_1
    first | exact resolve eq130 rule_def_1_1 | exact resolve rule_def_1_1 eq130 | grind only
  have eq237 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq235 rule_def_2_0
    first | exact resolve eq235 rule_def_2_0 | exact resolve rule_def_2_0 eq235 | grind only
  have eq274 : (sP2 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq133 rule_def_1_1
    first | exact resolve eq133 rule_def_1_1 | exact resolve rule_def_1_1 eq133 | grind only
  have eq278 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq274 rule_def_2_0
    first | exact resolve eq274 rule_def_2_0 | exact resolve rule_def_2_0 eq274 | grind only
  have eq321 : (sP2 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ c = sk2 := by
    clear * - eq135 rule_def_1_1
    first | exact resolve eq135 rule_def_1_1 | exact resolve rule_def_1_1 eq135 | grind only
  have eq323 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq321 rule_def_2_0
    first | exact resolve eq321 rule_def_2_0 | exact resolve rule_def_2_0 eq321 | grind only
  have eq332 : (sP2 sk3 sk2 sk4) ∨ (old sk3 sk2 sk4) ∨ c = sk4 ∨ c = sk2 := by
    clear * - eq144 rule_def_1_1
    first | exact resolve eq144 rule_def_1_1 | exact resolve rule_def_1_1 eq144 | grind only
  have eq343 : (sP2 sk3 sk2 sk4) ∨ (old sk3 sk2 sk4) ∨ a = sk3 ∨ c = sk2 := by
    clear * - eq146 rule_def_1_1
    first | exact resolve eq146 rule_def_1_1 | exact resolve rule_def_1_1 eq146 | grind only
  have eq354 : (new b c sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk2 := by
    clear * - eq207 eq136
    first | exact resolve eq207 eq136 | exact resolve eq136 eq207 | grind only
  have eq357 : (new b c sk4) ∨ (old sk3 sk2 sk4) ∨ b = sk2 := by
    clear * - eq207 eq147
    first | exact resolve eq207 eq147 | exact resolve eq147 eq207 | grind only
  have eq361 (X0 : G) : ¬(new b c X0) ∨ b = sk2 ∨ (old sk1 sk2 sk3) ∨ sk3 = X0 := by
    clear * - eq354 prev_0
    first | exact resolve eq354 prev_0 | exact resolve prev_0 eq354 | grind only
  have eq381 : (old sk3 sk2 sk4) ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq332 rule_def_2_0
    first | exact resolve eq332 rule_def_2_0 | exact resolve rule_def_2_0 eq332 | grind only
  have eq401 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ c = sk2 ∨ c = sk3 ∨ ¬(old X0 sk2 sk3) ∨ c = sk4 ∨ (old sk2 sk4 X1) := by
    clear * - eq381 old_1
    first | exact resolve eq381 old_1 | exact resolve old_1 eq381 | grind only
  have eq431 : (old sk3 sk2 sk4) ∨ a = sk3 ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq343 rule_def_2_0
    first | exact resolve eq343 rule_def_2_0 | exact resolve rule_def_2_0 eq343 | grind only
  have eq523 : b = sk2 ∨ (old sk1 sk2 sk3) ∨ sk3 = sk4 ∨ (old sk3 sk2 sk4) ∨ b = sk2 := by
    clear * - eq361 eq357
    first | exact resolve eq361 eq357 | exact resolve eq357 eq361 | grind only
  have eq524 : (old sk3 sk2 sk4) ∨ (old sk1 sk2 sk3) ∨ sk3 = sk4 ∨ b = sk2 := by
    clear * - eq523
    first | exact resolve eq523 rfl | grind only
  have eq1155 : c = sk2 ∨ ¬(old sk1 sk2 sk3) ∨ b = sk2 ∨ (old sk2 sk4 sk0) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq175 eq211
    first | exact resolve eq175 eq211 | exact resolve eq211 eq175 | grind only
  have eq1170 : (old sk2 sk4 sk0) ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq1155 eq158
    first | exact resolve eq1155 eq158 | exact resolve eq158 eq1155 | grind only
  have eq4550 : b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ (new sk2 sk4 sk0) := by
    clear * - eq1170 imp_new_0
    first | exact resolve eq1170 imp_new_0 | exact resolve imp_new_0 eq1170 | grind only
  have eq4557 : c = sk1 ∨ c = sk2 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4550 preserve_3
    first | exact resolve eq4550 preserve_3 | exact resolve preserve_3 eq4550 | grind only
  have eq4594 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ c = sk2 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq158 eq4557
    first | exact Or.assoc3 (eq4557.imp_left (fun h : c = sk1 => superpose h eq158)) | exact superpose eq158 eq4557 | exact superpose eq4557 eq158 | grind only
  have eq4666 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 := by
    clear * - eq4594
    first | exact resolve eq4594 rfl | grind only
  have eq4687 : c = sk2 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4666 p4YZ
    first | exact resolve eq4666 p4YZ | exact resolve p4YZ eq4666 | grind only
  have eq4728 : ¬(new c sk4 sk0) ∨ b = sk2 ∨ c = sk0 := by
    clear * - preserve_3 eq4687
    first | exact (eq4687.imp_left (fun h : c = sk2 => superpose h preserve_3)) | exact superpose preserve_3 eq4687 | exact superpose eq4687 preserve_3 | grind only
  have eq4735 : (sP1 sk1 c sk3) ∨ (old sk1 c sk3) ∨ c = b ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq136 eq4687
    first | exact Or.assoc3 (eq4687.imp_left (fun h : c = sk2 => superpose h eq136)) | exact superpose eq136 eq4687 | exact superpose eq4687 eq136 | grind only
  have eq4739 : (old sk1 c sk3) ∨ c = b ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq159 eq4687
    first | exact Or.assoc3 (eq4687.imp_left (fun h : c = sk2 => superpose h eq159)) | exact superpose eq159 eq4687 | exact superpose eq4687 eq159 | grind only
  have eq4742 : (old sk3 c sk4) ∨ c = b ∨ b = sk3 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq171 eq4687
    first | exact Or.assoc3 (eq4687.imp_left (fun h : c = sk2 => superpose h eq171)) | exact superpose eq171 eq4687 | exact superpose eq4687 eq171 | grind only
  have eq4761 : (old sk3 c sk4) ∨ (old sk1 c sk3) ∨ sk3 = sk4 ∨ c = b ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq524 eq4687
    first | exact Or.assoc4 (eq4687.imp_left (fun h : c = sk2 => superpose h eq524)) | exact superpose eq524 eq4687 | exact superpose eq4687 eq524 | grind only
  have eq4793 : (old sk1 c sk3) ∨ sk3 = sk4 ∨ c = b ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4761 p4XZ
    first | exact resolve eq4761 p4XZ | exact resolve p4XZ eq4761 | grind only
  have eq4806 : c = b ∨ b = sk3 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4742 p4XZ
    first | exact resolve eq4742 p4XZ | exact resolve p4XZ eq4742 | grind only
  have eq4807 : c = b ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4739 p4XZ
    first | exact resolve eq4739 p4XZ | exact resolve p4XZ eq4739 | grind only
  have eq4811 : (sP1 sk1 c sk3) ∨ c = b ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4735 p4XZ
    first | exact resolve eq4735 p4XZ | exact resolve p4XZ eq4735 | grind only
  have eq4816 : sk3 = sk4 ∨ c = b ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4793 p4XZ
    first | exact resolve eq4793 p4XZ | exact resolve p4XZ eq4793 | grind only
  have eq4817 : b = sk3 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4806 bc
    first | exact resolve eq4806 bc | exact resolve bc eq4806 | grind only
  have eq4818 : b = sk1 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4807 bc
    first | exact resolve eq4807 bc | exact resolve bc eq4807 | grind only
  have eq4820 : (sP1 sk1 c sk3) ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4811 bc
    first | exact resolve eq4811 bc | exact resolve bc eq4811 | grind only
  have eq4821 : sk3 = sk4 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4816 bc
    first | exact resolve eq4816 bc | exact resolve bc eq4816 | grind only
  have eq5063 : (old sk0 sk0 b) ∨ c = b ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq211 eq4818
    first | exact Or.assoc3 (eq4818.imp_left (fun h : b = sk1 => superpose h eq211)) | exact superpose eq211 eq4818 | exact superpose eq4818 eq211 | grind only
  have eq5142 : (old sk0 sk0 b) ∨ c = b ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq5063
    first | exact resolve eq5063 rfl | grind only
  have eq5167 : (old sk0 sk0 b) ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq5142 bc
    first | exact resolve eq5142 bc | exact resolve bc eq5142 | grind only
  have eq5343 : ¬(new c sk3 sk0) ∨ b = sk2 ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4728 eq4821
    first | exact Or.assoc3 (eq4821.imp_left (fun h : sk3 = sk4 => superpose h eq4728)) | exact superpose eq4728 eq4821 | exact superpose eq4821 eq4728 | grind only
  have eq5350 : ¬(new c sk3 sk0) ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq5343
    first | exact resolve eq5343 rfl | grind only
  have eq5400 : (sP1 sk1 c b) ∨ b = sk2 ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq4820 eq4817
    first | exact Or.assoc3 (eq4817.imp_left (fun h : b = sk3 => superpose h eq4820)) | exact superpose eq4820 eq4817 | exact superpose eq4817 eq4820 | grind only
  have eq5407 : (sP1 sk1 c b) ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq5400
    first | exact resolve eq5400 rfl | grind only
  have eq5673 : ¬(new c b sk0) ∨ b = sk2 ∨ c = sk0 ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq5350 eq4817
    first | exact Or.assoc3 (eq4817.imp_left (fun h : b = sk3 => superpose h eq5350)) | exact superpose eq5350 eq4817 | exact superpose eq4817 eq5350 | grind only
  have eq5680 : ¬(new c b sk0) ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq5673
    first | exact resolve eq5673 rfl | grind only
  have eq5735 (X0 : G) : ¬(old X0 X0 b) ∨ c = sk0 ∨ (new c b X0) ∨ b = sk2 := by
    clear * - eq5407 eq105
    first | exact resolve eq5407 eq105 | exact resolve eq105 eq5407 | grind only
  have eq8424 : c = sk0 ∨ (new c b sk0) ∨ b = sk2 ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq5735 eq5167
    first | exact resolve eq5735 eq5167 | exact resolve eq5167 eq5735 | grind only
  have eq8439 : c = sk0 ∨ (new c b sk0) ∨ b = sk2 := by
    clear * - eq8424
    first | exact resolve eq8424 rfl | grind only
  have eq8442 : b = sk2 ∨ c = sk0 := by
    clear * - eq8439 eq5680
    first | exact resolve eq8439 eq5680 | exact resolve eq5680 eq8439 | grind only
  have eq8502 : ¬(new b sk4 sk0) ∨ c = sk0 := by
    clear * - preserve_3 eq8442
    first | exact (eq8442.imp_left (fun h : b = sk2 => superpose h preserve_3)) | exact superpose preserve_3 eq8442 | exact superpose eq8442 preserve_3 | grind only
  have eq8504 (X0 : G) : ¬(new sk3 b X0) ∨ sk4 = X0 ∨ c = sk0 := by
    clear * - eq93 eq8442
    first | exact Or.assoc2 (eq8442.imp_left (fun h : b = sk2 => superpose h eq93)) | exact superpose eq93 eq8442 | exact superpose eq8442 eq93 | grind only
  have eq8513 : (old sk1 b sk3) ∨ c = sk3 ∨ c = b ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq278 eq8442
    first | exact Or.assoc4 (eq8442.imp_left (fun h : b = sk2 => superpose h eq278)) | exact superpose eq278 eq8442 | exact superpose eq8442 eq278 | grind only
  have eq8517 : (sP2 sk1 b sk3) ∨ (old sk1 b sk3) ∨ a = sk1 ∨ c = b ∨ c = sk0 := by
    clear * - eq321 eq8442
    first | exact Or.assoc4 (eq8442.imp_left (fun h : b = sk2 => superpose h eq321)) | exact superpose eq321 eq8442 | exact superpose eq8442 eq321 | grind only
  have eq8519 : (old sk1 b sk3) ∨ a = sk1 ∨ c = b ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq323 eq8442
    first | exact Or.assoc4 (eq8442.imp_left (fun h : b = sk2 => superpose h eq323)) | exact superpose eq323 eq8442 | exact superpose eq8442 eq323 | grind only
  have eq8523 : (sP2 sk3 b sk4) ∨ (old sk3 b sk4) ∨ a = sk3 ∨ c = b ∨ c = sk0 := by
    clear * - eq343 eq8442
    first | exact Or.assoc4 (eq8442.imp_left (fun h : b = sk2 => superpose h eq343)) | exact superpose eq343 eq8442 | exact superpose eq8442 eq343 | grind only
  have eq8535 : (old sk3 b sk4) ∨ a = sk3 ∨ c = b ∨ c = sk3 ∨ c = sk0 := by
    clear * - eq431 eq8442
    first | exact Or.assoc4 (eq8442.imp_left (fun h : b = sk2 => superpose h eq431)) | exact superpose eq431 eq8442 | exact superpose eq8442 eq431 | grind only
  have eq8559 : (old sk3 b sk4) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 := by
    clear * - eq8535 bc
    first | exact resolve eq8535 bc | exact resolve bc eq8535 | grind only
  have eq8562 : (sP2 sk3 b sk4) ∨ (old sk3 b sk4) ∨ a = sk3 ∨ c = sk0 := by
    clear * - eq8523 bc
    first | exact resolve eq8523 bc | exact resolve bc eq8523 | grind only
  have eq8565 : (old sk1 b sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq8519 bc
    first | exact resolve eq8519 bc | exact resolve bc eq8519 | grind only
  have eq8566 : (sP2 sk1 b sk3) ∨ (old sk1 b sk3) ∨ a = sk1 ∨ c = sk0 := by
    clear * - eq8517 bc
    first | exact resolve eq8517 bc | exact resolve bc eq8517 | grind only
  have eq8568 : (old sk1 b sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq8513 bc
    first | exact resolve eq8513 bc | exact resolve bc eq8513 | grind only
  have eq11967 : c = sk2 ∨ c = sk3 ∨ ¬(old sk1 sk2 sk3) ∨ c = sk4 ∨ (old sk2 sk4 sk0) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq401 eq211
    first | exact resolve eq401 eq211 | exact resolve eq211 eq401 | grind only
  have eq11998 : (old sk2 sk4 sk0) ∨ c = sk3 ∨ c = sk4 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq11967 eq278
    first | exact resolve eq11967 eq278 | exact resolve eq278 eq11967 | grind only
  have eq22696 : c = sk3 ∨ c = sk4 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ (new sk2 sk4 sk0) := by
    clear * - eq11998 imp_new_0
    first | exact resolve eq11998 imp_new_0 | exact resolve imp_new_0 eq11998 | grind only
  have eq22711 : c = sk4 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq22696 preserve_3
    first | exact resolve eq22696 preserve_3 | exact resolve preserve_3 eq22696 | grind only
  have eq22716 : (new sk3 sk2 c) ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - preserve_2 eq22711
    first | exact (eq22711.imp_left (fun h : c = sk4 => superpose h preserve_2)) | exact superpose preserve_2 eq22711 | exact superpose eq22711 preserve_2 | grind only
  have eq23633 : (new sk3 b c) ∨ c = sk3 ∨ c = b ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 := by
    clear * - eq22716 eq8442
    first | exact Or.assoc5 (eq8442.imp_left (fun h : b = sk2 => superpose h eq22716)) | exact superpose eq22716 eq8442 | exact superpose eq8442 eq22716 | grind only
  have eq23635 : (new sk3 b c) ∨ c = sk3 ∨ c = b ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq23633
    first | exact resolve eq23633 rfl | grind only
  have eq23643 : (new sk3 b c) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq23635 bc
    first | exact resolve eq23635 bc | exact resolve bc eq23635 | grind only
  have eq23689 : c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk4 ∨ c = sk0 := by
    clear * - eq23643 eq8504
    first | exact resolve eq23643 eq8504 | exact resolve eq8504 eq23643 | grind only
  have eq23701 : c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 := by
    clear * - eq23689
    first | exact resolve eq23689 rfl | grind only
  have eq23992 : ¬(new b c sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 := by
    clear * - eq8502 eq23701
    first | exact Or.assoc2 (eq23701.imp_left (fun h : c = sk4 => superpose h eq8502)) | exact superpose eq8502 eq23701 | exact superpose eq23701 eq8502 | grind only
  have eq23997 : (old sk3 b c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 := by
    clear * - eq8559 eq23701
    first | exact Or.assoc4 (eq23701.imp_left (fun h : c = sk4 => superpose h eq8559)) | exact superpose eq8559 eq23701 | exact superpose eq23701 eq8559 | grind only
  have eq24014 : (old sk3 b c) ∨ a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq23997
    first | exact resolve eq23997 rfl | grind only
  have eq24019 : ¬(new b c sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq23992
    first | exact resolve eq23992 rfl | grind only
  have eq24064 : a = sk3 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq24014 p4XY
    first | exact resolve eq24014 p4XY | exact resolve p4XY eq24014 | grind only
  have eq24427 : (old sk1 b a) ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq8568 eq24064
    first | exact Or.assoc4 (eq24064.imp_left (fun h : a = sk3 => superpose h eq8568)) | exact superpose eq8568 eq24064 | exact superpose eq24064 eq8568 | grind only
  have eq24457 : (old sk1 b a) ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 := by
    clear * - eq24427
    first | exact resolve eq24427 rfl | grind only
  have eq24552 : (old sk1 b a) ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 := by
    clear * - eq24457 ac
    first | exact resolve eq24457 ac | exact resolve ac eq24457 | grind only
  have eq25357 (X0 : G) : ¬(old X0 X0 sk1) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 ∨ (new b c X0) := by
    clear * - eq24552 eq75
    first | exact resolve eq24552 eq75 | exact resolve eq75 eq24552 | grind only
  have eq35110 : c = sk0 ∨ c = sk3 ∨ c = sk1 ∨ (new b c sk0) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq25357 eq211
    first | exact resolve eq25357 eq211 | exact resolve eq211 eq25357 | grind only
  have eq35118 : c = sk0 ∨ c = sk3 ∨ c = sk1 ∨ (new b c sk0) := by
    clear * - eq35110
    first | exact resolve eq35110 rfl | grind only
  have eq35121 : c = sk3 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq35118 eq24019
    first | exact resolve eq35118 eq24019 | exact resolve eq24019 eq35118 | grind only
  have eq35425 : (sP2 c b sk4) ∨ (old c b sk4) ∨ a = c ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq8562 eq35121
    first | exact Or.assoc4 (eq35121.imp_left (fun h : c = sk3 => superpose h eq8562)) | exact superpose eq8562 eq35121 | exact superpose eq35121 eq8562 | grind only
  have eq35427 : (old sk1 b c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq8565 eq35121
    first | exact Or.assoc4 (eq35121.imp_left (fun h : c = sk3 => superpose h eq8565)) | exact superpose eq8565 eq35121 | exact superpose eq35121 eq8565 | grind only
  have eq35468 : (old sk1 b c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq35427
    first | exact resolve eq35427 rfl | grind only
  have eq35470 : (sP2 c b sk4) ∨ (old c b sk4) ∨ a = c ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq35425
    first | exact resolve eq35425 rfl | grind only
  have eq35558 : a = sk1 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq35468 p4XY
    first | exact resolve eq35468 p4XY | exact resolve p4XY eq35468 | grind only
  have eq35560 : (sP2 c b sk4) ∨ a = c ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq35470 p4YZ
    first | exact resolve eq35470 p4YZ | exact resolve p4YZ eq35470 | grind only
  have eq35648 : (sP2 c b sk4) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq35560 ac
    first | exact resolve eq35560 ac | exact resolve ac eq35560 | grind only
  have eq35761 : (old sk0 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq211 eq35558
    first | exact Or.assoc3 (eq35558.imp_left (fun h : a = sk1 => superpose h eq211)) | exact superpose eq211 eq35558 | exact superpose eq35558 eq211 | grind only
  have eq36013 : (old sk0 sk0 a) ∨ a = c ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq35761
    first | exact resolve eq35761 rfl | grind only
  have eq36040 : (old sk0 sk0 a) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq36013 ac
    first | exact resolve eq36013 ac | exact resolve ac eq36013 | grind only
  have eq36262 : (old sk4 sk4 b) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq35648 rule_def_2_4
    first | exact resolve eq35648 rule_def_2_4 | exact resolve rule_def_2_4 eq35648 | grind only
  have eq36266 (X0 X1 : G) : ¬(old X1 X1 b) ∨ c = sk1 ∨ ¬(old X0 X0 a) ∨ (old b X1 X0) ∨ c = sk0 := by
    clear * - eq35648 eq118
    first | exact resolve eq35648 eq118 | exact resolve eq118 eq35648 | grind only
  have eq61829 (X0 : G) : c = sk1 ∨ ¬(old X0 X0 a) ∨ (old b sk4 X0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq36266 eq36262
    first | exact resolve eq36266 eq36262 | exact resolve eq36262 eq36266 | grind only
  have eq61832 (X0 : G) : ¬(old X0 X0 a) ∨ c = sk1 ∨ (old b sk4 X0) ∨ c = sk0 := by
    clear * - eq61829
    first | exact resolve eq61829 rfl | grind only
  have eq61861 : c = sk1 ∨ (old b sk4 sk0) ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq61832 eq36040
    first | exact resolve eq61832 eq36040 | exact resolve eq36040 eq61832 | grind only
  have eq61862 : (old b sk4 sk0) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq61861
    first | exact resolve eq61861 rfl | grind only
  have eq61924 : c = sk1 ∨ c = sk0 ∨ (new b sk4 sk0) := by
    clear * - eq61862 imp_new_0
    first | exact resolve eq61862 imp_new_0 | exact resolve imp_new_0 eq61862 | grind only
  have eq61942 : c = sk1 ∨ c = sk0 := by
    clear * - eq61924 eq8502
    first | exact resolve eq61924 eq8502 | exact resolve eq8502 eq61924 | grind only
  have eq62008 : (old sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq132 eq61942
    first | exact Or.assoc2 (eq61942.imp_left (fun h : c = sk1 => superpose h eq132)) | exact superpose eq132 eq61942 | exact superpose eq61942 eq132 | grind only
  have eq62023 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 := by
    clear * - eq237 eq61942
    first | exact Or.assoc3 (eq61942.imp_left (fun h : c = sk1 => superpose h eq237)) | exact superpose eq237 eq61942 | exact superpose eq61942 eq237 | grind only
  have eq62146 : (sP2 c b sk3) ∨ (old c b sk3) ∨ a = c ∨ c = sk0 ∨ c = sk0 := by
    clear * - eq8566 eq61942
    first | exact Or.assoc4 (eq61942.imp_left (fun h : c = sk1 => superpose h eq8566)) | exact superpose eq8566 eq61942 | exact superpose eq61942 eq8566 | grind only
  have eq62226 : (sP2 c b sk3) ∨ (old c b sk3) ∨ a = c ∨ c = sk0 := by
    clear * - eq62146
    first | exact resolve eq62146 rfl | grind only
  have eq62266 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq62023
    first | exact resolve eq62023 rfl | grind only
  have eq62298 : (sP2 c b sk3) ∨ a = c ∨ c = sk0 := by
    clear * - eq62226 p4YZ
    first | exact resolve eq62226 p4YZ | exact resolve p4YZ eq62226 | grind only
  have eq62345 : a = sk0 ∨ c = sk0 := by
    clear * - eq62266 p4XY
    first | exact resolve eq62266 p4XY | exact resolve p4XY eq62266 | grind only
  have eq62348 : c = sk0 ∨ b = sk0 := by
    clear * - eq62008 p4XY
    first | exact resolve eq62008 p4XY | exact resolve p4XY eq62008 | grind only
  have eq62375 : (sP2 c b sk3) ∨ c = sk0 := by
    clear * - eq62298 ac
    first | exact resolve eq62298 ac | exact resolve ac eq62298 | grind only
  have eq62682 : (old c c sk1) ∨ c = b ∨ b = sk0 := by
    clear * - eq132 eq62348
    first | exact Or.assoc2 (eq62348.imp_left (fun h : c = sk0 => superpose h eq132)) | exact superpose eq132 eq62348 | exact superpose eq62348 eq132 | grind only
  have eq62781 : c = b ∨ b = sk0 := by
    clear * - eq62682 p4XZ
    first | exact resolve eq62682 p4XZ | exact resolve p4XZ eq62682 | grind only
  have eq62800 : b = sk0 := by
    clear * - eq62781 bc
    first | exact resolve eq62781 bc | exact resolve bc eq62781 | grind only
  have eq62953 : a = b ∨ c = b := by
    clear * - eq62345 eq62800
    first | exact superpose eq62345 eq62800 | exact superpose eq62800 eq62345 | grind only
  have eq62954 : a = b := by
    clear * - eq62953 bc
    first | exact resolve eq62953 bc | exact resolve bc eq62953 | grind only
  have eq63073 (X0 : G) : ¬(old b b X0) := by
    clear * - p3 eq62954
    first | exact superpose p3 eq62954 | exact superpose eq62954 p3 | grind only
  have eq63428 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := by
    clear * - eq63073 rule_def_2_2
    first | exact resolve eq63073 rule_def_2_2 | exact resolve rule_def_2_2 eq63073 | grind only
  have eq64528 : c = sk0 := by
    clear * - eq62375 eq63428
    first | exact resolve eq62375 eq63428 | exact resolve eq63428 eq62375 | grind only
  have eq64548 : c = b := by
    clear * - eq64528 eq62800
    first | simpa only [eq62800, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq64528 | grind only
  clear * - eq64548 bc
  first | subsumption eq64548 bc | grind only


set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (new_new : new a b c) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X2 X4 ∨ old X2 X4 X0)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X0 X1 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X2 X4 ∨ new X2 X4 X0)) (old_2 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X4 X2 X3 ∨ ¬ old X5 X5 X4 ∨ X0 = X5)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X1 ∨ X2 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old (sF1 X Y Z) b a ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4 X5, ¬ new X0 X0 X1 ∨ ¬ new X1 X2 X3 ∨ ¬ new X4 X2 X3 ∨ ¬ new X5 X5 X4 ∨ X0 = X5) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq83 (X0 X1 X2 : G) : (new X2 X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - rule_def_1_2 imp_new_0
    first | exact resolve rule_def_1_2 imp_new_0 | exact resolve imp_new_0 rule_def_1_2 | grind only
  have eq86 (X0 X1 : G) : ¬(sP1 X0 X1 c) := by
    clear * - rule_def_1_2 p4YZ
    first | exact resolve rule_def_1_2 p4YZ | exact resolve p4YZ rule_def_1_2 | grind only
  have eq88 (X0 X1 X2 : G) : (new (sF0 X0 X1 X2) b a) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - rule_def_1_3 imp_new_0
    first | exact resolve rule_def_1_3 imp_new_0 | exact resolve imp_new_0 rule_def_1_3 | grind only
  have eq96 (X0 : G) : ¬(new sk1 sk2 X0) ∨ sk3 = X0 := by
    clear * - prev_0 preserve_1
    first | exact resolve prev_0 preserve_1 | exact resolve preserve_1 prev_0 | grind only
  have eq98 (X0 : G) : ¬(new sk5 sk5 X0) ∨ sk4 = X0 := by
    clear * - prev_0 preserve_3
    first | exact resolve prev_0 preserve_3 | exact resolve preserve_3 prev_0 | grind only
  have eq105 (X0 X1 X2 X3 X4 : G) : ¬(old X0 b (sF1 X1 X2 X3)) ∨ ¬(old X4 X4 X0) ∨ (old b a X4) ∨ ¬(sP2 X1 X2 X3) := by
    clear * - old_1 rule_def_2_3
    first | exact resolve old_1 rule_def_2_3 | exact resolve rule_def_2_3 old_1 | grind only
  have eq107 (X0 X1 : G) : ¬(new X1 X1 X0) ∨ ¬(new X0 b a) ∨ (new b c X1) := by
    clear * - prev_1 new_new
    first | exact resolve prev_1 new_new | exact resolve new_new prev_1 | grind only
  have eq109 (X0 X1 : G) : ¬(new X1 X1 X0) ∨ ¬(new X0 sk2 sk1) ∨ (new sk2 sk3 X1) := by
    clear * - prev_1 preserve_1
    first | exact resolve prev_1 preserve_1 | exact resolve preserve_1 prev_1 | grind only
  have eq110 (X0 X1 : G) : ¬(new X1 X1 X0) ∨ ¬(new X0 sk2 sk4) ∨ (new sk2 sk3 X1) := by
    clear * - prev_1 preserve_2
    first | exact resolve prev_1 preserve_2 | exact resolve preserve_2 prev_1 | grind only
  have eq130 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq131 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq132 : (sP0 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ (sP1 sk4 sk2 sk3) ∨ (sP2 sk4 sk2 sk3) := by
    clear * - new_imp preserve_2
    first | exact resolve new_imp preserve_2 | exact resolve preserve_2 new_imp | grind only
  have eq133 : (sP0 sk5 sk5 sk4) ∨ (old sk5 sk5 sk4) ∨ (sP1 sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) := by
    clear * - new_imp preserve_3
    first | exact resolve new_imp preserve_3 | exact resolve preserve_3 new_imp | grind only
  have eq138 : ¬(new sk1 sk2 sk4) ∨ (new sk2 sk3 sk0) := by
    clear * - eq110 preserve_0
    first | exact resolve eq110 preserve_0 | exact resolve preserve_0 eq110 | grind only
  have eq142 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq130 rule_def_0_2
    first | exact resolve eq130 rule_def_0_2 | exact resolve rule_def_0_2 eq130 | grind only
  have eq143 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq130 rule_def_0_1
    first | exact resolve eq130 rule_def_0_1 | exact resolve rule_def_0_1 eq130 | grind only
  have eq144 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 := by
    clear * - eq130 rule_def_0_0
    first | exact resolve eq130 rule_def_0_0 | exact resolve rule_def_0_0 eq130 | grind only
  have eq145 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq143 rule_def_1_0
    first | exact resolve eq143 rule_def_1_0 | exact resolve rule_def_1_0 eq143 | grind only
  have eq146 : (old sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq145 rule_def_2_1
    first | exact resolve eq145 rule_def_2_1 | exact resolve rule_def_2_1 eq145 | grind only
  have eq148 (X0 X1 X2 X3 : G) : ¬(old sk1 X1 X2) ∨ ¬(old X0 X1 X2) ∨ b = sk0 ∨ ¬(old X3 X3 X0) ∨ sk0 = X3 := by
    clear * - eq146 old_2
    first | exact resolve eq146 old_2 | exact resolve old_2 eq146 | grind only
  have eq154 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ c = sk3 := by
    clear * - eq131 rule_def_0_2
    first | exact resolve eq131 rule_def_0_2 | exact resolve rule_def_0_2 eq131 | grind only
  have eq155 : (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ b = sk2 := by
    clear * - eq131 rule_def_0_1
    first | exact resolve eq131 rule_def_0_1 | exact resolve rule_def_0_1 eq131 | grind only
  have eq156 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 := by
    clear * - eq131 rule_def_0_0
    first | exact resolve eq131 rule_def_0_0 | exact resolve rule_def_0_0 eq131 | grind only
  have eq157 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk2 := by
    clear * - eq155 rule_def_2_1
    first | exact resolve eq155 rule_def_2_1 | exact resolve rule_def_2_1 eq155 | grind only
  have eq158 : (sP1 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ (sP2 sk4 sk2 sk3) ∨ c = sk3 := by
    clear * - eq132 rule_def_0_2
    first | exact resolve eq132 rule_def_0_2 | exact resolve rule_def_0_2 eq132 | grind only
  have eq159 : (old sk4 sk2 sk3) ∨ (sP1 sk4 sk2 sk3) ∨ (sP2 sk4 sk2 sk3) ∨ b = sk2 := by
    clear * - eq132 rule_def_0_1
    first | exact resolve eq132 rule_def_0_1 | exact resolve rule_def_0_1 eq132 | grind only
  have eq160 : (sP1 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ (sP2 sk4 sk2 sk3) ∨ a = sk4 := by
    clear * - eq132 rule_def_0_0
    first | exact resolve eq132 rule_def_0_0 | exact resolve rule_def_0_0 eq132 | grind only
  have eq161 : (sP1 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ b = sk2 := by
    clear * - eq159 rule_def_2_1
    first | exact resolve eq159 rule_def_2_1 | exact resolve rule_def_2_1 eq159 | grind only
  have eq162 : (sP1 sk5 sk5 sk4) ∨ (old sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) ∨ c = sk4 := by
    clear * - eq133 rule_def_0_2
    first | exact resolve eq133 rule_def_0_2 | exact resolve rule_def_0_2 eq133 | grind only
  have eq163 : (old sk5 sk5 sk4) ∨ (sP1 sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) ∨ b = sk5 := by
    clear * - eq133 rule_def_0_1
    first | exact resolve eq133 rule_def_0_1 | exact resolve rule_def_0_1 eq133 | grind only
  have eq164 : (sP1 sk5 sk5 sk4) ∨ (old sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) ∨ a = sk5 := by
    clear * - eq133 rule_def_0_0
    first | exact resolve eq133 rule_def_0_0 | exact resolve rule_def_0_0 eq133 | grind only
  have eq165 : (old sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) ∨ b = sk5 := by
    clear * - eq163 rule_def_1_0
    first | exact resolve eq163 rule_def_1_0 | exact resolve rule_def_1_0 eq163 | grind only
  have eq166 : (old sk5 sk5 sk4) ∨ b = sk5 := by
    clear * - eq165 rule_def_2_1
    first | exact resolve eq165 rule_def_2_1 | exact resolve rule_def_2_1 eq165 | grind only
  have eq168 (X0 X1 X2 X3 : G) : ¬(old sk4 X1 X2) ∨ ¬(old X0 X1 X2) ∨ b = sk5 ∨ ¬(old X3 X3 X0) ∨ sk5 = X3 := by
    clear * - eq166 old_2
    first | exact resolve eq166 old_2 | exact resolve old_2 eq166 | grind only
  have eq169 (X0 : G) : ¬(old X0 X0 sk4) ∨ b = sk5 ∨ sk5 = X0 := by
    clear * - eq166 old_3
    first | exact resolve eq166 old_3 | exact resolve old_3 eq166 | grind only
  have eq205 (X0 X1 X2 : G) : ¬(new (sF0 X0 X1 X2) b a) ∨ (new b c X2) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - eq107 eq83
    first | exact resolve eq107 eq83 | exact resolve eq83 eq107 | grind only
  have eq210 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new b c X2) := by
    clear * - eq205 eq88
    first | exact resolve eq205 eq88 | exact resolve eq88 eq205 | grind only
  have eq219 : (old sk1 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq157 rule_def_1_1
    first | exact resolve eq157 rule_def_1_1 | exact resolve rule_def_1_1 eq157 | grind only
  have eq220 : (old sk1 sk2 sk3) ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq157 rule_def_1_0
    first | exact resolve eq157 rule_def_1_0 | exact resolve rule_def_1_0 eq157 | grind only
  have eq234 : (old sk4 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq161 rule_def_1_1
    first | exact resolve eq161 rule_def_1_1 | exact resolve rule_def_1_1 eq161 | grind only
  have eq235 : (old sk4 sk2 sk3) ∨ b = sk2 ∨ b = sk4 := by
    clear * - eq161 rule_def_1_0
    first | exact resolve eq161 rule_def_1_0 | exact resolve rule_def_1_0 eq161 | grind only
  have eq272 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq142 rule_def_1_1
    first | exact resolve eq142 rule_def_1_1 | exact resolve rule_def_1_1 eq142 | grind only
  have eq274 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq272 rule_def_2_0
    first | exact resolve eq272 rule_def_2_0 | exact resolve rule_def_2_0 eq272 | grind only
  have eq275 (X0 X1 X2 X3 : G) : ¬(old X0 X0 b) ∨ (old b a X0) ∨ ¬(sP2 X1 X2 X3) ∨ ¬(sP2 X1 X2 X3) := by
    clear * - eq105 rule_def_2_2
    first | exact resolve eq105 rule_def_2_2 | exact resolve rule_def_2_2 eq105 | grind only
  have eq276 (X0 X1 X2 X3 : G) : ¬(sP2 X1 X2 X3) ∨ (old b a X0) ∨ ¬(old X0 X0 b) := by
    clear * - eq275
    first | exact resolve eq275 rfl | grind only
  have eq280 (X0 X1 X2 X3 : G) : ¬(old sk1 X1 X2) ∨ c = sk0 ∨ ¬(old X0 X1 X2) ∨ c = sk1 ∨ ¬(old X3 X3 X0) ∨ sk0 = X3 := by
    clear * - eq274 old_2
    first | exact resolve eq274 old_2 | exact resolve old_2 eq274 | grind only
  have eq281 (X0 : G) : ¬(old X0 X0 sk1) ∨ c = sk0 ∨ c = sk1 ∨ sk0 = X0 := by
    clear * - eq274 old_3
    first | exact resolve eq274 old_3 | exact resolve old_3 eq274 | grind only
  have eq303 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq144 rule_def_1_1
    first | exact resolve eq144 rule_def_1_1 | exact resolve rule_def_1_1 eq144 | grind only
  have eq305 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq303 rule_def_2_0
    first | exact resolve eq303 rule_def_2_0 | exact resolve rule_def_2_0 eq303 | grind only
  have eq313 (X0 X1 X2 X3 : G) : ¬(old sk1 X1 X2) ∨ c = sk0 ∨ ¬(old X0 X1 X2) ∨ a = sk0 ∨ ¬(old X3 X3 X0) ∨ sk0 = X3 := by
    clear * - eq305 old_2
    first | exact resolve eq305 old_2 | exact resolve old_2 eq305 | grind only
  have eq338 : (sP2 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq154 rule_def_1_1
    first | exact resolve eq154 rule_def_1_1 | exact resolve rule_def_1_1 eq154 | grind only
  have eq339 : (sP2 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq154 rule_def_1_0
    first | exact resolve eq154 rule_def_1_0 | exact resolve rule_def_1_0 eq154 | grind only
  have eq342 : (sP2 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ c = sk2 := by
    clear * - eq156 rule_def_1_1
    first | exact resolve eq156 rule_def_1_1 | exact resolve rule_def_1_1 eq156 | grind only
  have eq343 : (sP2 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ b = sk1 := by
    clear * - eq156 rule_def_1_0
    first | exact resolve eq156 rule_def_1_0 | exact resolve rule_def_1_0 eq156 | grind only
  have eq344 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq338 rule_def_2_0
    first | exact resolve eq338 rule_def_2_0 | exact resolve rule_def_2_0 eq338 | grind only
  have eq353 : (sP2 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq158 rule_def_1_1
    first | exact resolve eq158 rule_def_1_1 | exact resolve rule_def_1_1 eq158 | grind only
  have eq364 : (sP2 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ a = sk4 ∨ c = sk2 := by
    clear * - eq160 rule_def_1_1
    first | exact resolve eq160 rule_def_1_1 | exact resolve rule_def_1_1 eq160 | grind only
  have eq365 : (sP2 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ a = sk4 ∨ b = sk4 := by
    clear * - eq160 rule_def_1_0
    first | exact resolve eq160 rule_def_1_0 | exact resolve rule_def_1_0 eq160 | grind only
  have eq366 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq339 rule_def_2_0
    first | exact resolve eq339 rule_def_2_0 | exact resolve rule_def_2_0 eq339 | grind only
  have eq375 : (old sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq162 rule_def_1_1
    first | exact resolve eq162 rule_def_1_1 | exact resolve rule_def_1_1 eq162 | grind only
  have eq377 : (old sk5 sk5 sk4) ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq375 rule_def_2_0
    first | exact resolve eq375 rule_def_2_0 | exact resolve rule_def_2_0 eq375 | grind only
  have eq389 : (old sk5 sk5 sk4) ∨ (sP2 sk5 sk5 sk4) ∨ a = sk5 ∨ c = sk5 := by
    clear * - eq164 rule_def_1_1
    first | exact resolve eq164 rule_def_1_1 | exact resolve rule_def_1_1 eq164 | grind only
  have eq391 : (old sk5 sk5 sk4) ∨ a = sk5 ∨ c = sk5 := by
    clear * - eq389 rule_def_2_0
    first | exact resolve eq389 rule_def_2_0 | exact resolve rule_def_2_0 eq389 | grind only
  have eq430 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq342 rule_def_2_0
    first | exact resolve eq342 rule_def_2_0 | exact resolve rule_def_2_0 eq342 | grind only
  have eq432 : (old sk3 sk3 b) ∨ a = sk1 ∨ c = sk2 ∨ (old sk1 sk2 sk3) := by
    clear * - eq342 rule_def_2_4
    first | exact resolve eq342 rule_def_2_4 | exact resolve rule_def_2_4 eq342 | grind only
  have eq465 : (sP2 sk4 sk2 sk3) ∨ (old sk4 sk2 sk3) ∨ (new b c sk3) ∨ a = sk4 := by
    clear * - eq210 eq160
    first | exact resolve eq210 eq160 | exact resolve eq160 eq210 | grind only
  have eq481 (X0 : G) : ¬(old X0 X0 b) ∨ (old b a X0) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ c = sk2 := by
    clear * - eq276 eq342
    first | exact resolve eq276 eq342 | exact resolve eq342 eq276 | grind only
  have eq484 : (old sk4 sk2 sk3) ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 := by
    clear * - eq353 rule_def_2_0
    first | exact resolve eq353 rule_def_2_0 | exact resolve rule_def_2_0 eq353 | grind only
  have eq538 : (old sk4 sk2 sk3) ∨ a = sk4 ∨ c = sk2 ∨ (old sk3 sk3 b) := by
    clear * - eq364 rule_def_2_4
    first | exact resolve eq364 rule_def_2_4 | exact resolve rule_def_2_4 eq364 | grind only
  have eq764 : (new b c sk3) ∨ (old sk4 sk2 sk3) ∨ a = sk4 ∨ (old sk3 sk3 b) := by
    clear * - eq465 rule_def_2_4
    first | exact resolve eq465 rule_def_2_4 | exact resolve rule_def_2_4 eq465 | grind only
  have eq916 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ b = sk0 ∨ ¬(old X0 sk2 sk3) ∨ sk0 = X1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq148 eq344
    first | exact resolve eq148 eq344 | exact resolve eq344 eq148 | grind only
  have eq918 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ b = sk0 ∨ ¬(old X0 sk2 sk3) ∨ sk0 = X1 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq148 eq219
    first | exact resolve eq148 eq219 | exact resolve eq219 eq148 | grind only
  have eq927 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ b = sk5 ∨ ¬(old X0 sk2 sk3) ∨ sk5 = X1 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq168 eq234
    first | exact resolve eq168 eq234 | exact resolve eq234 eq168 | grind only
  have eq929 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ b = sk5 ∨ ¬(old X0 sk2 sk3) ∨ sk5 = X1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 := by
    clear * - eq168 eq484
    first | exact resolve eq168 eq484 | exact resolve eq484 eq168 | grind only
  have eq1033 : (old sk4 sk2 sk3) ∨ a = sk4 ∨ (old sk3 sk3 b) ∨ (old b c sk3) ∨ (sP0 b c sk3) ∨ (sP1 b c sk3) ∨ (sP2 b c sk3) := by
    clear * - eq764 new_imp
    first | exact resolve eq764 new_imp | exact resolve new_imp eq764 | grind only
  have eq1037 : (old sk4 sk2 sk3) ∨ a = sk4 ∨ (old sk3 sk3 b) ∨ (old b c sk3) ∨ (sP0 b c sk3) ∨ (sP1 b c sk3) := by
    clear * - eq1033 rule_def_2_4
    first | exact resolve eq1033 rule_def_2_4 | exact resolve rule_def_2_4 eq1033 | grind only
  have eq1038 : (sP0 b c sk3) ∨ a = sk4 ∨ (old sk3 sk3 b) ∨ (old sk4 sk2 sk3) ∨ (sP1 b c sk3) := by
    clear * - eq1037 p4XZ
    first | exact resolve eq1037 p4XZ | exact resolve p4XZ eq1037 | grind only
  have eq2382 : (old b a sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ c = sk2 ∨ a = sk1 ∨ c = sk2 ∨ (old sk1 sk2 sk3) := by
    clear * - eq481 eq432
    first | exact resolve eq481 eq432 | exact resolve eq432 eq481 | grind only
  have eq2387 : (old sk1 sk2 sk3) ∨ (old b a sk3) ∨ a = sk1 ∨ c = sk2 := by
    clear * - eq2382
    first | exact resolve eq2382 rfl | grind only
  have eq3986 : b = sk0 ∨ ¬(old sk4 sk2 sk3) ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq918 eq377
    first | exact resolve eq918 eq377 | exact resolve eq377 eq918 | grind only
  have eq3987 : b = sk0 ∨ ¬(old sk4 sk2 sk3) ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ b = sk5 := by
    clear * - eq918 eq166
    first | exact resolve eq918 eq166 | exact resolve eq166 eq918 | grind only
  have eq3992 : b = sk0 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ b = sk5 := by
    clear * - eq3987 eq234
    first | exact resolve eq3987 eq234 | exact resolve eq234 eq3987 | grind only
  have eq3993 : b = sk0 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq3986 eq234
    first | exact resolve eq3986 eq234 | exact resolve eq234 eq3986 | grind only
  have eq3995 : c = sk2 ∨ b = sk2 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq3992 preserve_4
    first | exact resolve eq3992 preserve_4 | exact resolve preserve_4 eq3992 | grind only
  have eq3996 : c = sk4 ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq3993 preserve_4
    first | exact resolve eq3993 preserve_4 | exact resolve preserve_4 eq3993 | grind only
  have eq4020 : (old sk4 c sk3) ∨ c = b ∨ b = sk4 ∨ b = sk2 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq235 eq3995
    first | exact Or.assoc3 (eq3995.imp_left (fun h : c = sk2 => superpose h eq235)) | exact superpose eq235 eq3995 | exact superpose eq3995 eq235 | grind only
  have eq4087 : c = b ∨ b = sk4 ∨ b = sk2 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq4020 p4XZ
    first | exact resolve eq4020 p4XZ | exact resolve p4XZ eq4020 | grind only
  have eq4103 : b = sk4 ∨ b = sk2 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq4087 bc
    first | exact resolve eq4087 bc | exact resolve bc eq4087 | grind only
  have eq4109 : b = sk5 ∨ ¬(old sk1 sk2 sk3) ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq927 eq305
    first | exact resolve eq927 eq305 | exact resolve eq305 eq927 | grind only
  have eq4110 : b = sk5 ∨ ¬(old sk1 sk2 sk3) ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq927 eq274
    first | exact resolve eq927 eq274 | exact resolve eq274 eq927 | grind only
  have eq4123 : b = sk5 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq4110 eq219
    first | exact resolve eq4110 eq219 | exact resolve eq219 eq4110 | grind only
  have eq4124 : b = sk5 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq4109 eq219
    first | exact resolve eq4109 eq219 | exact resolve eq219 eq4109 | grind only
  have eq4125 : c = sk2 ∨ b = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq4123 preserve_4
    first | exact resolve eq4123 preserve_4 | exact resolve preserve_4 eq4123 | grind only
  have eq4126 : c = sk2 ∨ b = sk2 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq4124 preserve_4
    first | exact resolve eq4124 preserve_4 | exact resolve preserve_4 eq4124 | grind only
  have eq4145 (X0 : G) : ¬(old X0 X0 b) ∨ b = sk5 ∨ sk5 = X0 ∨ b = sk2 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq169 eq4103
    first | exact Or.assoc3 (eq4103.imp_left (fun h : b = sk4 => superpose h eq169)) | exact superpose eq169 eq4103 | exact superpose eq4103 eq169 | grind only
  have eq4221 (X0 : G) : ¬(old X0 X0 b) ∨ b = sk5 ∨ sk5 = X0 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq4145
    first | exact resolve eq4145 rfl | grind only
  have eq4359 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ ¬(old X0 sk2 sk3) ∨ c = sk1 ∨ c = sk0 ∨ sk0 = X1 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq280 eq219
    first | exact resolve eq280 eq219 | exact resolve eq219 eq280 | grind only
  have eq4361 (X0 X1 : G) : c = sk0 ∨ ¬(old X0 sk2 sk3) ∨ c = sk1 ∨ ¬(old X1 X1 X0) ∨ sk0 = X1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq280 eq344
    first | exact resolve eq280 eq344 | exact resolve eq344 eq280 | grind only
  have eq4378 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ ¬(old X0 sk2 sk3) ∨ c = sk1 ∨ c = sk0 ∨ sk0 = X1 ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq4361
    first | exact resolve eq4361 rfl | grind only
  have eq4382 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ ¬(old X0 sk2 sk3) ∨ a = sk0 ∨ c = sk0 ∨ sk0 = X1 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq313 eq219
    first | exact resolve eq313 eq219 | exact resolve eq219 eq313 | grind only
  have eq4672 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq234 eq3996
    first | exact Or.assoc3 (eq3996.imp_left (fun h : c = sk4 => superpose h eq234)) | exact superpose eq234 eq3996 | exact superpose eq3996 eq234 | grind only
  have eq4753 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq4672
    first | exact resolve eq4672 rfl | grind only
  have eq4772 : c = sk2 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq4753 p4YZ
    first | exact resolve eq4753 p4YZ | exact resolve p4YZ eq4753 | grind only
  have eq4810 : (old sk1 c sk3) ∨ c = b ∨ b = sk1 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq220 eq4772
    first | exact Or.assoc3 (eq4772.imp_left (fun h : c = sk2 => superpose h eq220)) | exact superpose eq220 eq4772 | exact superpose eq4772 eq220 | grind only
  have eq4812 : (old sk4 c sk3) ∨ c = b ∨ b = sk4 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq235 eq4772
    first | exact Or.assoc3 (eq4772.imp_left (fun h : c = sk2 => superpose h eq235)) | exact superpose eq235 eq4772 | exact superpose eq4772 eq235 | grind only
  have eq4881 : c = b ∨ b = sk4 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq4812 p4XZ
    first | exact resolve eq4812 p4XZ | exact resolve p4XZ eq4812 | grind only
  have eq4882 : c = b ∨ b = sk1 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq4810 p4XZ
    first | exact resolve eq4810 p4XZ | exact resolve p4XZ eq4810 | grind only
  have eq4897 : b = sk4 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq4881 bc
    first | exact resolve eq4881 bc | exact resolve bc eq4881 | grind only
  have eq4898 : b = sk2 ∨ b = sk1 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq4882 bc
    first | exact resolve eq4882 bc | exact resolve bc eq4882 | grind only
  have eq4905 : (new sk5 sk5 b) ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - preserve_3 eq4897
    first | exact (eq4897.imp_left (fun h : b = sk4 => superpose h preserve_3)) | exact superpose preserve_3 eq4897 | exact superpose eq4897 preserve_3 | grind only
  have eq4932 : (old sk5 sk5 b) ∨ c = b ∨ c = sk5 ∨ b = sk2 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq377 eq4897
    first | exact Or.assoc3 (eq4897.imp_left (fun h : b = sk4 => superpose h eq377)) | exact superpose eq377 eq4897 | exact superpose eq4897 eq377 | grind only
  have eq5010 : (old sk5 sk5 b) ∨ c = b ∨ c = sk5 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq4932
    first | exact resolve eq4932 rfl | grind only
  have eq5030 : (old sk5 sk5 b) ∨ c = sk5 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq5010 bc
    first | exact resolve eq5010 bc | exact resolve bc eq5010 | grind only
  have eq5070 : (old sk1 b sk3) ∨ c = sk3 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq366 eq4898
    first | exact Or.assoc4 (eq4898.imp_left (fun h : b = sk2 => superpose h eq366)) | exact superpose eq366 eq4898 | exact superpose eq4898 eq366 | grind only
  have eq5118 : (old sk1 b sk3) ∨ c = sk3 ∨ b = sk1 ∨ c = sk1 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq5070
    first | exact resolve eq5070 rfl | grind only
  have eq5204 (X0 : G) : ¬(new sk5 sk5 X0) ∨ b = sk0 ∨ c = sk5 ∨ b = sk2 ∨ b = X0 := by
    clear * - eq4905 prev_0
    first | exact resolve eq4905 prev_0 | exact resolve prev_0 eq4905 | grind only
  have eq5481 : (old sk1 c sk3) ∨ c = b ∨ b = sk1 ∨ b = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq220 eq4125
    first | exact Or.assoc3 (eq4125.imp_left (fun h : c = sk2 => superpose h eq220)) | exact superpose eq220 eq4125 | exact superpose eq4125 eq220 | grind only
  have eq5559 : c = b ∨ b = sk1 ∨ b = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq5481 p4XZ
    first | exact resolve eq5481 p4XZ | exact resolve p4XZ eq5481 | grind only
  have eq5577 : b = sk2 ∨ b = sk1 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq5559 bc
    first | exact resolve eq5559 bc | exact resolve bc eq5559 | grind only
  have eq5607 : (old sk4 c sk3) ∨ c = b ∨ b = sk4 ∨ b = sk2 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq235 eq4126
    first | exact Or.assoc3 (eq4126.imp_left (fun h : c = sk2 => superpose h eq235)) | exact superpose eq235 eq4126 | exact superpose eq4126 eq235 | grind only
  have eq5676 : c = b ∨ b = sk4 ∨ b = sk2 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq5607 p4XZ
    first | exact resolve eq5607 p4XZ | exact resolve p4XZ eq5607 | grind only
  have eq5692 : b = sk4 ∨ b = sk2 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq5676 bc
    first | exact resolve eq5676 bc | exact resolve bc eq5676 | grind only
  have eq6348 (X0 : G) : ¬(old X0 X0 b) ∨ b = sk5 ∨ sk5 = X0 ∨ b = sk2 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq169 eq5692
    first | exact Or.assoc3 (eq5692.imp_left (fun h : b = sk4 => superpose h eq169)) | exact superpose eq169 eq5692 | exact superpose eq5692 eq169 | grind only
  have eq6441 (X0 : G) : ¬(old X0 X0 b) ∨ b = sk5 ∨ sk5 = X0 ∨ b = sk2 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq6348
    first | exact resolve eq6348 rfl | grind only
  have eq10572 : a = sk4 ∨ (old sk3 sk3 b) ∨ (old sk4 sk2 sk3) ∨ (sP1 b c sk3) ∨ c = b := by
    clear * - eq1038 rule_def_0_1
    first | exact resolve eq1038 rule_def_0_1 | exact resolve rule_def_0_1 eq1038 | grind only
  have eq10575 : (sP1 b c sk3) ∨ (old sk3 sk3 b) ∨ (old sk4 sk2 sk3) ∨ a = sk4 := by
    clear * - eq10572 bc
    first | exact resolve eq10572 bc | exact resolve bc eq10572 | grind only
  have eq20718 : b = sk0 ∨ ¬(old sk4 sk2 sk3) ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq916 eq377
    first | exact resolve eq916 eq377 | exact resolve eq377 eq916 | grind only
  have eq20719 : b = sk0 ∨ ¬(old sk4 sk2 sk3) ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 := by
    clear * - eq916 eq166
    first | exact resolve eq916 eq166 | exact resolve eq166 eq916 | grind only
  have eq20746 : ¬(old sk4 sk2 sk3) ∨ b = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 := by
    clear * - eq20719 preserve_4
    first | exact resolve eq20719 preserve_4 | exact resolve preserve_4 eq20719 | grind only
  have eq20747 : b = sk0 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq20718 eq484
    first | exact resolve eq20718 eq484 | exact resolve eq484 eq20718 | grind only
  have eq20749 : c = sk4 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq20747 preserve_4
    first | exact resolve eq20747 preserve_4 | exact resolve preserve_4 eq20747 | grind only
  have eq20790 : (old sk5 sk5 c) ∨ a = sk5 ∨ c = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ c = sk5 := by
    clear * - eq391 eq20749
    first | exact Or.assoc3 (eq20749.imp_left (fun h : c = sk4 => superpose h eq391)) | exact superpose eq391 eq20749 | exact superpose eq20749 eq391 | grind only
  have eq21050 : (old sk5 sk5 c) ∨ a = sk5 ∨ c = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq20790
    first | exact resolve eq20790 rfl | grind only
  have eq21107 : c = sk3 ∨ c = sk5 ∨ a = sk5 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq21050 p4XY
    first | exact resolve eq21050 p4XY | exact resolve p4XY eq21050 | grind only
  have eq21145 : b = sk5 ∨ ¬(old sk1 sk2 sk3) ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq929 eq274
    first | exact resolve eq929 eq274 | exact resolve eq274 eq929 | grind only
  have eq21192 : b = sk5 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq21145 eq344
    first | exact resolve eq21145 eq344 | exact resolve eq344 eq21145 | grind only
  have eq21194 : c = sk4 ∨ c = sk3 ∨ c = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq21192 preserve_4
    first | exact resolve eq21192 preserve_4 | exact resolve preserve_4 eq21192 | grind only
  have eq21216 : (old sk5 sk5 c) ∨ b = sk5 ∨ c = sk3 ∨ c = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq166 eq21194
    first | exact Or.assoc2 (eq21194.imp_left (fun h : c = sk4 => superpose h eq166)) | exact superpose eq166 eq21194 | exact superpose eq21194 eq166 | grind only
  have eq21491 : (old sk5 sk5 c) ∨ b = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq21216
    first | exact resolve eq21216 rfl | grind only
  have eq21545 : c = sk3 ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq21491 p4XY
    first | exact resolve eq21491 p4XY | exact resolve p4XY eq21491 | grind only
  have eq21625 : (new sk1 sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - preserve_1 eq21545
    first | exact (eq21545.imp_left (fun h : c = sk3 => superpose h preserve_1)) | exact superpose preserve_1 eq21545 | exact superpose eq21545 preserve_1 | grind only
  have eq21649 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq430 eq21545
    first | exact Or.assoc4 (eq21545.imp_left (fun h : c = sk3 => superpose h eq430)) | exact superpose eq430 eq21545 | exact superpose eq21545 eq430 | grind only
  have eq21664 : (old sk4 sk2 c) ∨ a = sk4 ∨ c = sk2 ∨ (old c c b) ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq538 eq21545
    first | exact Or.assoc4 (eq21545.imp_left (fun h : c = sk3 => superpose h eq538)) | exact superpose eq538 eq21545 | exact superpose eq21545 eq538 | grind only
  have eq21960 : (old sk4 sk2 c) ∨ a = sk4 ∨ c = sk2 ∨ (old c c b) ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq21664
    first | exact resolve eq21664 rfl | grind only
  have eq21964 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ c = sk0 := by
    clear * - eq21649
    first | exact resolve eq21649 rfl | grind only
  have eq22032 : a = sk4 ∨ c = sk2 ∨ (old c c b) ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq21960 p4XY
    first | exact resolve eq21960 p4XY | exact resolve p4XY eq21960 | grind only
  have eq22041 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ c = sk0 := by
    clear * - eq21964 p4XY
    first | exact resolve eq21964 p4XY | exact resolve p4XY eq21964 | grind only
  have eq22074 : a = sk4 ∨ c = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq22032 p4XZ
    first | exact resolve eq22032 p4XZ | exact resolve p4XZ eq22032 | grind only
  have eq22262 : c = b ∨ b = sk1 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ c = sk0 := by
    clear * - eq5577 eq22041
    first | exact Or.assoc5 (eq22041.imp_left (fun h : c = sk2 => superpose h eq5577)) | exact superpose eq5577 eq22041 | exact superpose eq22041 eq5577 | grind only
  have eq22300 : c = b ∨ b = sk1 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := by
    clear * - eq22262
    first | exact resolve eq22262 rfl | grind only
  have eq22367 : a = sk1 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq22300 bc
    first | exact resolve eq22300 bc | exact resolve bc eq22300 | grind only
  have eq22543 (X0 : G) : ¬(old X0 X0 a) ∨ b = sk5 ∨ sk5 = X0 ∨ c = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq169 eq22074
    first | exact Or.assoc3 (eq22074.imp_left (fun h : a = sk4 => superpose h eq169)) | exact superpose eq169 eq22074 | exact superpose eq22074 eq169 | grind only
  have eq22824 (X0 : G) : ¬(old X0 X0 a) ∨ b = sk5 ∨ sk5 = X0 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq22543
    first | exact resolve eq22543 rfl | grind only
  have eq22918 : (old sk0 sk0 a) ∨ a = c ∨ c = sk0 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq274 eq22367
    first | exact Or.assoc3 (eq22367.imp_left (fun h : a = sk1 => superpose h eq274)) | exact superpose eq274 eq22367 | exact superpose eq22367 eq274 | grind only
  have eq23164 : (old sk0 sk0 a) ∨ a = c ∨ c = sk0 ∨ b = sk5 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq22918
    first | exact resolve eq22918 rfl | grind only
  have eq23221 : (old sk0 sk0 a) ∨ c = sk0 ∨ b = sk5 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq23164 ac
    first | exact resolve eq23164 ac | exact resolve ac eq23164 | grind only
  have eq26677 : ¬(old sk4 sk2 sk3) ∨ c = sk1 ∨ c = sk0 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq4359 eq377
    first | exact resolve eq4359 eq377 | exact resolve eq377 eq4359 | grind only
  have eq26715 : c = sk1 ∨ c = sk0 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq26677 eq234
    first | exact resolve eq26677 eq234 | exact resolve eq234 eq26677 | grind only
  have eq26717 : c = sk4 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq26715 preserve_4
    first | exact resolve eq26715 preserve_4 | exact resolve preserve_4 eq26715 | grind only
  have eq26750 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq234 eq26717
    first | exact Or.assoc3 (eq26717.imp_left (fun h : c = sk4 => superpose h eq234)) | exact superpose eq234 eq26717 | exact superpose eq26717 eq234 | grind only
  have eq27052 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq26750
    first | exact resolve eq26750 rfl | grind only
  have eq27103 : c = sk2 ∨ b = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq27052 p4YZ
    first | exact resolve eq27052 p4YZ | exact resolve p4YZ eq27052 | grind only
  have eq27216 : (old sk1 c sk3) ∨ c = b ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq220 eq27103
    first | exact Or.assoc3 (eq27103.imp_left (fun h : c = sk2 => superpose h eq220)) | exact superpose eq220 eq27103 | exact superpose eq27103 eq220 | grind only
  have eq27458 : c = b ∨ b = sk1 ∨ b = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq27216 p4XZ
    first | exact resolve eq27216 p4XZ | exact resolve p4XZ eq27216 | grind only
  have eq27485 : b = sk2 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq27458 bc
    first | exact resolve eq27458 bc | exact resolve bc eq27458 | grind only
  have eq28295 : ¬(old sk4 sk2 sk3) ∨ c = sk1 ∨ c = sk0 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq4378 eq377
    first | exact resolve eq4378 eq377 | exact resolve eq377 eq4378 | grind only
  have eq28320 : c = sk1 ∨ c = sk0 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq28295 eq484
    first | exact resolve eq28295 eq484 | exact resolve eq484 eq28295 | grind only
  have eq28322 : c = sk4 ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq28320 preserve_4
    first | exact resolve eq28320 preserve_4 | exact resolve preserve_4 eq28320 | grind only
  have eq28402 : ¬(old sk4 sk2 sk3) ∨ a = sk0 ∨ c = sk0 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq4382 eq377
    first | exact resolve eq4382 eq377 | exact resolve eq377 eq4382 | grind only
  have eq28440 : a = sk0 ∨ c = sk0 ∨ sk0 = sk5 ∨ b = sk2 ∨ c = sk2 ∨ c = sk4 ∨ c = sk5 := by
    clear * - eq28402 eq234
    first | exact resolve eq28402 eq234 | exact resolve eq234 eq28402 | grind only
  have eq28442 : c = sk4 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq28440 preserve_4
    first | exact resolve eq28440 preserve_4 | exact resolve preserve_4 eq28440 | grind only
  have eq30308 : (sP0 sk5 sk5 c) ∨ (old sk5 sk5 c) ∨ (sP1 sk5 sk5 c) ∨ (sP2 sk5 sk5 c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq133 eq28322
    first | exact Or.assoc4 (eq28322.imp_left (fun h : c = sk4 => superpose h eq133)) | exact superpose eq133 eq28322 | exact superpose eq28322 eq133 | grind only
  have eq30336 : (old sk5 sk5 c) ∨ a = sk5 ∨ c = sk5 ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq391 eq28322
    first | exact Or.assoc3 (eq28322.imp_left (fun h : c = sk4 => superpose h eq391)) | exact superpose eq391 eq28322 | exact superpose eq28322 eq391 | grind only
  have eq30607 : (old sk5 sk5 c) ∨ a = sk5 ∨ c = sk5 ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq30336
    first | exact resolve eq30336 rfl | grind only
  have eq30666 : c = sk3 ∨ c = sk5 ∨ c = sk0 ∨ a = sk5 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq30607 p4XY
    first | exact resolve eq30607 p4XY | exact resolve p4XY eq30607 | grind only
  have eq30674 : (sP0 sk5 sk5 c) ∨ (sP1 sk5 sk5 c) ∨ (sP2 sk5 sk5 c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq30308 p4XY
    first | exact resolve eq30308 p4XY | exact resolve p4XY eq30308 | grind only
  have eq30698 : (sP0 sk5 sk5 c) ∨ (sP2 sk5 sk5 c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq30674 rule_def_1_1
    first | exact resolve eq30674 rule_def_1_1 | exact resolve rule_def_1_1 eq30674 | grind only
  have eq30699 : (sP0 sk5 sk5 c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 := by
    clear * - eq30698 rule_def_2_0
    first | exact resolve eq30698 rule_def_2_0 | exact resolve rule_def_2_0 eq30698 | grind only
  have eq30789 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq234 eq28442
    first | exact Or.assoc3 (eq28442.imp_left (fun h : c = sk4 => superpose h eq234)) | exact superpose eq234 eq28442 | exact superpose eq28442 eq234 | grind only
  have eq31095 : (old c sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq30789
    first | exact resolve eq30789 rfl | grind only
  have eq31147 : c = sk2 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq31095 p4YZ
    first | exact resolve eq31095 p4YZ | exact resolve p4YZ eq31095 | grind only
  have eq31299 : (old sk4 c sk3) ∨ c = b ∨ b = sk4 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq235 eq31147
    first | exact Or.assoc3 (eq31147.imp_left (fun h : c = sk2 => superpose h eq235)) | exact superpose eq235 eq31147 | exact superpose eq31147 eq235 | grind only
  have eq31532 : c = b ∨ b = sk4 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq31299 p4XZ
    first | exact resolve eq31299 p4XZ | exact resolve p4XZ eq31299 | grind only
  have eq31554 : b = sk4 ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk5 := by
    clear * - eq31532 bc
    first | exact resolve eq31532 bc | exact resolve bc eq31532 | grind only
  have eq31572 : (new sk5 sk5 b) ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk5 := by
    clear * - preserve_3 eq31554
    first | exact (eq31554.imp_left (fun h : b = sk4 => superpose h preserve_3)) | exact superpose preserve_3 eq31554 | exact superpose eq31554 preserve_3 | grind only
  have eq33122 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 ∨ a = sk5 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq430 eq21107
    first | exact Or.assoc4 (eq21107.imp_left (fun h : c = sk3 => superpose h eq430)) | exact superpose eq430 eq21107 | exact superpose eq21107 eq430 | grind only
  have eq33526 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 ∨ a = sk5 ∨ b = sk0 := by
    clear * - eq33122
    first | exact resolve eq33122 rfl | grind only
  have eq33602 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk5 ∨ a = sk5 ∨ b = sk0 := by
    clear * - eq33526 p4XY
    first | exact resolve eq33526 p4XY | exact resolve p4XY eq33526 | grind only
  have eq35243 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 ∨ c = sk0 ∨ a = sk5 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq430 eq30666
    first | exact Or.assoc4 (eq30666.imp_left (fun h : c = sk3 => superpose h eq430)) | exact superpose eq430 eq30666 | exact superpose eq30666 eq430 | grind only
  have eq35616 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk5 ∨ c = sk0 ∨ a = sk5 := by
    clear * - eq35243
    first | exact resolve eq35243 rfl | grind only
  have eq35688 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk5 ∨ c = sk0 ∨ a = sk5 := by
    clear * - eq35616 p4XY
    first | exact resolve eq35616 p4XY | exact resolve p4XY eq35616 | grind only
  have eq37704 : c = b ∨ b = sk1 ∨ b = sk0 ∨ c = sk5 ∨ a = sk1 ∨ c = sk1 ∨ c = sk5 ∨ a = sk5 ∨ b = sk0 := by
    clear * - eq4898 eq33602
    first | exact Or.assoc4 (eq33602.imp_left (fun h : c = sk2 => superpose h eq4898)) | exact superpose eq4898 eq33602 | exact superpose eq33602 eq4898 | grind only
  have eq37781 : c = b ∨ b = sk1 ∨ b = sk0 ∨ c = sk5 ∨ a = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq37704
    first | exact resolve eq37704 rfl | grind only
  have eq37861 : a = sk1 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq37781 bc
    first | exact resolve eq37781 bc | exact resolve bc eq37781 | grind only
  have eq39459 : c = b ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 ∨ a = sk1 ∨ c = sk1 ∨ c = sk5 ∨ c = sk0 ∨ a = sk5 := by
    clear * - eq27485 eq35688
    first | exact Or.assoc5 (eq35688.imp_left (fun h : c = sk2 => superpose h eq27485)) | exact superpose eq27485 eq35688 | exact superpose eq35688 eq27485 | grind only
  have eq39466 : c = b ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 ∨ a = sk1 ∨ a = sk5 := by
    clear * - eq39459
    first | exact resolve eq39459 rfl | grind only
  have eq39539 : a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 ∨ b = sk1 ∨ a = sk5 := by
    clear * - eq39466 bc
    first | exact resolve eq39466 bc | exact resolve bc eq39466 | grind only
  have eq40629 : (old a b sk3) ∨ c = sk3 ∨ a = b ∨ a = c ∨ b = sk0 ∨ c = sk5 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq5118 eq37861
    first | exact Or.assoc6 (eq37861.imp_left (fun h : a = sk1 => superpose h eq5118)) | exact superpose eq5118 eq37861 | exact superpose eq37861 eq5118 | grind only
  have eq40692 : a ≠ b ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq37861
    grind only
  have eq40716 : (old a b sk3) ∨ c = sk3 ∨ a = b ∨ a = c ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq40629
    first | exact resolve eq40629 rfl | grind only
  have eq40782 : (old a b sk3) ∨ c = sk3 ∨ a = c ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq40716 eq40692
    first | exact resolve eq40716 eq40692 | exact resolve eq40692 eq40716 | grind only
  have eq40831 : c = sk3 ∨ a = c ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq40782 p3
    first | exact resolve eq40782 p3 | exact resolve p3 eq40782 | grind only
  have eq40835 : c = sk3 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq40831 ac
    first | exact resolve eq40831 ac | exact resolve ac eq40831 | grind only
  have eq42171 (X0 : G) : ¬(old X0 X0 a) ∨ c = sk0 ∨ a = c ∨ sk0 = X0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 ∨ b = sk1 ∨ a = sk5 := by
    clear * - eq281 eq39539
    first | exact Or.assoc4 (eq39539.imp_left (fun h : a = sk1 => superpose h eq281)) | exact superpose eq281 eq39539 | exact superpose eq39539 eq281 | grind only
  have eq42365 : a ≠ b ∨ c = sk0 ∨ c = sk1 ∨ c = sk5 ∨ b = sk1 ∨ a = sk5 := by
    clear * - eq39539
    grind only
  have eq42442 (X0 : G) : ¬(old X0 X0 a) ∨ c = sk0 ∨ a = c ∨ sk0 = X0 ∨ c = sk1 ∨ c = sk5 ∨ b = sk1 ∨ a = sk5 := by
    clear * - eq42171
    first | exact resolve eq42171 rfl | grind only
  have eq42491 (X0 : G) : ¬(old X0 X0 a) ∨ c = sk0 ∨ sk0 = X0 ∨ c = sk1 ∨ c = sk5 ∨ b = sk1 ∨ a = sk5 := by
    clear * - eq42442 ac
    first | exact resolve eq42442 ac | exact resolve ac eq42442 | grind only
  have eq43238 : (sP1 b c c) ∨ (old c c b) ∨ (old sk4 sk2 c) ∨ a = sk4 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq10575 eq40835
    first | exact Or.assoc4 (eq40835.imp_left (fun h : c = sk3 => superpose h eq10575)) | exact superpose eq10575 eq40835 | exact superpose eq40835 eq10575 | grind only
  have eq43461 : (old c c b) ∨ (old sk4 sk2 c) ∨ a = sk4 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq43238 eq86
    first | exact resolve eq43238 eq86 | exact resolve eq86 eq43238 | grind only
  have eq43490 : (old sk4 sk2 c) ∨ a = sk4 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq43461 p4XZ
    first | exact resolve eq43461 p4XZ | exact resolve p4XZ eq43461 | grind only
  have eq43499 : a = sk4 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq43490 p4XY
    first | exact resolve eq43490 p4XY | exact resolve p4XY eq43490 | grind only
  have eq45709 : b = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 := by
    clear * - eq20746 eq484
    first | exact resolve eq20746 eq484 | exact resolve eq484 eq20746 | grind only
  have eq45810 : c = sk4 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 := by
    clear * - eq45709
    first | exact resolve eq45709 rfl | grind only
  have eq45894 : (old sk5 sk5 c) ∨ b = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 := by
    clear * - eq166 eq45810
    first | exact Or.assoc2 (eq45810.imp_left (fun h : c = sk4 => superpose h eq166)) | exact superpose eq166 eq45810 | exact superpose eq45810 eq166 | grind only
  have eq46240 : (old sk5 sk5 c) ∨ b = sk5 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq45894
    first | exact resolve eq45894 rfl | grind only
  have eq46307 : c = sk3 ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq46240 p4XY
    first | exact resolve eq46240 p4XY | exact resolve p4XY eq46240 | grind only
  have eq46383 : (new sk1 sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - preserve_1 eq46307
    first | exact (eq46307.imp_left (fun h : c = sk3 => superpose h preserve_1)) | exact superpose preserve_1 eq46307 | exact superpose eq46307 preserve_1 | grind only
  have eq46407 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ c = sk2 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq430 eq46307
    first | exact Or.assoc4 (eq46307.imp_left (fun h : c = sk3 => superpose h eq430)) | exact superpose eq430 eq46307 | exact superpose eq46307 eq430 | grind only
  have eq46814 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 := by
    clear * - eq46407
    first | exact resolve eq46407 rfl | grind only
  have eq46888 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 := by
    clear * - eq46814 p4XY
    first | exact resolve eq46814 p4XY | exact resolve p4XY eq46814 | grind only
  have eq73254 : b = sk5 ∨ sk0 = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ b = sk5 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq22824 eq23221
    first | exact resolve eq22824 eq23221 | exact resolve eq23221 eq22824 | grind only
  have eq73263 : b = sk5 ∨ sk0 = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq73254
    first | exact resolve eq73254 rfl | grind only
  have eq73265 : c = sk2 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq73263 preserve_4
    first | exact resolve eq73263 preserve_4 | exact resolve preserve_4 eq73263 | grind only
  have eq73544 : c = b ∨ b = sk1 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq5577 eq73265
    first | exact Or.assoc5 (eq73265.imp_left (fun h : c = sk2 => superpose h eq5577)) | exact superpose eq5577 eq73265 | exact superpose eq73265 eq5577 | grind only
  have eq73690 : c = b ∨ b = sk1 ∨ b = sk5 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq73544
    first | exact resolve eq73544 rfl | grind only
  have eq73768 : c = sk1 ∨ b = sk5 ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq73690 bc
    first | exact resolve eq73690 bc | exact resolve bc eq73690 | grind only
  have eq73925 : (old sk0 sk0 c) ∨ b = sk0 ∨ b = sk5 ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq146 eq73768
    first | exact Or.assoc2 (eq73768.imp_left (fun h : c = sk1 => superpose h eq146)) | exact superpose eq146 eq73768 | exact superpose eq73768 eq146 | grind only
  have eq73943 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq305 eq73768
    first | exact Or.assoc3 (eq73768.imp_left (fun h : c = sk1 => superpose h eq305)) | exact superpose eq305 eq73768 | exact superpose eq73768 eq305 | grind only
  have eq74253 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk1 := by
    clear * - eq73943
    first | exact resolve eq73943 rfl | grind only
  have eq74369 : b = sk1 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq74253 p4XY
    first | exact resolve eq74253 p4XY | exact resolve p4XY eq74253 | grind only
  have eq74375 : b = sk1 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq73925 p4XY
    first | exact resolve eq73925 p4XY | exact resolve p4XY eq73925 | grind only
  have eq74570 (X0 : G) : ¬(new b sk2 X0) ∨ sk3 = X0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq96 eq74369
    first | exact Or.assoc2 (eq74369.imp_left (fun h : b = sk1 => superpose h eq96)) | exact superpose eq96 eq74369 | exact superpose eq74369 eq96 | grind only
  have eq74601 : (old sk0 sk0 b) ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq305 eq74369
    first | exact Or.assoc3 (eq74369.imp_left (fun h : b = sk1 => superpose h eq305)) | exact superpose eq305 eq74369 | exact superpose eq74369 eq305 | grind only
  have eq74820 : (new b sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = b ∨ c = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq21625 eq74369
    first | exact Or.assoc5 (eq74369.imp_left (fun h : b = sk1 => superpose h eq21625)) | exact superpose eq21625 eq74369 | exact superpose eq74369 eq21625 | grind only
  have eq74893 : (new b sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq74820
    first | exact resolve eq74820 rfl | grind only
  have eq74988 : (old sk0 sk0 b) ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq74601
    first | exact resolve eq74601 rfl | grind only
  have eq75019 : (new b sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq74893 bc
    first | exact resolve eq74893 bc | exact resolve bc eq74893 | grind only
  have eq75192 (X0 : G) : ¬(new b sk2 X0) ∨ sk3 = X0 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq96 eq74375
    first | exact Or.assoc2 (eq74375.imp_left (fun h : b = sk1 => superpose h eq96)) | exact superpose eq96 eq74375 | exact superpose eq74375 eq96 | grind only
  have eq75202 : (old sk0 sk0 b) ∨ b = sk0 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq146 eq74375
    first | exact Or.assoc2 (eq74375.imp_left (fun h : b = sk1 => superpose h eq146)) | exact superpose eq146 eq74375 | exact superpose eq74375 eq146 | grind only
  have eq75486 : (new b sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = b ∨ b = sk0 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq46383 eq74375
    first | exact Or.assoc5 (eq74375.imp_left (fun h : b = sk1 => superpose h eq46383)) | exact superpose eq46383 eq74375 | exact superpose eq74375 eq46383 | grind only
  have eq75495 : (new b sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq75486
    first | exact resolve eq75486 rfl | grind only
  have eq75632 : (old sk0 sk0 b) ∨ b = sk0 ∨ b = sk5 ∨ c = sk0 := by
    clear * - eq75202
    first | exact resolve eq75202 rfl | grind only
  have eq75644 : (new b sk2 c) ∨ b = sk5 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq75495 bc
    first | exact resolve eq75495 bc | exact resolve bc eq75495 | grind only
  have eq77036 : a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk5 ∨ sk0 = sk5 ∨ b = sk2 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq74988 eq6441
    first | exact resolve eq74988 eq6441 | exact resolve eq6441 eq74988 | grind only
  have eq77133 : a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ sk0 = sk5 ∨ b = sk2 := by
    clear * - eq77036
    first | exact resolve eq77036 rfl | grind only
  have eq77158 : b = sk2 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq77133 preserve_4
    first | exact resolve eq77133 preserve_4 | exact resolve preserve_4 eq77133 | grind only
  have eq77383 : c = b ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ c = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq22041 eq77158
    first | exact Or.assoc5 (eq77158.imp_left (fun h : b = sk2 => superpose h eq22041)) | exact superpose eq22041 eq77158 | exact superpose eq77158 eq22041 | grind only
  have eq77496 : c = b ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq77383
    first | exact resolve eq77383 rfl | grind only
  have eq77569 : a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq77496 bc
    first | exact resolve eq77496 bc | exact resolve bc eq77496 | grind only
  have eq77905 : b = sk0 ∨ b = sk5 ∨ c = sk0 ∨ b = sk5 ∨ sk0 = sk5 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq75632 eq4221
    first | exact resolve eq75632 eq4221 | exact resolve eq4221 eq75632 | grind only
  have eq78017 : b = sk0 ∨ b = sk5 ∨ c = sk0 ∨ sk0 = sk5 ∨ b = sk2 := by
    clear * - eq77905
    first | exact resolve eq77905 rfl | grind only
  have eq78029 : b = sk2 ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq78017 preserve_4
    first | exact resolve eq78017 preserve_4 | exact resolve preserve_4 eq78017 | grind only
  have eq78332 : c = b ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq46888 eq78029
    first | exact Or.assoc5 (eq78029.imp_left (fun h : b = sk2 => superpose h eq46888)) | exact superpose eq46888 eq78029 | exact superpose eq78029 eq46888 | grind only
  have eq78363 : c = b ∨ a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq78332
    first | exact resolve eq78332 rfl | grind only
  have eq78458 : a = sk1 ∨ c = sk1 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq78363 bc
    first | exact resolve eq78363 bc | exact resolve bc eq78363 | grind only
  have eq83845 : a = b ∨ c = b ∨ b = sk5 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq77569 eq74369
    first | exact Or.assoc5 (eq74369.imp_left (fun h : b = sk1 => superpose h eq77569)) | exact superpose eq77569 eq74369 | exact superpose eq74369 eq77569 | grind only
  have eq84349 : a = b ∨ c = b ∨ b = sk5 ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq83845
    first | exact resolve eq83845 rfl | grind only
  have eq84403 : b = sk5 ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq84349 bc
    first | exact resolve eq84349 bc | exact resolve bc eq84349 | grind only
  have eq84578 : (sP0 b b c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = b ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq30699 eq84403
    first | exact Or.assoc6 (eq84403.imp_left (fun h : b = sk5 => superpose h eq30699)) | exact superpose eq30699 eq84403 | exact superpose eq84403 eq30699 | grind only
  have eq84585 : (sP0 b b c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = b ∨ a = b ∨ a = sk0 := by
    clear * - eq84578
    first | exact resolve eq84578 rfl | grind only
  have eq84624 : c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = b ∨ a = b ∨ a = sk0 := by
    clear * - eq84585 rule_def_0_0
    first | exact resolve eq84585 rule_def_0_0 | exact resolve rule_def_0_0 eq84585 | grind only
  have eq84663 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ a = b ∨ a = sk0 := by
    clear * - eq84624 bc
    first | exact resolve eq84624 bc | exact resolve bc eq84624 | grind only
  have eq85305 : a = b ∨ c = b ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq78458 eq74375
    first | exact Or.assoc5 (eq74375.imp_left (fun h : b = sk1 => superpose h eq78458)) | exact superpose eq78458 eq74375 | exact superpose eq74375 eq78458 | grind only
  have eq85828 : a = b ∨ c = b ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq85305
    first | exact resolve eq85305 rfl | grind only
  have eq85878 : b = sk5 ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq85828 bc
    first | exact resolve eq85828 bc | exact resolve bc eq85828 | grind only
  have eq85955 : (old b b sk4) ∨ a = b ∨ c = b ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq391 eq85878
    first | exact Or.assoc3 (eq85878.imp_left (fun h : b = sk5 => superpose h eq391)) | exact superpose eq391 eq85878 | exact superpose eq85878 eq391 | grind only
  have eq86050 : (sP0 b b c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = b ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq30699 eq85878
    first | exact Or.assoc6 (eq85878.imp_left (fun h : b = sk5 => superpose h eq30699)) | exact superpose eq30699 eq85878 | exact superpose eq85878 eq30699 | grind only
  have eq86057 : (sP0 b b c) ∨ c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq86050
    first | exact resolve eq86050 rfl | grind only
  have eq86100 : (old b b sk4) ∨ a = b ∨ c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq85955
    first | exact resolve eq85955 rfl | grind only
  have eq86103 : c = sk0 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq86057 rule_def_0_0
    first | exact resolve eq86057 rule_def_0_0 | exact resolve rule_def_0_0 eq86057 | grind only
  have eq86136 : (old b b sk4) ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq86100 bc
    first | exact resolve eq86100 bc | exact resolve bc eq86100 | grind only
  have eq86141 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ a = b ∨ b = sk0 := by
    clear * - eq86103 bc
    first | exact resolve eq86103 bc | exact resolve bc eq86103 | grind only
  have eq86556 : (old b b a) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq86136 eq43499
    first | exact Or.assoc4 (eq43499.imp_left (fun h : a = sk4 => superpose h eq86136)) | exact superpose eq86136 eq43499 | exact superpose eq43499 eq86136 | grind only
  have eq86577 : (old b b a) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq86556
    first | exact resolve eq86556 rfl | grind only
  have eq86637 : a = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ b = sk1 ∨ c = sk1 ∨ a = sk5 := by
    clear * - eq86577 eq42491
    first | exact resolve eq86577 eq42491 | exact resolve eq42491 eq86577 | grind only
  have eq86644 : c = sk1 ∨ c = sk0 ∨ c = sk5 ∨ b = sk1 ∨ b = sk0 ∨ a = sk5 := by
    clear * - eq86637 eq42365
    first | exact resolve eq86637 eq42365 | exact resolve eq42365 eq86637 | grind only
  have eq99371 : b = sk5 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 := by
    clear * - eq75019 eq74570
    first | exact resolve eq75019 eq74570 | exact resolve eq74570 eq75019 | grind only
  have eq99414 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ b = sk5 := by
    clear * - eq99371
    first | exact resolve eq99371 rfl | grind only
  have eq99720 : (old sk1 sk2 c) ∨ (old b a c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ b = sk5 := by
    clear * - eq2387 eq99414
    first | exact Or.assoc4 (eq99414.imp_left (fun h : c = sk3 => superpose h eq2387)) | exact superpose eq2387 eq99414 | exact superpose eq99414 eq2387 | grind only
  have eq100188 : (old sk1 sk2 c) ∨ (old b a c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ b = sk5 := by
    clear * - eq99720
    first | exact resolve eq99720 rfl | grind only
  have eq100246 : (old b a c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ b = sk5 := by
    clear * - eq100188 p4XY
    first | exact resolve eq100188 p4XY | exact resolve p4XY eq100188 | grind only
  have eq100294 : c = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ b = sk5 := by
    clear * - eq100246 p4XY
    first | exact resolve eq100246 p4XY | exact resolve p4XY eq100246 | grind only
  have eq100655 : c = b ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ b = sk5 := by
    clear * - eq77158 eq100294
    first | exact Or.assoc4 (eq100294.imp_left (fun h : c = sk2 => superpose h eq77158)) | exact superpose eq77158 eq100294 | exact superpose eq100294 eq77158 | grind only
  have eq100666 : c = b ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ a = sk1 := by
    clear * - eq100655
    first | exact resolve eq100655 rfl | grind only
  have eq100789 : a = sk1 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq100666 bc
    first | exact resolve eq100666 bc | exact resolve bc eq100666 | grind only
  have eq101037 : (old sk0 sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq305 eq100789
    first | exact Or.assoc3 (eq100789.imp_left (fun h : a = sk1 => superpose h eq305)) | exact superpose eq305 eq100789 | exact superpose eq100789 eq305 | grind only
  have eq101522 : (old sk0 sk0 a) ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq101037
    first | exact resolve eq101037 rfl | grind only
  have eq103640 : a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk5 ∨ sk0 = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq101522 eq22824
    first | exact resolve eq101522 eq22824 | exact resolve eq22824 eq101522 | grind only
  have eq103739 : a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ sk0 = sk5 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq103640
    first | exact resolve eq103640 rfl | grind only
  have eq103742 : c = sk2 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq103739 preserve_4
    first | exact resolve eq103739 preserve_4 | exact resolve preserve_4 eq103739 | grind only
  have eq107718 : c = b ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq77158 eq103742
    first | exact Or.assoc4 (eq103742.imp_left (fun h : c = sk2 => superpose h eq77158)) | exact superpose eq77158 eq103742 | exact superpose eq103742 eq77158 | grind only
  have eq107739 : c = b ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq107718
    first | exact resolve eq107718 rfl | grind only
  have eq107849 : c = sk1 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq107739 bc
    first | exact resolve eq107739 bc | exact resolve bc eq107739 | grind only
  have eq108303 : a = c ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq100789 eq107849
    first | exact Or.assoc4 (eq107849.imp_left (fun h : c = sk1 => superpose h eq100789)) | exact superpose eq100789 eq107849 | exact superpose eq107849 eq100789 | grind only
  have eq108308 : a = c ∨ b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq108303
    first | exact resolve eq108303 rfl | grind only
  have eq108437 : b = sk5 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq108308 ac
    first | exact resolve eq108308 ac | exact resolve ac eq108308 | grind only
  have eq108617 : b ≠ sk0 ∨ a = sk0 ∨ c = sk0 := by
    clear * - preserve_4 eq108437
    first | exact (eq108437.imp_left (fun h : b = sk5 => superpose h preserve_4)) | exact superpose preserve_4 eq108437 | exact superpose eq108437 preserve_4 | grind only
  have eq108618 (X0 : G) : ¬(new b b X0) ∨ sk4 = X0 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq98 eq108437
    first | exact Or.assoc2 (eq108437.imp_left (fun h : b = sk5 => superpose h eq98)) | exact superpose eq98 eq108437 | exact superpose eq108437 eq98 | grind only
  have eq108735 : (new b b b) ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = b ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq31572 eq108437
    first | exact Or.assoc5 (eq108437.imp_left (fun h : b = sk5 => superpose h eq31572)) | exact superpose eq31572 eq108437 | exact superpose eq108437 eq31572 | grind only
  have eq108738 : (new b b b) ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = b := by
    clear * - eq108735
    first | exact resolve eq108735 rfl | grind only
  have eq108753 : (new b b b) ∨ b = sk2 ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq108738 bc
    first | exact resolve eq108738 bc | exact resolve bc eq108738 | grind only
  have eq110507 : ¬(new b sk2 sk1) ∨ c = sk0 ∨ a = sk0 ∨ b = sk2 ∨ (new sk2 sk3 b) := by
    clear * - eq108753 eq109
    first | exact resolve eq108753 eq109 | exact resolve eq109 eq108753 | grind only
  have eq119391 : b = sk5 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ c = sk3 ∨ b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq75644 eq75192
    first | exact resolve eq75644 eq75192 | exact resolve eq75192 eq75644 | grind only
  have eq119441 : c = sk3 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq119391
    first | exact resolve eq119391 rfl | grind only
  have eq119642 : (old sk1 sk2 c) ∨ (old b a c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq2387 eq119441
    first | exact Or.assoc4 (eq119441.imp_left (fun h : c = sk3 => superpose h eq2387)) | exact superpose eq2387 eq119441 | exact superpose eq119441 eq2387 | grind only
  have eq120205 : (old sk1 sk2 c) ∨ (old b a c) ∨ a = sk1 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq119642
    first | exact resolve eq119642 rfl | grind only
  have eq120272 : (old b a c) ∨ a = sk1 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq120205 p4XY
    first | exact resolve eq120205 p4XY | exact resolve p4XY eq120205 | grind only
  have eq120320 : c = sk2 ∨ a = sk1 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq120272 p4XY
    first | exact resolve eq120272 p4XY | exact resolve p4XY eq120272 | grind only
  have eq120635 : c = b ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq78029 eq120320
    first | exact Or.assoc4 (eq120320.imp_left (fun h : c = sk2 => superpose h eq78029)) | exact superpose eq78029 eq120320 | exact superpose eq120320 eq78029 | grind only
  have eq120662 : c = b ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 := by
    clear * - eq120635
    first | exact resolve eq120635 rfl | grind only
  have eq120812 : a = sk1 ∨ c = sk0 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq120662 bc
    first | exact resolve eq120662 bc | exact resolve bc eq120662 | grind only
  have eq120934 : (old sk0 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq146 eq120812
    first | exact Or.assoc2 (eq120812.imp_left (fun h : a = sk1 => superpose h eq146)) | exact superpose eq146 eq120812 | exact superpose eq120812 eq146 | grind only
  have eq121500 : (old sk0 sk0 a) ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 := by
    clear * - eq120934
    first | exact resolve eq120934 rfl | grind only
  have eq123578 : b = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk5 ∨ sk0 = sk5 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq121500 eq22824
    first | exact resolve eq121500 eq22824 | exact resolve eq22824 eq121500 | grind only
  have eq123684 : b = sk0 ∨ c = sk0 ∨ b = sk5 ∨ sk0 = sk5 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq123578
    first | exact resolve eq123578 rfl | grind only
  have eq123689 : c = sk2 ∨ c = sk0 ∨ b = sk5 ∨ b = sk0 ∨ c = sk1 := by
    clear * - eq123684 preserve_4
    first | exact resolve eq123684 preserve_4 | exact resolve preserve_4 eq123684 | grind only
  have eq126232 : c = b ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk5 ∨ b = sk0 ∨ c = sk1 := by
    clear * - eq78029 eq123689
    first | exact Or.assoc4 (eq123689.imp_left (fun h : c = sk2 => superpose h eq78029)) | exact superpose eq78029 eq123689 | exact superpose eq123689 eq78029 | grind only
  have eq126269 : c = b ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 := by
    clear * - eq126232
    first | exact resolve eq126232 rfl | grind only
  have eq126403 : c = sk1 ∨ c = sk0 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq126269 bc
    first | exact resolve eq126269 bc | exact resolve bc eq126269 | grind only
  have eq126859 : a = c ∨ c = sk0 ∨ b = sk0 ∨ b = sk5 ∨ c = sk0 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq120812 eq126403
    first | exact Or.assoc4 (eq126403.imp_left (fun h : c = sk1 => superpose h eq120812)) | exact superpose eq120812 eq126403 | exact superpose eq126403 eq120812 | grind only
  have eq126864 : a = c ∨ c = sk0 ∨ b = sk0 ∨ b = sk5 := by
    clear * - eq126859
    first | exact resolve eq126859 rfl | grind only
  have eq127021 : b = sk5 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq126864 ac
    first | exact resolve eq126864 ac | exact resolve ac eq126864 | grind only
  have eq127403 (X0 : G) : ¬(new b b X0) ∨ sk4 = X0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq98 eq127021
    first | exact Or.assoc2 (eq127021.imp_left (fun h : b = sk5 => superpose h eq98)) | exact superpose eq98 eq127021 | exact superpose eq127021 eq98 | grind only
  have eq127412 : (old b b sk4) ∨ c = sk4 ∨ c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq377 eq127021
    first | exact Or.assoc3 (eq127021.imp_left (fun h : b = sk5 => superpose h eq377)) | exact superpose eq377 eq127021 | exact superpose eq127021 eq377 | grind only
  have eq127460 : (new b b b) ∨ b = sk2 ∨ b = sk0 ∨ c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq4905 eq127021
    first | exact Or.assoc4 (eq127021.imp_left (fun h : b = sk5 => superpose h eq4905)) | exact superpose eq4905 eq127021 | exact superpose eq127021 eq4905 | grind only
  have eq127464 : (old b b b) ∨ c = b ∨ b = sk2 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq5030 eq127021
    first | exact Or.assoc4 (eq127021.imp_left (fun h : b = sk5 => superpose h eq5030)) | exact superpose eq5030 eq127021 | exact superpose eq127021 eq5030 | grind only
  have eq127465 (X0 : G) : ¬(new b b X0) ∨ b = sk0 ∨ c = b ∨ b = sk2 ∨ b = X0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq5204 eq127021
    first | exact Or.assoc5 (eq127021.imp_left (fun h : b = sk5 => superpose h eq5204)) | exact superpose eq5204 eq127021 | exact superpose eq127021 eq5204 | grind only
  have eq127538 (X0 : G) : ¬(new b b X0) ∨ b = sk0 ∨ c = b ∨ b = sk2 ∨ b = X0 ∨ c = sk0 := by
    clear * - eq127465
    first | exact resolve eq127465 rfl | grind only
  have eq127539 : (old b b b) ∨ c = b ∨ b = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq127464
    first | exact resolve eq127464 rfl | grind only
  have eq127543 : (new b b b) ∨ b = sk2 ∨ b = sk0 ∨ c = b ∨ c = sk0 := by
    clear * - eq127460
    first | exact resolve eq127460 rfl | grind only
  have eq127565 (X0 : G) : ¬(new b b X0) ∨ b = sk0 ∨ b = sk2 ∨ b = X0 ∨ c = sk0 := by
    clear * - eq127538 bc
    first | exact resolve eq127538 bc | exact resolve bc eq127538 | grind only
  have eq127566 : (old b b b) ∨ b = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq127539 bc
    first | exact resolve eq127539 bc | exact resolve bc eq127539 | grind only
  have eq127567 : (new b b b) ∨ b = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq127543 bc
    first | exact resolve eq127543 bc | exact resolve bc eq127543 | grind only
  have eq127581 : (old b b sk4) ∨ c = sk4 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq127412 bc
    first | exact resolve eq127412 bc | exact resolve bc eq127412 | grind only
  have eq129906 (X0 : G) : ¬(old X0 X0 b) ∨ b = sk0 ∨ c = sk0 ∨ b = sk2 ∨ b = X0 := by
    clear * - eq127566 old_3
    first | exact resolve eq127566 old_3 | exact resolve old_3 eq127566 | grind only
  have eq129939 : b = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ ¬(old b sk2 sk3) ∨ b = sk0 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq127566 eq918
    first | exact resolve eq127566 eq918 | exact resolve eq918 eq127566 | grind only
  have eq130004 : ¬(old b sk2 sk3) ∨ b = sk0 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq129939
    first | exact resolve eq129939 rfl | grind only
  have eq130190 : b = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk4 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq127567 eq127403
    first | exact resolve eq127567 eq127403 | exact resolve eq127403 eq127567 | grind only
  have eq130287 : b = sk4 ∨ b = sk0 ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq130190
    first | exact resolve eq130190 rfl | grind only
  have eq130388 : (old b sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq234 eq130287
    first | exact Or.assoc3 (eq130287.imp_left (fun h : b = sk4 => superpose h eq234)) | exact superpose eq234 eq130287 | exact superpose eq130287 eq234 | grind only
  have eq131004 : (old b sk2 sk3) ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq130388
    first | exact resolve eq130388 rfl | grind only
  have eq131142 : c = sk2 ∨ b = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq131004 eq130004
    first | exact resolve eq131004 eq130004 | exact resolve eq130004 eq131004 | grind only
  have eq131223 : (old sk1 c sk3) ∨ c = b ∨ b = sk1 ∨ b = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq220 eq131142
    first | exact Or.assoc3 (eq131142.imp_left (fun h : c = sk2 => superpose h eq220)) | exact superpose eq220 eq131142 | exact superpose eq131142 eq220 | grind only
  have eq131716 : c = b ∨ b = sk1 ∨ b = sk2 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq131223 p4XZ
    first | exact resolve eq131223 p4XZ | exact resolve p4XZ eq131223 | grind only
  have eq131765 : b = sk2 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq131716 bc
    first | exact resolve eq131716 bc | exact resolve bc eq131716 | grind only
  have eq265478 : (old sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ b = sk1 ∨ b = sk0 ∨ a = sk5 := by
    clear * - eq146 eq86644
    first | exact Or.assoc2 (eq86644.imp_left (fun h : c = sk1 => superpose h eq146)) | exact superpose eq146 eq86644 | exact superpose eq86644 eq146 | grind only
  have eq266284 : (old sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ b = sk1 ∨ a = sk5 := by
    clear * - eq265478
    first | exact resolve eq265478 rfl | grind only
  have eq266491 : b = sk1 ∨ c = sk0 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 := by
    clear * - eq266284 p4XY
    first | exact resolve eq266284 p4XY | exact resolve p4XY eq266284 | grind only
  have eq266771 : (new b sk2 sk3) ∨ c = sk0 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 := by
    clear * - preserve_1 eq266491
    first | exact (eq266491.imp_left (fun h : b = sk1 => superpose h preserve_1)) | exact superpose preserve_1 eq266491 | exact superpose eq266491 preserve_1 | grind only
  have eq266782 : (old sk0 sk0 b) ∨ b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 := by
    clear * - eq146 eq266491
    first | exact Or.assoc2 (eq266491.imp_left (fun h : b = sk1 => superpose h eq146)) | exact superpose eq146 eq266491 | exact superpose eq266491 eq146 | grind only
  have eq267660 : (old sk0 sk0 b) ∨ b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ a = sk5 := by
    clear * - eq266782
    first | exact resolve eq266782 rfl | grind only
  have eq269649 : b = sk0 ∨ c = sk0 ∨ c = sk5 ∨ a = sk5 ∨ b = sk0 ∨ c = sk0 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq267660 eq129906
    first | exact resolve eq267660 eq129906 | exact resolve eq129906 eq267660 | grind only
  have eq269770 : b = sk2 ∨ c = sk0 ∨ c = sk5 ∨ a = sk5 ∨ b = sk0 := by
    clear * - eq269649
    first | exact resolve eq269649 rfl | grind only
  have eq270428 : (new b b sk3) ∨ c = sk0 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 ∨ c = sk0 ∨ c = sk5 ∨ a = sk5 ∨ b = sk0 := by
    clear * - eq266771 eq269770
    first | exact Or.assoc5 (eq269770.imp_left (fun h : b = sk2 => superpose h eq266771)) | exact superpose eq266771 eq269770 | exact superpose eq269770 eq266771 | grind only
  have eq270429 : (new b b sk3) ∨ c = sk0 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 := by
    clear * - eq270428
    first | exact resolve eq270428 rfl | grind only
  have eq272908 : c = sk0 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 ∨ sk3 = sk4 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq270429 eq127403
    first | exact resolve eq270429 eq127403 | exact resolve eq127403 eq270429 | grind only
  have eq273041 : sk3 = sk4 ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 ∨ c = sk0 := by
    clear * - eq272908
    first | exact resolve eq272908 rfl | grind only
  have eq273142 : (new sk5 sk5 sk3) ∨ c = sk5 ∨ b = sk0 ∨ a = sk5 ∨ c = sk0 := by
    clear * - preserve_3 eq273041
    first | exact (eq273041.imp_left (fun h : sk3 = sk4 => superpose h preserve_3)) | exact superpose preserve_3 eq273041 | exact superpose eq273041 preserve_3 | grind only
  have eq277200 : (new b b sk3) ∨ c = b ∨ b = sk0 ∨ a = b ∨ c = sk0 ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq273142 eq85878
    first | exact Or.assoc5 (eq85878.imp_left (fun h : b = sk5 => superpose h eq273142)) | exact superpose eq273142 eq85878 | exact superpose eq85878 eq273142 | grind only
  have eq277201 : (new b b sk3) ∨ c = b ∨ b = sk0 ∨ a = b ∨ c = sk0 ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq273142 eq84403
    first | exact Or.assoc5 (eq84403.imp_left (fun h : b = sk5 => superpose h eq273142)) | exact superpose eq273142 eq84403 | exact superpose eq84403 eq273142 | grind only
  have eq277246 : (new b b sk3) ∨ c = b ∨ b = sk0 ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq277201
    first | exact resolve eq277201 rfl | grind only
  have eq277247 : (new b b sk3) ∨ c = b ∨ b = sk0 ∨ a = b ∨ c = sk0 := by
    clear * - eq277200
    first | exact resolve eq277200 rfl | grind only
  have eq277264 : (new b b sk3) ∨ c = b ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq277246 eq108617
    first | exact resolve eq277246 eq108617 | exact resolve eq108617 eq277246 | grind only
  have eq277265 : (new b b sk3) ∨ b = sk0 ∨ a = b ∨ c = sk0 := by
    clear * - eq277247 bc
    first | exact resolve eq277247 bc | exact resolve bc eq277247 | grind only
  have eq277273 : (new b b sk3) ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq277264 bc
    first | exact resolve eq277264 bc | exact resolve bc eq277264 | grind only
  have eq277309 : b = sk0 ∨ a = b ∨ c = sk0 ∨ sk3 = sk4 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq277265 eq127403
    first | exact resolve eq277265 eq127403 | exact resolve eq127403 eq277265 | grind only
  have eq277310 : b = sk0 ∨ a = b ∨ c = sk0 ∨ b = sk0 ∨ b = sk2 ∨ b = sk3 ∨ c = sk0 := by
    clear * - eq277265 eq127565
    first | exact resolve eq277265 eq127565 | exact resolve eq127565 eq277265 | grind only
  have eq277437 : b = sk3 ∨ a = b ∨ c = sk0 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq277310
    first | exact resolve eq277310 rfl | grind only
  have eq277438 : sk3 = sk4 ∨ a = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq277309
    first | exact resolve eq277309 rfl | grind only
  have eq278223 : (old b b sk3) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq86136 eq277438
    first | exact Or.assoc4 (eq277438.imp_left (fun h : sk3 = sk4 => superpose h eq86136)) | exact superpose eq86136 eq277438 | exact superpose eq277438 eq86136 | grind only
  have eq278512 : (old b b sk3) ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq278223
    first | exact resolve eq278223 rfl | grind only
  have eq279070 : a = b ∨ c = sk0 ∨ a = sk0 ∨ sk3 = sk4 ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq277273 eq108618
    first | exact resolve eq277273 eq108618 | exact resolve eq108618 eq277273 | grind only
  have eq279201 : sk3 = sk4 ∨ c = sk0 ∨ a = sk0 ∨ a = b := by
    clear * - eq279070
    first | exact resolve eq279070 rfl | grind only
  have eq279300 : (new sk3 sk2 sk3) ∨ c = sk0 ∨ a = sk0 ∨ a = b := by
    clear * - preserve_2 eq279201
    first | exact (eq279201.imp_left (fun h : sk3 = sk4 => superpose h preserve_2)) | exact superpose preserve_2 eq279201 | exact superpose eq279201 preserve_2 | grind only
  have eq279307 : ¬(new sk1 sk2 sk3) ∨ (new sk2 sk3 sk0) ∨ c = sk0 ∨ a = sk0 ∨ a = b := by
    clear * - eq138 eq279201
    first | exact Or.assoc2 (eq279201.imp_left (fun h : sk3 = sk4 => superpose h eq138)) | exact superpose eq138 eq279201 | exact superpose eq279201 eq138 | grind only
  have eq280621 : (new sk2 sk3 sk0) ∨ c = sk0 ∨ a = sk0 ∨ a = b := by
    clear * - eq279307 preserve_1
    first | exact resolve eq279307 preserve_1 | exact resolve preserve_1 eq279307 | grind only
  have eq281124 : (old b b c) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ a = b ∨ a = sk0 := by
    clear * - eq278512 eq84663
    first | exact Or.assoc4 (eq84663.imp_left (fun h : c = sk3 => superpose h eq278512)) | exact superpose eq278512 eq84663 | exact superpose eq84663 eq278512 | grind only
  have eq281125 : (old b b c) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ a = b ∨ b = sk0 := by
    clear * - eq278512 eq86141
    first | exact Or.assoc4 (eq86141.imp_left (fun h : c = sk3 => superpose h eq278512)) | exact superpose eq278512 eq86141 | exact superpose eq86141 eq278512 | grind only
  have eq281138 : (old b b c) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq281125
    first | exact resolve eq281125 rfl | grind only
  have eq281139 : (old b b c) ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := by
    clear * - eq281124
    first | exact resolve eq281124 rfl | grind only
  have eq281191 : c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ c = sk1 := by
    clear * - eq281138 p4XY
    first | exact resolve eq281138 p4XY | exact resolve p4XY eq281138 | grind only
  have eq281192 : (old b b c) ∨ a = b ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := by
    clear * - eq281139 eq108617
    first | exact resolve eq281139 eq108617 | exact resolve eq108617 eq281139 | grind only
  have eq281199 : c = sk2 ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ a = sk0 := by
    clear * - eq281192 p4XY
    first | exact resolve eq281192 p4XY | exact resolve p4XY eq281192 | grind only
  have eq282397 (X0 : G) : c = sk0 ∨ a = sk0 ∨ a = b ∨ ¬(new sk2 sk3 X0) ∨ sk0 = X0 := by
    clear * - eq280621 prev_0
    first | exact resolve eq280621 prev_0 | exact resolve prev_0 eq280621 | grind only
  have eq283686 : (new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ a = b ∨ c = sk0 ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq279300 eq277437
    first | exact Or.assoc4 (eq277437.imp_left (fun h : b = sk3 => superpose h eq279300)) | exact superpose eq279300 eq277437 | exact superpose eq277437 eq279300 | grind only
  have eq283691 : (new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ b = sk2 ∨ b = sk0 := by
    clear * - eq283686
    first | exact resolve eq283686 rfl | grind only
  have eq284317 : (new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ b = sk2 := by
    clear * - eq283691 eq108617
    first | exact resolve eq283691 eq108617 | exact resolve eq108617 eq283691 | grind only
  have eq286992 : c = b ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ c = sk1 := by
    clear * - eq131765 eq281191
    first | exact Or.assoc4 (eq281191.imp_left (fun h : c = sk2 => superpose h eq131765)) | exact superpose eq131765 eq281191 | exact superpose eq281191 eq131765 | grind only
  have eq287015 : c = b ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ c = sk1 := by
    clear * - eq286992
    first | exact resolve eq286992 rfl | grind only
  have eq287340 : c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ b = sk1 := by
    clear * - eq287015 bc
    first | exact resolve eq287015 bc | exact resolve bc eq287015 | grind only
  have eq288993 : (old sk0 sk0 c) ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ b = sk1 := by
    clear * - eq146 eq287340
    first | exact Or.assoc2 (eq287340.imp_left (fun h : c = sk1 => superpose h eq146)) | exact superpose eq146 eq287340 | exact superpose eq287340 eq146 | grind only
  have eq289011 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ b = sk1 := by
    clear * - eq305 eq287340
    first | exact Or.assoc3 (eq287340.imp_left (fun h : c = sk1 => superpose h eq305)) | exact superpose eq305 eq287340 | exact superpose eq287340 eq305 | grind only
  have eq289791 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = b ∨ b = sk1 := by
    clear * - eq289011
    first | exact resolve eq289011 rfl | grind only
  have eq289795 : (old sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ b = sk1 := by
    clear * - eq288993
    first | exact resolve eq288993 rfl | grind only
  have eq289996 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ a = b ∨ b = sk1 := by
    clear * - eq289791 eq108617
    first | exact resolve eq289791 eq108617 | exact resolve eq108617 eq289791 | grind only
  have eq290001 : b = sk1 ∨ c = sk0 ∨ a = b ∨ b = sk0 := by
    clear * - eq289795 p4XY
    first | exact resolve eq289795 p4XY | exact resolve p4XY eq289795 | grind only
  have eq290122 : b = sk1 ∨ c = sk0 ∨ a = b ∨ a = sk0 := by
    clear * - eq289996 p4XY
    first | exact resolve eq289996 p4XY | exact resolve p4XY eq289996 | grind only
  have eq290282 : (new sk0 sk0 b) ∨ c = sk0 ∨ a = b ∨ b = sk0 := by
    clear * - preserve_0 eq290001
    first | exact (eq290001.imp_left (fun h : b = sk1 => superpose h preserve_0)) | exact superpose preserve_0 eq290001 | exact superpose eq290001 preserve_0 | grind only
  have eq290793 : ¬(new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ b = sk2 ∨ (new sk2 sk3 b) ∨ c = sk0 ∨ a = b ∨ b = sk0 := by
    clear * - eq110507 eq290001
    first | exact Or.assoc5 (eq290001.imp_left (fun h : b = sk1 => superpose h eq110507)) | exact superpose eq110507 eq290001 | exact superpose eq290001 eq110507 | grind only
  have eq290896 : ¬(new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ b = sk2 ∨ (new sk2 sk3 b) ∨ a = b ∨ b = sk0 := by
    clear * - eq290793
    first | exact resolve eq290793 rfl | grind only
  have eq291249 : ¬(new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ b = sk2 ∨ a = b ∨ b = sk0 := by
    clear * - eq290896 eq282397
    first | exact resolve eq290896 eq282397 | exact resolve eq282397 eq290896 | grind only
  have eq291425 : ¬(new b sk2 b) ∨ c = sk0 ∨ a = sk0 ∨ b = sk2 ∨ a = b := by
    clear * - eq291249 eq108617
    first | exact resolve eq291249 eq108617 | exact resolve eq108617 eq291249 | grind only
  have eq291456 : b = sk2 ∨ a = sk0 ∨ c = sk0 ∨ a = b := by
    clear * - eq291425 eq284317
    first | exact resolve eq291425 eq284317 | exact resolve eq284317 eq291425 | grind only
  have eq293306 : c = b ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = b := by
    clear * - eq281199 eq291456
    first | exact Or.assoc5 (eq291456.imp_left (fun h : b = sk2 => superpose h eq281199)) | exact superpose eq281199 eq291456 | exact superpose eq291456 eq281199 | grind only
  have eq293307 : c = b ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ a = sk0 := by
    clear * - eq293306
    first | exact resolve eq293306 rfl | grind only
  have eq293548 : c = sk1 ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq293307 bc
    first | exact resolve eq293307 bc | exact resolve bc eq293307 | grind only
  have eq294348 : c = b ∨ c = sk0 ∨ a = b ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ a = sk0 := by
    clear * - eq290122 eq293548
    first | exact Or.assoc4 (eq293548.imp_left (fun h : c = sk1 => superpose h eq290122)) | exact superpose eq290122 eq293548 | exact superpose eq293548 eq290122 | grind only
  have eq294349 : c = b ∨ c = sk0 ∨ a = b ∨ a = sk0 := by
    clear * - eq294348
    first | exact resolve eq294348 rfl | grind only
  have eq294606 : a = sk0 ∨ a = b ∨ c = sk0 := by
    clear * - eq294349 bc
    first | exact resolve eq294349 bc | exact resolve bc eq294349 | grind only
  have eq294916 : (old a a sk1) ∨ a = b ∨ a = b ∨ c = sk0 := by
    clear * - eq146 eq294606
    first | exact Or.assoc2 (eq294606.imp_left (fun h : a = sk0 => superpose h eq146)) | exact superpose eq146 eq294606 | exact superpose eq294606 eq146 | grind only
  have eq295115 : (old a a sk1) ∨ a = b ∨ c = sk0 := by
    clear * - eq294916
    first | exact resolve eq294916 rfl | grind only
  have eq299739 : (new a a b) ∨ a = c ∨ a = b ∨ a = b ∨ a = b ∨ c = sk0 := by
    clear * - eq290282 eq294606
    first | exact Or.assoc4 (eq294606.imp_left (fun h : a = sk0 => superpose h eq290282)) | exact superpose eq290282 eq294606 | exact superpose eq294606 eq290282 | grind only
  have eq299740 : (new a a b) ∨ a = c ∨ a = b ∨ c = sk0 := by
    clear * - eq299739
    first | exact resolve eq299739 rfl | grind only
  have eq299747 : (new a a b) ∨ a = b ∨ c = sk0 := by
    clear * - eq299740 ac
    first | exact resolve eq299740 ac | exact resolve ac eq299740 | grind only
  have eq299891 : a = b ∨ c = sk0 ∨ (old a a b) ∨ (sP0 a a b) ∨ (sP1 a a b) ∨ (sP2 a a b) := by
    clear * - eq299747 new_imp
    first | exact resolve eq299747 new_imp | exact resolve new_imp eq299747 | grind only
  have eq299895 : a = b ∨ c = sk0 ∨ (old a a b) ∨ (sP1 a a b) ∨ (sP2 a a b) := by
    clear * - eq299891 rule_def_0_1
    first | exact resolve eq299891 rule_def_0_1 | exact resolve rule_def_0_1 eq299891 | grind only
  have eq299905 : a = b ∨ c = sk0 ∨ (old a a b) ∨ (sP2 a a b) := by
    clear * - eq299895 rule_def_1_0
    first | exact resolve eq299895 rule_def_1_0 | exact resolve rule_def_1_0 eq299895 | grind only
  have eq299906 : (old a a b) ∨ c = sk0 ∨ a = b := by
    clear * - eq299905 rule_def_2_1
    first | exact resolve eq299905 rule_def_2_1 | exact resolve rule_def_2_1 eq299905 | grind only
  have eq300026 : c = sk0 ∨ a = b ∨ b = sk0 ∨ c = sk0 ∨ b = sk2 ∨ a = b := by
    clear * - eq299906 eq129906
    first | exact resolve eq299906 eq129906 | exact resolve eq129906 eq299906 | grind only
  have eq300124 : b = sk2 ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq300026
    first | exact resolve eq300026 rfl | grind only
  have eq300842 : c = b ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ a = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq281191 eq300124
    first | exact Or.assoc5 (eq300124.imp_left (fun h : b = sk2 => superpose h eq281191)) | exact superpose eq281191 eq300124 | exact superpose eq300124 eq281191 | grind only
  have eq300849 : c = b ∨ b = sk0 ∨ c = sk0 ∨ a = b ∨ c = sk1 := by
    clear * - eq300842
    first | exact resolve eq300842 rfl | grind only
  have eq301149 : c = sk1 ∨ c = sk0 ∨ a = b ∨ b = sk0 := by
    clear * - eq300849 bc
    first | exact resolve eq300849 bc | exact resolve bc eq300849 | grind only
  have eq301921 : (old a a c) ∨ a = b ∨ c = sk0 ∨ c = sk0 ∨ a = b ∨ b = sk0 := by
    clear * - eq295115 eq301149
    first | exact Or.assoc3 (eq301149.imp_left (fun h : c = sk1 => superpose h eq295115)) | exact superpose eq295115 eq301149 | exact superpose eq301149 eq295115 | grind only
  have eq301924 : (old a a c) ∨ a = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq301921
    first | exact resolve eq301921 rfl | grind only
  have eq302239 : c = sk0 ∨ a = b ∨ b = sk0 := by
    clear * - eq301924 p4XY
    first | exact resolve eq301924 p4XY | exact resolve p4XY eq301924 | grind only
  have eq302567 : a = c ∨ a = b ∨ a = b ∨ a = b ∨ c = sk0 := by
    clear * - eq302239 eq294606
    first | exact Or.assoc3 (eq294606.imp_left (fun h : a = sk0 => superpose h eq302239)) | exact superpose eq302239 eq294606 | exact superpose eq294606 eq302239 | grind only
  have eq302695 : a = c ∨ a = b ∨ c = sk0 := by
    clear * - eq302567
    first | exact resolve eq302567 rfl | grind only
  have eq302771 : c = sk0 ∨ a = b := by
    clear * - eq302695 ac
    first | exact resolve eq302695 ac | exact resolve ac eq302695 | grind only
  have eq303064 : (old c c sk1) ∨ c = b ∨ a = b := by
    clear * - eq146 eq302771
    first | exact Or.assoc2 (eq302771.imp_left (fun h : c = sk0 => superpose h eq146)) | exact superpose eq146 eq302771 | exact superpose eq302771 eq146 | grind only
  have eq303257 : c = b ∨ a = b := by
    clear * - eq303064 p4XZ
    first | exact resolve eq303064 p4XZ | exact resolve p4XZ eq303064 | grind only
  have eq303301 : a = b := by
    clear * - eq303257 bc
    first | exact resolve eq303257 bc | exact resolve bc eq303257 | grind only
  have eq303565 (X0 : G) : ¬(old b b X0) := by
    clear * - p3 eq303301
    first | exact superpose p3 eq303301 | exact superpose eq303301 p3 | grind only
  have eq304095 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := by
    clear * - eq303565 rule_def_2_2
    first | exact resolve eq303565 rule_def_2_2 | exact resolve rule_def_2_2 eq303565 | grind only
  have eq304098 : c = sk4 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq303565 eq127581
    first | exact resolve eq303565 eq127581 | exact resolve eq127581 eq303565 | grind only
  have eq304907 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ b = sk1 := by
    clear * - eq304095 eq343
    first | exact resolve eq304095 eq343 | exact resolve eq343 eq304095 | grind only
  have eq304930 : (old sk4 sk2 sk3) ∨ a = sk4 ∨ b = sk4 := by
    clear * - eq304095 eq365
    first | exact resolve eq304095 eq365 | exact resolve eq365 eq304095 | grind only
  have eq305047 : b = sk4 ∨ (old sk4 sk2 sk3) ∨ b = sk4 := by
    clear * - eq304930 eq303301
    first | simpa only [eq303301, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq304930 | grind only
  have eq305048 : (old sk4 sk2 sk3) ∨ b = sk4 := by
    clear * - eq305047
    first | exact resolve eq305047 rfl | grind only
  have eq305063 : b = sk1 ∨ (old sk1 sk2 sk3) ∨ b = sk1 := by
    clear * - eq304907 eq303301
    first | simpa only [eq303301, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq304907 | grind only
  have eq305064 : (old sk1 sk2 sk3) ∨ b = sk1 := by
    clear * - eq305063
    first | exact resolve eq305063 rfl | grind only
  have eq312060 : (old c sk2 sk3) ∨ c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq305048 eq304098
    first | exact Or.assoc2 (eq304098.imp_left (fun h : c = sk4 => superpose h eq305048)) | exact superpose eq305048 eq304098 | exact superpose eq304098 eq305048 | grind only
  have eq312479 : c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq312060 p4YZ
    first | exact resolve eq312060 p4YZ | exact resolve p4YZ eq312060 | grind only
  have eq312680 : c = sk0 ∨ b = sk0 := by
    clear * - eq312479 bc
    first | exact resolve eq312479 bc | exact resolve bc eq312479 | grind only
  have eq312914 : (old c c sk1) ∨ c = b ∨ b = sk0 := by
    clear * - eq146 eq312680
    first | exact Or.assoc2 (eq312680.imp_left (fun h : c = sk0 => superpose h eq146)) | exact superpose eq146 eq312680 | exact superpose eq312680 eq146 | grind only
  have eq313104 : c = b ∨ b = sk0 := by
    clear * - eq312914 p4XZ
    first | exact resolve eq312914 p4XZ | exact resolve p4XZ eq312914 | grind only
  have eq313158 : b = sk0 := by
    clear * - eq313104 bc
    first | exact resolve eq313104 bc | exact resolve bc eq313104 | grind only
  have eq313292 : (old b b sk1) ∨ c = sk1 ∨ c = b := by
    clear * - eq274 eq313158
    first | exact superpose eq274 eq313158 | exact superpose eq313158 eq274 | grind only
  have eq313520 : c = sk1 ∨ c = b := by
    clear * - eq313292 eq303565
    first | exact resolve eq313292 eq303565 | exact resolve eq303565 eq313292 | grind only
  have eq313557 : c = sk1 := by
    clear * - eq313520 bc
    first | exact resolve eq313520 bc | exact resolve bc eq313520 | grind only
  have eq314222 : (old c sk2 sk3) ∨ c = b := by
    clear * - eq305064 eq313557
    first | exact superpose eq305064 eq313557 | exact superpose eq313557 eq305064 | grind only
  have eq314227 : c = b := by
    clear * - eq314222 p4YZ
    first | exact resolve eq314222 p4YZ | exact resolve p4YZ eq314222 | grind only
  clear * - eq314227 bc
  first | subsumption eq314227 bc | grind only


set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (old_3 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X1 ∨ X2 = X0)) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X2 X1 ∨ X2 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq125 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq126 : (sP0 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ (sP1 sk2 sk2 sk1) ∨ (sP2 sk2 sk2 sk1) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq130 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq125 rule_def_0_2
    first | exact resolve eq125 rule_def_0_2 | exact resolve rule_def_0_2 eq125 | grind only
  have eq131 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq125 rule_def_0_1
    first | exact resolve eq125 rule_def_0_1 | exact resolve rule_def_0_1 eq125 | grind only
  have eq133 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq131 rule_def_1_0
    first | exact resolve eq131 rule_def_1_0 | exact resolve rule_def_1_0 eq131 | grind only
  have eq134 : (old sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq133 rule_def_2_1
    first | exact resolve eq133 rule_def_2_1 | exact resolve rule_def_2_1 eq133 | grind only
  have eq135 : (sP1 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ (sP2 sk2 sk2 sk1) ∨ c = sk1 := by
    clear * - eq126 rule_def_0_2
    first | exact resolve eq126 rule_def_0_2 | exact resolve rule_def_0_2 eq126 | grind only
  have eq136 : (old sk2 sk2 sk1) ∨ (sP1 sk2 sk2 sk1) ∨ (sP2 sk2 sk2 sk1) ∨ b = sk2 := by
    clear * - eq126 rule_def_0_1
    first | exact resolve eq126 rule_def_0_1 | exact resolve rule_def_0_1 eq126 | grind only
  have eq138 : (old sk2 sk2 sk1) ∨ (sP2 sk2 sk2 sk1) ∨ b = sk2 := by
    clear * - eq136 rule_def_1_0
    first | exact resolve eq136 rule_def_1_0 | exact resolve rule_def_1_0 eq136 | grind only
  have eq139 : (old sk2 sk2 sk1) ∨ b = sk2 := by
    clear * - eq138 rule_def_2_1
    first | exact resolve eq138 rule_def_2_1 | exact resolve rule_def_2_1 eq138 | grind only
  have eq142 (X0 : G) : ¬(old X0 X0 sk1) ∨ b = sk0 ∨ sk0 = X0 := by
    clear * - eq134 old_3
    first | exact resolve eq134 old_3 | exact resolve old_3 eq134 | grind only
  have eq150 (X0 : G) : ¬(old X0 X0 sk1) ∨ b = sk2 ∨ sk2 = X0 := by
    clear * - eq139 old_3
    first | exact resolve eq139 old_3 | exact resolve old_3 eq139 | grind only
  have eq159 : b = sk0 ∨ sk0 = sk2 ∨ b = sk2 := by
    clear * - eq142 eq139
    first | exact resolve eq142 eq139 | exact resolve eq139 eq142 | grind only
  have eq161 : b = sk2 ∨ b = sk0 := by
    clear * - eq159 preserve_2
    first | exact resolve eq159 preserve_2 | exact resolve preserve_2 eq159 | grind only
  have eq233 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq130 rule_def_1_1
    first | exact resolve eq130 rule_def_1_1 | exact resolve rule_def_1_1 eq130 | grind only
  have eq235 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq233 rule_def_2_0
    first | exact resolve eq233 rule_def_2_0 | exact resolve rule_def_2_0 eq233 | grind only
  have eq239 : c = sk1 ∨ c = sk0 ∨ b = sk2 ∨ sk0 = sk2 := by
    clear * - eq235 eq150
    first | exact resolve eq235 eq150 | exact resolve eq150 eq235 | grind only
  have eq248 : c = sk1 ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq239 preserve_2
    first | exact resolve eq239 preserve_2 | exact resolve preserve_2 eq239 | grind only
  have eq262 : (old sk2 sk2 c) ∨ b = sk2 ∨ c = sk0 ∨ b = sk2 := by
    clear * - eq139 eq248
    first | exact Or.assoc2 (eq248.imp_left (fun h : c = sk1 => superpose h eq139)) | exact superpose eq139 eq248 | exact superpose eq248 eq139 | grind only
  have eq274 : (old sk2 sk2 c) ∨ b = sk2 ∨ c = sk0 := by
    clear * - eq262
    first | exact resolve eq262 rfl | grind only
  have eq275 : b = sk2 ∨ c = sk0 := by
    clear * - eq274 p4XY
    first | exact resolve eq274 p4XY | exact resolve p4XY eq274 | grind only
  have eq282 : b ≠ sk0 ∨ c = sk0 := by
    clear * - preserve_2 eq275
    first | exact (eq275.imp_left (fun h : b = sk2 => superpose h preserve_2)) | exact superpose preserve_2 eq275 | exact superpose eq275 preserve_2 | grind only
  have eq353 : (old sk2 sk2 sk1) ∨ (sP2 sk2 sk2 sk1) ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq135 rule_def_1_1
    first | exact resolve eq135 rule_def_1_1 | exact resolve rule_def_1_1 eq135 | grind only
  have eq357 : (old sk2 sk2 sk1) ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq353 rule_def_2_0
    first | exact resolve eq353 rule_def_2_0 | exact resolve rule_def_2_0 eq353 | grind only
  have eq360 : c = sk1 ∨ c = sk2 ∨ b = sk0 ∨ sk0 = sk2 := by
    clear * - eq357 eq142
    first | exact resolve eq357 eq142 | exact resolve eq142 eq357 | grind only
  have eq372 : c = sk1 ∨ c = sk2 ∨ b = sk0 := by
    clear * - eq360 preserve_2
    first | exact resolve eq360 preserve_2 | exact resolve preserve_2 eq360 | grind only
  have eq392 : (old sk0 sk0 c) ∨ b = sk0 ∨ c = sk2 ∨ b = sk0 := by
    clear * - eq134 eq372
    first | exact Or.assoc2 (eq372.imp_left (fun h : c = sk1 => superpose h eq134)) | exact superpose eq134 eq372 | exact superpose eq372 eq134 | grind only
  have eq415 : (old sk0 sk0 c) ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq392
    first | exact resolve eq392 rfl | grind only
  have eq420 : c = sk2 ∨ b = sk0 := by
    clear * - eq415 p4XY
    first | exact resolve eq415 p4XY | exact resolve p4XY eq415 | grind only
  have eq440 : c = b ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq161 eq420
    first | exact Or.assoc2 (eq420.imp_left (fun h : c = sk2 => superpose h eq161)) | exact superpose eq161 eq420 | exact superpose eq420 eq161 | grind only
  have eq447 : c = b ∨ b = sk0 := by
    clear * - eq440
    first | exact resolve eq440 rfl | grind only
  have eq451 : b = sk0 := by
    clear * - eq447 bc
    first | exact resolve eq447 bc | exact resolve bc eq447 | grind only
  have eq471 : b ≠ b ∨ c = b := by
    clear * - eq282 eq451
    first | exact superpose eq282 eq451 | exact superpose eq451 eq282 | grind only
  have eq473 : c = b := by
    clear * - eq471
    first | exact resolve eq471 rfl | grind only
  clear * - eq473 bc
  first | subsumption eq473 bc | grind only


set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X0 X1 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X2 X4 ∨ new X2 X4 X0)) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X3 ∨ ¬ new X3 X1 X0 ∨ ¬ new X4 X4 X1 ∨ new X2 X1 X4) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq114 (X0 X1 : G) : ¬(new X1 X1 X0) ∨ ¬(new X0 sk1 sk0) ∨ (new sk1 sk2 X1) := by
    clear * - prev_1 preserve_0
    first | exact resolve prev_1 preserve_0 | exact resolve preserve_0 prev_1 | grind only
  have eq130 : ¬(new sk3 sk1 sk0) ∨ (new sk1 sk2 sk1) := by
    clear * - eq114 preserve_1
    first | exact resolve eq114 preserve_1 | exact resolve preserve_1 eq114 | grind only
  have eq132 : (new sk1 sk2 sk1) := by
    clear * - eq130 preserve_2
    first | exact resolve eq130 preserve_2 | exact resolve preserve_2 eq130 | grind only
  have eq135 (X0 X1 : G) : ¬(new X1 X1 X0) ∨ ¬(new X0 sk2 sk1) ∨ (new sk2 sk1 X1) := by
    clear * - eq132 prev_1
    first | exact resolve eq132 prev_1 | exact resolve prev_1 eq132 | grind only
  have eq310 : ¬(new sk1 sk2 sk1) ∨ (new sk2 sk1 sk4) := by
    clear * - eq135 preserve_3
    first | exact resolve eq135 preserve_3 | exact resolve preserve_3 eq135 | grind only
  have eq311 : (new sk2 sk1 sk4) := by
    clear * - eq310 eq132
    first | exact resolve eq310 eq132 | exact resolve eq132 eq310 | grind only
  clear * - eq311 preserve_4
  first | subsumption eq311 preserve_4 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X2 X4 ∨ old X2 X4 X0)) (prev_2 : (∀ X0 X1 X2 X3 X4 X5, ¬ new X0 X0 X1 ∨ ¬ new X1 X2 X3 ∨ ¬ new X4 X2 X3 ∨ ¬ new X5 X5 X4 ∨ X0 = X5)) (old_5 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X2 X2 X3 ∨ ¬ old X3 X3 X4 ∨ ¬ old X4 X3 X1 ∨ old X3 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X0 X1 ∨ ¬ new X2 X2 X3 ∨ ¬ new X3 X3 X4 ∨ ¬ new X4 X3 X1 ∨ new X3 X2 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq101 (X0 : G) : ¬(new sk0 sk0 X0) ∨ sk1 = X0 := by
    clear * - prev_0 preserve_0
    first | exact resolve prev_0 preserve_0 | exact resolve preserve_0 prev_0 | grind only
  have eq133 (X0 X1 X2 X3 : G) : ¬(new sk4 X1 X2) ∨ ¬(new X0 X1 X2) ∨ ¬(new X3 X3 X0) ∨ sk3 = X3 := by
    clear * - prev_2 preserve_2
    first | exact resolve prev_2 preserve_2 | exact resolve preserve_2 prev_2 | grind only
  have eq146 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq147 : (sP0 sk2 sk2 sk3) ∨ (old sk2 sk2 sk3) ∨ (sP1 sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq148 : (sP0 sk3 sk3 sk4) ∨ (old sk3 sk3 sk4) ∨ (sP1 sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) := by
    clear * - new_imp preserve_2
    first | exact resolve new_imp preserve_2 | exact resolve preserve_2 new_imp | grind only
  have eq149 : (sP0 sk4 sk3 sk1) ∨ (old sk4 sk3 sk1) ∨ (sP1 sk4 sk3 sk1) ∨ (sP2 sk4 sk3 sk1) := by
    clear * - new_imp preserve_3
    first | exact resolve new_imp preserve_3 | exact resolve preserve_3 new_imp | grind only
  have eq171 (X0 X1 : G) : ¬(new X1 X1 X0) ∨ ¬(new X0 sk3 sk1) ∨ sk3 = X1 := by
    clear * - eq133 preserve_3
    first | exact resolve eq133 preserve_3 | exact resolve preserve_3 eq133 | grind only
  have eq172 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq146 rule_def_0_2
    first | exact resolve eq146 rule_def_0_2 | exact resolve rule_def_0_2 eq146 | grind only
  have eq173 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq146 rule_def_0_1
    first | exact resolve eq146 rule_def_0_1 | exact resolve rule_def_0_1 eq146 | grind only
  have eq174 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 := by
    clear * - eq146 rule_def_0_0
    first | exact resolve eq146 rule_def_0_0 | exact resolve rule_def_0_0 eq146 | grind only
  have eq175 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq173 rule_def_1_0
    first | exact resolve eq173 rule_def_1_0 | exact resolve rule_def_1_0 eq173 | grind only
  have eq176 : (old sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq175 rule_def_2_1
    first | exact resolve eq175 rule_def_2_1 | exact resolve rule_def_2_1 eq175 | grind only
  have eq184 : (sP1 sk2 sk2 sk3) ∨ (old sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) ∨ c = sk3 := by
    clear * - eq147 rule_def_0_2
    first | exact resolve eq147 rule_def_0_2 | exact resolve rule_def_0_2 eq147 | grind only
  have eq185 : (old sk2 sk2 sk3) ∨ (sP1 sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) ∨ b = sk2 := by
    clear * - eq147 rule_def_0_1
    first | exact resolve eq147 rule_def_0_1 | exact resolve rule_def_0_1 eq147 | grind only
  have eq186 : (sP1 sk2 sk2 sk3) ∨ (old sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) ∨ a = sk2 := by
    clear * - eq147 rule_def_0_0
    first | exact resolve eq147 rule_def_0_0 | exact resolve rule_def_0_0 eq147 | grind only
  have eq187 : (old sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) ∨ b = sk2 := by
    clear * - eq185 rule_def_1_0
    first | exact resolve eq185 rule_def_1_0 | exact resolve rule_def_1_0 eq185 | grind only
  have eq188 : (old sk2 sk2 sk3) ∨ b = sk2 := by
    clear * - eq187 rule_def_2_1
    first | exact resolve eq187 rule_def_2_1 | exact resolve rule_def_2_1 eq187 | grind only
  have eq196 : (sP1 sk3 sk3 sk4) ∨ (old sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) ∨ c = sk4 := by
    clear * - eq148 rule_def_0_2
    first | exact resolve eq148 rule_def_0_2 | exact resolve rule_def_0_2 eq148 | grind only
  have eq197 : (old sk3 sk3 sk4) ∨ (sP1 sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) ∨ b = sk3 := by
    clear * - eq148 rule_def_0_1
    first | exact resolve eq148 rule_def_0_1 | exact resolve rule_def_0_1 eq148 | grind only
  have eq198 : (sP1 sk3 sk3 sk4) ∨ (old sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) ∨ a = sk3 := by
    clear * - eq148 rule_def_0_0
    first | exact resolve eq148 rule_def_0_0 | exact resolve rule_def_0_0 eq148 | grind only
  have eq199 : (old sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) ∨ b = sk3 := by
    clear * - eq197 rule_def_1_0
    first | exact resolve eq197 rule_def_1_0 | exact resolve rule_def_1_0 eq197 | grind only
  have eq200 : (old sk3 sk3 sk4) ∨ b = sk3 := by
    clear * - eq199 rule_def_2_1
    first | exact resolve eq199 rule_def_2_1 | exact resolve rule_def_2_1 eq199 | grind only
  have eq208 : (sP1 sk4 sk3 sk1) ∨ (old sk4 sk3 sk1) ∨ (sP2 sk4 sk3 sk1) ∨ c = sk1 := by
    clear * - eq149 rule_def_0_2
    first | exact resolve eq149 rule_def_0_2 | exact resolve rule_def_0_2 eq149 | grind only
  have eq209 : (old sk4 sk3 sk1) ∨ (sP1 sk4 sk3 sk1) ∨ (sP2 sk4 sk3 sk1) ∨ b = sk3 := by
    clear * - eq149 rule_def_0_1
    first | exact resolve eq149 rule_def_0_1 | exact resolve rule_def_0_1 eq149 | grind only
  have eq210 : (sP1 sk4 sk3 sk1) ∨ (old sk4 sk3 sk1) ∨ (sP2 sk4 sk3 sk1) ∨ a = sk4 := by
    clear * - eq149 rule_def_0_0
    first | exact resolve eq149 rule_def_0_0 | exact resolve rule_def_0_0 eq149 | grind only
  have eq211 : (sP1 sk4 sk3 sk1) ∨ (old sk4 sk3 sk1) ∨ b = sk3 := by
    clear * - eq209 rule_def_2_1
    first | exact resolve eq209 rule_def_2_1 | exact resolve rule_def_2_1 eq209 | grind only
  have eq292 : ¬(new sk3 sk3 sk1) ∨ sk2 = sk3 := by
    clear * - eq171 preserve_1
    first | exact resolve eq171 preserve_1 | exact resolve preserve_1 eq171 | grind only
  have eq298 : (old sk4 sk3 sk1) ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq211 rule_def_1_1
    first | exact resolve eq211 rule_def_1_1 | exact resolve rule_def_1_1 eq211 | grind only
  have eq300 (X0 X1 : G) : b = sk3 ∨ c = sk3 ∨ ¬(old X0 X0 sk3) ∨ ¬(old sk3 sk3 sk4) ∨ ¬(old X1 X1 sk1) ∨ (old sk3 X0 X1) := by
    clear * - eq298 old_5
    first | exact resolve eq298 old_5 | exact resolve old_5 eq298 | grind only
  have eq301 (X0 X1 : G) : ¬(old X1 X1 X0) ∨ c = sk3 ∨ ¬(old X0 sk3 sk4) ∨ b = sk3 ∨ (old sk3 sk1 X1) := by
    clear * - eq298 old_1
    first | exact resolve eq298 old_1 | exact resolve old_1 eq298 | grind only
  have eq304 (X0 X1 : G) : ¬(old X1 X1 sk1) ∨ c = sk3 ∨ ¬(old X0 X0 sk3) ∨ b = sk3 ∨ (old sk3 X0 X1) := by
    clear * - eq300 eq200
    first | exact resolve eq300 eq200 | exact resolve eq200 eq300 | grind only
  have eq341 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq172 rule_def_1_1
    first | exact resolve eq172 rule_def_1_1 | exact resolve rule_def_1_1 eq172 | grind only
  have eq343 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq341 rule_def_2_0
    first | exact resolve eq341 rule_def_2_0 | exact resolve rule_def_2_0 eq341 | grind only
  have eq346 : (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq174 rule_def_1_1
    first | exact resolve eq174 rule_def_1_1 | exact resolve rule_def_1_1 eq174 | grind only
  have eq348 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq346 rule_def_2_0
    first | exact resolve eq346 rule_def_2_0 | exact resolve rule_def_2_0 eq346 | grind only
  have eq361 : (old sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq184 rule_def_1_1
    first | exact resolve eq184 rule_def_1_1 | exact resolve rule_def_1_1 eq184 | grind only
  have eq363 : (old sk2 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq361 rule_def_2_0
    first | exact resolve eq361 rule_def_2_0 | exact resolve rule_def_2_0 eq361 | grind only
  have eq376 : (old sk2 sk2 sk3) ∨ (sP2 sk2 sk2 sk3) ∨ a = sk2 ∨ c = sk2 := by
    clear * - eq186 rule_def_1_1
    first | exact resolve eq186 rule_def_1_1 | exact resolve rule_def_1_1 eq186 | grind only
  have eq378 : (old sk2 sk2 sk3) ∨ a = sk2 ∨ c = sk2 := by
    clear * - eq376 rule_def_2_0
    first | exact resolve eq376 rule_def_2_0 | exact resolve rule_def_2_0 eq376 | grind only
  have eq390 : (old sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) ∨ c = sk4 ∨ c = sk3 := by
    clear * - eq196 rule_def_1_1
    first | exact resolve eq196 rule_def_1_1 | exact resolve rule_def_1_1 eq196 | grind only
  have eq392 : (old sk3 sk3 sk4) ∨ c = sk4 ∨ c = sk3 := by
    clear * - eq390 rule_def_2_0
    first | exact resolve eq390 rule_def_2_0 | exact resolve rule_def_2_0 eq390 | grind only
  have eq404 : (old sk3 sk3 sk4) ∨ (sP2 sk3 sk3 sk4) ∨ a = sk3 ∨ c = sk3 := by
    clear * - eq198 rule_def_1_1
    first | exact resolve eq198 rule_def_1_1 | exact resolve rule_def_1_1 eq198 | grind only
  have eq406 : (old sk3 sk3 sk4) ∨ a = sk3 ∨ c = sk3 := by
    clear * - eq404 rule_def_2_0
    first | exact resolve eq404 rule_def_2_0 | exact resolve rule_def_2_0 eq404 | grind only
  have eq418 : (sP2 sk4 sk3 sk1) ∨ (old sk4 sk3 sk1) ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq208 rule_def_1_1
    first | exact resolve eq208 rule_def_1_1 | exact resolve rule_def_1_1 eq208 | grind only
  have eq431 : (sP2 sk4 sk3 sk1) ∨ (old sk4 sk3 sk1) ∨ a = sk4 ∨ c = sk3 := by
    clear * - eq210 rule_def_1_1
    first | exact resolve eq210 rule_def_1_1 | exact resolve rule_def_1_1 eq210 | grind only
  have eq537 : (old sk4 sk3 sk1) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq418 rule_def_2_0
    first | exact resolve eq418 rule_def_2_0 | exact resolve rule_def_2_0 eq418 | grind only
  have eq550 (X0 X1 : G) : c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ ¬(old X0 X0 sk3) ∨ ¬(old sk3 sk3 sk4) ∨ ¬(old X1 X1 sk1) ∨ (old sk3 X0 X1) := by
    clear * - eq537 old_5
    first | exact resolve eq537 old_5 | exact resolve old_5 eq537 | grind only
  have eq555 (X0 X1 : G) : ¬(old X1 X1 sk1) ∨ c = sk3 ∨ c = sk4 ∨ ¬(old X0 X0 sk3) ∨ c = sk1 ∨ (old sk3 X0 X1) := by
    clear * - eq550 eq392
    first | exact resolve eq550 eq392 | exact resolve eq392 eq550 | grind only
  have eq2064 : c = sk3 ∨ ¬(old sk3 sk3 sk4) ∨ b = sk3 ∨ (old sk3 sk1 sk2) ∨ b = sk2 := by
    clear * - eq301 eq188
    first | exact resolve eq301 eq188 | exact resolve eq188 eq301 | grind only
  have eq2081 : (old sk3 sk1 sk2) ∨ b = sk3 ∨ c = sk3 ∨ b = sk2 := by
    clear * - eq2064 eq200
    first | exact resolve eq2064 eq200 | exact resolve eq200 eq2064 | grind only
  have eq2108 (X0 : G) : ¬(old X0 X0 sk3) ∨ c = sk3 ∨ b = sk3 ∨ (old sk3 X0 sk0) ∨ b = sk0 := by
    clear * - eq304 eq176
    first | exact resolve eq304 eq176 | exact resolve eq176 eq304 | grind only
  have eq3049 : (old sk3 sk2 sk0) ∨ b = sk3 ∨ c = sk3 ∨ b = sk0 ∨ b = sk2 := by
    clear * - eq2108 eq188
    first | exact resolve eq2108 eq188 | exact resolve eq188 eq2108 | grind only
  have eq3062 : b = sk3 ∨ c = sk3 ∨ b = sk0 ∨ b = sk2 ∨ (new sk3 sk2 sk0) := by
    clear * - eq3049 imp_new_0
    first | exact resolve eq3049 imp_new_0 | exact resolve imp_new_0 eq3049 | grind only
  have eq3064 : b = sk2 ∨ c = sk3 ∨ b = sk0 ∨ b = sk3 := by
    clear * - eq3062 preserve_4
    first | exact resolve eq3062 preserve_4 | exact resolve preserve_4 eq3062 | grind only
  have eq3073 : ¬(new sk3 b sk0) ∨ c = sk3 ∨ b = sk0 ∨ b = sk3 := by
    clear * - preserve_4 eq3064
    first | exact (eq3064.imp_left (fun h : b = sk2 => superpose h preserve_4)) | exact superpose preserve_4 eq3064 | exact superpose eq3064 preserve_4 | grind only
  have eq3090 : (old b b sk3) ∨ c = sk3 ∨ c = b ∨ c = sk3 ∨ b = sk0 ∨ b = sk3 := by
    clear * - eq363 eq3064
    first | exact Or.assoc3 (eq3064.imp_left (fun h : b = sk2 => superpose h eq363)) | exact superpose eq363 eq3064 | exact superpose eq3064 eq363 | grind only
  have eq3165 : (old b b sk3) ∨ c = sk3 ∨ c = b ∨ b = sk0 ∨ b = sk3 := by
    clear * - eq3090
    first | exact resolve eq3090 rfl | grind only
  have eq3193 : (old b b sk3) ∨ c = sk3 ∨ b = sk0 ∨ b = sk3 := by
    clear * - eq3165 bc
    first | exact resolve eq3165 bc | exact resolve bc eq3165 | grind only
  have eq3281 : c = sk3 ∨ b = sk0 ∨ b = sk3 ∨ c = sk3 ∨ b = sk3 ∨ (old sk3 b sk0) ∨ b = sk0 := by
    clear * - eq3193 eq2108
    first | exact resolve eq3193 eq2108 | exact resolve eq2108 eq3193 | grind only
  have eq3318 : (old sk3 b sk0) ∨ b = sk0 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq3281
    first | exact resolve eq3281 rfl | grind only
  have eq3330 : b = sk0 ∨ b = sk3 ∨ c = sk3 ∨ (new sk3 b sk0) := by
    clear * - eq3318 imp_new_0
    first | exact resolve eq3318 imp_new_0 | exact resolve imp_new_0 eq3318 | grind only
  have eq3331 : b = sk0 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq3330 eq3073
    first | exact resolve eq3330 eq3073 | exact resolve eq3073 eq3330 | grind only
  have eq3338 : ¬(new sk3 sk2 b) ∨ b = sk3 ∨ c = sk3 := by
    clear * - preserve_4 eq3331
    first | exact (eq3331.imp_left (fun h : b = sk0 => superpose h preserve_4)) | exact superpose preserve_4 eq3331 | exact superpose eq3331 preserve_4 | grind only
  have eq3339 (X0 : G) : ¬(new b b X0) ∨ sk1 = X0 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq101 eq3331
    first | exact Or.assoc2 (eq3331.imp_left (fun h : b = sk0 => superpose h eq101)) | exact superpose eq101 eq3331 | exact superpose eq3331 eq101 | grind only
  have eq3349 : (old b b sk1) ∨ c = sk1 ∨ c = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq343 eq3331
    first | exact Or.assoc3 (eq3331.imp_left (fun h : b = sk0 => superpose h eq343)) | exact superpose eq343 eq3331 | exact superpose eq3331 eq343 | grind only
  have eq3350 : (old b b sk1) ∨ a = b ∨ c = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq348 eq3331
    first | exact Or.assoc3 (eq3331.imp_left (fun h : b = sk0 => superpose h eq348)) | exact superpose eq348 eq3331 | exact superpose eq3331 eq348 | grind only
  have eq3363 : (old b b sk1) ∨ a = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq3350 bc
    first | exact resolve eq3350 bc | exact resolve bc eq3350 | grind only
  have eq3364 : (old b b sk1) ∨ c = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq3349 bc
    first | exact resolve eq3349 bc | exact resolve bc eq3349 | grind only
  have eq3433 (X0 : G) : a = b ∨ b = sk3 ∨ c = sk3 ∨ c = sk3 ∨ ¬(old X0 X0 sk3) ∨ b = sk3 ∨ (old sk3 X0 b) := by
    clear * - eq3363 eq304
    first | exact resolve eq3363 eq304 | exact resolve eq304 eq3363 | grind only
  have eq3468 (X0 : G) : ¬(old X0 X0 sk3) ∨ b = sk3 ∨ c = sk3 ∨ a = b ∨ (old sk3 X0 b) := by
    clear * - eq3433
    first | exact resolve eq3433 rfl | grind only
  have eq3482 (X0 : G) : c = sk1 ∨ b = sk3 ∨ c = sk3 ∨ c = sk3 ∨ ¬(old X0 X0 sk3) ∨ b = sk3 ∨ (old sk3 X0 b) := by
    clear * - eq3364 eq304
    first | exact resolve eq3364 eq304 | exact resolve eq304 eq3364 | grind only
  have eq3519 (X0 : G) : ¬(old X0 X0 sk3) ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ (old sk3 X0 b) := by
    clear * - eq3482
    first | exact resolve eq3482 rfl | grind only
  have eq6428 : (old sk3 sk2 b) ∨ c = sk3 ∨ a = b ∨ b = sk3 ∨ b = sk2 := by
    clear * - eq3468 eq188
    first | exact resolve eq3468 eq188 | exact resolve eq188 eq3468 | grind only
  have eq6440 : c = sk3 ∨ a = b ∨ b = sk3 ∨ b = sk2 ∨ (new sk3 sk2 b) := by
    clear * - eq6428 imp_new_0
    first | exact resolve eq6428 imp_new_0 | exact resolve imp_new_0 eq6428 | grind only
  have eq6443 : b = sk2 ∨ a = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq6440 eq3338
    first | exact resolve eq6440 eq3338 | exact resolve eq3338 eq6440 | grind only
  have eq6465 : (old b b sk3) ∨ a = b ∨ c = b ∨ a = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq378 eq6443
    first | exact Or.assoc3 (eq6443.imp_left (fun h : b = sk2 => superpose h eq378)) | exact superpose eq378 eq6443 | exact superpose eq6443 eq378 | grind only
  have eq6547 : ¬(new sk3 b b) ∨ b = sk3 ∨ c = sk3 ∨ a = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq3338 eq6443
    first | exact Or.assoc3 (eq6443.imp_left (fun h : b = sk2 => superpose h eq3338)) | exact superpose eq3338 eq6443 | exact superpose eq6443 eq3338 | grind only
  have eq6553 : ¬(new sk3 b b) ∨ b = sk3 ∨ c = sk3 ∨ a = b := by
    clear * - eq6547
    first | exact resolve eq6547 rfl | grind only
  have eq6600 : (old b b sk3) ∨ a = b ∨ c = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq6465
    first | exact resolve eq6465 rfl | grind only
  have eq6642 : (old b b sk3) ∨ a = b ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq6600 bc
    first | exact resolve eq6600 bc | exact resolve bc eq6600 | grind only
  have eq7509 : a = b ∨ b = sk3 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ a = b ∨ (old sk3 b b) := by
    clear * - eq6642 eq3468
    first | exact resolve eq6642 eq3468 | exact resolve eq3468 eq6642 | grind only
  have eq7544 : (old sk3 b b) ∨ b = sk3 ∨ c = sk3 ∨ a = b := by
    clear * - eq7509
    first | exact resolve eq7509 rfl | grind only
  have eq7577 : b = sk3 ∨ c = sk3 ∨ a = b ∨ (new sk3 b b) := by
    clear * - eq7544 imp_new_0
    first | exact resolve eq7544 imp_new_0 | exact resolve imp_new_0 eq7544 | grind only
  have eq7583 : c = sk3 ∨ b = sk3 ∨ a = b := by
    clear * - eq7577 eq6553
    first | exact resolve eq7577 eq6553 | exact resolve eq6553 eq7577 | grind only
  have eq7616 : (old c c sk4) ∨ c = b ∨ b = sk3 ∨ a = b := by
    clear * - eq200 eq7583
    first | exact Or.assoc2 (eq7583.imp_left (fun h : c = sk3 => superpose h eq200)) | exact superpose eq200 eq7583 | exact superpose eq7583 eq200 | grind only
  have eq7861 : c = b ∨ b = sk3 ∨ a = b := by
    clear * - eq7616 p4XZ
    first | exact resolve eq7616 p4XZ | exact resolve p4XZ eq7616 | grind only
  have eq7899 : b = sk3 ∨ a = b := by
    clear * - eq7861 bc
    first | exact resolve eq7861 bc | exact resolve bc eq7861 | grind only
  have eq7955 : ¬(new b b sk1) ∨ b = sk2 ∨ a = b := by
    clear * - eq292 eq7899
    first | exact Or.assoc2 (eq7899.imp_left (fun h : b = sk3 => superpose h eq292)) | exact superpose eq292 eq7899 | exact superpose eq7899 eq292 | grind only
  have eq7977 : (old b b sk4) ∨ a = b ∨ c = b ∨ a = b := by
    clear * - eq406 eq7899
    first | exact Or.assoc3 (eq7899.imp_left (fun h : b = sk3 => superpose h eq406)) | exact superpose eq406 eq7899 | exact superpose eq7899 eq406 | grind only
  have eq8113 : (old b b sk4) ∨ a = b ∨ c = b := by
    clear * - eq7977
    first | exact resolve eq7977 rfl | grind only
  have eq8166 : (old b b sk4) ∨ a = b := by
    clear * - eq8113 bc
    first | exact resolve eq8113 bc | exact resolve bc eq8113 | grind only
  have eq18468 (X0 : G) : ¬(old X0 X0 sk3) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ (old sk3 X0 sk0) ∨ b = sk0 := by
    clear * - eq555 eq176
    first | exact resolve eq555 eq176 | exact resolve eq176 eq555 | grind only
  have eq21857 : (old sk3 sk2 b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ b = sk2 := by
    clear * - eq3519 eq188
    first | exact resolve eq3519 eq188 | exact resolve eq188 eq3519 | grind only
  have eq21973 : c = sk3 ∨ c = sk1 ∨ b = sk3 ∨ b = sk2 ∨ (new sk3 sk2 b) := by
    clear * - eq21857 imp_new_0
    first | exact resolve eq21857 imp_new_0 | exact resolve imp_new_0 eq21857 | grind only
  have eq21982 : c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ b = sk2 := by
    clear * - eq21973 eq3338
    first | exact resolve eq21973 eq3338 | exact resolve eq3338 eq21973 | grind only
  have eq22139 : (old sk3 c sk2) ∨ b = sk3 ∨ c = sk3 ∨ b = sk2 ∨ c = sk3 ∨ b = sk3 ∨ b = sk2 := by
    clear * - eq2081 eq21982
    first | exact Or.assoc4 (eq21982.imp_left (fun h : c = sk1 => superpose h eq2081)) | exact superpose eq2081 eq21982 | exact superpose eq21982 eq2081 | grind only
  have eq22442 : (old sk3 c sk2) ∨ b = sk3 ∨ c = sk3 ∨ b = sk2 := by
    clear * - eq22139
    first | exact resolve eq22139 rfl | grind only
  have eq22536 : b = sk2 ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq22442 p4XZ
    first | exact resolve eq22442 p4XZ | exact resolve p4XZ eq22442 | grind only
  have eq22642 : (new b b sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - preserve_1 eq22536
    first | exact (eq22536.imp_left (fun h : b = sk2 => superpose h preserve_1)) | exact superpose preserve_1 eq22536 | exact superpose eq22536 preserve_1 | grind only
  have eq22660 : (old b b sk3) ∨ c = sk3 ∨ c = b ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq363 eq22536
    first | exact Or.assoc3 (eq22536.imp_left (fun h : b = sk2 => superpose h eq363)) | exact superpose eq363 eq22536 | exact superpose eq22536 eq363 | grind only
  have eq22763 : ¬(new sk3 b b) ∨ b = sk3 ∨ c = sk3 ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq3338 eq22536
    first | exact Or.assoc3 (eq22536.imp_left (fun h : b = sk2 => superpose h eq3338)) | exact superpose eq3338 eq22536 | exact superpose eq22536 eq3338 | grind only
  have eq22862 : ¬(new sk3 b b) ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq22763
    first | exact resolve eq22763 rfl | grind only
  have eq22908 : (old b b sk3) ∨ c = sk3 ∨ c = b ∨ b = sk3 := by
    clear * - eq22660
    first | exact resolve eq22660 rfl | grind only
  have eq22953 : (old b b sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq22908 bc
    first | exact resolve eq22908 bc | exact resolve bc eq22908 | grind only
  have eq22973 : c = sk3 ∨ b = sk3 ∨ sk1 = sk3 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq22642 eq3339
    first | exact resolve eq22642 eq3339 | exact resolve eq3339 eq22642 | grind only
  have eq23077 : sk1 = sk3 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq22973
    first | exact resolve eq22973 rfl | grind only
  have eq24398 : c = sk3 ∨ b = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ (old sk3 b b) := by
    clear * - eq22953 eq3519
    first | exact resolve eq22953 eq3519 | exact resolve eq3519 eq22953 | grind only
  have eq24460 : (old sk3 b b) ∨ b = sk3 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq24398
    first | exact resolve eq24398 rfl | grind only
  have eq30698 : b = sk3 ∨ c = sk1 ∨ c = sk3 ∨ (new sk3 b b) := by
    clear * - eq24460 imp_new_0
    first | exact resolve eq24460 imp_new_0 | exact resolve imp_new_0 eq24460 | grind only
  have eq30710 : c = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq30698 eq22862
    first | exact resolve eq30698 eq22862 | exact resolve eq22862 eq30698 | grind only
  have eq31080 : c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq23077 eq30710
    first | exact Or.assoc3 (eq30710.imp_left (fun h : c = sk1 => superpose h eq23077)) | exact superpose eq23077 eq30710 | exact superpose eq30710 eq23077 | grind only
  have eq31107 : c = sk3 ∨ b = sk3 := by
    clear * - eq31080
    first | exact resolve eq31080 rfl | grind only
  have eq31403 : (old c c sk4) ∨ c = b ∨ b = sk3 := by
    clear * - eq200 eq31107
    first | exact Or.assoc2 (eq31107.imp_left (fun h : c = sk3 => superpose h eq200)) | exact superpose eq200 eq31107 | exact superpose eq31107 eq200 | grind only
  have eq31780 : c = b ∨ b = sk3 := by
    clear * - eq31403 p4XZ
    first | exact resolve eq31403 p4XZ | exact resolve p4XZ eq31403 | grind only
  have eq31835 : b = sk3 := by
    clear * - eq31780 bc
    first | exact resolve eq31780 bc | exact resolve bc eq31780 | grind only
  have eq31939 : (new sk2 sk2 b) := by
    clear * - preserve_1 eq31835
    first | exact superpose preserve_1 eq31835 | exact superpose eq31835 preserve_1 | grind only
  have eq31942 : ¬(new b sk2 sk0) := by
    clear * - preserve_4 eq31835
    first | exact superpose preserve_4 eq31835 | exact superpose eq31835 preserve_4 | grind only
  have eq31963 : (old sk2 sk2 b) ∨ b = sk2 := by
    clear * - eq188 eq31835
    first | exact superpose eq188 eq31835 | exact superpose eq31835 eq188 | grind only
  have eq32004 : (old b b sk4) ∨ c = sk4 ∨ c = b := by
    clear * - eq392 eq31835
    first | exact superpose eq392 eq31835 | exact superpose eq31835 eq392 | grind only
  have eq32015 : (sP2 sk4 b sk1) ∨ (old sk4 b sk1) ∨ a = sk4 ∨ c = b := by
    clear * - eq431 eq31835
    first | exact superpose eq431 eq31835 | exact superpose eq31835 eq431 | grind only
  have eq32304 : (sP2 sk4 b sk1) ∨ (old sk4 b sk1) ∨ a = sk4 := by
    clear * - eq32015 bc
    first | exact resolve eq32015 bc | exact resolve bc eq32015 | grind only
  have eq32308 : (old b b sk4) ∨ c = sk4 := by
    clear * - eq32004 bc
    first | exact resolve eq32004 bc | exact resolve bc eq32004 | grind only
  have eq65076 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ (old sk3 sk2 sk0) ∨ b = sk0 ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq18468 eq363
    first | exact resolve eq18468 eq363 | exact resolve eq363 eq18468 | grind only
  have eq65088 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ (old sk3 sk2 sk0) ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq65076
    first | exact resolve eq65076 rfl | grind only
  have eq65103 : c = b ∨ c = sk4 ∨ c = sk1 ∨ (old sk3 sk2 sk0) ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq65088 eq31835
    first | simpa only [eq31835, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq65088 | grind only
  have eq65111 : c = sk4 ∨ c = sk1 ∨ (old sk3 sk2 sk0) ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq65103 bc
    first | exact resolve eq65103 bc | exact resolve bc eq65103 | grind only
  have eq65119 : (old b sk2 sk0) ∨ c = sk4 ∨ c = sk1 ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq65111 eq31835
    first | simpa only [eq31835, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq65111 | grind only
  have eq65780 : c = sk4 ∨ c = sk1 ∨ b = sk0 ∨ c = sk2 ∨ (new b sk2 sk0) := by
    clear * - eq65119 imp_new_0
    first | exact resolve eq65119 imp_new_0 | exact resolve imp_new_0 eq65119 | grind only
  have eq65791 : c = sk4 ∨ c = sk1 ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq65780 eq31942
    first | exact resolve eq65780 eq31942 | exact resolve eq31942 eq65780 | grind only
  have eq66081 : (old b b c) ∨ a = b ∨ c = sk1 ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq8166 eq65791
    first | exact Or.assoc2 (eq65791.imp_left (fun h : c = sk4 => superpose h eq8166)) | exact superpose eq8166 eq65791 | exact superpose eq65791 eq8166 | grind only
  have eq66410 : c = sk1 ∨ a = b ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq66081 p4XY
    first | exact resolve eq66081 p4XY | exact resolve p4XY eq66081 | grind only
  have eq66805 : (old sk0 sk0 c) ∨ b = sk0 ∨ a = b ∨ b = sk0 ∨ c = sk2 := by
    clear * - eq176 eq66410
    first | exact Or.assoc2 (eq66410.imp_left (fun h : c = sk1 => superpose h eq176)) | exact superpose eq176 eq66410 | exact superpose eq66410 eq176 | grind only
  have eq67520 : (old sk0 sk0 c) ∨ b = sk0 ∨ a = b ∨ c = sk2 := by
    clear * - eq66805
    first | exact resolve eq66805 rfl | grind only
  have eq67684 : c = sk2 ∨ a = b ∨ b = sk0 := by
    clear * - eq67520 p4XY
    first | exact resolve eq67520 p4XY | exact resolve p4XY eq67520 | grind only
  have eq68128 : (old c c b) ∨ c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq31963 eq67684
    first | exact Or.assoc2 (eq67684.imp_left (fun h : c = sk2 => superpose h eq31963)) | exact superpose eq31963 eq67684 | exact superpose eq67684 eq31963 | grind only
  have eq68274 : c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq68128 p4XZ
    first | exact resolve eq68128 p4XZ | exact resolve p4XZ eq68128 | grind only
  have eq68418 : b = sk0 ∨ a = b := by
    clear * - eq68274 bc
    first | exact resolve eq68274 bc | exact resolve bc eq68274 | grind only
  have eq68654 : (new b b sk1) ∨ a = b := by
    clear * - preserve_0 eq68418
    first | exact (eq68418.imp_left (fun h : b = sk0 => superpose h preserve_0)) | exact superpose preserve_0 eq68418 | exact superpose eq68418 preserve_0 | grind only
  have eq68851 : ¬(new b sk2 b) ∨ a = b := by
    clear * - eq31942 eq68418
    first | exact (eq68418.imp_left (fun h : b = sk0 => superpose h eq31942)) | exact superpose eq31942 eq68418 | exact superpose eq68418 eq31942 | grind only
  have eq69095 : a = b ∨ b = sk2 ∨ a = b := by
    clear * - eq68654 eq7955
    first | exact resolve eq68654 eq7955 | exact resolve eq7955 eq68654 | grind only
  have eq69252 : b = sk2 ∨ a = b := by
    clear * - eq69095
    first | exact resolve eq69095 rfl | grind only
  have eq70988 : (new b b b) ∨ a = b := by
    clear * - eq31939 eq69252
    first | exact (eq69252.imp_left (fun h : b = sk2 => superpose h eq31939)) | exact superpose eq31939 eq69252 | exact superpose eq69252 eq31939 | grind only
  have eq71635 : ¬(new b b b) ∨ a = b ∨ a = b := by
    clear * - eq68851 eq69252
    first | exact Or.assoc2 (eq69252.imp_left (fun h : b = sk2 => superpose h eq68851)) | exact superpose eq68851 eq69252 | exact superpose eq69252 eq68851 | grind only
  have eq71636 : ¬(new b b b) ∨ a = b := by
    clear * - eq71635
    first | exact resolve eq71635 rfl | grind only
  have eq71643 : a = b := by
    clear * - eq71636 eq70988
    first | exact resolve eq71636 eq70988 | exact resolve eq70988 eq71636 | grind only
  have eq71666 (X0 : G) : ¬(old b b X0) := by
    clear * - p3 eq71643
    first | exact superpose p3 eq71643 | exact superpose eq71643 p3 | grind only
  have eq71888 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := by
    clear * - eq71666 rule_def_2_2
    first | exact resolve eq71666 rule_def_2_2 | exact resolve rule_def_2_2 eq71666 | grind only
  have eq71895 : c = sk4 := by
    clear * - eq71666 eq32308
    first | exact resolve eq71666 eq32308 | exact resolve eq32308 eq71666 | grind only
  have eq72337 : (sP2 c b sk1) ∨ (old c b sk1) ∨ a = c := by
    clear * - eq32304 eq71895
    first | exact superpose eq32304 eq71895 | exact superpose eq71895 eq32304 | grind only
  have eq72376 : (old c b sk1) ∨ a = c := by
    clear * - eq72337 eq71888
    first | exact resolve eq72337 eq71888 | exact resolve eq71888 eq72337 | grind only
  have eq72534 : a = c := by
    clear * - eq72376 p4YZ
    first | exact resolve eq72376 p4YZ | exact resolve p4YZ eq72376 | grind only
  clear * - eq72534 ac
  first | subsumption eq72534 ac | grind only


set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq127 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq133 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq127 rule_def_0_1
    first | exact resolve eq127 rule_def_0_1 | exact resolve rule_def_0_1 eq127 | grind only
  have eq134 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq127 rule_def_0_0
    first | exact resolve eq127 rule_def_0_0 | exact resolve rule_def_0_0 eq127 | grind only
  have eq135 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - eq134 preserve_1
    first | exact resolve eq134 preserve_1 | exact resolve preserve_1 eq134 | grind only
  have eq136 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq133 rule_def_2_1
    first | exact resolve eq133 rule_def_2_1 | exact resolve rule_def_2_1 eq133 | grind only
  have eq144 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq136 rule_def_1_0
    first | exact resolve eq136 rule_def_1_0 | exact resolve rule_def_1_0 eq136 | grind only
  have eq145 : (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq144 preserve_2
    first | exact resolve eq144 preserve_2 | exact resolve preserve_2 eq144 | grind only
  have eq153 : b = sk1 ∨ memold sk0 := by
    clear * - eq145 old_mem1
    first | exact resolve eq145 old_mem1 | exact resolve old_mem1 eq145 | grind only
  have eq156 : b = sk1 := by
    clear * - eq153 preserve_3
    first | exact resolve eq153 preserve_3 | exact resolve preserve_3 eq153 | grind only
  have eq202 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk0 := by
    clear * - eq135 rule_def_1_0
    first | exact resolve eq135 rule_def_1_0 | exact resolve rule_def_1_0 eq135 | grind only
  have eq204 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - eq202 preserve_2
    first | exact resolve eq202 preserve_2 | exact resolve preserve_2 eq202 | grind only
  have eq210 : (old sk0 b sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - eq204 eq156
    first | simpa only [eq156, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq204 | grind only
  have eq216 : (sP2 sk0 b sk2) ∨ (old sk0 b sk2) := by
    clear * - eq210 eq156
    first | simpa only [eq156, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq210 | grind only
  have eq252 : (old sk0 b sk2) ∨ c = sk0 := by
    clear * - eq216 rule_def_2_0
    first | exact resolve eq216 rule_def_2_0 | exact resolve rule_def_2_0 eq216 | grind only
  have eq261 : (old sk0 b sk2) := by
    clear * - eq252 preserve_4
    first | exact resolve eq252 preserve_4 | exact resolve preserve_4 eq252 | grind only
  have eq268 : memold sk0 := by
    clear * - eq261 old_mem1
    first | exact resolve eq261 old_mem1 | exact resolve old_mem1 eq261 | grind only
  clear * - eq268 preserve_3
  first | subsumption eq268 preserve_3 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq127 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq133 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq127 rule_def_0_1
    first | exact resolve eq127 rule_def_0_1 | exact resolve rule_def_0_1 eq127 | grind only
  have eq135 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq133 rule_def_2_1
    first | exact resolve eq133 rule_def_2_1 | exact resolve rule_def_2_1 eq133 | grind only
  have eq136 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := by
    clear * - eq135 preserve_2
    first | exact resolve eq135 preserve_2 | exact resolve preserve_2 eq135 | grind only
  have eq143 : (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq136 rule_def_1_1
    first | exact resolve eq136 rule_def_1_1 | exact resolve rule_def_1_1 eq136 | grind only
  have eq145 : (old sk0 sk1 sk2) := by
    clear * - eq143 preserve_4
    first | exact resolve eq143 preserve_4 | exact resolve preserve_4 eq143 | grind only
  have eq154 : memold sk1 := by
    clear * - eq145 old_mem2
    first | exact resolve eq145 old_mem2 | exact resolve old_mem2 eq145 | grind only
  clear * - eq154 preserve_3
  first | subsumption eq154 preserve_3 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq88 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X2 := by
    clear * - rule_def_1_2 old_mem1
    first | exact resolve rule_def_1_2 old_mem1 | exact resolve old_mem1 rule_def_1_2 | grind only
  have eq127 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq132 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq127 rule_def_0_2
    first | exact resolve eq127 rule_def_0_2 | exact resolve rule_def_0_2 eq127 | grind only
  have eq133 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq127 rule_def_0_1
    first | exact resolve eq127 rule_def_0_1 | exact resolve rule_def_0_1 eq127 | grind only
  have eq135 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq133 rule_def_2_1
    first | exact resolve eq133 rule_def_2_1 | exact resolve rule_def_2_1 eq133 | grind only
  have eq136 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := by
    clear * - eq132 preserve_4
    first | exact resolve eq132 preserve_4 | exact resolve preserve_4 eq132 | grind only
  have eq142 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ memold sk2 := by
    clear * - eq135 eq88
    first | exact resolve eq135 eq88 | exact resolve eq88 eq135 | grind only
  have eq145 : b = sk1 ∨ memold sk2 := by
    clear * - eq142 old_mem3
    first | exact resolve eq142 old_mem3 | exact resolve old_mem3 eq142 | grind only
  have eq146 : b = sk1 := by
    clear * - eq145 preserve_3
    first | exact resolve eq145 preserve_3 | exact resolve preserve_3 eq145 | grind only
  have eq187 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ memold sk2 := by
    clear * - eq136 eq88
    first | exact resolve eq136 eq88 | exact resolve eq88 eq136 | grind only
  have eq193 : (sP2 sk0 sk1 sk2) ∨ memold sk2 := by
    clear * - eq187 old_mem3
    first | exact resolve eq187 old_mem3 | exact resolve old_mem3 eq187 | grind only
  have eq199 : (sP2 sk0 sk1 sk2) := by
    clear * - eq193 preserve_3
    first | exact resolve eq193 preserve_3 | exact resolve preserve_3 eq193 | grind only
  have eq204 : (sP2 sk0 b sk2) := by
    clear * - eq199 eq146
    first | simpa only [eq146, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq199 | grind only
  have eq212 : (old sk2 sk2 b) := by
    clear * - eq204 rule_def_2_4
    first | exact resolve eq204 rule_def_2_4 | exact resolve rule_def_2_4 eq204 | grind only
  have eq249 : memold sk2 := by
    clear * - eq212 old_mem2
    first | exact resolve eq212 old_mem2 | exact resolve old_mem2 eq212 | grind only
  clear * - eq249 preserve_3
  first | subsumption eq249 preserve_3 | grind only


structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X0 X1 ∨ ¬ R X1 X2 X3 ∨ ¬ R X3 X2 X4 ∨ R X2 X4 X0)
  rule_2 : (∀ X0 X1 X2 X3 X4 X5, ¬ R X0 X0 X1 ∨ ¬ R X1 X2 X3 ∨ ¬ R X4 X2 X3 ∨ ¬ R X5 X5 X4 ∨ X0 = X5)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X2 X2 X1 ∨ X2 = X0)
  rule_4 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X3 ∨ ¬ R X3 X1 X0 ∨ ¬ R X4 X4 X1 ∨ R X2 X1 X4)
  rule_5 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X0 X1 ∨ ¬ R X2 X2 X3 ∨ ¬ R X3 X3 X4 ∨ ¬ R X4 X3 X1 ∨ R X3 X2 X0)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬R X Y Z ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬R X Y Z ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬R X Y Z ∨ Z ∈ finsupp

variable {G : Type*} (ps : PartialSolution G)

set_option linter.all false in
theorem PartialSolution.adjoin (a b c : G) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ ps.R a b X0)
    (p4XY : ∀ X1 X2, ¬ ps.R X1 X2 c) (p4XZ : ∀ X1 X2, ¬ ps.R X1 c X2) (p4YZ : ∀ X1 X2, ¬ ps.R c X1 X2)
    : ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by classical
  let sP0 (X Y Z) := a = X ∧ b = Y ∧ c = Z
  have hsP0 (X Y Z) (h : sP0 X Y Z) : a = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP0
  obtain ⟨rule_def_0_0, rule_def_0_1, rule_def_0_2⟩ := hsP0
  simp_rw [or_comm] at rule_def_0_0 rule_def_0_1 rule_def_0_2
  let sP1 (X Y Z) := ∃ sF0, b = X ∧ c = Y ∧ ps.R Z Z sF0 ∧ ps.R sF0 b a
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z) := ∃ sF1, c = X ∧ b = Y ∧ ps.R b b sF1 ∧ ps.R sF1 b a ∧ ps.R Z Z b
  choose! sF1 hsP2 using fun (X Y Z) (h : sP2 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3, rule_def_2_4⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 sP2 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_1 ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_5 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ new_new prev_0 ps.rule_1 prev_1 ps.rule_2 ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 new_imp imp_new_0
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 bc p4XY ps.rule_3 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 new_imp
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 prev_1
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 prev_2 ps.rule_5 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 rule_def_2_2 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_0 rule_def_0_1 rule_def_1_0 rule_def_2_0 rule_def_2_1 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_1 rule_def_2_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_1 rule_def_0_2 rule_def_1_2 rule_def_2_1 rule_def_2_4 new_imp ps.mem_1 ps.mem_2 ps.mem_3
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
    ¬ ps.compl X0 X0 X1 ∨ ¬ ps.compl X1 X2 X3 ∨ ¬ ps.compl X3 X2 X4 ∨ ps.compl X2 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X0) (max (Nat.pair X1 X2) (max (Nat.pair X3 X2) (max (Nat.pair X2 X4) 0)))
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

theorem PartialSolution.toMagma_equation1279 :
    letI := ps.toMagma
    Equation1279 ℕ := by
  simp only [Equation1279]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 (ps.complFun X0 X0) X1 (ps.complFun (ps.complFun X0 X0) X1) (ps.complFun (ps.complFun (ps.complFun X0 X0) X1) X1)

end Eq1279
