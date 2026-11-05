import Mathlib.Tactic.ClearExcept
import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

set_option linter.all false

set_option linter.all false

/-! A countable completion construction for E1119. Nine local invariants
make adjoining a fresh product consistent. The clausal preservation arguments
were found by Vampire and are replayed below as kernel-checked deductions.
The external prover is not invoked at build time and supplies no axiom. -/
namespace Eq1119

set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq219 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq220 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq225 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq219 rule_def_0_2
    first | exact resolve eq219 rule_def_0_2 | exact resolve rule_def_0_2 eq219 | grind only
  have eq226 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq219 rule_def_0_1
    first | exact resolve eq219 rule_def_0_1 | exact resolve rule_def_0_1 eq219 | grind only
  have eq227 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq219 rule_def_0_0
    first | exact resolve eq219 rule_def_0_0 | exact resolve rule_def_0_0 eq219 | grind only
  have eq228 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq226 rule_def_5_2
    first | exact resolve eq226 rule_def_5_2 | exact resolve rule_def_5_2 eq226 | grind only
  have eq229 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq225 rule_def_5_3
    first | exact resolve eq225 rule_def_5_3 | exact resolve rule_def_5_3 eq225 | grind only
  have eq230 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq228 rule_def_6_2
    first | exact resolve eq228 rule_def_6_2 | exact resolve rule_def_6_2 eq228 | grind only
  have eq231 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq229 rule_def_6_3
    first | exact resolve eq229 rule_def_6_3 | exact resolve rule_def_6_3 eq229 | grind only
  have eq232 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq230 rule_def_7_2
    first | exact resolve eq230 rule_def_7_2 | exact resolve rule_def_7_2 eq230 | grind only
  have eq233 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq231 rule_def_7_3
    first | exact resolve eq231 rule_def_7_3 | exact resolve rule_def_7_3 eq231 | grind only
  have eq234 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) ∨ c = sk3 := by
    clear * - eq220 rule_def_0_2
    first | exact resolve eq220 rule_def_0_2 | exact resolve rule_def_0_2 eq220 | grind only
  have eq235 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) ∨ b = sk1 := by
    clear * - eq220 rule_def_0_1
    first | exact resolve eq220 rule_def_0_1 | exact resolve rule_def_0_1 eq220 | grind only
  have eq236 : (sP11 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 := by
    clear * - eq220 rule_def_0_0
    first | exact resolve eq220 rule_def_0_0 | exact resolve rule_def_0_0 eq220 | grind only
  have eq237 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) ∨ b = sk1 := by
    clear * - eq235 rule_def_5_2
    first | exact resolve eq235 rule_def_5_2 | exact resolve rule_def_5_2 eq235 | grind only
  have eq238 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) ∨ c = sk3 := by
    clear * - eq234 rule_def_5_3
    first | exact resolve eq234 rule_def_5_3 | exact resolve rule_def_5_3 eq234 | grind only
  have eq239 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) ∨ b = sk1 := by
    clear * - eq237 rule_def_6_2
    first | exact resolve eq237 rule_def_6_2 | exact resolve rule_def_6_2 eq237 | grind only
  have eq240 : (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (sP11 sk0 sk1 sk3) ∨ c = sk3 := by
    clear * - eq238 rule_def_6_3
    first | exact resolve eq238 rule_def_6_3 | exact resolve rule_def_6_3 eq238 | grind only
  have eq241 : (sP11 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := by
    clear * - eq239 rule_def_7_2
    first | exact resolve eq239 rule_def_7_2 | exact resolve rule_def_7_2 eq239 | grind only
  have eq242 : (sP11 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 := by
    clear * - eq240 rule_def_7_3
    first | exact resolve eq240 rule_def_7_3 | exact resolve rule_def_7_3 eq240 | grind only
  have eq243 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq232 rule_def_11_3
    first | exact resolve eq232 rule_def_11_3 | exact resolve rule_def_11_3 eq232 | grind only
  have eq244 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq232 rule_def_11_2
    first | exact resolve eq232 rule_def_11_2 | exact resolve rule_def_11_2 eq232 | grind only
  have eq248 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq244 rule_def_1_0
    first | exact resolve eq244 rule_def_1_0 | exact resolve rule_def_1_0 eq244 | grind only
  have eq249 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq243 rule_def_1_1
    first | exact resolve eq243 rule_def_1_1 | exact resolve rule_def_1_1 eq243 | grind only
  have eq251 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq248 rule_def_2_1
    first | exact resolve eq248 rule_def_2_1 | exact resolve rule_def_2_1 eq248 | grind only
  have eq252 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq249 rule_def_2_2
    first | exact resolve eq249 rule_def_2_2 | exact resolve rule_def_2_2 eq249 | grind only
  have eq254 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq251 rule_def_3_1
    first | exact resolve eq251 rule_def_3_1 | exact resolve rule_def_3_1 eq251 | grind only
  have eq255 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq252 rule_def_3_2
    first | exact resolve eq252 rule_def_3_2 | exact resolve rule_def_3_2 eq252 | grind only
  have eq256 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq254 rule_def_4_1
    first | exact resolve eq254 rule_def_4_1 | exact resolve rule_def_4_1 eq254 | grind only
  have eq257 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq255 rule_def_4_2
    first | exact resolve eq255 rule_def_4_2 | exact resolve rule_def_4_2 eq255 | grind only
  have eq258 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq256 rule_def_8_2
    first | exact resolve eq256 rule_def_8_2 | exact resolve rule_def_8_2 eq256 | grind only
  have eq259 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq257 rule_def_8_3
    first | exact resolve eq257 rule_def_8_3 | exact resolve rule_def_8_3 eq257 | grind only
  have eq260 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq258 rule_def_9_2
    first | exact resolve eq258 rule_def_9_2 | exact resolve rule_def_9_2 eq258 | grind only
  have eq261 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq259 rule_def_9_3
    first | exact resolve eq259 rule_def_9_3 | exact resolve rule_def_9_3 eq259 | grind only
  have eq262 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq260 rule_def_10_2
    first | exact resolve eq260 rule_def_10_2 | exact resolve rule_def_10_2 eq260 | grind only
  have eq263 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq261 rule_def_10_3
    first | exact resolve eq261 rule_def_10_3 | exact resolve rule_def_10_3 eq261 | grind only
  have eq267 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0 := by
    clear * - eq262 old_0
    first | exact resolve eq262 old_0 | exact resolve old_0 eq262 | grind only
  have eq334 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq233 rule_def_11_2
    first | exact resolve eq233 rule_def_11_2 | exact resolve rule_def_11_2 eq233 | grind only
  have eq338 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq334 rule_def_1_0
    first | exact resolve eq334 rule_def_1_0 | exact resolve rule_def_1_0 eq334 | grind only
  have eq341 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq338 rule_def_2_1
    first | exact resolve eq338 rule_def_2_1 | exact resolve rule_def_2_1 eq338 | grind only
  have eq344 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq341 rule_def_3_1
    first | exact resolve eq341 rule_def_3_1 | exact resolve rule_def_3_1 eq341 | grind only
  have eq346 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq344 rule_def_4_1
    first | exact resolve eq344 rule_def_4_1 | exact resolve rule_def_4_1 eq344 | grind only
  have eq348 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq346 rule_def_8_2
    first | exact resolve eq346 rule_def_8_2 | exact resolve rule_def_8_2 eq346 | grind only
  have eq350 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq348 rule_def_9_2
    first | exact resolve eq348 rule_def_9_2 | exact resolve rule_def_9_2 eq348 | grind only
  have eq352 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq350 rule_def_10_2
    first | exact resolve eq350 rule_def_10_2 | exact resolve rule_def_10_2 eq350 | grind only
  have eq364 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq241 rule_def_11_3
    first | exact resolve eq241 rule_def_11_3 | exact resolve rule_def_11_3 eq241 | grind only
  have eq365 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq241 rule_def_11_2
    first | exact resolve eq241 rule_def_11_2 | exact resolve rule_def_11_2 eq241 | grind only
  have eq369 : (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq365 rule_def_1_0
    first | exact resolve eq365 rule_def_1_0 | exact resolve rule_def_1_0 eq365 | grind only
  have eq370 : (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq364 rule_def_1_1
    first | exact resolve eq364 rule_def_1_1 | exact resolve rule_def_1_1 eq364 | grind only
  have eq372 : (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq369 rule_def_2_1
    first | exact resolve eq369 rule_def_2_1 | exact resolve rule_def_2_1 eq369 | grind only
  have eq373 : (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq370 rule_def_2_2
    first | exact resolve eq370 rule_def_2_2 | exact resolve rule_def_2_2 eq370 | grind only
  have eq375 : (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq372 rule_def_3_1
    first | exact resolve eq372 rule_def_3_1 | exact resolve rule_def_3_1 eq372 | grind only
  have eq376 : (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq373 rule_def_3_2
    first | exact resolve eq373 rule_def_3_2 | exact resolve rule_def_3_2 eq373 | grind only
  have eq377 : (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq375 rule_def_4_1
    first | exact resolve eq375 rule_def_4_1 | exact resolve rule_def_4_1 eq375 | grind only
  have eq378 : (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq376 rule_def_4_2
    first | exact resolve eq376 rule_def_4_2 | exact resolve rule_def_4_2 eq376 | grind only
  have eq379 : (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq377 rule_def_8_2
    first | exact resolve eq377 rule_def_8_2 | exact resolve rule_def_8_2 eq377 | grind only
  have eq380 : (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq378 rule_def_8_3
    first | exact resolve eq378 rule_def_8_3 | exact resolve rule_def_8_3 eq378 | grind only
  have eq381 : (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq379 rule_def_9_2
    first | exact resolve eq379 rule_def_9_2 | exact resolve rule_def_9_2 eq379 | grind only
  have eq382 : (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq380 rule_def_9_3
    first | exact resolve eq380 rule_def_9_3 | exact resolve rule_def_9_3 eq380 | grind only
  have eq383 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq381 rule_def_10_2
    first | exact resolve eq381 rule_def_10_2 | exact resolve rule_def_10_2 eq381 | grind only
  have eq384 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq382 rule_def_10_3
    first | exact resolve eq382 rule_def_10_3 | exact resolve rule_def_10_3 eq382 | grind only
  have eq396 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq242 rule_def_11_2
    first | exact resolve eq242 rule_def_11_2 | exact resolve rule_def_11_2 eq242 | grind only
  have eq400 : (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq396 rule_def_1_0
    first | exact resolve eq396 rule_def_1_0 | exact resolve rule_def_1_0 eq396 | grind only
  have eq403 : (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq400 rule_def_2_1
    first | exact resolve eq400 rule_def_2_1 | exact resolve rule_def_2_1 eq400 | grind only
  have eq406 : (sP4 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq403 rule_def_3_1
    first | exact resolve eq403 rule_def_3_1 | exact resolve rule_def_3_1 eq403 | grind only
  have eq408 : (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq406 rule_def_4_1
    first | exact resolve eq406 rule_def_4_1 | exact resolve rule_def_4_1 eq406 | grind only
  have eq410 : (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq408 rule_def_8_2
    first | exact resolve eq408 rule_def_8_2 | exact resolve rule_def_8_2 eq408 | grind only
  have eq412 : (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq410 rule_def_9_2
    first | exact resolve eq410 rule_def_9_2 | exact resolve rule_def_9_2 eq410 | grind only
  have eq414 : (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq412 rule_def_10_2
    first | exact resolve eq412 rule_def_10_2 | exact resolve rule_def_10_2 eq412 | grind only
  have eq417 : b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ sk2 = sk3 := by
    clear * - eq383 eq267
    first | exact resolve eq383 eq267 | exact resolve eq267 eq383 | grind only
  have eq426 : b = sk1 ∨ c = sk1 ∨ sk2 = sk3 := by
    clear * - eq417
    first | exact resolve eq417 rfl | grind only
  have eq428 : c = sk1 ∨ b = sk1 := by
    clear * - eq426 preserve_2
    first | exact resolve eq426 preserve_2 | exact resolve preserve_2 eq426 | grind only
  have eq431 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq227 rule_def_11_2
    first | exact resolve eq227 rule_def_11_2 | exact resolve rule_def_11_2 eq227 | grind only
  have eq435 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq431 rule_def_1_0
    first | exact resolve eq431 rule_def_1_0 | exact resolve rule_def_1_0 eq431 | grind only
  have eq438 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq435 rule_def_2_1
    first | exact resolve eq435 rule_def_2_1 | exact resolve rule_def_2_1 eq435 | grind only
  have eq441 : (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq438 rule_def_3_1
    first | exact resolve eq438 rule_def_3_1 | exact resolve rule_def_3_1 eq438 | grind only
  have eq444 : (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq441 rule_def_4_1
    first | exact resolve eq441 rule_def_4_1 | exact resolve rule_def_4_1 eq441 | grind only
  have eq447 : (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq444 rule_def_8_2
    first | exact resolve eq444 rule_def_8_2 | exact resolve rule_def_8_2 eq444 | grind only
  have eq450 : (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq447 rule_def_9_2
    first | exact resolve eq447 rule_def_9_2 | exact resolve rule_def_9_2 eq447 | grind only
  have eq452 : (sP7 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq450 rule_def_10_2
    first | exact resolve eq450 rule_def_10_2 | exact resolve rule_def_10_2 eq450 | grind only
  have eq464 : (old sk0 c sk2) ∨ c = b ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq263 eq428
    first | exact Or.assoc3 (eq428.imp_left (fun h : c = sk1 => superpose h eq263)) | exact superpose eq263 eq428 | exact superpose eq428 eq263 | grind only
  have eq471 : c = b ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq464 p4XZ
    first | exact resolve eq464 p4XZ | exact resolve p4XZ eq464 | grind only
  have eq480 : b = sk2 ∨ b = sk1 := by
    clear * - eq471 bc
    first | exact resolve eq471 bc | exact resolve bc eq471 | grind only
  have eq484 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq236 rule_def_11_3
    first | exact resolve eq236 rule_def_11_3 | exact resolve rule_def_11_3 eq236 | grind only
  have eq485 : (sP1 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq236 rule_def_11_2
    first | exact resolve eq236 rule_def_11_2 | exact resolve rule_def_11_2 eq236 | grind only
  have eq490 : (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq485 rule_def_1_0
    first | exact resolve eq485 rule_def_1_0 | exact resolve rule_def_1_0 eq485 | grind only
  have eq491 : (sP2 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq484 rule_def_1_1
    first | exact resolve eq484 rule_def_1_1 | exact resolve rule_def_1_1 eq484 | grind only
  have eq493 : (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq490 rule_def_2_1
    first | exact resolve eq490 rule_def_2_1 | exact resolve rule_def_2_1 eq490 | grind only
  have eq494 : (sP3 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq491 rule_def_2_2
    first | exact resolve eq491 rule_def_2_2 | exact resolve rule_def_2_2 eq491 | grind only
  have eq496 : (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq493 rule_def_3_1
    first | exact resolve eq493 rule_def_3_1 | exact resolve rule_def_3_1 eq493 | grind only
  have eq497 : (sP4 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq494 rule_def_3_2
    first | exact resolve eq494 rule_def_3_2 | exact resolve rule_def_3_2 eq494 | grind only
  have eq499 : (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq496 rule_def_4_1
    first | exact resolve eq496 rule_def_4_1 | exact resolve rule_def_4_1 eq496 | grind only
  have eq500 : (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP8 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq497 rule_def_4_2
    first | exact resolve eq497 rule_def_4_2 | exact resolve rule_def_4_2 eq497 | grind only
  have eq502 : (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq499 rule_def_8_2
    first | exact resolve eq499 rule_def_8_2 | exact resolve rule_def_8_2 eq499 | grind only
  have eq503 : (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP9 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq500 rule_def_8_3
    first | exact resolve eq500 rule_def_8_3 | exact resolve rule_def_8_3 eq500 | grind only
  have eq505 : (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq502 rule_def_9_2
    first | exact resolve eq502 rule_def_9_2 | exact resolve rule_def_9_2 eq502 | grind only
  have eq506 : (sP5 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (sP10 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq503 rule_def_9_3
    first | exact resolve eq503 rule_def_9_3 | exact resolve rule_def_9_3 eq503 | grind only
  have eq507 : (sP7 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq505 rule_def_10_2
    first | exact resolve eq505 rule_def_10_2 | exact resolve rule_def_10_2 eq505 | grind only
  have eq508 : (sP7 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq506 rule_def_10_3
    first | exact resolve eq506 rule_def_10_3 | exact resolve rule_def_10_3 eq506 | grind only
  have eq572 : (old sk0 c sk3) ∨ c = b ∨ b = sk3 ∨ b = sk1 := by
    clear * - eq384 eq428
    first | exact Or.assoc3 (eq428.imp_left (fun h : c = sk1 => superpose h eq384)) | exact superpose eq384 eq428 | exact superpose eq428 eq384 | grind only
  have eq577 : c = b ∨ b = sk3 ∨ b = sk1 := by
    clear * - eq572 p4XZ
    first | exact resolve eq572 p4XZ | exact resolve p4XZ eq572 | grind only
  have eq578 : b = sk3 ∨ b = sk1 := by
    clear * - eq577 bc
    first | exact resolve eq577 bc | exact resolve bc eq577 | grind only
  have eq593 : b ≠ sk2 ∨ b = sk1 := by
    clear * - preserve_2 eq578
    first | exact (eq578.imp_left (fun h : b = sk3 => superpose h preserve_2)) | exact superpose preserve_2 eq578 | exact superpose eq578 preserve_2 | grind only
  have eq603 : b = sk1 := by
    clear * - eq593 eq480
    first | exact resolve eq593 eq480 | exact resolve eq480 eq593 | grind only
  have eq613 : (old sk0 b sk2) ∨ c = sk2 ∨ c = b := by
    clear * - eq352 eq603
    first | exact superpose eq352 eq603 | exact superpose eq603 eq352 | grind only
  have eq615 : (old sk0 b sk2) ∨ c = sk2 := by
    clear * - eq613 bc
    first | exact resolve eq613 bc | exact resolve bc eq613 | grind only
  have eq642 (X0 : G) : c = sk3 ∨ c = sk1 ∨ ¬(old sk0 sk1 X0) ∨ sk3 = X0 := by
    clear * - eq414 old_0
    first | exact resolve eq414 old_0 | exact resolve old_0 eq414 | grind only
  have eq644 : (old sk0 b sk3) ∨ c = sk3 ∨ c = b := by
    clear * - eq414 eq603
    first | exact superpose eq414 eq603 | exact superpose eq603 eq414 | grind only
  have eq648 : (old sk0 b sk3) ∨ c = sk3 := by
    clear * - eq644 bc
    first | exact resolve eq644 bc | exact resolve bc eq644 | grind only
  have eq649 (X0 : G) : c = b ∨ c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ sk3 = X0 := by
    clear * - eq642 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq642 | grind only
  have eq652 (X0 : G) : c = sk3 ∨ ¬(old sk0 sk1 X0) ∨ sk3 = X0 := by
    clear * - eq649 bc
    first | exact resolve eq649 bc | exact resolve bc eq649 | grind only
  have eq655 (X0 : G) : ¬(old sk0 b X0) ∨ c = sk3 ∨ sk3 = X0 := by
    clear * - eq652 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq652 | grind only
  have eq780 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq452 rule_def_7_1
    first | exact resolve eq452 rule_def_7_1 | exact resolve rule_def_7_1 eq452 | grind only
  have eq781 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq452 rule_def_7_0
    first | exact resolve eq452 rule_def_7_0 | exact resolve rule_def_7_0 eq452 | grind only
  have eq786 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq781 rule_def_6_0
    first | exact resolve eq781 rule_def_6_0 | exact resolve rule_def_6_0 eq781 | grind only
  have eq787 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq780 rule_def_6_1
    first | exact resolve eq780 rule_def_6_1 | exact resolve rule_def_6_1 eq780 | grind only
  have eq788 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq786 rule_def_5_0
    first | exact resolve eq786 rule_def_5_0 | exact resolve rule_def_5_0 eq786 | grind only
  have eq789 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq787 rule_def_5_1
    first | exact resolve eq787 rule_def_5_1 | exact resolve rule_def_5_1 eq787 | grind only
  have eq790 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq788 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq788 | grind only
  have eq791 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq789 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq789 | grind only
  have eq792 : c = b ∨ (old sk0 b sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq790 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq790 | grind only
  have eq793 : c = b ∨ (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq791 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq791 | grind only
  have eq794 : (old sk0 b sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq792 bc
    first | exact resolve eq792 bc | exact resolve bc eq792 | grind only
  have eq795 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq793 bc
    first | exact resolve eq793 bc | exact resolve bc eq793 | grind only
  have eq797 : a = sk0 ∨ a = b ∨ c = sk3 ∨ sk2 = sk3 := by
    clear * - eq794 eq655
    first | exact resolve eq794 eq655 | exact resolve eq655 eq794 | grind only
  have eq805 : c = sk3 ∨ a = b ∨ a = sk0 := by
    clear * - eq797 preserve_2
    first | exact resolve eq797 preserve_2 | exact resolve preserve_2 eq797 | grind only
  have eq862 : (sP7 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ a = b ∨ a = sk0 := by
    clear * - eq507 eq805
    first | exact Or.assoc6 (eq805.imp_left (fun h : c = sk3 => superpose h eq507)) | exact superpose eq507 eq805 | exact superpose eq805 eq507 | grind only
  have eq865 : (sP7 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq862
    first | exact resolve eq862 rfl | grind only
  have eq867 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq865 rule_def_7_0
    first | exact resolve eq865 rule_def_7_0 | exact resolve rule_def_7_0 eq865 | grind only
  have eq872 : (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq867 rule_def_6_0
    first | exact resolve eq867 rule_def_6_0 | exact resolve rule_def_6_0 eq867 | grind only
  have eq876 : (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq872 rule_def_5_0
    first | exact resolve eq872 rule_def_5_0 | exact resolve rule_def_5_0 eq872 | grind only
  have eq880 : a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq876 p4XY
    first | exact resolve eq876 p4XY | exact resolve p4XY eq876 | grind only
  have eq884 : c = b ∨ a = sk0 ∨ a = b := by
    clear * - eq880 eq603
    first | simpa only [eq603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq880 | grind only
  have eq888 : a = sk0 ∨ a = b := by
    clear * - eq884 bc
    first | exact resolve eq884 bc | exact resolve bc eq884 | grind only
  have eq919 : (old a b sk2) ∨ c = sk2 ∨ a = b := by
    clear * - eq615 eq888
    first | exact Or.assoc2 (eq888.imp_left (fun h : a = sk0 => superpose h eq615)) | exact superpose eq615 eq888 | exact superpose eq888 eq615 | grind only
  have eq921 : (old a b sk3) ∨ c = sk3 ∨ a = b := by
    clear * - eq648 eq888
    first | exact Or.assoc2 (eq888.imp_left (fun h : a = sk0 => superpose h eq648)) | exact superpose eq648 eq888 | exact superpose eq888 eq648 | grind only
  have eq925 : c = sk3 ∨ a = b := by
    clear * - eq921 p3
    first | exact resolve eq921 p3 | exact resolve p3 eq921 | grind only
  have eq926 : c = sk2 ∨ a = b := by
    clear * - eq919 p3
    first | exact resolve eq919 p3 | exact resolve p3 eq919 | grind only
  have eq983 : c ≠ sk2 ∨ a = b := by
    clear * - preserve_2 eq925
    first | exact (eq925.imp_left (fun h : c = sk3 => superpose h preserve_2)) | exact superpose preserve_2 eq925 | exact superpose eq925 preserve_2 | grind only
  have eq995 : a = b := by
    clear * - eq983 eq926
    first | exact resolve eq983 eq926 | exact resolve eq926 eq983 | grind only
  have eq1008 (X0 : G) : ¬(old b b X0) := by
    clear * - p3 eq995
    first | exact superpose p3 eq995 | exact superpose eq995 p3 | grind only
  have eq1239 : a = sk0 ∨ c = sk0 ∨ c = sk3 ∨ sk2 = sk3 := by
    clear * - eq795 eq655
    first | exact resolve eq795 eq655 | exact resolve eq655 eq795 | grind only
  have eq1252 : a = sk0 ∨ c = sk0 ∨ c = sk3 := by
    clear * - eq1239 preserve_2
    first | exact resolve eq1239 preserve_2 | exact resolve preserve_2 eq1239 | grind only
  have eq1254 : c = sk3 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1252 eq995
    first | simpa only [eq995, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq1252 | grind only
  have eq1271 : (sP7 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq508 eq1254
    first | exact Or.assoc6 (eq1254.imp_left (fun h : c = sk3 => superpose h eq508)) | exact superpose eq508 eq1254 | exact superpose eq1254 eq508 | grind only
  have eq1277 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1271 rule_def_7_1
    first | exact resolve eq1271 rule_def_7_1 | exact resolve rule_def_7_1 eq1271 | grind only
  have eq1283 : (sP5 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1277 rule_def_6_1
    first | exact resolve eq1277 rule_def_6_1 | exact resolve rule_def_6_1 eq1277 | grind only
  have eq1288 : (old sk0 sk1 c) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1283 rule_def_5_1
    first | exact resolve eq1283 rule_def_5_1 | exact resolve rule_def_5_1 eq1283 | grind only
  have eq1293 : a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1288 p4XY
    first | exact resolve eq1288 p4XY | exact resolve p4XY eq1288 | grind only
  have eq1298 : a = sk0 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1293 bc
    first | exact resolve eq1293 bc | exact resolve bc eq1293 | grind only
  have eq1304 : b = sk0 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq1298 eq995
    first | simpa only [eq995, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq1298 | grind only
  have eq1305 : c = sk0 ∨ b = sk0 := by
    clear * - eq1304
    first | exact resolve eq1304 rfl | grind only
  have eq1358 : (old c b sk2) ∨ c = sk2 ∨ b = sk0 := by
    clear * - eq615 eq1305
    first | exact Or.assoc2 (eq1305.imp_left (fun h : c = sk0 => superpose h eq615)) | exact superpose eq615 eq1305 | exact superpose eq1305 eq615 | grind only
  have eq1360 : (old c b sk3) ∨ c = sk3 ∨ b = sk0 := by
    clear * - eq648 eq1305
    first | exact Or.assoc2 (eq1305.imp_left (fun h : c = sk0 => superpose h eq648)) | exact superpose eq648 eq1305 | exact superpose eq1305 eq648 | grind only
  have eq1368 : c = sk3 ∨ b = sk0 := by
    clear * - eq1360 p4YZ
    first | exact resolve eq1360 p4YZ | exact resolve p4YZ eq1360 | grind only
  have eq1369 : c = sk2 ∨ b = sk0 := by
    clear * - eq1358 p4YZ
    first | exact resolve eq1358 p4YZ | exact resolve p4YZ eq1358 | grind only
  have eq1468 : c ≠ sk2 ∨ b = sk0 := by
    clear * - preserve_2 eq1368
    first | exact (eq1368.imp_left (fun h : c = sk3 => superpose h preserve_2)) | exact superpose preserve_2 eq1368 | exact superpose eq1368 preserve_2 | grind only
  have eq1491 : b = sk0 := by
    clear * - eq1468 eq1369
    first | exact resolve eq1468 eq1369 | exact resolve eq1369 eq1468 | grind only
  have eq1541 : (old b b sk2) ∨ c = sk2 := by
    clear * - eq615 eq1491
    first | exact superpose eq615 eq1491 | exact superpose eq1491 eq615 | grind only
  have eq1543 : (old b b sk3) ∨ c = sk3 := by
    clear * - eq648 eq1491
    first | exact superpose eq648 eq1491 | exact superpose eq1491 eq648 | grind only
  have eq1555 : c = sk3 := by
    clear * - eq1543 eq1008
    first | exact resolve eq1543 eq1008 | exact resolve eq1008 eq1543 | grind only
  have eq1556 : c = sk2 := by
    clear * - eq1541 eq1008
    first | exact resolve eq1541 eq1008 | exact resolve eq1008 eq1541 | grind only
  have eq1620 : c ≠ sk2 := by
    clear * - preserve_2 eq1555
    first | exact superpose preserve_2 eq1555 | exact superpose eq1555 preserve_2 | grind only
  clear * - eq1620 eq1556
  first | subsumption eq1620 eq1556 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (new_new : new a b c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X3 ∨ ¬ old X3 X1 X4 ∨ old X0 X4 X1)) (old_4 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X0 X1)) (old_5 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X1 X0)) (old_7 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X1 X1)) (old_8 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X3 ∨ ¬ old X2 X1 X4 ∨ ¬ old X2 X4 X3 ∨ old X1 X1 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ b ≠ Z ∨ ¬ old X b X2 ∨ ¬ old X X2 a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z, c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ ¬ old b b a ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (imp_new_8 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), a = b ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), c = X ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_0 : ∀ (X Y Z : G), a = b ∨ ¬sP9 X Y Z) (rule_def_9_1 : ∀ (X Y Z : G), c = X ∨ ¬sP9 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (imp_new_11 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_10_0 : ∀ (X Y Z : G), a = b ∨ ¬sP10 X Y Z) (rule_def_10_1 : ∀ (X Y Z : G), c = X ∨ ¬sP10 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (imp_new_12 : ∀ X Y Z, a ≠ b ∨ b ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_11_0 : ∀ (X Y Z : G), a = b ∨ ¬sP11 X Y Z) (rule_def_11_1 : ∀ (X Y Z : G), b = X ∨ ¬sP11 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X3 ∨ ¬ new X3 X1 X4 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq168 (X0 X2 X3 : G) : b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X0 X3 a) ∨ (new X0 c X2) := by
    clear * - imp_new_2
    first | exact resolve imp_new_2 rfl | grind only
  have eq169 (X0 X3 : G) : ¬(old X0 b X3) ∨ ¬(old X0 X3 a) ∨ (new X0 c b) := by
    clear * - eq168
    first | exact resolve eq168 rfl | grind only
  have eq176 (X1 X2 : G) : c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b b a) ∨ (new c X1 X2) := by
    clear * - imp_new_5
    first | exact resolve imp_new_5 rfl | grind only
  have eq177 (X2 : G) : b ≠ X2 ∨ ¬(old b b a) ∨ (new c c X2) := by
    clear * - eq176
    first | exact resolve eq176 rfl | grind only
  have eq178 : ¬(old b b a) ∨ (new c c b) := by
    clear * - eq177
    first | exact resolve eq177 rfl | grind only
  have eq185 (X1 X2 : G) : a ≠ b ∨ b ≠ X1 ∨ c ≠ X2 ∨ (new c X1 X2) := by
    clear * - imp_new_8
    first | exact resolve imp_new_8 rfl | grind only
  have eq186 (X2 : G) : a ≠ b ∨ c ≠ X2 ∨ (new c b X2) := by
    clear * - eq185
    first | exact resolve eq185 rfl | grind only
  have eq187 : a ≠ b ∨ (new c b c) := by
    clear * - eq186
    first | exact resolve eq186 rfl | grind only
  have eq194 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new c X1 X2) := by
    clear * - imp_new_11
    first | exact resolve imp_new_11 rfl | grind only
  have eq195 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new c c X2) := by
    clear * - eq194
    first | exact resolve eq194 rfl | grind only
  have eq196 : a ≠ b ∨ (new c c b) := by
    clear * - eq195
    first | exact resolve eq195 rfl | grind only
  have eq197 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new b X1 X2) := by
    clear * - imp_new_12
    first | exact resolve imp_new_12 rfl | grind only
  have eq198 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new b c X2) := by
    clear * - eq197
    first | exact resolve eq197 rfl | grind only
  have eq199 : a ≠ b ∨ (new b c b) := by
    clear * - eq198
    first | exact resolve eq198 rfl | grind only
  have eq200 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old X0 b X3) ∨ (sF0 X0 X1 X2) = X3 := by
    clear * - rule_def_1_2 old_0
    first | exact resolve rule_def_1_2 old_0 | exact resolve old_0 rule_def_1_2 | grind only
  have eq201 (X0 X1 X2 : G) : (new X0 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - rule_def_1_2 imp_new_0
    first | exact resolve rule_def_1_2 imp_new_0 | exact resolve imp_new_0 rule_def_1_2 | grind only
  have eq205 (X0 X1 : G) : ¬(sP1 a X0 X1) := by
    clear * - rule_def_1_2 p3
    first | exact resolve rule_def_1_2 p3 | exact resolve p3 rule_def_1_2 | grind only
  have eq209 (X0 X1 X2 : G) : (new X0 (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - rule_def_1_3 imp_new_0
    first | exact resolve rule_def_1_3 imp_new_0 | exact resolve imp_new_0 rule_def_1_3 | grind only
  have eq211 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := by
    clear * - prev_0 preserve_0
    first | exact resolve prev_0 preserve_0 | exact resolve preserve_0 prev_0 | grind only
  have eq212 (X0 : G) : ¬(new sk0 sk2 X0) ∨ sk3 = X0 := by
    clear * - prev_0 preserve_1
    first | exact resolve prev_0 preserve_1 | exact resolve preserve_1 prev_0 | grind only
  have eq214 (X0 : G) : ¬(new a b X0) ∨ c = X0 := by
    clear * - prev_0 new_new
    first | exact resolve prev_0 new_new | exact resolve new_new prev_0 | grind only
  have eq218 (X0 X1 X2 : G) : ¬(old X0 (sF0 X0 X1 X2) a) ∨ (new X0 c b) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - eq169 rule_def_1_2
    first | exact resolve eq169 rule_def_1_2 | exact resolve rule_def_1_2 eq169 | grind only
  have eq219 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c b) := by
    clear * - eq218 rule_def_1_3
    first | exact resolve eq218 rule_def_1_3 | exact resolve rule_def_1_3 eq218 | grind only
  have eq225 (X0 X1 X2 X3 X4 : G) : ¬(old X1 X2 (sF0 X1 X3 X4)) ∨ ¬(old X0 X1 a) ∨ ¬(old X0 X2 X1) ∨ (old X2 X2 X1) ∨ ¬(sP1 X1 X3 X4) := by
    clear * - old_8 rule_def_1_3
    first | exact resolve old_8 rule_def_1_3 | exact resolve rule_def_1_3 old_8 | grind only
  have eq226 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq227 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq228 : (sP0 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) := by
    clear * - new_imp preserve_2
    first | exact resolve new_imp preserve_2 | exact resolve preserve_2 new_imp | grind only
  have eq232 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq226 rule_def_0_2
    first | exact resolve eq226 rule_def_0_2 | exact resolve rule_def_0_2 eq226 | grind only
  have eq233 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq226 rule_def_0_1
    first | exact resolve eq226 rule_def_0_1 | exact resolve rule_def_0_1 eq226 | grind only
  have eq234 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq226 rule_def_0_0
    first | exact resolve eq226 rule_def_0_0 | exact resolve rule_def_0_0 eq226 | grind only
  have eq235 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq233 rule_def_5_2
    first | exact resolve eq233 rule_def_5_2 | exact resolve rule_def_5_2 eq233 | grind only
  have eq236 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq232 rule_def_5_3
    first | exact resolve eq232 rule_def_5_3 | exact resolve rule_def_5_3 eq232 | grind only
  have eq237 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq235 rule_def_6_2
    first | exact resolve eq235 rule_def_6_2 | exact resolve rule_def_6_2 eq235 | grind only
  have eq238 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq236 rule_def_6_3
    first | exact resolve eq236 rule_def_6_3 | exact resolve rule_def_6_3 eq236 | grind only
  have eq239 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq237 rule_def_7_2
    first | exact resolve eq237 rule_def_7_2 | exact resolve rule_def_7_2 eq237 | grind only
  have eq240 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq238 rule_def_7_3
    first | exact resolve eq238 rule_def_7_3 | exact resolve rule_def_7_3 eq238 | grind only
  have eq241 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq227 rule_def_0_2
    first | exact resolve eq227 rule_def_0_2 | exact resolve rule_def_0_2 eq227 | grind only
  have eq242 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq227 rule_def_0_1
    first | exact resolve eq227 rule_def_0_1 | exact resolve rule_def_0_1 eq227 | grind only
  have eq243 : (sP11 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 := by
    clear * - eq227 rule_def_0_0
    first | exact resolve eq227 rule_def_0_0 | exact resolve rule_def_0_0 eq227 | grind only
  have eq244 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq242 rule_def_5_2
    first | exact resolve eq242 rule_def_5_2 | exact resolve rule_def_5_2 eq242 | grind only
  have eq245 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq241 rule_def_5_3
    first | exact resolve eq241 rule_def_5_3 | exact resolve rule_def_5_3 eq241 | grind only
  have eq246 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq244 rule_def_6_2
    first | exact resolve eq244 rule_def_6_2 | exact resolve rule_def_6_2 eq244 | grind only
  have eq247 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq245 rule_def_6_3
    first | exact resolve eq245 rule_def_6_3 | exact resolve rule_def_6_3 eq245 | grind only
  have eq248 : (sP11 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq246 rule_def_7_2
    first | exact resolve eq246 rule_def_7_2 | exact resolve rule_def_7_2 eq246 | grind only
  have eq249 : (sP11 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq247 rule_def_7_3
    first | exact resolve eq247 rule_def_7_3 | exact resolve rule_def_7_3 eq247 | grind only
  have eq250 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq239 rule_def_11_3
    first | exact resolve eq239 rule_def_11_3 | exact resolve rule_def_11_3 eq239 | grind only
  have eq251 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq239 rule_def_11_2
    first | exact resolve eq239 rule_def_11_2 | exact resolve rule_def_11_2 eq239 | grind only
  have eq252 : (sP10 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq239 rule_def_11_1
    first | exact resolve eq239 rule_def_11_1 | exact resolve rule_def_11_1 eq239 | grind only
  have eq253 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b := by
    clear * - eq239 rule_def_11_0
    first | exact resolve eq239 rule_def_11_0 | exact resolve rule_def_11_0 eq239 | grind only
  have eq254 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b := by
    clear * - eq253 rule_def_8_0
    first | exact resolve eq253 rule_def_8_0 | exact resolve rule_def_8_0 eq253 | grind only
  have eq255 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq251 rule_def_1_0
    first | exact resolve eq251 rule_def_1_0 | exact resolve rule_def_1_0 eq251 | grind only
  have eq256 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq250 rule_def_1_1
    first | exact resolve eq250 rule_def_1_1 | exact resolve rule_def_1_1 eq250 | grind only
  have eq257 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b := by
    clear * - eq254 rule_def_9_0
    first | exact resolve eq254 rule_def_9_0 | exact resolve rule_def_9_0 eq254 | grind only
  have eq258 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq255 rule_def_2_1
    first | exact resolve eq255 rule_def_2_1 | exact resolve rule_def_2_1 eq255 | grind only
  have eq259 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq256 rule_def_2_2
    first | exact resolve eq256 rule_def_2_2 | exact resolve rule_def_2_2 eq256 | grind only
  have eq260 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b := by
    clear * - eq257 rule_def_10_0
    first | exact resolve eq257 rule_def_10_0 | exact resolve rule_def_10_0 eq257 | grind only
  have eq261 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq258 rule_def_3_1
    first | exact resolve eq258 rule_def_3_1 | exact resolve rule_def_3_1 eq258 | grind only
  have eq262 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq259 rule_def_3_2
    first | exact resolve eq259 rule_def_3_2 | exact resolve rule_def_3_2 eq259 | grind only
  have eq263 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq261 rule_def_4_1
    first | exact resolve eq261 rule_def_4_1 | exact resolve rule_def_4_1 eq261 | grind only
  have eq264 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq262 rule_def_4_2
    first | exact resolve eq262 rule_def_4_2 | exact resolve rule_def_4_2 eq262 | grind only
  have eq265 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq263 rule_def_8_2
    first | exact resolve eq263 rule_def_8_2 | exact resolve rule_def_8_2 eq263 | grind only
  have eq266 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq264 rule_def_8_3
    first | exact resolve eq264 rule_def_8_3 | exact resolve rule_def_8_3 eq264 | grind only
  have eq267 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq265 rule_def_9_2
    first | exact resolve eq265 rule_def_9_2 | exact resolve rule_def_9_2 eq265 | grind only
  have eq268 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq266 rule_def_9_3
    first | exact resolve eq266 rule_def_9_3 | exact resolve rule_def_9_3 eq266 | grind only
  have eq269 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq267 rule_def_10_2
    first | exact resolve eq267 rule_def_10_2 | exact resolve rule_def_10_2 eq267 | grind only
  have eq270 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq268 rule_def_10_3
    first | exact resolve eq268 rule_def_10_3 | exact resolve rule_def_10_3 eq268 | grind only
  have eq271 : (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) ∨ c = sk4 := by
    clear * - eq228 rule_def_0_2
    first | exact resolve eq228 rule_def_0_2 | exact resolve rule_def_0_2 eq228 | grind only
  have eq272 : (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) ∨ b = sk1 := by
    clear * - eq228 rule_def_0_1
    first | exact resolve eq228 rule_def_0_1 | exact resolve rule_def_0_1 eq228 | grind only
  have eq273 : (sP11 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 := by
    clear * - eq228 rule_def_0_0
    first | exact resolve eq228 rule_def_0_0 | exact resolve rule_def_0_0 eq228 | grind only
  have eq274 : (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) ∨ b = sk1 := by
    clear * - eq272 rule_def_5_2
    first | exact resolve eq272 rule_def_5_2 | exact resolve rule_def_5_2 eq272 | grind only
  have eq275 : (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) ∨ c = sk4 := by
    clear * - eq271 rule_def_5_3
    first | exact resolve eq271 rule_def_5_3 | exact resolve rule_def_5_3 eq271 | grind only
  have eq276 : (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) ∨ b = sk1 := by
    clear * - eq274 rule_def_6_2
    first | exact resolve eq274 rule_def_6_2 | exact resolve rule_def_6_2 eq274 | grind only
  have eq277 : (old sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (sP11 sk3 sk1 sk4) ∨ c = sk4 := by
    clear * - eq275 rule_def_6_3
    first | exact resolve eq275 rule_def_6_3 | exact resolve rule_def_6_3 eq275 | grind only
  have eq278 : (sP11 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 := by
    clear * - eq276 rule_def_7_2
    first | exact resolve eq276 rule_def_7_2 | exact resolve rule_def_7_2 eq276 | grind only
  have eq279 : (sP11 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 := by
    clear * - eq277 rule_def_7_3
    first | exact resolve eq277 rule_def_7_3 | exact resolve rule_def_7_3 eq277 | grind only
  have eq341 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq260 rule_def_4_3
    first | exact resolve eq260 rule_def_4_3 | exact resolve rule_def_4_3 eq260 | grind only
  have eq346 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq341 rule_def_2_3
    first | exact resolve eq341 rule_def_2_3 | exact resolve rule_def_2_3 eq341 | grind only
  have eq348 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq346 rule_def_3_3
    first | exact resolve eq346 rule_def_3_3 | exact resolve rule_def_3_3 eq346 | grind only
  have eq358 (X0 X1 X2 X3 : G) : ¬(old X0 X1 a) ∨ ¬(old X0 b X1) ∨ (old b b X1) ∨ ¬(sP1 X1 X2 X3) ∨ ¬(sP1 X1 X2 X3) := by
    clear * - eq225 rule_def_1_2
    first | exact resolve eq225 rule_def_1_2 | exact resolve rule_def_1_2 eq225 | grind only
  have eq359 (X0 X1 X2 X3 : G) : ¬(sP1 X1 X2 X3) ∨ ¬(old X0 b X1) ∨ (old b b X1) ∨ ¬(old X0 X1 a) := by
    clear * - eq358
    first | exact resolve eq358 rfl | grind only
  have eq381 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq240 rule_def_11_3
    first | exact resolve eq240 rule_def_11_3 | exact resolve rule_def_11_3 eq240 | grind only
  have eq382 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq240 rule_def_11_2
    first | exact resolve eq240 rule_def_11_2 | exact resolve rule_def_11_2 eq240 | grind only
  have eq386 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq382 rule_def_1_0
    first | exact resolve eq382 rule_def_1_0 | exact resolve rule_def_1_0 eq382 | grind only
  have eq387 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq381 rule_def_1_1
    first | exact resolve eq381 rule_def_1_1 | exact resolve rule_def_1_1 eq381 | grind only
  have eq389 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq386 rule_def_2_1
    first | exact resolve eq386 rule_def_2_1 | exact resolve rule_def_2_1 eq386 | grind only
  have eq390 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq387 rule_def_2_2
    first | exact resolve eq387 rule_def_2_2 | exact resolve rule_def_2_2 eq387 | grind only
  have eq392 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq389 rule_def_3_1
    first | exact resolve eq389 rule_def_3_1 | exact resolve rule_def_3_1 eq389 | grind only
  have eq393 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq390 rule_def_3_2
    first | exact resolve eq390 rule_def_3_2 | exact resolve rule_def_3_2 eq390 | grind only
  have eq394 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq392 rule_def_4_1
    first | exact resolve eq392 rule_def_4_1 | exact resolve rule_def_4_1 eq392 | grind only
  have eq395 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq393 rule_def_4_2
    first | exact resolve eq393 rule_def_4_2 | exact resolve rule_def_4_2 eq393 | grind only
  have eq396 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq394 rule_def_8_2
    first | exact resolve eq394 rule_def_8_2 | exact resolve rule_def_8_2 eq394 | grind only
  have eq397 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq395 rule_def_8_3
    first | exact resolve eq395 rule_def_8_3 | exact resolve rule_def_8_3 eq395 | grind only
  have eq398 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq396 rule_def_9_2
    first | exact resolve eq396 rule_def_9_2 | exact resolve rule_def_9_2 eq396 | grind only
  have eq399 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq397 rule_def_9_3
    first | exact resolve eq397 rule_def_9_3 | exact resolve rule_def_9_3 eq397 | grind only
  have eq400 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq398 rule_def_10_2
    first | exact resolve eq398 rule_def_10_2 | exact resolve rule_def_10_2 eq398 | grind only
  have eq401 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq399 rule_def_10_3
    first | exact resolve eq399 rule_def_10_3 | exact resolve rule_def_10_3 eq399 | grind only
  have eq412 : (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq248 rule_def_11_3
    first | exact resolve eq248 rule_def_11_3 | exact resolve rule_def_11_3 eq248 | grind only
  have eq413 : (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq248 rule_def_11_2
    first | exact resolve eq248 rule_def_11_2 | exact resolve rule_def_11_2 eq248 | grind only
  have eq417 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq413 rule_def_1_0
    first | exact resolve eq413 rule_def_1_0 | exact resolve rule_def_1_0 eq413 | grind only
  have eq418 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq412 rule_def_1_1
    first | exact resolve eq412 rule_def_1_1 | exact resolve rule_def_1_1 eq412 | grind only
  have eq420 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq417 rule_def_2_1
    first | exact resolve eq417 rule_def_2_1 | exact resolve rule_def_2_1 eq417 | grind only
  have eq421 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq418 rule_def_2_2
    first | exact resolve eq418 rule_def_2_2 | exact resolve rule_def_2_2 eq418 | grind only
  have eq423 : (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq420 rule_def_3_1
    first | exact resolve eq420 rule_def_3_1 | exact resolve rule_def_3_1 eq420 | grind only
  have eq424 : (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq421 rule_def_3_2
    first | exact resolve eq421 rule_def_3_2 | exact resolve rule_def_3_2 eq421 | grind only
  have eq425 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq423 rule_def_4_1
    first | exact resolve eq423 rule_def_4_1 | exact resolve rule_def_4_1 eq423 | grind only
  have eq426 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq424 rule_def_4_2
    first | exact resolve eq424 rule_def_4_2 | exact resolve rule_def_4_2 eq424 | grind only
  have eq427 : (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq425 rule_def_8_2
    first | exact resolve eq425 rule_def_8_2 | exact resolve rule_def_8_2 eq425 | grind only
  have eq428 : (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq426 rule_def_8_3
    first | exact resolve eq426 rule_def_8_3 | exact resolve rule_def_8_3 eq426 | grind only
  have eq429 : (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq427 rule_def_9_2
    first | exact resolve eq427 rule_def_9_2 | exact resolve rule_def_9_2 eq427 | grind only
  have eq430 : (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq428 rule_def_9_3
    first | exact resolve eq428 rule_def_9_3 | exact resolve rule_def_9_3 eq428 | grind only
  have eq431 : (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq429 rule_def_10_2
    first | exact resolve eq429 rule_def_10_2 | exact resolve rule_def_10_2 eq429 | grind only
  have eq432 : (old sk0 sk2 sk3) ∨ b = sk2 ∨ b = sk3 := by
    clear * - eq430 rule_def_10_3
    first | exact resolve eq430 rule_def_10_3 | exact resolve rule_def_10_3 eq430 | grind only
  have eq444 : (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq249 rule_def_11_2
    first | exact resolve eq249 rule_def_11_2 | exact resolve rule_def_11_2 eq249 | grind only
  have eq445 : (sP10 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 := by
    clear * - eq249 rule_def_11_1
    first | exact resolve eq249 rule_def_11_1 | exact resolve rule_def_11_1 eq249 | grind only
  have eq448 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq444 rule_def_1_0
    first | exact resolve eq444 rule_def_1_0 | exact resolve rule_def_1_0 eq444 | grind only
  have eq451 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq448 rule_def_2_1
    first | exact resolve eq448 rule_def_2_1 | exact resolve rule_def_2_1 eq448 | grind only
  have eq454 : (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq451 rule_def_3_1
    first | exact resolve eq451 rule_def_3_1 | exact resolve rule_def_3_1 eq451 | grind only
  have eq456 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq454 rule_def_4_1
    first | exact resolve eq454 rule_def_4_1 | exact resolve rule_def_4_1 eq454 | grind only
  have eq458 : (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq456 rule_def_8_2
    first | exact resolve eq456 rule_def_8_2 | exact resolve rule_def_8_2 eq456 | grind only
  have eq460 : (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq458 rule_def_9_2
    first | exact resolve eq458 rule_def_9_2 | exact resolve rule_def_9_2 eq458 | grind only
  have eq462 : (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq460 rule_def_10_2
    first | exact resolve eq460 rule_def_10_2 | exact resolve rule_def_10_2 eq460 | grind only
  have eq468 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq278 rule_def_11_3
    first | exact resolve eq278 rule_def_11_3 | exact resolve rule_def_11_3 eq278 | grind only
  have eq469 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq278 rule_def_11_2
    first | exact resolve eq278 rule_def_11_2 | exact resolve rule_def_11_2 eq278 | grind only
  have eq470 : (sP10 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 := by
    clear * - eq278 rule_def_11_1
    first | exact resolve eq278 rule_def_11_1 | exact resolve rule_def_11_1 eq278 | grind only
  have eq471 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b := by
    clear * - eq278 rule_def_11_0
    first | exact resolve eq278 rule_def_11_0 | exact resolve rule_def_11_0 eq278 | grind only
  have eq472 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b := by
    clear * - eq471 rule_def_8_0
    first | exact resolve eq471 rule_def_8_0 | exact resolve rule_def_8_0 eq471 | grind only
  have eq473 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq469 rule_def_1_0
    first | exact resolve eq469 rule_def_1_0 | exact resolve rule_def_1_0 eq469 | grind only
  have eq474 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq468 rule_def_1_1
    first | exact resolve eq468 rule_def_1_1 | exact resolve rule_def_1_1 eq468 | grind only
  have eq475 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b := by
    clear * - eq472 rule_def_9_0
    first | exact resolve eq472 rule_def_9_0 | exact resolve rule_def_9_0 eq472 | grind only
  have eq476 : (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq473 rule_def_2_1
    first | exact resolve eq473 rule_def_2_1 | exact resolve rule_def_2_1 eq473 | grind only
  have eq477 : (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq474 rule_def_2_2
    first | exact resolve eq474 rule_def_2_2 | exact resolve rule_def_2_2 eq474 | grind only
  have eq478 : (sP4 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b := by
    clear * - eq475 rule_def_10_0
    first | exact resolve eq475 rule_def_10_0 | exact resolve rule_def_10_0 eq475 | grind only
  have eq479 : (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq476 rule_def_3_1
    first | exact resolve eq476 rule_def_3_1 | exact resolve rule_def_3_1 eq476 | grind only
  have eq480 : (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq477 rule_def_3_2
    first | exact resolve eq477 rule_def_3_2 | exact resolve rule_def_3_2 eq477 | grind only
  have eq481 : (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq479 rule_def_4_1
    first | exact resolve eq479 rule_def_4_1 | exact resolve rule_def_4_1 eq479 | grind only
  have eq482 : (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq480 rule_def_4_2
    first | exact resolve eq480 rule_def_4_2 | exact resolve rule_def_4_2 eq480 | grind only
  have eq483 : (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq481 rule_def_8_2
    first | exact resolve eq481 rule_def_8_2 | exact resolve rule_def_8_2 eq481 | grind only
  have eq484 : (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq482 rule_def_8_3
    first | exact resolve eq482 rule_def_8_3 | exact resolve rule_def_8_3 eq482 | grind only
  have eq485 : (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq483 rule_def_9_2
    first | exact resolve eq483 rule_def_9_2 | exact resolve rule_def_9_2 eq483 | grind only
  have eq486 : (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq484 rule_def_9_3
    first | exact resolve eq484 rule_def_9_3 | exact resolve rule_def_9_3 eq484 | grind only
  have eq487 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq485 rule_def_10_2
    first | exact resolve eq485 rule_def_10_2 | exact resolve rule_def_10_2 eq485 | grind only
  have eq488 : (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk4 := by
    clear * - eq486 rule_def_10_3
    first | exact resolve eq486 rule_def_10_3 | exact resolve rule_def_10_3 eq486 | grind only
  have eq494 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq279 rule_def_11_2
    first | exact resolve eq279 rule_def_11_2 | exact resolve rule_def_11_2 eq279 | grind only
  have eq498 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq494 rule_def_1_0
    first | exact resolve eq494 rule_def_1_0 | exact resolve rule_def_1_0 eq494 | grind only
  have eq501 : (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq498 rule_def_2_1
    first | exact resolve eq498 rule_def_2_1 | exact resolve rule_def_2_1 eq498 | grind only
  have eq504 : (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq501 rule_def_3_1
    first | exact resolve eq501 rule_def_3_1 | exact resolve rule_def_3_1 eq501 | grind only
  have eq506 : (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq504 rule_def_4_1
    first | exact resolve eq504 rule_def_4_1 | exact resolve rule_def_4_1 eq504 | grind only
  have eq508 : (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq506 rule_def_8_2
    first | exact resolve eq506 rule_def_8_2 | exact resolve rule_def_8_2 eq506 | grind only
  have eq510 : (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq508 rule_def_9_2
    first | exact resolve eq508 rule_def_9_2 | exact resolve rule_def_9_2 eq508 | grind only
  have eq512 : (old sk3 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq510 rule_def_10_2
    first | exact resolve eq510 rule_def_10_2 | exact resolve rule_def_10_2 eq510 | grind only
  have eq519 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq234 rule_def_11_2
    first | exact resolve eq234 rule_def_11_2 | exact resolve rule_def_11_2 eq234 | grind only
  have eq523 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq519 rule_def_1_0
    first | exact resolve eq519 rule_def_1_0 | exact resolve rule_def_1_0 eq519 | grind only
  have eq526 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq523 rule_def_2_1
    first | exact resolve eq523 rule_def_2_1 | exact resolve rule_def_2_1 eq523 | grind only
  have eq529 : (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq526 rule_def_3_1
    first | exact resolve eq526 rule_def_3_1 | exact resolve rule_def_3_1 eq526 | grind only
  have eq532 : (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq529 rule_def_4_1
    first | exact resolve eq529 rule_def_4_1 | exact resolve rule_def_4_1 eq529 | grind only
  have eq535 : (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq532 rule_def_8_2
    first | exact resolve eq532 rule_def_8_2 | exact resolve rule_def_8_2 eq532 | grind only
  have eq538 : (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq535 rule_def_9_2
    first | exact resolve eq535 rule_def_9_2 | exact resolve rule_def_9_2 eq535 | grind only
  have eq540 : (sP7 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := by
    clear * - eq538 rule_def_10_2
    first | exact resolve eq538 rule_def_10_2 | exact resolve rule_def_10_2 eq538 | grind only
  have eq546 : (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq243 rule_def_11_3
    first | exact resolve eq243 rule_def_11_3 | exact resolve rule_def_11_3 eq243 | grind only
  have eq548 : (sP10 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq243 rule_def_11_1
    first | exact resolve eq243 rule_def_11_1 | exact resolve rule_def_11_1 eq243 | grind only
  have eq552 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq546 rule_def_1_1
    first | exact resolve eq546 rule_def_1_1 | exact resolve rule_def_1_1 eq546 | grind only
  have eq555 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq552 rule_def_2_2
    first | exact resolve eq552 rule_def_2_2 | exact resolve rule_def_2_2 eq552 | grind only
  have eq558 : (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq555 rule_def_3_2
    first | exact resolve eq555 rule_def_3_2 | exact resolve rule_def_3_2 eq555 | grind only
  have eq561 : (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq558 rule_def_4_2
    first | exact resolve eq558 rule_def_4_2 | exact resolve rule_def_4_2 eq558 | grind only
  have eq564 : (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq561 rule_def_8_3
    first | exact resolve eq561 rule_def_8_3 | exact resolve rule_def_8_3 eq561 | grind only
  have eq567 : (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq564 rule_def_9_3
    first | exact resolve eq564 rule_def_9_3 | exact resolve rule_def_9_3 eq564 | grind only
  have eq569 : (sP7 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq567 rule_def_10_3
    first | exact resolve eq567 rule_def_10_3 | exact resolve rule_def_10_3 eq567 | grind only
  have eq573 (X0 X1 : G) : ¬(old X0 sk1 X1) ∨ c = sk1 ∨ ¬(old X0 X1 sk3) ∨ b = sk1 ∨ (old X0 sk4 sk1) := by
    clear * - eq487 old_1
    first | exact resolve eq487 old_1 | exact resolve old_1 eq487 | grind only
  have eq579 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq273 rule_def_11_2
    first | exact resolve eq273 rule_def_11_2 | exact resolve rule_def_11_2 eq273 | grind only
  have eq581 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq273 rule_def_11_0
    first | exact resolve eq273 rule_def_11_0 | exact resolve rule_def_11_0 eq273 | grind only
  have eq582 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq581 rule_def_5_0
    first | exact resolve eq581 rule_def_5_0 | exact resolve rule_def_5_0 eq581 | grind only
  have eq583 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq579 rule_def_1_0
    first | exact resolve eq579 rule_def_1_0 | exact resolve rule_def_1_0 eq579 | grind only
  have eq585 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq582 rule_def_6_0
    first | exact resolve eq582 rule_def_6_0 | exact resolve rule_def_6_0 eq582 | grind only
  have eq586 : (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq583 rule_def_2_1
    first | exact resolve eq583 rule_def_2_1 | exact resolve rule_def_2_1 eq583 | grind only
  have eq588 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq585 rule_def_7_0
    first | exact resolve eq585 rule_def_7_0 | exact resolve rule_def_7_0 eq585 | grind only
  have eq589 : (sP4 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq586 rule_def_3_1
    first | exact resolve eq586 rule_def_3_1 | exact resolve rule_def_3_1 eq586 | grind only
  have eq591 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq588 rule_def_8_0
    first | exact resolve eq588 rule_def_8_0 | exact resolve rule_def_8_0 eq588 | grind only
  have eq592 : (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq589 rule_def_4_1
    first | exact resolve eq589 rule_def_4_1 | exact resolve rule_def_4_1 eq589 | grind only
  have eq594 : (sP1 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq591 rule_def_9_0
    first | exact resolve eq591 rule_def_9_0 | exact resolve rule_def_9_0 eq591 | grind only
  have eq595 : (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq592 rule_def_8_2
    first | exact resolve eq592 rule_def_8_2 | exact resolve rule_def_8_2 eq592 | grind only
  have eq597 : (sP4 sk3 sk1 sk4) ∨ (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq594 rule_def_10_0
    first | exact resolve eq594 rule_def_10_0 | exact resolve rule_def_10_0 eq594 | grind only
  have eq598 : (sP5 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP7 sk3 sk1 sk4) ∨ (sP10 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq595 rule_def_9_2
    first | exact resolve eq595 rule_def_9_2 | exact resolve rule_def_9_2 eq595 | grind only
  have eq600 : (sP7 sk3 sk1 sk4) ∨ (sP6 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 := by
    clear * - eq598 rule_def_10_2
    first | exact resolve eq598 rule_def_10_2 | exact resolve rule_def_10_2 eq598 | grind only
  have eq613 (X0 X1 : G) : ¬(old X0 sk1 X1) ∨ c = sk1 ∨ ¬(old X0 X1 sk3) ∨ c = sk4 ∨ (old X0 sk4 sk1) := by
    clear * - eq512 old_1
    first | exact resolve eq512 old_1 | exact resolve old_1 eq512 | grind only
  have eq816 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq540 rule_def_7_1
    first | exact resolve eq540 rule_def_7_1 | exact resolve rule_def_7_1 eq540 | grind only
  have eq817 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq540 rule_def_7_0
    first | exact resolve eq540 rule_def_7_0 | exact resolve rule_def_7_0 eq540 | grind only
  have eq818 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq817 rule_def_6_0
    first | exact resolve eq817 rule_def_6_0 | exact resolve rule_def_6_0 eq817 | grind only
  have eq819 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq816 rule_def_6_1
    first | exact resolve eq816 rule_def_6_1 | exact resolve rule_def_6_1 eq816 | grind only
  have eq820 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ a = b := by
    clear * - eq818 rule_def_5_0
    first | exact resolve eq818 rule_def_5_0 | exact resolve rule_def_5_0 eq818 | grind only
  have eq821 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq819 rule_def_5_1
    first | exact resolve eq819 rule_def_5_1 | exact resolve rule_def_5_1 eq819 | grind only
  have eq888 : (sP6 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 ∨ c = sk0 := by
    clear * - eq569 rule_def_7_1
    first | exact resolve eq569 rule_def_7_1 | exact resolve rule_def_7_1 eq569 | grind only
  have eq891 : (sP5 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 ∨ c = sk0 := by
    clear * - eq888 rule_def_6_1
    first | exact resolve eq888 rule_def_6_1 | exact resolve rule_def_6_1 eq888 | grind only
  have eq893 : (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk3 ∨ c = sk0 := by
    clear * - eq891 rule_def_5_1
    first | exact resolve eq891 rule_def_5_1 | exact resolve rule_def_5_1 eq891 | grind only
  have eq912 : (sP6 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq600 rule_def_7_1
    first | exact resolve eq600 rule_def_7_1 | exact resolve rule_def_7_1 eq600 | grind only
  have eq913 : (sP6 sk3 sk1 sk4) ∨ (sP5 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 ∨ a = b := by
    clear * - eq600 rule_def_7_0
    first | exact resolve eq600 rule_def_7_0 | exact resolve rule_def_7_0 eq600 | grind only
  have eq914 : (sP5 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 ∨ a = b := by
    clear * - eq913 rule_def_6_0
    first | exact resolve eq913 rule_def_6_0 | exact resolve rule_def_6_0 eq913 | grind only
  have eq915 : (sP5 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq912 rule_def_6_1
    first | exact resolve eq912 rule_def_6_1 | exact resolve rule_def_6_1 eq912 | grind only
  have eq916 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 ∨ a = b := by
    clear * - eq914 rule_def_5_0
    first | exact resolve eq914 rule_def_5_0 | exact resolve rule_def_5_0 eq914 | grind only
  have eq917 : (old sk3 sk1 sk4) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq915 rule_def_5_1
    first | exact resolve eq915 rule_def_5_1 | exact resolve rule_def_5_1 eq915 | grind only
  have eq1012 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq478 rule_def_4_3
    first | exact resolve eq478 rule_def_4_3 | exact resolve rule_def_4_3 eq478 | grind only
  have eq1015 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ c = sk3 := by
    clear * - eq478 rule_def_4_0
    first | exact resolve eq478 rule_def_4_0 | exact resolve rule_def_4_0 eq478 | grind only
  have eq1016 : (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ c = sk3 := by
    clear * - eq1015 rule_def_2_0
    first | exact resolve eq1015 rule_def_2_0 | exact resolve rule_def_2_0 eq1015 | grind only
  have eq1017 : (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq1012 rule_def_2_3
    first | exact resolve eq1012 rule_def_2_3 | exact resolve rule_def_2_3 eq1012 | grind only
  have eq1018 : (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ c = sk3 := by
    clear * - eq1016 rule_def_3_0
    first | exact resolve eq1016 rule_def_3_0 | exact resolve rule_def_3_0 eq1016 | grind only
  have eq1019 : (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq1017 rule_def_3_3
    first | exact resolve eq1017 rule_def_3_3 | exact resolve rule_def_3_3 eq1017 | grind only
  have eq1102 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b ∨ (old b b a) := by
    clear * - eq597 rule_def_4_3
    first | exact resolve eq597 rule_def_4_3 | exact resolve rule_def_4_3 eq597 | grind only
  have eq1107 : (sP3 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b ∨ (old b b a) := by
    clear * - eq1102 rule_def_2_3
    first | exact resolve eq1102 rule_def_2_3 | exact resolve rule_def_2_3 eq1102 | grind only
  have eq1109 : (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ a = sk3 ∨ a = b ∨ (old b b a) := by
    clear * - eq1107 rule_def_3_3
    first | exact resolve eq1107 rule_def_3_3 | exact resolve rule_def_3_3 eq1107 | grind only
  have eq1126 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq252 rule_def_10_1
    first | exact resolve eq252 rule_def_10_1 | exact resolve rule_def_10_1 eq252 | grind only
  have eq1128 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1126 rule_def_2_0
    first | exact resolve eq1126 rule_def_2_0 | exact resolve rule_def_2_0 eq1126 | grind only
  have eq1129 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1128 rule_def_3_0
    first | exact resolve eq1128 rule_def_3_0 | exact resolve rule_def_3_0 eq1128 | grind only
  have eq1130 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1129 rule_def_4_0
    first | exact resolve eq1129 rule_def_4_0 | exact resolve rule_def_4_0 eq1129 | grind only
  have eq1131 : (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1130 rule_def_8_1
    first | exact resolve eq1130 rule_def_8_1 | exact resolve rule_def_8_1 eq1130 | grind only
  have eq1132 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1131 rule_def_9_1
    first | exact resolve eq1131 rule_def_9_1 | exact resolve rule_def_9_1 eq1131 | grind only
  have eq1195 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq445 rule_def_10_1
    first | exact resolve eq445 rule_def_10_1 | exact resolve rule_def_10_1 eq445 | grind only
  have eq1197 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1195 rule_def_2_0
    first | exact resolve eq1195 rule_def_2_0 | exact resolve rule_def_2_0 eq1195 | grind only
  have eq1198 : (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1197 rule_def_3_0
    first | exact resolve eq1197 rule_def_3_0 | exact resolve rule_def_3_0 eq1197 | grind only
  have eq1199 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1198 rule_def_4_0
    first | exact resolve eq1198 rule_def_4_0 | exact resolve rule_def_4_0 eq1198 | grind only
  have eq1200 : (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1199 rule_def_8_1
    first | exact resolve eq1199 rule_def_8_1 | exact resolve rule_def_8_1 eq1199 | grind only
  have eq1201 : (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1200 rule_def_9_1
    first | exact resolve eq1200 rule_def_9_1 | exact resolve rule_def_9_1 eq1200 | grind only
  have eq1218 : (sP2 sk3 sk1 sk4) ∨ (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq470 rule_def_10_1
    first | exact resolve eq470 rule_def_10_1 | exact resolve rule_def_10_1 eq470 | grind only
  have eq1220 : (sP3 sk3 sk1 sk4) ∨ (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq1218 rule_def_2_0
    first | exact resolve eq1218 rule_def_2_0 | exact resolve rule_def_2_0 eq1218 | grind only
  have eq1221 : (sP4 sk3 sk1 sk4) ∨ (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq1220 rule_def_3_0
    first | exact resolve eq1220 rule_def_3_0 | exact resolve rule_def_3_0 eq1220 | grind only
  have eq1222 : (sP8 sk3 sk1 sk4) ∨ (sP9 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq1221 rule_def_4_0
    first | exact resolve eq1221 rule_def_4_0 | exact resolve rule_def_4_0 eq1221 | grind only
  have eq1223 : (sP9 sk3 sk1 sk4) ∨ (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq1222 rule_def_8_1
    first | exact resolve eq1222 rule_def_8_1 | exact resolve rule_def_8_1 eq1222 | grind only
  have eq1224 : (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ b = sk3 ∨ c = sk3 := by
    clear * - eq1223 rule_def_9_1
    first | exact resolve eq1223 rule_def_9_1 | exact resolve rule_def_9_1 eq1223 | grind only
  have eq1290 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq548 rule_def_10_1
    first | exact resolve eq548 rule_def_10_1 | exact resolve rule_def_10_1 eq548 | grind only
  have eq1292 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1290 rule_def_2_0
    first | exact resolve eq1290 rule_def_2_0 | exact resolve rule_def_2_0 eq1290 | grind only
  have eq1293 : (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1292 rule_def_3_0
    first | exact resolve eq1292 rule_def_3_0 | exact resolve rule_def_3_0 eq1292 | grind only
  have eq1294 : (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1293 rule_def_4_0
    first | exact resolve eq1293 rule_def_4_0 | exact resolve rule_def_4_0 eq1293 | grind only
  have eq1295 : (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1294 rule_def_5_1
    first | exact resolve eq1294 rule_def_5_1 | exact resolve rule_def_5_1 eq1294 | grind only
  have eq1296 : (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1295 rule_def_6_1
    first | exact resolve eq1295 rule_def_6_1 | exact resolve rule_def_6_1 eq1295 | grind only
  have eq1297 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1296 rule_def_7_1
    first | exact resolve eq1296 rule_def_7_1 | exact resolve rule_def_7_1 eq1296 | grind only
  have eq1298 : (sP9 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1297 rule_def_8_1
    first | exact resolve eq1297 rule_def_8_1 | exact resolve rule_def_8_1 eq1297 | grind only
  have eq1299 : (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq1298 rule_def_9_1
    first | exact resolve eq1298 rule_def_9_1 | exact resolve rule_def_9_1 eq1298 | grind only
  have eq1745 : c = sk1 ∨ ¬(old sk0 sk2 sk3) ∨ b = sk1 ∨ (old sk0 sk4 sk1) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq573 eq269
    first | exact resolve eq573 eq269 | exact resolve eq269 eq573 | grind only
  have eq1748 : c = sk1 ∨ ¬(old sk0 sk2 sk3) ∨ b = sk1 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq573 eq401
    first | exact resolve eq573 eq401 | exact resolve eq401 eq573 | grind only
  have eq1770 : ¬(old sk0 sk2 sk3) ∨ c = sk1 ∨ b = sk1 ∨ (old sk0 sk4 sk1) := by
    clear * - eq1745
    first | exact resolve eq1745 rfl | grind only
  have eq1771 : (old sk0 sk4 sk1) ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq1748 eq431
    first | exact resolve eq1748 eq431 | exact resolve eq431 eq1748 | grind only
  have eq1806 : c = sk1 ∨ ¬(old sk0 sk2 sk3) ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq613 eq400
    first | exact resolve eq613 eq400 | exact resolve eq400 eq613 | grind only
  have eq1807 : c = sk1 ∨ ¬(old sk0 sk2 sk3) ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq613 eq401
    first | exact resolve eq613 eq401 | exact resolve eq401 eq613 | grind only
  have eq1809 : c = sk1 ∨ ¬(old sk0 sk2 sk3) ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq613 eq821
    first | exact resolve eq613 eq821 | exact resolve eq821 eq613 | grind only
  have eq1825 : ¬(old sk0 sk2 sk3) ∨ c = sk1 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq1809
    first | exact resolve eq1809 rfl | grind only
  have eq1827 : ¬(old sk0 sk2 sk3) ∨ c = sk1 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk2 := by
    clear * - eq1806
    first | exact resolve eq1806 rfl | grind only
  have eq1829 : (old sk0 sk4 sk1) ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq1807 eq431
    first | exact resolve eq1807 eq431 | exact resolve eq431 eq1807 | grind only
  have eq1875 : b = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk2 ∨ (new sk0 sk4 sk1) := by
    clear * - eq1771 imp_new_0
    first | exact resolve eq1771 imp_new_0 | exact resolve imp_new_0 eq1771 | grind only
  have eq1878 : c = sk2 ∨ c = sk1 ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq1875 preserve_3
    first | exact resolve eq1875 preserve_3 | exact resolve preserve_3 eq1875 | grind only
  have eq1900 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq269 eq1878
    first | exact Or.assoc3 (eq1878.imp_left (fun h : c = sk2 => superpose h eq269)) | exact superpose eq269 eq1878 | exact superpose eq1878 eq269 | grind only
  have eq1954 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 ∨ b = sk2 := by
    clear * - eq1900
    first | exact resolve eq1900 rfl | grind only
  have eq1991 : b = sk2 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq1954 p4XY
    first | exact resolve eq1954 p4XY | exact resolve p4XY eq1954 | grind only
  have eq2024 (X0 : G) : ¬(old X0 sk3 a) ∨ b = sk1 ∨ a = b ∨ (old b b a) ∨ ¬(old X0 b sk3) ∨ (old b b sk3) ∨ (old sk3 sk1 sk4) := by
    clear * - eq1019 eq359
    first | exact resolve eq1019 eq359 | exact resolve eq359 eq1019 | grind only
  have eq2049 : (old sk0 b sk3) ∨ c = sk3 ∨ c = b ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq462 eq1991
    first | exact Or.assoc3 (eq1991.imp_left (fun h : b = sk2 => superpose h eq462)) | exact superpose eq462 eq1991 | exact superpose eq1991 eq462 | grind only
  have eq2084 : ¬(old sk0 b sk3) ∨ c = sk1 ∨ b = sk1 ∨ (old sk0 sk4 sk1) ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq1770 eq1991
    first | exact Or.assoc4 (eq1991.imp_left (fun h : b = sk2 => superpose h eq1770)) | exact superpose eq1770 eq1991 | exact superpose eq1991 eq1770 | grind only
  have eq2085 : ¬(old sk0 b sk3) ∨ c = sk1 ∨ b = sk1 ∨ (old sk0 sk4 sk1) := by
    clear * - eq2084
    first | exact resolve eq2084 rfl | grind only
  have eq2116 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq2049 bc
    first | exact resolve eq2049 bc | exact resolve bc eq2049 | grind only
  have eq2195 : (new sk3 c b) ∨ a = sk3 ∨ a = b ∨ (old b b a) ∨ (old sk3 sk1 sk4) := by
    clear * - eq1109 eq219
    first | exact resolve eq1109 eq219 | exact resolve eq219 eq1109 | grind only
  have eq2288 : c = sk1 ∨ b = sk1 ∨ (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq2085 eq2116
    first | exact resolve eq2085 eq2116 | exact resolve eq2116 eq2085 | grind only
  have eq2289 : (old sk0 sk4 sk1) ∨ b = sk1 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq2288
    first | exact resolve eq2288 rfl | grind only
  have eq2297 : b = sk1 ∨ c = sk1 ∨ c = sk3 ∨ (new sk0 sk4 sk1) := by
    clear * - eq2289 imp_new_0
    first | exact resolve eq2289 imp_new_0 | exact resolve imp_new_0 eq2289 | grind only
  have eq2301 : c = sk3 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq2297 preserve_3
    first | exact resolve eq2297 preserve_3 | exact resolve preserve_3 eq2297 | grind only
  have eq2318 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq487 eq2301
    first | exact Or.assoc3 (eq2301.imp_left (fun h : c = sk3 => superpose h eq487)) | exact superpose eq487 eq2301 | exact superpose eq2301 eq487 | grind only
  have eq2389 : (old c sk1 sk4) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq2318
    first | exact resolve eq2318 rfl | grind only
  have eq2422 : c = sk1 ∨ b = sk1 := by
    clear * - eq2389 p4YZ
    first | exact resolve eq2389 p4YZ | exact resolve p4YZ eq2389 | grind only
  have eq2447 : ¬(new sk0 sk4 c) ∨ b = sk1 := by
    clear * - preserve_3 eq2422
    first | exact (eq2422.imp_left (fun h : c = sk1 => superpose h preserve_3)) | exact superpose preserve_3 eq2422 | exact superpose eq2422 preserve_3 | grind only
  have eq2457 : (old sk0 c sk2) ∨ c = b ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq270 eq2422
    first | exact Or.assoc3 (eq2422.imp_left (fun h : c = sk1 => superpose h eq270)) | exact superpose eq270 eq2422 | exact superpose eq2422 eq270 | grind only
  have eq2465 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ c = b ∨ a = b ∨ (old b b a) ∨ b = sk1 := by
    clear * - eq348 eq2422
    first | exact Or.assoc5 (eq2422.imp_left (fun h : c = sk1 => superpose h eq348)) | exact superpose eq348 eq2422 | exact superpose eq2422 eq348 | grind only
  have eq2474 : (old sk3 c sk4) ∨ c = b ∨ b = sk4 ∨ b = sk1 := by
    clear * - eq488 eq2422
    first | exact Or.assoc3 (eq2422.imp_left (fun h : c = sk1 => superpose h eq488)) | exact superpose eq488 eq2422 | exact superpose eq2422 eq488 | grind only
  have eq2497 : (sP1 sk3 c sk4) ∨ (old sk3 c sk4) ∨ c = b ∨ a = b ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq1018 eq2422
    first | exact Or.assoc5 (eq2422.imp_left (fun h : c = sk1 => superpose h eq1018)) | exact superpose eq1018 eq2422 | exact superpose eq2422 eq1018 | grind only
  have eq2507 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ c = b ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq1132 eq2422
    first | exact Or.assoc5 (eq2422.imp_left (fun h : c = sk1 => superpose h eq1132)) | exact superpose eq1132 eq2422 | exact superpose eq2422 eq1132 | grind only
  have eq2509 : (sP1 sk3 c sk4) ∨ (old sk3 c sk4) ∨ c = b ∨ b = sk3 ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq1224 eq2422
    first | exact Or.assoc5 (eq2422.imp_left (fun h : c = sk1 => superpose h eq1224)) | exact superpose eq1224 eq2422 | exact superpose eq2422 eq1224 | grind only
  have eq2517 : (sP1 sk3 c sk4) ∨ c = b ∨ b = sk3 ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq2509 p4XZ
    first | exact resolve eq2509 p4XZ | exact resolve p4XZ eq2509 | grind only
  have eq2519 : (sP1 sk0 c sk2) ∨ c = b ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq2507 p4XZ
    first | exact resolve eq2507 p4XZ | exact resolve p4XZ eq2507 | grind only
  have eq2527 : (sP1 sk3 c sk4) ∨ c = b ∨ a = b ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq2497 p4XZ
    first | exact resolve eq2497 p4XZ | exact resolve p4XZ eq2497 | grind only
  have eq2543 : c = b ∨ b = sk4 ∨ b = sk1 := by
    clear * - eq2474 p4XZ
    first | exact resolve eq2474 p4XZ | exact resolve p4XZ eq2474 | grind only
  have eq2549 : (sP1 sk0 c sk2) ∨ c = b ∨ a = b ∨ (old b b a) ∨ b = sk1 := by
    clear * - eq2465 p4XZ
    first | exact resolve eq2465 p4XZ | exact resolve p4XZ eq2465 | grind only
  have eq2554 : c = b ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq2457 p4XZ
    first | exact resolve eq2457 p4XZ | exact resolve p4XZ eq2457 | grind only
  have eq2562 : (sP1 sk3 c sk4) ∨ b = sk3 ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq2517 bc
    first | exact resolve eq2517 bc | exact resolve bc eq2517 | grind only
  have eq2563 : (sP1 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq2519 bc
    first | exact resolve eq2519 bc | exact resolve bc eq2519 | grind only
  have eq2565 : (sP1 sk3 c sk4) ∨ a = b ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq2527 bc
    first | exact resolve eq2527 bc | exact resolve bc eq2527 | grind only
  have eq2566 : b = sk4 ∨ b = sk1 := by
    clear * - eq2543 bc
    first | exact resolve eq2543 bc | exact resolve bc eq2543 | grind only
  have eq2569 : (sP1 sk0 c sk2) ∨ a = b ∨ (old b b a) ∨ b = sk1 := by
    clear * - eq2549 bc
    first | exact resolve eq2549 bc | exact resolve bc eq2549 | grind only
  have eq2572 : b = sk2 ∨ b = sk1 := by
    clear * - eq2554 bc
    first | exact resolve eq2554 bc | exact resolve bc eq2554 | grind only
  have eq2644 : (new sk0 b sk3) ∨ b = sk1 := by
    clear * - preserve_1 eq2572
    first | exact (eq2572.imp_left (fun h : b = sk2 => superpose h preserve_1)) | exact superpose preserve_1 eq2572 | exact superpose eq2572 preserve_1 | grind only
  have eq2645 (X0 : G) : ¬(new sk0 b X0) ∨ sk3 = X0 ∨ b = sk1 := by
    clear * - eq212 eq2572
    first | exact Or.assoc2 (eq2572.imp_left (fun h : b = sk2 => superpose h eq212)) | exact superpose eq212 eq2572 | exact superpose eq2572 eq212 | grind only
  have eq2664 : (old sk0 b sk3) ∨ c = sk3 ∨ c = b ∨ b = sk1 := by
    clear * - eq462 eq2572
    first | exact Or.assoc3 (eq2572.imp_left (fun h : b = sk2 => superpose h eq462)) | exact superpose eq462 eq2572 | exact superpose eq2572 eq462 | grind only
  have eq2726 : (old sk0 b sk3) ∨ c = sk3 ∨ b = sk1 := by
    clear * - eq2664 bc
    first | exact resolve eq2664 bc | exact resolve bc eq2664 | grind only
  have eq2771 : ¬(new sk0 b c) ∨ b = sk1 ∨ b = sk1 := by
    clear * - eq2447 eq2566
    first | exact Or.assoc2 (eq2566.imp_left (fun h : b = sk4 => superpose h eq2447)) | exact superpose eq2447 eq2566 | exact superpose eq2566 eq2447 | grind only
  have eq2772 : ¬(new sk0 b c) ∨ b = sk1 := by
    clear * - eq2771
    first | exact resolve eq2771 rfl | grind only
  have eq3155 (X0 X1 : G) : ¬(sP1 sk0 X0 X1) ∨ b = sk1 ∨ sk3 = (sF0 sk0 X0 X1) := by
    clear * - eq2645 eq201
    first | exact resolve eq2645 eq201 | exact resolve eq201 eq2645 | grind only
  have eq3668 (X0 : G) : ¬(old X0 sk3 a) ∨ c = sk3 ∨ b = sk1 ∨ ¬(old X0 b sk3) ∨ (old b b sk3) ∨ b = sk3 := by
    clear * - eq2562 eq359
    first | exact resolve eq2562 eq359 | exact resolve eq359 eq2562 | grind only
  have eq3693 : c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ b = sk2 ∨ (new sk0 sk4 sk1) := by
    clear * - eq1829 imp_new_0
    first | exact resolve eq1829 imp_new_0 | exact resolve imp_new_0 eq1829 | grind only
  have eq3703 : c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq3693 preserve_3
    first | exact resolve eq3693 preserve_3 | exact resolve preserve_3 eq3693 | grind only
  have eq3709 : ¬(new sk0 c sk1) ∨ c = sk1 ∨ c = sk2 ∨ b = sk2 := by
    clear * - preserve_3 eq3703
    first | exact (eq3703.imp_left (fun h : c = sk4 => superpose h preserve_3)) | exact superpose preserve_3 eq3703 | exact superpose eq3703 preserve_3 | grind only
  have eq3947 : (sP1 sk0 c b) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk1 := by
    clear * - eq2563 eq2572
    first | exact Or.assoc4 (eq2572.imp_left (fun h : b = sk2 => superpose h eq2563)) | exact superpose eq2563 eq2572 | exact superpose eq2572 eq2563 | grind only
  have eq3952 : (sP1 sk0 c b) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq3947
    first | exact resolve eq3947 rfl | grind only
  have eq3974 (X0 : G) : ¬(old sk3 b X0) ∨ c = sk3 ∨ b = sk1 ∨ a = b ∨ (sF0 sk3 c sk4) = X0 := by
    clear * - eq2565 eq200
    first | exact resolve eq2565 eq200 | exact resolve eq200 eq2565 | grind only
  have eq4229 : b = sk1 ∨ sk3 = (sF0 sk0 c b) ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq3155 eq3952
    first | exact resolve eq3155 eq3952 | exact resolve eq3952 eq3155 | grind only
  have eq4230 : sk3 = (sF0 sk0 c b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq4229
    first | exact resolve eq4229 rfl | grind only
  have eq4242 : c = sk1 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq1827 eq462
    first | exact resolve eq1827 eq462 | exact resolve eq462 eq1827 | grind only
  have eq4257 : (old sk0 sk4 sk1) ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq4242
    first | exact resolve eq4242 rfl | grind only
  have eq4308 : a = b ∨ (old b b a) ∨ b = sk1 ∨ b = sk1 ∨ sk3 = (sF0 sk0 c sk2) := by
    clear * - eq2569 eq3155
    first | exact resolve eq2569 eq3155 | exact resolve eq3155 eq2569 | grind only
  have eq4331 : (old b b a) ∨ a = b ∨ b = sk1 ∨ sk3 = (sF0 sk0 c sk2) := by
    clear * - eq4308
    first | exact resolve eq4308 rfl | grind only
  have eq5765 : (old sk0 sk3 a) ∨ ¬(sP1 sk0 c b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - rule_def_1_3 eq4230
    first | exact Or.assoc2 (eq4230.imp_left (fun h : sk3 = (sF0 sk0 c b) => superpose h rule_def_1_3)) | exact superpose rule_def_1_3 eq4230 | exact superpose eq4230 rule_def_1_3 | grind only
  have eq5785 : (old sk0 sk3 a) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq5765 eq3952
    first | exact resolve eq5765 eq3952 | exact resolve eq3952 eq5765 | grind only
  have eq6249 : c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ (new sk0 sk4 sk1) := by
    clear * - eq4257 imp_new_0
    first | exact resolve eq4257 imp_new_0 | exact resolve imp_new_0 eq4257 | grind only
  have eq6263 : c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq6249 preserve_3
    first | exact resolve eq6249 preserve_3 | exact resolve preserve_3 eq6249 | grind only
  have eq6303 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq917 eq6263
    first | exact Or.assoc4 (eq6263.imp_left (fun h : c = sk4 => superpose h eq917)) | exact superpose eq917 eq6263 | exact superpose eq6263 eq917 | grind only
  have eq6364 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq6303
    first | exact resolve eq6303 rfl | grind only
  have eq6378 : a = sk3 ∨ c = sk1 ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq6364 p4XY
    first | exact resolve eq6364 p4XY | exact resolve p4XY eq6364 | grind only
  have eq6409 : c = sk1 ∨ c = sk4 ∨ (old sk0 sk4 sk1) ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk3 ∨ c = sk0 := by
    clear * - eq1825 eq893
    first | exact resolve eq1825 eq893 | exact resolve eq893 eq1825 | grind only
  have eq6436 : (old sk0 sk4 sk1) ∨ c = sk4 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq6409
    first | exact resolve eq6409 rfl | grind only
  have eq6441 : (new a sk1 sk4) ∨ c = sk1 ∨ c = sk3 ∨ c = sk2 := by
    clear * - preserve_2 eq6378
    first | exact (eq6378.imp_left (fun h : a = sk3 => superpose h preserve_2)) | exact superpose preserve_2 eq6378 | exact superpose eq6378 preserve_2 | grind only
  have eq8439 : a = b ∨ b = sk1 ∨ sk3 = (sF0 sk0 c sk2) ∨ (old a b a) := by
    clear * - eq4331 old_4
    first | exact resolve eq4331 old_4 | exact resolve old_4 eq4331 | grind only
  have eq8444 : sk3 = (sF0 sk0 c sk2) ∨ b = sk1 ∨ a = b := by
    clear * - eq8439 p3
    first | exact resolve eq8439 p3 | exact resolve p3 eq8439 | grind only
  have eq8458 : ¬(sP1 sk0 c sk2) ∨ (old sk0 b sk3) ∨ b = sk1 ∨ a = b := by
    clear * - rule_def_1_2 eq8444
    first | exact Or.assoc2 (eq8444.imp_left (fun h : sk3 = (sF0 sk0 c sk2) => superpose h rule_def_1_2)) | exact superpose rule_def_1_2 eq8444 | exact superpose eq8444 rule_def_1_2 | grind only
  have eq8459 : ¬(sP1 sk0 c sk2) ∨ (old sk0 sk3 a) ∨ b = sk1 ∨ a = b := by
    clear * - rule_def_1_3 eq8444
    first | exact Or.assoc2 (eq8444.imp_left (fun h : sk3 = (sF0 sk0 c sk2) => superpose h rule_def_1_3)) | exact superpose rule_def_1_3 eq8444 | exact superpose eq8444 rule_def_1_3 | grind only
  have eq8514 : (old sk0 b sk3) ∨ b = sk1 ∨ a = b ∨ a = b ∨ (old b b a) ∨ b = sk1 := by
    clear * - eq8458 eq2569
    first | exact resolve eq8458 eq2569 | exact resolve eq2569 eq8458 | grind only
  have eq8537 : (old sk0 b sk3) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq8514
    first | exact resolve eq8514 rfl | grind only
  have eq8580 : (old sk0 sk3 a) ∨ b = sk1 ∨ a = b ∨ a = b ∨ (old b b a) ∨ b = sk1 := by
    clear * - eq8459 eq2569
    first | exact resolve eq8459 eq2569 | exact resolve eq2569 eq8459 | grind only
  have eq8603 : (old sk0 sk3 a) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq8580
    first | exact resolve eq8580 rfl | grind only
  have eq11090 : b = sk1 ∨ a = b ∨ (old b b a) ∨ ¬(old sk0 b sk3) ∨ (old b b sk3) ∨ (old sk3 sk1 sk4) ∨ b = sk1 ∨ a = b ∨ (old b b a) := by
    clear * - eq2024 eq8603
    first | exact resolve eq2024 eq8603 | exact resolve eq8603 eq2024 | grind only
  have eq11109 : b = sk1 ∨ a = b ∨ (old b b a) ∨ ¬(old sk0 b sk3) ∨ (old b b sk3) ∨ (old sk3 sk1 sk4) := by
    clear * - eq11090
    first | exact resolve eq11090 rfl | grind only
  have eq11112 : (old sk3 sk1 sk4) ∨ a = b ∨ (old b b a) ∨ (old b b sk3) ∨ b = sk1 := by
    clear * - eq11109 eq8537
    first | exact resolve eq11109 eq8537 | exact resolve eq8537 eq11109 | grind only
  have eq11337 : (old sk3 c sk4) ∨ a = b ∨ (old b b a) ∨ (old b b sk3) ∨ c = b ∨ b = sk1 := by
    clear * - eq11112 eq2422
    first | exact Or.assoc5 (eq2422.imp_left (fun h : c = sk1 => superpose h eq11112)) | exact superpose eq11112 eq2422 | exact superpose eq2422 eq11112 | grind only
  have eq11378 : a = b ∨ (old b b a) ∨ (old b b sk3) ∨ c = b ∨ b = sk1 := by
    clear * - eq11337 p4XZ
    first | exact resolve eq11337 p4XZ | exact resolve p4XZ eq11337 | grind only
  have eq11379 : (old b b sk3) ∨ (old b b a) ∨ a = b ∨ b = sk1 := by
    clear * - eq11378 bc
    first | exact resolve eq11378 bc | exact resolve bc eq11378 | grind only
  have eq11384 : (old sk3 sk3 b) ∨ a = b ∨ b = sk1 ∨ (old b b a) := by
    clear * - eq11379 old_5
    first | exact resolve eq11379 old_5 | exact resolve old_5 eq11379 | grind only
  have eq11385 : (old sk3 b sk3) ∨ a = b ∨ b = sk1 ∨ (old b b a) := by
    clear * - eq11379 old_4
    first | exact resolve eq11379 old_4 | exact resolve old_4 eq11379 | grind only
  have eq11448 : (new sk3 sk3 b) ∨ b = sk1 ∨ (old b b a) ∨ a = b := by
    clear * - eq11384 imp_new_0
    first | exact resolve eq11384 imp_new_0 | exact resolve imp_new_0 eq11384 | grind only
  have eq11541 (X0 : G) : ¬(new sk3 sk3 X0) ∨ (old b b a) ∨ a = b ∨ b = sk1 ∨ b = X0 := by
    clear * - eq11448 prev_0
    first | exact resolve eq11448 prev_0 | exact resolve prev_0 eq11448 | grind only
  have eq13922 : c = sk4 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 ∨ (new sk0 sk4 sk1) := by
    clear * - eq6436 imp_new_0
    first | exact resolve eq6436 imp_new_0 | exact resolve imp_new_0 eq6436 | grind only
  have eq13940 : c = sk4 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq13922 preserve_3
    first | exact resolve eq13922 preserve_3 | exact resolve preserve_3 eq13922 | grind only
  have eq14001 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq917 eq13940
    first | exact Or.assoc4 (eq13940.imp_left (fun h : c = sk4 => superpose h eq917)) | exact superpose eq917 eq13940 | exact superpose eq13940 eq917 | grind only
  have eq14090 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk1 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq14001
    first | exact resolve eq14001 rfl | grind only
  have eq14103 : a = sk3 ∨ c = sk1 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq14090 p4XY
    first | exact resolve eq14090 p4XY | exact resolve p4XY eq14090 | grind only
  have eq14276 : (old sk0 sk2 a) ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq893 eq14103
    first | exact Or.assoc4 (eq14103.imp_left (fun h : a = sk3 => superpose h eq893)) | exact superpose eq893 eq14103 | exact superpose eq14103 eq893 | grind only
  have eq14452 : a ≠ b ∨ c = sk1 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq14103
    grind only
  have eq14535 : (old sk0 sk2 a) ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq14276
    first | exact resolve eq14276 rfl | grind only
  have eq14578 : (old sk0 sk2 a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq14535 eq14452
    first | exact resolve eq14535 eq14452 | exact resolve eq14452 eq14535 | grind only
  have eq18957 : c = sk3 ∨ b = sk1 ∨ a = b ∨ sk3 = (sF0 sk3 c sk4) ∨ a = b ∨ b = sk1 ∨ (old b b a) := by
    clear * - eq3974 eq11385
    first | exact resolve eq3974 eq11385 | exact resolve eq11385 eq3974 | grind only
  have eq18978 : (old b b a) ∨ b = sk1 ∨ a = b ∨ sk3 = (sF0 sk3 c sk4) ∨ c = sk3 := by
    clear * - eq18957
    first | exact resolve eq18957 rfl | grind only
  have eq20055 : b = sk1 ∨ a = b ∨ sk3 = (sF0 sk3 c sk4) ∨ c = sk3 ∨ (old a b a) := by
    clear * - eq18978 old_4
    first | exact resolve eq18978 old_4 | exact resolve old_4 eq18978 | grind only
  have eq20086 : sk3 = (sF0 sk3 c sk4) ∨ a = b ∨ b = sk1 ∨ c = sk3 := by
    clear * - eq20055 p3
    first | exact resolve eq20055 p3 | exact resolve p3 eq20055 | grind only
  have eq20154 : (new sk3 sk3 a) ∨ ¬(sP1 sk3 c sk4) ∨ a = b ∨ b = sk1 ∨ c = sk3 := by
    clear * - eq209 eq20086
    first | exact Or.assoc2 (eq20086.imp_left (fun h : sk3 = (sF0 sk3 c sk4) => superpose h eq209)) | exact superpose eq209 eq20086 | exact superpose eq20086 eq209 | grind only
  have eq20187 : (new sk3 sk3 a) ∨ a = b ∨ b = sk1 ∨ c = sk3 := by
    clear * - eq20154 eq2565
    first | exact resolve eq20154 eq2565 | exact resolve eq2565 eq20154 | grind only
  have eq20199 : a = b ∨ b = sk1 ∨ c = sk3 ∨ (old b b a) ∨ a = b ∨ b = sk1 ∨ a = b := by
    clear * - eq20187 eq11541
    first | exact resolve eq20187 eq11541 | exact resolve eq11541 eq20187 | grind only
  have eq20221 : (old b b a) ∨ b = sk1 ∨ c = sk3 ∨ a = b := by
    clear * - eq20199
    first | exact resolve eq20199 rfl | grind only
  have eq20540 : b = sk1 ∨ c = sk3 ∨ a = b ∨ (old a b a) := by
    clear * - eq20221 old_4
    first | exact resolve eq20221 old_4 | exact resolve old_4 eq20221 | grind only
  have eq20571 : c = sk3 ∨ b = sk1 ∨ a = b := by
    clear * - eq20540 p3
    first | exact resolve eq20540 p3 | exact resolve p3 eq20540 | grind only
  have eq20738 : (new sk0 b c) ∨ b = sk1 ∨ b = sk1 ∨ a = b := by
    clear * - eq2644 eq20571
    first | exact Or.assoc2 (eq20571.imp_left (fun h : c = sk3 => superpose h eq2644)) | exact superpose eq2644 eq20571 | exact superpose eq20571 eq2644 | grind only
  have eq20887 : (new sk0 b c) ∨ b = sk1 ∨ a = b := by
    clear * - eq20738
    first | exact resolve eq20738 rfl | grind only
  have eq21014 : b = sk1 ∨ a = b := by
    clear * - eq20887 eq2772
    first | exact resolve eq20887 eq2772 | exact resolve eq2772 eq20887 | grind only
  have eq21099 (X0 : G) : ¬(new sk0 b X0) ∨ sk2 = X0 ∨ a = b := by
    clear * - eq211 eq21014
    first | exact Or.assoc2 (eq21014.imp_left (fun h : b = sk1 => superpose h eq211)) | exact superpose eq211 eq21014 | exact superpose eq21014 eq211 | grind only
  have eq21109 : (old sk0 b sk2) ∨ c = sk2 ∨ c = b ∨ a = b := by
    clear * - eq400 eq21014
    first | exact Or.assoc3 (eq21014.imp_left (fun h : b = sk1 => superpose h eq400)) | exact superpose eq400 eq21014 | exact superpose eq21014 eq400 | grind only
  have eq21110 : (old sk0 b sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = b := by
    clear * - eq401 eq21014
    first | exact Or.assoc3 (eq21014.imp_left (fun h : b = sk1 => superpose h eq401)) | exact superpose eq401 eq21014 | exact superpose eq21014 eq401 | grind only
  have eq21135 : (old sk0 b sk2) ∨ a = sk0 ∨ c = b ∨ a = b ∨ a = b := by
    clear * - eq820 eq21014
    first | exact Or.assoc4 (eq21014.imp_left (fun h : b = sk1 => superpose h eq820)) | exact superpose eq820 eq21014 | exact superpose eq21014 eq820 | grind only
  have eq21151 : (old sk3 b sk4) ∨ a = sk3 ∨ c = b ∨ a = b ∨ a = b := by
    clear * - eq916 eq21014
    first | exact Or.assoc4 (eq21014.imp_left (fun h : b = sk1 => superpose h eq916)) | exact superpose eq916 eq21014 | exact superpose eq21014 eq916 | grind only
  have eq21192 : ¬(new sk0 c b) ∨ c = b ∨ c = sk2 ∨ b = sk2 ∨ a = b := by
    clear * - eq3709 eq21014
    first | exact Or.assoc4 (eq21014.imp_left (fun h : b = sk1 => superpose h eq3709)) | exact superpose eq3709 eq21014 | exact superpose eq21014 eq3709 | grind only
  have eq21217 : (new a b sk4) ∨ c = b ∨ c = sk3 ∨ c = sk2 ∨ a = b := by
    clear * - eq6441 eq21014
    first | exact Or.assoc4 (eq21014.imp_left (fun h : b = sk1 => superpose h eq6441)) | exact superpose eq6441 eq21014 | exact superpose eq21014 eq6441 | grind only
  have eq21314 : (old sk3 b sk4) ∨ a = sk3 ∨ c = b ∨ a = b := by
    clear * - eq21151
    first | exact resolve eq21151 rfl | grind only
  have eq21322 : (old sk0 b sk2) ∨ a = sk0 ∨ c = b ∨ a = b := by
    clear * - eq21135
    first | exact resolve eq21135 rfl | grind only
  have eq21358 : (new a b sk4) ∨ c = sk3 ∨ c = sk2 ∨ a = b := by
    clear * - eq21217 bc
    first | exact resolve eq21217 bc | exact resolve bc eq21217 | grind only
  have eq21372 : ¬(new sk0 c b) ∨ c = sk2 ∨ b = sk2 ∨ a = b := by
    clear * - eq21192 bc
    first | exact resolve eq21192 bc | exact resolve bc eq21192 | grind only
  have eq21387 : (old sk3 b sk4) ∨ a = sk3 ∨ a = b := by
    clear * - eq21314 bc
    first | exact resolve eq21314 bc | exact resolve bc eq21314 | grind only
  have eq21395 : (old sk0 b sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq21322 bc
    first | exact resolve eq21322 bc | exact resolve bc eq21322 | grind only
  have eq21405 : (old sk0 b sk2) ∨ c = sk2 ∨ a = b := by
    clear * - eq21109 bc
    first | exact resolve eq21109 bc | exact resolve bc eq21109 | grind only
  have eq23864 : c = sk2 ∨ b = sk2 ∨ a = b ∨ ¬(old sk0 sk2 a) ∨ (new sk0 c b) := by
    clear * - eq21110 eq169
    first | exact resolve eq21110 eq169 | exact resolve eq169 eq21110 | grind only
  have eq23944 : ¬(old sk0 sk2 a) ∨ b = sk2 ∨ a = b ∨ c = sk2 := by
    clear * - eq23864 eq21372
    first | exact resolve eq23864 eq21372 | exact resolve eq21372 eq23864 | grind only
  have eq26613 : c = sk4 ∨ c = sk2 ∨ a = b ∨ c = sk3 := by
    clear * - eq21358 eq214
    first | exact resolve eq21358 eq214 | exact resolve eq214 eq21358 | grind only
  have eq26766 : (old sk3 b c) ∨ a = sk3 ∨ a = b ∨ c = sk2 ∨ a = b ∨ c = sk3 := by
    clear * - eq21387 eq26613
    first | exact Or.assoc3 (eq26613.imp_left (fun h : c = sk4 => superpose h eq21387)) | exact superpose eq21387 eq26613 | exact superpose eq26613 eq21387 | grind only
  have eq26767 : (old sk3 b c) ∨ a = sk3 ∨ a = b ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq26766
    first | exact resolve eq26766 rfl | grind only
  have eq26848 : a = sk3 ∨ a = b ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq26767 p4XY
    first | exact resolve eq26767 p4XY | exact resolve p4XY eq26767 | grind only
  have eq26894 : (old sk0 sk2 a) ∨ b = sk2 ∨ a = b ∨ a = b ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq432 eq26848
    first | exact Or.assoc3 (eq26848.imp_left (fun h : a = sk3 => superpose h eq432)) | exact superpose eq432 eq26848 | exact superpose eq26848 eq432 | grind only
  have eq27372 : (old sk0 sk2 a) ∨ b = sk2 ∨ a = b ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq26894
    first | exact resolve eq26894 rfl | grind only
  have eq27394 : c = sk3 ∨ a = b ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq27372 eq23944
    first | exact resolve eq27372 eq23944 | exact resolve eq23944 eq27372 | grind only
  have eq27481 : (old sk0 sk2 c) ∨ b = sk2 ∨ c = sk2 ∨ a = b ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq431 eq27394
    first | exact Or.assoc3 (eq27394.imp_left (fun h : c = sk3 => superpose h eq431)) | exact superpose eq431 eq27394 | exact superpose eq27394 eq431 | grind only
  have eq27882 : (old sk0 sk2 c) ∨ b = sk2 ∨ c = sk2 ∨ a = b := by
    clear * - eq27481
    first | exact resolve eq27481 rfl | grind only
  have eq27956 : c = sk2 ∨ b = sk2 ∨ a = b := by
    clear * - eq27882 p4XY
    first | exact resolve eq27882 p4XY | exact resolve p4XY eq27882 | grind only
  have eq28145 : (old sk0 b c) ∨ a = sk0 ∨ a = b ∨ b = sk2 ∨ a = b := by
    clear * - eq21395 eq27956
    first | exact Or.assoc3 (eq27956.imp_left (fun h : c = sk2 => superpose h eq21395)) | exact superpose eq21395 eq27956 | exact superpose eq27956 eq21395 | grind only
  have eq28147 : (old sk0 b c) ∨ a = sk0 ∨ a = b ∨ b = sk2 := by
    clear * - eq28145
    first | exact resolve eq28145 rfl | grind only
  have eq28211 : b = sk2 ∨ a = b ∨ a = sk0 := by
    clear * - eq28147 p4XY
    first | exact resolve eq28147 p4XY | exact resolve p4XY eq28147 | grind only
  have eq28304 : (new sk0 b sk3) ∨ a = b ∨ a = sk0 := by
    clear * - preserve_1 eq28211
    first | exact (eq28211.imp_left (fun h : b = sk2 => superpose h preserve_1)) | exact superpose preserve_1 eq28211 | exact superpose eq28211 preserve_1 | grind only
  have eq29651 : a = b ∨ a = sk0 ∨ sk2 = sk3 ∨ a = b := by
    clear * - eq28304 eq21099
    first | exact resolve eq28304 eq21099 | exact resolve eq21099 eq28304 | grind only
  have eq29688 : sk2 = sk3 ∨ a = sk0 ∨ a = b := by
    clear * - eq29651
    first | exact resolve eq29651 rfl | grind only
  have eq30201 : a = sk2 ∨ a = b ∨ c = sk2 ∨ c = sk2 ∨ a = sk0 ∨ a = b := by
    clear * - eq26848 eq29688
    first | exact Or.assoc4 (eq29688.imp_left (fun h : sk2 = sk3 => superpose h eq26848)) | exact superpose eq26848 eq29688 | exact superpose eq29688 eq26848 | grind only
  have eq30210 : a = sk2 ∨ a = b ∨ c = sk2 ∨ a = sk0 := by
    clear * - eq30201
    first | exact resolve eq30201 rfl | grind only
  have eq34926 : a = b ∨ a = b ∨ c = b ∨ a = sk0 ∨ a = b ∨ a = sk0 := by
    clear * - eq30210 eq28211
    first | exact Or.assoc4 (eq28211.imp_left (fun h : b = sk2 => superpose h eq30210)) | exact superpose eq30210 eq28211 | exact superpose eq28211 eq30210 | grind only
  have eq35295 : a = b ∨ c = b ∨ a = sk0 := by
    clear * - eq34926
    first | exact resolve eq34926 rfl | grind only
  have eq35304 : a = sk0 ∨ a = b := by
    clear * - eq35295 bc
    first | exact resolve eq35295 bc | exact resolve bc eq35295 | grind only
  have eq35425 : (sP1 a sk2 sk3) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ a = b ∨ a = c ∨ a = b := by
    clear * - eq1201 eq35304
    first | exact Or.assoc5 (eq35304.imp_left (fun h : a = sk0 => superpose h eq1201)) | exact superpose eq1201 eq35304 | exact superpose eq35304 eq1201 | grind only
  have eq35705 : (old a b sk2) ∨ c = sk2 ∨ a = b ∨ a = b := by
    clear * - eq21405 eq35304
    first | exact Or.assoc3 (eq35304.imp_left (fun h : a = sk0 => superpose h eq21405)) | exact superpose eq21405 eq35304 | exact superpose eq35304 eq21405 | grind only
  have eq35716 : (old a b sk2) ∨ c = sk2 ∨ a = b := by
    clear * - eq35705
    first | exact resolve eq35705 rfl | grind only
  have eq35911 : (sP1 a sk2 sk3) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ a = b ∨ a = c := by
    clear * - eq35425
    first | exact resolve eq35425 rfl | grind only
  have eq35943 : c = sk2 ∨ a = b := by
    clear * - eq35716 p3
    first | exact resolve eq35716 p3 | exact resolve p3 eq35716 | grind only
  have eq35991 : (old a sk2 sk3) ∨ c = sk3 ∨ a = b ∨ a = c := by
    clear * - eq35911 eq205
    first | exact resolve eq35911 eq205 | exact resolve eq205 eq35911 | grind only
  have eq36017 : (old a sk2 sk3) ∨ c = sk3 ∨ a = b := by
    clear * - eq35991 ac
    first | exact resolve eq35991 ac | exact resolve ac eq35991 | grind only
  have eq36103 : (old sk0 c sk3) ∨ c = b ∨ b = sk3 ∨ a = b := by
    clear * - eq432 eq35943
    first | exact Or.assoc3 (eq35943.imp_left (fun h : c = sk2 => superpose h eq432)) | exact superpose eq432 eq35943 | exact superpose eq35943 eq432 | grind only
  have eq36207 : (old sk0 c a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 ∨ a = b := by
    clear * - eq14578 eq35943
    first | exact Or.assoc6 (eq35943.imp_left (fun h : c = sk2 => superpose h eq14578)) | exact superpose eq14578 eq35943 | exact superpose eq35943 eq14578 | grind only
  have eq36299 : (old sk0 c a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq36207 eq14452
    first | exact resolve eq36207 eq14452 | exact resolve eq14452 eq36207 | grind only
  have eq36310 : c = b ∨ b = sk3 ∨ a = b := by
    clear * - eq36103 p4XZ
    first | exact resolve eq36103 p4XZ | exact resolve p4XZ eq36103 | grind only
  have eq36317 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq36299 p4XZ
    first | exact resolve eq36299 p4XZ | exact resolve p4XZ eq36299 | grind only
  have eq36321 : b = sk3 ∨ a = b := by
    clear * - eq36310 bc
    first | exact resolve eq36310 bc | exact resolve bc eq36310 | grind only
  have eq41442 : (old a c sk3) ∨ c = sk3 ∨ a = b ∨ a = b := by
    clear * - eq36017 eq35943
    first | exact Or.assoc3 (eq35943.imp_left (fun h : c = sk2 => superpose h eq36017)) | exact superpose eq36017 eq35943 | exact superpose eq35943 eq36017 | grind only
  have eq41473 : (old a c sk3) ∨ c = sk3 ∨ a = b := by
    clear * - eq41442
    first | exact resolve eq41442 rfl | grind only
  have eq41489 : c = sk3 ∨ a = b := by
    clear * - eq41473 p4XZ
    first | exact resolve eq41473 p4XZ | exact resolve p4XZ eq41473 | grind only
  have eq41716 : (new c c b) ∨ a = c ∨ a = b ∨ (old b b a) ∨ (old c sk1 sk4) ∨ a = b := by
    clear * - eq2195 eq41489
    first | exact Or.assoc5 (eq41489.imp_left (fun h : c = sk3 => superpose h eq2195)) | exact superpose eq2195 eq41489 | exact superpose eq41489 eq2195 | grind only
  have eq41854 : c = b ∨ a = b ∨ a = b := by
    clear * - eq36321 eq41489
    first | exact Or.assoc2 (eq41489.imp_left (fun h : c = sk3 => superpose h eq36321)) | exact superpose eq36321 eq41489 | exact superpose eq41489 eq36321 | grind only
  have eq41857 : c = b ∨ a = b := by
    clear * - eq41854
    first | exact resolve eq41854 rfl | grind only
  have eq41966 : (new c c b) ∨ a = c ∨ a = b ∨ (old b b a) ∨ (old c sk1 sk4) := by
    clear * - eq41716
    first | exact resolve eq41716 rfl | grind only
  have eq42032 : a = b := by
    clear * - eq41857 bc
    first | exact resolve eq41857 bc | exact resolve bc eq41857 | grind only
  have eq42049 : (new c c b) ∨ a = c ∨ (old b b a) ∨ (old c sk1 sk4) := by
    clear * - eq41966 eq196
    first | exact resolve eq41966 eq196 | exact resolve eq196 eq41966 | grind only
  have eq42089 : (new c c b) ∨ a = c ∨ (old c sk1 sk4) := by
    clear * - eq42049 eq178
    first | exact resolve eq42049 eq178 | exact resolve eq178 eq42049 | grind only
  have eq42092 : (new c c b) ∨ (old c sk1 sk4) := by
    clear * - eq42089 ac
    first | exact resolve eq42089 ac | exact resolve ac eq42089 | grind only
  have eq42094 : (new c c b) := by
    clear * - eq42092 p4YZ
    first | exact resolve eq42092 p4YZ | exact resolve p4YZ eq42092 | grind only
  have eq42261 (X0 : G) : ¬(old b b X0) := by
    clear * - p3 eq42032
    first | exact superpose p3 eq42032 | exact superpose eq42032 p3 | grind only
  have eq42263 : (new b b c) := by
    clear * - new_new eq42032
    first | exact superpose new_new eq42032 | exact superpose eq42032 new_new | grind only
  have eq42265 : b ≠ b ∨ (new c b c) := by
    clear * - eq187 eq42032
    first | exact superpose eq187 eq42032 | exact superpose eq42032 eq187 | grind only
  have eq42267 : b ≠ b ∨ (new b c b) := by
    clear * - eq199 eq42032
    first | exact superpose eq199 eq42032 | exact superpose eq42032 eq199 | grind only
  have eq42270 (X0 : G) : ¬(new b b X0) ∨ c = X0 := by
    clear * - eq214 eq42032
    first | exact superpose eq214 eq42032 | exact superpose eq42032 eq214 | grind only
  have eq42339 : (old sk0 sk3 b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq5785 eq42032
    first | exact superpose eq5785 eq42032 | exact superpose eq42032 eq5785 | grind only
  have eq42375 : (new b c b) := by
    clear * - eq42267
    first | exact resolve eq42267 rfl | grind only
  have eq42377 : (new c b c) := by
    clear * - eq42265
    first | exact resolve eq42265 rfl | grind only
  have eq42693 (X0 : G) : ¬(new c b X0) ∨ c = X0 := by
    clear * - eq42377 prev_0
    first | exact resolve eq42377 prev_0 | exact resolve prev_0 eq42377 | grind only
  have eq69666 : (old sk0 sk2 c) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ b = sk3 := by
    clear * - eq893 eq36317
    first | exact Or.assoc4 (eq36317.imp_left (fun h : c = sk3 => superpose h eq893)) | exact superpose eq893 eq36317 | exact superpose eq36317 eq893 | grind only
  have eq70124 : (old sk0 sk2 c) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ c = sk1 ∨ b = sk3 := by
    clear * - eq69666
    first | exact resolve eq69666 rfl | grind only
  have eq70185 : a = sk0 ∨ c = b ∨ c = sk0 ∨ c = sk1 ∨ b = sk3 := by
    clear * - eq70124 p4XY
    first | exact resolve eq70124 p4XY | exact resolve p4XY eq70124 | grind only
  have eq70219 : a = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk3 := by
    clear * - eq70185 bc
    first | exact resolve eq70185 bc | exact resolve bc eq70185 | grind only
  have eq70235 : b = sk3 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq70219 eq42032
    first | simpa only [eq42032, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq70219 | grind only
  have eq70342 : (old b sk1 sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq512 eq70235
    first | exact Or.assoc3 (eq70235.imp_left (fun h : b = sk3 => superpose h eq512)) | exact superpose eq512 eq70235 | exact superpose eq70235 eq512 | grind only
  have eq70395 : (sP1 sk0 sk2 b) ∨ (old sk0 sk2 b) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq1299 eq70235
    first | exact Or.assoc5 (eq70235.imp_left (fun h : b = sk3 => superpose h eq1299)) | exact superpose eq1299 eq70235 | exact superpose eq70235 eq1299 | grind only
  have eq70992 : (sP1 sk0 sk2 b) ∨ (old sk0 sk2 b) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq70395
    first | exact resolve eq70395 rfl | grind only
  have eq71022 : (old b sk1 sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq70342
    first | exact resolve eq70342 rfl | grind only
  have eq71085 : b = sk0 ∨ (sP1 sk0 sk2 b) ∨ (old sk0 sk2 b) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq70992 eq42032
    first | simpa only [eq42032, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq70992 | grind only
  have eq71086 : (sP1 sk0 sk2 b) ∨ b = sk0 ∨ (old sk0 sk2 b) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq71085
    first | exact resolve eq71085 rfl | grind only
  have eq92037 : (new sk0 c b) ∨ (old sk0 sk2 b) ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq71086 eq219
    first | exact resolve eq71086 eq219 | exact resolve eq219 eq71086 | grind only
  have eq125279 : c = sk3 ∨ b = sk1 ∨ ¬(old sk0 b sk3) ∨ (old b b sk3) ∨ b = sk3 ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq3668 eq5785
    first | exact resolve eq3668 eq5785 | exact resolve eq5785 eq3668 | grind only
  have eq125305 : c = sk3 ∨ b = sk1 ∨ ¬(old sk0 b sk3) ∨ (old b b sk3) ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq125279
    first | exact resolve eq125279 rfl | grind only
  have eq125310 : c = sk3 ∨ b = sk1 ∨ (old b b sk3) ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq125305 eq2726
    first | exact resolve eq125305 eq2726 | exact resolve eq2726 eq125305 | grind only
  have eq125313 : c = sk3 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq125310 eq42261
    first | exact resolve eq125310 eq42261 | exact resolve eq42261 eq125310 | grind only
  have eq125780 : (old sk0 c b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 ∨ b = sk3 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq42339 eq125313
    first | exact Or.assoc4 (eq125313.imp_left (fun h : c = sk3 => superpose h eq42339)) | exact superpose eq42339 eq125313 | exact superpose eq125313 eq42339 | grind only
  have eq125843 : (old sk0 c b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ b = sk3 := by
    clear * - eq125780
    first | exact resolve eq125780 rfl | grind only
  have eq126052 : b = sk3 ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq125843 p4XZ
    first | exact resolve eq125843 p4XZ | exact resolve p4XZ eq125843 | grind only
  have eq126750 : (old sk0 b b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ b = sk1 := by
    clear * - eq42339 eq126052
    first | exact Or.assoc4 (eq126052.imp_left (fun h : b = sk3 => superpose h eq42339)) | exact superpose eq42339 eq126052 | exact superpose eq126052 eq42339 | grind only
  have eq126802 : (old sk0 b b) ∨ b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq126750
    first | exact resolve eq126750 rfl | grind only
  have eq127745 : b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ (old b b b) := by
    clear * - eq126802 old_7
    first | exact resolve eq126802 old_7 | exact resolve old_7 eq126802 | grind only
  have eq127835 : b = sk1 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq127745 eq42261
    first | exact resolve eq127745 eq42261 | exact resolve eq42261 eq127745 | grind only
  have eq127912 : ¬(new sk0 sk4 b) ∨ b = sk0 ∨ c = sk0 := by
    clear * - preserve_3 eq127835
    first | exact (eq127835.imp_left (fun h : b = sk1 => superpose h preserve_3)) | exact superpose preserve_3 eq127835 | exact superpose eq127835 preserve_3 | grind only
  have eq127950 : (old sk0 b sk2) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq821 eq127835
    first | exact Or.assoc4 (eq127835.imp_left (fun h : b = sk1 => superpose h eq821)) | exact superpose eq821 eq127835 | exact superpose eq127835 eq821 | grind only
  have eq128322 : (old b b sk4) ∨ c = sk4 ∨ c = b ∨ c = sk0 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq71022 eq127835
    first | exact Or.assoc5 (eq127835.imp_left (fun h : b = sk1 => superpose h eq71022)) | exact superpose eq71022 eq127835 | exact superpose eq127835 eq71022 | grind only
  have eq128459 : (old b b sk4) ∨ c = sk4 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq128322
    first | exact resolve eq128322 rfl | grind only
  have eq128568 : (old sk0 b sk2) ∨ a = sk0 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq127950
    first | exact resolve eq127950 rfl | grind only
  have eq128583 : c = sk4 ∨ c = b ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq128459 eq42261
    first | exact resolve eq128459 eq42261 | exact resolve eq42261 eq128459 | grind only
  have eq128691 : (old sk0 b sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq128568 bc
    first | exact resolve eq128568 bc | exact resolve bc eq128568 | grind only
  have eq128715 : c = sk4 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq128583 bc
    first | exact resolve eq128583 bc | exact resolve bc eq128583 | grind only
  have eq128770 : b = sk0 ∨ (old sk0 b sk2) ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq128691 eq42032
    first | simpa only [eq42032, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq128691 | grind only
  have eq128771 : (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq128770
    first | exact resolve eq128770 rfl | grind only
  have eq129660 : ¬(new sk0 c b) ∨ b = sk0 ∨ c = sk0 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq127912 eq128715
    first | exact Or.assoc3 (eq128715.imp_left (fun h : c = sk4 => superpose h eq127912)) | exact superpose eq127912 eq128715 | exact superpose eq128715 eq127912 | grind only
  have eq129661 : ¬(new sk0 c b) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq129660
    first | exact resolve eq129660 rfl | grind only
  have eq129945 : b = sk0 ∨ c = sk0 ∨ ¬(old sk0 sk2 a) ∨ (new sk0 c b) := by
    clear * - eq128771 eq169
    first | exact resolve eq128771 eq169 | exact resolve eq169 eq128771 | grind only
  have eq130111 : b = sk0 ∨ c = sk0 ∨ ¬(old sk0 sk2 a) := by
    clear * - eq129945 eq129661
    first | exact resolve eq129945 eq129661 | exact resolve eq129661 eq129945 | grind only
  have eq130114 : ¬(old sk0 sk2 b) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq130111 eq42032
    first | simpa only [eq42032, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq130111 | grind only
  have eq130628 : b = sk0 ∨ c = sk0 ∨ (old sk0 sk2 b) ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := by
    clear * - eq129661 eq92037
    first | exact resolve eq129661 eq92037 | exact resolve eq92037 eq129661 | grind only
  have eq130631 : b = sk0 ∨ c = sk0 ∨ (old sk0 sk2 b) ∨ c = sk1 := by
    clear * - eq130628
    first | exact resolve eq130628 rfl | grind only
  have eq130644 : c = sk1 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq130631 eq130114
    first | exact resolve eq130631 eq130114 | exact resolve eq130114 eq130631 | grind only
  have eq131106 : c = b ∨ b = sk0 ∨ c = sk0 ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq127835 eq130644
    first | exact Or.assoc3 (eq130644.imp_left (fun h : c = sk1 => superpose h eq127835)) | exact superpose eq127835 eq130644 | exact superpose eq130644 eq127835 | grind only
  have eq131111 : c = b ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq131106
    first | exact resolve eq131106 rfl | grind only
  have eq131230 : c = sk0 ∨ b = sk0 := by
    clear * - eq131111 bc
    first | exact resolve eq131111 bc | exact resolve bc eq131111 | grind only
  have eq131311 : (new c sk1 sk2) ∨ b = sk0 := by
    clear * - preserve_0 eq131230
    first | exact (eq131230.imp_left (fun h : c = sk0 => superpose h preserve_0)) | exact superpose preserve_0 eq131230 | exact superpose eq131230 preserve_0 | grind only
  have eq131313 : ¬(new c sk4 sk1) ∨ b = sk0 := by
    clear * - preserve_3 eq131230
    first | exact (eq131230.imp_left (fun h : c = sk0 => superpose h preserve_3)) | exact superpose preserve_3 eq131230 | exact superpose eq131230 preserve_3 | grind only
  have eq131550 : ¬(new c b c) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq2772 eq131230
    first | exact Or.assoc2 (eq131230.imp_left (fun h : c = sk0 => superpose h eq2772)) | exact superpose eq2772 eq131230 | exact superpose eq131230 eq2772 | grind only
  have eq131934 : b = sk1 ∨ b = sk0 := by
    clear * - eq131550 eq42377
    first | exact resolve eq131550 eq42377 | exact resolve eq42377 eq131550 | grind only
  have eq132029 : (new sk3 b sk4) ∨ b = sk0 := by
    clear * - preserve_2 eq131934
    first | exact (eq131934.imp_left (fun h : b = sk1 => superpose h preserve_2)) | exact superpose preserve_2 eq131934 | exact superpose eq131934 preserve_2 | grind only
  have eq132732 : (new c b sk2) ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq131311 eq131934
    first | exact Or.assoc2 (eq131934.imp_left (fun h : b = sk1 => superpose h eq131311)) | exact superpose eq131311 eq131934 | exact superpose eq131934 eq131311 | grind only
  have eq132753 : (new c b sk2) ∨ b = sk0 := by
    clear * - eq132732
    first | exact resolve eq132732 rfl | grind only
  have eq132954 : ¬(new c sk4 b) ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq131313 eq131934
    first | exact Or.assoc2 (eq131934.imp_left (fun h : b = sk1 => superpose h eq131313)) | exact superpose eq131313 eq131934 | exact superpose eq131934 eq131313 | grind only
  have eq132955 : ¬(new c sk4 b) ∨ b = sk0 := by
    clear * - eq132954
    first | exact resolve eq132954 rfl | grind only
  have eq133442 : c = sk2 ∨ b = sk0 := by
    clear * - eq132753 eq42693
    first | exact resolve eq132753 eq42693 | exact resolve eq42693 eq132753 | grind only
  have eq133579 : (old sk0 c sk3) ∨ c = b ∨ b = sk3 ∨ b = sk0 := by
    clear * - eq432 eq133442
    first | exact Or.assoc3 (eq133442.imp_left (fun h : c = sk2 => superpose h eq432)) | exact superpose eq432 eq133442 | exact superpose eq133442 eq432 | grind only
  have eq134012 : c = b ∨ b = sk3 ∨ b = sk0 := by
    clear * - eq133579 p4XZ
    first | exact resolve eq133579 p4XZ | exact resolve p4XZ eq133579 | grind only
  have eq134029 : b = sk3 ∨ b = sk0 := by
    clear * - eq134012 bc
    first | exact resolve eq134012 bc | exact resolve bc eq134012 | grind only
  have eq134700 : (new b b sk4) ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq132029 eq134029
    first | exact Or.assoc2 (eq134029.imp_left (fun h : b = sk3 => superpose h eq132029)) | exact superpose eq132029 eq134029 | exact superpose eq134029 eq132029 | grind only
  have eq134701 : (new b b sk4) ∨ b = sk0 := by
    clear * - eq134700
    first | exact resolve eq134700 rfl | grind only
  have eq135929 : c = sk4 ∨ b = sk0 := by
    clear * - eq134701 eq42270
    first | exact resolve eq134701 eq42270 | exact resolve eq42270 eq134701 | grind only
  have eq136302 : ¬(new c c b) ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq132955 eq135929
    first | exact Or.assoc2 (eq135929.imp_left (fun h : c = sk4 => superpose h eq132955)) | exact superpose eq132955 eq135929 | exact superpose eq135929 eq132955 | grind only
  have eq136307 : ¬(new c c b) ∨ b = sk0 := by
    clear * - eq136302
    first | exact resolve eq136302 rfl | grind only
  have eq136359 : b = sk0 := by
    clear * - eq136307 eq42094
    first | exact resolve eq136307 eq42094 | exact resolve eq42094 eq136307 | grind only
  have eq136743 : ¬(new b b c) ∨ b = sk1 := by
    clear * - eq2772 eq136359
    first | exact superpose eq2772 eq136359 | exact superpose eq136359 eq2772 | grind only
  have eq137628 : b = sk1 := by
    clear * - eq136743 eq42263
    first | exact resolve eq136743 eq42263 | exact resolve eq42263 eq136743 | grind only
  have eq137711 : (old sk0 b sk2) ∨ c = sk2 ∨ c = b := by
    clear * - eq400 eq137628
    first | exact superpose eq400 eq137628 | exact superpose eq137628 eq400 | grind only
  have eq138336 : (old sk0 b sk2) ∨ c = sk2 := by
    clear * - eq137711 bc
    first | exact resolve eq137711 bc | exact resolve bc eq137711 | grind only
  have eq138412 : (old b b sk2) ∨ c = sk2 := by
    clear * - eq138336 eq136359
    first | simpa only [eq136359, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq138336 | grind only
  have eq138453 : c = sk2 := by
    clear * - eq138412 eq42261
    first | exact resolve eq138412 eq42261 | exact resolve eq42261 eq138412 | grind only
  have eq138717 : (old sk0 c sk3) ∨ c = b ∨ b = sk3 := by
    clear * - eq432 eq138453
    first | exact superpose eq432 eq138453 | exact superpose eq138453 eq432 | grind only
  have eq139056 : c = b ∨ b = sk3 := by
    clear * - eq138717 p4XZ
    first | exact resolve eq138717 p4XZ | exact resolve p4XZ eq138717 | grind only
  have eq139072 : b = sk3 := by
    clear * - eq139056 bc
    first | exact resolve eq139056 bc | exact resolve bc eq139056 | grind only
  have eq139368 : (old b sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq512 eq139072
    first | exact superpose eq512 eq139072 | exact superpose eq139072 eq512 | grind only
  have eq140104 : (old b b sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq139368 eq137628
    first | simpa only [eq137628, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq139368 | grind only
  have eq140120 : c = sk4 ∨ c = sk1 := by
    clear * - eq140104 eq42261
    first | exact resolve eq140104 eq42261 | exact resolve eq42261 eq140104 | grind only
  have eq140133 : c = b ∨ c = sk4 := by
    clear * - eq140120 eq137628
    first | simpa only [eq137628, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq140120 | grind only
  have eq140141 : c = sk4 := by
    clear * - eq140133 bc
    first | exact resolve eq140133 bc | exact resolve bc eq140133 | grind only
  have eq140343 : ¬(new sk0 c sk1) := by
    clear * - preserve_3 eq140141
    first | exact superpose preserve_3 eq140141 | exact superpose eq140141 preserve_3 | grind only
  have eq140648 : ¬(new sk0 c b) := by
    clear * - eq140343 eq137628
    first | simpa only [eq137628, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq140343 | grind only
  have eq140656 : ¬(new b c b) := by
    clear * - eq140648 eq136359
    first | simpa only [eq136359, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq140648 | grind only
  clear * - eq140656 eq42375
  first | subsumption eq140656 eq42375 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (new_new : new a b c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1, ¬ old X0 X1 X0 ∨ old X1 X1 X0)) (old_6 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X0 X1 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), c = X ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_1 : ∀ (X Y Z : G), c = X ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (imp_new_11 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_10_1 : ∀ (X Y Z : G), c = X ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (rule_def_11_0 : ∀ (X Y Z : G), a = b ∨ ¬sP11 X Y Z) (rule_def_11_1 : ∀ (X Y Z : G), b = X ∨ ¬sP11 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X0 ∨ new X1 X1 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq192 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new c X1 X2) := by
    clear * - imp_new_11
    first | exact resolve imp_new_11 rfl | grind only
  have eq193 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new c c X2) := by
    clear * - eq192
    first | exact resolve eq192 rfl | grind only
  have eq194 : a ≠ b ∨ (new c c b) := by
    clear * - eq193
    first | exact resolve eq193 rfl | grind only
  have eq200 (X0 X1 : G) : (old b (sF0 b X0 X1) b) ∨ ¬(sP1 b X0 X1) := by
    clear * - rule_def_1_2 old_6
    first | exact resolve rule_def_1_2 old_6 | exact resolve old_6 rule_def_1_2 | grind only
  have eq206 (X0 X1 X2 X3 : G) : ¬(old X0 (sF0 X0 X1 X2) X3) ∨ ¬(sP1 X0 X1 X2) ∨ a = X3 := by
    clear * - rule_def_1_3 old_0
    first | exact resolve rule_def_1_3 old_0 | exact resolve old_0 rule_def_1_3 | grind only
  have eq226 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq231 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq226 rule_def_0_2
    first | exact resolve eq226 rule_def_0_2 | exact resolve rule_def_0_2 eq226 | grind only
  have eq232 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ b = sk1 := by
    clear * - eq226 rule_def_0_1
    first | exact resolve eq226 rule_def_0_1 | exact resolve rule_def_0_1 eq226 | grind only
  have eq233 : (sP11 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 := by
    clear * - eq226 rule_def_0_0
    first | exact resolve eq226 rule_def_0_0 | exact resolve rule_def_0_0 eq226 | grind only
  have eq234 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ b = sk1 := by
    clear * - eq232 rule_def_5_2
    first | exact resolve eq232 rule_def_5_2 | exact resolve rule_def_5_2 eq232 | grind only
  have eq235 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq231 rule_def_2_0
    first | exact resolve eq231 rule_def_2_0 | exact resolve rule_def_2_0 eq231 | grind only
  have eq236 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ b = sk1 := by
    clear * - eq234 rule_def_6_2
    first | exact resolve eq234 rule_def_6_2 | exact resolve rule_def_6_2 eq234 | grind only
  have eq237 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq235 rule_def_3_0
    first | exact resolve eq235 rule_def_3_0 | exact resolve rule_def_3_0 eq235 | grind only
  have eq238 : (sP11 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 := by
    clear * - eq236 rule_def_7_2
    first | exact resolve eq236 rule_def_7_2 | exact resolve rule_def_7_2 eq236 | grind only
  have eq239 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq237 rule_def_4_0
    first | exact resolve eq237 rule_def_4_0 | exact resolve rule_def_4_0 eq237 | grind only
  have eq240 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq239 rule_def_5_3
    first | exact resolve eq239 rule_def_5_3 | exact resolve rule_def_5_3 eq239 | grind only
  have eq241 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq240 rule_def_6_3
    first | exact resolve eq240 rule_def_6_3 | exact resolve rule_def_6_3 eq240 | grind only
  have eq242 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq241 rule_def_7_3
    first | exact resolve eq241 rule_def_7_3 | exact resolve rule_def_7_3 eq241 | grind only
  have eq243 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq242 rule_def_8_1
    first | exact resolve eq242 rule_def_8_1 | exact resolve rule_def_8_1 eq242 | grind only
  have eq244 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (sP11 sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq243 rule_def_9_1
    first | exact resolve eq243 rule_def_9_1 | exact resolve rule_def_9_1 eq243 | grind only
  have eq245 : (sP11 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk0 := by
    clear * - eq244 rule_def_10_1
    first | exact resolve eq244 rule_def_10_1 | exact resolve rule_def_10_1 eq244 | grind only
  have eq252 : (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq245 rule_def_11_2
    first | exact resolve eq245 rule_def_11_2 | exact resolve rule_def_11_2 eq245 | grind only
  have eq253 : (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq245 rule_def_11_1
    first | exact resolve eq245 rule_def_11_1 | exact resolve rule_def_11_1 eq245 | grind only
  have eq255 : (old sk0 sk1 sk0) ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq253 rule_def_1_1
    first | exact resolve eq253 rule_def_1_1 | exact resolve rule_def_1_1 eq253 | grind only
  have eq256 : (old sk0 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq252 rule_def_1_0
    first | exact resolve eq252 rule_def_1_0 | exact resolve rule_def_1_0 eq252 | grind only
  have eq261 : (old sk1 sk1 sk0) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq255 old_2
    first | exact resolve eq255 old_2 | exact resolve old_2 eq255 | grind only
  have eq268 : (old sk1 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq256 old_2
    first | exact resolve eq256 old_2 | exact resolve old_2 eq256 | grind only
  have eq280 : b = sk0 ∨ c = sk0 ∨ (new sk1 sk1 sk0) := by
    clear * - eq261 imp_new_0
    first | exact resolve eq261 imp_new_0 | exact resolve imp_new_0 eq261 | grind only
  have eq281 : c = sk0 ∨ b = sk0 := by
    clear * - eq280 preserve_1
    first | exact resolve eq280 preserve_1 | exact resolve preserve_1 eq280 | grind only
  have eq291 : ¬(new sk1 sk1 c) ∨ b = sk0 := by
    clear * - preserve_1 eq281
    first | exact (eq281.imp_left (fun h : c = sk0 => superpose h preserve_1)) | exact superpose preserve_1 eq281 | exact superpose eq281 preserve_1 | grind only
  have eq309 (X0 X1 : G) : ¬(sP1 b X0 X1) ∨ a = b ∨ ¬(sP1 b X0 X1) := by
    clear * - eq206 eq200
    first | exact resolve eq206 eq200 | exact resolve eq200 eq206 | grind only
  have eq310 (X0 X1 : G) : ¬(sP1 b X0 X1) ∨ a = b := by
    clear * - eq309
    first | exact resolve eq309 rfl | grind only
  have eq322 : c = sk1 ∨ c = sk0 ∨ (new sk1 sk1 sk0) := by
    clear * - eq268 imp_new_0
    first | exact resolve eq268 imp_new_0 | exact resolve imp_new_0 eq268 | grind only
  have eq323 : c = sk1 ∨ c = sk0 := by
    clear * - eq322 preserve_1
    first | exact resolve eq322 preserve_1 | exact resolve preserve_1 eq322 | grind only
  have eq325 : ¬(new c c sk0) ∨ c = sk0 := by
    clear * - preserve_1 eq323
    first | exact (eq323.imp_left (fun h : c = sk1 => superpose h preserve_1)) | exact superpose preserve_1 eq323 | exact superpose eq323 preserve_1 | grind only
  have eq329 : (sP11 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (old sk0 c sk0) ∨ c = sk0 ∨ c = sk0 := by
    clear * - eq245 eq323
    first | exact Or.assoc4 (eq323.imp_left (fun h : c = sk1 => superpose h eq245)) | exact superpose eq245 eq323 | exact superpose eq323 eq245 | grind only
  have eq336 : (sP11 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (old sk0 c sk0) ∨ c = sk0 := by
    clear * - eq329
    first | exact resolve eq329 rfl | grind only
  have eq337 : (sP11 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ c = sk0 := by
    clear * - eq336 p4XZ
    first | exact resolve eq336 p4XZ | exact resolve p4XZ eq336 | grind only
  have eq376 : (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq238 rule_def_11_1
    first | exact resolve eq238 rule_def_11_1 | exact resolve rule_def_11_1 eq238 | grind only
  have eq382 : (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq376 rule_def_1_1
    first | exact resolve eq376 rule_def_1_1 | exact resolve rule_def_1_1 eq376 | grind only
  have eq387 : (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq382 rule_def_2_2
    first | exact resolve eq382 rule_def_2_2 | exact resolve rule_def_2_2 eq382 | grind only
  have eq391 : (sP4 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq387 rule_def_3_2
    first | exact resolve eq387 rule_def_3_2 | exact resolve rule_def_3_2 eq387 | grind only
  have eq394 : (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq391 rule_def_4_2
    first | exact resolve eq391 rule_def_4_2 | exact resolve rule_def_4_2 eq391 | grind only
  have eq397 : (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq394 rule_def_8_3
    first | exact resolve eq394 rule_def_8_3 | exact resolve rule_def_8_3 eq394 | grind only
  have eq400 : (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq397 rule_def_9_3
    first | exact resolve eq397 rule_def_9_3 | exact resolve rule_def_9_3 eq397 | grind only
  have eq403 : (old sk0 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq400 rule_def_10_3
    first | exact resolve eq400 rule_def_10_3 | exact resolve rule_def_10_3 eq400 | grind only
  have eq412 : (old c sk1 c) ∨ b = sk1 ∨ c = b ∨ b = sk0 := by
    clear * - eq403 eq281
    first | exact Or.assoc3 (eq281.imp_left (fun h : c = sk0 => superpose h eq403)) | exact superpose eq403 eq281 | exact superpose eq281 eq403 | grind only
  have eq413 : b = sk1 ∨ c = b ∨ b = sk0 := by
    clear * - eq412 p4XY
    first | exact resolve eq412 p4XY | exact resolve p4XY eq412 | grind only
  have eq414 : b = sk1 ∨ b = sk0 := by
    clear * - eq413 bc
    first | exact resolve eq413 bc | exact resolve bc eq413 | grind only
  have eq417 : (sP1 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq233 rule_def_11_1
    first | exact resolve eq233 rule_def_11_1 | exact resolve rule_def_11_1 eq233 | grind only
  have eq423 : (sP2 sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq417 rule_def_1_1
    first | exact resolve eq417 rule_def_1_1 | exact resolve rule_def_1_1 eq417 | grind only
  have eq428 : (sP3 sk0 sk1 sk0) ∨ (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq423 rule_def_2_2
    first | exact resolve eq423 rule_def_2_2 | exact resolve rule_def_2_2 eq423 | grind only
  have eq433 : (sP4 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq428 rule_def_3_2
    first | exact resolve eq428 rule_def_3_2 | exact resolve rule_def_3_2 eq428 | grind only
  have eq437 : (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP8 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq433 rule_def_4_2
    first | exact resolve eq433 rule_def_4_2 | exact resolve rule_def_4_2 eq433 | grind only
  have eq441 : (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP9 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq437 rule_def_8_3
    first | exact resolve eq437 rule_def_8_3 | exact resolve rule_def_8_3 eq437 | grind only
  have eq445 : (sP5 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP7 sk0 sk1 sk0) ∨ (sP10 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq441 rule_def_9_3
    first | exact resolve eq441 rule_def_9_3 | exact resolve rule_def_9_3 eq441 | grind only
  have eq448 : (sP7 sk0 sk1 sk0) ∨ (sP6 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := by
    clear * - eq445 rule_def_10_3
    first | exact resolve eq445 rule_def_10_3 | exact resolve rule_def_10_3 eq445 | grind only
  have eq466 : ¬(new b b c) ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq291 eq414
    first | exact Or.assoc2 (eq414.imp_left (fun h : b = sk1 => superpose h eq291)) | exact superpose eq291 eq414 | exact superpose eq414 eq291 | grind only
  have eq468 : ¬(new b b c) ∨ b = sk0 := by
    clear * - eq466
    first | exact resolve eq466 rfl | grind only
  have eq688 : (sP1 sk0 c sk0) ∨ c = sk0 ∨ a = b := by
    clear * - eq337 rule_def_11_0
    first | exact resolve eq337 rule_def_11_0 | exact resolve rule_def_11_0 eq337 | grind only
  have eq747 : (sP6 sk0 sk1 sk0) ∨ (sP5 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 ∨ a = b := by
    clear * - eq448 rule_def_7_0
    first | exact resolve eq448 rule_def_7_0 | exact resolve rule_def_7_0 eq448 | grind only
  have eq754 : (sP5 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 ∨ a = b := by
    clear * - eq747 rule_def_6_0
    first | exact resolve eq747 rule_def_6_0 | exact resolve rule_def_6_0 eq747 | grind only
  have eq756 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 ∨ a = b := by
    clear * - eq754 rule_def_5_0
    first | exact resolve eq754 rule_def_5_0 | exact resolve rule_def_5_0 eq754 | grind only
  have eq858 : (old c sk1 c) ∨ a = c ∨ c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq756 eq281
    first | exact Or.assoc4 (eq281.imp_left (fun h : c = sk0 => superpose h eq756)) | exact superpose eq756 eq281 | exact superpose eq281 eq756 | grind only
  have eq862 : a = c ∨ c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq858 p4XY
    first | exact resolve eq858 p4XY | exact resolve p4XY eq858 | grind only
  have eq863 : c = b ∨ a = b ∨ b = sk0 := by
    clear * - eq862 ac
    first | exact resolve eq862 ac | exact resolve ac eq862 | grind only
  have eq864 : b = sk0 ∨ a = b := by
    clear * - eq863 bc
    first | exact resolve eq863 bc | exact resolve bc eq863 | grind only
  have eq898 : (sP1 b c b) ∨ c = b ∨ a = b ∨ a = b := by
    clear * - eq688 eq864
    first | exact Or.assoc3 (eq864.imp_left (fun h : b = sk0 => superpose h eq688)) | exact superpose eq688 eq864 | exact superpose eq864 eq688 | grind only
  have eq901 : (sP1 b c b) ∨ c = b ∨ a = b := by
    clear * - eq898
    first | exact resolve eq898 rfl | grind only
  have eq908 : c = b ∨ a = b := by
    clear * - eq901 eq310
    first | exact resolve eq901 eq310 | exact resolve eq310 eq901 | grind only
  have eq928 : a = b := by
    clear * - eq908 bc
    first | exact resolve eq908 bc | exact resolve bc eq908 | grind only
  have eq945 : (new b b c) := by
    clear * - new_new eq928
    first | exact superpose new_new eq928 | exact superpose eq928 new_new | grind only
  have eq948 : b ≠ b ∨ (new c c b) := by
    clear * - eq194 eq928
    first | exact superpose eq194 eq928 | exact superpose eq928 eq194 | grind only
  have eq965 : (new c c b) := by
    clear * - eq948
    first | exact resolve eq948 rfl | grind only
  have eq989 : b = sk0 := by
    clear * - eq945 eq468
    first | exact resolve eq945 eq468 | exact resolve eq468 eq945 | grind only
  have eq1012 : ¬(new c c b) ∨ c = b := by
    clear * - eq325 eq989
    first | exact superpose eq325 eq989 | exact superpose eq989 eq325 | grind only
  have eq1031 : c = b := by
    clear * - eq1012 eq965
    first | exact resolve eq1012 eq965 | exact resolve eq965 eq1012 | grind only
  clear * - eq1031 bc
  first | subsumption eq1031 bc | grind only


set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (new_new : new a b c) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_4 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X0 X1)) (old_5 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X1 X0)) (old_6 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X0 X1 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), a = b ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_0 : ∀ (X Y Z : G), a = b ∨ ¬sP9 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (imp_new_11 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_10_0 : ∀ (X Y Z : G), a = b ∨ ¬sP10 X Y Z) (rule_def_10_1 : ∀ (X Y Z : G), c = X ∨ ¬sP10 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (rule_def_11_0 : ∀ (X Y Z : G), a = b ∨ ¬sP11 X Y Z) (rule_def_11_1 : ∀ (X Y Z : G), b = X ∨ ¬sP11 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X0 ∨ new X2 X2 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq196 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new c X1 X2) := by
    clear * - imp_new_11
    first | exact resolve imp_new_11 rfl | grind only
  have eq197 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new c c X2) := by
    clear * - eq196
    first | exact resolve eq196 rfl | grind only
  have eq198 : a ≠ b ∨ (new c c b) := by
    clear * - eq197
    first | exact resolve eq197 rfl | grind only
  have eq204 (X0 X1 : G) : (old b (sF0 b X0 X1) b) ∨ ¬(sP1 b X0 X1) := by
    clear * - rule_def_1_2 old_6
    first | exact resolve rule_def_1_2 old_6 | exact resolve old_6 rule_def_1_2 | grind only
  have eq210 (X0 X1 X2 X3 : G) : ¬(old X0 (sF0 X0 X1 X2) X3) ∨ ¬(sP1 X0 X1 X2) ∨ a = X3 := by
    clear * - rule_def_1_3 old_0
    first | exact resolve rule_def_1_3 old_0 | exact resolve old_0 rule_def_1_3 | grind only
  have eq213 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := by
    clear * - prev_0 preserve_0
    first | exact resolve prev_0 preserve_0 | exact resolve preserve_0 prev_0 | grind only
  have eq231 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq232 : (sP0 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq238 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq231 rule_def_0_2
    first | exact resolve eq231 rule_def_0_2 | exact resolve rule_def_0_2 eq231 | grind only
  have eq239 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq231 rule_def_0_1
    first | exact resolve eq231 rule_def_0_1 | exact resolve rule_def_0_1 eq231 | grind only
  have eq240 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq231 rule_def_0_0
    first | exact resolve eq231 rule_def_0_0 | exact resolve rule_def_0_0 eq231 | grind only
  have eq241 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq239 rule_def_5_2
    first | exact resolve eq239 rule_def_5_2 | exact resolve rule_def_5_2 eq239 | grind only
  have eq242 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq238 rule_def_5_3
    first | exact resolve eq238 rule_def_5_3 | exact resolve rule_def_5_3 eq238 | grind only
  have eq243 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq241 rule_def_6_2
    first | exact resolve eq241 rule_def_6_2 | exact resolve rule_def_6_2 eq241 | grind only
  have eq244 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq242 rule_def_6_3
    first | exact resolve eq242 rule_def_6_3 | exact resolve rule_def_6_3 eq242 | grind only
  have eq245 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq243 rule_def_7_2
    first | exact resolve eq243 rule_def_7_2 | exact resolve rule_def_7_2 eq243 | grind only
  have eq246 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq244 rule_def_7_3
    first | exact resolve eq244 rule_def_7_3 | exact resolve rule_def_7_3 eq244 | grind only
  have eq247 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq245 rule_def_11_3
    first | exact resolve eq245 rule_def_11_3 | exact resolve rule_def_11_3 eq245 | grind only
  have eq248 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq245 rule_def_11_2
    first | exact resolve eq245 rule_def_11_2 | exact resolve rule_def_11_2 eq245 | grind only
  have eq252 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq248 rule_def_1_0
    first | exact resolve eq248 rule_def_1_0 | exact resolve rule_def_1_0 eq248 | grind only
  have eq253 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq247 rule_def_1_1
    first | exact resolve eq247 rule_def_1_1 | exact resolve rule_def_1_1 eq247 | grind only
  have eq255 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq252 rule_def_2_1
    first | exact resolve eq252 rule_def_2_1 | exact resolve rule_def_2_1 eq252 | grind only
  have eq256 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq253 rule_def_2_2
    first | exact resolve eq253 rule_def_2_2 | exact resolve rule_def_2_2 eq253 | grind only
  have eq258 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq255 rule_def_3_1
    first | exact resolve eq255 rule_def_3_1 | exact resolve rule_def_3_1 eq255 | grind only
  have eq259 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq256 rule_def_3_2
    first | exact resolve eq256 rule_def_3_2 | exact resolve rule_def_3_2 eq256 | grind only
  have eq260 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq258 rule_def_4_1
    first | exact resolve eq258 rule_def_4_1 | exact resolve rule_def_4_1 eq258 | grind only
  have eq261 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq259 rule_def_4_2
    first | exact resolve eq259 rule_def_4_2 | exact resolve rule_def_4_2 eq259 | grind only
  have eq262 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq260 rule_def_8_2
    first | exact resolve eq260 rule_def_8_2 | exact resolve rule_def_8_2 eq260 | grind only
  have eq263 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq261 rule_def_8_3
    first | exact resolve eq261 rule_def_8_3 | exact resolve rule_def_8_3 eq261 | grind only
  have eq264 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq262 rule_def_9_2
    first | exact resolve eq262 rule_def_9_2 | exact resolve rule_def_9_2 eq262 | grind only
  have eq265 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq263 rule_def_9_3
    first | exact resolve eq263 rule_def_9_3 | exact resolve rule_def_9_3 eq263 | grind only
  have eq266 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq264 rule_def_10_2
    first | exact resolve eq264 rule_def_10_2 | exact resolve rule_def_10_2 eq264 | grind only
  have eq267 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq265 rule_def_10_3
    first | exact resolve eq265 rule_def_10_3 | exact resolve rule_def_10_3 eq265 | grind only
  have eq268 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ c = sk0 := by
    clear * - eq232 rule_def_0_2
    first | exact resolve eq232 rule_def_0_2 | exact resolve rule_def_0_2 eq232 | grind only
  have eq269 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ b = sk1 := by
    clear * - eq232 rule_def_0_1
    first | exact resolve eq232 rule_def_0_1 | exact resolve rule_def_0_1 eq232 | grind only
  have eq270 : (sP11 sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 := by
    clear * - eq232 rule_def_0_0
    first | exact resolve eq232 rule_def_0_0 | exact resolve rule_def_0_0 eq232 | grind only
  have eq271 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ b = sk1 := by
    clear * - eq269 rule_def_5_2
    first | exact resolve eq269 rule_def_5_2 | exact resolve rule_def_5_2 eq269 | grind only
  have eq272 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ c = sk0 := by
    clear * - eq268 rule_def_5_3
    first | exact resolve eq268 rule_def_5_3 | exact resolve rule_def_5_3 eq268 | grind only
  have eq273 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ b = sk1 := by
    clear * - eq271 rule_def_6_2
    first | exact resolve eq271 rule_def_6_2 | exact resolve rule_def_6_2 eq271 | grind only
  have eq274 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ c = sk0 := by
    clear * - eq272 rule_def_6_3
    first | exact resolve eq272 rule_def_6_3 | exact resolve rule_def_6_3 eq272 | grind only
  have eq275 : (old sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (sP11 sk1 sk1 sk0) ∨ b = sk1 := by
    clear * - eq273 rule_def_7_2
    first | exact resolve eq273 rule_def_7_2 | exact resolve rule_def_7_2 eq273 | grind only
  have eq276 : (sP11 sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 := by
    clear * - eq274 rule_def_7_3
    first | exact resolve eq274 rule_def_7_3 | exact resolve rule_def_7_3 eq274 | grind only
  have eq277 : (sP10 sk1 sk1 sk0) ∨ (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 := by
    clear * - eq275 rule_def_11_1
    first | exact resolve eq275 rule_def_11_1 | exact resolve rule_def_11_1 eq275 | grind only
  have eq280 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ b = sk1 ∨ sk2 = X0 := by
    clear * - eq266 old_0
    first | exact resolve eq266 old_0 | exact resolve old_0 eq266 | grind only
  have eq332 (X0 X1 : G) : ¬(sP1 b X0 X1) ∨ a = b ∨ ¬(sP1 b X0 X1) := by
    clear * - eq210 eq204
    first | exact resolve eq210 eq204 | exact resolve eq204 eq210 | grind only
  have eq333 (X0 X1 : G) : ¬(sP1 b X0 X1) ∨ a = b := by
    clear * - eq332
    first | exact resolve eq332 rfl | grind only
  have eq399 : (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq277 rule_def_10_3
    first | exact resolve eq277 rule_def_10_3 | exact resolve rule_def_10_3 eq277 | grind only
  have eq401 : (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq277 rule_def_10_1
    first | exact resolve eq277 rule_def_10_1 | exact resolve rule_def_10_1 eq277 | grind only
  have eq404 : (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq401 rule_def_1_0
    first | exact resolve eq401 rule_def_1_0 | exact resolve rule_def_1_0 eq401 | grind only
  have eq406 : (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq399 rule_def_1_1
    first | exact resolve eq399 rule_def_1_1 | exact resolve rule_def_1_1 eq399 | grind only
  have eq408 : (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq404 rule_def_2_1
    first | exact resolve eq404 rule_def_2_1 | exact resolve rule_def_2_1 eq404 | grind only
  have eq410 : (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq406 rule_def_2_2
    first | exact resolve eq406 rule_def_2_2 | exact resolve rule_def_2_2 eq406 | grind only
  have eq411 : (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq408 rule_def_3_1
    first | exact resolve eq408 rule_def_3_1 | exact resolve rule_def_3_1 eq408 | grind only
  have eq413 : (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq410 rule_def_3_2
    first | exact resolve eq410 rule_def_3_2 | exact resolve rule_def_3_2 eq410 | grind only
  have eq414 : (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq411 rule_def_4_1
    first | exact resolve eq411 rule_def_4_1 | exact resolve rule_def_4_1 eq411 | grind only
  have eq416 : (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq413 rule_def_4_2
    first | exact resolve eq413 rule_def_4_2 | exact resolve rule_def_4_2 eq413 | grind only
  have eq417 : (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq414 rule_def_8_2
    first | exact resolve eq414 rule_def_8_2 | exact resolve rule_def_8_2 eq414 | grind only
  have eq419 : (sP9 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq416 rule_def_8_3
    first | exact resolve eq416 rule_def_8_3 | exact resolve rule_def_8_3 eq416 | grind only
  have eq420 : (old sk1 sk1 sk0) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq417 rule_def_9_2
    first | exact resolve eq417 rule_def_9_2 | exact resolve rule_def_9_2 eq417 | grind only
  have eq422 : (old sk1 sk1 sk0) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq419 rule_def_9_3
    first | exact resolve eq419 rule_def_9_3 | exact resolve rule_def_9_3 eq419 | grind only
  have eq427 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq420 old_5
    first | exact resolve eq420 old_5 | exact resolve old_5 eq420 | grind only
  have eq428 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ b = sk1 := by
    clear * - eq420 old_4
    first | exact resolve eq420 old_4 | exact resolve old_4 eq420 | grind only
  have eq436 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq246 rule_def_11_2
    first | exact resolve eq246 rule_def_11_2 | exact resolve rule_def_11_2 eq246 | grind only
  have eq440 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq436 rule_def_1_0
    first | exact resolve eq436 rule_def_1_0 | exact resolve rule_def_1_0 eq436 | grind only
  have eq443 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq440 rule_def_2_1
    first | exact resolve eq440 rule_def_2_1 | exact resolve rule_def_2_1 eq440 | grind only
  have eq446 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq443 rule_def_3_1
    first | exact resolve eq443 rule_def_3_1 | exact resolve rule_def_3_1 eq443 | grind only
  have eq448 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq446 rule_def_4_1
    first | exact resolve eq446 rule_def_4_1 | exact resolve rule_def_4_1 eq446 | grind only
  have eq450 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq448 rule_def_8_2
    first | exact resolve eq448 rule_def_8_2 | exact resolve rule_def_8_2 eq448 | grind only
  have eq452 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq450 rule_def_9_2
    first | exact resolve eq450 rule_def_9_2 | exact resolve rule_def_9_2 eq450 | grind only
  have eq454 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq452 rule_def_10_2
    first | exact resolve eq452 rule_def_10_2 | exact resolve rule_def_10_2 eq452 | grind only
  have eq461 : (old sk0 sk1 sk0) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq422 old_4
    first | exact resolve eq422 old_4 | exact resolve old_4 eq422 | grind only
  have eq469 : (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq276 rule_def_11_2
    first | exact resolve eq276 rule_def_11_2 | exact resolve rule_def_11_2 eq276 | grind only
  have eq473 : (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq469 rule_def_1_0
    first | exact resolve eq469 rule_def_1_0 | exact resolve rule_def_1_0 eq469 | grind only
  have eq476 : (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq473 rule_def_2_1
    first | exact resolve eq473 rule_def_2_1 | exact resolve rule_def_2_1 eq473 | grind only
  have eq479 : (sP4 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq476 rule_def_3_1
    first | exact resolve eq476 rule_def_3_1 | exact resolve rule_def_3_1 eq476 | grind only
  have eq481 : (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq479 rule_def_4_1
    first | exact resolve eq479 rule_def_4_1 | exact resolve rule_def_4_1 eq479 | grind only
  have eq483 : (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq481 rule_def_8_2
    first | exact resolve eq481 rule_def_8_2 | exact resolve rule_def_8_2 eq481 | grind only
  have eq485 : (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq483 rule_def_9_2
    first | exact resolve eq483 rule_def_9_2 | exact resolve rule_def_9_2 eq483 | grind only
  have eq487 : (old sk1 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq485 rule_def_10_2
    first | exact resolve eq485 rule_def_10_2 | exact resolve rule_def_10_2 eq485 | grind only
  have eq502 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq240 rule_def_11_0
    first | exact resolve eq240 rule_def_11_0 | exact resolve rule_def_11_0 eq240 | grind only
  have eq503 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq502 rule_def_5_0
    first | exact resolve eq502 rule_def_5_0 | exact resolve rule_def_5_0 eq502 | grind only
  have eq506 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq503 rule_def_6_0
    first | exact resolve eq503 rule_def_6_0 | exact resolve rule_def_6_0 eq503 | grind only
  have eq509 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq506 rule_def_7_0
    first | exact resolve eq506 rule_def_7_0 | exact resolve rule_def_7_0 eq506 | grind only
  have eq512 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq509 rule_def_8_0
    first | exact resolve eq509 rule_def_8_0 | exact resolve rule_def_8_0 eq509 | grind only
  have eq515 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq512 rule_def_9_0
    first | exact resolve eq512 rule_def_9_0 | exact resolve rule_def_9_0 eq512 | grind only
  have eq518 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := by
    clear * - eq515 rule_def_10_0
    first | exact resolve eq515 rule_def_10_0 | exact resolve rule_def_10_0 eq515 | grind only
  have eq534 : (sP1 sk1 sk1 sk0) ∨ (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq270 rule_def_11_2
    first | exact resolve eq270 rule_def_11_2 | exact resolve rule_def_11_2 eq270 | grind only
  have eq538 : (sP2 sk1 sk1 sk0) ∨ (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq534 rule_def_1_0
    first | exact resolve eq534 rule_def_1_0 | exact resolve rule_def_1_0 eq534 | grind only
  have eq541 : (sP3 sk1 sk1 sk0) ∨ (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq538 rule_def_2_1
    first | exact resolve eq538 rule_def_2_1 | exact resolve rule_def_2_1 eq538 | grind only
  have eq544 : (sP4 sk1 sk1 sk0) ∨ (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq541 rule_def_3_1
    first | exact resolve eq541 rule_def_3_1 | exact resolve rule_def_3_1 eq541 | grind only
  have eq547 : (sP5 sk1 sk1 sk0) ∨ (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq544 rule_def_4_1
    first | exact resolve eq544 rule_def_4_1 | exact resolve rule_def_4_1 eq544 | grind only
  have eq550 : (sP6 sk1 sk1 sk0) ∨ (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq547 rule_def_5_1
    first | exact resolve eq547 rule_def_5_1 | exact resolve rule_def_5_1 eq547 | grind only
  have eq553 : (sP7 sk1 sk1 sk0) ∨ (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq550 rule_def_6_1
    first | exact resolve eq550 rule_def_6_1 | exact resolve rule_def_6_1 eq550 | grind only
  have eq555 : (sP8 sk1 sk1 sk0) ∨ (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq553 rule_def_7_1
    first | exact resolve eq553 rule_def_7_1 | exact resolve rule_def_7_1 eq553 | grind only
  have eq557 : (sP9 sk1 sk1 sk0) ∨ (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq555 rule_def_8_2
    first | exact resolve eq555 rule_def_8_2 | exact resolve rule_def_8_2 eq555 | grind only
  have eq558 : (sP10 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq557 rule_def_9_2
    first | exact resolve eq557 rule_def_9_2 | exact resolve rule_def_9_2 eq557 | grind only
  have eq559 : (old sk1 sk1 sk0) ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq558 rule_def_10_2
    first | exact resolve eq558 rule_def_10_2 | exact resolve rule_def_10_2 eq558 | grind only
  have eq564 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq487 old_5
    first | exact resolve eq487 old_5 | exact resolve old_5 eq487 | grind only
  have eq565 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq487 old_4
    first | exact resolve eq487 old_4 | exact resolve old_4 eq487 | grind only
  have eq586 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ a = sk1 := by
    clear * - eq559 old_4
    first | exact resolve eq559 old_4 | exact resolve old_4 eq559 | grind only
  have eq612 : (new sk0 sk0 sk1) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq427 imp_new_0
    first | exact resolve eq427 imp_new_0 | exact resolve imp_new_0 eq427 | grind only
  have eq620 : c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ sk0 = sk2 := by
    clear * - eq428 eq280
    first | exact resolve eq428 eq280 | exact resolve eq280 eq428 | grind only
  have eq630 : sk0 = sk2 ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq620
    first | exact resolve eq620 rfl | grind only
  have eq778 : (new sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq564 imp_new_0
    first | exact resolve eq564 imp_new_0 | exact resolve imp_new_0 eq564 | grind only
  have eq792 : (new sk0 sk1 sk0) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq565 imp_new_0
    first | exact resolve eq565 imp_new_0 | exact resolve imp_new_0 eq565 | grind only
  have eq902 : (new sk2 sk2 sk1) ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq612 eq630
    first | exact Or.assoc3 (eq630.imp_left (fun h : sk0 = sk2 => superpose h eq612)) | exact superpose eq612 eq630 | exact superpose eq630 eq612 | grind only
  have eq903 : (new sk2 sk2 sk1) ∨ b = sk1 ∨ c = sk1 := by
    clear * - eq902
    first | exact resolve eq902 rfl | grind only
  have eq904 : c = sk1 ∨ b = sk1 := by
    clear * - eq903 preserve_2
    first | exact resolve eq903 preserve_2 | exact resolve preserve_2 eq903 | grind only
  have eq927 : (old sk0 c sk2) ∨ c = b ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq267 eq904
    first | exact Or.assoc3 (eq904.imp_left (fun h : c = sk1 => superpose h eq267)) | exact superpose eq267 eq904 | exact superpose eq904 eq267 | grind only
  have eq940 : (old sk0 c sk0) ∨ b = sk0 ∨ c = b ∨ b = sk1 := by
    clear * - eq461 eq904
    first | exact Or.assoc3 (eq904.imp_left (fun h : c = sk1 => superpose h eq461)) | exact superpose eq461 eq904 | exact superpose eq904 eq461 | grind only
  have eq950 : b = sk0 ∨ c = b ∨ b = sk1 := by
    clear * - eq940 p4XZ
    first | exact resolve eq940 p4XZ | exact resolve p4XZ eq940 | grind only
  have eq960 : c = b ∨ b = sk2 ∨ b = sk1 := by
    clear * - eq927 p4XZ
    first | exact resolve eq927 p4XZ | exact resolve p4XZ eq927 | grind only
  have eq967 : b = sk0 ∨ b = sk1 := by
    clear * - eq950 bc
    first | exact resolve eq950 bc | exact resolve bc eq950 | grind only
  have eq976 : b = sk2 ∨ b = sk1 := by
    clear * - eq960 bc
    first | exact resolve eq960 bc | exact resolve bc eq960 | grind only
  have eq990 : (new sk1 sk1 b) ∨ b = sk1 := by
    clear * - preserve_1 eq967
    first | exact (eq967.imp_left (fun h : b = sk0 => superpose h preserve_1)) | exact superpose preserve_1 eq967 | exact superpose eq967 preserve_1 | grind only
  have eq1077 : ¬(new b b sk1) ∨ b = sk1 := by
    clear * - preserve_2 eq976
    first | exact (eq976.imp_left (fun h : b = sk2 => superpose h preserve_2)) | exact superpose preserve_2 eq976 | exact superpose eq976 preserve_2 | grind only
  have eq1212 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b ∨ c = sk0 := by
    clear * - eq518 rule_def_4_0
    first | exact resolve eq518 rule_def_4_0 | exact resolve rule_def_4_0 eq518 | grind only
  have eq1218 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b ∨ c = sk0 := by
    clear * - eq1212 rule_def_2_0
    first | exact resolve eq1212 rule_def_2_0 | exact resolve rule_def_2_0 eq1212 | grind only
  have eq1220 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b ∨ c = sk0 := by
    clear * - eq1218 rule_def_3_0
    first | exact resolve eq1218 rule_def_3_0 | exact resolve rule_def_3_0 eq1218 | grind only
  have eq1524 : sk0 = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq792 eq213
    first | exact resolve eq792 eq213 | exact resolve eq213 eq792 | grind only
  have eq1602 : (new sk2 sk2 sk1) ∨ c = sk2 ∨ c = sk1 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq778 eq1524
    first | exact Or.assoc3 (eq1524.imp_left (fun h : sk0 = sk2 => superpose h eq778)) | exact superpose eq778 eq1524 | exact superpose eq1524 eq778 | grind only
  have eq1610 : c ≠ sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq1524
    grind only
  have eq1612 : (new sk2 sk2 sk1) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq1602
    first | exact resolve eq1602 rfl | grind only
  have eq1636 : (new sk2 sk2 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq1612 eq1610
    first | exact resolve eq1612 eq1610 | exact resolve eq1610 eq1612 | grind only
  have eq1657 : c = sk0 ∨ c = sk1 := by
    clear * - eq1636 preserve_2
    first | exact resolve eq1636 preserve_2 | exact resolve preserve_2 eq1636 | grind only
  have eq1698 : (old c sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk1 := by
    clear * - eq454 eq1657
    first | exact Or.assoc3 (eq1657.imp_left (fun h : c = sk0 => superpose h eq454)) | exact superpose eq454 eq1657 | exact superpose eq1657 eq454 | grind only
  have eq1704 : (sP4 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (sP3 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = b ∨ c = sk1 := by
    clear * - eq518 eq1657
    first | exact Or.assoc7 (eq1657.imp_left (fun h : c = sk0 => superpose h eq518)) | exact superpose eq518 eq1657 | exact superpose eq1657 eq518 | grind only
  have eq1712 : (old c sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 := by
    clear * - eq586 eq1657
    first | exact Or.assoc3 (eq1657.imp_left (fun h : c = sk0 => superpose h eq586)) | exact superpose eq586 eq1657 | exact superpose eq1657 eq586 | grind only
  have eq1729 : (old c sk1 c) ∨ c = sk1 ∨ a = sk1 := by
    clear * - eq1712
    first | exact resolve eq1712 rfl | grind only
  have eq1734 : (old c sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq1698
    first | exact resolve eq1698 rfl | grind only
  have eq1745 : a = sk1 ∨ c = sk1 := by
    clear * - eq1729 p4XY
    first | exact resolve eq1729 p4XY | exact resolve p4XY eq1729 | grind only
  have eq1753 : (sP2 c sk1 sk2) ∨ (sP3 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = b ∨ c = sk1 := by
    clear * - eq1704 rule_def_4_1
    first | exact resolve eq1704 rule_def_4_1 | exact resolve rule_def_4_1 eq1704 | grind only
  have eq1756 : c = sk2 ∨ c = sk1 := by
    clear * - eq1734 p4YZ
    first | exact resolve eq1734 p4YZ | exact resolve p4YZ eq1734 | grind only
  have eq1769 : (sP3 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = b ∨ c = sk1 := by
    clear * - eq1753 rule_def_2_1
    first | exact resolve eq1753 rule_def_2_1 | exact resolve rule_def_2_1 eq1753 | grind only
  have eq1774 : (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = b ∨ c = sk1 := by
    clear * - eq1769 rule_def_3_1
    first | exact resolve eq1769 rule_def_3_1 | exact resolve rule_def_3_1 eq1769 | grind only
  have eq1776 : (old c sk1 sk2) ∨ a = c ∨ a = b ∨ c = sk1 := by
    clear * - eq1774 rule_def_1_0
    first | exact resolve eq1774 rule_def_1_0 | exact resolve rule_def_1_0 eq1774 | grind only
  have eq1778 : a = c ∨ a = b ∨ c = sk1 := by
    clear * - eq1776 p4YZ
    first | exact resolve eq1776 p4YZ | exact resolve p4YZ eq1776 | grind only
  have eq1780 : c = sk1 ∨ a = b := by
    clear * - eq1778 ac
    first | exact resolve eq1778 ac | exact resolve ac eq1778 | grind only
  have eq1794 : ¬(new sk2 sk2 a) ∨ c = sk1 := by
    clear * - preserve_2 eq1745
    first | exact (eq1745.imp_left (fun h : a = sk1 => superpose h preserve_2)) | exact superpose preserve_2 eq1745 | exact superpose eq1745 preserve_2 | grind only
  have eq1961 : (old sk0 c sk0) ∨ b = sk0 ∨ c = b ∨ a = b := by
    clear * - eq461 eq1780
    first | exact Or.assoc3 (eq1780.imp_left (fun h : c = sk1 => superpose h eq461)) | exact superpose eq461 eq1780 | exact superpose eq1780 eq461 | grind only
  have eq1976 : (new c c b) ∨ c = b ∨ a = b := by
    clear * - eq990 eq1780
    first | exact Or.assoc2 (eq1780.imp_left (fun h : c = sk1 => superpose h eq990)) | exact superpose eq990 eq1780 | exact superpose eq1780 eq990 | grind only
  have eq1991 : (new c c b) ∨ c = b := by
    clear * - eq1976 eq198
    first | exact resolve eq1976 eq198 | exact resolve eq198 eq1976 | grind only
  have eq2006 : b = sk0 ∨ c = b ∨ a = b := by
    clear * - eq1961 p4XZ
    first | exact resolve eq1961 p4XZ | exact resolve p4XZ eq1961 | grind only
  have eq2028 : (new c c b) := by
    clear * - eq1991 bc
    first | exact resolve eq1991 bc | exact resolve bc eq1991 | grind only
  have eq2033 : b = sk0 ∨ a = b := by
    clear * - eq2006 bc
    first | exact resolve eq2006 bc | exact resolve bc eq2006 | grind only
  have eq2301 : ¬(new c c a) ∨ c = sk1 ∨ c = sk1 := by
    clear * - eq1794 eq1756
    first | exact Or.assoc2 (eq1756.imp_left (fun h : c = sk2 => superpose h eq1794)) | exact superpose eq1794 eq1756 | exact superpose eq1756 eq1794 | grind only
  have eq2304 : ¬(new c c a) ∨ c = sk1 := by
    clear * - eq2301
    first | exact resolve eq2301 rfl | grind only
  have eq2941 : (sP1 b sk1 sk2) ∨ (old b sk1 sk2) ∨ a = b ∨ a = b ∨ c = b ∨ a = b := by
    clear * - eq1220 eq2033
    first | exact Or.assoc5 (eq2033.imp_left (fun h : b = sk0 => superpose h eq1220)) | exact superpose eq1220 eq2033 | exact superpose eq2033 eq1220 | grind only
  have eq2955 : (sP1 b sk1 sk2) ∨ (old b sk1 sk2) ∨ a = b ∨ c = b := by
    clear * - eq2941
    first | exact resolve eq2941 rfl | grind only
  have eq2956 : (old b sk1 sk2) ∨ a = b ∨ c = b := by
    clear * - eq2955 eq333
    first | exact resolve eq2955 eq333 | exact resolve eq333 eq2955 | grind only
  have eq2957 : (old b sk1 sk2) ∨ a = b := by
    clear * - eq2956 bc
    first | exact resolve eq2956 bc | exact resolve bc eq2956 | grind only
  have eq2964 : (old b c sk2) ∨ a = b ∨ a = b := by
    clear * - eq2957 eq1780
    first | exact Or.assoc2 (eq1780.imp_left (fun h : c = sk1 => superpose h eq2957)) | exact superpose eq2957 eq1780 | exact superpose eq1780 eq2957 | grind only
  have eq2972 : (old b c sk2) ∨ a = b := by
    clear * - eq2964
    first | exact resolve eq2964 rfl | grind only
  have eq2974 : a = b := by
    clear * - eq2972 p4XZ
    first | exact resolve eq2972 p4XZ | exact resolve p4XZ eq2972 | grind only
  have eq3003 : (new b b c) := by
    clear * - new_new eq2974
    first | exact superpose new_new eq2974 | exact superpose eq2974 new_new | grind only
  have eq3033 : ¬(new c c b) ∨ c = sk1 := by
    clear * - eq2304 eq2974
    first | exact superpose eq2304 eq2974 | exact superpose eq2974 eq2304 | grind only
  have eq3038 : c = sk1 := by
    clear * - eq3033 eq2028
    first | exact resolve eq3033 eq2028 | exact resolve eq2028 eq3033 | grind only
  have eq3160 : ¬(new b b c) ∨ c = b := by
    clear * - eq1077 eq3038
    first | exact superpose eq1077 eq3038 | exact superpose eq3038 eq1077 | grind only
  have eq3178 : c = b := by
    clear * - eq3160 eq3003
    first | exact resolve eq3160 eq3003 | exact resolve eq3003 eq3160 | grind only
  clear * - eq3178 bc
  first | subsumption eq3178 bc | grind only


set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_4 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X0 X1)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP4 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (imp_new_8 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), a = b ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_0 : ∀ (X Y Z : G), a = b ∨ ¬sP9 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (rule_def_10_0 : ∀ (X Y Z : G), a = b ∨ ¬sP10 X Y Z) (rule_def_10_1 : ∀ (X Y Z : G), c = X ∨ ¬sP10 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (imp_new_12 : ∀ X Y Z, a ≠ b ∨ b ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_11_1 : ∀ (X Y Z : G), b = X ∨ ¬sP11 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq187 (X1 X2 : G) : a ≠ b ∨ b ≠ X1 ∨ c ≠ X2 ∨ (new c X1 X2) := by
    clear * - imp_new_8
    first | exact resolve imp_new_8 rfl | grind only
  have eq188 (X2 : G) : a ≠ b ∨ c ≠ X2 ∨ (new c b X2) := by
    clear * - eq187
    first | exact resolve eq187 rfl | grind only
  have eq189 : a ≠ b ∨ (new c b c) := by
    clear * - eq188
    first | exact resolve eq188 rfl | grind only
  have eq199 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new b X1 X2) := by
    clear * - imp_new_12
    first | exact resolve imp_new_12 rfl | grind only
  have eq200 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new b c X2) := by
    clear * - eq199
    first | exact resolve eq199 rfl | grind only
  have eq201 : a ≠ b ∨ (new b c b) := by
    clear * - eq200
    first | exact resolve eq200 rfl | grind only
  have eq208 (X0 X1 : G) : ¬(sP1 c X0 X1) := by
    clear * - rule_def_1_2 p4YZ
    first | exact resolve rule_def_1_2 p4YZ | exact resolve p4YZ rule_def_1_2 | grind only
  have eq232 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq237 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq232 rule_def_0_2
    first | exact resolve eq232 rule_def_0_2 | exact resolve rule_def_0_2 eq232 | grind only
  have eq238 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq232 rule_def_0_1
    first | exact resolve eq232 rule_def_0_1 | exact resolve rule_def_0_1 eq232 | grind only
  have eq239 : (sP11 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 := by
    clear * - eq232 rule_def_0_0
    first | exact resolve eq232 rule_def_0_0 | exact resolve rule_def_0_0 eq232 | grind only
  have eq240 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq238 rule_def_5_2
    first | exact resolve eq238 rule_def_5_2 | exact resolve rule_def_5_2 eq238 | grind only
  have eq241 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq237 rule_def_5_3
    first | exact resolve eq237 rule_def_5_3 | exact resolve rule_def_5_3 eq237 | grind only
  have eq242 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq240 rule_def_6_2
    first | exact resolve eq240 rule_def_6_2 | exact resolve rule_def_6_2 eq240 | grind only
  have eq243 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq241 rule_def_6_3
    first | exact resolve eq241 rule_def_6_3 | exact resolve rule_def_6_3 eq241 | grind only
  have eq244 : (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (sP11 sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq242 rule_def_7_2
    first | exact resolve eq242 rule_def_7_2 | exact resolve rule_def_7_2 eq242 | grind only
  have eq245 : (sP11 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 := by
    clear * - eq243 rule_def_7_3
    first | exact resolve eq243 rule_def_7_3 | exact resolve rule_def_7_3 eq243 | grind only
  have eq246 : (sP10 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := by
    clear * - eq244 rule_def_11_1
    first | exact resolve eq244 rule_def_11_1 | exact resolve rule_def_11_1 eq244 | grind only
  have eq252 : (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq246 rule_def_10_3
    first | exact resolve eq246 rule_def_10_3 | exact resolve rule_def_10_3 eq246 | grind only
  have eq254 : (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq246 rule_def_10_1
    first | exact resolve eq246 rule_def_10_1 | exact resolve rule_def_10_1 eq246 | grind only
  have eq255 : (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b := by
    clear * - eq246 rule_def_10_0
    first | exact resolve eq246 rule_def_10_0 | exact resolve rule_def_10_0 eq246 | grind only
  have eq256 : (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b := by
    clear * - eq255 rule_def_8_0
    first | exact resolve eq255 rule_def_8_0 | exact resolve rule_def_8_0 eq255 | grind only
  have eq257 : (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq254 rule_def_1_0
    first | exact resolve eq254 rule_def_1_0 | exact resolve rule_def_1_0 eq254 | grind only
  have eq259 : (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq252 rule_def_1_1
    first | exact resolve eq252 rule_def_1_1 | exact resolve rule_def_1_1 eq252 | grind only
  have eq260 : (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b := by
    clear * - eq256 rule_def_9_0
    first | exact resolve eq256 rule_def_9_0 | exact resolve rule_def_9_0 eq256 | grind only
  have eq261 : (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq257 rule_def_2_1
    first | exact resolve eq257 rule_def_2_1 | exact resolve rule_def_2_1 eq257 | grind only
  have eq263 : (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq259 rule_def_2_2
    first | exact resolve eq259 rule_def_2_2 | exact resolve rule_def_2_2 eq259 | grind only
  have eq264 : (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq261 rule_def_3_1
    first | exact resolve eq261 rule_def_3_1 | exact resolve rule_def_3_1 eq261 | grind only
  have eq266 : (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq263 rule_def_3_2
    first | exact resolve eq263 rule_def_3_2 | exact resolve rule_def_3_2 eq263 | grind only
  have eq267 : (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq264 rule_def_4_1
    first | exact resolve eq264 rule_def_4_1 | exact resolve rule_def_4_1 eq264 | grind only
  have eq269 : (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq266 rule_def_4_2
    first | exact resolve eq266 rule_def_4_2 | exact resolve rule_def_4_2 eq266 | grind only
  have eq270 : (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq267 rule_def_8_2
    first | exact resolve eq267 rule_def_8_2 | exact resolve rule_def_8_2 eq267 | grind only
  have eq272 : (sP9 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq269 rule_def_8_3
    first | exact resolve eq269 rule_def_8_3 | exact resolve rule_def_8_3 eq269 | grind only
  have eq273 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := by
    clear * - eq270 rule_def_9_2
    first | exact resolve eq270 rule_def_9_2 | exact resolve rule_def_9_2 eq270 | grind only
  have eq275 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ b = sk1 := by
    clear * - eq272 rule_def_9_3
    first | exact resolve eq272 rule_def_9_3 | exact resolve rule_def_9_3 eq272 | grind only
  have eq283 : (old sk1 sk0 sk1) ∨ c = sk0 ∨ b = sk0 := by
    clear * - eq273 old_4
    first | exact resolve eq273 old_4 | exact resolve old_4 eq273 | grind only
  have eq329 : c = sk0 ∨ b = sk0 ∨ (new sk1 sk0 sk1) := by
    clear * - eq283 imp_new_0
    first | exact resolve eq283 imp_new_0 | exact resolve imp_new_0 eq283 | grind only
  have eq330 : c = sk0 ∨ b = sk0 := by
    clear * - eq329 preserve_1
    first | exact resolve eq329 preserve_1 | exact resolve preserve_1 eq329 | grind only
  have eq336 : ¬(new sk1 c sk1) ∨ b = sk0 := by
    clear * - preserve_1 eq330
    first | exact (eq330.imp_left (fun h : c = sk0 => superpose h preserve_1)) | exact superpose preserve_1 eq330 | exact superpose eq330 preserve_1 | grind only
  have eq342 : (old c c sk1) ∨ c = b ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq275 eq330
    first | exact Or.assoc3 (eq330.imp_left (fun h : c = sk0 => superpose h eq275)) | exact superpose eq275 eq330 | exact superpose eq330 eq275 | grind only
  have eq344 : c = b ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq342 p4XZ
    first | exact resolve eq342 p4XZ | exact resolve p4XZ eq342 | grind only
  have eq347 : b = sk1 ∨ b = sk0 := by
    clear * - eq344 bc
    first | exact resolve eq344 bc | exact resolve bc eq344 | grind only
  have eq380 : ¬(new b c b) ∨ b = sk0 ∨ b = sk0 := by
    clear * - eq336 eq347
    first | exact Or.assoc2 (eq347.imp_left (fun h : b = sk1 => superpose h eq336)) | exact superpose eq336 eq347 | exact superpose eq347 eq336 | grind only
  have eq381 : ¬(new b c b) ∨ b = sk0 := by
    clear * - eq380
    first | exact resolve eq380 rfl | grind only
  have eq406 : (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq245 rule_def_11_2
    first | exact resolve eq245 rule_def_11_2 | exact resolve rule_def_11_2 eq245 | grind only
  have eq412 : (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq406 rule_def_1_0
    first | exact resolve eq406 rule_def_1_0 | exact resolve rule_def_1_0 eq406 | grind only
  have eq415 : (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq412 rule_def_2_1
    first | exact resolve eq412 rule_def_2_1 | exact resolve rule_def_2_1 eq412 | grind only
  have eq418 : (sP4 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq415 rule_def_3_1
    first | exact resolve eq415 rule_def_3_1 | exact resolve rule_def_3_1 eq415 | grind only
  have eq420 : (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq418 rule_def_4_1
    first | exact resolve eq418 rule_def_4_1 | exact resolve rule_def_4_1 eq418 | grind only
  have eq422 : (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq420 rule_def_8_2
    first | exact resolve eq420 rule_def_8_2 | exact resolve rule_def_8_2 eq420 | grind only
  have eq424 : (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq422 rule_def_9_2
    first | exact resolve eq422 rule_def_9_2 | exact resolve rule_def_9_2 eq422 | grind only
  have eq426 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq424 rule_def_10_2
    first | exact resolve eq424 rule_def_10_2 | exact resolve rule_def_10_2 eq424 | grind only
  have eq429 : (sP1 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq239 rule_def_11_2
    first | exact resolve eq239 rule_def_11_2 | exact resolve rule_def_11_2 eq239 | grind only
  have eq435 : (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq429 rule_def_1_0
    first | exact resolve eq429 rule_def_1_0 | exact resolve rule_def_1_0 eq429 | grind only
  have eq438 : (sP3 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq435 rule_def_2_1
    first | exact resolve eq435 rule_def_2_1 | exact resolve rule_def_2_1 eq435 | grind only
  have eq441 : (sP4 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq438 rule_def_3_1
    first | exact resolve eq438 rule_def_3_1 | exact resolve rule_def_3_1 eq438 | grind only
  have eq444 : (sP5 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq441 rule_def_4_1
    first | exact resolve eq441 rule_def_4_1 | exact resolve rule_def_4_1 eq441 | grind only
  have eq447 : (sP6 sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq444 rule_def_5_1
    first | exact resolve eq444 rule_def_5_1 | exact resolve rule_def_5_1 eq444 | grind only
  have eq450 : (sP7 sk0 sk0 sk1) ∨ (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq447 rule_def_6_1
    first | exact resolve eq447 rule_def_6_1 | exact resolve rule_def_6_1 eq447 | grind only
  have eq452 : (sP8 sk0 sk0 sk1) ∨ (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq450 rule_def_7_1
    first | exact resolve eq450 rule_def_7_1 | exact resolve rule_def_7_1 eq450 | grind only
  have eq454 : (sP9 sk0 sk0 sk1) ∨ (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq452 rule_def_8_2
    first | exact resolve eq452 rule_def_8_2 | exact resolve rule_def_8_2 eq452 | grind only
  have eq455 : (sP10 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq454 rule_def_9_2
    first | exact resolve eq454 rule_def_9_2 | exact resolve rule_def_9_2 eq454 | grind only
  have eq456 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq455 rule_def_10_2
    first | exact resolve eq455 rule_def_10_2 | exact resolve rule_def_10_2 eq455 | grind only
  have eq460 : (old sk1 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := by
    clear * - eq426 old_4
    first | exact resolve eq426 old_4 | exact resolve old_4 eq426 | grind only
  have eq545 : c = sk0 ∨ c = sk1 ∨ (new sk1 sk0 sk1) := by
    clear * - eq460 imp_new_0
    first | exact resolve eq460 imp_new_0 | exact resolve imp_new_0 eq460 | grind only
  have eq547 : c = sk1 ∨ c = sk0 := by
    clear * - eq545 preserve_1
    first | exact resolve eq545 preserve_1 | exact resolve preserve_1 eq545 | grind only
  have eq553 : ¬(new c sk0 c) ∨ c = sk0 := by
    clear * - preserve_1 eq547
    first | exact (eq547.imp_left (fun h : c = sk1 => superpose h preserve_1)) | exact superpose preserve_1 eq547 | exact superpose eq547 preserve_1 | grind only
  have eq569 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 := by
    clear * - eq456 eq547
    first | exact Or.assoc3 (eq547.imp_left (fun h : c = sk1 => superpose h eq456)) | exact superpose eq456 eq547 | exact superpose eq547 eq456 | grind only
  have eq570 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 := by
    clear * - eq569
    first | exact resolve eq569 rfl | grind only
  have eq575 : a = sk0 ∨ c = sk0 := by
    clear * - eq570 p4XY
    first | exact resolve eq570 p4XY | exact resolve p4XY eq570 | grind only
  have eq611 : a = c ∨ a = b ∨ c = sk0 := by
    clear * - eq330 eq575
    first | exact Or.assoc2 (eq575.imp_left (fun h : a = sk0 => superpose h eq330)) | exact superpose eq330 eq575 | exact superpose eq575 eq330 | grind only
  have eq620 : c = sk0 ∨ a = b := by
    clear * - eq611 ac
    first | exact resolve eq611 ac | exact resolve ac eq611 | grind only
  have eq860 : (sP2 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b ∨ (old b b a) := by
    clear * - eq260 rule_def_4_3
    first | exact resolve eq260 rule_def_4_3 | exact resolve rule_def_4_3 eq260 | grind only
  have eq874 : (sP3 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b ∨ (old b b a) := by
    clear * - eq860 rule_def_2_3
    first | exact resolve eq860 rule_def_2_3 | exact resolve rule_def_2_3 eq860 | grind only
  have eq875 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b ∨ (old b b a) := by
    clear * - eq874 rule_def_3_3
    first | exact resolve eq874 rule_def_3_3 | exact resolve rule_def_3_3 eq874 | grind only
  have eq1631 : (sP1 c c sk1) ∨ (old c c sk1) ∨ c = b ∨ a = b ∨ (old b b a) ∨ a = b := by
    clear * - eq875 eq620
    first | exact Or.assoc5 (eq620.imp_left (fun h : c = sk0 => superpose h eq875)) | exact superpose eq875 eq620 | exact superpose eq620 eq875 | grind only
  have eq1643 : (sP1 c c sk1) ∨ (old c c sk1) ∨ c = b ∨ a = b ∨ (old b b a) := by
    clear * - eq1631
    first | exact resolve eq1631 rfl | grind only
  have eq1645 : (old c c sk1) ∨ c = b ∨ a = b ∨ (old b b a) := by
    clear * - eq1643 eq208
    first | exact resolve eq1643 eq208 | exact resolve eq208 eq1643 | grind only
  have eq1647 : c = b ∨ a = b ∨ (old b b a) := by
    clear * - eq1645 p4XZ
    first | exact resolve eq1645 p4XZ | exact resolve p4XZ eq1645 | grind only
  have eq1649 : (old b b a) ∨ a = b := by
    clear * - eq1647 bc
    first | exact resolve eq1647 bc | exact resolve bc eq1647 | grind only
  have eq1655 : a = b ∨ (old a b a) := by
    clear * - eq1649 old_4
    first | exact resolve eq1649 old_4 | exact resolve old_4 eq1649 | grind only
  have eq1660 : a = b := by
    clear * - eq1655 p3
    first | exact resolve eq1655 p3 | exact resolve p3 eq1655 | grind only
  have eq1684 : b ≠ b ∨ (new c b c) := by
    clear * - eq189 eq1660
    first | exact superpose eq189 eq1660 | exact superpose eq1660 eq189 | grind only
  have eq1686 : b ≠ b ∨ (new b c b) := by
    clear * - eq201 eq1660
    first | exact superpose eq201 eq1660 | exact superpose eq1660 eq201 | grind only
  have eq1715 : (new b c b) := by
    clear * - eq1686
    first | exact resolve eq1686 rfl | grind only
  have eq1717 : (new c b c) := by
    clear * - eq1684
    first | exact resolve eq1684 rfl | grind only
  have eq1789 : b = sk0 := by
    clear * - eq1715 eq381
    first | exact resolve eq1715 eq381 | exact resolve eq381 eq1715 | grind only
  have eq1845 : ¬(new c b c) ∨ c = b := by
    clear * - eq553 eq1789
    first | exact superpose eq553 eq1789 | exact superpose eq1789 eq553 | grind only
  have eq1872 : c = b := by
    clear * - eq1845 eq1717
    first | exact resolve eq1845 eq1717 | exact resolve eq1717 eq1845 | grind only
  clear * - eq1872 bc
  first | subsumption eq1872 bc | grind only


set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (prev_3 : (∀ X0 X1 X2, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X0 ∨ new X2 X2 X1)) (prev_4 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X0 X1)) : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X1 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq204 : (new sk1 sk0 sk1) := by
    clear * - prev_4 preserve_0
    first | exact resolve prev_4 preserve_0 | exact resolve preserve_0 prev_4 | grind only
  have eq223 (X0 : G) : ¬(new sk1 sk0 X0) ∨ (new X0 X0 sk0) := by
    clear * - prev_3 preserve_0
    first | exact resolve prev_3 preserve_0 | exact resolve preserve_0 prev_3 | grind only
  have eq224 : (new sk1 sk1 sk0) := by
    clear * - eq223 eq204
    first | exact resolve eq223 eq204 | exact resolve eq204 eq223 | grind only
  clear * - eq224 preserve_1
  first | subsumption eq224 preserve_1 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_6_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (prev_4 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X0 X1)) (prev_5 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X1 X0)) : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X0 X1 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq207 : (new sk1 sk1 sk0) := by
    clear * - prev_5 preserve_0
    first | exact resolve prev_5 preserve_0 | exact resolve preserve_0 prev_5 | grind only
  have eq210 : (new sk0 sk1 sk0) := by
    clear * - eq207 prev_4
    first | exact resolve eq207 prev_4 | exact resolve prev_4 eq207 | grind only
  clear * - eq210 preserve_1
  first | subsumption eq210 preserve_1 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_7_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (bc : c ≠ b) (old_7 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X1 X1)) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X1 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq248 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq254 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq248 rule_def_0_2
    first | exact resolve eq248 rule_def_0_2 | exact resolve rule_def_0_2 eq248 | grind only
  have eq255 : (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq248 rule_def_0_1
    first | exact resolve eq248 rule_def_0_1 | exact resolve rule_def_0_1 eq248 | grind only
  have eq257 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq255 rule_def_1_1
    first | exact resolve eq255 rule_def_1_1 | exact resolve rule_def_1_1 eq255 | grind only
  have eq258 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq254 rule_def_1_0
    first | exact resolve eq254 rule_def_1_0 | exact resolve rule_def_1_0 eq254 | grind only
  have eq259 : (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq257 rule_def_2_2
    first | exact resolve eq257 rule_def_2_2 | exact resolve rule_def_2_2 eq257 | grind only
  have eq260 : (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq258 rule_def_2_1
    first | exact resolve eq258 rule_def_2_1 | exact resolve rule_def_2_1 eq258 | grind only
  have eq261 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq259 rule_def_3_2
    first | exact resolve eq259 rule_def_3_2 | exact resolve rule_def_3_2 eq259 | grind only
  have eq262 : (old sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq260 rule_def_3_1
    first | exact resolve eq260 rule_def_3_1 | exact resolve rule_def_3_1 eq260 | grind only
  have eq263 : (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq261 rule_def_4_2
    first | exact resolve eq261 rule_def_4_2 | exact resolve rule_def_4_2 eq261 | grind only
  have eq264 : (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq262 rule_def_4_1
    first | exact resolve eq262 rule_def_4_1 | exact resolve rule_def_4_1 eq262 | grind only
  have eq265 : (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq263 rule_def_5_2
    first | exact resolve eq263 rule_def_5_2 | exact resolve rule_def_5_2 eq263 | grind only
  have eq266 : (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq264 rule_def_5_3
    first | exact resolve eq264 rule_def_5_3 | exact resolve rule_def_5_3 eq264 | grind only
  have eq267 : (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq265 rule_def_6_2
    first | exact resolve eq265 rule_def_6_2 | exact resolve rule_def_6_2 eq265 | grind only
  have eq268 : (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq266 rule_def_6_3
    first | exact resolve eq266 rule_def_6_3 | exact resolve rule_def_6_3 eq266 | grind only
  have eq269 : (old sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq267 rule_def_7_2
    first | exact resolve eq267 rule_def_7_2 | exact resolve rule_def_7_2 eq267 | grind only
  have eq270 : (old sk0 sk1 sk1) ∨ (sP8 sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq268 rule_def_7_3
    first | exact resolve eq268 rule_def_7_3 | exact resolve rule_def_7_3 eq268 | grind only
  have eq271 : (old sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq269 rule_def_8_3
    first | exact resolve eq269 rule_def_8_3 | exact resolve rule_def_8_3 eq269 | grind only
  have eq272 : (old sk0 sk1 sk1) ∨ (sP9 sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq270 rule_def_8_2
    first | exact resolve eq270 rule_def_8_2 | exact resolve rule_def_8_2 eq270 | grind only
  have eq273 : (old sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq271 rule_def_9_3
    first | exact resolve eq271 rule_def_9_3 | exact resolve rule_def_9_3 eq271 | grind only
  have eq274 : (old sk0 sk1 sk1) ∨ (sP10 sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq272 rule_def_9_2
    first | exact resolve eq272 rule_def_9_2 | exact resolve rule_def_9_2 eq272 | grind only
  have eq275 : (old sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq273 rule_def_10_3
    first | exact resolve eq273 rule_def_10_3 | exact resolve rule_def_10_3 eq273 | grind only
  have eq276 : (old sk0 sk1 sk1) ∨ (sP11 sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq274 rule_def_10_2
    first | exact resolve eq274 rule_def_10_2 | exact resolve rule_def_10_2 eq274 | grind only
  have eq277 : (old sk0 sk1 sk1) ∨ b = sk1 := by
    clear * - eq275 rule_def_11_3
    first | exact resolve eq275 rule_def_11_3 | exact resolve rule_def_11_3 eq275 | grind only
  have eq278 : (old sk0 sk1 sk1) ∨ c = sk1 := by
    clear * - eq276 rule_def_11_2
    first | exact resolve eq276 rule_def_11_2 | exact resolve rule_def_11_2 eq276 | grind only
  have eq281 : (old sk1 sk1 sk1) ∨ b = sk1 := by
    clear * - eq277 old_7
    first | exact resolve eq277 old_7 | exact resolve old_7 eq277 | grind only
  have eq308 : b = sk1 ∨ (new sk1 sk1 sk1) := by
    clear * - eq281 imp_new_0
    first | exact resolve eq281 imp_new_0 | exact resolve imp_new_0 eq281 | grind only
  have eq309 : b = sk1 := by
    clear * - eq308 preserve_1
    first | exact resolve eq308 preserve_1 | exact resolve preserve_1 eq308 | grind only
  have eq317 : ¬(new b b b) := by
    clear * - preserve_1 eq309
    first | exact superpose preserve_1 eq309 | exact superpose eq309 preserve_1 | grind only
  have eq321 : (old sk0 b b) ∨ c = b := by
    clear * - eq278 eq309
    first | exact superpose eq278 eq309 | exact superpose eq309 eq278 | grind only
  have eq322 : (old sk0 b b) := by
    clear * - eq321 bc
    first | exact resolve eq321 bc | exact resolve bc eq321 | grind only
  have eq335 : (old b b b) := by
    clear * - eq322 old_7
    first | exact resolve eq322 old_7 | exact resolve old_7 eq322 | grind only
  have eq357 : (new b b b) := by
    clear * - eq335 imp_new_0
    first | exact resolve eq335 imp_new_0 | exact resolve imp_new_0 eq335 | grind only
  clear * - eq357 eq317
  first | subsumption eq357 eq317 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_8_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (new_new : new a b c) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X3 ∨ ¬ new X3 X1 X4 ∨ new X0 X4 X1)) (prev_2 : (∀ X0 X1, ¬ new X0 X1 X0 ∨ new X1 X1 X0)) (prev_5 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X1 X0)) (prev_7 : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X1 X1)) (old_8 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X3 ∨ ¬ old X2 X1 X4 ∨ ¬ old X2 X4 X3 ∨ old X1 X1 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ b ≠ Z ∨ ¬ old X b X2 ∨ ¬ old X X2 a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z, c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ ¬ old b b a ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), a = b ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), c = X ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_0 : ∀ (X Y Z : G), a = b ∨ ¬sP9 X Y Z) (rule_def_9_1 : ∀ (X Y Z : G), c = X ∨ ¬sP9 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (imp_new_11 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_10_0 : ∀ (X Y Z : G), a = b ∨ ¬sP10 X Y Z) (rule_def_10_1 : ∀ (X Y Z : G), c = X ∨ ¬sP10 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (imp_new_12 : ∀ X Y Z, a ≠ b ∨ b ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_11_0 : ∀ (X Y Z : G), a = b ∨ ¬sP11 X Y Z) (rule_def_11_1 : ∀ (X Y Z : G), b = X ∨ ¬sP11 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X3 ∨ ¬ new X2 X1 X4 ∨ ¬ new X2 X4 X3 ∨ new X1 X1 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq184 (X0 X2 X3 : G) : b ≠ X2 ∨ ¬(old X0 b X3) ∨ ¬(old X0 X3 a) ∨ (new X0 c X2) := by
    clear * - imp_new_2
    first | exact resolve imp_new_2 rfl | grind only
  have eq185 (X0 X3 : G) : ¬(old X0 b X3) ∨ ¬(old X0 X3 a) ∨ (new X0 c b) := by
    clear * - eq184
    first | exact resolve eq184 rfl | grind only
  have eq192 (X1 X2 : G) : c ≠ X1 ∨ b ≠ X2 ∨ ¬(old b b a) ∨ (new c X1 X2) := by
    clear * - imp_new_5
    first | exact resolve imp_new_5 rfl | grind only
  have eq193 (X2 : G) : b ≠ X2 ∨ ¬(old b b a) ∨ (new c c X2) := by
    clear * - eq192
    first | exact resolve eq192 rfl | grind only
  have eq194 : ¬(old b b a) ∨ (new c c b) := by
    clear * - eq193
    first | exact resolve eq193 rfl | grind only
  have eq210 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new c X1 X2) := by
    clear * - imp_new_11
    first | exact resolve imp_new_11 rfl | grind only
  have eq211 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new c c X2) := by
    clear * - eq210
    first | exact resolve eq210 rfl | grind only
  have eq212 : a ≠ b ∨ (new c c b) := by
    clear * - eq211
    first | exact resolve eq211 rfl | grind only
  have eq213 (X1 X2 : G) : a ≠ b ∨ c ≠ X1 ∨ b ≠ X2 ∨ (new b X1 X2) := by
    clear * - imp_new_12
    first | exact resolve imp_new_12 rfl | grind only
  have eq214 (X2 : G) : a ≠ b ∨ b ≠ X2 ∨ (new b c X2) := by
    clear * - eq213
    first | exact resolve eq213 rfl | grind only
  have eq215 : a ≠ b ∨ (new b c b) := by
    clear * - eq214
    first | exact resolve eq214 rfl | grind only
  have eq221 (X0 X1 : G) : ¬(sP1 a X0 X1) := by
    clear * - rule_def_1_2 p3
    first | exact resolve rule_def_1_2 p3 | exact resolve p3 rule_def_1_2 | grind only
  have eq229 (X0 : G) : ¬(new sk2 sk1 X0) ∨ sk4 = X0 := by
    clear * - prev_0 preserve_2
    first | exact resolve prev_0 preserve_2 | exact resolve preserve_2 prev_0 | grind only
  have eq230 (X0 : G) : ¬(new sk2 sk4 X0) ∨ sk3 = X0 := by
    clear * - prev_0 preserve_3
    first | exact resolve prev_0 preserve_3 | exact resolve preserve_3 prev_0 | grind only
  have eq231 (X0 : G) : ¬(new a b X0) ∨ c = X0 := by
    clear * - prev_0 new_new
    first | exact resolve prev_0 new_new | exact resolve new_new prev_0 | grind only
  have eq236 (X0 X1 X2 : G) : ¬(old X0 (sF0 X0 X1 X2) a) ∨ (new X0 c b) ∨ ¬(sP1 X0 X1 X2) := by
    clear * - eq185 rule_def_1_2
    first | exact resolve eq185 rule_def_1_2 | exact resolve rule_def_1_2 eq185 | grind only
  have eq237 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c b) := by
    clear * - eq236 rule_def_1_3
    first | exact resolve eq236 rule_def_1_3 | exact resolve rule_def_1_3 eq236 | grind only
  have eq244 (X0 X1 : G) : ¬(new X0 sk1 X1) ∨ ¬(new X0 X1 sk2) ∨ (new X0 sk4 sk1) := by
    clear * - prev_1 preserve_2
    first | exact resolve prev_1 preserve_2 | exact resolve preserve_2 prev_1 | grind only
  have eq251 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq252 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) := by
    clear * - new_imp preserve_1
    first | exact resolve new_imp preserve_1 | exact resolve preserve_1 new_imp | grind only
  have eq253 : (sP0 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (sP11 sk2 sk1 sk4) := by
    clear * - new_imp preserve_2
    first | exact resolve new_imp preserve_2 | exact resolve preserve_2 new_imp | grind only
  have eq254 : (sP0 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) := by
    clear * - new_imp preserve_3
    first | exact resolve new_imp preserve_3 | exact resolve preserve_3 new_imp | grind only
  have eq262 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq251 rule_def_0_2
    first | exact resolve eq251 rule_def_0_2 | exact resolve rule_def_0_2 eq251 | grind only
  have eq263 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq251 rule_def_0_1
    first | exact resolve eq251 rule_def_0_1 | exact resolve rule_def_0_1 eq251 | grind only
  have eq265 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq263 rule_def_5_2
    first | exact resolve eq263 rule_def_5_2 | exact resolve rule_def_5_2 eq263 | grind only
  have eq266 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq262 rule_def_5_3
    first | exact resolve eq262 rule_def_5_3 | exact resolve rule_def_5_3 eq262 | grind only
  have eq267 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq265 rule_def_6_2
    first | exact resolve eq265 rule_def_6_2 | exact resolve rule_def_6_2 eq265 | grind only
  have eq268 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq266 rule_def_6_3
    first | exact resolve eq266 rule_def_6_3 | exact resolve rule_def_6_3 eq266 | grind only
  have eq269 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq267 rule_def_7_2
    first | exact resolve eq267 rule_def_7_2 | exact resolve rule_def_7_2 eq267 | grind only
  have eq270 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq268 rule_def_7_3
    first | exact resolve eq268 rule_def_7_3 | exact resolve rule_def_7_3 eq268 | grind only
  have eq271 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq252 rule_def_0_2
    first | exact resolve eq252 rule_def_0_2 | exact resolve rule_def_0_2 eq252 | grind only
  have eq272 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP5 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq252 rule_def_0_1
    first | exact resolve eq252 rule_def_0_1 | exact resolve rule_def_0_1 eq252 | grind only
  have eq274 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq272 rule_def_5_2
    first | exact resolve eq272 rule_def_5_2 | exact resolve rule_def_5_2 eq272 | grind only
  have eq275 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP6 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq271 rule_def_5_3
    first | exact resolve eq271 rule_def_5_3 | exact resolve rule_def_5_3 eq271 | grind only
  have eq276 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq274 rule_def_6_2
    first | exact resolve eq274 rule_def_6_2 | exact resolve rule_def_6_2 eq274 | grind only
  have eq277 : (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP7 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (sP11 sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq275 rule_def_6_3
    first | exact resolve eq275 rule_def_6_3 | exact resolve rule_def_6_3 eq275 | grind only
  have eq278 : (sP11 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 := by
    clear * - eq276 rule_def_7_2
    first | exact resolve eq276 rule_def_7_2 | exact resolve rule_def_7_2 eq276 | grind only
  have eq279 : (sP11 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 := by
    clear * - eq277 rule_def_7_3
    first | exact resolve eq277 rule_def_7_3 | exact resolve rule_def_7_3 eq277 | grind only
  have eq280 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq269 rule_def_11_3
    first | exact resolve eq269 rule_def_11_3 | exact resolve rule_def_11_3 eq269 | grind only
  have eq286 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq280 rule_def_1_1
    first | exact resolve eq280 rule_def_1_1 | exact resolve rule_def_1_1 eq280 | grind only
  have eq289 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq286 rule_def_2_2
    first | exact resolve eq286 rule_def_2_2 | exact resolve rule_def_2_2 eq286 | grind only
  have eq292 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq289 rule_def_3_2
    first | exact resolve eq289 rule_def_3_2 | exact resolve rule_def_3_2 eq289 | grind only
  have eq294 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq292 rule_def_4_2
    first | exact resolve eq292 rule_def_4_2 | exact resolve rule_def_4_2 eq292 | grind only
  have eq296 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq294 rule_def_8_3
    first | exact resolve eq294 rule_def_8_3 | exact resolve rule_def_8_3 eq294 | grind only
  have eq298 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq296 rule_def_9_3
    first | exact resolve eq296 rule_def_9_3 | exact resolve rule_def_9_3 eq296 | grind only
  have eq300 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq298 rule_def_10_3
    first | exact resolve eq298 rule_def_10_3 | exact resolve rule_def_10_3 eq298 | grind only
  have eq301 : (old sk2 sk1 sk4) ∨ (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (sP11 sk2 sk1 sk4) ∨ c = sk4 := by
    clear * - eq253 rule_def_0_2
    first | exact resolve eq253 rule_def_0_2 | exact resolve rule_def_0_2 eq253 | grind only
  have eq303 : (sP11 sk2 sk1 sk4) ∨ (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 := by
    clear * - eq253 rule_def_0_0
    first | exact resolve eq253 rule_def_0_0 | exact resolve rule_def_0_0 eq253 | grind only
  have eq305 : (old sk2 sk1 sk4) ∨ (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (sP11 sk2 sk1 sk4) ∨ c = sk4 := by
    clear * - eq301 rule_def_5_3
    first | exact resolve eq301 rule_def_5_3 | exact resolve rule_def_5_3 eq301 | grind only
  have eq307 : (old sk2 sk1 sk4) ∨ (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (sP11 sk2 sk1 sk4) ∨ c = sk4 := by
    clear * - eq305 rule_def_6_3
    first | exact resolve eq305 rule_def_6_3 | exact resolve rule_def_6_3 eq305 | grind only
  have eq309 : (sP11 sk2 sk1 sk4) ∨ (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 := by
    clear * - eq307 rule_def_7_3
    first | exact resolve eq307 rule_def_7_3 | exact resolve rule_def_7_3 eq307 | grind only
  have eq314 : (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) ∨ c = sk3 := by
    clear * - eq254 rule_def_0_2
    first | exact resolve eq254 rule_def_0_2 | exact resolve rule_def_0_2 eq254 | grind only
  have eq315 : (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) ∨ b = sk4 := by
    clear * - eq254 rule_def_0_1
    first | exact resolve eq254 rule_def_0_1 | exact resolve rule_def_0_1 eq254 | grind only
  have eq316 : (sP11 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 := by
    clear * - eq254 rule_def_0_0
    first | exact resolve eq254 rule_def_0_0 | exact resolve rule_def_0_0 eq254 | grind only
  have eq317 : (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) ∨ b = sk4 := by
    clear * - eq315 rule_def_5_2
    first | exact resolve eq315 rule_def_5_2 | exact resolve rule_def_5_2 eq315 | grind only
  have eq318 : (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) ∨ c = sk3 := by
    clear * - eq314 rule_def_5_3
    first | exact resolve eq314 rule_def_5_3 | exact resolve rule_def_5_3 eq314 | grind only
  have eq319 : (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) ∨ b = sk4 := by
    clear * - eq317 rule_def_6_2
    first | exact resolve eq317 rule_def_6_2 | exact resolve rule_def_6_2 eq317 | grind only
  have eq320 : (old sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (sP11 sk2 sk4 sk3) ∨ c = sk3 := by
    clear * - eq318 rule_def_6_3
    first | exact resolve eq318 rule_def_6_3 | exact resolve rule_def_6_3 eq318 | grind only
  have eq321 : (sP11 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 := by
    clear * - eq319 rule_def_7_2
    first | exact resolve eq319 rule_def_7_2 | exact resolve rule_def_7_2 eq319 | grind only
  have eq322 : (sP11 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 := by
    clear * - eq320 rule_def_7_3
    first | exact resolve eq320 rule_def_7_3 | exact resolve rule_def_7_3 eq320 | grind only
  have eq453 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq270 rule_def_11_3
    first | exact resolve eq270 rule_def_11_3 | exact resolve rule_def_11_3 eq270 | grind only
  have eq454 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq270 rule_def_11_2
    first | exact resolve eq270 rule_def_11_2 | exact resolve rule_def_11_2 eq270 | grind only
  have eq458 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq454 rule_def_1_0
    first | exact resolve eq454 rule_def_1_0 | exact resolve rule_def_1_0 eq454 | grind only
  have eq459 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq453 rule_def_1_1
    first | exact resolve eq453 rule_def_1_1 | exact resolve rule_def_1_1 eq453 | grind only
  have eq461 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq458 rule_def_2_1
    first | exact resolve eq458 rule_def_2_1 | exact resolve rule_def_2_1 eq458 | grind only
  have eq462 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq459 rule_def_2_2
    first | exact resolve eq459 rule_def_2_2 | exact resolve rule_def_2_2 eq459 | grind only
  have eq464 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq461 rule_def_3_1
    first | exact resolve eq461 rule_def_3_1 | exact resolve rule_def_3_1 eq461 | grind only
  have eq465 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq462 rule_def_3_2
    first | exact resolve eq462 rule_def_3_2 | exact resolve rule_def_3_2 eq462 | grind only
  have eq466 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq464 rule_def_4_1
    first | exact resolve eq464 rule_def_4_1 | exact resolve rule_def_4_1 eq464 | grind only
  have eq467 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq465 rule_def_4_2
    first | exact resolve eq465 rule_def_4_2 | exact resolve rule_def_4_2 eq465 | grind only
  have eq468 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq466 rule_def_8_2
    first | exact resolve eq466 rule_def_8_2 | exact resolve rule_def_8_2 eq466 | grind only
  have eq469 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq467 rule_def_8_3
    first | exact resolve eq467 rule_def_8_3 | exact resolve rule_def_8_3 eq467 | grind only
  have eq470 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq468 rule_def_9_2
    first | exact resolve eq468 rule_def_9_2 | exact resolve rule_def_9_2 eq468 | grind only
  have eq471 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq469 rule_def_9_3
    first | exact resolve eq469 rule_def_9_3 | exact resolve rule_def_9_3 eq469 | grind only
  have eq472 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq470 rule_def_10_2
    first | exact resolve eq470 rule_def_10_2 | exact resolve rule_def_10_2 eq470 | grind only
  have eq473 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq471 rule_def_10_3
    first | exact resolve eq471 rule_def_10_3 | exact resolve rule_def_10_3 eq471 | grind only
  have eq485 : (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq278 rule_def_11_2
    first | exact resolve eq278 rule_def_11_2 | exact resolve rule_def_11_2 eq278 | grind only
  have eq489 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq485 rule_def_1_0
    first | exact resolve eq485 rule_def_1_0 | exact resolve rule_def_1_0 eq485 | grind only
  have eq492 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq489 rule_def_2_1
    first | exact resolve eq489 rule_def_2_1 | exact resolve rule_def_2_1 eq489 | grind only
  have eq495 : (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq492 rule_def_3_1
    first | exact resolve eq492 rule_def_3_1 | exact resolve rule_def_3_1 eq492 | grind only
  have eq497 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq495 rule_def_4_1
    first | exact resolve eq495 rule_def_4_1 | exact resolve rule_def_4_1 eq495 | grind only
  have eq499 : (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq497 rule_def_8_2
    first | exact resolve eq497 rule_def_8_2 | exact resolve rule_def_8_2 eq497 | grind only
  have eq501 : (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq499 rule_def_9_2
    first | exact resolve eq499 rule_def_9_2 | exact resolve rule_def_9_2 eq499 | grind only
  have eq503 : (old sk0 sk2 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq501 rule_def_10_2
    first | exact resolve eq501 rule_def_10_2 | exact resolve rule_def_10_2 eq501 | grind only
  have eq516 : (sP1 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq279 rule_def_11_2
    first | exact resolve eq279 rule_def_11_2 | exact resolve rule_def_11_2 eq279 | grind only
  have eq520 : (sP2 sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq516 rule_def_1_0
    first | exact resolve eq516 rule_def_1_0 | exact resolve rule_def_1_0 eq516 | grind only
  have eq523 : (sP3 sk0 sk2 sk3) ∨ (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq520 rule_def_2_1
    first | exact resolve eq520 rule_def_2_1 | exact resolve rule_def_2_1 eq520 | grind only
  have eq526 : (sP4 sk0 sk2 sk3) ∨ (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq523 rule_def_3_1
    first | exact resolve eq523 rule_def_3_1 | exact resolve rule_def_3_1 eq523 | grind only
  have eq528 : (sP8 sk0 sk2 sk3) ∨ (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq526 rule_def_4_1
    first | exact resolve eq526 rule_def_4_1 | exact resolve rule_def_4_1 eq526 | grind only
  have eq530 : (sP9 sk0 sk2 sk3) ∨ (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq528 rule_def_8_2
    first | exact resolve eq528 rule_def_8_2 | exact resolve rule_def_8_2 eq528 | grind only
  have eq532 : (sP10 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq530 rule_def_9_2
    first | exact resolve eq530 rule_def_9_2 | exact resolve rule_def_9_2 eq530 | grind only
  have eq534 : (old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq532 rule_def_10_2
    first | exact resolve eq532 rule_def_10_2 | exact resolve rule_def_10_2 eq532 | grind only
  have eq565 : (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq309 rule_def_11_3
    first | exact resolve eq309 rule_def_11_3 | exact resolve rule_def_11_3 eq309 | grind only
  have eq566 : (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq309 rule_def_11_2
    first | exact resolve eq309 rule_def_11_2 | exact resolve rule_def_11_2 eq309 | grind only
  have eq570 : (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq566 rule_def_1_0
    first | exact resolve eq566 rule_def_1_0 | exact resolve rule_def_1_0 eq566 | grind only
  have eq571 : (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq565 rule_def_1_1
    first | exact resolve eq565 rule_def_1_1 | exact resolve rule_def_1_1 eq565 | grind only
  have eq573 : (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq570 rule_def_2_1
    first | exact resolve eq570 rule_def_2_1 | exact resolve rule_def_2_1 eq570 | grind only
  have eq574 : (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq571 rule_def_2_2
    first | exact resolve eq571 rule_def_2_2 | exact resolve rule_def_2_2 eq571 | grind only
  have eq576 : (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq573 rule_def_3_1
    first | exact resolve eq573 rule_def_3_1 | exact resolve rule_def_3_1 eq573 | grind only
  have eq577 : (sP4 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq574 rule_def_3_2
    first | exact resolve eq574 rule_def_3_2 | exact resolve rule_def_3_2 eq574 | grind only
  have eq578 : (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq576 rule_def_4_1
    first | exact resolve eq576 rule_def_4_1 | exact resolve rule_def_4_1 eq576 | grind only
  have eq579 : (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq577 rule_def_4_2
    first | exact resolve eq577 rule_def_4_2 | exact resolve rule_def_4_2 eq577 | grind only
  have eq580 : (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq578 rule_def_8_2
    first | exact resolve eq578 rule_def_8_2 | exact resolve rule_def_8_2 eq578 | grind only
  have eq581 : (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq579 rule_def_8_3
    first | exact resolve eq579 rule_def_8_3 | exact resolve rule_def_8_3 eq579 | grind only
  have eq582 : (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq580 rule_def_9_2
    first | exact resolve eq580 rule_def_9_2 | exact resolve rule_def_9_2 eq580 | grind only
  have eq583 : (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq581 rule_def_9_3
    first | exact resolve eq581 rule_def_9_3 | exact resolve rule_def_9_3 eq581 | grind only
  have eq584 : (old sk2 sk1 sk4) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq582 rule_def_10_2
    first | exact resolve eq582 rule_def_10_2 | exact resolve rule_def_10_2 eq582 | grind only
  have eq585 : (old sk2 sk1 sk4) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq583 rule_def_10_3
    first | exact resolve eq583 rule_def_10_3 | exact resolve rule_def_10_3 eq583 | grind only
  have eq590 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq321 rule_def_11_3
    first | exact resolve eq321 rule_def_11_3 | exact resolve rule_def_11_3 eq321 | grind only
  have eq591 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq321 rule_def_11_2
    first | exact resolve eq321 rule_def_11_2 | exact resolve rule_def_11_2 eq321 | grind only
  have eq592 : (sP10 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 := by
    clear * - eq321 rule_def_11_1
    first | exact resolve eq321 rule_def_11_1 | exact resolve rule_def_11_1 eq321 | grind only
  have eq595 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq591 rule_def_1_0
    first | exact resolve eq591 rule_def_1_0 | exact resolve rule_def_1_0 eq591 | grind only
  have eq596 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq590 rule_def_1_1
    first | exact resolve eq590 rule_def_1_1 | exact resolve rule_def_1_1 eq590 | grind only
  have eq598 : (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq595 rule_def_2_1
    first | exact resolve eq595 rule_def_2_1 | exact resolve rule_def_2_1 eq595 | grind only
  have eq599 : (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq596 rule_def_2_2
    first | exact resolve eq596 rule_def_2_2 | exact resolve rule_def_2_2 eq596 | grind only
  have eq601 : (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq598 rule_def_3_1
    first | exact resolve eq598 rule_def_3_1 | exact resolve rule_def_3_1 eq598 | grind only
  have eq602 : (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq599 rule_def_3_2
    first | exact resolve eq599 rule_def_3_2 | exact resolve rule_def_3_2 eq599 | grind only
  have eq603 : (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq601 rule_def_4_1
    first | exact resolve eq601 rule_def_4_1 | exact resolve rule_def_4_1 eq601 | grind only
  have eq604 : (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq602 rule_def_4_2
    first | exact resolve eq602 rule_def_4_2 | exact resolve rule_def_4_2 eq602 | grind only
  have eq605 : (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq603 rule_def_8_2
    first | exact resolve eq603 rule_def_8_2 | exact resolve rule_def_8_2 eq603 | grind only
  have eq606 : (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq604 rule_def_8_3
    first | exact resolve eq604 rule_def_8_3 | exact resolve rule_def_8_3 eq604 | grind only
  have eq607 : (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq605 rule_def_9_2
    first | exact resolve eq605 rule_def_9_2 | exact resolve rule_def_9_2 eq605 | grind only
  have eq608 : (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq606 rule_def_9_3
    first | exact resolve eq606 rule_def_9_3 | exact resolve rule_def_9_3 eq606 | grind only
  have eq609 : (old sk2 sk4 sk3) ∨ b = sk4 ∨ c = sk4 := by
    clear * - eq607 rule_def_10_2
    first | exact resolve eq607 rule_def_10_2 | exact resolve rule_def_10_2 eq607 | grind only
  have eq610 : (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq608 rule_def_10_3
    first | exact resolve eq608 rule_def_10_3 | exact resolve rule_def_10_3 eq608 | grind only
  have eq615 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq322 rule_def_11_3
    first | exact resolve eq322 rule_def_11_3 | exact resolve rule_def_11_3 eq322 | grind only
  have eq616 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq322 rule_def_11_2
    first | exact resolve eq322 rule_def_11_2 | exact resolve rule_def_11_2 eq322 | grind only
  have eq620 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq616 rule_def_1_0
    first | exact resolve eq616 rule_def_1_0 | exact resolve rule_def_1_0 eq616 | grind only
  have eq621 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq615 rule_def_1_1
    first | exact resolve eq615 rule_def_1_1 | exact resolve rule_def_1_1 eq615 | grind only
  have eq623 : (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq620 rule_def_2_1
    first | exact resolve eq620 rule_def_2_1 | exact resolve rule_def_2_1 eq620 | grind only
  have eq624 : (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq621 rule_def_2_2
    first | exact resolve eq621 rule_def_2_2 | exact resolve rule_def_2_2 eq621 | grind only
  have eq626 : (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq623 rule_def_3_1
    first | exact resolve eq623 rule_def_3_1 | exact resolve rule_def_3_1 eq623 | grind only
  have eq627 : (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq624 rule_def_3_2
    first | exact resolve eq624 rule_def_3_2 | exact resolve rule_def_3_2 eq624 | grind only
  have eq628 : (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq626 rule_def_4_1
    first | exact resolve eq626 rule_def_4_1 | exact resolve rule_def_4_1 eq626 | grind only
  have eq629 : (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq627 rule_def_4_2
    first | exact resolve eq627 rule_def_4_2 | exact resolve rule_def_4_2 eq627 | grind only
  have eq630 : (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq628 rule_def_8_2
    first | exact resolve eq628 rule_def_8_2 | exact resolve rule_def_8_2 eq628 | grind only
  have eq631 : (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq629 rule_def_8_3
    first | exact resolve eq629 rule_def_8_3 | exact resolve rule_def_8_3 eq629 | grind only
  have eq632 : (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq630 rule_def_9_2
    first | exact resolve eq630 rule_def_9_2 | exact resolve rule_def_9_2 eq630 | grind only
  have eq633 : (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq631 rule_def_9_3
    first | exact resolve eq631 rule_def_9_3 | exact resolve rule_def_9_3 eq631 | grind only
  have eq634 : (old sk2 sk4 sk3) ∨ c = sk3 ∨ c = sk4 := by
    clear * - eq632 rule_def_10_2
    first | exact resolve eq632 rule_def_10_2 | exact resolve rule_def_10_2 eq632 | grind only
  have eq635 : (old sk2 sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq633 rule_def_10_3
    first | exact resolve eq633 rule_def_10_3 | exact resolve rule_def_10_3 eq633 | grind only
  have eq707 : (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq303 rule_def_11_3
    first | exact resolve eq303 rule_def_11_3 | exact resolve rule_def_11_3 eq303 | grind only
  have eq708 : (sP1 sk2 sk1 sk4) ∨ (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq303 rule_def_11_2
    first | exact resolve eq303 rule_def_11_2 | exact resolve rule_def_11_2 eq303 | grind only
  have eq712 : (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq708 rule_def_1_0
    first | exact resolve eq708 rule_def_1_0 | exact resolve rule_def_1_0 eq708 | grind only
  have eq713 : (sP2 sk2 sk1 sk4) ∨ (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq707 rule_def_1_1
    first | exact resolve eq707 rule_def_1_1 | exact resolve rule_def_1_1 eq707 | grind only
  have eq715 : (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq712 rule_def_2_1
    first | exact resolve eq712 rule_def_2_1 | exact resolve rule_def_2_1 eq712 | grind only
  have eq716 : (sP3 sk2 sk1 sk4) ∨ (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq713 rule_def_2_2
    first | exact resolve eq713 rule_def_2_2 | exact resolve rule_def_2_2 eq713 | grind only
  have eq718 : (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq715 rule_def_3_1
    first | exact resolve eq715 rule_def_3_1 | exact resolve rule_def_3_1 eq715 | grind only
  have eq719 : (sP4 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq716 rule_def_3_2
    first | exact resolve eq716 rule_def_3_2 | exact resolve rule_def_3_2 eq716 | grind only
  have eq721 : (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq718 rule_def_4_1
    first | exact resolve eq718 rule_def_4_1 | exact resolve rule_def_4_1 eq718 | grind only
  have eq722 : (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP8 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq719 rule_def_4_2
    first | exact resolve eq719 rule_def_4_2 | exact resolve rule_def_4_2 eq719 | grind only
  have eq724 : (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq721 rule_def_8_2
    first | exact resolve eq721 rule_def_8_2 | exact resolve rule_def_8_2 eq721 | grind only
  have eq725 : (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP9 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq722 rule_def_8_3
    first | exact resolve eq722 rule_def_8_3 | exact resolve rule_def_8_3 eq722 | grind only
  have eq727 : (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq724 rule_def_9_2
    first | exact resolve eq724 rule_def_9_2 | exact resolve rule_def_9_2 eq724 | grind only
  have eq728 : (sP5 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP7 sk2 sk1 sk4) ∨ (sP10 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq725 rule_def_9_3
    first | exact resolve eq725 rule_def_9_3 | exact resolve rule_def_9_3 eq725 | grind only
  have eq729 : (sP7 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 := by
    clear * - eq727 rule_def_10_2
    first | exact resolve eq727 rule_def_10_2 | exact resolve rule_def_10_2 eq727 | grind only
  have eq730 : (sP7 sk2 sk1 sk4) ∨ (sP6 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 := by
    clear * - eq728 rule_def_10_3
    first | exact resolve eq728 rule_def_10_3 | exact resolve rule_def_10_3 eq728 | grind only
  have eq737 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq316 rule_def_11_3
    first | exact resolve eq316 rule_def_11_3 | exact resolve rule_def_11_3 eq316 | grind only
  have eq740 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq316 rule_def_11_0
    first | exact resolve eq316 rule_def_11_0 | exact resolve rule_def_11_0 eq316 | grind only
  have eq741 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq740 rule_def_5_0
    first | exact resolve eq740 rule_def_5_0 | exact resolve rule_def_5_0 eq740 | grind only
  have eq743 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq737 rule_def_1_1
    first | exact resolve eq737 rule_def_1_1 | exact resolve rule_def_1_1 eq737 | grind only
  have eq744 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq741 rule_def_6_0
    first | exact resolve eq741 rule_def_6_0 | exact resolve rule_def_6_0 eq741 | grind only
  have eq746 : (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq743 rule_def_2_2
    first | exact resolve eq743 rule_def_2_2 | exact resolve rule_def_2_2 eq743 | grind only
  have eq747 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq744 rule_def_7_0
    first | exact resolve eq744 rule_def_7_0 | exact resolve rule_def_7_0 eq744 | grind only
  have eq749 : (sP4 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq746 rule_def_3_2
    first | exact resolve eq746 rule_def_3_2 | exact resolve rule_def_3_2 eq746 | grind only
  have eq750 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq747 rule_def_8_0
    first | exact resolve eq747 rule_def_8_0 | exact resolve rule_def_8_0 eq747 | grind only
  have eq752 : (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq749 rule_def_4_2
    first | exact resolve eq749 rule_def_4_2 | exact resolve rule_def_4_2 eq749 | grind only
  have eq753 : (sP1 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq750 rule_def_9_0
    first | exact resolve eq750 rule_def_9_0 | exact resolve rule_def_9_0 eq750 | grind only
  have eq755 : (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq752 rule_def_8_3
    first | exact resolve eq752 rule_def_8_3 | exact resolve rule_def_8_3 eq752 | grind only
  have eq756 : (sP4 sk2 sk4 sk3) ∨ (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b := by
    clear * - eq753 rule_def_10_0
    first | exact resolve eq753 rule_def_10_0 | exact resolve rule_def_10_0 eq753 | grind only
  have eq758 : (sP5 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP7 sk2 sk4 sk3) ∨ (sP10 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq755 rule_def_9_3
    first | exact resolve eq755 rule_def_9_3 | exact resolve rule_def_9_3 eq755 | grind only
  have eq760 : (sP7 sk2 sk4 sk3) ∨ (sP6 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 := by
    clear * - eq758 rule_def_10_3
    first | exact resolve eq758 rule_def_10_3 | exact resolve rule_def_10_3 eq758 | grind only
  have eq761 (X0 X1 : G) : ¬(old sk2 X1 sk4) ∨ c = sk4 ∨ ¬(old X0 sk2 sk3) ∨ b = sk4 ∨ ¬(old X0 X1 sk2) ∨ (old X1 X1 sk2) := by
    clear * - eq609 old_8
    first | exact resolve eq609 old_8 | exact resolve old_8 eq609 | grind only
  have eq769 (X0 X1 : G) : ¬(old sk2 X1 sk4) ∨ c = sk4 ∨ ¬(old X0 sk2 sk3) ∨ c = sk3 ∨ ¬(old X0 X1 sk2) ∨ (old X1 X1 sk2) := by
    clear * - eq634 old_8
    first | exact resolve eq634 old_8 | exact resolve old_8 eq634 | grind only
  have eq1116 : (sP6 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq729 rule_def_7_1
    first | exact resolve eq729 rule_def_7_1 | exact resolve rule_def_7_1 eq729 | grind only
  have eq1119 : (sP5 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq1116 rule_def_6_1
    first | exact resolve eq1116 rule_def_6_1 | exact resolve rule_def_6_1 eq1116 | grind only
  have eq1121 : (old sk2 sk1 sk4) ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq1119 rule_def_5_1
    first | exact resolve eq1119 rule_def_5_1 | exact resolve rule_def_5_1 eq1119 | grind only
  have eq1134 : (sP6 sk2 sk1 sk4) ∨ (sP5 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 ∨ c = sk2 := by
    clear * - eq730 rule_def_7_1
    first | exact resolve eq730 rule_def_7_1 | exact resolve rule_def_7_1 eq730 | grind only
  have eq1137 : (sP5 sk2 sk1 sk4) ∨ (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 ∨ c = sk2 := by
    clear * - eq1134 rule_def_6_1
    first | exact resolve eq1134 rule_def_6_1 | exact resolve rule_def_6_1 eq1134 | grind only
  have eq1139 : (old sk2 sk1 sk4) ∨ a = sk2 ∨ b = sk4 ∨ c = sk2 := by
    clear * - eq1137 rule_def_5_1
    first | exact resolve eq1137 rule_def_5_1 | exact resolve rule_def_5_1 eq1137 | grind only
  have eq1170 : (sP6 sk2 sk4 sk3) ∨ (sP5 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 ∨ c = sk2 := by
    clear * - eq760 rule_def_7_1
    first | exact resolve eq760 rule_def_7_1 | exact resolve rule_def_7_1 eq760 | grind only
  have eq1173 : (sP5 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 ∨ c = sk2 := by
    clear * - eq1170 rule_def_6_1
    first | exact resolve eq1170 rule_def_6_1 | exact resolve rule_def_6_1 eq1170 | grind only
  have eq1175 : (old sk2 sk4 sk3) ∨ a = sk2 ∨ b = sk3 ∨ c = sk2 := by
    clear * - eq1173 rule_def_5_1
    first | exact resolve eq1173 rule_def_5_1 | exact resolve rule_def_5_1 eq1173 | grind only
  have eq1397 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b ∨ (old b b a) := by
    clear * - eq756 rule_def_4_3
    first | exact resolve eq756 rule_def_4_3 | exact resolve rule_def_4_3 eq756 | grind only
  have eq1402 : (sP3 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b ∨ (old b b a) := by
    clear * - eq1397 rule_def_2_3
    first | exact resolve eq1397 rule_def_2_3 | exact resolve rule_def_2_3 eq1397 | grind only
  have eq1404 : (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ a = sk2 ∨ a = b ∨ (old b b a) := by
    clear * - eq1402 rule_def_3_3
    first | exact resolve eq1402 rule_def_3_3 | exact resolve rule_def_3_3 eq1402 | grind only
  have eq1559 : (sP2 sk2 sk4 sk3) ∨ (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq592 rule_def_10_1
    first | exact resolve eq592 rule_def_10_1 | exact resolve rule_def_10_1 eq592 | grind only
  have eq1561 : (sP3 sk2 sk4 sk3) ∨ (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq1559 rule_def_2_0
    first | exact resolve eq1559 rule_def_2_0 | exact resolve rule_def_2_0 eq1559 | grind only
  have eq1562 : (sP4 sk2 sk4 sk3) ∨ (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq1561 rule_def_3_0
    first | exact resolve eq1561 rule_def_3_0 | exact resolve rule_def_3_0 eq1561 | grind only
  have eq1563 : (sP8 sk2 sk4 sk3) ∨ (sP9 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq1562 rule_def_4_0
    first | exact resolve eq1562 rule_def_4_0 | exact resolve rule_def_4_0 eq1562 | grind only
  have eq1564 : (sP9 sk2 sk4 sk3) ∨ (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq1563 rule_def_8_1
    first | exact resolve eq1563 rule_def_8_1 | exact resolve rule_def_8_1 eq1563 | grind only
  have eq1565 : (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq1564 rule_def_9_1
    first | exact resolve eq1564 rule_def_9_1 | exact resolve rule_def_9_1 eq1564 | grind only
  have eq2684 : (new sk2 c b) ∨ a = sk2 ∨ a = b ∨ (old b b a) ∨ (old sk2 sk4 sk3) := by
    clear * - eq1404 eq237
    first | exact resolve eq1404 eq237 | exact resolve eq237 eq1404 | grind only
  have eq2801 (X0 : G) : c = sk4 ∨ ¬(old X0 sk2 sk3) ∨ b = sk4 ∨ ¬(old X0 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ c = sk4 ∨ b = sk4 := by
    clear * - eq761 eq585
    first | exact resolve eq761 eq585 | exact resolve eq585 eq761 | grind only
  have eq2808 (X0 : G) : ¬(old X0 sk2 sk3) ∨ c = sk4 ∨ b = sk4 ∨ ¬(old X0 sk1 sk2) ∨ (old sk1 sk1 sk2) := by
    clear * - eq2801
    first | exact resolve eq2801 rfl | grind only
  have eq2825 (X0 : G) : c = sk4 ∨ ¬(old X0 sk2 sk3) ∨ c = sk3 ∨ ¬(old X0 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ c = sk4 ∨ c = sk1 := by
    clear * - eq769 eq584
    first | exact resolve eq769 eq584 | exact resolve eq584 eq769 | grind only
  have eq2832 (X0 : G) : ¬(old X0 sk2 sk3) ∨ c = sk4 ∨ c = sk3 ∨ ¬(old X0 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ c = sk1 := by
    clear * - eq2825
    first | exact resolve eq2825 rfl | grind only
  have eq3363 : c = sk4 ∨ b = sk4 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq2808 eq503
    first | exact resolve eq2808 eq503 | exact resolve eq503 eq2808 | grind only
  have eq3371 : (old sk1 sk1 sk2) ∨ b = sk4 ∨ c = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq3363 eq473
    first | exact resolve eq3363 eq473 | exact resolve eq473 eq3363 | grind only
  have eq3405 : b = sk4 ∨ c = sk4 ∨ b = sk2 ∨ c = sk2 ∨ (new sk1 sk1 sk2) := by
    clear * - eq3371 imp_new_0
    first | exact resolve eq3371 imp_new_0 | exact resolve imp_new_0 eq3371 | grind only
  have eq3412 : c = sk4 ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq3405 preserve_4
    first | exact resolve eq3405 preserve_4 | exact resolve preserve_4 eq3405 | grind only
  have eq3471 : (sP1 sk2 c sk3) ∨ (old sk2 c sk3) ∨ c = b ∨ b = sk2 ∨ c = sk2 ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq1565 eq3412
    first | exact Or.assoc5 (eq3412.imp_left (fun h : c = sk4 => superpose h eq1565)) | exact superpose eq1565 eq3412 | exact superpose eq3412 eq1565 | grind only
  have eq3482 : (sP1 sk2 c sk3) ∨ (old sk2 c sk3) ∨ c = b ∨ b = sk2 ∨ c = sk2 ∨ b = sk4 := by
    clear * - eq3471
    first | exact resolve eq3471 rfl | grind only
  have eq3503 : (sP1 sk2 c sk3) ∨ c = b ∨ b = sk2 ∨ c = sk2 ∨ b = sk4 := by
    clear * - eq3482 p4XZ
    first | exact resolve eq3482 p4XZ | exact resolve p4XZ eq3482 | grind only
  have eq3545 : (sP1 sk2 c sk3) ∨ b = sk2 ∨ c = sk2 ∨ b = sk4 := by
    clear * - eq3503 bc
    first | exact resolve eq3503 bc | exact resolve bc eq3503 | grind only
  have eq5523 : c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ c = sk1 ∨ c = sk3 ∨ c = sk2 := by
    clear * - eq2832 eq534
    first | exact resolve eq2832 eq534 | exact resolve eq534 eq2832 | grind only
  have eq5530 : c = sk4 ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq5523
    first | exact resolve eq5523 rfl | grind only
  have eq5535 : (old sk1 sk1 sk2) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq5530 eq472
    first | exact resolve eq5530 eq472 | exact resolve eq472 eq5530 | grind only
  have eq5716 : c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk1 sk2) := by
    clear * - eq5535 imp_new_0
    first | exact resolve eq5535 imp_new_0 | exact resolve imp_new_0 eq5535 | grind only
  have eq5728 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq5716 preserve_4
    first | exact resolve eq5716 preserve_4 | exact resolve preserve_4 eq5716 | grind only
  have eq5777 : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq1121 eq5728
    first | exact Or.assoc4 (eq5728.imp_left (fun h : c = sk4 => superpose h eq1121)) | exact superpose eq1121 eq5728 | exact superpose eq5728 eq1121 | grind only
  have eq5858 : (old sk2 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := by
    clear * - eq5777
    first | exact resolve eq5777 rfl | grind only
  have eq5904 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ a = sk2 := by
    clear * - eq5858 p4XY
    first | exact resolve eq5858 p4XY | exact resolve p4XY eq5858 | grind only
  have eq6008 : (old sk2 sk4 c) ∨ a = sk2 ∨ c = b ∨ c = sk2 ∨ c = sk1 ∨ c = sk2 ∨ a = sk2 := by
    clear * - eq1175 eq5904
    first | exact Or.assoc4 (eq5904.imp_left (fun h : c = sk3 => superpose h eq1175)) | exact superpose eq1175 eq5904 | exact superpose eq5904 eq1175 | grind only
  have eq6085 : (old sk2 sk4 c) ∨ a = sk2 ∨ c = b ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq6008
    first | exact resolve eq6008 rfl | grind only
  have eq6115 : a = sk2 ∨ c = b ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq6085 p4XY
    first | exact resolve eq6085 p4XY | exact resolve p4XY eq6085 | grind only
  have eq6148 : c = sk1 ∨ c = sk2 ∨ a = sk2 := by
    clear * - eq6115 bc
    first | exact resolve eq6115 bc | exact resolve bc eq6115 | grind only
  have eq6161 : (new sk2 c sk4) ∨ c = sk2 ∨ a = sk2 := by
    clear * - preserve_2 eq6148
    first | exact (eq6148.imp_left (fun h : c = sk1 => superpose h preserve_2)) | exact superpose preserve_2 eq6148 | exact superpose eq6148 preserve_2 | grind only
  have eq6185 : (old sk0 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 := by
    clear * - eq473 eq6148
    first | exact Or.assoc3 (eq6148.imp_left (fun h : c = sk1 => superpose h eq473)) | exact superpose eq473 eq6148 | exact superpose eq6148 eq473 | grind only
  have eq6214 : (old sk2 c sk4) ∨ a = sk2 ∨ b = sk4 ∨ c = sk2 ∨ c = sk2 ∨ a = sk2 := by
    clear * - eq1139 eq6148
    first | exact Or.assoc4 (eq6148.imp_left (fun h : c = sk1 => superpose h eq1139)) | exact superpose eq1139 eq6148 | exact superpose eq6148 eq1139 | grind only
  have eq6290 : (old sk2 c sk4) ∨ a = sk2 ∨ b = sk4 ∨ c = sk2 := by
    clear * - eq6214
    first | exact resolve eq6214 rfl | grind only
  have eq6298 : (old sk0 c sk2) ∨ c = sk2 ∨ b = sk2 ∨ a = sk2 := by
    clear * - eq6185
    first | exact resolve eq6185 rfl | grind only
  have eq6325 : b = sk4 ∨ a = sk2 ∨ c = sk2 := by
    clear * - eq6290 p4XZ
    first | exact resolve eq6290 p4XZ | exact resolve p4XZ eq6290 | grind only
  have eq6341 : a = sk2 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6298 p4XZ
    first | exact resolve eq6298 p4XZ | exact resolve p4XZ eq6298 | grind only
  have eq6561 : (new a sk4 sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - preserve_3 eq6341
    first | exact (eq6341.imp_left (fun h : a = sk2 => superpose h preserve_3)) | exact superpose preserve_3 eq6341 | exact superpose eq6341 preserve_3 | grind only
  have eq6600 : (old sk0 a sk3) ∨ a = b ∨ a = c ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq503 eq6341
    first | exact Or.assoc3 (eq6341.imp_left (fun h : a = sk2 => superpose h eq503)) | exact superpose eq503 eq6341 | exact superpose eq6341 eq503 | grind only
  have eq6765 : (sP1 a c sk3) ∨ a = b ∨ a = c ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq3545 eq6341
    first | exact Or.assoc4 (eq6341.imp_left (fun h : a = sk2 => superpose h eq3545)) | exact superpose eq3545 eq6341 | exact superpose eq6341 eq3545 | grind only
  have eq6798 : a ≠ b ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6341
    grind only
  have eq6832 : (sP1 a c sk3) ∨ a = c ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6765 eq6798
    first | exact resolve eq6765 eq6798 | exact resolve eq6798 eq6765 | grind only
  have eq6917 : (old sk0 a sk3) ∨ a = c ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6600 eq6798
    first | exact resolve eq6600 eq6798 | exact resolve eq6798 eq6600 | grind only
  have eq6959 : a = c ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6832 eq221
    first | exact resolve eq6832 eq221 | exact resolve eq221 eq6832 | grind only
  have eq7003 : (old sk0 a sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6917 ac
    first | exact resolve eq6917 ac | exact resolve ac eq6917 | grind only
  have eq7012 : b = sk4 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6959 ac
    first | exact resolve eq6959 ac | exact resolve ac eq6959 | grind only
  have eq7213 : (new sk2 c b) ∨ c = sk2 ∨ a = sk2 ∨ a = sk2 ∨ c = sk2 := by
    clear * - eq6161 eq6325
    first | exact Or.assoc3 (eq6325.imp_left (fun h : b = sk4 => superpose h eq6161)) | exact superpose eq6161 eq6325 | exact superpose eq6325 eq6161 | grind only
  have eq7216 : (new sk2 c b) ∨ c = sk2 ∨ a = sk2 := by
    clear * - eq7213
    first | exact resolve eq7213 rfl | grind only
  have eq7393 : (new a b sk3) ∨ b = sk2 ∨ c = sk2 ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq6561 eq7012
    first | exact Or.assoc3 (eq7012.imp_left (fun h : b = sk4 => superpose h eq6561)) | exact superpose eq6561 eq7012 | exact superpose eq7012 eq6561 | grind only
  have eq7396 : (new a b sk3) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq7393
    first | exact resolve eq7393 rfl | grind only
  have eq7577 : c = sk3 ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq7396 eq231
    first | exact resolve eq7396 eq231 | exact resolve eq231 eq7396 | grind only
  have eq7672 : (old sk0 a c) ∨ b = sk2 ∨ c = sk2 ∨ c = sk2 ∨ b = sk2 := by
    clear * - eq7003 eq7577
    first | exact Or.assoc3 (eq7577.imp_left (fun h : c = sk3 => superpose h eq7003)) | exact superpose eq7003 eq7577 | exact superpose eq7577 eq7003 | grind only
  have eq7677 : (old sk0 a c) ∨ b = sk2 ∨ c = sk2 := by
    clear * - eq7672
    first | exact resolve eq7672 rfl | grind only
  have eq7725 : c = sk2 ∨ b = sk2 := by
    clear * - eq7677 p4XY
    first | exact resolve eq7677 p4XY | exact resolve p4XY eq7677 | grind only
  have eq7755 : ¬(new sk1 sk1 c) ∨ b = sk2 := by
    clear * - preserve_4 eq7725
    first | exact (eq7725.imp_left (fun h : c = sk2 => superpose h preserve_4)) | exact superpose preserve_4 eq7725 | exact superpose eq7725 preserve_4 | grind only
  have eq7777 : (old sk0 sk1 c) ∨ b = sk1 ∨ c = b ∨ b = sk2 := by
    clear * - eq300 eq7725
    first | exact Or.assoc3 (eq7725.imp_left (fun h : c = sk2 => superpose h eq300)) | exact superpose eq300 eq7725 | exact superpose eq7725 eq300 | grind only
  have eq7924 : (new c c b) ∨ a = c ∨ a = b ∨ (old b b a) ∨ (old c sk4 sk3) ∨ b = sk2 := by
    clear * - eq2684 eq7725
    first | exact Or.assoc5 (eq7725.imp_left (fun h : c = sk2 => superpose h eq2684)) | exact superpose eq2684 eq7725 | exact superpose eq7725 eq2684 | grind only
  have eq7944 : (new c c b) ∨ a = c ∨ (old b b a) ∨ (old c sk4 sk3) ∨ b = sk2 := by
    clear * - eq7924 eq212
    first | exact resolve eq7924 eq212 | exact resolve eq212 eq7924 | grind only
  have eq8040 : b = sk1 ∨ c = b ∨ b = sk2 := by
    clear * - eq7777 p4XY
    first | exact resolve eq7777 p4XY | exact resolve p4XY eq7777 | grind only
  have eq8053 : (new c c b) ∨ a = c ∨ (old c sk4 sk3) ∨ b = sk2 := by
    clear * - eq7944 eq194
    first | exact resolve eq7944 eq194 | exact resolve eq194 eq7944 | grind only
  have eq8100 : b = sk1 ∨ b = sk2 := by
    clear * - eq8040 bc
    first | exact resolve eq8040 bc | exact resolve bc eq8040 | grind only
  have eq8104 : (new c c b) ∨ (old c sk4 sk3) ∨ b = sk2 := by
    clear * - eq8053 ac
    first | exact resolve eq8053 ac | exact resolve ac eq8053 | grind only
  have eq8122 : (new c c b) ∨ b = sk2 := by
    clear * - eq8104 p4YZ
    first | exact resolve eq8104 p4YZ | exact resolve p4YZ eq8104 | grind only
  have eq8557 : ¬(new b b c) ∨ b = sk2 ∨ b = sk2 := by
    clear * - eq7755 eq8100
    first | exact Or.assoc2 (eq8100.imp_left (fun h : b = sk1 => superpose h eq7755)) | exact superpose eq7755 eq8100 | exact superpose eq8100 eq7755 | grind only
  have eq8559 : ¬(new b b c) ∨ b = sk2 := by
    clear * - eq8557
    first | exact resolve eq8557 rfl | grind only
  have eq8574 : b = sk2 ∨ (new b b c) := by
    clear * - eq8122 prev_5
    first | exact resolve eq8122 prev_5 | exact resolve prev_5 eq8122 | grind only
  have eq8580 : b = sk2 := by
    clear * - eq8574 eq8559
    first | exact resolve eq8574 eq8559 | exact resolve eq8559 eq8574 | grind only
  have eq8598 : (new sk0 sk1 b) := by
    clear * - preserve_0 eq8580
    first | exact superpose preserve_0 eq8580 | exact superpose eq8580 preserve_0 | grind only
  have eq8600 : (new b sk1 sk4) := by
    clear * - preserve_2 eq8580
    first | exact superpose preserve_2 eq8580 | exact superpose eq8580 preserve_2 | grind only
  have eq8602 : ¬(new sk1 sk1 b) := by
    clear * - preserve_4 eq8580
    first | exact superpose preserve_4 eq8580 | exact superpose eq8580 preserve_4 | grind only
  have eq8604 (X0 : G) : ¬(new b sk1 X0) ∨ sk4 = X0 := by
    clear * - eq229 eq8580
    first | exact superpose eq229 eq8580 | exact superpose eq8580 eq229 | grind only
  have eq8605 (X0 : G) : ¬(new b sk4 X0) ∨ sk3 = X0 := by
    clear * - eq230 eq8580
    first | exact superpose eq230 eq8580 | exact superpose eq8580 eq230 | grind only
  have eq8651 : (old b sk4 sk3) ∨ b = sk4 ∨ b = sk3 := by
    clear * - eq610 eq8580
    first | exact superpose eq610 eq8580 | exact superpose eq8580 eq610 | grind only
  have eq8657 : (old b sk4 sk3) ∨ c = sk3 ∨ b = sk3 := by
    clear * - eq635 eq8580
    first | exact superpose eq635 eq8580 | exact superpose eq8580 eq635 | grind only
  have eq8835 : (new b c b) ∨ c = b ∨ a = b := by
    clear * - eq7216 eq8580
    first | exact superpose eq7216 eq8580 | exact superpose eq8580 eq7216 | grind only
  have eq8873 : (new b c b) ∨ c = b := by
    clear * - eq8835 eq215
    first | exact resolve eq8835 eq215 | exact resolve eq215 eq8835 | grind only
  have eq8989 : (new b c b) := by
    clear * - eq8873 bc
    first | exact resolve eq8873 bc | exact resolve bc eq8873 | grind only
  have eq9096 : (new b sk1 c) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := by
    clear * - eq8600 eq5728
    first | exact (eq5728.imp_left (fun h : c = sk4 => superpose h eq8600)) | exact superpose eq8600 eq5728 | exact superpose eq5728 eq8600 | grind only
  have eq9100 : c = b ∨ (new b sk1 c) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq9096 eq8580
    first | simpa only [eq8580, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq9096 | grind only
  have eq9104 : (new b sk1 c) ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq9100 bc
    first | exact resolve eq9100 bc | exact resolve bc eq9100 | grind only
  have eq9147 : (new c c b) := by
    clear * - eq8989 prev_2
    first | exact resolve eq8989 prev_2 | exact resolve prev_2 eq8989 | grind only
  have eq14309 : c = sk4 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq9104 eq8604
    first | exact resolve eq9104 eq8604 | exact resolve eq8604 eq9104 | grind only
  have eq14310 : c = sk3 ∨ c = sk1 ∨ ¬(new b c sk2) ∨ (new b sk4 sk1) := by
    clear * - eq9104 eq244
    first | exact resolve eq9104 eq244 | exact resolve eq244 eq9104 | grind only
  have eq14317 : ¬(new b c b) ∨ c = sk3 ∨ c = sk1 ∨ (new b sk4 sk1) := by
    clear * - eq14310 eq8580
    first | simpa only [eq8580, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq14310 | grind only
  have eq14319 : (new b sk4 sk1) ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq14317 eq8989
    first | exact resolve eq14317 eq8989 | exact resolve eq8989 eq14317 | grind only
  have eq14460 : (old b c sk3) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk3 := by
    clear * - eq8657 eq14309
    first | exact Or.assoc3 (eq14309.imp_left (fun h : c = sk4 => superpose h eq8657)) | exact superpose eq8657 eq14309 | exact superpose eq14309 eq8657 | grind only
  have eq14472 : (old b c sk3) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 := by
    clear * - eq14460
    first | exact resolve eq14460 rfl | grind only
  have eq14505 : c = sk3 ∨ b = sk3 ∨ c = sk1 := by
    clear * - eq14472 p4XZ
    first | exact resolve eq14472 p4XZ | exact resolve p4XZ eq14472 | grind only
  have eq14718 : (old b sk4 c) ∨ b = sk4 ∨ c = b ∨ b = sk3 ∨ c = sk1 := by
    clear * - eq8651 eq14505
    first | exact Or.assoc3 (eq14505.imp_left (fun h : c = sk3 => superpose h eq8651)) | exact superpose eq8651 eq14505 | exact superpose eq14505 eq8651 | grind only
  have eq14739 : b = sk4 ∨ c = b ∨ b = sk3 ∨ c = sk1 := by
    clear * - eq14718 p4XY
    first | exact resolve eq14718 p4XY | exact resolve p4XY eq14718 | grind only
  have eq14762 : b = sk4 ∨ b = sk3 ∨ c = sk1 := by
    clear * - eq14739 bc
    first | exact resolve eq14739 bc | exact resolve bc eq14739 | grind only
  have eq15191 : (new b sk1 b) ∨ b = sk3 ∨ c = sk1 := by
    clear * - eq8600 eq14762
    first | exact (eq14762.imp_left (fun h : b = sk4 => superpose h eq8600)) | exact superpose eq8600 eq14762 | exact superpose eq14762 eq8600 | grind only
  have eq15761 : sk1 = sk3 ∨ c = sk3 ∨ c = sk1 := by
    clear * - eq14319 eq8605
    first | exact resolve eq14319 eq8605 | exact resolve eq8605 eq14319 | grind only
  have eq16753 : b = sk3 ∨ c = sk1 ∨ (new sk1 sk1 b) := by
    clear * - eq15191 prev_2
    first | exact resolve eq15191 prev_2 | exact resolve prev_2 eq15191 | grind only
  have eq16759 : b = sk3 ∨ c = sk1 := by
    clear * - eq16753 eq8602
    first | exact resolve eq16753 eq8602 | exact resolve eq8602 eq16753 | grind only
  have eq16906 : b = sk1 ∨ c = b ∨ c = sk1 ∨ c = sk1 := by
    clear * - eq15761 eq16759
    first | exact Or.assoc3 (eq16759.imp_left (fun h : b = sk3 => superpose h eq15761)) | exact superpose eq15761 eq16759 | exact superpose eq16759 eq15761 | grind only
  have eq16915 : b = sk1 ∨ c = b ∨ c = sk1 := by
    clear * - eq16906
    first | exact resolve eq16906 rfl | grind only
  have eq16928 : c = sk1 ∨ b = sk1 := by
    clear * - eq16915 bc
    first | exact resolve eq16915 bc | exact resolve bc eq16915 | grind only
  have eq17215 : ¬(new c c b) ∨ b = sk1 := by
    clear * - eq8602 eq16928
    first | exact (eq16928.imp_left (fun h : c = sk1 => superpose h eq8602)) | exact superpose eq8602 eq16928 | exact superpose eq16928 eq8602 | grind only
  have eq17227 : b = sk1 := by
    clear * - eq17215 eq9147
    first | exact resolve eq17215 eq9147 | exact resolve eq9147 eq17215 | grind only
  have eq17391 : (new sk0 b b) := by
    clear * - eq8598 eq17227
    first | exact superpose eq8598 eq17227 | exact superpose eq17227 eq8598 | grind only
  have eq17393 : ¬(new b b b) := by
    clear * - eq8602 eq17227
    first | exact superpose eq8602 eq17227 | exact superpose eq17227 eq8602 | grind only
  have eq18324 : (new b b b) := by
    clear * - eq17391 prev_7
    first | exact resolve eq17391 prev_7 | exact resolve prev_7 eq17391 | grind only
  clear * - eq18324 eq17393
  first | subsumption eq18324 eq17393 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (memold : G → Prop) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), c = X ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_1 : ∀ (X Y Z : G), c = X ∨ ¬sP9 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (rule_def_10_1 : ∀ (X Y Z : G), c = X ∨ ¬sP10 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (rule_def_11_1 : ∀ (X Y Z : G), b = X ∨ ¬sP11 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq210 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X0 := by
    clear * - rule_def_1_2 old_mem1
    first | exact resolve rule_def_1_2 old_mem1 | exact resolve old_mem1 rule_def_1_2 | grind only
  have eq230 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq234 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq230 rule_def_0_2
    first | exact resolve eq230 rule_def_0_2 | exact resolve rule_def_0_2 eq230 | grind only
  have eq235 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq230 rule_def_0_1
    first | exact resolve eq230 rule_def_0_1 | exact resolve rule_def_0_1 eq230 | grind only
  have eq236 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ a = sk0 := by
    clear * - eq230 rule_def_0_0
    first | exact resolve eq230 rule_def_0_0 | exact resolve rule_def_0_0 eq230 | grind only
  have eq237 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := by
    clear * - eq236 preserve_1
    first | exact resolve eq236 preserve_1 | exact resolve preserve_1 eq236 | grind only
  have eq238 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq235 rule_def_5_2
    first | exact resolve eq235 rule_def_5_2 | exact resolve rule_def_5_2 eq235 | grind only
  have eq239 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq234 rule_def_5_3
    first | exact resolve eq234 rule_def_5_3 | exact resolve rule_def_5_3 eq234 | grind only
  have eq240 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq238 rule_def_6_2
    first | exact resolve eq238 rule_def_6_2 | exact resolve rule_def_6_2 eq238 | grind only
  have eq241 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq239 rule_def_6_3
    first | exact resolve eq239 rule_def_6_3 | exact resolve rule_def_6_3 eq239 | grind only
  have eq242 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq240 rule_def_7_2
    first | exact resolve eq240 rule_def_7_2 | exact resolve rule_def_7_2 eq240 | grind only
  have eq243 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq241 rule_def_7_3
    first | exact resolve eq241 rule_def_7_3 | exact resolve rule_def_7_3 eq241 | grind only
  have eq244 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq242 rule_def_11_3
    first | exact resolve eq242 rule_def_11_3 | exact resolve rule_def_11_3 eq242 | grind only
  have eq246 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk0 := by
    clear * - eq242 rule_def_11_1
    first | exact resolve eq242 rule_def_11_1 | exact resolve rule_def_11_1 eq242 | grind only
  have eq249 : (sP10 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq246 preserve_2
    first | exact resolve eq246 preserve_2 | exact resolve preserve_2 eq246 | grind only
  have eq251 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq244 rule_def_1_1
    first | exact resolve eq244 rule_def_1_1 | exact resolve rule_def_1_1 eq244 | grind only
  have eq254 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq251 rule_def_2_2
    first | exact resolve eq251 rule_def_2_2 | exact resolve rule_def_2_2 eq251 | grind only
  have eq257 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq254 rule_def_3_2
    first | exact resolve eq254 rule_def_3_2 | exact resolve rule_def_3_2 eq254 | grind only
  have eq259 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq257 rule_def_4_2
    first | exact resolve eq257 rule_def_4_2 | exact resolve rule_def_4_2 eq257 | grind only
  have eq261 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq259 rule_def_8_3
    first | exact resolve eq259 rule_def_8_3 | exact resolve rule_def_8_3 eq259 | grind only
  have eq263 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq261 rule_def_9_3
    first | exact resolve eq261 rule_def_9_3 | exact resolve rule_def_9_3 eq261 | grind only
  have eq265 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ b = sk2 := by
    clear * - eq263 rule_def_10_3
    first | exact resolve eq263 rule_def_10_3 | exact resolve rule_def_10_3 eq263 | grind only
  have eq370 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq243 rule_def_11_2
    first | exact resolve eq243 rule_def_11_2 | exact resolve rule_def_11_2 eq243 | grind only
  have eq377 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq370 rule_def_1_0
    first | exact resolve eq370 rule_def_1_0 | exact resolve rule_def_1_0 eq370 | grind only
  have eq380 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq377 rule_def_2_1
    first | exact resolve eq377 rule_def_2_1 | exact resolve rule_def_2_1 eq377 | grind only
  have eq383 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq380 rule_def_3_1
    first | exact resolve eq380 rule_def_3_1 | exact resolve rule_def_3_1 eq380 | grind only
  have eq385 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq383 rule_def_4_1
    first | exact resolve eq383 rule_def_4_1 | exact resolve rule_def_4_1 eq383 | grind only
  have eq387 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq385 rule_def_8_2
    first | exact resolve eq385 rule_def_8_2 | exact resolve rule_def_8_2 eq385 | grind only
  have eq389 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq387 rule_def_9_2
    first | exact resolve eq387 rule_def_9_2 | exact resolve rule_def_9_2 eq387 | grind only
  have eq391 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := by
    clear * - eq389 rule_def_10_2
    first | exact resolve eq389 rule_def_10_2 | exact resolve rule_def_10_2 eq389 | grind only
  have eq399 : c = sk2 ∨ c = sk1 ∨ memold sk0 := by
    clear * - eq391 old_mem1
    first | exact resolve eq391 old_mem1 | exact resolve old_mem1 eq391 | grind only
  have eq404 : c = sk2 ∨ c = sk1 := by
    clear * - eq399 preserve_3
    first | exact resolve eq399 preserve_3 | exact resolve preserve_3 eq399 | grind only
  have eq435 : (sP11 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP8 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq237 eq404
    first | exact superpose eq237 eq404 | exact superpose eq404 eq237 | grind only
  have eq445 : (sP1 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP8 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq435 rule_def_11_2
    first | exact resolve eq435 rule_def_11_2 | exact resolve rule_def_11_2 eq435 | grind only
  have eq447 : (sP2 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP8 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq445 rule_def_1_0
    first | exact resolve eq445 rule_def_1_0 | exact resolve rule_def_1_0 eq445 | grind only
  have eq449 : (sP3 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP8 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq447 rule_def_2_1
    first | exact resolve eq447 rule_def_2_1 | exact resolve rule_def_2_1 eq447 | grind only
  have eq451 : (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP8 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq449 rule_def_3_1
    first | exact resolve eq449 rule_def_3_1 | exact resolve rule_def_3_1 eq449 | grind only
  have eq453 : (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP8 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq451 rule_def_4_1
    first | exact resolve eq451 rule_def_4_1 | exact resolve rule_def_4_1 eq451 | grind only
  have eq455 : (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP9 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq453 rule_def_8_2
    first | exact resolve eq453 rule_def_8_2 | exact resolve rule_def_8_2 eq453 | grind only
  have eq457 : (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (sP10 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq455 rule_def_9_2
    first | exact resolve eq455 rule_def_9_2 | exact resolve rule_def_9_2 eq455 | grind only
  have eq459 : (sP5 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq457 rule_def_10_2
    first | exact resolve eq457 rule_def_10_2 | exact resolve rule_def_10_2 eq457 | grind only
  have eq461 : (sP7 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ c = sk1 := by
    clear * - eq459 p4XY
    first | exact resolve eq459 p4XY | exact resolve p4XY eq459 | grind only
  have eq551 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq461 rule_def_7_1
    first | exact resolve eq461 rule_def_7_1 | exact resolve rule_def_7_1 eq461 | grind only
  have eq554 : (sP5 sk0 sk1 c) ∨ c = sk1 ∨ c = sk0 := by
    clear * - eq551 rule_def_6_1
    first | exact resolve eq551 rule_def_6_1 | exact resolve rule_def_6_1 eq551 | grind only
  have eq556 : c = sk1 ∨ c = sk0 := by
    clear * - eq554 rule_def_5_1
    first | exact resolve eq554 rule_def_5_1 | exact resolve rule_def_5_1 eq554 | grind only
  have eq557 : c = sk1 := by
    clear * - eq556 preserve_4
    first | exact resolve eq556 preserve_4 | exact resolve preserve_4 eq556 | grind only
  have eq563 : (old sk0 c sk2) ∨ c = b ∨ b = sk2 := by
    clear * - eq265 eq557
    first | exact superpose eq265 eq557 | exact superpose eq557 eq265 | grind only
  have eq573 : c = b ∨ b = sk2 := by
    clear * - eq563 p4XZ
    first | exact resolve eq563 p4XZ | exact resolve p4XZ eq563 | grind only
  have eq578 : b = sk2 := by
    clear * - eq573 bc
    first | exact resolve eq573 bc | exact resolve bc eq573 | grind only
  have eq863 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq249 rule_def_10_1
    first | exact resolve eq249 rule_def_10_1 | exact resolve rule_def_10_1 eq249 | grind only
  have eq877 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq863 rule_def_2_0
    first | exact resolve eq863 rule_def_2_0 | exact resolve rule_def_2_0 eq863 | grind only
  have eq882 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq877 rule_def_3_0
    first | exact resolve eq877 rule_def_3_0 | exact resolve rule_def_3_0 eq877 | grind only
  have eq887 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq882 rule_def_4_0
    first | exact resolve eq882 rule_def_4_0 | exact resolve rule_def_4_0 eq882 | grind only
  have eq892 : (sP9 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq887 rule_def_8_1
    first | exact resolve eq887 rule_def_8_1 | exact resolve rule_def_8_1 eq887 | grind only
  have eq897 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk0 := by
    clear * - eq892 rule_def_9_1
    first | exact resolve eq892 rule_def_9_1 | exact resolve rule_def_9_1 eq892 | grind only
  have eq902 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq897 preserve_4
    first | exact resolve eq897 preserve_4 | exact resolve preserve_4 eq897 | grind only
  have eq907 : (sP1 sk0 sk1 b) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq902 eq578
    first | simpa only [eq578, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq902 | grind only
  have eq912 : (sP1 sk0 c b) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq907 eq557
    first | simpa only [eq557, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq907 | grind only
  have eq917 : (old sk0 sk1 b) ∨ (sP1 sk0 c b) ∨ b = sk1 := by
    clear * - eq912 eq578
    first | simpa only [eq578, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq912 | grind only
  have eq921 : (old sk0 c b) ∨ (sP1 sk0 c b) ∨ b = sk1 := by
    clear * - eq917 eq557
    first | simpa only [eq557, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq917 | grind only
  have eq922 : (sP1 sk0 c b) ∨ b = sk1 := by
    clear * - eq921 p4XZ
    first | exact resolve eq921 p4XZ | exact resolve p4XZ eq921 | grind only
  have eq923 : c = b ∨ (sP1 sk0 c b) := by
    clear * - eq922 eq557
    first | simpa only [eq557, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm] using eq922 | grind only
  have eq924 : (sP1 sk0 c b) := by
    clear * - eq923 bc
    first | exact resolve eq923 bc | exact resolve bc eq923 | grind only
  have eq929 : memold sk0 := by
    clear * - eq924 eq210
    first | exact resolve eq924 eq210 | exact resolve eq210 eq924 | grind only
  clear * - eq929 preserve_3
  first | subsumption eq929 preserve_3 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP5 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP6 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_9_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP9 X Y Z) (rule_def_10_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP10 X Y Z) (rule_def_11_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq230 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq235 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq230 rule_def_0_1
    first | exact resolve eq230 rule_def_0_1 | exact resolve rule_def_0_1 eq230 | grind only
  have eq237 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq235 rule_def_5_2
    first | exact resolve eq235 rule_def_5_2 | exact resolve rule_def_5_2 eq235 | grind only
  have eq239 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq237 rule_def_6_2
    first | exact resolve eq237 rule_def_6_2 | exact resolve rule_def_6_2 eq237 | grind only
  have eq241 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ b = sk1 := by
    clear * - eq239 rule_def_7_2
    first | exact resolve eq239 rule_def_7_2 | exact resolve rule_def_7_2 eq239 | grind only
  have eq243 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := by
    clear * - eq241 preserve_2
    first | exact resolve eq241 preserve_2 | exact resolve preserve_2 eq241 | grind only
  have eq245 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq243 rule_def_11_2
    first | exact resolve eq243 rule_def_11_2 | exact resolve rule_def_11_2 eq243 | grind only
  have eq249 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq245 rule_def_1_0
    first | exact resolve eq245 rule_def_1_0 | exact resolve rule_def_1_0 eq245 | grind only
  have eq252 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq249 rule_def_2_1
    first | exact resolve eq249 rule_def_2_1 | exact resolve rule_def_2_1 eq249 | grind only
  have eq255 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq252 rule_def_3_1
    first | exact resolve eq252 rule_def_3_1 | exact resolve rule_def_3_1 eq252 | grind only
  have eq257 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq255 rule_def_4_1
    first | exact resolve eq255 rule_def_4_1 | exact resolve rule_def_4_1 eq255 | grind only
  have eq259 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq257 rule_def_8_2
    first | exact resolve eq257 rule_def_8_2 | exact resolve rule_def_8_2 eq257 | grind only
  have eq261 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq259 rule_def_9_2
    first | exact resolve eq259 rule_def_9_2 | exact resolve rule_def_9_2 eq259 | grind only
  have eq263 : (old sk0 sk1 sk2) ∨ c = sk1 := by
    clear * - eq261 rule_def_10_2
    first | exact resolve eq261 rule_def_10_2 | exact resolve rule_def_10_2 eq261 | grind only
  have eq265 : (old sk0 sk1 sk2) := by
    clear * - eq263 preserve_4
    first | exact resolve eq263 preserve_4 | exact resolve preserve_4 eq263 | grind only
  have eq272 : memold sk1 := by
    clear * - eq265 old_mem2
    first | exact resolve eq265 old_mem2 | exact resolve old_mem2 eq265 | grind only
  clear * - eq272 preserve_3
  first | subsumption eq272 preserve_3 | grind only


set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (sP9 : G → G → G → Prop) (sP10 : G → G → G → Prop) (sP11 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP3 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP4 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP5 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP6 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP7 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (rule_def_9_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP9 X Y Z) (rule_def_10_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP10 X Y Z) (rule_def_11_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP11 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq230 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) := by
    clear * - new_imp preserve_0
    first | exact resolve new_imp preserve_0 | exact resolve preserve_0 new_imp | grind only
  have eq234 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq230 rule_def_0_2
    first | exact resolve eq230 rule_def_0_2 | exact resolve rule_def_0_2 eq230 | grind only
  have eq238 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq234 rule_def_5_3
    first | exact resolve eq234 rule_def_5_3 | exact resolve rule_def_5_3 eq234 | grind only
  have eq240 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq238 rule_def_6_3
    first | exact resolve eq238 rule_def_6_3 | exact resolve rule_def_6_3 eq238 | grind only
  have eq242 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (sP11 sk0 sk1 sk2) ∨ c = sk2 := by
    clear * - eq240 rule_def_7_3
    first | exact resolve eq240 rule_def_7_3 | exact resolve rule_def_7_3 eq240 | grind only
  have eq243 : (sP11 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := by
    clear * - eq242 preserve_4
    first | exact resolve eq242 preserve_4 | exact resolve preserve_4 eq242 | grind only
  have eq244 : (sP1 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq243 rule_def_11_3
    first | exact resolve eq243 rule_def_11_3 | exact resolve rule_def_11_3 eq243 | grind only
  have eq250 : (sP2 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq244 rule_def_1_1
    first | exact resolve eq244 rule_def_1_1 | exact resolve rule_def_1_1 eq244 | grind only
  have eq253 : (sP3 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq250 rule_def_2_2
    first | exact resolve eq250 rule_def_2_2 | exact resolve rule_def_2_2 eq250 | grind only
  have eq256 : (sP4 sk0 sk1 sk2) ∨ (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq253 rule_def_3_2
    first | exact resolve eq253 rule_def_3_2 | exact resolve rule_def_3_2 eq253 | grind only
  have eq258 : (sP8 sk0 sk1 sk2) ∨ (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq256 rule_def_4_2
    first | exact resolve eq256 rule_def_4_2 | exact resolve rule_def_4_2 eq256 | grind only
  have eq260 : (sP9 sk0 sk1 sk2) ∨ (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq258 rule_def_8_3
    first | exact resolve eq258 rule_def_8_3 | exact resolve rule_def_8_3 eq258 | grind only
  have eq262 : (sP10 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq260 rule_def_9_3
    first | exact resolve eq260 rule_def_9_3 | exact resolve rule_def_9_3 eq260 | grind only
  have eq264 : (old sk0 sk1 sk2) ∨ b = sk2 := by
    clear * - eq262 rule_def_10_3
    first | exact resolve eq262 rule_def_10_3 | exact resolve rule_def_10_3 eq262 | grind only
  have eq265 : (old sk0 sk1 sk2) := by
    clear * - eq264 preserve_2
    first | exact resolve eq264 preserve_2 | exact resolve preserve_2 eq264 | grind only
  have eq273 : memold sk2 := by
    clear * - eq265 old_mem3
    first | exact resolve eq265 old_mem3 | exact resolve old_mem3 eq265 | grind only
  clear * - eq273 preserve_3
  first | subsumption eq273 preserve_3 | grind only


structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X2 X3 ∨ ¬ R X3 X1 X4 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1, ¬ R X0 X1 X0 ∨ R X1 X1 X0)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X0 ∨ R X2 X2 X1)
  rule_4 : (∀ X0 X1, ¬ R X0 X0 X1 ∨ R X1 X0 X1)
  rule_5 : (∀ X0 X1, ¬ R X0 X0 X1 ∨ R X1 X1 X0)
  rule_6 : (∀ X0 X1, ¬ R X0 X0 X1 ∨ R X0 X1 X0)
  rule_7 : (∀ X0 X1, ¬ R X0 X1 X1 ∨ R X1 X1 X1)
  rule_8 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X2 X3 ∨ ¬ R X2 X1 X4 ∨ ¬ R X2 X4 X3 ∨ R X1 X1 X2)
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
  let sP1 (X Y Z) := ∃ sF0, c = Y ∧ b = Z ∧ ps.R X b sF0 ∧ ps.R X sF0 a
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z) := c = X ∧ c = Y ∧ b = Z ∧ ps.R b b a
  have hsP2 (X Y Z) (h : sP2 X Y Z) : c = X ∧ c = Y ∧ b = Z ∧ ps.R b b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3
  let sP3 (X Y Z) := c = X ∧ c = Y ∧ b = Z ∧ ps.R b b a
  have hsP3 (X Y Z) (h : sP3 X Y Z) : c = X ∧ c = Y ∧ b = Z ∧ ps.R b b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP3
  obtain ⟨rule_def_3_0, rule_def_3_1, rule_def_3_2, rule_def_3_3⟩ := hsP3
  simp_rw [or_comm] at rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3
  let sP4 (X Y Z) := c = X ∧ c = Y ∧ b = Z ∧ ps.R b b a
  have hsP4 (X Y Z) (h : sP4 X Y Z) : c = X ∧ c = Y ∧ b = Z ∧ ps.R b b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP4
  obtain ⟨rule_def_4_0, rule_def_4_1, rule_def_4_2, rule_def_4_3⟩ := hsP4
  simp_rw [or_comm] at rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3
  let sP5 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ c = Z
  have hsP5 (X Y Z) (h : sP5 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP5
  obtain ⟨rule_def_5_0, rule_def_5_1, rule_def_5_2, rule_def_5_3⟩ := hsP5
  simp_rw [or_comm] at rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3
  let sP6 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ c = Z
  have hsP6 (X Y Z) (h : sP6 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP6
  obtain ⟨rule_def_6_0, rule_def_6_1, rule_def_6_2, rule_def_6_3⟩ := hsP6
  simp_rw [or_comm] at rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3
  let sP7 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ c = Z
  have hsP7 (X Y Z) (h : sP7 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP7
  obtain ⟨rule_def_7_0, rule_def_7_1, rule_def_7_2, rule_def_7_3⟩ := hsP7
  simp_rw [or_comm] at rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3
  let sP8 (X Y Z) := a = b ∧ c = X ∧ c = Y ∧ b = Z
  have hsP8 (X Y Z) (h : sP8 X Y Z) : a = b ∧ c = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP8
  obtain ⟨rule_def_8_0, rule_def_8_1, rule_def_8_2, rule_def_8_3⟩ := hsP8
  simp_rw [or_comm] at rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3
  let sP9 (X Y Z) := a = b ∧ c = X ∧ c = Y ∧ b = Z
  have hsP9 (X Y Z) (h : sP9 X Y Z) : a = b ∧ c = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP9
  obtain ⟨rule_def_9_0, rule_def_9_1, rule_def_9_2, rule_def_9_3⟩ := hsP9
  simp_rw [or_comm] at rule_def_9_0 rule_def_9_1 rule_def_9_2 rule_def_9_3
  let sP10 (X Y Z) := a = b ∧ c = X ∧ c = Y ∧ b = Z
  have hsP10 (X Y Z) (h : sP10 X Y Z) : a = b ∧ c = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP10
  obtain ⟨rule_def_10_0, rule_def_10_1, rule_def_10_2, rule_def_10_3⟩ := hsP10
  simp_rw [or_comm] at rule_def_10_0 rule_def_10_1 rule_def_10_2 rule_def_10_3
  let sP11 (X Y Z) := a = b ∧ b = X ∧ c = Y ∧ b = Z
  have hsP11 (X Y Z) (h : sP11 X Y Z) : a = b ∧ b = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP11
  obtain ⟨rule_def_11_0, rule_def_11_1, rule_def_11_2, rule_def_11_3⟩ := hsP11
  simp_rw [or_comm] at rule_def_11_0 rule_def_11_1 rule_def_11_2 rule_def_11_3

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_4 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_5 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_6 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_7 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_8 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_9 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_10 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_11 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_12 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z ∨ sP9 X Y Z ∨ sP10 X Y Z ∨ sP11 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [not_and, not_exists, imp_iff_not_or, sP3, ← forall_or_right, or_assoc] at imp_new_4
  simp only [not_and, not_exists, imp_iff_not_or, sP4, ← forall_or_right, or_assoc] at imp_new_5
  simp only [not_and, not_exists, imp_iff_not_or, sP5, ← forall_or_right, or_assoc] at imp_new_6
  simp only [not_and, not_exists, imp_iff_not_or, sP6, ← forall_or_right, or_assoc] at imp_new_7
  simp only [not_and, not_exists, imp_iff_not_or, sP7, ← forall_or_right, or_assoc] at imp_new_8
  simp only [not_and, not_exists, imp_iff_not_or, sP8, ← forall_or_right, or_assoc] at imp_new_9
  simp only [not_and, not_exists, imp_iff_not_or, sP9, ← forall_or_right, or_assoc] at imp_new_10
  simp only [not_and, not_exists, imp_iff_not_or, sP10, ← forall_or_right, or_assoc] at imp_new_11
  simp only [not_and, not_exists, imp_iff_not_or, sP11, ← forall_or_right, or_assoc] at imp_new_12
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 bc p3 p4XY p4XZ p4YZ ps.rule_0 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_1 rule_def_2_2 rule_def_3_1 rule_def_3_2 rule_def_4_1 rule_def_4_2 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_2 rule_def_8_3 rule_def_9_2 rule_def_9_3 rule_def_10_2 rule_def_10_3 rule_def_11_2 rule_def_11_3 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 ac bc p3 p4XY p4XZ p4YZ new_new ps.rule_0 prev_0 ps.rule_1 ps.rule_4 ps.rule_5 ps.rule_7 ps.rule_8 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 imp_new_8 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 rule_def_9_0 rule_def_9_1 rule_def_9_2 rule_def_9_3 imp_new_11 rule_def_10_0 rule_def_10_1 rule_def_10_2 rule_def_10_3 imp_new_12 rule_def_11_0 rule_def_11_1 rule_def_11_2 rule_def_11_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 ac bc p4XY p4XZ new_new ps.rule_0 ps.rule_2 ps.rule_6 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_2 rule_def_3_0 rule_def_3_2 rule_def_4_0 rule_def_4_2 rule_def_5_0 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_2 rule_def_7_3 rule_def_8_1 rule_def_8_3 rule_def_9_1 rule_def_9_3 imp_new_11 rule_def_10_1 rule_def_10_3 rule_def_11_0 rule_def_11_1 rule_def_11_2 new_imp imp_new_0
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 ac bc p4XY p4XZ p4YZ new_new ps.rule_0 prev_0 ps.rule_4 ps.rule_5 ps.rule_6 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_2 rule_def_8_3 rule_def_9_0 rule_def_9_2 rule_def_9_3 imp_new_11 rule_def_10_0 rule_def_10_1 rule_def_10_2 rule_def_10_3 rule_def_11_0 rule_def_11_1 rule_def_11_2 rule_def_11_3 new_imp imp_new_0
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 ac bc p3 p4XY p4XZ p4YZ ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_1 rule_def_6_2 rule_def_6_3 imp_new_8 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_2 rule_def_8_3 rule_def_9_0 rule_def_9_2 rule_def_9_3 rule_def_10_0 rule_def_10_1 rule_def_10_2 rule_def_10_3 imp_new_12 rule_def_11_1 rule_def_11_2 new_imp imp_new_0
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 prev_3 prev_4
  have prev_6 := rule_6_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 prev_4 prev_5
  have prev_7 := rule_7_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 bc ps.rule_7 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_1 rule_def_2_2 rule_def_3_1 rule_def_3_2 rule_def_4_1 rule_def_4_2 rule_def_5_2 rule_def_5_3 rule_def_6_2 rule_def_6_3 rule_def_7_2 rule_def_7_3 rule_def_8_2 rule_def_8_3 rule_def_9_2 rule_def_9_3 rule_def_10_2 rule_def_10_3 rule_def_11_2 rule_def_11_3 new_imp imp_new_0
  have prev_8 := rule_8_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 ac bc p3 p4XY p4XZ p4YZ new_new prev_0 prev_1 prev_2 prev_5 prev_7 ps.rule_8 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 rule_def_9_0 rule_def_9_1 rule_def_9_2 rule_def_9_3 imp_new_11 rule_def_10_0 rule_def_10_1 rule_def_10_2 rule_def_10_3 imp_new_12 rule_def_11_0 rule_def_11_1 rule_def_11_2 rule_def_11_3 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    rule_6 := prev_6
    rule_7 := prev_7
    rule_8 := prev_8
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 (· ∈ ps.finsupp) bc p4XY p4XZ rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_1 rule_def_8_2 rule_def_8_3 rule_def_9_1 rule_def_9_2 rule_def_9_3 rule_def_10_1 rule_def_10_2 rule_def_10_3 rule_def_11_1 rule_def_11_2 rule_def_11_3 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_0 rule_def_2_1 rule_def_3_1 rule_def_4_1 rule_def_5_2 rule_def_6_2 rule_def_7_2 rule_def_8_2 rule_def_9_2 rule_def_10_2 rule_def_11_2 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 sP9 sP10 sP11 (· ∈ ps.finsupp) rule_def_0_2 rule_def_1_1 rule_def_2_2 rule_def_3_2 rule_def_4_2 rule_def_5_3 rule_def_6_3 rule_def_7_3 rule_def_8_3 rule_def_9_3 rule_def_10_3 rule_def_11_3 new_imp ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X0 X2 X3 ∨ ¬ ps.compl X3 X1 X4 ∨ ps.compl X0 X4 X1 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X0 X2) (max (Nat.pair X3 X1) (max (Nat.pair X0 X4) 0)))
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

theorem PartialSolution.toMagma_equation1119 :
    letI := ps.toMagma
    Equation1119 ℕ := by
  simp only [Equation1119]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X1 X0 (ps.complFun X1 X0) (ps.complFun X1 (ps.complFun X1 X0)) (ps.complFun (ps.complFun X1 (ps.complFun X1 X0)) X0)

end Eq1119
