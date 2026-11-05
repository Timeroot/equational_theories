import equational_theories.Equations.All
import Mathlib.Tactic

/-! E1075 and E1278 admit integer models whose zero row is translation by one.
Thus no positive iterate of a left translation is forced to be the identity.
These models have bijective rows; they do not settle the remaining collision
questions. -/
namespace Parastrophes.TranslationPeriods

def sign2 (x : Int) : Int := if x % 2 = 0 then 1 else -1

def sign4 (x : Int) : Int := if x % 4 < 2 then 1 else -1

theorem sign2_step (x : Int) : sign2 (x + sign2 x) = -sign2 x := by
  unfold sign2
  split_ifs <;> omega

theorem sign4_step (x y : Int) : sign4 (y + 2 * sign4 x) = -sign4 y := by
  unfold sign4
  split_ifs <;> omega

@[implicit_reducible] def model1278 : Magma Int := ⟨fun x y => y + sign2 x⟩
@[implicit_reducible] def model1075 : Magma Int := ⟨fun x y => y + sign4 x⟩

theorem model1278_law : @Equation1278 Int model1278 := by
  intro x y
  change x = x + sign2 (y + sign2 (x + sign2 x)) + sign2 y
  rw [sign2_step]
  have hs : sign2 (y - sign2 x) = -sign2 y := by
    unfold sign2
    split_ifs <;> omega
  rw [← sub_eq_add_neg, hs]
  omega

theorem model1075_law : @Equation1075 Int model1075 := by
  intro x y
  change x = x + sign4 (y + sign4 x + sign4 x) + sign4 y
  rw [show y + sign4 x + sign4 x = y + 2 * sign4 x by omega, sign4_step]
  omega

theorem model1278_iterate (n : Nat) (y : Int) :
    ((model1278.op 0)^[n]) y = y + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change y + n + sign2 0 = y + (n + 1 : Nat)
    norm_num [sign2]
    omega

theorem model1075_iterate (n : Nat) (y : Int) :
    ((model1075.op 0)^[n]) y = y + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change y + n + sign4 0 = y + (n + 1 : Nat)
    norm_num [sign4]
    omega

theorem model1278_no_period {n : Nat} (hn : 0 < n) :
    (model1278.op 0)^[n] ≠ id := by
  intro h
  have he := congrFun h 0
  rw [model1278_iterate] at he
  simp only [zero_add, id_eq] at he
  omega

theorem model1075_no_period {n : Nat} (hn : 0 < n) :
    (model1075.op 0)^[n] ≠ id := by
  intro h
  have he := congrFun h 0
  rw [model1075_iterate] at he
  simp only [zero_add, id_eq] at he
  omega

theorem model1278_left_bijective (a : Int) : Function.Bijective (model1278.op a) := by
  refine ⟨fun _ _ h => add_right_cancel h, fun y => ⟨y - sign2 a, ?_⟩⟩
  change y - sign2 a + sign2 a = y
  omega

theorem model1075_left_bijective (a : Int) : Function.Bijective (model1075.op a) := by
  refine ⟨fun _ _ h => add_right_cancel h, fun y => ⟨y - sign4 a, ?_⟩⟩
  change y - sign4 a + sign4 a = y
  omega

end Parastrophes.TranslationPeriods
