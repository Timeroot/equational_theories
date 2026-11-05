import equational_theories.Parastrophes.Equation1518Uniform
import equational_theories.Parastrophes.Equation1518SquareCycles
import Mathlib.Tactic.FinCases

/-!
# A finite lower bound for E1518 uniform division terms

A new central extension of the fifteen-element seed has no inverse-square
term of depth at most four at the point (0,0). The certificate lists the
values generated at each of the first four depths and checks closure from
one layer to the next. Induction covers ALL terms of those depths, rather
than just a sampled list of proposed terms. An explicit depth-five term
attains the inverse square in this model. This is a lower bound, not a
negative answer to unrestricted uniform term recovery.
-/
namespace Parastrophes.Eq1518TermDepth
open FreeMagma Eq1518SquareCycles
open Eq1518Uniform (termDepth)

def offset : Fin 15 → Fin 15 → ZMod 3 := ![
    ![0,0,0,2,0,2,0,2,0,0,0,1,0,1,0],
    ![0,0,0,0,2,1,0,1,2,0,0,0,0,2,0],
    ![0,0,0,0,0,0,0,1,1,1,0,0,0,0,0],
    ![0,0,0,0,0,1,0,0,1,0,2,0,1,0,0],
    ![1,1,0,0,0,1,0,1,1,1,1,0,0,1,0],
    ![2,0,0,2,0,1,0,1,0,0,2,2,0,2,1],
    ![1,0,0,2,0,1,0,1,2,1,2,2,1,2,2],
    ![0,1,1,1,2,2,0,2,2,1,2,2,2,0,2],
    ![1,2,0,1,0,1,2,2,1,1,1,0,2,2,2],
    ![0,0,1,0,0,2,1,0,1,0,1,0,2,2,1],
    ![2,2,0,2,2,0,0,2,0,0,2,0,2,2,1],
    ![2,0,0,0,2,1,2,0,2,1,2,1,2,1,0],
    ![0,0,0,2,0,2,0,0,0,1,2,0,0,0,0],
    ![1,2,0,1,2,1,0,1,1,0,2,2,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  ]

theorem offset_condition : ∀ x y : Fin 15,
    offset y x + offset x (seed.op y x) +
      offset (seed.op y y) (seed.op x (seed.op y x)) = 0 := by decide

@[implicit_reducible] def model : Magma (Fin 15 × ZMod 3) := extension seed offset

theorem model_law : @Equation1518 (Fin 15 × ZMod 3) model :=
  extension_law seed seed_law offset offset_condition

def index (x : Fin 15 × ZMod 3) : ℕ := 3*x.1.val+x.2.val

def balls : Fin 5 → List ℕ := ![
    [0],
    [0,3],
    [0,3,6,36],
    [0,3,6,9,12,18,21,27,33,36,39],
    [0,1,3,4,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,26,27,28,29,30,31,33,34,36,37,38,39,42,43,44]
  ]

theorem ball_base : ∀ n : Fin 5, index (0,0) ∈ balls n := by decide

def point (n : ℕ) : Fin 15 × ZMod 3 :=
  (⟨n / 3 % 15, Nat.mod_lt _ (by decide)⟩, n)

theorem point_index : ∀ x : Fin 15 × ZMod 3, point (index x) = x := by decide

/-- Check only pairs in the preceding layer, rather than all 45² pairs. -/
theorem ball_step_data : ∀ n : Fin 4,
    (balls n.castSucc).all (fun a => (balls n.castSucc).all (fun b =>
      (balls n.succ).contains (index (model.op (point a) (point b))))) = true := by
  decide +kernel

theorem ball_step (n : Fin 4) (x y : Fin 15 × ZMod 3)
    (hx : index x ∈ balls n.castSucc) (hy : index y ∈ balls n.castSucc) :
    index (model.op x y) ∈ balls n.succ := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp (ball_step_data n) _ hx) _ hy
  simpa only [point_index] using List.contains_iff_mem.mp h

theorem ball_no_root : ∀ x : Fin 15 × ZMod 3,
    index x ∈ balls 4 → model.op x x ≠ (0,0) := by decide

theorem eval_mem (t : FreeMagma (Fin 2)) (n : Fin 5) (ht : termDepth t ≤ n.val) :
    index (@evalInMagma _ _ model (fun _ => (0,0)) t) ∈ balls n := by
  induction t generalizing n with
  | Leaf i => exact ball_base n
  | Fork t u ihT ihU =>
    have hn : 0 < n.val := by simp only [termDepth] at ht; omega
    let k : Fin 4 := ⟨n.val-1, by omega⟩
    have hkn : k.succ = n := by apply Fin.ext; simp only [Fin.val_succ]; dsimp [k]; omega
    rw [← hkn]
    apply ball_step k
    · exact ihT k.castSucc (by simp only [termDepth] at ht; dsimp [k]; omega)
    · exact ihU k.castSucc (by simp only [termDepth] at ht; dsimp [k]; omega)

theorem no_shallow_squareRoot (t : FreeMagma (Fin 2)) (ht : termDepth t ≤ 4) :
    ¬ Eq1518Uniform.SquareRootWitness t := by
  intro h
  have hm := h _ model inferInstance model_law (0,0)
  have he := ball_no_root _ (eval_mem t 4 ht)
  apply he
  simpa only [termMagma, Magma.op, ite_self] using hm

/-- Any term closing the finite uniform-division row has depth at least five. -/
theorem division_depth_lower_bound (t : FreeMagma (Fin 2))
    (h : UniformTermWitness .fin Law1518 .left t) : 5 ≤ termDepth t := by
  by_contra hn
  exact no_shallow_squareRoot t (by omega) (Eq1518Uniform.root_of_division h)

def attainingTerm : FreeMagma (Fin 2) := (Lf 0 ⋆ ((Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)))))

theorem attaining_depth : termDepth attainingTerm = 5 := by decide

theorem attaining_root :
    let x := (termMagma model attainingTerm).op (0,0) (0,0)
    model.op x x = (0,0) := by decide

end Parastrophes.Eq1518TermDepth
