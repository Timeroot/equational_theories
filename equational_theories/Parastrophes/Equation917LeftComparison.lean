import equational_theories.Parastrophes.Equation917SandwichCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.ReduceModChar

/-!
# A shorter comparison identity for E917's left image

Write `q(x)=(x*(x*x))*x`, `U(x)=x*q(x)` and `H(x,y)=q(x)*(x*y)`.
The twelve-operation candidate is

    x = (U(z)*y) * H(x,z*y).

It holds in every actual image. Conversely, it forces surjective rows on any
carrier and a quasigroup on finite carriers. On a nonempty finite carrier it
is equivalent to the existence of a permutation a such that

    U(x)*y=a(x*y),       a(y)*H(x,y)=x.

The remaining step, proving U=id, is FALSE: the extension at the end of this
file is a 25-element counterexample. This is a refutation of this particular
candidate, not of every single-equation characterization.
-/
namespace Parastrophes.Eq917Image.LeftComparison
open SandwichCandidate (U H)

variable {A : Type} (D : Magma A)

def Identity : Prop := ∀ x y z,
  x = D.op (D.op (U D z) y) (H D x (D.op z y))

theorem of_basis (h : Basis D) : Identity D := by
  intro x y z
  have hz : U D z = z := (h.1 z).symm
  rw [hz]
  exact h.2 x _

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hm, hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))

/-- One row indexed by U²(t) is onto. It supplies every other row index. -/
theorem rows_surjective (h : Identity D) : ∀ a, Function.Surjective (D.op a) := by
  have hs (y z : A) : Function.Surjective (D.op (D.op (U D z) y)) :=
    fun x => ⟨_, (h x y z).symm⟩
  intro t
  have hr : Function.Surjective (D.op (U D (U D t))) := hs (core D (U D t)) t
  obtain ⟨y, hy⟩ := hr t
  simpa only [hy] using hs y (U D t)

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D := by
  have hq : IsSideQuasigroup .left D := fun x =>
    ⟨Finite.injective_iff_surjective.mpr (rows_surjective D h x),
      rows_surjective D h x⟩
  refine ⟨hq, fun t => ?_⟩
  classical
  let le (x : A) := Equiv.ofBijective (D.op x) (hq x)
  let a : A ≃ A := (le t).symm.trans (le (U D t))
  have frame (x y : A) : D.op (a y) (H D x y) = x := by
    have he := (h x ((le t).symm y) t).symm
    change D.op ((le (U D t)) ((le t).symm y))
      (H D x ((le t) ((le t).symm y))) = x at he
    simpa only [(le t).apply_symm_apply] using he
  have col : Function.Injective (fun y => D.op y t) := by
    intro y z he
    let x := D.op y t
    have hy : H D x (a.symm y) = t := by
      apply (hq y).1
      simpa only [a.apply_symm_apply] using frame x (a.symm y)
    have hz : H D x (a.symm z) = t := by
      apply (hq z).1
      simpa only [a.apply_symm_apply] using (frame x (a.symm z)).trans he
    have hh := ((hq (core D x)).1.comp (hq x).1) (hy.trans hz.symm)
    exact a.symm.injective hh
  exact ⟨col, Finite.surjective_of_injective col⟩

theorem reduction [Finite A] [Nonempty A] (h : Identity D) :
    ∃ a : A ≃ A,
      (∀ x y, D.op (U D x) y = a (D.op x y)) ∧
      (∀ x y, D.op (a y) (H D x y) = x) := by
  classical
  let o : A := Classical.choice inferInstance
  have hq := quasigroup D h
  let le (x : A) := Equiv.ofBijective (D.op x) (hq.1 x)
  let a : A ≃ A := (le o).symm.trans (le (U D o))
  have frame (x y : A) : D.op (a y) (H D x y) = x := by
    have he := (h x ((le o).symm y) o).symm
    change D.op ((le (U D o)) ((le o).symm y))
      (H D x ((le o) ((le o).symm y))) = x at he
    simpa only [(le o).apply_symm_apply] using he
  refine ⟨a, ?_, frame⟩
  intro x y
  apply (hq.2 (H D o (D.op x y))).1
  exact (h o y x).symm.trans (frame o _).symm

theorem of_reduction (a : A → A)
    (ha : ∀ x y, D.op (U D x) y = a (D.op x y))
    (hf : ∀ x y, D.op (a y) (H D x y) = x) : Identity D := by
  intro x y z
  rw [ha, hf]

/-- The period of U at any one point is a period at every point. In
particular a nontrivial U has no fixed points and has uniform cycle length. -/
theorem unit_iterate_fixed [Finite A] (h : Identity D) (n : Nat) (o : A)
    (ho : (U D)^[n] o = o) : ∀ x, (U D)^[n] x = x := by
  letI : Nonempty A := ⟨o⟩
  obtain ⟨a, ha, _⟩ := reduction D h
  have hq := quasigroup D h
  have step (k : Nat) (x y : A) :
      D.op ((U D)^[k] x) y = (a : A → A)^[k] (D.op x y) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', ha, ih]
  have aid (x : A) : (a : A → A)^[n] x = x := by
    obtain ⟨y, rfl⟩ := (hq.1 o).2 x
    exact (step n o y).symm.trans (by rw [ho])
  intro x
  apply (hq.2 o).1
  change D.op ((U D)^[n] x) o = D.op x o
  rw [step, aid]

theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : U D o = o) : Basis D := by
  have hu : ∀ x, U D x = x := by
    simpa only [Function.iterate_one] using unit_iterate_fixed D h 1 o ho
  have hq := quasigroup D h
  refine ⟨fun x => (hu x).symm, fun x y => ?_⟩
  obtain ⟨z, hz⟩ := (hq.1 o).2 y
  simpa only [hu, hz] using h x z o

/-! A symbolic counterexample. The five-element quotient is a genuine E917
division image. Only its 25 offsets are stored; all fibre calculations are
ring calculations in characteristic five, rather than 25³ assignments. -/
namespace Counterexample

def base : Fin 5 → Fin 5 → Fin 5 :=
  ![![4,0,1,3,2], ![0,2,3,4,1], ![1,3,0,2,4], ![3,4,2,1,0], ![2,1,4,0,3]]

@[implicit_reducible] def baseMagma : Magma (Fin 5) := ⟨base⟩

theorem base_image : InImage Law917 .left baseMagma := by
  apply (characterizes_fin baseMagma).mp
  unfold Basis Cross
  decide

def offset : Fin 5 → Fin 5 → ZMod 5 :=
  ![![4,1,2,2,2], ![3,1,1,3,3], ![3,0,0,1,2], ![0,4,3,0,4], ![1,0,0,0,0]]

@[implicit_reducible] def model : Magma (Fin 5 × ZMod 5) :=
  ⟨fun x y => (base x.1 y.1, 3*x.2 + 3*y.2 + offset x.1 y.1)⟩

@[simp] theorem model_op (x y : Fin 5 × ZMod 5) :
    model.op x y = (base x.1 y.1, 3*x.2 + 3*y.2 + offset x.1 y.1) := rfl

def square : Fin 5 → Fin 5 := ![1,4,3,0,2]
def coreOffset : Fin 5 → ZMod 5 := ![0,1,0,2,2]

theorem core_formula (x : Fin 5 × ZMod 5) :
    core model x = (square x.1, x.2 + coreOffset x.1) := by
  rcases x with ⟨i,u⟩
  fin_cases i <;> apply Prod.ext <;>
    simp [core, model_op, base, offset, square, coreOffset] <;>
    ring_nf <;> reduce_mod_char

theorem unit_formula (x : Fin 5 × ZMod 5) : U model x = (x.1, x.2+1) := by
  unfold U
  rw [core_formula]
  rcases x with ⟨i,u⟩
  fin_cases i <;> apply Prod.ext <;>
    simp [model_op, base, offset, square, coreOffset] <;>
    ring_nf <;> reduce_mod_char

def shift (x : Fin 5 × ZMod 5) := (x.1, x.2+3)

theorem regular (x y : Fin 5 × ZMod 5) :
    model.op (U model x) y = shift (model.op x y) := by
  rw [unit_formula]
  apply Prod.ext
  · rfl
  · change 3*(x.2+1)+3*y.2+offset x.1 y.1 =
      (3*x.2+3*y.2+offset x.1 y.1)+3
    ring

theorem frame (x y : Fin 5 × ZMod 5) :
    model.op (shift y) (H model x y) = x := by
  unfold H
  rw [core_formula]
  rcases x with ⟨i,u⟩
  rcases y with ⟨j,v⟩
  fin_cases i <;> fin_cases j <;> apply Prod.ext <;>
    simp [model_op, shift, base, offset, square, coreOffset] <;>
    ring_nf <;> reduce_mod_char

theorem identity : Identity model := of_reduction model shift regular frame

theorem not_image : ¬ InImage Law917 .left model := by
  rintro ⟨M, hM, hd⟩
  have he := (forward M model hd ((@Law917.models_iff _ M).mp hM)).1 (0,0)
  have hz : U model (0,0) = (0,0) := he.symm
  rw [unit_formula] at hz
  exact (by decide : (1 : ZMod 5) ≠ 0) (congrArg Prod.snd hz)

/-- The bad model is itself a quasigroup, so adding cancellation hypotheses
cannot repair this proposed characterization. -/
theorem model_quasigroup : IsQuasigroup model := quasigroup model identity

end Counterexample

end Parastrophes.Eq917Image.LeftComparison
