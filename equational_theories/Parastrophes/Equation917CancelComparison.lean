import equational_theories.Parastrophes.Equation917BalancedComparison

/-!
# A comparison with unit shifts on both sides

Write q(x)=(x*(x*x))*x, U(x)=x*q(x), and H(x,y)=q(x)*(x*y).
The proposed identity is

    x = (((U(w)*(y*z))*v) * H(x,U(w*(y*U(z)))*v)).

It has 48 operations and five variables. Its forward implication, surjective
rows, and exact finite permutation reduction are proved here. Its converse
remains open; no characterization attribute is attached.

The placement of the three U occurrences comes from a displacement calculation:
if multiplication sends input shifts s,t to A*s+B*t, the compared shifts have
difference A*(A-1-B^2). Under A=-B^3 and B^6+B^5+B^3+1=0 this is -1. This
motivates the candidate; it is not an assumption that arbitrary magmas have
such coordinates, nor a proof of its converse.

The operation count includes duplication under U: U(t) contains five copies
of t. Its right tree has 34 operations, its left tree has six, the two final
products add two, and the outer crossed frame adds six.
-/
namespace Parastrophes.Eq917Image.CancelComparison
open Law FreeMagma
open SandwichCandidate (U H)

variable {A : Type} (D : Magma A)

def leftTree (w y z : A) := D.op (U D w) (D.op y z)
def rightTree (w y z : A) := U D (D.op w (D.op y (U D z)))
def Identity : Prop := ∀ x w y z v,
  x = D.op (D.op (leftTree D w y z) v) (H D x (D.op (rightTree D w y z) v))

/-- A syntax-level record, deliberately without a characterization attribute. -/
def candidateLaw : NatMagmaLaw :=
  let q (t : FreeMagma Nat) := (t ⋆ (t ⋆ t)) ⋆ t
  let u (t : FreeMagma Nat) := t ⋆ q t
  let x := Lf 0
  let w := Lf 1
  let y := Lf 2
  let z := Lf 3
  let v := Lf 4
  ⟨x, ((u w ⋆ (y ⋆ z)) ⋆ v) ⋆ (q x ⋆ (x ⋆ (u (w ⋆ (y ⋆ u z)) ⋆ v)))⟩

theorem candidateLaw_iff : @satisfies _ A D candidateLaw ↔ Identity D := by
  constructor
  · intro h x w y z v
    exact h (fun n => if n=0 then x else if n=1 then w else if n=2 then y else if n=3 then z else v)
  · intro h v
    exact h (v 0) (v 1) (v 2) (v 3) (v 4)

theorem candidate_operation_count : candidateLaw.lhs.forks+candidateLaw.rhs.forks=48 := by decide

theorem of_basis (h : Basis D) : Identity D := by
  have hu (x) : U D x = x := (h.1 x).symm
  intro x w y z v
  simp only [leftTree, rightTree, hu]
  exact h.2 x _

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hm, hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))

/-- One onto row creates an onto U-row. That row can be made a left-tree
value, and then supplies every row index. No finiteness is used. -/
theorem rows_surjective (h : Identity D) : ∀ a, Function.Surjective (D.op a) := by
  have good (w y z v : A) : Function.Surjective (D.op (D.op (leftTree D w y z) v)) :=
    fun x => ⟨_, (h x w y z v).symm⟩
  intro o
  let i := leftTree D o o o
  have hi : Function.Surjective (D.op (U D i)) := good o o o (core D i)
  obtain ⟨t, ht⟩ := hi (U D i)
  obtain ⟨z, hz⟩ := hi t
  have hs : leftTree D i (U D i) z = U D i := by
    dsimp only [leftTree]
    rw [hz, ht]
  obtain ⟨v, hv⟩ := hi o
  simpa only [hs, hv] using good i (U D i) z v

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D := by
  have hq : IsSideQuasigroup .left D := fun x =>
    ⟨Finite.injective_iff_surjective.mpr (rows_surjective D h x), rows_surjective D h x⟩
  refine ⟨hq, fun o => ?_⟩
  classical
  let le (x : A) := Equiv.ofBijective (D.op x) (hq x)
  let j := rightTree D o o o
  let k := leftTree D o o o
  let c : A ≃ A := (le j).symm.trans (le k)
  have frame (x y : A) : D.op (c y) (H D x y) = x := by
    have he := (h x o o o ((le j).symm y)).symm
    change D.op ((le k) ((le j).symm y))
      (H D x ((le j) ((le j).symm y))) = x at he
    simpa only [(le j).apply_symm_apply] using he
  have col : Function.Injective (fun y => D.op y o) := by
    intro y z he
    let x := D.op y o
    have hy : H D x (c.symm y) = o := by
      apply (hq y).1
      simpa only [c.apply_symm_apply] using frame x (c.symm y)
    have hz : H D x (c.symm z) = o := by
      apply (hq z).1
      simpa only [c.apply_symm_apply] using (frame x (c.symm z)).trans he
    exact c.symm.injective (((hq (core D x)).1.comp (hq x).1) (hy.trans hz.symm))
  exact ⟨col, Finite.surjective_of_injective col⟩

/-- The finite candidate is exactly a system of three common permutations.
Its second rule couples a left shift of U to a right shift of d; neither
shift is silently assumed to be the identity or to commute with another. -/
theorem reduction [Finite A] [Nonempty A] (h : Identity D) :
    Function.Bijective (U D) ∧ ∃ d g c : A ≃ A,
      (∀ x y, D.op x (U D y) = d (D.op x y)) ∧
      (∀ x y, D.op (U D x) y = g (U D (D.op x (d y)))) ∧
      (∀ x y, D.op (g x) y = c (D.op x y)) ∧
      (∀ x y, D.op (c y) (H D x y) = x) := by
  classical
  let o : A := Classical.choice inferInstance
  have hq := quasigroup D h
  let le (x : A) := Equiv.ofBijective (D.op x) (hq.1 x)
  let re (x : A) := Equiv.ofBijective (fun y => D.op y x) (hq.2 x)
  let j := rightTree D o o o
  let k := leftTree D o o o
  let c : A ≃ A := (le j).symm.trans (le k)
  have frame (x y : A) : D.op (c y) (H D x y) = x := by
    have he := (h x o o o ((le j).symm y)).symm
    change D.op ((le k) ((le j).symm y))
      (H D x ((le j) ((le j).symm y))) = x at he
    simpa only [(le j).apply_symm_apply] using he
  have comparison (w y z v : A) :
      D.op (leftTree D w y z) v = c (D.op (rightTree D w y z) v) := by
    apply (hq.2 (H D o (D.op (rightTree D w y z) v))).1
    exact (h o w y z v).symm.trans (frame o _).symm
  let g : A ≃ A := (re o).trans (c.trans (re o).symm)
  have middle (w y z : A) : leftTree D w y z = g (rightTree D w y z) := by
    apply (re o).injective
    change D.op (leftTree D w y z) o =
      (re o) ((re o).symm (c ((re o) (rightTree D w y z))))
    rw [(re o).apply_symm_apply]
    exact comparison w y z o
  have ui : Function.Injective (U D) := by
    intro x y he
    apply (hq.1 o).1
    apply (hq.1 (U D o)).1
    change leftTree D o o x = leftTree D o o y
    rw [middle, middle]
    simp only [rightTree, he]
  have ub : Function.Bijective (U D) := ⟨ui, Finite.surjective_of_injective ui⟩
  let ue := Equiv.ofBijective (U D) ub
  let d : A ≃ A := (le (U D o)).trans (g.symm.trans (ue.symm.trans (le o).symm))
  have first (x y : A) : D.op x (U D y) = d (D.op x y) := by
    apply (le o).injective
    apply ue.injective
    apply g.injective
    change g (U D (D.op o (D.op x (U D y)))) =
      g (ue ((le o) ((le o).symm (ue.symm (g.symm ((le (U D o)) (D.op x y)))))))
    rw [(le o).apply_symm_apply, ue.apply_symm_apply, g.apply_symm_apply]
    exact (middle o x y).symm
  have second (x y : A) : D.op (U D x) y = g (U D (D.op x (d y))) := by
    obtain ⟨z, rfl⟩ := (hq.1 o).2 y
    rw [← first]
    exact middle x o z
  have third (x y : A) : D.op (g x) y = c (D.op x y) := by
    obtain ⟨z, rfl⟩ := (ub.comp ((hq.1 o).comp ((hq.1 o).comp ub))).2 x
    change D.op (g (rightTree D o o z)) y = c (D.op (rightTree D o o z) y)
    rw [← middle]
    exact comparison o o z y
  exact ⟨ub, d, g, c, first, second, third, frame⟩

theorem of_reduction (d g c : A → A)
    (hd : ∀ x y, D.op x (U D y) = d (D.op x y))
    (hg : ∀ x y, D.op (U D x) y = g (U D (D.op x (d y))))
    (hc : ∀ x y, D.op (g x) y = c (D.op x y))
    (hf : ∀ x y, D.op (c y) (H D x y) = x) : Identity D := by
  intro x w y z v
  dsimp only [leftTree, rightTree]
  rw [hg w, ← hd y z, hc, hf]

/-- The common right action makes every cycle of U have the same length.
This justifies fixing a uniform cycle decomposition in finite model searches. -/
theorem unit_iterate_fixed [Finite A] (h : Identity D) (n : ℕ) (o : A)
    (ho : (U D)^[n] o=o) : ∀ x, (U D)^[n] x=x := by
  letI : Nonempty A := ⟨o⟩
  obtain ⟨_, d, _, _, hd, _, _, _⟩ := reduction D h
  have hq := quasigroup D h
  have step (k : ℕ) (x y : A) :
      D.op x ((U D)^[k] y) = (d : A → A)^[k] (D.op x y) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', hd, ih]
  have did (x : A) : (d : A → A)^[n] x=x := by
    obtain ⟨y, rfl⟩ := (hq.2 o).2 x
    rw [← step, ho]
  intro x
  apply (hq.1 o).1
  rw [step, did]

theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : U D o=o) : Basis D := by
  have hu : ∀ x, U D x=x := by
    simpa only [Function.iterate_one] using unit_iterate_fixed D h 1 o ho
  have hq := quasigroup D h
  refine ⟨fun x => (hu x).symm, ?_⟩
  intro x y
  obtain ⟨v, hv⟩ := (hq.1 (D.op o (D.op o o))).2 y
  have he := h x o o o v
  simpa only [leftTree, rightTree, hu, hv, H] using he

theorem commuting_outputs [Finite A] (h : Identity D) (d g c : A → A)
    (hd : ∀ x y, D.op x (U D y) = d (D.op x y))
    (hc : ∀ x y, D.op (g x) y = c (D.op x y)) : Function.Commute c d := by
  intro x
  obtain ⟨y, hy⟩ := ((quasigroup D h).1 x).2 x
  have he : D.op (g x) (U D y) = D.op (g x) (U D y) := rfl
  conv_lhs at he => rw [hc, hd]
  conv_rhs at he => rw [hd, hc]
  simpa only [hy] using he

end Parastrophes.Eq917Image.CancelComparison
