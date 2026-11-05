import equational_theories.Parastrophes.Equation917SandwichCandidate
import Mathlib.GroupTheory.Perm.Sign

/-!
# A shorter E917 image candidate with a common crossed permutation

Put q(x)=(x*(x*x))*x, U(x)=x*q(x), H(x,y)=q(x)*(x*y), and
F(x,y)=y*H(x,y). The proposed equation is

    x = (U(y)*v) * H(x,F(y*v,z)).

It has 22 operations after expansion. Every actual E917 left image satisfies
it. This file does NOT prove its general converse and registers no
characterization attribute.

The outer rows are onto even on infinite carriers: they include the row at
U²(o), whose values then supply every row index. Finiteness supplies row
cancellation, which removes z and gives a common F-map a. Comparing the
original equation for two inputs shows a is injective; surjectivity of a then
also gives column cancellation. The exact finite reduction is

    F(x,y)=a(x),  U(x)*y=b(x*y),  a(x)*y=a(b(x)*y),

with a,b permutations. Thus every U-cycle has the same length. A single fixed
point forces U=id; comparing two evaluations of q(q(x)) then forces a=id.
Finding that fixed point without an extra hypothesis is still open.
-/
namespace Parastrophes.Eq917Image.FrontProduct
open Law FreeMagma
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)

def Identity : Prop := ∀ x y v z,
  x = D.op (D.op (U D y) v) (H D x (F D (D.op y v) z))

theorem of_basis (h : Basis D) : Identity D := by
  intro x y v z
  have hu (t) : U D t=t := (h.1 t).symm
  have hf (s t) : F D s t=s := (h.2 s t).symm
  rw [hu, hf]
  exact h.2 x _

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M,hm,hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))

theorem rows_surjective (h : Identity D) : ∀ a, Function.Surjective (D.op a) := by
  have good (y v : A) : Function.Surjective (D.op (D.op (U D y) v)) :=
    fun x => ⟨_, (h x y v y).symm⟩
  intro o
  have hh : Function.Surjective (D.op (U D (U D o))) := good o (core D (U D o))
  obtain ⟨v, hv⟩ := hh o
  simpa only [hv] using good (U D o) v

theorem rows [Finite A] (h : Identity D) : IsSideQuasigroup .left D :=
  fun a => ⟨Finite.injective_iff_surjective.mpr (rows_surjective D h a), rows_surjective D h a⟩

theorem common [Finite A] (h : Identity D) (o : A) :
    ∃ a : A ≃ A, ∀ x y, F D x y = a x := by
  classical
  have hq := rows D h
  let a := fun x => F D x o
  have ha (x z) : F D x z=a x := by
    obtain ⟨v, rfl⟩ := (hq o).2 x
    have he := (h o o v z).symm.trans (h o o v o)
    exact (hq o).1 ((hq (core D o)).1 ((hq (D.op (U D o) v)).1 he))
  have hi : Function.Injective a := by
    intro x y he
    have hh (t) : H D x t=H D y t := by
      apply (hq t).1
      exact (ha x t).trans (he.trans (ha y t).symm)
    exact (h x o o o).trans ((congrArg (D.op (D.op (U D o) o)) (hh _)).trans (h y o o o).symm)
  exact ⟨Equiv.ofBijective a ⟨hi,Finite.surjective_of_injective hi⟩, ha⟩

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D := by
  have hq := rows D h
  refine ⟨hq,fun y => ?_⟩
  obtain ⟨a,ha⟩ := common D h y
  have hi : Function.Injective (fun x => D.op x y) := by
    intro x z he
    let t := a.symm (D.op x y)
    have hx : H D t x=y := (hq x).1 ((ha t x).trans (a.apply_symm_apply _))
    have hz : H D t z=y := (hq z).1 ((ha t z).trans ((a.apply_symm_apply _).trans he))
    exact ((hq (core D t)).1.comp (hq t).1) (hx.trans hz.symm)
  exact ⟨hi,Finite.surjective_of_injective hi⟩

theorem reduction [Finite A] (h : Identity D) (o : A) :
    ∃ a b : A ≃ A,
      (∀ x y, F D x y=a x) ∧
      (∀ x y, D.op (U D x) y=b (D.op x y)) ∧
      (∀ x y, D.op (a x) y=a (D.op (b x) y)) := by
  classical
  have hq := quasigroup D h
  obtain ⟨a,ha⟩ := common D h o
  have frame (x y v) : D.op (D.op (U D y) v) (H D x (a (D.op y v)))=x := by
    simpa only [ha] using (h x y v o).symm
  have shift (y v w) : D.op (a (D.op y v)) w=a (D.op (D.op (U D y) v) w) := by
    have hs : Function.Surjective (fun x => H D x (a (D.op y v))) := by
      apply Finite.surjective_of_injective
      intro x z he
      apply a.injective
      exact (ha x _).symm.trans ((congrArg (D.op (a (D.op y v))) he).trans (ha z _))
    obtain ⟨x,rfl⟩ := hs w
    rw [frame]
    exact ha x _
  let r := Equiv.ofBijective (fun x => D.op x o) (hq.2 o)
  let b := a.trans (r.trans (a.symm.trans r.symm))
  have hb (x y) : D.op (U D x) y=b (D.op x y) := by
    apply r.injective
    apply a.injective
    change a (D.op (D.op (U D x) y) o)=
      a (r (r.symm (a.symm (r (a (D.op x y))))))
    rw [r.apply_symm_apply,a.apply_symm_apply]
    exact (shift x y o).symm
  refine ⟨a,b,ha,hb,?_⟩
  intro x y
  obtain ⟨v,rfl⟩ := (hq.1 o).2 x
  rw [← hb]
  exact shift o v y

theorem of_reduction (a b : A → A)
    (ha : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (hi : Function.Injective a) : Identity D := by
  intro x y v z
  apply hi
  rw [ha,hb,← hc]
  exact (ha x (a (D.op y v))).symm

theorem unit_bijective [Finite A] (h : Identity D) : Function.Bijective (U D) := by
  have hi : Function.Injective (U D) := by
    intro x y he
    obtain ⟨a,b,_,hb,_⟩ := reduction D h x
    apply ((quasigroup D h).2 x).1
    apply b.injective
    rw [← hb,← hb,he]
  exact ⟨hi,Finite.surjective_of_injective hi⟩

/-- The common output conjugates every U-cycle to the same permutation.
Consequently one fixed point propagates to all points. -/
theorem unit_iterate_fixed [Finite A] (h : Identity D) (n : ℕ) (o : A)
    (ho : (U D)^[n] o=o) : ∀ x, (U D)^[n] x=x := by
  obtain ⟨a,b,_,hb,_⟩ := reduction D h o
  have hq := quasigroup D h
  have step (k : ℕ) (x y : A) :
      D.op ((U D)^[k] x) y=(b : A → A)^[k] (D.op x y) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply',hb,ih]
  have bid (x : A) : (b : A → A)^[n] x=x := by
    obtain ⟨y,rfl⟩ := (hq.1 o).2 x
    rw [← step,ho]
  intro x
  apply (hq.2 o).1
  change D.op ((U D)^[n] x) o=D.op x o
  rw [step,bid]

/-- Once U is the identity, the remaining crossed permutation is trivial.
The proof moves its shift through the two inputs, then compares two
expressions for q(q(x)). No finiteness or assumption about its order is used. -/
private theorem crossed_of_unit (a : A ≃ A) (hq : IsQuasigroup D)
    (hu : ∀ x, U D x=x) (hf : ∀ x y, F D x y=a x)
    (hl : ∀ x y, D.op (a x) y=a (D.op x y)) : ∀ x, a x=x := by
  have hli (x y) : D.op (a.symm x) y=a.symm (D.op x y) := by
    apply a.injective
    rw [← hl,a.apply_symm_apply,a.apply_symm_apply]
  have qa (x) : core D (a x)=core D x := by
    apply (hq.1 (a x)).1
    calc
      D.op (a x) (core D (a x)) = a x := hu (a x)
      _ = a (D.op x (core D x)) := (congrArg a (hu x)).symm
      _ = D.op (a x) (core D x) := (hl x _).symm
  have qai (x) : core D (a.symm x)=core D x := by
    simpa only [a.apply_symm_apply] using (qa (a.symm x)).symm
  have right (x y) : D.op x (a y)=a.symm (D.op x y) := by
    apply (hq.1 (core D x)).1
    apply (hq.1 y).1
    have he := hf x (a y)
    change D.op (a y) (H D x (a y))=a x at he
    rw [hl] at he
    have he' := a.injective he
    have hh := hf (a.symm x) y
    simp only [a.apply_symm_apply] at hh
    simpa only [F,H,qai,hli] using he'.trans hh.symm
  have righti (x y) : D.op x (a.symm y)=a (D.op x y) := by
    have he := right x (a.symm y)
    simpa only [a.apply_symm_apply] using (congrArg a he).symm
  have qq (x) : core D (core D x)=a.symm (a.symm (D.op x x)) := by
    let p := D.op x (D.op x x)
    let z := D.op (core D x) p
    have first : D.op (core D (core D x)) z=a.symm x := by
      apply (hq.1 p).1
      have he := hf (core D x) p
      change D.op p (D.op (core D (core D x)) z)=a (D.op p x) at he
      rw [righti]
      exact he
    apply (hq.2 z).1
    change D.op (core D (core D x)) z=D.op (a.symm (a.symm (D.op x x))) z
    rw [first,hli,hli]
    have he := hf x (D.op x x)
    change D.op (D.op x x) z=a x at he
    rw [he,a.symm_apply_apply]
  have inner (x) : D.op (core D x) (D.op x x)=a.symm (a.symm (core D x)) := by
    have he := hu (core D x)
    change D.op (core D x) (core D (core D x))=core D x at he
    rw [qq,righti,righti] at he
    simpa only [a.symm_apply_apply] using congrArg (fun t => a.symm (a.symm t)) he
  intro x
  have he := hf x x
  change D.op x (D.op (core D x) (D.op x x))=a x at he
  rw [inner,righti,righti] at he
  have hx : D.op x (core D x)=x := hu x
  rw [hx] at he
  exact a.injective he

/-- A fixed point of U suffices for the full image basis. Existence of such
 a point in every finite candidate remains the open step. -/
theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : U D o=o) : Basis D := by
  have hu : ∀ x, U D x=x := by
    simpa only [Function.iterate_one] using unit_iterate_fixed D h 1 o ho
  obtain ⟨a,b,ha,hb,hc⟩ := reduction D h o
  have hq := quasigroup D h
  have bid (x) : b x=x := by
    obtain ⟨y,rfl⟩ := (hq.1 o).2 x
    exact (hb o y).symm.trans (by rw [hu])
  have hl (x y) : D.op (a x) y=a (D.op x y) := by rw [hc,bid]
  have aid := crossed_of_unit D a hq hu ha hl
  exact ⟨fun x => (hu x).symm,fun x y => ((ha x y).trans (aid x)).symm⟩

/-- A fixed point of either auxiliary permutation also finishes the converse. -/
theorem basis_of_output_fixed [Finite A] (h : Identity D) (b : A → A)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y)) (o : A) (ho : b o=o) :
    Basis D := by
  have hq := quasigroup D h
  obtain ⟨x,hx⟩ := (hq.2 o).2 o
  change D.op x o=o at hx
  apply basis_of_fixed_point D h x
  apply (hq.2 o).1
  change D.op (U D x) o=D.op x o
  rw [hb,hx,ho]

theorem basis_of_crossed_fixed [Finite A] (h : Identity D) (a b : A → A)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (hai : Function.Injective a) (o : A) (ho : a o=o) : Basis D := by
  have hq := quasigroup D h
  obtain ⟨y,hy⟩ := (hq.1 o).2 o
  have hbo : b o=o := by
    apply (hq.2 y).1
    apply hai
    have he := hc o y
    simpa only [ho,hy] using he.symm
  exact basis_of_output_fixed D h b hb o hbo

/-- U is an even permutation: its column-conjugate b is a commutator.
For example, this excludes a single even-length cycle at every even order. -/
theorem unit_even [Fintype A] [DecidableEq A] (h : Identity D) :
    Equiv.Perm.sign (Equiv.ofBijective (U D) (unit_bijective D h))=1 := by
  classical
  cases isEmpty_or_nonempty A with
  | inl he =>
    letI := he
    have hh : Equiv.ofBijective (U D) (unit_bijective D h)=Equiv.refl A := by
      ext x; exact isEmptyElim x
    rw [hh]
    exact map_one _
  | inr hn =>
    letI := hn
    let o : A := Classical.choice hn
    obtain ⟨a,b,_,hb,hc⟩ := reduction D h o
    let r : Equiv.Perm A := Equiv.ofBijective (fun x => D.op x o) ((quasigroup D h).2 o)
    let u : Equiv.Perm A := Equiv.ofBijective (U D) (unit_bijective D h)
    have eq1 : r * a = a * r * b := by
      ext x
      exact hc x o
    have eq2 : r * u = b * r := by
      ext x
      exact hb x o
    have sig1 := congrArg (Equiv.Perm.sign (α := A)) eq1
    have sig2 := congrArg (Equiv.Perm.sign (α := A)) eq2
    simp only [map_mul] at sig1 sig2
    have bs : Equiv.Perm.sign b=1 := by
      apply mul_left_cancel (a := Equiv.Perm.sign a * Equiv.Perm.sign r)
      rw [mul_one,← sig1,mul_comm]
    change Equiv.Perm.sign u=1
    apply mul_left_cancel (a := Equiv.Perm.sign r)
    rw [mul_one,sig2,bs,one_mul]

def candidateLaw : NatMagmaLaw :=
  let q (t : FreeMagma Nat) := (t ⋆ (t ⋆ t)) ⋆ t
  let u (t : FreeMagma Nat) := t ⋆ q t
  let hh (x y : FreeMagma Nat) := q x ⋆ (x ⋆ y)
  let f (x y : FreeMagma Nat) := y ⋆ hh x y
  let x := Lf 0
  let y := Lf 1
  let v := Lf 2
  let z := Lf 3
  ⟨x,(u y ⋆ v) ⋆ hh x (f (y ⋆ v) z)⟩

theorem candidateLaw_iff : @satisfies _ A D candidateLaw ↔ Identity D := by
  constructor
  · intro h x y v z
    exact h (fun n => if n=0 then x else if n=1 then y else if n=2 then v else z)
  · intro h v
    exact h (v 0) (v 1) (v 2) (v 3)

theorem candidate_operations : candidateLaw.lhs.forks+candidateLaw.rhs.forks=22 := by decide

end Parastrophes.Eq917Image.FrontProduct
