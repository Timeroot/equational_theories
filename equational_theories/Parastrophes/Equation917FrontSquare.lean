import equational_theories.Parastrophes.Equation917FrontProduct
import equational_theories.Parastrophes.Equation917SplitCandidate

/-!
# A double-crossed comparison for the E917 left image

Put q(x)=(x*(x*x))*x, U(x)=x*q(x), H(x,y)=q(x)*(x*y), and
F(x,y)=y*H(x,y). This file studies the 72-operation identity

    x = (U(y)*v) * H(x,F(F(y*v,z),w)).

Its unrestricted converse remains OPEN. No characterization attribute is
registered. Every actual E917 left image satisfies it, and every finite
model of the candidate is a quasigroup. Its exact finite reduction is

    F(x,y)=a(x),  U(x)*y=b(x*y),  a(a(x))*y=a(b(x)*y),

where a and b are permutations. One fixed point of a forces the full image
basis. Both a and U have uniform cycle lengths. Unlike the 22-operation
comparison, this does not prove that a fixed point of U suffices.

The new cancellation step is in `common`: initially only the double composite
F(F(x,z),w) is independent of z,w. One of its values supplies a bijective
H-column, and the corresponding F-column then cancels the double composite.
All the proofs below are ordinary Lean equalities and finite bijectivity
arguments. Neither bounded model searches nor affine calculations are used.
-/

namespace Parastrophes.Eq917Image.FrontSquare
open Law FreeMagma
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)

def Identity : Prop := ∀ x y v z w,
  x=D.op (D.op (U D y) v) (H D x (F D (F D (D.op y v) z) w))

theorem of_basis (h : Basis D) : Identity D := by
  have hu (x) : U D x=x := (h.1 x).symm
  have hf (x y) : F D x y=x := (h.2 x y).symm
  intro x y v z w
  rw [hu,hf,hf]
  exact h.2 x _

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M,hm,hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))

theorem rows_surjective (h : Identity D) : ∀ a, Function.Surjective (D.op a) := by
  have good (y v : A) : Function.Surjective (D.op (D.op (U D y) v)) :=
    fun x => ⟨_, (h x y v y y).symm⟩
  intro o
  have hh : Function.Surjective (D.op (U D (U D o))) := good o (core D (U D o))
  obtain ⟨v,hv⟩ := hh o
  simpa only [hv] using good (U D o) v

theorem rows [Finite A] (h : Identity D) : IsSideQuasigroup .left D :=
  fun a => ⟨Finite.injective_iff_surjective.mpr (rows_surjective D h a), rows_surjective D h a⟩

/-- Cancelling the three outer rows makes the two-fold composite common.
Its value at one argument supplies a bijective H-column, hence one bijective
F-column. That column cancels the composite to make F itself common. -/
theorem common [Finite A] (h : Identity D) (o : A) :
    ∃ a : A ≃ A, ∀ x y, F D x y=a x := by
  classical
  have hq := rows D h
  let g := fun x => F D (F D x o) o
  have hg (x z w) : F D (F D x z) w=g x := by
    obtain ⟨v,rfl⟩ := (hq o).2 x
    have he := (h o o v z w).symm.trans (h o o v o o)
    exact (hq o).1 ((hq (core D o)).1 ((hq (D.op (U D o) v)).1 he))
  let c := g (D.op o o)
  have back (x) : D.op (D.op (U D o) o) (H D x c)=x := by
    have he := (h x o o o o).symm
    simpa only [hg] using he
  have ki : Function.Injective (fun x => H D x c) := by
    intro x y he
    exact (back x).symm.trans ((congrArg (D.op (D.op (U D o) o)) he).trans (back y))
  have kb : Function.Bijective (fun x => H D x c) := ⟨ki,Finite.surjective_of_injective ki⟩
  let f := fun x => F D x c
  have fb : Function.Bijective f := (hq c).comp kb
  have hf (x y) : F D x y=f x := by
    apply fb.1
    exact (hg x y c).trans (hg x c c).symm
  exact ⟨Equiv.ofBijective f fb,hf⟩

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
      (∀ x y, D.op (a (a x)) y=a (D.op (b x) y)) := by
  classical
  have hq := quasigroup D h
  obtain ⟨a,ha⟩ := common D h o
  have frame (x y v) : D.op (D.op (U D y) v) (H D x (a (a (D.op y v))))=x := by
    simpa only [ha] using (h x y v o o).symm
  have shift (y v w) : D.op (a (a (D.op y v))) w=a (D.op (D.op (U D y) v) w) := by
    have hs : Function.Surjective (fun x => H D x (a (a (D.op y v)))) := by
      apply Finite.surjective_of_injective
      intro x z he
      apply a.injective
      exact (ha x _).symm.trans ((congrArg (D.op (a (a (D.op y v)))) he).trans (ha z _))
    obtain ⟨x,rfl⟩ := hs w
    rw [frame]
    exact ha x _
  let r := Equiv.ofBijective (fun x => D.op x o) (hq.2 o)
  let b := a.trans (a.trans (r.trans (a.symm.trans r.symm)))
  have hb (x y) : D.op (U D x) y=b (D.op x y) := by
    apply r.injective
    apply a.injective
    change a (D.op (D.op (U D x) y) o)=
      a (r (r.symm (a.symm (r (a (a (D.op x y)))))))
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
    (hc : ∀ x y, D.op (a (a x)) y=a (D.op (b x) y))
    (hi : Function.Injective a) : Identity D := by
  intro x y v z w
  apply hi
  rw [ha,ha,hb,← hc]
  exact (ha x (a (a (D.op y v)))).symm

theorem unit_bijective [Finite A] (h : Identity D) : Function.Bijective (U D) := by
  have hi : Function.Injective (U D) := by
    intro x y he
    obtain ⟨a,b,_,hb,_⟩ := reduction D h x
    apply ((quasigroup D h).2 x).1
    apply b.injective
    rw [← hb,← hb,he]
  exact ⟨hi,Finite.surjective_of_injective hi⟩

theorem basis_of_crossed_fixed [Finite A] (h : Identity D) (a b : A ≃ A)
    (ha : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a (a x)) y=a (D.op (b x) y))
    (o : A) (ho : a o=o) : Basis D := by
  have hq := quasigroup D h
  let g := fun x => a (a (b.symm x))
  have hg (x y) : D.op (g x) y=a (D.op x y) := by
    simpa only [b.apply_symm_apply] using hc (b.symm x) y
  have aid := (SplitCandidate.output_fixed_point D g a hq hg o ho).2
  have bid (x) : b x=x := by
    apply (hq.2 o).1
    have he := hc x o
    simpa only [aid] using he.symm
  have uid (x) : U D x=x := by
    apply (hq.2 o).1
    change D.op (U D x) o=D.op x o
    rw [hb,bid]
  exact ⟨fun x => (uid x).symm,fun x y => ((ha x y).trans (aid x)).symm⟩


/-- A power of U that fixes one point fixes every point. This statement
uses the first-input/output autotopy, not a bound on the carrier size. -/
theorem unit_iterate_fixed [Finite A] (h : Identity D) (n : ℕ) (o : A)
    (ho : (U D)^[n] o=o) : ∀ x, (U D)^[n] x=x := by
  obtain ⟨a,b,_,hb,_⟩ := reduction D h o
  exact (SplitCandidate.iterate_fixed_point D (U D) b (quasigroup D h)
    hb n o ho).1

/-- The crossed permutation also has uniform cycle lengths. The right-hand
map of an autotopy is just as rigid as its left-hand map. -/
theorem crossed_iterate_fixed (a b : A ≃ A) (hq : IsQuasigroup D)
    (hc : ∀ x y, D.op (a (a x)) y=a (D.op (b x) y))
    (n : ℕ) (o : A) (ho : (a : A → A)^[n] o=o) :
    ∀ x, (a : A → A)^[n] x=x := by
  let g := fun x => a (a (b.symm x))
  have hg (x y) : D.op (g x) y=a (D.op x y) := by
    simpa only [b.apply_symm_apply] using hc (b.symm x) y
  exact (SplitCandidate.output_fixed_point D (g^[n]) ((a : A → A)^[n]) hq
    (SplitCandidate.autotopy_iterate D g a hg n) o ho).2

def candidateLaw : NatMagmaLaw :=
  let q (t : FreeMagma Nat) := (t ⋆ (t ⋆ t)) ⋆ t
  let u (t : FreeMagma Nat) := t ⋆ q t
  let hh (x y : FreeMagma Nat) := q x ⋆ (x ⋆ y)
  let f (x y : FreeMagma Nat) := y ⋆ hh x y
  let x := Lf 0
  let y := Lf 1
  let v := Lf 2
  let z := Lf 3
  let w := Lf 4
  ⟨x,(u y ⋆ v) ⋆ hh x (f (f (y ⋆ v) z) w)⟩

theorem candidateLaw_iff : @satisfies _ A D candidateLaw ↔ Identity D := by
  constructor
  · intro h x y v z w
    exact h (fun n => if n=0 then x else if n=1 then y else if n=2 then v else if n=3 then z else w)
  · intro h v
    exact h (v 0) (v 1) (v 2) (v 3) (v 4)

theorem candidate_operations : candidateLaw.lhs.forks+candidateLaw.rhs.forks=72 := by decide
end Parastrophes.Eq917Image.FrontSquare
