import equational_theories.Parastrophes.Equation917FrontProduct

/-!
# Removing the cycle restrictions from the E917 regular-output converse

Write q(x)=(x*(x*x))*x, U(x)=x*q(x), and F(x,y)=y*(q(x)*(x*y)).
The 22-operation FrontProduct candidate has a finite normalization

    F(x,y)=a(x), U(x)*y=b(x*y), a(x)*y=a(b(x)*y).

This file proves that U=b alone finishes this normalized converse. Neither
commutation of a and b nor a bound on their cycle lengths needs to be assumed.
The main algebraic theorem works on arbitrary quasigroups.

First use left division to compare two crossed identities in a common column.
This transports a conjugate of b through the right argument, forcing ab=ba.
Then q(bx)=q(x), q(ax)=b(qx), and crossing determines how a and b move through
both arguments. Comparing two products with the same right factor gives

    q(q(x)) = a⁻² b³ (x*x).

The unit identity at q(x), followed by crossing at (x,x), now gives ab=id.
The first-argument shift then makes a=id, hence b=id. This replaces a finite
orbit-quotient argument by direct algebra, without solver certificates.

For finite models of the candidate, the full image basis is consequently
equivalent to either of the following extra conditions:

* U commutes with every right translation;
* q(U(x))=q(x) for every x.

Neither extra condition has been proved for every candidate. Thus this is
still a conditional converse, with no single-equation characterization tag.
-/
namespace Parastrophes.Eq917Image.FrontProduct
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)

/-- Unit regularity forces the two crossed shifts to commute. -/
theorem commute_of_unit_output (a b : A ≃ A) (hq : IsQuasigroup D)
    (ha : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (b x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (hu : ∀ x, U D x=b x) : Function.Commute a b := by
  classical
  let e (x) := Equiv.ofBijective (D.op x) (hq.1 x)
  let l (x y) := (e x).symm y
  have ml (x y) : D.op x (l x y)=y := (e x).apply_symm_apply y
  have lm (x y) : l x (D.op x y)=y := (e x).symm_apply_apply y
  have qb (x) : core D (b x)=core D x := by
    apply (hq.1 x).1
    apply b.injective
    rw [← hb]
    change U D (b x)=b (U D x)
    rw [hu,hu]
  have inva (x y) : D.op (b (a.symm x)) y=a.symm (D.op x y) := by
    apply a.injective
    rw [a.apply_symm_apply,← hc,a.apply_symm_apply]
  have lb (x y) : l (b x) y=l x (b.symm y) := by
    apply (hq.1 x).1
    apply b.injective
    rw [← hb,ml,ml,b.apply_symm_apply]
  have cross_l (x y) : D.op (l x y) (D.op (core D x) y)=a x := by
    have he := ha x (l x y)
    simpa only [F,H,ml] using he
  let d := fun x => a (b (a.symm x))
  have ld (x y) : l x (b.symm y)=d (l x y) := by
    apply (hq.2 (D.op (core D x) y)).1
    change D.op (l x (b.symm y)) (D.op (core D x) y)=
      D.op (a (b (a.symm (l x y)))) (D.op (core D x) y)
    have he := cross_l (b x) y
    rw [lb,qb] at he
    rw [he,hc,hb,inva,cross_l,a.symm_apply_apply]
  have right (x y) : D.op x (d y)=b.symm (D.op x y) := by
    have he := ld x (D.op x y)
    rw [lm] at he
    rw [← he,ml]
  intro x
  obtain ⟨y,hy⟩ := (hq.1 x).2 x
  have he : D.op (a x) (d y)=D.op (a x) (d y) := rfl
  conv_lhs at he => rw [hc,hb,right,b.apply_symm_apply]
  conv_rhs at he => rw [right,hc,hb]
  have hh := congrArg b he
  rw [b.apply_symm_apply,hy] at hh
  exact hh.symm

/-- Purely algebraic converse: no finiteness or cycle hypotheses. -/
theorem basis_of_regular_unit (a b : A ≃ A) (hq : IsQuasigroup D)
    (ha : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (b x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (hu : ∀ x, U D x=b x) : Basis D := by
  have ab := commute_of_unit_output D a b hq ha hb hc hu
  have ba (x) : b (a x)=a (b x) := (ab x).symm
  have bai (x) : b (a.symm x)=a.symm (b x) := by
    apply a.injective
    rw [ab,a.apply_symm_apply,a.apply_symm_apply]
  have biai (x) : b.symm (a.symm x)=a.symm (b.symm x) := by
    apply b.injective
    rw [b.apply_symm_apply,bai,b.apply_symm_apply]
  have qb (x) : core D (b x)=core D x := by
    apply (hq.1 x).1
    apply b.injective
    rw [← hb]
    change U D (b x)=b (U D x)
    rw [hu,hu]
  have qbi (x) : core D (b.symm x)=core D x := by
    simpa only [b.apply_symm_apply] using (qb (b.symm x)).symm
  have leftbi (x y) : D.op (b.symm x) y=b.symm (D.op x y) := by
    apply b.injective
    rw [← hb,b.apply_symm_apply,b.apply_symm_apply]
  have lefta (x y) : D.op (a x) y=a (b (D.op x y)) := by rw [hc,hb]
  have leftai (x y) : D.op (a.symm x) y=b.symm (a.symm (D.op x y)) := by
    apply b.injective
    apply a.injective
    rw [← lefta,a.apply_symm_apply,b.apply_symm_apply,a.apply_symm_apply]
  have rightb (x y) : D.op x (b y)=b.symm (D.op x y) := by
    apply (hq.1 (core D x)).1
    apply (hq.1 y).1
    apply b.injective
    have he := ha x (b y)
    change D.op (b y) (D.op (core D x) (D.op x (b y)))=a x at he
    rw [hb] at he
    have hh := congrArg b (ha (b.symm x) y)
    change b (D.op y (D.op (core D (b.symm x)) (D.op (b.symm x) y)))=
      b (a (b.symm x)) at hh
    rw [qbi,leftbi,← ab,b.apply_symm_apply] at hh
    exact he.trans hh.symm
  have rightbi (x y) : D.op x (b.symm y)=b (D.op x y) := by
    have he := rightb x (b.symm y)
    simpa only [b.apply_symm_apply] using (congrArg b he).symm
  have local_unit (x) : D.op x (core D (a x))=x := by
    have he := hu (a x)
    change D.op (a x) (core D (a x))=b (a x) at he
    rw [lefta,ba] at he
    exact b.injective (a.injective he)
  have qa (x) : core D (a x)=b (core D x) := by
    apply (hq.2 (D.op (core D x) x)).1
    have he := ha x (core D x)
    change D.op (core D x) (D.op (core D x) (U D x))=a x at he
    rw [hu,rightb,rightbi] at he
    have hh := ha x (core D (a x))
    change D.op (core D (a x)) (D.op (core D x) (D.op x (core D (a x))))=a x at hh
    rw [local_unit] at hh
    change D.op (core D (a x)) (D.op (core D x) x)=D.op (b (core D x)) (D.op (core D x) x)
    rw [hb]
    exact hh.trans he.symm
  have qai (x) : core D (a.symm x)=b.symm (core D x) := by
    apply b.injective
    rw [← qa,a.apply_symm_apply,b.apply_symm_apply]
  have righta (x y) : D.op x (a y)=b.symm (a.symm (D.op x y)) := by
    apply (hq.1 (core D x)).1
    apply (hq.1 y).1
    apply b.injective
    have he := ha x (a y)
    change D.op (a y) (D.op (core D x) (D.op x (a y)))=a x at he
    rw [lefta] at he
    have hh := ha (a.symm x) y
    change D.op y (D.op (core D (a.symm x)) (D.op (a.symm x) y))=a (a.symm x) at hh
    rw [qai,leftai,leftbi,rightbi,a.apply_symm_apply] at hh
    exact (a.injective he).trans hh.symm
  have rightai (x y) : D.op x (a.symm y)=a (b (D.op x y)) := by
    have he := righta x (a.symm y)
    simpa only [a.apply_symm_apply,b.apply_symm_apply] using (congrArg (fun t => a (b t)) he).symm
  have qq (x) : core D (core D x)=a.symm (a.symm (b (b (b (D.op x x))))) := by
    let p := D.op x (D.op x x)
    let z := D.op (core D x) p
    have first : D.op (core D (core D x)) z=a.symm (b x) := by
      apply (hq.1 p).1
      have he := ha (core D x) p
      change D.op p (D.op (core D (core D x)) z)=a (D.op p x) at he
      rw [rightai,rightb,b.apply_symm_apply]
      exact he
    apply (hq.2 z).1
    change D.op (core D (core D x)) z=D.op (a.symm (a.symm (b (b (b (D.op x x)))))) z
    rw [first,leftai,leftai,hb,hb,hb]
    have he := ha x (D.op x x)
    change D.op (D.op x x) z=a x at he
    simp only [he,ba,a.symm_apply_apply,biai,b.symm_apply_apply]
  have inner (x) : D.op (core D x) (D.op x x)=a.symm (a.symm (b (b (core D x)))) := by
    have he := hu (core D x)
    change D.op (core D x) (core D (core D x))=b (core D x) at he
    simp only [qq,rightai,rightb,ba,b.apply_symm_apply] at he
    have hh := congrArg (fun t => b (a.symm (a.symm t))) he
    simpa only [a.symm_apply_apply,b.apply_symm_apply,bai] using hh
  have abid (x) : a (b x)=x := by
    have he := ha x x
    change D.op x (D.op (core D x) (D.op x x))=a x at he
    simp only [inner,rightai,rightb,ba,b.apply_symm_apply] at he
    have hx : D.op x (core D x)=b x := hu x
    rw [hx] at he
    exact a.injective he
  have aid (x) : a x=x := by
    apply (hq.2 x).1
    change D.op (a x) x=D.op x x
    rw [lefta,abid]
  have bid (x) : b x=x := by simpa only [aid] using abid x
  exact ⟨fun x => ((hu x).trans (bid x)).symm,
    fun x y => ((ha x y).trans (aid x)).symm⟩

/-- In the finite normalization of the 22-operation candidate, U=b suffices. -/
theorem basis_of_unit_output [Finite A] (h : Identity D)
    (a b : A ≃ A)
    (ha : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (hu : ∀ x, U D x=b x) : Basis D := by
  apply basis_of_regular_unit D a b (quasigroup D h) ha _ hc hu
  intro x y
  rw [← hu,hb]

/-- Within the candidate, commutation of U with every right translation is
exactly the missing condition. There is no assumption about cycle lengths. -/
theorem basis_iff_unit_commutes_columns [Finite A] (h : Identity D) :
    Basis D ↔ ∀ x y, U D (D.op x y)=D.op (U D x) y := by
  constructor
  · intro hb x y
    have hu (x) : U D x=x := (hb.1 x).symm
    rw [hu,hu]
  · intro comm
    cases isEmpty_or_nonempty A with
    | inl he =>
      letI := he
      exact ⟨fun x => isEmptyElim x,fun x => isEmptyElim x⟩
    | inr hn =>
      letI := hn
      let o : A := Classical.choice hn
      obtain ⟨a,b,ha,hb,hc⟩ := reduction D h o
      have hu (x) : U D x=b x := by
        obtain ⟨y,rfl⟩ := ((quasigroup D h).1 o).2 x
        rw [comm,hb]
      exact basis_of_unit_output D h a b ha hb hc hu

/-- An equivalent unary condition: the core is constant on each U-cycle.
Counterexamples must therefore have q(U(x)) ≠ q(x) somewhere. -/
theorem basis_iff_core_unit [Finite A] (h : Identity D) :
    Basis D ↔ ∀ x, core D (U D x)=core D x := by
  constructor
  · intro hb x
    have hu : U D x=x := (hb.1 x).symm
    rw [hu]
  · intro hqU
    cases isEmpty_or_nonempty A with
    | inl he =>
      letI := he
      exact ⟨fun x => isEmptyElim x,fun x => isEmptyElim x⟩
    | inr hn =>
      letI := hn
      let o : A := Classical.choice hn
      obtain ⟨a,b,ha,hb,hc⟩ := reduction D h o
      have hu (x) : U D x=b x := by
        obtain ⟨y,rfl⟩ := (unit_bijective D h).2 x
        change D.op (U D y) (core D (U D y))=b (U D y)
        rw [hqU,hb]
        rfl
      exact basis_of_unit_output D h a b ha hb hc hu


end Parastrophes.Eq917Image.FrontProduct
