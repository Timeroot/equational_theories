import equational_theories.Parastrophes.Equation917FrontProduct

/-!
# A fourth-order obstruction for the E917 comparison

This concerns the 22-operation comparison in `Equation917FrontProduct`.
If its normalized permutations satisfy b=a² and a⁴=id, the comparison has
its full converse. These are extra hypotheses: this file does not say that
every candidate has them, or that every four-point fibre has this form.
No catalogue characterization attribute is registered.

The algebraic core needs no finiteness. Suppose F(x,y)=a(x), U(x)=a²(x),
and shifting the first input by a shifts the output by a⁻¹. Put b=a².
First q(bx)=q(x). Two crossed evaluations, compared in a common column,
give q(ax)=b(qx). These identities make b, then a, commute with every row.
Now two evaluations with the common last factor q(x)*(x*(x*x)) show
q(q(x))=x*x. The crossed identity at (x,x) becomes a(x)=a⁴(x)=x.

A bounded Prover9 run suggested the result. The proof here is a handwritten
sequence of cancellations; no solver certificate or finite table is needed.
-/
namespace Parastrophes.Eq917Image.FrontProduct
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)

/-- The crossed permutation is trivial under the stated fourth-order shifts. -/
theorem crossed_four (a : A ≃ A) (hq : IsQuasigroup D)
    (h4 : ∀ x, a (a (a (a x)))=x)
    (hu : ∀ x, U D x=a (a x))
    (hf : ∀ x y, F D x y=a x)
    (hl : ∀ x y, D.op (a x) y=a.symm (D.op x y)) : ∀ x, a x=x := by
  let m := D.op
  let b := fun x => a (a x)
  have b2 (x) : b (b x)=x := h4 x
  have ba (x) : b (a x)=a.symm x := by
    apply a.injective
    exact (h4 x).trans (a.apply_symm_apply x).symm
  have bai (x) : b (a.symm x)=a x := by
    dsimp only [b]
    rw [a.apply_symm_apply]
  have aii (x) : a.symm (a.symm x)=b x := by
    apply a.injective
    apply a.injective
    simp only [a.apply_symm_apply]
    exact (h4 x).symm
  have bi : Function.Injective b := a.injective.comp a.injective
  have hlm (x y) : m (a x) y=a.symm (m x y) := hl x y
  have hb (x y) : m (b x) y=b (m x y) := by
    dsimp only [b]
    rw [hlm,hlm,aii]
  have ux (x) : m x (core D x)=b x := hu x
  have fc (x y) : m y (m (core D x) (m x y))=a x := hf x y
  have b_unit (x) : m (b x) (core D x)=x := by rw [hb,ux,b2]
  have qb (x) : core D (b x)=core D x := by
    apply (hq.1 (b x)).1
    exact ((ux (b x)).trans (b2 x)).trans (b_unit x).symm
  have shifted_unit (x) : m x (core D (a x))=x := by
    have he := ux (a x)
    rw [hlm,ba] at he
    exact a.symm.injective he
  -- Cross twice, then compare with an arbitrary preimage of x in its own row.
  have qa (x) : core D (a x)=b (core D x) := by
    obtain ⟨r,hr⟩ := (hq.1 x).2 x
    change m x r=x at hr
    have he := fc (b x) (core D x)
    rw [qb,b_unit] at he
    have hh : m (b (core D x)) (m (core D x) x)=a x := by
      rw [hb,he]
      change a (a (a (a (a x))))=a x
      rw [h4]
    have he' := fc x r
    rw [hr] at he'
    have hr' : r=b (core D x) := (hq.2 (m (core D x) x)).1 (he'.trans hh.symm)
    apply (hq.1 x).1
    change m x (core D (a x))=m x (b (core D x))
    rw [shifted_unit,← hr',hr]
  -- The square of a commutes with every row; then so does a itself.
  have rb (x y) : m x (b y)=b (m x y) := by
    apply (hq.1 (core D x)).1
    apply (hq.1 y).1
    apply bi
    have he := fc x (b y)
    rw [hb] at he
    have hh := congrArg b (fc (b x) y)
    rw [qb,hb] at hh
    have bb (x) : b (a (b x))=a x := by
      change a (a (a (a (a x))))=a x
      rw [h4]
    rw [bb] at hh
    exact he.trans hh.symm
  have ra (x y) : m x (a y)=a (m x y) := by
    apply (hq.1 (core D x)).1
    apply (hq.1 y).1
    have he := congrArg a (fc x (a y))
    rw [hlm,a.apply_symm_apply] at he
    have hh := fc (a x) y
    rw [qa,hb,hlm,← rb,bai] at hh
    exact he.trans hh.symm
  -- The two crossed evaluations have the same last factor, hence q²(x)=x*x.
  have qq (x) : core D (core D x)=m x x := by
    let p := m x (m x x)
    let z := m (core D x) p
    have first : m (core D (core D x)) z=a x := by
      apply (hq.1 p).1
      have he := fc (core D x) p
      change m p (m (core D (core D x)) z)=a (m p x) at he
      exact he.trans (ra p x).symm
    apply (hq.2 z).1
    exact first.trans (fc x (m x x)).symm
  intro x
  have inner : m (core D x) (m x x)=b (core D x) := by
    have he := ux (core D x)
    rwa [qq] at he
  have he := fc x x
  rw [inner,rb,ux,b2] at he
  exact he.symm

/-- The 22-operation candidate has its full converse if its normalized maps
satisfy b=a² and a⁴=id. This is a restriction on the maps, not on carrier size. -/
theorem basis_of_fourth_square [Finite A] (h : Identity D) (a b : A ≃ A)
    (hf : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (h4 : ∀ x, a (a (a (a x)))=x)
    (hs : ∀ x, b x=a (a x)) : Basis D := by
  have hq := quasigroup D h
  have hl (x y) : D.op (a x) y=a.symm (D.op x y) := by
    apply a.injective
    rw [a.apply_symm_apply]
    have he := hc (a.symm x) y
    rw [a.apply_symm_apply,hs,a.apply_symm_apply] at he
    exact he.symm
  have aii (x) : a.symm (a.symm x)=a (a x) := by
    apply a.injective
    apply a.injective
    simp only [a.apply_symm_apply]
    exact (h4 x).symm
  have hu (x) : U D x=a (a x) := by
    apply (hq.2 x).1
    change D.op (U D x) x=D.op (a (a x)) x
    rw [hb,hs,hl,hl,aii]
  have ha := crossed_four D a hq h4 hu hf hl
  exact ⟨fun x => (hu x |>.trans (by rw [ha,ha])).symm,
    fun x y => ((hf x y).trans (ha x)).symm⟩

end Parastrophes.Eq917Image.FrontProduct
