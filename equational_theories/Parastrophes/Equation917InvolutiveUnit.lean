import equational_theories.Parastrophes.Equation917FrontProduct

/-!
# A quotient argument for one involution case of the E917 comparison

This concerns the 22-operation FrontProduct candidate. In its normalized
form assume U=b, b²=id, and a commutes with b. Then the full image basis
holds, with no bound on the size of the finite carrier.

First q(bx)=q(x). Comparing crossed identities transports b through the
second argument as well as the first. Therefore its orbits form a magma
congruence. The quotient still satisfies the candidate and now has U=id,
so the existing fixed-point converse applies downstairs. Its crossed law
says a(x) belongs to the two-point orbit {x,b(x)}. Either alternative supplies
a fixed point of a, and the original magma is consequently an image.

The commuting-involutions hypotheses are conditional. In particular this
is not the unrestricted converse or a characterization catalogue entry.
-/

namespace Parastrophes.Eq917Image.FrontProduct
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)

theorem basis_of_involutive_unit_output [Finite A] (h : Identity D)
    (a b : A ≃ A)
    (ha : ∀ x y, F D x y=a x)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (hu : ∀ x, U D x=b x) (b2 : ∀ x, b (b x)=x)
    (ab : Function.Commute a b) : Basis D := by
  classical
  by_contra bad
  have hn : Nonempty A := by
    by_contra he
    have hi : IsEmpty A := not_nonempty_iff.mp he
    exact bad ⟨fun x => (hi.false x).elim, fun x => (hi.false x).elim⟩
  let o : A := Classical.choice hn
  have hq := quasigroup D h
  have left (x y) : D.op (b x) y=b (D.op x y) := by rw [← hu,hb]
  have qb (x) : core D (b x)=core D x := by
    apply (hq.1 x).1
    apply b.injective
    rw [← left]
    change U D (b x)=b (U D x)
    rw [hu,hu]
  have right (x y) : D.op x (b y)=b (D.op x y) := by
    apply (hq.1 (core D x)).1
    apply (hq.1 y).1
    apply b.injective
    have he := ha x (b y)
    change D.op (b y) (D.op (core D x) (D.op x (b y)))=a x at he
    rw [left] at he
    have hh := congrArg b (ha (b x) y)
    change b (D.op y (D.op (core D (b x)) (D.op (b x) y)))=b (a (b x)) at hh
    rw [qb,left,ab,b2] at hh
    exact he.trans hh.symm
  let s : Setoid A := {
    r := fun x y => x=y ∨ x=b y
    iseqv := {
      refl := fun x => Or.inl rfl
      symm := by
        intro x y he
        rcases he with he | he
        · exact Or.inl he.symm
        · exact Or.inr (by rw [he,b2])
      trans := by
        intro x y z he hf
        rcases he with he | he <;> rcases hf with hf | hf
        · exact Or.inl (he.trans hf)
        · exact Or.inr (he.trans hf)
        · exact Or.inr (by rw [he,hf])
        · exact Or.inl (by rw [he,hf,b2]) } }
  let p : A → Quotient s := Quotient.mk s
  have pb (x) : p (b x)=p x := Quotient.sound (Or.inr rfl)
  let Q : Magma (Quotient s) := ⟨Quotient.map₂ D.op (by
    intro x x' hx y y' hy
    change x=x' ∨ x=b x' at hx
    change y=y' ∨ y=b y' at hy
    change D.op x y=D.op x' y' ∨ D.op x y=b (D.op x' y')
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (right _ _)
    · exact Or.inr (left _ _)
    · exact Or.inl (by rw [left,right,b2]))⟩
  have hQ : Identity Q := by
    intro x y v z
    refine Quotient.inductionOn x ?_
    intro x
    refine Quotient.inductionOn y ?_
    intro y
    refine Quotient.inductionOn v ?_
    intro v
    refine Quotient.inductionOn z ?_
    intro z
    exact congrArg p (h x y v z)
  have hU : U Q (p o)=p o := by
    change p (U D o)=p o
    rw [hu,pb]
  have basisQ := basis_of_fixed_point Q hQ (p o) hU
  have pax : p (a o)=p o := by
    have he := basisQ.2 (p o) (p o)
    change p o=p (F D o o) at he
    rw [ha] at he
    exact he.symm
  have cases := Quotient.exact pax
  change a o=o ∨ a o=b o at cases
  rcases cases with he | he
  · exact bad (basis_of_crossed_fixed D h a b hb hc a.injective o he)
  · have hf := hc o o
    rw [he] at hf
    exact bad (basis_of_crossed_fixed D h a b hb hc a.injective _ hf.symm)
end Parastrophes.Eq917Image.FrontProduct
