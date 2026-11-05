import equational_theories.Parastrophes.Equation917FrontProduct
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Small fibres cannot obstruct the E917 comparison converse

This concerns the 22-operation candidate in `Equation917FrontProduct`.
If a finite model of that candidate has a homomorphism to a genuine E917
left-division image, and each fibre has at most three elements, the model
is itself a genuine image. The homomorphism need not be onto. There is no
affine, commutativity, or coordinate assumption on its fibres.

The candidate supplies two permutations a,b. Both preserve the fibres:
F projects to the identity in the target, as does U. In a counterexample,
a,b have no fixed points, and b(x) differs from a(x). Thus x,a(x),b(x)
exhaust their fibre. Injectivity forces b=a² and a³=id. The normalized
comparison then gives U=a and (a(x))*y=a⁻¹(x*y).

The algebraic lemma `crossed_three` excludes that last possibility, even
without finiteness. Two inverse-translation calculations give
q(a(q(x)))=x*x and q(a⁻¹(x))=a(q(x)). They imply both
x*a(x)=q(q(x)) and x*a⁻¹(x)=q(q(x)). Row cancellation makes a²=id,
which together with a³=id makes a=id.

This proves preservation of the converse under arbitrary finite extensions
with fibres of size at most three, and hence under towers of these extensions.
It does not prove the unrestricted converse and registers no single-equation
characterization attribute. The proofs use no finite tables or ATP certificates.
-/
namespace Parastrophes.Eq917Image.FrontProduct
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)

/-- The algebraic obstruction to a nontrivial three-point fibre. -/
theorem crossed_three (a : A ≃ A) (hq : IsQuasigroup D)
    (h3 : ∀ x, a (a (a x))=x)
    (hu : ∀ x, U D x=a x)
    (hf : ∀ x y, F D x y=a x)
    (hl : ∀ x y, D.op (a x) y=a.symm (D.op x y)) : ∀ x, a x=x := by
  let m := D.op
  let le (x : A) := Equiv.ofBijective (m x) (hq.1 x)
  let re (y : A) := Equiv.ofBijective (fun x => m x y) (hq.2 y)
  let l (x y : A) := (le x).symm y
  let r (x y : A) := (re y).symm x
  have ml (x y) : m x (l x y)=y := (le x).apply_symm_apply y
  have lm (x y) : l x (m x y)=y := (le x).symm_apply_apply y
  have mr (x y) : m (r x y) y=x := (re y).apply_symm_apply x
  have rm (x y) : r (m x y) y=x := (re y).symm_apply_apply x
  have aa (x) : a (a x)=a.symm x := by
    apply a.injective
    rw [h3,a.apply_symm_apply]
  have hlm (x y) : m (a x) y=a.symm (m x y) := hl x y
  have ai2 (x) : a.symm (a.symm x)=a x := by
    rw [← aa (a.symm x),a.apply_symm_apply]
  have hli (x y) : m (a.symm x) y=a (m x y) := by
    rw [← aa,hlm,hlm,ai2]
  have ux (x) : m x (core D x)=a x := hu x
  have fc (x y) : m y (m (core D x) (m x y))=a x := hf x y
  have shifted_unit (x) : m x (core D (a x))=x := by
    have he := ux (a x)
    rw [hlm,aa] at he
    exact a.symm.injective he
  have diag (x) : l x x=core D (a x) := by
    exact (congrArg (l x) (shifted_unit x)).symm.trans (lm x _)
  have cross_inverse (x y) : l (core D x) (l y (a x))=m x y := by
    have he := congrArg (l (core D x) ∘ l y) (fc x y)
    simpa only [Function.comp_apply,lm] using he.symm
  have double_inverse (x y) : l x (l (core D x) y)=r (a x) y := by
    apply (hq.2 y).1
    change m (l x (l (core D x) y)) y=m (r (a x) y) y
    rw [mr]
    have he := fc x (l x (l (core D x) y))
    rw [ml,ml] at he
    exact he
  have inverse_rotate (x y) : r (l (core D x) y) (r (a x) y)=x := by
    rw [← double_inverse]
    have he := rm x (l x (l (core D x) y))
    rwa [ml] at he
  -- First compare a crossed identity with the shifted unit identity.
  have core_twice (x) : core D (a (core D x))=m x x := by
    let z := core D (a (core D x))
    have he := fc x (l x z)
    rw [ml,shifted_unit] at he
    have he' : l x z=x := (hq.2 (core D x)).1 (he.trans (ux x).symm)
    have hh := ml x z
    rw [he'] at hh
    exact hh.symm
  have cross_division (x y) : r (l y (a x)) (m x y)=core D x := by
    have he := congrArg (l y) (fc x y)
    rw [lm] at he
    rw [← he,rm]
  -- Two ways to undo the same pair of translations transport q through a.
  have core_shift (x) : core D (a.symm x)=a (core D x) := by
    have he := cross_division (a.symm x) (m x x)
    rw [a.apply_symm_apply] at he
    have mid : m (a.symm x) (m x x)=r (a.symm (core D x)) x := by
      apply (hq.2 x).1
      change m (m (a.symm x) (m x x)) x=m (r (a.symm (core D x)) x) x
      rw [mr,hli,hlm]
      rfl
    rw [mid] at he
    have hh := inverse_rotate (a (core D x)) x
    rw [core_twice,aa] at hh
    exact he.symm.trans hh
  -- The opposite shifts of x now have the same product with x.
  have mixed (x) : m x (a x)=core D (core D x) := by
    have he := cross_inverse x (a x)
    rw [diag,aa,core_shift] at he
    have hh := ux (core D x)
    rw [← hh,lm] at he
    exact he.symm
  have mixed' (x) : m x (a.symm x)=core D (core D x) := by
    have he := core_twice (a.symm x)
    rw [core_shift,aa,core_shift,hli] at he
    exact a.injective he.symm
  intro x
  have he : a x=a.symm x := (hq.1 x).1 ((mixed x).trans (mixed' x).symm)
  have he' : a (a x)=x := by rw [he,a.apply_symm_apply]
  have hh := h3 x
  rw [he'] at hh
  exact hh


/-- If the 22-operation candidate maps homomorphically to a genuine image,
with at most three elements in each fibre, it is itself a genuine image.
No affine description of the fibres is assumed. -/
theorem basis_of_small_fibres [Finite A] {I : Type} (B : Magma I)
    (hB : Basis B) (p : A → I)
    (hp : ∀ x y, p (D.op x y)=B.op (p x) (p y))
    (hs : ∀ i, Nat.card {x // p x=i} ≤ 3)
    (h : Identity D) : Basis D := by
  classical
  by_contra bad
  have hn : Nonempty A := by
    by_contra he
    have hi : IsEmpty A := not_nonempty_iff.mp he
    exact bad ⟨fun x => (hi.false x).elim, fun x => (hi.false x).elim⟩
  let o : A := Classical.choice hn
  obtain ⟨a,b,ha,hb,hc⟩ := reduction D h o
  have hq := quasigroup D h
  have pq (x) : p (core D x)=core B (p x) := by
    unfold core
    rw [hp,hp,hp]
  have pu (x) : p (U D x)=p x := by
    unfold U
    rw [hp,pq]
    exact (hB.1 (p x)).symm
  have pf (x y) : p (F D x y)=p x := by
    unfold F H
    rw [hp,hp,hp,pq]
    exact (hB.2 (p x) (p y)).symm
  have pa (x) : p (a x)=p x := (congrArg p (ha x o)).symm.trans (pf x o)
  have pb (x) : p (b x)=p x := by
    obtain ⟨y,rfl⟩ := (hq.1 o).2 x
    rw [← hb,hp,pu,← hp]
  have an (x) : a x ≠ x := fun he => bad
    (basis_of_crossed_fixed D h a b hb hc a.injective x he)
  have bn (x) : b x ≠ x := fun he => bad (basis_of_output_fixed D h b hb x he)
  have abn (x) : b x ≠ a x := by
    intro he
    have hh := hc x o
    rw [he] at hh
    exact an _ hh.symm
  -- The three known distinct points exhaust a fibre of size at most three.
  have span (x t : A) (ht : p t=p x) : t=x ∨ t=a x ∨ t=b x := by
    let f : Fin 3 → {z // p z=p x} := ![⟨x,rfl⟩,⟨a x,pa x⟩,⟨b x,pb x⟩]
    have fi : Function.Injective f := by
      intro i j hij
      have he := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j
      all_goals first | rfl | exact (an x he).elim | exact (an x he.symm).elim |
        exact (bn x he).elim | exact (bn x he.symm).elim |
        exact (abn x he).elim | exact (abn x he.symm).elim
    have fs : Function.Surjective f :=
      (fi.bijective_of_nat_card_le (by simpa only [Nat.card_fin] using hs (p x))).2
    obtain ⟨i,hi⟩ := fs ⟨t,ht⟩
    have he := congrArg Subtype.val hi
    fin_cases i
    · exact Or.inl he.symm
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr he.symm)
  have bshape (x) : b x=a (a x) := by
    have no_two : a (a x) ≠ x := by
      intro he
      rcases span x (a (b x)) (by rw [pa,pb]) with hh | hh | hh
      · exact abn x (a.injective (hh.trans he.symm))
      · exact bn x (a.injective hh)
      · exact an (b x) hh
    rcases span x (a (a x)) (by rw [pa,pa]) with he | he | he
    · exact (no_two he).elim
    · exact (an x (a.injective he)).elim
    · exact he.symm
  have a3 (x) : a (a (a x))=x := by
    rw [← bshape x]
    rcases span x (a (b x)) (by rw [pa,pb]) with he | he | he
    · exact he
    · exact (bn x (a.injective he)).elim
    · exact (an (b x) he).elim
  have left2 (x y) : D.op (a (a x)) y=a (D.op x y) := by
    have he := hc (a x) y
    rwa [bshape,a3] at he
  have left (x y) : D.op (a x) y=a.symm (D.op x y) := by
    rw [hc,bshape,left2]
    apply a.injective
    rw [a3,a.apply_symm_apply]
  have unit (x) : U D x=a x := by
    apply (hq.2 o).1
    change D.op (U D x) o=D.op (a x) o
    rw [hb,bshape,left]
    apply a.injective
    rw [a3,a.apply_symm_apply]
  exact an o (crossed_three D a hq a3 unit ha left o)

/-- Exactness within this specified class of extensions, among arbitrary
candidate operations on the finite source carrier. -/
theorem small_fibres_characterizes [Finite A] {I : Type} (B : Magma I)
    (hB : Basis B) (p : A → I)
    (hp : ∀ x y, p (D.op x y)=B.op (p x) (p y))
    (hs : ∀ i, Nat.card {x // p x=i} ≤ 3) :
    Identity D ↔ InImage Law917 .left D :=
  ⟨fun h => (characterizes_fin D).mp (basis_of_small_fibres D B hB p hp hs h),
    of_image D⟩

end Parastrophes.Eq917Image.FrontProduct
