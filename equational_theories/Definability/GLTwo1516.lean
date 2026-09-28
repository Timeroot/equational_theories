import equational_theories.Definability.GLTwoE63

/-! Reducing GL-equivariant E1516 companions to a homogeneous operation on a line.
The finite order-29 homogeneous classification is a separate proof obligation.
Nothing in this module assumes the external CP-SAT search is a Lean theorem. -/
namespace Definability.GLTwo1516
open GLTwoE63

variable {K : Type} [Field K]

/-- In a left-cancellative E1516 magma, an involutive squaring automorphism
must be the identity. This disposes of the multiplier -1 case without SAT. -/
lemma square_involution_idempotent {A : Type*} (p : A → A → A)
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y)))
    (hlc : ∀ a b c, p a b = p a c → b = c)
    (ha : ∀ x y, p (p x y) (p x y) = p (p x x) (p y y))
    (hi : ∀ x, p (p x x) (p x x) = x) : ∀ x, p x x = x := by
  let S := fun x => p x x
  have hS (x y) : S (p x y) = p (S x) (S y) := ha x y
  have hSS (x) : S (S x) = x := hi x
  intro x
  have hx : x = p (S x) (p x (S x)) := hlaw x x
  have hs : S x = p x (p (S x) x) := by
    calc
      S x = S (p (S x) (p x (S x))) := congrArg S hx
      _ = p (S (S x)) (S (p x (S x))) := hS (S x) (p x (S x))
      _ = p x (p (S x) x) := by
        exact congrArg₂ p (hSS x)
          ((hS x (S x)).trans (congrArg (p (S x)) (hSS x)))
  have hleft : p (S x) x = x := hlc x _ _ hs.symm
  have hright : p x (S x) = S x := by
    calc
      p x (S x) = p (S (S x)) (S x) := congrArg (fun z => p z (S x)) (hSS x).symm
      _ = S (p (S x) x) := (hS (S x) x).symm
      _ = S x := congrArg S hleft
  exact hlc x _ _ hright

def Homogeneous (p : K → K → K) : Prop :=
  ∀ t x y, t ≠ 0 → p (t*x) (t*y) = t*p x y

def line (q : V K → V K → V K) (x y : K) : K := (q (x,0) (y,0)).1

lemma line_pair {q : V K → V K → V K} (he : Equivariant q) (h2 : (2:K) ≠ 0)
    (x y : K) : q (x,0) (y,0) = (line q x y,0) := by
  apply Prod.ext
  · rfl
  · exact axis1 he h2 x y

lemma line_homogeneous {q : V K → V K → V K} (he : Equivariant q) :
    Homogeneous (line q) := by
  intro t x y ht
  have hd : t*t-0*0 ≠ 0 := by simpa using mul_ne_zero ht ht
  have h := congrArg Prod.fst (he t 0 0 t hd (x,0) (y,0))
  simpa [matrix, line] using h.symm

lemma line_law {q : V K → V K → V K} (he : Equivariant q) (h2 : (2:K) ≠ 0)
    (h : ∀ x y, x = q (q y y) (q x (q x y))) :
    ∀ x y, x = line q (line q y y) (line q x (line q x y)) := by
  intro x y
  have hh := h (x,0) (y,0)
  simp only [line_pair he h2] at hh
  exact congrArg Prod.fst hh

lemma idempotent_of_line_one {q : V K → V K → V K} (he : Equivariant q)
    (h2 : (2:K) ≠ 0) (h : line q 1 1 = 1) : ∀ x, q x x = x := by
  have hone : q e1 e1 = e1 := by simpa [h] using line_pair he h2 1 1
  intro x
  rcases x with ⟨x,y⟩
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · subst y
      apply Prod.ext
      · exact axis2 he h2 0 0
      · exact axis1 he h2 0 0
    · have hd : (0:K)*0-1*y ≠ 0 := by simpa using hy
      have hh := he 0 1 y 0 hd e1 e1
      simpa [hone, matrix, e1] using hh.symm
  · have hd : x*1-0*y ≠ 0 := by simpa using hx
    have hh := he x 0 y 1 hd e1 e1
    simpa [hone, matrix, e1] using hh.symm

lemma root_of_equivariant_of_homogeneous_classification
    {q : V K → V K → V K} (he : Equivariant q) (h2 : (2:K) ≠ 0)
    (h : ∀ x y, x = q (q y y) (q x (q x y)))
    (hc : ∀ p : K → K → K, Homogeneous p →
      (∀ x y, x = p (p y y) (p x (p x y))) → p 1 1 = 1) :
    ∃ d : K, d^5+d^4+1 = 0 := by
  have hi := idempotent_of_line_one he h2
    (hc (line q) (line_homogeneous he) (line_law he h2 h))
  apply root_of_equivariant he h2
  intro x y
  simpa only [hi] using h x y

open Law Law.MagmaLaw

/-- The homogeneous classification, when proved, rules out definability from
any scalar source over this field for which the E63 polynomial has no root. -/
theorem not_definableFromFin [Finite K] (a b : K) {L : NatMagmaLaw}
    (hs : @satisfies _ (V K) (source a b) L)
    (h2 : (2:K) ≠ 0) (hr : ∀ d : K, d^5+d^4+1 ≠ 0)
    (hc : ∀ p : K → K → K, Homogeneous p →
      (∀ x y, x = p (p y y) (p x (p x y))) → p 1 1 = 1) :
    ¬ Law1516.DefinableFromFin L := by
  intro hd
  obtain ⟨N, hN, hdef⟩ := hd (source a b) hs
  obtain ⟨d, hd⟩ := root_of_equivariant_of_homogeneous_classification
    (equivariant_of_definable a b N hdef) h2
    ((@Law1516.models_iff (V K) N).mp hN) hc
  exact hr d hd

/-- info: 'Definability.GLTwo1516.not_definableFromFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_definableFromFin
end Definability.GLTwo1516
