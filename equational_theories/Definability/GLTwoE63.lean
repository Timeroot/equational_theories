import equational_theories.Definability.Negative
import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A general-linear symmetry obstruction to first-order definitions of E63.
Only two-dimensional vector spaces and a scalar root obstruction are needed. -/

namespace Definability.GLTwoE63

variable {K : Type} [Field K]
abbrev V (K : Type) := K × K

def matrix (a b c d : K) (v : V K) : V K :=
  (a * v.1 + b * v.2, c * v.1 + d * v.2)

lemma matrix_injective (a b c d : K) (h : a*d-b*c ≠ 0) :
    Function.Injective (matrix a b c d) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  change a*x.1+b*x.2 = a*y.1+b*y.2 at h1
  change c*x.1+d*x.2 = c*y.1+d*y.2 at h2
  apply Prod.ext
  · apply mul_left_cancel₀ h
    linear_combination d*h1-b*h2
  · apply mul_left_cancel₀ h
    linear_combination a*h2-c*h1

noncomputable def matrixEquiv [Finite K] (a b c d : K) (h : a*d-b*c ≠ 0) :
    V K ≃ V K := Equiv.ofBijective (matrix a b c d)
      ⟨matrix_injective a b c d h, Finite.surjective_of_injective (matrix_injective a b c d h)⟩

@[implicit_reducible] def source (a b : K) : Magma (V K) :=
  ⟨fun x y => (a*x.1+b*y.1, a*x.2+b*y.2)⟩

lemma matrix_source (a b c d s t : K) : (source s t).IsEndo (matrix a b c d) := by
  intro x y
  change matrix a b c d (s*x.1+t*y.1, s*x.2+t*y.2) =
    (s*(matrix a b c d x).1+t*(matrix a b c d y).1,
     s*(matrix a b c d x).2+t*(matrix a b c d y).2)
  apply Prod.ext <;> dsimp [matrix] <;> ring

def Equivariant (q : V K → V K → V K) : Prop :=
  ∀ a b c d (_h : a*d-b*c ≠ 0) x y,
    matrix a b c d (q x y) = q (matrix a b c d x) (matrix a b c d y)

lemma equivariant_of_definable [Finite K] (a b : K) (N : Magma (V K))
    (h : @Set.Definable (V K) ∅ MagmaLanguage (source a b).FOStructure
      (Option (Fin 2)) N.Graph) : Equivariant N.op := by
  intro c d e f hdet x y
  exact Magma.IsEndo.of_definable h (e := matrixEquiv c d e f hdet)
    (matrix_source c d e f a b) x y

abbrev e1 : V K := (1,0)
abbrev e2 : V K := (0,1)

lemma transport {q : V K → V K → V K} (he : Equivariant q)
    (a b c d : K) (hd : a*d-b*c ≠ 0) :
    q (a,c) (b,d) =
      (a*(q e1 e2).1+b*(q e1 e2).2, c*(q e1 e2).1+d*(q e1 e2).2) := by
  simpa [matrix, e1, e2] using (he a b c d hd e1 e2).symm

lemma axis1 {q : V K → V K → V K} (he : Equivariant q) (h2 : (2:K) ≠ 0)
    (x y : K) : (q (x,0) (y,0)).2 = 0 := by
  have h := congrArg Prod.snd (he 1 0 0 (-1) (by simp) (x,0) (y,0))
  simp only [matrix, one_mul, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul] at h
  have hz : (2:K) * (q (x,0) (y,0)).2 = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left h2

lemma axis2 {q : V K → V K → V K} (he : Equivariant q) (h2 : (2:K) ≠ 0)
    (x y : K) : (q (0,x) (0,y)).1 = 0 := by
  have h := congrArg Prod.fst (he (-1) 0 0 1 (by simp) (0,x) (0,y))
  simp only [matrix, one_mul, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul] at h
  have hz : (2:K) * (q (0,x) (0,y)).1 = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left h2

lemma cross_first {q : V K → V K → V K} (he : Equivariant q) (h2 : (2:K) ≠ 0)
    (x : K) : (q e2 (x,0)).1 = x*(q e1 e2).2 := by
  by_cases hx : x = 0
  · subst x
    simpa [e2] using axis2 he h2 1 0
  · have h := congrArg Prod.fst (transport he 0 x 1 0 (by simpa using hx))
    simpa [e2] using h

lemma root_of_equivariant {q : V K → V K → V K} (he : Equivariant q)
    (h2 : (2:K) ≠ 0)
    (h63 : ∀ x y, x = q y (q x (q x y))) :
    ∃ d : K, d^5+d^4+1 = 0 := by
  let a := (q e1 e2).1
  let b := (q e1 e2).2
  have hab : q e1 e2 = (a,b) := Prod.eta _
  have hb : b ≠ 0 := by
    intro hb
    have hz := axis1 he h2 1 a
    have hinner : q e1 (a,b) = ((q e1 (a,b)).1,0) := by
      apply Prod.ext
      · rfl
      · simpa [e1, hb] using hz
    have h := congrArg Prod.fst (h63 e1 e2)
    rw [hab, hinner, cross_first he h2] at h
    change 1 = _ * b at h
    rw [hb, mul_zero] at h
    exact one_ne_zero h
  have hm : q e1 (a,b) = (a*(1+b), b^2) := by
    have h := transport he 1 a 0 b (by simpa using hb)
    change q e1 (a,b) = _ at h
    rw [h]
    apply Prod.ext <;> dsimp [a,b] <;> ring
  have ha : a*(1+b) ≠ 0 := by
    intro ha
    have h := congrArg Prod.fst (h63 e1 e2)
    rw [hab, hm, ha] at h
    have hz := axis2 he h2 1 (b^2)
    change 1 = (q (0,1) (0,b^2)).1 at h
    rw [hz] at h
    exact one_ne_zero h
  have ht := transport he 0 (a*(1+b)) 1 (b^2) (by simpa using ha)
  have h := h63 e1 e2
  rw [hab, hm, ht] at h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  change 1 = 0*a+(a*(1+b))*b at hfirst
  change 0 = 1*a+b^2*b at hsecond
  refine ⟨b, ?_⟩
  linear_combination hfirst - b*(1+b)*hsecond

lemma root_of_definable [Finite K] (a b : K) (N : Magma (V K)) (h2 : (2:K) ≠ 0)
    (hd : @Set.Definable (V K) ∅ MagmaLanguage (source a b).FOStructure
      (Option (Fin 2)) N.Graph)
    (h63 : @Equation63 (V K) N) : ∃ d : K, d^5+d^4+1 = 0 :=
  root_of_equivariant (equivariant_of_definable a b N hd) h2 h63

open Law Law.MagmaLaw

/-- If the E63 scalar polynomial has no root, a finite scalar-linear model
of any source law prevents a first-order definition of E63. -/
theorem not_definableFromFin [Finite K] (a b : K) {L : NatMagmaLaw}
    (hs : @satisfies _ (V K) (source a b) L)
    (h2 : (2:K) ≠ 0) (hr : ∀ d : K, d^5+d^4+1 ≠ 0) :
    ¬ Law63.DefinableFromFin L := by
  intro h
  obtain ⟨N, hN, hd⟩ := h (source a b) hs
  obtain ⟨d, hdroot⟩ := root_of_definable a b N h2 hd
    ((@Law63.models_iff (V K) N).mp hN)
  exact hr d hdroot

/-- info: 'Definability.GLTwoE63.root_of_definable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms root_of_definable
/-- info: 'Definability.GLTwoE63.not_definableFromFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_definableFromFin

end Definability.GLTwoE63
