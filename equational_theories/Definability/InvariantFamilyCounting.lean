import equational_theories.Definability.FiniteSymmetry
import equational_theories.Definability.CloneFamilyCounting
import Mathlib.Algebra.Group.Defs

/-! Clone counting for a complete family of operations preserved by given permutations,
and an exact test that fixes the first variable at zero in a translation-invariant magma. -/
open Law Law.MagmaLaw FreeMagma
namespace Magma.InvariantFamily

theorem not_termStructuralFromFin {A P G : Type} [Fintype A] [Inhabited A] [Fintype P]
    (generators : G → A → A) (F : P → Magma A)
    (hF : Function.Injective (fun p => (F p).op))
    (coverage : ∀ N : Magma A, (∀ i, N.IsEndo (generators i)) → ∃ p, F p = N)
    (hfamily : ∀ p i, (F p).IsEndo (generators i))
    {L L' : NatMagmaLaw} (S T : P → Prop) [DecidablePred S] [DecidablePred T]
    (hS : ∀ p, S p → @satisfies _ A (F p) L')
    (hT : ∀ p, @satisfies _ A (F p) L → T p)
    (hcount : Fintype.card {p // T p} < Fintype.card {p // S p}) :
    ¬ L.TermStructuralFromFin L' := by
  classical
  obtain ⟨p₁,h₁⟩ := coverage ⟨fun x _ => x⟩ (fun _ _ _ => rfl)
  obtain ⟨p₂,h₂⟩ := coverage ⟨fun _ y => y⟩ (fun _ _ _ => rfl)
  have hcomp : ∀ p q r, ∃ s, F s = ⟨fun x y => (F p).op ((F q).op x y) ((F r).op x y)⟩ := by
    intro p q r
    apply coverage
    intro i x y
    change generators i ((F p).op ((F q).op x y) ((F r).op x y)) = _
    rw [hfamily p i, hfamily q i, hfamily r i]
    rfl
  choose comp hc using hcomp
  apply not_termStructuralFromFin_of_cloneFamily_count (fun p => (F p).op) hF p₁ p₂ comp
    (by intro x y; exact congrArg (fun N : Magma A => @Magma.op A N x y) h₁)
    (by intro x y; exact congrArg (fun N : Magma A => @Magma.op A N x y) h₂)
    (by intro p q r x y; exact congrArg (fun N : Magma A => @Magma.op A N x y) (hc p q r)) S T hS hT hcount

theorem family_endos {n g k m : ℕ}
    (generators : Fin g → Equiv.Perm (Fin n)) (words : Fin k → List (Fin g))
    (tr : Fin n → Fin n → Fin m × Fin k) (sizes : Fin m → ℕ)
    (values : (i : Fin m) → Fin (sizes i) → Fin n)
    (hindex : ∀ i x y, (tr (generators i x) (generators i y)).1 = (tr x y).1)
    (hvalue : ∀ i x y a,
      generators i (FiniteSymmetry.wordPerm generators (words (tr x y).2) (values (tr x y).1 a)) =
      FiniteSymmetry.wordPerm generators (words (tr (generators i x) (generators i y)).2)
        (values (tr x y).1 a))
    (p : (i : Fin m) → Fin (sizes i)) :
    ∀ i, (FiniteSymmetry.family generators words tr sizes values p).IsEndo (generators i) := by
  intro i x y
  change generators i (FiniteSymmetry.wordPerm generators (words (tr x y).2)
    (values (tr x y).1 (p (tr x y).1))) =
    FiniteSymmetry.wordPerm generators (words (tr (generators i x) (generators i y)).2)
      (values (tr (generators i x) (generators i y)).1 (p (tr (generators i x) (generators i y)).1))
  rw [hindex]
  exact hvalue i x y _

variable {A : Type} [AddCommGroup A] {k : ℕ}

def ZeroTest (M : Magma A) (L : MagmaLaw (Fin (k+1))) : Prop :=
  ∀ φ : Fin k → A, @evalInMagma _ _ M (Fin.cons 0 φ) L.lhs =
    @evalInMagma _ _ M (Fin.cons 0 φ) L.rhs
instance [Fintype A] [DecidableEq A] (M : Magma A) (L : MagmaLaw (Fin (k+1))) :
    Decidable (ZeroTest M L) := by unfold ZeroTest; infer_instance

theorem eval_translate (M : Magma A) (h : ∀ a, M.IsEndo (fun x => a+x))
    (a : A) (φ : Fin k → A) (t : FreeMagma (Fin k)) :
    @evalInMagma _ _ M (fun i => a+φ i) t = a + @evalInMagma _ _ M φ t := by
  induction t with
  | Leaf i => rfl
  | Fork l r hl hr =>
    change M.op _ _ = a + M.op _ _
    rw [hl,hr]
    exact (h a _ _).symm

theorem zeroTest_iff_satisfies (M : Magma A) (h : ∀ a, M.IsEndo (fun x => a+x))
    (L : MagmaLaw (Fin (k+1))) : ZeroTest M L ↔ @satisfies _ A M L := by
  constructor
  · intro ht φ
    let ψ : Fin k → A := fun i => φ i.succ - φ 0
    have he : φ = fun i : Fin (k+1) => φ 0 + (Fin.cons 0 ψ : Fin (k+1) → A) i := by
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ i => simp [ψ]
    change @evalInMagma _ _ M φ L.lhs = @evalInMagma _ _ M φ L.rhs
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    rw [eval_translate M h, eval_translate M h, ht ψ]
  · intro ht φ
    exact ht (Fin.cons 0 φ)
end Magma.InvariantFamily

/-- info: 'Magma.InvariantFamily.not_termStructuralFromFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.InvariantFamily.not_termStructuralFromFin
/-- info: 'Magma.InvariantFamily.zeroTest_iff_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.InvariantFamily.zeroTest_iff_satisfies
/-- info: 'Magma.InvariantFamily.family_endos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.InvariantFamily.family_endos
