import equational_theories.Parastrophes.Equation1518Uniform
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Prod

/-!
# Finite pools cannot replace a uniform inverse-square term

Suppose a finite list of unary terms supplies a square root at every point of
every finite E1518 model, allowing the chosen term to depend on both the model
and the point. Then one term in that list works everywhere. Otherwise choose
one pointed countermodel per term and take their finite direct product: the
term selected for the product still fails in its own coordinate.

This is a finite-product argument, not compactness over arbitrary carriers.
In particular, to disprove finite uniform recovery it suffices to construct
pointed finite models requiring arbitrarily deep terms. The theorem does not
assert that such an unbounded family has yet been constructed.
-/
namespace Parastrophes.Eq1518Uniform
open FreeMagma

@[implicit_reducible] def productMagma {I : Type} {G : I → Type}
    (M : ∀ i, Magma (G i)) : Magma (∀ i, G i) :=
  ⟨fun x y i => (M i).op (x i) (y i)⟩

theorem product_law {I : Type} {G : I → Type} (M : ∀ i, Magma (G i))
    (h : ∀ i, @Equation1518 (G i) (M i)) :
    @Equation1518 (∀ i, G i) (productMagma M) := by
  intro x y
  funext i
  exact h i (x i) (y i)

theorem product_eval {I : Type} {G : I → Type} (M : ∀ i, Magma (G i))
    (t : FreeMagma (Fin 2)) (x : ∀ i, G i) (i : I) :
    ((termMagma (productMagma M) t).op x x) i =
      (termMagma (M i) t).op (x i) (x i) := by
  simp only [Magma.op, ite_self]
  change (@evalInMagma _ _ (productMagma M) (fun _ => x) t) i =
    @evalInMagma _ _ (M i) (fun _ => x i) t
  induction t with
  | Leaf _ => rfl
  | Fork t u ihT ihU => exact congrArg₂ (M i).op ihT ihU

/-- Model- and point-dependent choice from a fixed finite pool already gives
one uniform term. No bound on the orders of the models is assumed. -/
theorem finite_pool (terms : Finset (FreeMagma (Fin 2)))
    (h : ∀ (G : Type) (M : Magma G), Finite G → @Equation1518 G M → ∀ x,
      ∃ t ∈ terms, M.op ((termMagma M t).op x x) ((termMagma M t).op x x) = x) :
    ∃ t ∈ terms, SquareRootWitness t := by
  classical
  by_contra hn
  have bad : ∀ t : ↥terms, ∃ (G : Type) (M : Magma G),
      Finite G ∧ @Equation1518 G M ∧ ∃ x,
        M.op ((termMagma M t.val).op x x) ((termMagma M t.val).op x x) ≠ x := by
    intro t
    have ht : ¬ SquareRootWitness t.val := fun hw => hn ⟨t.val, t.property, hw⟩
    simpa only [SquareRootWitness, not_forall, Classical.not_imp, exists_prop] using ht
  choose G M hG hM x hx using bad
  letI (i : ↥terms) : Finite (G i) := hG i
  obtain ⟨t, ht, he⟩ := h (∀ i, G i) (productMagma M) inferInstance (product_law M hM) x
  let i : ↥terms := ⟨t, ht⟩
  apply hx i
  have hc := congrFun he i
  change (M i).op (((termMagma (productMagma M) t).op x x) i)
    (((termMagma (productMagma M) t).op x x) i) = x i at hc
  simpa only [product_eval] using hc

/-- The finite pool of all binary terms of depth at most n. -/
def termsThrough : ℕ → Finset (FreeMagma (Fin 2))
  | 0 => Finset.univ.image Leaf
  | n + 1 => Finset.univ.image Leaf ∪
      ((termsThrough n) ×ˢ (termsThrough n)).image (fun p => Fork p.1 p.2)

theorem mem_termsThrough (t : FreeMagma (Fin 2)) (n : ℕ) :
    t ∈ termsThrough n ↔ termDepth t ≤ n := by
  induction n generalizing t with
  | zero => cases t <;> simp [termsThrough, termDepth]
  | succ n ih =>
    cases t with
    | Leaf i => simp [termsThrough, termDepth]
    | Fork t u =>
      simp only [termsThrough, Finset.mem_union, Finset.mem_image,
        FreeMagma.Fork.injEq]
      simp [ih, termDepth]

/-- Uniform finite left division is equivalent to a uniform bound on the
depth needed at a single point. The term may initially depend on that point;
the finite-product argument removes that dependence. -/
theorem recovery_iff_bounded_pointwise :
    UniformTermRecovery .fin Law1518 .left ↔
    ∃ n : ℕ, ∀ (G : Type) (M : Magma G), Finite G → @Equation1518 G M → ∀ x,
      ∃ t : FreeMagma (Fin 2), termDepth t ≤ n ∧
        M.op ((termMagma M t).op x x) ((termMagma M t).op x x) = x := by
  rw [recovery_iff_squareRoot]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨termDepth t, fun G M hG hM x => ⟨t, le_refl _, ht G M hG hM x⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨t, _, ht⟩ := finite_pool (termsThrough n) (by
      intro G M hG hM x
      obtain ⟨t, ht, hr⟩ := hn G M hG hM x
      exact ⟨t, (mem_termsThrough t n).mpr ht, hr⟩)
    exact ⟨t, ht⟩

end Parastrophes.Eq1518Uniform
