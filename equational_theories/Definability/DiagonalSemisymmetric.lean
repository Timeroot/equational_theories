import equational_theories.Definability.DivisionFO
import equational_theories.Definability.QuasigroupWitness
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# An invertible diagonal change from E14 to E3272

Let `D x = x ◇ x`. If `D` is a permutation and `◇` satisfies E14, then
`x □ y = D⁻¹ (x ◇ D y)` satisfies E3272. Its diagonal is `D⁻¹`, and applying
this change a second time recovers `◇`. Both operations therefore define each
other by the same atomic formula `z ◇ z = x ◇ (y ◇ y)`.

This is a conditional structural construction, not a resolution of the general
finite E14 → E3272 definability question: finite E14 magmas can have nonbijective
squaring. For finite carriers the inverse permutation is a power, so the
construction and its inverse are also magma terms.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

namespace DiagonalSemisymmetric

variable {G : Type}

/-- Change an operation by its invertible diagonal. -/
@[implicit_reducible]
def twist (M : Magma G) (d : Equiv.Perm G) : Magma G :=
  ⟨fun x y => d.symm (M.op x (d y))⟩

@[simp] theorem twist_op (M : Magma G) (d : Equiv.Perm G) (x y : G) :
    (twist M d).op x y = d.symm (M.op x (d y)) := rfl

theorem twist_diagonal (M : Magma G) (d : Equiv.Perm G)
    (hd : ∀ x, M.op x x = d x) (h : @Equation14 G M) (x : G) :
    (twist M d).op x x = d.symm x := by
  change d.symm (M.op x (d x)) = d.symm x
  rw [← hd, ← h x x]

theorem twist_satisfies_3272 (M : Magma G) (d : Equiv.Perm G)
    (hd : ∀ x, M.op x x = d x) (h : @Equation14 G M) :
    @Equation3272 G (twist M d) := by
  intro x y
  rw [twist_diagonal M d hd h x, twist_diagonal M d hd h y]
  simp only [twist_op, Equiv.apply_symm_apply]
  rw [← h x y]

/-- The diagonal change is an involution. -/
theorem twist_twice (M : Magma G) (d : Equiv.Perm G) :
    twist (twist M d) d.symm = M := by
  cases M
  simp only [twist]
  congr 1
  funext x y
  simp

/-- The same atomic formula defines both directions of the construction. -/
def graphFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.equal (DivisionFO.ap G (var none) (var none))
    (DivisionFO.ap G (var (some 0))
      (DivisionFO.ap G (var (some 1)) (var (some 1))))

@[simp] theorem realize_graphFormula (M : Magma G) (v : Option (Fin 2) → G) :
    @Formula.Realize _ G M.FOStructure₀ _ (graphFormula G) v ↔
      M.op (v none) (v none) = M.op (v (some 0)) (M.op (v (some 1)) (v (some 1))) := by
  rfl

theorem definable_graph_twist (M : Magma G) (d : Equiv.Perm G)
    (hd : ∀ x, M.op x x = d x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ (twist M d).Graph := by
  refine ⟨graphFormula G, Set.ext fun v => ?_⟩
  show (twist M d).op (v (some 0)) (v (some 1)) = v none ↔ _
  rw [Set.mem_setOf_eq, realize_graphFormula, hd, hd, twist_op]
  exact d.symm_apply_eq.trans eq_comm

/-- A bijective diagonal suffices for FO-structural interpretability, even on
infinite carriers. Neither an automorphism property for the diagonal nor
commutativity is needed. -/
theorem structuralOn_of_bijective_diagonal (M : Magma G)
    (h : @Equation14 G M) (hd : Function.Bijective fun x => M.op x x) :
    Law3272.StructuralOnMagma M := by
  let d := Equiv.ofBijective (fun x => M.op x x) hd
  have hdiag : ∀ x, M.op x x = d x := fun _ => rfl
  refine ⟨twist M d, (@Law3272.models_iff G (twist M d)).mpr (twist_satisfies_3272 M d hdiag h),
    definable_graph_twist M d hdiag, ?_⟩
  simpa only [twist_twice] using
    definable_graph_twist (twist M d) d.symm (twist_diagonal M d hdiag h)

/-- Repeated squaring, as a term rather than a numerical operation. -/
def squareIter {α : Type} (t : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    ℕ → (MagmaLanguage[[(∅ : Set G)]]).Term α
  | 0 => t
  | n + 1 => DivisionFO.ap G (squareIter t n) (squareIter t n)

theorem realize_squareIter (M : Magma G) {α : Type}
    (t : (MagmaLanguage[[(∅ : Set G)]]).Term α) (v : α → G) (n : ℕ) :
    @Term.realize _ G M.FOStructure₀ _ v (squareIter t n) =
      (fun x => M.op x x)^[n] (@Term.realize _ G M.FOStructure₀ _ v t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change M.op (@Term.realize _ G M.FOStructure₀ _ v (squareIter t n))
      (@Term.realize _ G M.FOStructure₀ _ v (squareIter t n)) = _
    rw [ih, Function.iterate_succ_apply']

/-- On a finite carrier, an inverse diagonal can be replaced by a sufficiently
large fixed number of squarings. -/
theorem termDefinable_twist [Finite G] (M : Magma G) (d : Equiv.Perm G)
    (hd : ∀ x, M.op x x = d x) :
    @Set.TermDefinable _ (∅ : Set G) MagmaLanguage M.FOStructure _
      (twist M d).FinArityOp := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  have hperiod := hN d d.injective
  have hinv : ∀ x, d^[N] x = d.symm x := by
    intro x
    apply d.injective
    have hp := congrFun hperiod x
    rw [Function.iterate_succ_apply'] at hp
    simpa only [Equiv.apply_symm_apply] using hp
  refine ⟨squareIter (DivisionFO.ap G (var 0)
    (DivisionFO.ap G (var 1) (var 1))) N, ?_⟩
  funext v
  rw [realize_squareIter]
  change d.symm (M.op (v 0) (d (v 1))) = (fun x => M.op x x)^[N] (M.op (v 0) (M.op (v 1) (v 1)))
  rw [show (fun x => M.op x x) = d from funext hd, hd, hinv]

/-- In the finite case both directions of the diagonal change are term-defined. -/
theorem termStructuralOn_of_bijective_diagonal [Finite G] (M : Magma G)
    (h : @Equation14 G M) (hd : Function.Bijective fun x => M.op x x) :
    Law3272.TermStructuralOnMagma M := by
  let d := Equiv.ofBijective (fun x => M.op x x) hd
  have hdiag : ∀ x, M.op x x = d x := fun _ => rfl
  refine ⟨twist M d,
    (@Law3272.models_iff G (twist M d)).mpr (twist_satisfies_3272 M d hdiag h),
    termDefinable_twist M d hdiag, ?_⟩
  simpa only [twist_twice] using
    termDefinable_twist (twist M d) d.symm (twist_diagonal M d hdiag h)

/-- An equivariant self-map on a finite transitive set is a permutation. Here the
self-map is squaring and transitivity is stated directly through automorphisms. -/
theorem bijective_diagonal_of_transitive [Finite G] (M : Magma G)
    (ht : ∀ a b : G, ∃ e : Equiv.Perm G,
      (∀ x y, e (M.op x y) = M.op (e x) (e y)) ∧ e a = b) :
    Function.Bijective fun x => M.op x x := by
  suffices hs : Function.Surjective fun x => M.op x x from
    ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  intro y
  obtain ⟨e, he, hey⟩ := ht (M.op y y) y
  exact ⟨e y, (he y y).symm.trans hey⟩

/-- In particular, a finite counterexample to FO-definability cannot have a
transitive automorphism group. -/
theorem termStructuralOn_of_transitive [Finite G] (M : Magma G)
    (h : @Equation14 G M)
    (ht : ∀ a b : G, ∃ e : Equiv.Perm G,
      (∀ x y, e (M.op x y) = M.op (e x) (e y)) ∧ e a = b) :
    Law3272.TermStructuralOnMagma M :=
  termStructuralOn_of_bijective_diagonal M h (bijective_diagonal_of_transitive M ht)

/-- In a commutative E14 magma, the fixed points of left multiplication by `x`
are precisely the square roots of `x`. -/
theorem fixed_iff_square (M : Magma G) (h : @Equation14 G M)
    (hc : ∀ x y, M.op x y = M.op y x) (x z : G) :
    M.op x z = z ↔ M.op z z = x := by
  constructor
  · intro hz
    have hx := h x z
    rwa [hz, eq_comm] at hx
  · intro hz
    rw [← hz, hc]
    exact (h z z).symm

/-- Every left multiplication in a commutative E14 magma is an involution. -/
theorem left_involutive (M : Magma G) (h : @Equation14 G M)
    (hc : ∀ x y, M.op x y = M.op y x) (x : G) :
    Function.Involutive (M.op x) := by
  intro z
  rw [← hc z x]
  exact (h z x).symm

/-- Every diagonal fiber in a finite commutative E14 magma has the same parity
as the whole carrier. This follows by pairing the nonfixed points of the
corresponding left translation. -/
theorem card_square_fiber_modEq [Fintype G] (M : Magma G)
    (h : @Equation14 G M) (hc : ∀ x y, M.op x y = M.op y x) (x : G) :
    Fintype.card G ≡ Nat.card {z : G // M.op z z = x} [MOD 2] := by
  classical
  let f : Function.End G := M.op x
  have hf : f ^ (2 ^ 1) = 1 := funext (left_involutive M h hc x)
  let e : Function.fixedPoints f ≃ {z : G // M.op z z = x} :=
    Equiv.subtypeEquivRight (fixed_iff_square M h hc x)
  have hp := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  rw [Fintype.card_congr e] at hp
  simpa only [Nat.card_eq_fintype_card] using hp

/-- Odd finite commutative E14 magmas have bijective squaring: every left
multiplication is an involution on an odd set, hence has a fixed point, which is
a square root of its index. -/
theorem bijective_diagonal_of_commutative_odd [Fintype G] (M : Magma G)
    (h : @Equation14 G M) (hc : ∀ x y, M.op x y = M.op y x)
    (hodd : Odd (Fintype.card G)) :
    Function.Bijective fun x => M.op x x := by
  suffices hs : Function.Surjective fun x => M.op x x from
    ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  intro x
  let e := Function.Involutive.toPerm (M.op x) (left_involutive M h hc x)
  have he : e ^ (2 ^ 1) = 1 := by
    ext z
    exact left_involutive M h hc x z
  obtain ⟨z, hz⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (p := 2) (n := 1) hodd.not_two_dvd_nat he
  exact ⟨z, (fixed_iff_square M h hc x z).mp hz⟩

/-- The finite odd-order commutative subclass admits the stronger term-structural
construction. The general even-order subclass remains outside this argument. -/
theorem termStructuralOn_of_commutative_odd [Fintype G] (M : Magma G)
    (h : @Equation14 G M) (hc : ∀ x y, M.op x y = M.op y x)
    (hodd : Odd (Fintype.card G)) :
    Law3272.TermStructuralOnMagma M :=
  termStructuralOn_of_bijective_diagonal M h
    (bijective_diagonal_of_commutative_odd M h hc hodd)

end DiagonalSemisymmetric
