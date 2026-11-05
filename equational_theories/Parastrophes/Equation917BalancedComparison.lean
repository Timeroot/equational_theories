import equational_theories.Parastrophes.Equation917PowerComparison

/-!
# A balanced comparison for the E917 division image

Write q(x)=(x*(x*x))*x, U(x)=x*q(x), and H(x,y)=q(x)*(x*y).
The proposed single identity is

    x = (((U(w)*U(z))*(U(y)*t))*v) * H(x,((w*z)*(y*t))*v).

There are 26 operations and six variables. Every actual E917 left image
satisfies it. It forces all rows onto on arbitrary carriers, and hence a
quasigroup on finite carriers. Its exact finite permutation reduction is
recorded below; that reduction is not yet a proof of the converse.
-/
namespace Parastrophes.Eq917Image.BalancedComparison
open Law FreeMagma
open SandwichCandidate (U H)

variable {A : Type} (D : Magma A)

def tree (w z y t : A) := D.op (D.op w z) (D.op y t)
def shifted (w z y t : A) := D.op (D.op (U D w) (U D z)) (D.op (U D y) t)
def Identity : Prop := ∀ x w z y t v,
  x = D.op (D.op (shifted D w z y t) v) (H D x (D.op (tree D w z y t) v))

theorem of_basis (h : Basis D) : Identity D := by
  have hu (x) : U D x = x := (h.1 x).symm
  intro x w z y t v
  simp only [shifted, hu]
  exact h.2 x _

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hm, hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))

/-- A row indexed by a shifted tree value followed by any product is onto.
Starting with one such value i, its U-row is onto. This lets us make every
product k*b another shifted tree value, where k=U(i)*U(i). In particular
U(k) is a tree value. Its product with U(i) indexes another onto row; that
row finally makes U(i) itself a tree value. Its onto row now supplies all
row indices. This argument needs no finiteness or injectivity. -/
theorem rows_surjective (h : Identity D) : ∀ a, Function.Surjective (D.op a) := by
  have good (w z y t v : A) :
      Function.Surjective (D.op (D.op (shifted D w z y t) v)) :=
    fun x => ⟨_, (h x w z y t v).symm⟩
  intro o
  let i := shifted D o o o o
  have hi : Function.Surjective (D.op (U D i)) := good o o o o (core D i)
  let k := D.op (U D i) (U D i)
  have hk (b v : A) : Function.Surjective (D.op (D.op (D.op k b) v)) := by
    obtain ⟨t, ht⟩ := hi b
    have he := good i i i t v
    change Function.Surjective (D.op (D.op (D.op k (D.op (U D i) t)) v)) at he
    simpa only [ht] using he
  have hj (v : A) : Function.Surjective (D.op (D.op (U D k) v)) := hk (core D k) v
  let l := D.op (U D k) (U D i)
  have hl : Function.Surjective (D.op l) := hj (U D i)
  obtain ⟨b, hb⟩ := hl (U D i)
  obtain ⟨t, ht⟩ := hi b
  have hp : shifted D k i i t = U D i := by
    change D.op l (D.op (U D i) t) = U D i
    rw [ht]
    exact hb
  obtain ⟨v, hv⟩ := hi o
  have he := good k i i t v
  simpa only [hp, hv] using he

/-- After finite row cancellation, the two trees define a common
permutation of row indices. Its crossed frame also gives column cancellation. -/
theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D := by
  have hq : IsSideQuasigroup .left D := fun x =>
    ⟨Finite.injective_iff_surjective.mpr (rows_surjective D h x),
      rows_surjective D h x⟩
  refine ⟨hq, fun o => ?_⟩
  classical
  let le (x : A) := Equiv.ofBijective (D.op x) (hq x)
  let j := tree D o o o o
  let k := shifted D o o o o
  let c : A ≃ A := (le j).symm.trans (le k)
  have frame (x y : A) : D.op (c y) (H D x y) = x := by
    have he := (h x o o o o ((le j).symm y)).symm
    change D.op ((le k) ((le j).symm y))
      (H D x ((le j) ((le j).symm y))) = x at he
    simpa only [(le j).apply_symm_apply] using he
  have col : Function.Injective (fun y => D.op y o) := by
    intro y z he
    let x := D.op y o
    have hy : H D x (c.symm y) = o := by
      apply (hq y).1
      simpa only [c.apply_symm_apply] using frame x (c.symm y)
    have hz : H D x (c.symm z) = o := by
      apply (hq z).1
      simpa only [c.apply_symm_apply] using (frame x (c.symm z)).trans he
    have hh := ((hq (core D x)).1.comp (hq x).1) (hy.trans hz.symm)
    exact c.symm.injective hh
  exact ⟨col, Finite.surjective_of_injective col⟩

/-- Four permutations give an exact normalized form. In particular U acts
in both arguments: the second rule and the first recover its right action.
Nothing here asserts that these permutations are the identity. -/
theorem reduction [Finite A] [Nonempty A] (h : Identity D) :
    ∃ a b g c : A ≃ A,
      (∀ x y, D.op (U D x) y = a (D.op x y)) ∧
      (∀ x y, D.op (U D x) (U D y) = b (D.op x y)) ∧
      (∀ x y, D.op (b x) (a y) = g (D.op x y)) ∧
      (∀ x y, D.op (g x) y = c (D.op x y)) ∧
      (∀ x y, D.op (c y) (H D x y) = x) := by
  classical
  let o : A := Classical.choice inferInstance
  have hq := quasigroup D h
  let le (x : A) := Equiv.ofBijective (D.op x) (hq.1 x)
  let re (x : A) := Equiv.ofBijective (fun y => D.op y x) (hq.2 x)
  let j := tree D o o o o
  let k := shifted D o o o o
  let c : A ≃ A := (le j).symm.trans (le k)
  have frame (x y : A) : D.op (c y) (H D x y) = x := by
    have he := (h x o o o o ((le j).symm y)).symm
    change D.op ((le k) ((le j).symm y))
      (H D x ((le j) ((le j).symm y))) = x at he
    simpa only [(le j).apply_symm_apply] using he
  have comparison (w z y t v : A) :
      D.op (shifted D w z y t) v = c (D.op (tree D w z y t) v) := by
    apply (hq.2 (H D o (D.op (tree D w z y t) v))).1
    exact (h o w z y t v).symm.trans (frame o _).symm
  let g : A ≃ A := (re o).trans (c.trans (re o).symm)
  have middle (w z y t : A) : shifted D w z y t = g (tree D w z y t) := by
    apply (re o).injective
    change D.op (shifted D w z y t) o =
      (re o) ((re o).symm (c ((re o) (tree D w z y t))))
    rw [(re o).apply_symm_apply]
    exact comparison w z y t o
  let a : A ≃ A := (le (D.op o o)).trans
    (g.trans (le (D.op (U D o) (U D o))).symm)
  have first (x y : A) : D.op (U D x) y = a (D.op x y) := by
    apply (le (D.op (U D o) (U D o))).injective
    change D.op (D.op (U D o) (U D o)) (D.op (U D x) y) =
      (le (D.op (U D o) (U D o)))
        ((le (D.op (U D o) (U D o))).symm (g ((le (D.op o o)) (D.op x y))))
    rw [(le (D.op (U D o) (U D o))).apply_symm_apply]
    exact middle o o x y
  let b : A ≃ A := (re (D.op o o)).trans
    (g.trans (re (D.op (U D o) o)).symm)
  have second (x y : A) : D.op (U D x) (U D y) = b (D.op x y) := by
    apply (re (D.op (U D o) o)).injective
    change D.op (D.op (U D x) (U D y)) (D.op (U D o) o) =
      (re (D.op (U D o) o))
        ((re (D.op (U D o) o)).symm (g ((re (D.op o o)) (D.op x y))))
    rw [(re (D.op (U D o) o)).apply_symm_apply]
    exact middle x y o o
  have third (x y : A) : D.op (b x) (a y) = g (D.op x y) := by
    obtain ⟨z, rfl⟩ := (hq.1 o).2 x
    obtain ⟨t, rfl⟩ := (hq.1 o).2 y
    rw [← second, ← first]
    exact middle o z o t
  have fourth (x y : A) : D.op (g x) y = c (D.op x y) := by
    obtain ⟨z, rfl⟩ := (hq.1 (D.op o o)).2 x
    obtain ⟨t, rfl⟩ := (hq.1 o).2 z
    change D.op (g (tree D o o o t)) y = c (D.op (tree D o o o t) y)
    rw [← middle o o o t]
    exact comparison o o o t y
  exact ⟨a, b, g, c, first, second, third, fourth, frame⟩

theorem of_reduction (a b g c : A → A)
    (ha : ∀ x y, D.op (U D x) y = a (D.op x y))
    (hb : ∀ x y, D.op (U D x) (U D y) = b (D.op x y))
    (hg : ∀ x y, D.op (b x) (a y) = g (D.op x y))
    (hc : ∀ x y, D.op (g x) y = c (D.op x y))
    (hf : ∀ x y, D.op (c y) (H D x y) = x) : Identity D := by
  intro x w z y t v
  simp only [shifted, tree, hb, ha, hg, hc, hf]

/-- The two input shifts determine a right action of U as well as its left
action. The output shifts commute because they can be applied to independent
inputs of a product. These are consequences, not extra search assumptions. -/
theorem right_action (a b : A ≃ A)
    (ha : ∀ x y, D.op (U D x) y = a (D.op x y))
    (hb : ∀ x y, D.op (U D x) (U D y) = b (D.op x y)) :
    ∀ x y, D.op x (U D y) = a.symm (b (D.op x y)) := by
  intro x y
  apply a.injective
  rw [a.apply_symm_apply, ← ha, hb]

theorem commuting_outputs (a d g c : A → A) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (U D x) y = a (D.op x y))
    (hd : ∀ x y, D.op x (U D y) = d (D.op x y))
    (hc : ∀ x y, D.op (g x) y = c (D.op x y)) :
    Function.Commute a d ∧ Function.Commute c d := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := (hq.1 x).2 x
    have he : D.op (U D x) (U D y) = D.op (U D x) (U D y) := rfl
    conv_lhs at he => rw [ha, hd]
    conv_rhs at he => rw [hd, ha]
    simpa only [hy] using he
  · intro x
    obtain ⟨y, hy⟩ := (hq.1 x).2 x
    have he : D.op (g x) (U D y) = D.op (g x) (U D y) := rfl
    conv_lhs at he => rw [hc, hd]
    conv_rhs at he => rw [hd, hc]
    simpa only [hy] using he

theorem unit_bijective [Finite A] (h : Identity D) : Function.Bijective (U D) := by
  have hi : Function.Injective (U D) := by
    intro x y he
    letI : Nonempty A := ⟨x⟩
    obtain ⟨a, _, _, _, ha, _, _, _, _⟩ := reduction D h
    apply ((quasigroup D h).2 x).1
    change D.op x x = D.op y x
    apply a.injective
    rw [← ha, ← ha, he]
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- A period at one point is a period everywhere. Thus a counterexample
cannot have U-cycles of different lengths. This does not provide a fixed point. -/
theorem unit_iterate_fixed [Finite A] (h : Identity D) (n : ℕ) (o : A)
    (ho : (U D)^[n] o = o) : ∀ x, (U D)^[n] x = x := by
  letI : Nonempty A := ⟨o⟩
  obtain ⟨a, _, _, _, ha, _, _, _, _⟩ := reduction D h
  have hq := quasigroup D h
  have step (k : ℕ) (x y : A) : D.op ((U D)^[k] x) y = (a : A → A)^[k] (D.op x y) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', ha, ih]
  have aid (x : A) : (a : A → A)^[n] x = x := by
    obtain ⟨y, rfl⟩ := (hq.1 o).2 x
    rw [← step, ho]
  intro x
  apply (hq.2 o).1
  change D.op ((U D)^[n] x) o = D.op x o
  rw [step, aid]

theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : U D o = o) : Basis D := by
  have hu : ∀ x, U D x = x := by
    simpa only [Function.iterate_one] using unit_iterate_fixed D h 1 o ho
  have hq := quasigroup D h
  refine ⟨fun x => (hu x).symm, ?_⟩
  intro x y
  obtain ⟨v, hv⟩ := (hq.1 (tree D o o o o)).2 y
  have he := h x o o o o v
  have hs : shifted D o o o o = tree D o o o o := by simp only [shifted, tree, hu]
  simpa only [hs, hv, H] using he

end Parastrophes.Eq917Image.BalancedComparison
