import equational_theories.Parastrophes.Equation917SandwichAffine
import equational_theories.Parastrophes.Equation917SandwichPermutations
import equational_theories.Parastrophes.Equation917CompositionCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# The E917 sandwich candidate is exact at every prime order

This concerns the 782-operation sandwich candidate, NOT the distinct F²G⁴U
composition candidate. Its common permutations a,b,c commute. When a is one
full cycle, use coordinates in ZMod n in which a(x)=x+1. Commutation makes b
and c translations too. The row relations then force multiplication to be
affine, and the already checked affine converse forces a=id, a contradiction
on a nontrivial carrier. No finite-model search certificate is used.

Moreover all cycles of a have equal length: a power fixing one point fixes
every point. At prime order a is therefore either the identity or one full
cycle. Excluding the latter proves the full converse at every prime order.
The unrestricted composite-order converse remains open, and no catalogue
characterization attribute is registered.
-/
namespace Parastrophes.Eq917Image.SandwichCandidate

variable {n : ℕ} [NeZero n]

/-- A constant increment determines a function on the finite cyclic ring. -/
private theorem increment_formula (f : ZMod n → ZMod n) (d : ZMod n)
    (h : ∀ x, f (x + 1) = f x + d) (x : ZMod n) :
    f x = f 0 + x * d := by
  have hi (k : ℕ) : f k = f 0 + (k : ZMod n) * d := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, h, ih]
      ring
  simpa using hi x.val

/-- In coordinates where the common F-map is successor, the whole operation
is forced to be affine. The two coefficient permutations were not assumed
additive: that is the point of the calculation. -/
theorem affine_of_successor (D : Magma (ZMod n)) (h : Identity D)
    (hs : ∀ x y, F D x y = x + 1) :
    ∃ B d : ZMod n, ∀ x y, D.op x y = -B^3*x+B*y+d := by
  obtain ⟨a, b, c, _, _, _, hf, _, mb, ma, inv, ab, ac, _, _⟩ :=
    commuting_permutations D h
  have ha (x) : a x = x + 1 := (hf x 0).symm.trans (hs x 0)
  have hb (x) : b (x + 1) = b x + 1 := by
    have he := ab x
    simpa only [ha] using he.symm
  have hc (x) : c (x + 1) = c x + 1 := by
    have he := ac x
    simpa only [ha] using he.symm
  let beta := b 0
  let gamma := c 0
  have bval (x) : b x = x + beta := by
    have he := increment_formula b 1 hb x
    simpa only [mul_one, add_comm] using he
  have cval (x) : c x = x + gamma := by
    have he := increment_formula c 1 hc x
    simpa only [mul_one, add_comm] using he
  have row (x y) : D.op x y = D.op x 0 + y * gamma := by
    apply increment_formula
    intro t
    have he := ma x t
    simpa only [ha, cval] using he
  have bg : beta * gamma = 1 := by
    have he := mb 0 0
    rw [ha, bval, zero_add, row 0 beta] at he
    exact add_left_cancel he
  have shift (x) : D.op (x + beta) 0 = D.op x 0 - gamma^2 := by
    have he := inv x 0
    rw [bval, cval, zero_add, row (x + beta) gamma] at he
    linear_combination he
  have left (x) : D.op x 0 = D.op 0 0 - gamma^3*x := by
    let f := fun z => D.op (beta*z) 0
    have step (z) : f (z + 1) = f z + (-gamma^2) := by
      dsimp only [f]
      rw [mul_add, mul_one, shift]
      exact sub_eq_add_neg _ _
    have he := increment_formula f (-gamma^2) step (gamma*x)
    dsimp only [f] at he
    rw [← mul_assoc beta gamma x, bg, one_mul, mul_zero] at he
    linear_combination he
  refine ⟨gamma, D.op 0 0, ?_⟩
  intro x y
  rw [row, left]
  ring

/-- Every nontrivial cyclic-coordinate instance is impossible, regardless
of its order. This leaves the multiple-cycle obstruction open. -/
theorem no_successor_common_map [Nontrivial (ZMod n)]
    (D : Magma (ZMod n)) (h : Identity D) :
    ¬ (∀ x y, F D x y = x + 1) := by
  intro hs
  obtain ⟨B, d, he⟩ := affine_of_successor D h hs
  have hD : D = Affine.magma (-B^3) B d := by
    cases D with
    | mk op =>
      congr
      funext x y
      exact he x y
  have hb := Affine.basis (-B^3) B d (hD ▸ h)
  have hz := hb.2 0 0
  change (0 : ZMod n) = F (Affine.magma (-B^3) B d) 0 0 at hz
  rw [← hD, hs, zero_add] at hz
  exact zero_ne_one hz

/-- The same obstruction on an arbitrary carrier with an explicit cyclic
labeling of its common map. Transporting the operation preserves every term
in the candidate. -/
theorem no_cyclic_labeling {A : Type} [Nontrivial (ZMod n)]
    (D : Magma A) (h : Identity D) (e : A ≃ ZMod n) :
    ¬ (∀ x y, e (F D x y) = e x + 1) := by
  intro hs
  let M : Magma (ZMod n) := ⟨fun x y => e (D.op (e.symm x) (e.symm y))⟩
  have hop (x y) : M.op x y = e (D.op (e.symm x) (e.symm y)) := rfl
  have hm : Identity M := by
    intro x y z w
    have he := congrArg e (h (e.symm x) (e.symm y) (e.symm z) (e.symm w))
    simpa only [U, F, G, H, core, hop, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply] using he
  apply no_successor_common_map M hm
  intro x y
  have he := hs (e.symm x) (e.symm y)
  simpa only [F, H, core, hop, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply] using he

/-- Label a full permutation cycle by its successive powers. -/
private theorem label_cycle {A : Type} [Fintype A]
    (a : Equiv.Perm A) (ha : a.IsCycleOn Set.univ)
    (hcard : Fintype.card A = n) (o : A) :
    ∃ e : A ≃ ZMod n, ∀ x, e (a x) = e x + 1 := by
  classical
  have hac : a.IsCycleOn (Finset.univ : Finset A) := by simpa using ha
  let r : ZMod n → A := fun x => (a ^ x.val) o
  have ri : Function.Injective r := by
    intro x y he
    have hh := (hac.pow_apply_eq_pow_apply (Finset.mem_univ o)).mp he
    have hh' : x.val % n = y.val % n := by simpa [Nat.ModEq, hcard] using hh
    rw [Nat.mod_eq_of_lt x.val_lt, Nat.mod_eq_of_lt y.val_lt] at hh'
    exact ZMod.val_injective n hh'
  have rs : Function.Surjective r := by
    intro y
    obtain ⟨k, hk, he⟩ := hac.exists_pow_eq (Finset.mem_univ o) (Finset.mem_univ y)
    have hk' : k < n := by simpa [hcard] using hk
    refine ⟨(k : ZMod n), ?_⟩
    change (a ^ (k : ZMod n).val) o = y
    rwa [ZMod.val_natCast_of_lt hk']
  have step (x) : r (x + 1) = a (r x) := by
    change (a ^ (x + 1).val) o = a ((a ^ x.val) o)
    rw [← Equiv.Perm.mul_apply, ← pow_succ']
    apply (hac.pow_apply_eq_pow_apply (Finset.mem_univ o)).mpr
    rw [Finset.card_univ, hcard]
    apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
    simp only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_one]
  let e := (Equiv.ofBijective r ⟨ri, rs⟩).symm
  refine ⟨e, ?_⟩
  intro x
  apply e.symm.injective
  change r (e (a x)) = r (e x + 1)
  rw [step]
  exact (e.symm_apply_apply (a x)).trans (congrArg a (e.symm_apply_apply x)).symm

/-- Without choosing coordinates: the common map of a nontrivial finite
sandwich candidate cannot be a single cycle covering the carrier. -/
theorem no_full_cycle {A : Type} [Fintype A] [Nontrivial A]
    (D : Magma A) (h : Identity D) (a : Equiv.Perm A)
    (hf : ∀ x y, F D x y = a x) : ¬ a.IsCycleOn Set.univ := by
  classical
  intro ha
  letI : Fact (1 < Fintype.card A) := ⟨Fintype.one_lt_card⟩
  letI : NeZero (Fintype.card A) := ⟨ne_of_gt (lt_trans Nat.zero_lt_one Fact.out)⟩
  obtain ⟨e, he⟩ := label_cycle (n := Fintype.card A) a ha rfl (Classical.arbitrary A)
  apply no_cyclic_labeling D h e
  intro x y
  rw [hf, he]

/-- If every power with a fixed point is the identity, a permutation on a
prime-size carrier is either the identity or one full cycle. -/
private theorem uniform_prime_cycle {A : Type} [Fintype A]
    (a : Equiv.Perm A) (hp : (Fintype.card A).Prime)
    (fixed : ∀ k x, (a ^ k) x = x → a ^ k = 1) :
    a = 1 ∨ a.IsCycleOn Set.univ := by
  classical
  by_cases he : a = 1
  · exact Or.inl he
  have nofix (x) : a x ≠ x := by
    intro hx
    exact he (by simpa using fixed 1 x (by simpa using hx))
  have support : a.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, nofix]
  have divides (c : Equiv.Perm A) (hc : c ∈ a.cycleFactorsFinset) :
      orderOf a ∣ c.support.card := by
    have cyc := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc
    obtain ⟨x, hx⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    exact orderOf_dvd_of_pow_eq_one (fixed _ x (cyc.pow_card_apply hx))
  have hd : orderOf a ∣ Fintype.card A := by
    rw [← Finset.card_univ, ← support, ← a.sum_cycleType]
    apply Multiset.dvd_sum
    intro k hk
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    exact divides c hc
  have ho : orderOf a = Fintype.card A :=
    (hp.eq_one_or_self_of_dvd _ hd).resolve_left (by simpa only [orderOf_eq_one_iff] using he)
  have hn : Nonempty A := Fintype.card_pos_iff.mp hp.pos
  letI := hn
  let o := Classical.arbitrary A
  let c := a.cycleOf o
  have hc : c ∈ a.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (by simpa using nofix o)
  have hpos : 0 < c.support.card :=
    Finset.card_pos.mpr (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  have hcard : c.support.card = Fintype.card A := by
    apply le_antisymm (Finset.card_le_univ _)
    exact ho ▸ Nat.le_of_dvd hpos (divides c hc)
  have hs : c.support = Finset.univ := Finset.eq_univ_of_card _ hcard
  exact Or.inr (by simpa only [hs, Finset.coe_univ] using
    Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc)

/-- The sandwich identity has the full converse at every prime order.
Its unrestricted composite-order converse remains open. -/
theorem basis_of_prime_card {A : Type} [Fintype A]
    (D : Magma A) (hp : (Fintype.card A).Prime) (h : Identity D) : Basis D := by
  classical
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp hp.one_lt
  obtain ⟨a, b, c, ha, _, _, hf, _, mb, ma, _, _, _, _, hu⟩ :=
    commuting_permutations D h
  let ae := Equiv.ofBijective a ha
  have hq := quasigroup D h
  have fixed (k : ℕ) (x : A) (hx : (ae ^ k) x = x) : ae ^ k = 1 := by
    have hh := CompositionCandidate.shifts_iterate_fixed D a b hq mb k x hx
    ext y
    exact hh.1 y
  have hae : ae = 1 := (uniform_prime_cycle ae hp fixed).resolve_right
    (no_full_cycle D h ae hf)
  have aid (x) : a x = x := Equiv.congr_fun hae x
  have bid (x) : b x = x := by
    apply (hq.1 x).1
    rw [mb, aid]
  have cid (x) : c x = x := by
    obtain ⟨y, hy⟩ := (hq.1 x).2 x
    calc
      c x = c (D.op x y) := congrArg c hy.symm
      _ = D.op x (a y) := (ma x y).symm
      _ = x := by rw [aid, hy]
  constructor
  · intro x
    simpa only [aid, bid, cid] using (hu x).symm
  · intro x y
    exact ((hf x y).trans (aid x)).symm

/-- A uniform theorem over all prime orders, using algebra and permutation
cycles rather than bounded searches. -/
theorem characterizes_prime_card {A : Type} [Fintype A]
    (D : Magma A) (hp : (Fintype.card A).Prime) :
    Identity D ↔ InImage Law917 .left D :=
  ⟨fun h => (characterizes_fin D).mp (basis_of_prime_card D hp h), of_image D⟩

end Parastrophes.Eq917Image.SandwichCandidate
