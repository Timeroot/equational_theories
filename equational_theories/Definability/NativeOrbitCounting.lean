import DefOrbit.Counting
import equational_theories.Definability.NativeOrbit

/-! The compiled count equals the cardinality of the corresponding subtype. -/
namespace DefOrbit

theorem countAux_spec (f : Nat → Bool) (n acc : Nat) :
    countAux f n acc = acc + ∑ i ∈ Finset.range n, if f i then 1 else 0 := by
  induction n generalizing acc with
  | zero => simp [countAux]
  | succ n ih =>
    simp only [countAux, ih, Finset.sum_range_succ]
    omega

theorem countBelow_spec (f : Nat → Bool) (n : Nat) :
    countBelow f n = Fintype.card {i : Fin n // f i.val = true} := by
  rw [countBelow, countAux_spec]
  simp only [Nat.zero_add]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (Fin.sum_univ_eq_sum_range (fun i => if f i then 1 else 0) n).symm

theorem card_eq_countBelow {P : Type*} [Fintype P] {n : Nat} (e : P ≃ Fin n)
    (p : P → Prop) [DecidablePred p] (f : Nat → Bool)
    (h : ∀ x, p x ↔ f (e x).val = true) :
    Fintype.card {x // p x} = countBelow f n := by
  rw [countBelow_spec]
  exact Fintype.card_congr (e.subtypeEquiv h)

end DefOrbit

/-- info: 'DefOrbit.countBelow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DefOrbit.countBelow_spec

/-- info: 'DefOrbit.card_eq_countBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DefOrbit.card_eq_countBelow
