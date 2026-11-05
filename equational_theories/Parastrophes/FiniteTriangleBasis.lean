import equational_theories.Parastrophes.FiniteTriangleTrades
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Disjoint zero-sum triples encoding finite term calculations

For each ordered pair i≤j with code k=pair(i,j)+1<N, take the three vectors
`-e_i-e_j`, `e_k`, and `e_i+e_j-e_k` in (F5)^N. They sum to zero. The code
k exceeds both inputs. These triples are pairwise disjoint: their coefficient
patterns distinguish the three roles, and k is the unique negative coordinate
in the last vector. Characteristic five keeps 1,2,-1,-2 distinct.
-/
namespace Parastrophes.FiniteTriangleBasis

abbrev Vec (n : Nat) := Fin n → ZMod 5

def basis {n} (i : Fin n) : Vec n := fun k => if k = i then 1 else 0

theorem basis_value {n} (i k : Fin n) : basis i k = 0 ∨ basis i k = 1 := by
  by_cases h : k = i <;> simp [basis, h]

theorem basis_self {n} (i : Fin n) : basis i i = 1 := by simp [basis]

theorem basis_injective {n} : Function.Injective (@basis n) := by
  intro i j h
  by_contra hn
  have he := congrFun h i
  simp [basis, hn] at he
  exact (by decide : (1 : ZMod 5) ≠ 0) he

private theorem one_add_ne_zero (u : ZMod 5) (hu : u=0 ∨ u=1) : 1+u ≠ 0 := by
  rcases hu with rfl | rfl <;> decide

private theorem neg_pair_ne_one (u v : ZMod 5) (hu : u=0 ∨ u=1) (hv : v=0 ∨ v=1) :
    -u-v ≠ 1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

private theorem neg_pair_ne_one_add (u v w : ZMod 5)
    (hu : u=0 ∨ u=1) (hv : v=0 ∨ v=1) (hw : w=0 ∨ w=1) : -u-v ≠ 1+w := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hw with rfl | rfl <;> decide

private theorem pair_ne_neg_one (u v : ZMod 5) (hu : u=0 ∨ u=1) (hv : v=0 ∨ v=1) :
    u+v ≠ -1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

private theorem value_ne_neg_one (u : ZMod 5) (hu : u=0 ∨ u=1) : u ≠ -1 := by
  rcases hu with rfl | rfl <;> decide

theorem pair_basis_eq {n} (i j a b : Fin n) (he : basis i + basis j = basis a + basis b) :
    (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
  have hi : i=a ∨ i=b := by
    by_contra h
    push Not at h
    have hh := congrFun he i
    have hh' : 1 + basis j i = 0 := by simpa [basis, h.1, h.2] using hh
    exact one_add_ne_zero _ (basis_value j i) hh'
  rcases hi with rfl | rfl
  · exact Or.inl ⟨rfl, basis_injective (add_left_cancel he)⟩
  · rw [add_comm (basis a) (basis i)] at he
    exact Or.inr ⟨rfl, basis_injective (add_left_cancel he)⟩

def Block (n : Nat) := {p : Fin n × Fin n // p.1 ≤ p.2 ∧ Nat.pair p.1.val p.2.val + 1 < n}

def output {n} (p : Block n) : Fin n := ⟨Nat.pair p.val.1.val p.val.2.val + 1, p.property.2⟩

theorem left_lt_output {n} (p : Block n) : p.val.1 < output p := by
  have := Nat.left_le_pair p.val.1.val p.val.2.val
  change p.val.1.val < Nat.pair p.val.1.val p.val.2.val + 1
  omega

theorem right_lt_output {n} (p : Block n) : p.val.2 < output p := by
  have := Nat.right_le_pair p.val.1.val p.val.2.val
  change p.val.2.val < Nat.pair p.val.1.val p.val.2.val + 1
  omega

theorem output_injective {n} : Function.Injective (@output n) := by
  intro p q he
  have hv := congrArg Fin.val he
  change Nat.pair p.val.1.val p.val.2.val + 1 = Nat.pair q.val.1.val q.val.2.val + 1 at hv
  have hh := Nat.pair_eq_pair.mp (Nat.add_right_cancel hv)
  exact Subtype.ext (Prod.ext (Fin.ext hh.1) (Fin.ext hh.2))

def negative {n} (p : Block n) : Vec n := -basis p.val.1 - basis p.val.2
def mixed {n} (p : Block n) : Vec n := basis p.val.1 + basis p.val.2 - basis (output p)

theorem mixed_output {n} (p : Block n) : mixed p (output p) = -1 := by
  have hi := ne_of_gt (left_lt_output p)
  have hj := ne_of_gt (right_lt_output p)
  simp [mixed, basis, hi, hj]

theorem mixed_left {n} (p : Block n) : mixed p p.val.1 = 1 + basis p.val.2 p.val.1 := by
  have hi := ne_of_lt (left_lt_output p)
  simp [mixed, basis, hi]

theorem negative_injective {n} : Function.Injective (@negative n) := by
  intro p q he
  have hh : basis p.val.1 + basis p.val.2 = basis q.val.1 + basis q.val.2 := by
    have hn := congrArg Neg.neg he
    simpa [negative, sub_eq_add_neg, neg_add, add_comm] using hn
  rcases pair_basis_eq _ _ _ _ hh with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have hp := p.property.1
    have hq := q.property.1
    rw [← h.2, ← h.1] at hq
    have hij := le_antisymm hp hq
    exact Subtype.ext (Prod.ext (hij.trans h.2) (hij.symm.trans h.1))

theorem mixed_injective {n} : Function.Injective (@mixed n) := by
  intro p q he
  apply output_injective
  by_contra hn
  have hh := congrFun he (output p)
  rw [mixed_output] at hh
  have hq : mixed q (output p) = basis q.val.1 (output p) + basis q.val.2 (output p) := by
    simp [mixed, basis, hn]
  rw [hq] at hh
  exact pair_ne_neg_one _ _ (basis_value _ _) (basis_value _ _) hh.symm

theorem negative_ne_basis {n} (p q : Block n) : negative p ≠ basis (output q) := by
  intro he
  have hh := congrFun he (output q)
  rw [basis_self] at hh
  exact neg_pair_ne_one _ _ (basis_value _ _) (basis_value _ _) hh

theorem negative_ne_mixed {n} (p q : Block n) : negative p ≠ mixed q := by
  intro he
  have hh := congrFun he q.val.1
  rw [mixed_left] at hh
  exact neg_pair_ne_one_add _ _ _ (basis_value _ _) (basis_value _ _) (basis_value _ _) hh

theorem basis_ne_mixed {n} (p q : Block n) : basis (output p) ≠ mixed q := by
  intro he
  have hh := congrFun he (output q)
  rw [mixed_output] at hh
  exact value_ne_neg_one _ (basis_value _ _) hh

def triple {n} (p : Block n) (i : Fin 3) : Vec n :=
  if i=0 then negative p else if i=1 then basis (output p) else mixed p

theorem triple_sum {n} (p : Block n) : triple p 0 + triple p 1 + triple p 2 = 0 := by
  simp only [triple, Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq]
  unfold negative mixed
  abel

theorem triple_nonzero {n} (p : Block n) (i : Fin 3) : triple p i ≠ 0 := by
  fin_cases i
  · intro he
    have hh := congrFun he p.val.1
    have hh' : -(1 + basis p.val.2 p.val.1) = 0 := by simpa [triple, negative, basis, sub_eq_add_neg, add_comm] using hh
    exact one_add_ne_zero _ (basis_value _ _) (neg_eq_zero.mp hh')
  · intro he
    have hh := congrFun he (output p)
    have hh' : (1 : ZMod 5) = 0 := by simpa [triple, basis] using hh
    exact (by decide : (1 : ZMod 5) ≠ 0) hh'
  · intro he
    have hh := congrFun he (output p)
    have hh' : (-1 : ZMod 5) = 0 := by simpa [triple, mixed_output] using hh
    exact (by decide : (-1 : ZMod 5) ≠ 0) hh'

theorem triple_injective {n} : Function.Injective (fun z : Block n × Fin 3 => triple z.1 z.2) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ he
  fin_cases i <;> fin_cases j <;> simp only [triple, Fin.isValue] at he
  · exact Prod.ext (negative_injective he) rfl
  · exact (negative_ne_basis p q he).elim
  · exact (negative_ne_mixed p q he).elim
  · exact (negative_ne_basis q p he.symm).elim
  · exact Prod.ext (output_injective (basis_injective he)) rfl
  · exact (basis_ne_mixed p q he).elim
  · exact (negative_ne_mixed q p he.symm).elim
  · exact (basis_ne_mixed q p he.symm).elim
  · exact Prod.ext (mixed_injective he) rfl

end Parastrophes.FiniteTriangleBasis
