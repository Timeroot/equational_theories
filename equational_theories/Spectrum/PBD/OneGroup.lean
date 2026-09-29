import equational_theories.Spectrum.PBD.HoleGroups

/-! Relabel a group-divisible design with one exceptional group, optionally
inserting empty groups. -/
namespace Spectrum.PBD
open Classical PairDecomposition

abbrev oneGroupTypes (a b n : ℕ) (i : Option (Fin n)) : Type :=
  Fin (i.elim a (fun _ => b))

abbrev OneGroupDesign (K : Set ℕ) (a b n : ℕ) := GroupDivisible K (oneGroupTypes a b n)

namespace PairDecomposition.GroupDivisible
variable {K : Set ℕ} {I : Type*} {A : I → Type*} [Finite I] [∀ i, Finite (A i)]

private theorem card_other_groups {a b n : ℕ} (i : I) (hb : 0 < b)
    (hi : Nat.card (A i) = a) (hs : ∀ j, j ≠ i → Nat.card (A j) = b)
    (hc : Nat.card (Σ j, A j) = a+n*b) : Nat.card {j : I // j ≠ i} = n := by
  letI := Fintype.ofFinite I
  letI (j : I) : Fintype (A j) := Fintype.ofFinite _
  have hs' (j : {j : I // j ≠ i}) : Nat.card (A j.val) = b := hs j.val j.property
  have heq : Nat.card (Σ j, A j) = a + Nat.card {j : I // j ≠ i}*b := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    simp only [Fintype.card_eq_nat_card]
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => Nat.card (A j)) i,hi]
    simp only [hs',Finset.sum_const,Finset.card_univ,smul_eq_mul,
      Fintype.card_eq_nat_card]
  exact Nat.eq_of_mul_eq_mul_right hb (by omega)

private noncomputable def exceptionEquiv {a b n : ℕ} (i : I) (hb : 0 < b)
    (hi : Nat.card (A i) = a) (hs : ∀ j, j ≠ i → Nat.card (A j) = b)
    (hc : Nat.card (Σ j, A j) = a+n*b) :
    Σ e : I ≃ Option (Fin n), ∀ j, A j ≃ oneGroupTypes a b n (e j) := by
  have hJ := card_other_groups i hb hi hs hc
  let f : {j : I // j ≠ i} ≃ Fin n := (Finite.card_eq.mp (by simpa using hJ)).some
  let e := (Equiv.optionSubtypeNe i).symm.trans f.optionCongr
  refine ⟨e,fun j => (Finite.card_eq.mp ?_).some⟩
  by_cases hji : j = i
  · subst j
    simpa [e,oneGroupTypes] using hi
  · simpa [e,Equiv.optionSubtypeNe_symm_of_ne hji,oneGroupTypes] using hs j hji

noncomputable def toOneException {a b n : ℕ} (D : GroupDivisible K A) (i : I) (hb : 0 < b)
    (hi : Nat.card (A i) = a) (hs : ∀ j, j ≠ i → Nat.card (A j) = b)
    (hc : Nat.card (Σ j, A j) = a+n*b) : OneGroupDesign K a b n :=
  D.relabel (exceptionEquiv i hb hi hs hc).1 (exceptionEquiv i hb hi hs hc).2

noncomputable def fromOneException {a b n : ℕ} (D : OneGroupDesign K a b n) (i : I) (hb : 0 < b)
    (hi : Nat.card (A i) = a) (hs : ∀ j, j ≠ i → Nat.card (A j) = b)
    (hc : Nat.card (Σ j, A j) = a+n*b) : GroupDivisible K A := by
  let E := exceptionEquiv i hb hi hs hc
  let e : (Σ j, A j) ≃ (Σ j, oneGroupTypes a b n j) := Equiv.sigmaCongr E.1 E.2
  apply (D.transport e.symm).congr
  intro x y _
  change E.1 x.1 ≠ E.1 y.1 ↔ x.1 ≠ y.1
  exact E.1.injective.ne_iff

def supportedEquiv : (Σ i : {i // Nonempty (A i)}, A i.val) ≃ (Σ i, A i) where
  toFun x := ⟨x.1.val,x.2⟩
  invFun x := ⟨⟨x.1,⟨x.2⟩⟩,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Zero-size groups can be inserted without affecting any pairs. -/
noncomputable def fromOneExceptionWithZeros {a b n : ℕ} (D : OneGroupDesign K a b n)
    (i : I) (ha : 0 < a) (hb : 0 < b)
    (hi : Nat.card (A i) = a) (hs : ∀ j, j ≠ i → Nat.card (A j) = 0 ∨ Nat.card (A j) = b)
    (hc : Nat.card (Σ j, A j) = a+n*b) : GroupDivisible K A := by
  let J := {i // Nonempty (A i)}
  have hiN : Nonempty (A i) := Finite.card_pos_iff.mp (by omega)
  let i' : J := ⟨i,hiN⟩
  have hs' (j : J) (hj : j ≠ i') : Nat.card (A j.val) = b := by
    have hji : j.val ≠ i := fun h => hj (Subtype.ext h)
    have hp : 0 < Nat.card (A j.val) := @Finite.card_pos _ _ j.property
    exact (hs j.val hji).resolve_left (by omega)
  have hc' : Nat.card (Σ j : J, A j.val) = a+n*b :=
    (Nat.card_congr (supportedEquiv (A := A))).trans hc
  let E : GroupDivisible K (fun j : J => A j.val) := D.fromOneException i' hb hi hs' hc'
  apply (E.transport (supportedEquiv (A := A))).congr
  intro x y _
  change (⟨x.1,⟨x.2⟩⟩ : J) ≠ ⟨y.1,⟨y.2⟩⟩ ↔ x.1 ≠ y.1
  exact Subtype.val_injective.ne_iff.symm

end PairDecomposition.GroupDivisible
end Spectrum.PBD
