import equational_theories.Spectrum.PBD.Hole
import equational_theories.Spectrum.PBD.TransversalExistence

/-! Track marked blocks through truncated transversal constructions. -/
namespace Spectrum.PBD
open Classical PairDecomposition

/-- A complete design with one block reserved for a later hole. -/
def HasBlockDesign (K : Set ℕ) (n s : ℕ) : Prop :=
  ∃ D : Complete K (Fin n), D.ContainsBlock s

theorem HasBlockDesign.mem_closure {K : Set ℕ} {n s : ℕ} (h : HasBlockDesign K n s) :
    n ∈ designClosure K := ⟨h.choose⟩

theorem HasBlockDesign.hole {K : Set ℕ} {n s v : ℕ} (h : HasBlockDesign K n s)
    (he : n = s+v) : HasHole K s v :=
  h.choose_spec.hole (by simpa using he)

theorem hasBlockDesign_of_card {K : Set ℕ} {X : Type*} [Finite X]
    {D : Complete K X} {n s : ℕ} (h : D.ContainsBlock s) (hc : Nat.card X = n) :
    HasBlockDesign K n s := by
  let e : X ≃ Fin n := (Finite.card_eq.mp (by simpa using hc)).some
  exact ⟨D.transport e,h.transport e⟩

namespace MarkedTruncation
variable {K : Set ℕ} {k q r : ℕ} (T : Transversal (Option (Fin k)) (Fin q))
variable (hr : r ≤ q) (hk : k ∈ K) (hk' : k+1 ∈ K)
variable (F : Complete K (Fin q)) (P : Complete K (Fin r))

def retained : Option (Fin k) → Set (Fin q)
  | none => {x | x.val < r}
  | some _ => Set.univ

abbrev Points := Fin 0 ⊕ (Σ i : Option (Fin k), retained (r := r) (q := q) (k := k) i)

private def partEquiv : retained (r := r) (q := q) (k := k) none ≃ Fin r where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,lt_of_lt_of_le x.isLt hr⟩,x.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hr in
private theorem card_retained (i : Option (Fin k)) :
    Nat.card (retained (r := r) (q := q) (k := k) i) = match i with | none => r | some _ => q := by
  cases i with
  | none => simpa using Nat.card_congr (partEquiv hr)
  | some i => simp [retained]

include hk hk' in
private theorem sizes (p : Fin q × Fin q) :
    Nat.card {i | T.line p i ∈ retained (r := r) (q := q) (k := k) i} ∈ K := by
  by_cases hp : (T.line p none).val < r
  · have h : {i | T.line p i ∈ retained (r := r) (q := q) (k := k) i} = Set.univ := by
      ext i
      cases i <;> simp [retained,hp]
    simpa [h] using hk'
  · let e : {i | T.line p i ∈ retained (r := r) (q := q) (k := k) i} ≃ Fin k := {
      toFun := fun i => match i with
        | ⟨none,h⟩ => False.elim (hp h)
        | ⟨some i,_⟩ => i
      invFun := fun i => ⟨some i,trivial⟩
      left_inv := by rintro ⟨i,hi⟩; cases i with
                    | none => exact (hp hi).elim
                    | some i => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_fin]
    exact hk

noncomputable def gdd : GroupDivisible K (fun i => retained (r := r) (q := q) (k := k) i) :=
  T.truncated retained (sizes T hk hk')

noncomputable def group (i : Option (Fin k)) : Complete K (Fin 0 ⊕ retained (r := r) (q := q) (k := k) i) := by
  cases i with
  | none => exact P.ofCard (by simp only [Nat.card_sum,Nat.card_fin,zero_add,card_retained hr])
  | some i => exact F.ofCard (by simp only [Nat.card_sum,Nat.card_fin,zero_add,card_retained hr])

noncomputable def design : Complete K (Points (r := r) (q := q) (k := k)) :=
  (gdd T hk hk').adjoin 0 (by omega) (group hr F P)

include hr in
theorem card_points : Nat.card (Points (r := r) (q := q) (k := k)) = k*q+r := by
  rw [Nat.card_sum,Nat.card_fin,zero_add,Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_eq_nat_card,card_retained hr,Fintype.sum_option,Finset.sum_const,
    Finset.card_univ,Nat.card_fin,smul_eq_mul]
  omega

theorem contains_full (hkp : 0 < k) {s : ℕ} (hF : F.ContainsBlock s) :
    (design T hr hk hk' F P).ContainsBlock s := by
  apply GroupDivisible.adjoin_contains_group _ 0 _ _ (some ⟨0,hkp⟩)
  exact hF.transport _

theorem contains_part {s : ℕ} (hP : P.ContainsBlock s) :
    (design T hr hk hk' F P).ContainsBlock s := by
  apply GroupDivisible.adjoin_contains_group _ 0 _ _ none
  exact hP.transport _

theorem contains_short_line (hkp : 0 < k) (hrq : r < q) :
    (design T hr hk hk' F P).ContainsBlock k := by
  let i : Fin k := ⟨0,hkp⟩
  obtain ⟨p,hp⟩ := (T.pair (some i) none (by simp)).surjective
    (⟨0,by omega⟩,⟨r,hrq⟩)
  have hp' : (T.line p none).val = r := congrArg (fun z => z.2.val) hp
  let b : Set (Σ i, retained (r := r) (q := q) (k := k) i) :=
    {x | x.2.val = T.line p x.1}
  have hb : b ∈ (gdd T hk hk').blocks := by
    letI := Fintype.ofFinite (Fin q × Fin q)
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
  have h := (gdd T hk hk').adjoin_contains_line 0 (by omega) (group hr F P) ⟨b,hb⟩
  have hc : Nat.card b = k := by
    rw [Nat.card_congr (T.truncatedLineEquiv retained p)]
    let e : {j | T.line p j ∈ retained (r := r) (q := q) (k := k) j} ≃ Fin k := {
      toFun := fun j => match j with
        | ⟨none,h⟩ => False.elim (by change (T.line p none).val < r at h; omega)
        | ⟨some j,_⟩ => j
      invFun := fun j => ⟨some j,trivial⟩
      left_inv := by rintro ⟨j,hj⟩; cases j with
                    | none => change (T.line p none).val < r at hj; omega
                    | some j => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_fin]
  simpa only [hc] using h

end MarkedTruncation
end Spectrum.PBD
