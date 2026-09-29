import equational_theories.Spectrum.PBD.OneGroup
import equational_theories.Spectrum.PBD.Gluing

/-! Localizing a transversal design gives the two unequal-group ingredients
used to transfer a complete fibre to every fibre of a PBD-closed set. -/
namespace Spectrum.PBD
open Classical PairDecomposition
namespace Transversal
variable {C : Set ℕ} {v q e : ℕ} (T : Transversal (Fin v) (Fin q))
variable (he : e ≤ 1) (hv : v ∈ C) (hq : q+e ∈ C)

abbrev FullPoints := Points (fun _ : Fin v => (Set.univ : Set (Fin q))) e

private theorem block_card (b : Fin v ⊕ (Fin q × Fin q)) :
    Nat.card (block T (fun _ => Set.univ) e b) = match b with | .inl _ => q+e | .inr _ => v := by
  cases b with
  | inl i =>
    rw [Nat.card_congr (groupEquiv T (fun _ => Set.univ) e i)]
    simp [Nat.add_comm]
  | inr p =>
    rw [Nat.card_congr (lineEquiv T (fun _ => Set.univ) e p)]
    simp

noncomputable def pairDesign : Complete C (FullPoints (v := v) (q := q) (e := e)) :=
  ofIndexed (block T (fun _ => Set.univ) e)
    (fun b => by rw [block_card]; cases b; exact hq; exact hv)
    (fun _ _ _ _ _ _ => trivial) (fun x y h _ => cover T (fun _ => Set.univ) e he x y h)

include T he hv hq in
/-- Delete an ordinary point from a TD after optionally adjoining one common
point to its groups. The resulting group sizes are `q+e-1` once and `v-1`
exactly q times. -/
theorem localized_oneGroup (hv2 : 2 ≤ v) (hqpos : 0 < q) :
    Nonempty (OneGroupDesign C (q+e-1) (v-1) q) := by
  let D := pairDesign T he hv hq
  let i : Fin v := ⟨0,by omega⟩
  let z : Fin q := ⟨0,hqpos⟩
  let o : FullPoints (v := v) (q := q) (e := e) := .inr ⟨i,⟨z,trivial⟩⟩
  let G : Set (FullPoints (v := v) (q := q) (e := e)) := block T (fun _ => Set.univ) e (.inl i)
  have hG : G ∈ D.blocks := by
    letI := Fintype.ofFinite (Fin v ⊕ (Fin q × Fin q))
    exact Finset.mem_image.mpr ⟨.inl i,Finset.mem_univ _,rfl⟩
  let g : LocalGroups D o := ⟨⟨G,hG⟩,rfl⟩
  have hsize : Nat.card (LocalGroup D o g) = q+e-1 := by
    rw [card_localGroup]
    have h := block_card T (e := e) (.inl i)
    exact congrArg (fun n => n-1) h
  have hothers (b : LocalGroups D o) (hb : b ≠ g) : Nat.card (LocalGroup D o b) = v-1 := by
    rw [card_localGroup]
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp b.val.property
    cases j with
    | inl j =>
      have ho : o ∈ block T (fun _ => Set.univ) e (.inl j) := hj ▸ b.property
      change i = j at ho
      subst j
      have hbg : b = g := Subtype.ext (Subtype.ext hj.symm)
      exact (hb hbg).elim
    | inr p =>
      have hc : Nat.card b.val.val = v := by
        rw [← hj]
        exact block_card T (.inr p)
      rw [hc]
  have hc : Nat.card (Σ b : LocalGroups D o, LocalGroup D o b) =
      (q+e-1)+q*(v-1) := by
    rw [card_localPoints]
    have hcP : Nat.card (FullPoints (v := v) (q := q) (e := e)) = e+v*q := by
      simp [FullPoints,Points,Nat.card_eq_fintype_card,Fintype.card_sigma]
    rw [hcP]
    have hq1 : q+e-1+1 = q+e := Nat.sub_add_cancel (by omega)
    have hv1 : v-1+1 = v := Nat.sub_add_cancel (by omega)
    have hP : e+v*q-1+1 = e+v*q := Nat.sub_add_cancel (by nlinarith)
    nlinarith only [hq1,hv1,hP]
  exact ⟨(D.localize o).toOneException g (by omega) hsize hothers hc⟩

end Transversal
end Spectrum.PBD
