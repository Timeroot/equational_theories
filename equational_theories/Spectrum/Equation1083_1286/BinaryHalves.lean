import equational_theories.Spectrum.Equation1083_1286.BinarySeed
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Card

/-! Six full groups and three correlated half-groups in a field transversal
 design give a pointed E1286 model of order 240. The three binary images of
 x, y, x+y have either one or three zeros, so every transversal block has
 size 7 or 9. Only a four-case calculation in ZMod 2 is enumerated. -/
namespace Spectrum.E1083E1286.BinaryHalves
open Classical Law Law.MagmaLaw

private theorem slopes {F : Type*} [Field F] [Fintype F] (h : 8 ≤ Fintype.card F) :
    ∃ c : Fin 8 ↪ F, c 0 = 0 ∧ c 1 = 1 := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 8) (β := F) (by simpa using h)
  have hd : e 1 - e 0 ≠ 0 := sub_ne_zero.mpr (fun he => (by decide : (1 : Fin 8) ≠ 0) (e.injective he))
  refine ⟨⟨fun i => (e i-e 0)/(e 1-e 0), ?_⟩, ?_, ?_⟩
  · intro i j he
    exact e.injective (sub_left_injective ((div_left_inj' hd).mp he))
  · simp
  · exact div_self hd

private def keep {F : Type*} (φ : F → ZMod 2) : Option (Fin 8) → F → Prop
  | none, x => φ x = 0
  | some i, x => if i.val < 2 then φ x = 0 else True

private noncomputable def design {F : Type*} [Field F] [Fintype F] (c : Fin 8 ↪ F) :
    E63.Transversal (Option (Fin 8)) F (F × F) where
  coord := (PBD.Transversal.field c).line
  pair i j hij x y := by
    obtain ⟨p,hp⟩ := ((PBD.Transversal.field c).pair i j hij).surjective (x,y)
    refine ⟨p,⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩,?_⟩
    intro u hu
    exact ((PBD.Transversal.field c).pair i j hij).injective ((Prod.ext hu.1 hu.2).trans hp.symm)

private theorem block_card {F : Type*} [Field F] [Fintype F]
    (c : Fin 8 ↪ F) (h0 : c 0 = 0) (h1 : c 1 = 1)
    (φ : F →+ ZMod 2) (t : F × F) :
    Fintype.card {i // keep φ i ((design c).coord t i)} = 7 ∨
    Fintype.card {i // keep φ i ((design c).coord t i)} = 9 := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option, Fin.sum_univ_succ]
  simp [keep, design, PBD.Transversal.field, PBD.Transversal.ring,
    PBD.Transversal.coord, h0, h1, map_add]
  have arithmetic : ∀ a b : ZMod 2,
      (if b = 0 then 1 else 0) + ((if a = 0 then 1 else 0) + ((if a+b = 0 then 1 else 0) + 6)) = 7 ∨
      (if b = 0 then 1 else 0) + ((if a = 0 then 1 else 0) + ((if a+b = 0 then 1 else 0) + 6)) = 9 := by decide
  have ar := arithmetic (φ t.1) (φ t.2)
  split_ifs at ar ⊢ <;> omega

private theorem half_card {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (φ : F →ₗ[ZMod 2] ZMod 2) (hφ : φ 1 = 1) (hF : Fintype.card F = 32) :
    Fintype.card {x // φ x = 0} = 16 := by
  have hs : Function.Surjective φ := by
    intro z
    refine ⟨z • (1 : F), ?_⟩
    simp [hφ]
  have hc := Submodule.card_eq_card_quotient_mul_card φ.ker
  have hq : Nat.card (F ⧸ φ.ker) = 2 := by
    rw [Nat.card_congr (φ.quotKerEquivOfSurjective hs).toEquiv]
    simp
  rw [hq, Nat.card_eq_fintype_card, hF] at hc
  have hk : Nat.card φ.ker = Fintype.card {x // φ x = 0} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.refl _)
  rw [hk] at hc
  omega

private theorem pointed_field {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (hF : Fintype.card F = 32) : Nonempty (Pointed true (Fin 240)) := by
  obtain ⟨c,h0,h1⟩ := slopes (by omega : 8 ≤ Fintype.card F)
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : F) ≠ 0)
  have hc := half_card φ hφ hF
  let T := design c
  let K := keep φ
  have hK (i) : Fintype.card {x // K i x} = match i with
      | none => 16 | some j => if j.val < 2 then 16 else 32 := by
    rw [← Nat.card_eq_fintype_card]
    cases i with
    | none =>
      change Nat.card {x // φ x = 0} = 16
      rwa [Nat.card_eq_fintype_card]
    | some j =>
      by_cases hj : j.val < 2
      · simp only [K, keep, if_pos hj]
        rwa [Nat.card_eq_fintype_card]
      · simp [K, keep, hj, Nat.card_eq_fintype_card, hF]
  let A := Σ i, {x // K i x}
  let D := T.restrict K
  have hg : ∀ i, Nonempty (Pointed true {x // K i x}) := by
    intro i
    cases i with
    | none =>
      exact ⟨(quarticPointed 2 true).transport (Fintype.equivOfCardEq (by simpa using (hK none).symm))⟩
    | some i =>
      by_cases hi : i.val < 2
      · exact ⟨(quarticPointed 2 true).transport (Fintype.equivOfCardEq (by simpa [hi] using (hK (some i)).symm))⟩
      · exact ⟨BinarySeed.pointed32.transport (Fintype.equivOfCardEq (by simpa [hi] using (hK (some i)).symm))⟩
  let G (i) := (hg i).some.transport (T.groupEquiv K i).symm
  have hb : ∀ t, Model true (D.block t) true := by
    intro t
    apply Model.relabel (e := (T.blockEquiv K t).symm)
    rcases block_card c h0 h1 φ.toAddMonoidHom t with h | h
    · exact idem7.of_card h
    · exact idem9.of_card h
  choose b hb hi using hb
  let p := (G none).point
  let P : Pointed true A := {
    op := D.op (fun i => (G i).op) b
    lawful := design_lawful D _ _ (fun i => (G i).lawful) hb (fun j => hi j rfl)
    point := p.val
    fixed := (D.op_group _ _ none p p).trans (congrArg Subtype.val (G none).fixed) }
  have hA : Fintype.card A = 240 := by
    change Fintype.card (Σ i, {x // K i x}) = 240
    simp only [Fintype.card_sigma, hK, Fintype.sum_option, Fin.sum_univ_succ]
    decide
  exact ⟨P.transport (Fintype.equivFinOfCardEq hA)⟩

theorem pointed240 : Nonempty (Pointed true (Fin 240)) := by
  letI : Fintype (GaloisField 2 5) := Fintype.ofFinite _
  apply pointed_field (F := GaloisField 2 5)
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 5 (by decide)]
  decide

theorem model240 : Law1286.HasModel 240 := pointed240.some.hasModel (by simp)

spectrum_assert model240 complete

end Spectrum.E1083E1286.BinaryHalves

/-- info: 'Spectrum.E1083E1286.BinaryHalves.model240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.E1083E1286.BinaryHalves.model240
