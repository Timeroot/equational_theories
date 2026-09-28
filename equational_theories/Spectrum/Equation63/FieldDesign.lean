import equational_theories.Spectrum.Equation63.IdempotentConstructions
import Mathlib.FieldTheory.Finite.GaloisField

/-! Transversal designs over finite fields, and products of transversal designs.
These provide additional idempotent E63 constructions without table certificates. -/
namespace Spectrum.E63
open Classical

/-- Any finite field with at least seven elements supplies a TD(8,q). Choose
seven distinct slopes; every nonzero slope difference is a unit. -/
noncomputable def fieldDesign (F : Type*) [Field F] [Fintype F]
    (h : 7 ≤ Fintype.card F) : Transversal Groups F (F × F) := by
  let e : Fin 7 ↪ F :=
    (Function.Embedding.nonempty_of_card_le (by simpa using h)).some
  exact cyclicDesign e (fun i j hij =>
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun he => hij (e.injective he))))

/-- Reindex the blocks of a transversal design. -/
noncomputable def Transversal.reindex {I Q T U : Type*}
    (D : Transversal I Q T) (e : U ≃ T) : Transversal I Q U where
  coord t i := D.coord (e t) i
  pair i j hij x y := by
    obtain ⟨t, ht, hu⟩ := D.pair i j hij x y
    refine ⟨e.symm t, by simpa using ht, ?_⟩
    intro u hh
    apply e.injective
    simpa using hu (e u) hh

/-- Take products coordinatewise, retaining the same set of groups. -/
noncomputable def Transversal.product {I Q R T U : Type*}
    (D : Transversal I Q T) (E : Transversal I R U) :
    Transversal I (Q × R) (T × U) where
  coord t i := (D.coord t.1 i, E.coord t.2 i)
  pair i j hij x y := by
    obtain ⟨t, ht, hut⟩ := D.pair i j hij x.1 y.1
    obtain ⟨u, hu, huu⟩ := E.pair i j hij x.2 y.2
    refine ⟨(t,u), ⟨Prod.ext ht.1 hu.1, Prod.ext ht.2 hu.2⟩, ?_⟩
    rintro ⟨v,w⟩ ⟨hv,hw⟩
    exact Prod.ext
      (hut v ⟨congrArg Prod.fst hv, congrArg Prod.fst hw⟩)
      (huu w ⟨congrArg Prod.snd hv, congrArg Prod.snd hw⟩)

/-- A TD(8,q), with its q² blocks indexed by a fixed finite type. -/
def HasTD (q : ℕ) : Prop := Nonempty (Transversal Groups (Fin q) (Fin (q*q)))

theorem field_td (F : Type*) [Field F] [Fintype F]
    (h : 7 ≤ Fintype.card F) : HasTD (Fintype.card F) := by
  let D := (fieldDesign F h).relabel (Fintype.equivFin F)
  exact ⟨D.reindex (Fintype.equivFinOfCardEq (by simp)).symm⟩

/-- Every prime power at least seven admits a TD(8,q). -/
theorem prime_power_td {p e : ℕ} (hp : p.Prime) (he : e ≠ 0)
    (h7 : 7 ≤ p^e) : HasTD (p^e) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p e) = p^e := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p e he]
  rw [← hc] at h7 ⊢
  exact field_td (GaloisField p e) h7

theorem HasTD.mul {q r : ℕ} (h : HasTD q) (k : HasTD r) : HasTD (q*r) := by
  obtain ⟨D⟩ := h
  obtain ⟨E⟩ := k
  let P : Transversal Groups (Fin (q*r)) (Fin (q*q) × Fin (r*r)) :=
    (D.product E).relabel (Fintype.equivFinOfCardEq (by simp))
  refine ⟨P.reindex (Fintype.equivFinOfCardEq ?_).symm⟩
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Use an available transversal design with idempotent group fillings. -/
theorem HasTD.idempotent_models {q r : ℕ} (D : HasTD q) (hr : r ≤ q)
    (g : Model (Fin q) true) (h : Model (Fin r) true) :
    Model (Fin (7*q+r)) true := by
  obtain ⟨D⟩ := D
  exact D.idempotent_models hr g h idem7 idem8

end Spectrum.E63
