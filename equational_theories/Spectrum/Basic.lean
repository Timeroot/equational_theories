import equational_theories.MagmaOp
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Factorization.Induction

/-!
Finite spectra of magma laws.

`HasModel n` allows the empty magma, as does the older `FullSpectrum.EqFullSpectrum`.
`spectrum` contains only positive cardinalities, following Bruno le Floch's spectrum note.
In particular every law has an empty model, but zero is not in its spectrum.
-/

open Law FreeMagma

namespace Magma

/-- Transport an operation along a bijection of its carrier. -/
@[implicit_reducible]
def transport {G H : Type*} (M : Magma G) (e : G ≃ H) : Magma H :=
  ⟨fun x y => e (M.op (e.symm x) (e.symm y))⟩

/-- The bijection used to transport a magma is an isomorphism. -/
def transportEquiv {G H : Type*} (M : Magma G) (e : G ≃ H) :
    @MagmaEquiv G H M (M.transport e) := by
  letI := M
  letI := M.transport e
  refine { toEquiv := e, map_op' := ?_ }
  intro x y
  change e (M.op x y) = e (M.op (e.symm (e x)) (e.symm (e y)))
  simp

/-- The coordinatewise product of two magmas. -/
@[implicit_reducible]
def product {G H : Type*} (M : Magma G) (N : Magma H) : Magma (G × H) :=
  ⟨fun x y => (M.op x.1 y.1, N.op x.2 y.2)⟩

end Magma

namespace Law.MagmaLaw

variable {α β : Type*} {L L₁ L₂ L₃ : MagmaLaw α} {n m : ℕ}

/-- Existence of a model on exactly `n` elements, including `n = 0`. -/
def HasModel (L : MagmaLaw α) (n : ℕ) : Prop :=
  ∃ M : Magma (Fin n), @satisfies _ (Fin n) M L

/-- The positive finite spectrum of a law. -/
def spectrum (L : MagmaLaw α) : Set ℕ := {n | 0 < n ∧ L.HasModel n}

/-- A law has full spectrum when it has models of every finite size. -/
def HasFullSpectrum (L : MagmaLaw α) : Prop := ∀ n, L.HasModel n

@[simp] theorem mem_spectrum : n ∈ L.spectrum ↔ 0 < n ∧ L.HasModel n := Iff.rfl

@[simp] theorem hasModel_zero (L : MagmaLaw α) : L.HasModel 0 :=
  ⟨⟨fun x _ => x⟩, fun φ => Fin.elim0 (φ L.lhs.first)⟩

@[simp] theorem hasModel_one (L : MagmaLaw α) : L.HasModel 1 :=
  ⟨⟨fun x _ => x⟩, fun _ => Subsingleton.elim _ _⟩

@[simp] theorem zero_not_mem_spectrum (L : MagmaLaw α) : 0 ∉ L.spectrum := by
  simp [spectrum]

@[simp] theorem one_mem_spectrum (L : MagmaLaw α) : 1 ∈ L.spectrum :=
  ⟨Nat.zero_lt_one, L.hasModel_one⟩

/-- A concrete model on any finite carrier yields a spectrum witness. -/
theorem hasModel_of_fintype {G : Type*} [Fintype G] (M : Magma G)
    (h : @satisfies _ G M L) : L.HasModel (Fintype.card G) := by
  classical
  letI := M
  letI := M.transport (Fintype.equivFin G)
  exact ⟨M.transport (Fintype.equivFin G),
    (satisfies_equiv (M.transportEquiv (Fintype.equivFin G))).mp h⟩

theorem hasModel_of_card {G : Type*} [Fintype G] (M : Magma G)
    (h : @satisfies _ G M L) (hc : Fintype.card G = n) : L.HasModel n :=
  hc ▸ hasModel_of_fintype M h

/-- Existence on `Fin n` is independent of the choice of a carrier of size `n`. -/
theorem HasModel.on_fintype (h : L.HasModel n) (G : Type*) [Fintype G]
    (hc : Fintype.card G = n) : ∃ M : Magma G, @satisfies _ G M L := by
  classical
  obtain ⟨M, hM⟩ := h
  let e : Fin n ≃ G := (Fintype.equivFinOfCardEq hc).symm
  letI := M
  letI := M.transport e
  exact ⟨M.transport e, (satisfies_equiv (M.transportEquiv e)).mp hM⟩

theorem satisfies_product {G H : Type*} (M : Magma G) (N : Magma H)
    (hM : @satisfies _ G M L) (hN : @satisfies _ H N L) :
    @satisfies _ (G × H) (M.product N) L := by
  intro φ
  have eval (t : FreeMagma α) :
      @evalInMagma _ _ (M.product N) φ t =
        (@evalInMagma _ _ M (fun a => (φ a).1) t,
         @evalInMagma _ _ N (fun a => (φ a).2) t) := by
    induction t with
    | Leaf a => rfl
    | Fork a b ha hb => simp only [evalInMagma, ha, hb]; rfl
  change @evalInMagma _ _ (M.product N) φ L.lhs =
    @evalInMagma _ _ (M.product N) φ L.rhs
  rw [eval, eval]
  exact Prod.ext (hM _) (hN _)

/-- Spectra are multiplicatively closed because equations hold coordinatewise. -/
theorem HasModel.mul (hn : L.HasModel n) (hm : L.HasModel m) : L.HasModel (n * m) := by
  obtain ⟨M, hM⟩ := hn
  obtain ⟨N, hN⟩ := hm
  exact hasModel_of_card (M.product N) (satisfies_product M N hM hN) (by simp)

theorem mul_mem_spectrum (hn : n ∈ L.spectrum) (hm : m ∈ L.spectrum) :
    n * m ∈ L.spectrum := ⟨Nat.mul_pos hn.1 hm.1, hn.2.mul hm.2⟩

theorem HasModel.pow (h : L.HasModel n) (k : ℕ) : L.HasModel (n ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => simpa [pow_succ] using ih.mul h

/-- For full spectrum, it suffices to construct a model at each prime order. -/
theorem hasFullSpectrum_iff_primes :
    L.HasFullSpectrum ↔ ∀ p : ℕ, p.Prime → L.HasModel p := by
  constructor
  · exact fun h p _ => h p
  · intro h n
    induction n using Nat.recOnMul with
    | zero => exact L.hasModel_zero
    | one => exact L.hasModel_one
    | prime p hp => exact h p hp
    | mul a b ha hb => exact ha.mul hb

theorem hasFullSpectrum_iff_spectrum :
    L.HasFullSpectrum ↔ L.spectrum = {n | 0 < n} := by
  constructor
  · intro h
    ext n
    exact ⟨fun hn => hn.1, fun hn => ⟨hn, h n⟩⟩
  · intro h n
    by_cases hn : n = 0
    · subst n; exact L.hasModel_zero
    · exact ((show n ∈ L.spectrum by rw [h]; exact Nat.pos_of_ne_zero hn)).2

/-- `L` is subspectral to `K` if every positive order of `L` is an order of `K`.
This has the same orientation as `L.implies K`. -/
def Subspectral (L : MagmaLaw α) (K : MagmaLaw β) : Prop := L.spectrum ⊆ K.spectrum

theorem subspectral_iff_hasModel {K : MagmaLaw β} :
    L.Subspectral K ↔ ∀ n, L.HasModel n → K.HasModel n := by
  constructor
  · intro h n hn
    by_cases hz : n = 0
    · subst n; exact K.hasModel_zero
    · exact (h ⟨Nat.pos_of_ne_zero hz, hn⟩).2
  · exact fun h _ hn => ⟨hn.1, h _ hn.2⟩

theorem Subspectral.refl (L : MagmaLaw α) : L.Subspectral L := fun _ h => h

theorem Subspectral.trans (h₁ : L₁.Subspectral L₂) (h₂ : L₂.Subspectral L₃) :
    L₁.Subspectral L₃ := fun _ h => h₂ (h₁ h)

theorem Subspectral.hasModel {K : MagmaLaw β} (h : L.Subspectral K) :
    L.HasModel n → K.HasModel n := (subspectral_iff_hasModel.mp h) n

theorem Subspectral.hasFullSpectrum {K : MagmaLaw β} (h : L.Subspectral K)
    (hL : L.HasFullSpectrum) : K.HasFullSpectrum := fun n => h.hasModel (hL n)

theorem Subspectral.not_hasModel {K : MagmaLaw β} (h : L.Subspectral K)
    (hn : ¬ K.HasModel n) : ¬ L.HasModel n := fun hL => hn (h.hasModel hL)

theorem subspectral_of_implies {K : MagmaLaw β} (h : L.implies K) : L.Subspectral K := by
  rw [subspectral_iff_hasModel]
  rintro n ⟨M, hM⟩
  exact ⟨M, @h (Fin n) M hM⟩

theorem spectrum_eq_of_iff {K : MagmaLaw β} (h : L.iff K) : L.spectrum = K.spectrum :=
  Set.Subset.antisymm (subspectral_of_implies h.mp) (subspectral_of_implies h.mpr)

theorem HasModel.dual (h : L.HasModel n) : L.dual.HasModel n := by
  obtain ⟨M, hM⟩ := h
  exact ⟨@opMagma (Fin n) M, @models.Op _ (Fin n) M _ _ hM⟩

@[simp] theorem hasModel_dual_iff : L.dual.HasModel n ↔ L.HasModel n :=
  ⟨fun h => L.law_dual_dual ▸ h.dual, HasModel.dual⟩

@[simp] theorem spectrum_dual (L : MagmaLaw α) : L.dual.spectrum = L.spectrum := by
  ext n
  simp

theorem spectrum_eq_of_isDual (h : L₁.IsDual L₂) : L₁.spectrum = L₂.spectrum :=
  (spectrum_eq_of_iff h).trans (spectrum_dual L₂)

end Law.MagmaLaw
