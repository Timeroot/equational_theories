import equational_theories.Spectrum.BookendCardinality
import equational_theories.Spectrum.Shapes
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Bool

/-! # The spectrum of the bookend law E167

Decompose ordered pairs into the diagonal and two orientations of each
unordered pair. Swapping coordinates has a square root precisely when the
number of unordered pairs is even.
-/

namespace Spectrum.Bookend

abbrev Asc (G : Type*) [LinearOrder G] := {p : G × G // p.1 < p.2}

def encode {G : Type*} [LinearOrder G] (p : G × G) : G ⊕ (Asc G × Bool) :=
  if he : p.1 = p.2 then .inl p.1
  else if hl : p.1 < p.2 then .inr (⟨p, hl⟩, false)
  else .inr (⟨(p.2, p.1), lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)⟩, true)

def decode {G : Type*} [LinearOrder G] : G ⊕ (Asc G × Bool) → G × G
  | .inl x => (x, x)
  | .inr (p, false) => p.val
  | .inr (p, true) => p.val.swap

def pairEquiv (G : Type*) [LinearOrder G] : (G × G) ≃ G ⊕ (Asc G × Bool) where
  toFun := encode
  invFun := decode
  left_inv := by
    rintro ⟨x, y⟩
    simp only [encode]
    split_ifs with he hl
    · simp [decode, he]
    · rfl
    · rfl
  right_inv := by
    rintro (x | ⟨⟨⟨x,y⟩, h⟩, b⟩)
    · simp [decode, encode]
    · cases b <;> simp [decode, encode, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h]

theorem encode_swap {G : Type*} [LinearOrder G] (p : G × G) :
    encode p.swap = Sum.map id (fun q => (q.1, !q.2)) (encode p) := by
  obtain ⟨q, rfl⟩ := (pairEquiv G).symm.surjective p
  rcases q with x | ⟨⟨⟨x,y⟩, h⟩, b⟩
  · simp [pairEquiv, decode, encode]
  · cases b <;> simp [pairEquiv, decode, encode, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h]

theorem card_pairs (G : Type*) [LinearOrder G] [Fintype G] :
    Fintype.card G * Fintype.card G = Fintype.card G + 2 * Fintype.card (Asc G) := by
  simpa [Fintype.card_prod, Fintype.card_sum, Nat.mul_comm] using Fintype.card_congr (pairEquiv G)

theorem swap_sign (G : Type*) [LinearOrder G] [Fintype G] :
    Equiv.Perm.sign (Equiv.prodComm G G) = (-1 : ℤˣ) ^ Fintype.card (Asc G) := by
  have hs := Equiv.Perm.sign_eq_sign_of_equiv (Equiv.prodComm G G)
    (Equiv.sumCongr (Equiv.refl G) (Equiv.prodCongrRight fun _ : Asc G => Equiv.boolNot))
    (pairEquiv G) (fun p => encode_swap p)
  rw [hs, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_prodCongrRight]
  have hb : Equiv.Perm.sign Equiv.boolNot = -1 := by decide
  simp [hb]
  congr 1

theorem even_pairs {G : Type*} [LinearOrder G] [Fintype G] [Magma G]
    (h : Equation167 G) : Even (Fintype.card (Asc G)) := by
  have hs := swap_even h
  rw [swap_sign] at hs
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hs

theorem residue_of_even {n u : ℕ} (hc : n * n = n + 2 * u) (hu : Even u) :
    n % 4 = 0 ∨ n % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hu
  have hm' : (n % 4 * (n % 4)) % 4 = n % 4 := by
    rw [← Nat.mul_mod, hc]
    omega
  have hn := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases n % 4 <;> simp_all

/-- Rotate the two paired unordered pairs and their two orientations in a four-cycle. -/
def turn {U K : Type*} (e : U ≃ K × Bool) (q : U × Bool) : U × Bool :=
  (e.symm ((e q.1).1, !(e q.1).2), xor q.2 (e q.1).2)

theorem turn_twice {U K : Type*} (e : U ≃ K × Bool) (q : U × Bool) :
    turn e (turn e q) = (q.1, !q.2) := by
  rcases q with ⟨u,b⟩
  obtain ⟨⟨i,c⟩,rfl⟩ := e.symm.surjective u
  cases c <;> cases b <;> simp [turn]

def root {G K : Type*} [LinearOrder G] (e : Asc G ≃ K × Bool) (p : G × G) : G × G :=
  (pairEquiv G).symm (Sum.map id (turn e) (pairEquiv G p))

theorem root_twice {G K : Type*} [LinearOrder G] (e : Asc G ≃ K × Bool) (p : G × G) :
    root e (root e p) = p.swap := by
  apply (pairEquiv G).injective
  simp only [root, Equiv.apply_symm_apply]
  rw [show pairEquiv G p.swap = Sum.map id (fun q => (q.1, !q.2)) (pairEquiv G p)
    from encode_swap p]
  cases pairEquiv G p <;> simp [turn_twice]

/-- A square root of coordinate swap gives a bookend magma on the same carrier. -/
@[implicit_reducible] def magmaOfRoot {G : Type*} (T : G × G → G × G) : Magma G :=
  ⟨fun x y => (T (x,y)).1⟩

theorem law_of_root {G : Type*} (T : G × G → G × G)
    (hT : ∀ p, T (T p) = p.swap) : @Equation167 G (magmaOfRoot T) := by
  have hc (p : G × G) : T p.swap = (T p).swap := by
    rw [← hT p, hT]
  intro x y
  change x = (T ((T (y,x)).1, (T (x,y)).1)).1
  have hxy : (T (x,y)).1 = (T (y,x)).2 := congrArg Prod.fst (hc (y,x))
  rw [hxy]
  change x = (T (T (y,x))).1
  rw [hT]
  rfl

theorem even_of_residue {n u : ℕ} (hc : n * n = n + 2 * u)
    (hn : n % 4 = 0 ∨ n % 4 = 1) : Even u := by
  rw [Nat.even_iff]
  have hm := congrArg (· % 4) hc
  change (n * n) % 4 = (n + 2 * u) % 4 at hm
  rw [Nat.mul_mod n n 4] at hm
  rcases hn with hn | hn <;> rw [hn] at hm <;> norm_num at hm <;> omega

theorem model_of_even (G : Type*) [LinearOrder G] [Fintype G]
    (hu : Even (Fintype.card (Asc G))) : ∃ M : Magma G, @Equation167 G M := by
  classical
  obtain ⟨k,hk⟩ := hu
  let e : Asc G ≃ Fin k × Bool := Fintype.equivOfCardEq (by simp [hk, Nat.mul_two])
  exact ⟨magmaOfRoot (root e), law_of_root _ (root_twice e)⟩

end Spectrum.Bookend

namespace Spectrum

theorem orders_167 {n : ℕ} (h : n ∈ Law167.spectrum) : n ∈ residues 4 {0,1} ∅ := by
  obtain ⟨hn,M,hM⟩ := h
  letI := M
  have hp := Bookend.even_pairs ((@Law167.models_iff _ M).mp hM)
  have hc := Bookend.card_pairs (Fin n)
  simp only [Fintype.card_fin] at hc
  exact ⟨hn, by simpa using Bookend.residue_of_even hc hp, by simp⟩

theorem models_167 {n : ℕ} (h : n ∈ residues 4 {0,1} ∅) : Law167.HasModel n := by
  have hc := Bookend.card_pairs (Fin n)
  simp only [Fintype.card_fin] at hc
  have hn : n % 4 = 0 ∨ n % 4 = 1 := by simpa using h.2.1
  obtain ⟨M,hM⟩ := Bookend.model_of_even (Fin n) (Bookend.even_of_residue hc hn)
  exact ⟨M, (@Law167.models_iff _ M).mpr hM⟩

/-- The complete positive finite spectrum of the bookend law. -/
theorem exact_167 : Law167.spectrum = residues 4 {0,1} ∅ :=
  Set.Subset.antisymm (fun _ h => orders_167 h) (fun _ h => ⟨h.1, models_167 h⟩)

end Spectrum
