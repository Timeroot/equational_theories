import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-! Explicit seven-group transversal designs, including a dense family of orders. -/
namespace Spectrum

structure TransversalSeven (Q : Type*) where
  line : Q × Q → Fin 7 → Q
  pair : ∀ i j, i ≠ j → Function.Bijective (fun p => (line p i, line p j))

namespace TransversalSeven

def field {F : Type*} [Field F] (c : Fin 7 ↪ F) : TransversalSeven F where
  line p i := p.1 + c i * p.2
  pair i j hij := by
    have hc : c j - c i ≠ 0 := sub_ne_zero.mpr (fun h => hij (c.injective h).symm)
    constructor
    · rintro ⟨a,b⟩ ⟨d,e⟩ he
      obtain ⟨h1,h2⟩ := Prod.mk.inj he
      dsimp at h1 h2
      have hb : b = e := by
        apply (mul_left_cancel₀ hc)
        linear_combination h2 - h1
      apply Prod.ext _ hb
      rw [hb] at h1
      exact add_right_cancel h1
    · rintro ⟨x,y⟩
      refine ⟨(x - c i * ((y-x)/(c j-c i)), (y-x)/(c j-c i)), ?_⟩
      apply Prod.ext
      · dsimp; ring
      · dsimp
        field_simp
        ring

def product {Q R : Type*} (D : TransversalSeven Q) (E : TransversalSeven R) :
    TransversalSeven (Q × R) where
  line p i := (D.line (p.1.1,p.2.1) i, E.line (p.1.2,p.2.2) i)
  pair i j hij := by
    constructor
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨e,f⟩,⟨g,h⟩⟩ he
      have hD := (D.pair i j hij).injective
        (congrArg (fun z => (z.1.1,z.2.1)) he)
      have hE := (E.pair i j hij).injective
        (congrArg (fun z => (z.1.2,z.2.2)) he)
      simp only [Prod.mk.injEq] at hD hE ⊢
      exact ⟨⟨hD.1,hE.1⟩,⟨hD.2,hE.2⟩⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
      obtain ⟨⟨e,f⟩,hD⟩ := (D.pair i j hij).surjective (a,c)
      obtain ⟨⟨g,h⟩,hE⟩ := (E.pair i j hij).surjective (b,d)
      refine ⟨((e,g),(f,h)), ?_⟩
      simp only [Prod.mk.injEq] at hD hE ⊢
      exact ⟨⟨hD.1,hE.1⟩,⟨hD.2,hE.2⟩⟩

theorem exists_field (F : Type*) [Field F] [Fintype F] (h : 7 ≤ Fintype.card F) :
    Nonempty (TransversalSeven F) := by
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 7) (β := F)
    (by simpa using h)
  exact ⟨field c⟩

def bases : Finset ℕ := {7,9,11,13,17,23,31,41}

private theorem exists_prime {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ (Q : Type) (f : Fintype Q), Nonempty (TransversalSeven Q) ∧
      @Fintype.card Q f = p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨ZMod p, inferInstance, exists_field (ZMod p) (by simpa using h7), ZMod.card p⟩

theorem exists_base {b : ℕ} (hb : b ∈ bases) :
    ∃ (Q : Type) (f : Fintype Q), Nonempty (TransversalSeven Q) ∧
      @Fintype.card Q f = b := by
  simp only [bases, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exists_prime (by decide) (by omega)
  · letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    letI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField 3 2) = 9 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by decide)]
      norm_num
    exact ⟨GaloisField 3 2, inferInstance, exists_field _ (by omega), hc⟩
  · exact exists_prime (by decide) (by omega)
  · exact exists_prime (by decide) (by omega)
  · exact exists_prime (by decide) (by omega)
  · exact exists_prime (by decide) (by omega)
  · exact exists_prime (by decide) (by omega)
  · exact exists_prime (by decide) (by omega)

theorem exists_size {b : ℕ} (hb : b ∈ bases) (k : ℕ) :
    ∃ (Q : Type) (f : Fintype Q), Nonempty (TransversalSeven Q) ∧
      @Fintype.card Q f = b * 7^k := by
  induction k with
  | zero => simpa using exists_base hb
  | succ k ih =>
    obtain ⟨Q,f,⟨D⟩,hc⟩ := ih
    letI := f
    obtain ⟨R,g,⟨E⟩,hd⟩ := exists_prime (p := 7) (by decide) (by omega)
    letI := g
    exact ⟨Q × R, inferInstance, ⟨D.product E⟩,
      by simp [Fintype.card_prod, hc, hd, pow_succ, Nat.mul_assoc]⟩

theorem core_size {n : ℕ} (hn : 35 ≤ n) :
    ∃ b ∈ bases, ∃ k : ℕ, 5 * (b * 7^k) ≤ n ∧ n < 7 * (b * 7^k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h287 : n < 287
    · by_cases h49 : n < 49
      · exact ⟨7, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      by_cases h63 : n < 63
      · exact ⟨9, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      by_cases h77 : n < 77
      · exact ⟨11, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      by_cases h91 : n < 91
      · exact ⟨13, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      by_cases h119 : n < 119
      · exact ⟨17, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      by_cases h161 : n < 161
      · exact ⟨23, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      by_cases h217 : n < 217
      · exact ⟨31, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
      exact ⟨41, by simp [bases], 0, by norm_num; omega, by norm_num; omega⟩
    · obtain ⟨b,hb,k,hlo,hhi⟩ := ih (n/7) (by omega) (by omega)
      refine ⟨b,hb,k+1,?_,?_⟩ <;> rw [pow_succ]
      · have : 7 * (5 * (b * 7^k)) ≤ n := by omega
        nlinarith
      · have : n < 7 * (7 * (b * 7^k)) := by omega
        nlinarith

theorem split_size {q t : ℕ} (hq : 7 ≤ q) (ht : t ≤ 2*q) :
    ∃ r s : ℕ, r ≤ q ∧ s ≤ q ∧ r ≠ 2 ∧ r ≠ 4 ∧ s ≠ 2 ∧ s ≠ 4 ∧ r+s=t := by
  by_cases htq : t ≤ q
  · by_cases hbad : t = 2 ∨ t = 4
    · exact ⟨1,t-1,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
    · exact ⟨t,0,htq,by omega,by omega,by omega,by omega,by omega,by omega⟩
  · by_cases hbad : t-q = 2 ∨ t-q = 4
    · exact ⟨q-1,t-q+1,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
    · exact ⟨q,t-q,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

end TransversalSeven
end Spectrum
