import equational_theories.Spectrum.PBD.Model
import Mathlib.FieldTheory.Finite.GaloisField

/-! Transversal designs from finite fields, cyclic rings, and products. -/
namespace Spectrum.PBD
open Classical

structure Transversal (I Q : Type*) where
  line : Q × Q → I → Q
  pair : ∀ i j, i ≠ j → Function.Bijective (fun p => (line p i, line p j))

namespace Transversal
variable {I J Q R : Type*}

def reindex (D : Transversal I Q) (e : J ≃ I) : Transversal J Q where
  line p i := D.line p (e i)
  pair i j h := D.pair (e i) (e j) (fun he => h (e.injective he))

def relabel (D : Transversal I Q) (e : Q ≃ R) : Transversal I R where
  line p i := e (D.line (e.symm p.1, e.symm p.2) i)
  pair i j h := by
    constructor
    · intro p r he
      have he' := (D.pair i j h).injective
        (Prod.ext (e.injective (congrArg Prod.fst he))
          (e.injective (congrArg Prod.snd he)))
      exact Prod.ext (e.symm.injective (congrArg Prod.fst he'))
        (e.symm.injective (congrArg Prod.snd he'))
    · intro p
      obtain ⟨r,hr⟩ := (D.pair i j h).surjective (e.symm p.1,e.symm p.2)
      exact ⟨(e r.1,e r.2), by simpa using congrArg (fun t : Q × Q => (e t.1,e t.2)) hr⟩

def product (D : Transversal I Q) (E : Transversal I R) : Transversal I (Q × R) where
  line p i := (D.line (p.1.1,p.2.1) i, E.line (p.1.2,p.2.2) i)
  pair i j hij := by
    constructor
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨e,f⟩,⟨g,h⟩⟩ he
      have hD := (D.pair i j hij).injective (congrArg (fun z => (z.1.1,z.2.1)) he)
      have hE := (E.pair i j hij).injective (congrArg (fun z => (z.1.2,z.2.2)) he)
      simp only [Prod.mk.injEq] at hD hE ⊢
      exact ⟨⟨hD.1,hE.1⟩,⟨hD.2,hE.2⟩⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
      obtain ⟨⟨e,f⟩,hD⟩ := (D.pair i j hij).surjective (a,c)
      obtain ⟨⟨g,h⟩,hE⟩ := (E.pair i j hij).surjective (b,d)
      refine ⟨((e,g),(f,h)), ?_⟩
      simp only [Prod.mk.injEq] at hD hE ⊢
      exact ⟨⟨hD.1,hE.1⟩,⟨hD.2,hE.2⟩⟩

section Ring
variable [CommRing R]

def coord (c : I → R) (p : R × R) : Option I → R
  | none => p.2
  | some i => p.1 + c i * p.2

theorem coord_injective (c : I → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (i j : Option I) (hne : i ≠ j) :
    Function.Injective (fun p => (coord c p i, coord c p j)) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  cases i with
  | none =>
    cases j with
    | none => exact (hne rfl).elim
    | some j =>
      change b = b' at h1
      change a + c j * b = a' + c j * b' at h2
      exact Prod.ext (by rw [h1] at h2; exact add_right_cancel h2) h1
  | some i =>
    cases j with
    | none =>
      change b = b' at h2
      change a + c i * b = a' + c i * b' at h1
      exact Prod.ext (by rw [h2] at h1; exact add_right_cancel h1) h2
    | some j =>
      change a + c i * b = a' + c i * b' at h1
      change a + c j * b = a' + c j * b' at h2
      obtain ⟨u,heq⟩ := hu i j (fun h => hne (congrArg some h))
      have hz : (c i - c j) * (b-b') = 0 := by linear_combination h1 - h2
      rw [← heq] at hz
      have hb : b = b' := sub_eq_zero.mp ((Units.mul_right_eq_zero u).mp hz)
      exact Prod.ext (by rw [hb] at h1; exact add_right_cancel h1) hb

noncomputable def ring [Finite R] (c : I → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j)) : Transversal (Option I) R where
  line := coord c
  pair i j h := ⟨coord_injective c hu i j h,
    Finite.injective_iff_surjective.mp (coord_injective c hu i j h)⟩
end Ring

noncomputable def field {F : Type*} [Field F] [Finite F] (c : I ↪ F) :
    Transversal (Option I) F :=
  ring c (fun _ _ hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hij (c.injective h))))

def restrictIndex (D : Transversal I Q) (f : J ↪ I) : Transversal J Q where
  line p i := D.line p (f i)
  pair i j hij := D.pair (f i) (f j) (fun h => hij (f.injective h))

end Transversal

/-- A transversal design with k groups of q points each. -/
def HasTD (k q : ℕ) := Nonempty (Transversal (Fin k) (Fin q))

namespace HasTD

theorem field (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (hk : k ≤ Fintype.card F + 1) : HasTD k (Fintype.card F) := by
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le (α := Fin k) (β := Option F)
    (by simpa using hk)
  exact ⟨((Transversal.field (Function.Embedding.refl F)).restrictIndex c).relabel
    (Fintype.equivFin F)⟩

theorem primePower {p e k : ℕ} (hp : p.Prime) (he : e ≠ 0) (hk : k ≤ p^e+1) :
    HasTD k (p^e) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p e) = p^e := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p e he]
  simpa only [hc] using (field (GaloisField p e) (k := k) (by simpa only [hc] using hk))

theorem mul {k q r : ℕ} (h : HasTD k q) (g : HasTD k r) : HasTD k (q*r) := by
  obtain ⟨D⟩ := h
  obtain ⟨E⟩ := g
  exact ⟨(D.product E).relabel (Fintype.equivFinOfCardEq (by simp))⟩

end HasTD
end Spectrum.PBD
