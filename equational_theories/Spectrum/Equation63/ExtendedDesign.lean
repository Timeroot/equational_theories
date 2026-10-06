import equational_theories.Spectrum.Equation63.FieldDesign

/-! More flexible transversal-design constructions: arbitrary group count and
one common point adjoined to all groups. -/
namespace Spectrum.E63
open Classical

variable {R : Type*} [CommRing R] [Finite R]

def wideLineCoord {k : ℕ} (c : Fin k → R) (t : R × R) : Option (Fin k) → R
  | none => t.2
  | some i => t.1 + c i * t.2

omit [Finite R] in
theorem wide_line_pair_injective {k : ℕ} (c : Fin k → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (i j : Option (Fin k)) (hne : i ≠ j) :
    Function.Injective (fun t => (wideLineCoord c t i, wideLineCoord c t j)) := by
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
      obtain ⟨u, heq⟩ := hu i j (fun h => hne (congrArg some h))
      have hz : (c i - c j) * (b-b') = 0 := by linear_combination h1 - h2
      rw [← heq] at hz
      have hb : b = b' := sub_eq_zero.mp ((Units.mul_right_eq_zero u).mp hz)
      exact Prod.ext (by rw [hb] at h1; exact add_right_cancel h1) hb

noncomputable def wideCyclicDesign {k : ℕ} (c : Fin k → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j)) : Transversal (Option (Fin k)) R (R × R) where
  coord := wideLineCoord c
  pair i j hne x y := by
    have hi := wide_line_pair_injective c hu i j hne
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hi) (x,y)
    refine ⟨t, ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩, ?_⟩
    intro u hu
    exact hi ((Prod.ext hu.1 hu.2).trans ht.symm)


noncomputable def wideFieldDesign {k : ℕ} (F : Type*) [Field F] [Fintype F]
    (h : k ≤ Fintype.card F) : Transversal (Option (Fin k)) F (F × F) := by
  let e : Fin k ↪ F :=
    (Function.Embedding.nonempty_of_card_le (by simpa using h)).some
  exact wideCyclicDesign e (fun i j hij =>
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun he => hij (e.injective he))))

def wideSelect {Q : Type*} {k : ℕ} (s : Set Q) : Option (Fin k) → Q → Prop
  | none, x => x ∈ s
  | some _, _ => True

theorem Transversal.wide_idempotent {k : ℕ} {Q T : Type*} [Fintype Q] [Fintype T]
    (D : Transversal (Option (Fin k)) Q T) (s : Set Q) (g : Model Q true) (r : Model s true)
    (h7 : Model (Fin k) true) (h8 : Model (Fin (k+1)) true) :
    Model (Fin (k * Fintype.card Q + Fintype.card s)) true := by
  let keep := wideSelect (k := k) s
  let A := Σ i, {x // keep i x}
  have hg : ∀ i, Model {x // (D.restrict keep).group x = i} true := by
    intro i
    apply Model.relabel (e := (D.groupEquiv keep i).symm)
    cases i with
    | none => exact r
    | some i => exact g.relabel (Equiv.Set.univ Q).symm
  have hb : ∀ t, Model ((D.restrict keep).block t) true := by
    intro t
    apply Model.relabel (e := (D.blockEquiv keep t).symm)
    by_cases he : D.coord t none ∈ s
    · apply h8.of_card
      have hh : (fun i => keep i (D.coord t i)) = fun _ => True := by
        funext i
        cases i <;> simp [keep, wideSelect, he]
      simp [hh, Fintype.card_option]
    · apply h7.of_card
      let e : {i // keep i (D.coord t i)} ≃ Fin k := {
        toFun := fun i => match i with
          | ⟨some j, _⟩ => j
          | ⟨none, h⟩ => False.elim (he h)
        invFun := fun j => ⟨some j, trivial⟩
        left_inv := by rintro ⟨(_ | j), h⟩; exact (he h).elim; rfl
        right_inv := fun _ => rfl }
      simpa using Fintype.card_congr e
  have hm : Model A true := (D.restrict keep).idempotent_model hg hb
  apply hm.relabel
  apply Fintype.equivFinOfCardEq
  change Fintype.card (Σ i : Option (Fin k), {x // keep i x}) = _
  rw [Fintype.card_sigma]
  simp [keep, wideSelect, Fintype.sum_option, Nat.add_comm]
  exact Fintype.card_congr (Equiv.refl s)

theorem Transversal.wide_idempotent_models {k : ℕ} {q r : ℕ} {T : Type*} [Fintype T]
    (D : Transversal (Option (Fin k)) (Fin q) T) (hr : r ≤ q)
    (g : Model (Fin q) true) (h : Model (Fin r) true)
    (h7 : Model (Fin k) true) (h8 : Model (Fin (k+1)) true) : Model (Fin (k*q+r)) true := by
  let s : Set (Fin q) := {x | x.val < r}
  let e : s ≃ Fin r := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hr⟩,x.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hh := D.wide_idempotent s g (h.relabel e.symm) h7 h8
  convert hh using 1
  simp only [Fintype.card_fin]
  congr 1
  rw [Fintype.card_eq_nat_card, Nat.card_congr e, Nat.card_fin]


/-- A transversal design with an arbitrary number of full groups. -/
def HasWideTD (k q : ℕ) : Prop :=
  Nonempty (Transversal (Option (Fin k)) (Fin q) (Fin (q*q)))

theorem wide_field_td {k : ℕ} (F : Type*) [Field F] [Fintype F]
    (h : k ≤ Fintype.card F) : HasWideTD k (Fintype.card F) := by
  let D := (wideFieldDesign F h).relabel (Fintype.equivFin F)
  exact ⟨D.reindex (Fintype.equivFinOfCardEq (by simp)).symm⟩

theorem wide_prime_power_td {k p e : ℕ} (hp : p.Prime) (he : e ≠ 0)
    (hk : k ≤ p^e) : HasWideTD k (p^e) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p e) = p^e := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p e he]
  rw [← hc] at hk ⊢
  exact wide_field_td (GaloisField p e) hk

theorem HasWideTD.idempotent_models {k q r : ℕ} (D : HasWideTD k q) (hr : r ≤ q)
    (g : Model (Fin q) true) (h : Model (Fin r) true)
    (hk : Model (Fin k) true) (hk1 : Model (Fin (k+1)) true) :
    Model (Fin (k*q+r)) true := by
  obtain ⟨D⟩ := D
  exact D.wide_idempotent_models hr g h hk hk1

end Spectrum.E63
