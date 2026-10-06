import equational_theories.Spectrum.Equation63.ExtendedDesign

/-! Completing a quasi-difference matrix with a smaller transversal design. -/
namespace Spectrum.E63.QuasiDifference
open Classical
variable {G H R I T : Type*} [AddCommGroup G]

def shift (t : G) : G ⊕ H → G ⊕ H
  | .inl a => .inl (a+t)
  | .inr h => .inr h

def difference : G ⊕ H → G ⊕ H → Option G
  | .inl a, .inl b => some (a-b)
  | _, _ => none

def hole : G ⊕ H → Option H
  | .inl _ => none
  | .inr h => some h

variable (M : R → I → G ⊕ H)

structure Checked : Prop where
  differences : ∀ i j, i ≠ j → ∀ r s,
    difference (M r i) (M r j) ≠ none →
    difference (M r i) (M r j) = difference (M s i) (M s j) → r = s
  holes : ∀ i r s, hole (M r i) ≠ none → hole (M r i) = hole (M s i) → r = s
  single : ∀ i j, i ≠ j → ∀ r, hole (M r i) = none ∨ hole (M r j) = none

/-- Small left-inverse certificates avoid a quadratic comparison of rows. -/
theorem Checked.of_leftInverses
    (d : I → I → Option G → R) (h : I → Option H → R)
    (hd : ∀ i j, i ≠ j → ∀ r,
      difference (M r i) (M r j) = none ∨ d i j (difference (M r i) (M r j)) = r)
    (hh : ∀ i r, hole (M r i) = none ∨ h i (hole (M r i)) = r)
    (hs : ∀ i j, i ≠ j → ∀ r, hole (M r i) = none ∨ hole (M r j) = none) :
    Checked M where
  differences i j hij r s hn he := by
    have hr := (hd i j hij r).resolve_left hn
    have hs := (hd i j hij s).resolve_left (fun hh => hn (he.trans hh))
    rw [he] at hr
    exact hr.symm.trans hs
  holes i r s hn he := by
    have hr := (hh i r).resolve_left hn
    have hs := (hh i s).resolve_left (fun hh => hn (he.trans hh))
    rw [he] at hr
    exact hr.symm.trans hs
  single := hs

theorem partial_injective (hc : Checked M) (i j : I) (hij : i ≠ j) :
    Function.Injective (fun p : R × G => (shift p.2 (M p.1 i), shift p.2 (M p.1 j))) := by
  rintro ⟨r,t⟩ ⟨s,u⟩ he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  have finish (hrs : r = s) (k : I) (a : G) (hk : M r k = .inl a)
      (he : shift t (M r k) = shift u (M s k)) : (r,t) = (s,u) := by
    subst s
    simp only [hk, shift, Sum.inl.injEq] at he
    exact Prod.ext rfl (add_left_cancel he)
  cases er : M r i with
  | inl a =>
    cases es : M s i with
    | inr z => simp [er,es,shift] at h1
    | inl c =>
      cases erj : M r j with
      | inl b =>
        cases esj : M s j with
        | inr z => simp [erj,esj,shift] at h2
        | inl d =>
          have ha : a+t=c+u := by simpa [er,es,shift] using h1
          have hb : b+t=d+u := by simpa [erj,esj,shift] using h2
          have hd : a-b=c-d := by
            calc
              a-b = (a+t)-(b+t) := by abel
              _ = (c+u)-(d+u) := by rw [ha,hb]
              _ = c-d := by abel
          have hrs := hc.differences i j hij r s (by simp [er,erj,difference])
            (by simp [er,erj,es,esj,difference,hd])
          exact finish hrs i a er h1
      | inr z =>
        cases esj : M s j with
        | inl d => simp [erj,esj,shift] at h2
        | inr w =>
          have hz : z=w := by simpa [erj,esj,shift] using h2
          have hrs := hc.holes j r s (by simp [erj,hole]) (by simp [erj,esj,hole,hz])
          exact finish hrs i a er h1
  | inr z =>
    cases es : M s i with
    | inl c => simp [er,es,shift] at h1
    | inr w =>
      have hz : z=w := by simpa [er,es,shift] using h1
      have hrs := hc.holes i r s (by simp [er,hole]) (by simp [er,es,hole,hz])
      cases erj : M r j with
      | inr b => simpa [er,erj,hole] using hc.single i j hij r
      | inl b => exact finish hrs j b erj h2

def coord (D : Transversal I H T) : (R × G) ⊕ T → I → G ⊕ H
  | .inl p, i => shift p.2 (M p.1 i)
  | .inr t, i => .inr (D.coord t i)

theorem coord_injective (hc : Checked M) (D : Transversal I H T)
    (i j : I) (hij : i ≠ j) :
    Function.Injective (fun t => (coord M D t i, coord M D t j)) := by
  intro a b he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (partial_injective M hc i j hij he)
    | inr b =>
      rcases hc.single i j hij a.1 with hi | hj
      · cases e : M a.1 i <;> simp [hole,e] at hi
        simp [coord,e,shift] at h1
      · cases e : M a.1 j <;> simp [hole,e] at hj
        simp [coord,e,shift] at h2
  | inr a =>
    cases b with
    | inl b =>
      rcases hc.single i j hij b.1 with hi | hj
      · cases e : M b.1 i <;> simp [hole,e] at hi
        simp [coord,e,shift] at h1
      · cases e : M b.1 j <;> simp [hole,e] at hj
        simp [coord,e,shift] at h2
    | inr b =>
      have hi : D.coord a i = D.coord b i := by simpa [coord] using h1
      have hj : D.coord a j = D.coord b j := by simpa [coord] using h2
      obtain ⟨t,ht,hu⟩ := D.pair i j hij (D.coord b i) (D.coord b j)
      exact congrArg Sum.inr ((hu a ⟨hi,hj⟩).trans (hu b ⟨rfl,rfl⟩).symm)

/-- Only the short quasi-difference certificate is checked by computation.
The development by translations and the hole filling are proved abstractly. -/
noncomputable def design [Fintype G] [Fintype H] [Fintype R] [Fintype T]
    (hc : Checked M) (D : Transversal I H T)
    (hcard : Fintype.card ((R × G) ⊕ T) = Fintype.card ((G ⊕ H) × (G ⊕ H))) :
    Transversal I (G ⊕ H) ((R × G) ⊕ T) where
  coord := coord M D
  pair i j hij x y := by
    have hb := (Fintype.bijective_iff_injective_and_card
      (fun t => (coord M D t i, coord M D t j))).mpr
      ⟨coord_injective M hc D i j hij,hcard⟩
    obtain ⟨t,ht⟩ := hb.surjective (x,y)
    refine ⟨t, ⟨congrArg Prod.fst ht,congrArg Prod.snd ht⟩, ?_⟩
    intro u hu
    exact hb.injective ((Prod.ext hu.1 hu.2).trans ht.symm)

end Spectrum.E63.QuasiDifference
