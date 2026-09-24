import equational_theories.Spectrum.Equation63.Gluing

/-! Transversal designs and their restrictions to selected points. -/
namespace Spectrum.E63
open Classical Law Law.MagmaLaw

structure Transversal (I Q T : Type*) where
  coord : T → I → Q
  pair : ∀ i j, i ≠ j → ∀ x y, ∃! t, coord t i = x ∧ coord t j = y

variable {I Q T : Type*}

/-- Delete any selection of points from a transversal design. -/
noncomputable def Transversal.restrict (D : Transversal I Q T) (keep : I → Q → Prop) :
    Design (Σ i, {x // keep i x}) I T where
  group := Sigma.fst
  block t := {p | D.coord t p.1 = p.2.val}
  transverse t := by
    rintro ⟨i,x,hx⟩ hp ⟨j,y,hy⟩ hq he
    dsimp at he
    subst j
    have hh : x = y := hp.symm.trans hq
    subst y
    rfl
  pair := by
    rintro ⟨i,x,hx⟩ ⟨j,y,hy⟩ he
    exact D.pair i j he x y

/-- A restricted block is parametrized by the groups whose point survives. -/
noncomputable def Transversal.blockEquiv (D : Transversal I Q T) (keep : I → Q → Prop)
    (t : T) : ((D.restrict keep).block t) ≃ {i // keep i (D.coord t i)} where
  toFun p := ⟨p.val.1, by
    have hp : D.coord t p.val.1 = p.val.2.val := p.property
    rw [hp]
    exact p.val.2.property⟩
  invFun i := ⟨⟨i.val, ⟨D.coord t i, i.property⟩⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨i,x,hx⟩, hp⟩
    have hp' : D.coord t i = x := hp
    subst x
    rfl
  right_inv _ := rfl

noncomputable def Transversal.groupEquiv (D : Transversal I Q T) (keep : I → Q → Prop)
    (i : I) : {x // (D.restrict keep).group x = i} ≃ {x // keep i x} where
  toFun p := p.property ▸ p.val.2
  invFun x := ⟨⟨i,x⟩, rfl⟩
  left_inv := by rintro ⟨⟨j,x⟩, h⟩; cases h; rfl
  right_inv _ := rfl

abbrev Groups := Option (Fin 7)

def select {Q : Type*} (s : Set Q) : Groups → Q → Prop
  | none, x => x ∈ s
  | some _, _ => True

/-- Seven full groups and one truncated group; transversal blocks have size 7 or 8. -/
theorem Transversal.seven [Fintype Q] [Fintype T] (D : Transversal Groups Q T)
    (s : Set Q) (g : Model Q) (r : Model s)
    (h7 : Model (Fin 7) true) (h8 : Model (Fin 8) true) :
    Model (Fin (7 * Fintype.card Q + Fintype.card s)) := by
  let keep := select s
  let A := Σ i, {x // keep i x}
  have hg : ∀ i, Model {x // (D.restrict keep).group x = i} := by
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
        cases i <;> simp [keep, select, he]
      simp [hh, Fintype.card_option]
    · apply h7.of_card
      let e : {i // keep i (D.coord t i)} ≃ Fin 7 := {
        toFun := fun i => match i with
          | ⟨some j, _⟩ => j
          | ⟨none, h⟩ => False.elim (he h)
        invFun := fun j => ⟨some j, trivial⟩
        left_inv := by rintro ⟨(_ | j), h⟩; exact (he h).elim; rfl
        right_inv := fun _ => rfl }
      exact Fintype.card_congr e
  have hm : Model A := (D.restrict keep).model hg hb
  apply hm.relabel
  apply Fintype.equivFinOfCardEq
  change Fintype.card (Σ i : Groups, {x // keep i x}) = _
  rw [Fintype.card_sigma]
  simp [keep, select, Fintype.sum_option, Nat.mul_comm, Nat.add_comm]
  exact Fintype.card_congr (Equiv.refl s)

noncomputable def Transversal.relabel (D : Transversal I Q T) {P : Type*} (e : Q ≃ P) :
    Transversal I P T where
  coord t i := e (D.coord t i)
  pair i j h x y := by
    obtain ⟨t, ht, hu⟩ := D.pair i j h (e.symm x) (e.symm y)
    refine ⟨t, ⟨by simp [ht.1], by simp [ht.2]⟩, ?_⟩
    intro u hh
    apply hu
    exact ⟨e.injective (hh.1.trans (e.apply_symm_apply x).symm),
      e.injective (hh.2.trans (e.apply_symm_apply y).symm)⟩

theorem Transversal.models {q r : ℕ} [Fintype T] (D : Transversal Groups (Fin q) T)
    (hr : r ≤ q) (g : Law63.HasModel q) (h : Law63.HasModel r)
    (h7 : Model (Fin 7) true) (h8 : Model (Fin 8) true) : Law63.HasModel (7*q+r) := by
  let s : Set (Fin q) := {x | x.val < r}
  let e : s ≃ Fin r := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hr⟩,x.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hh := (D.seven s (model_of_hasModel g)
    ((model_of_hasModel h).relabel e.symm) h7 h8).hasModel
  convert hh using 1
  simp only [Fintype.card_fin]
  congr 1
  rw [Fintype.card_eq_nat_card, Nat.card_congr e, Nat.card_fin]

end Spectrum.E63
