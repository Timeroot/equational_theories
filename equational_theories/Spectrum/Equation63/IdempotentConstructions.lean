import equational_theories.Spectrum.Equation63.CyclicDesign
import equational_theories.Spectrum.Equation63.Seeds

/-! Idempotent versions of the E63 product, singular product, and transversal
gluing constructions. The diagonal in a glued model comes from a group filling,
so idempotent group fillings produce an idempotent result. -/
namespace Spectrum.E63
open Classical Law Law.MagmaLaw

theorem Model.product {A C : Type*} {idem : Bool}
    (h : Model A idem) (k : Model C idem) : Model (A × C) idem := by
  obtain ⟨op, hl, hi⟩ := h
  obtain ⟨op', hl', hi'⟩ := k
  exact ⟨fun x y => (op x.1 y.1, op' x.2 y.2),
    fun x y => Prod.ext (hl x.1 y.1) (hl' x.2 y.2),
    fun he x => Prod.ext (hi he x.1) (hi' he x.2)⟩

theorem Model.mul {n m : ℕ} {idem : Bool}
    (h : Model (Fin n) idem) (k : Model (Fin m) idem) : Model (Fin (n*m)) idem :=
  (h.product k).relabel (Fintype.equivFinOfCardEq (by simp))

theorem idem0 : Model (Fin 0) true :=
  ⟨fun x _ => x, fun x => Fin.elim0 x, fun _ x => Fin.elim0 x⟩

theorem idem1 : Model (Fin 1) true :=
  ⟨fun x _ => x, fun _ _ => Subsingleton.elim _ _, fun _ _ => rfl⟩

theorem singular_idem {V B : Type*} [DecidableEq V] (v : V → V → V)
    (q : Option B → Option B → Option B) (b : B → B → B)
    (hq : Idem q) : Idem (singularOp v q b) := by
  rintro (_ | ⟨i,a⟩)
  · rfl
  · simp [singularOp, hq, embed]

/-- The complement model may be nonidempotent: every square is calculated in
the idempotent model with the distinguished point adjoined. -/
theorem singular_idempotent_model {k m : ℕ} (hv : Model (Fin k) true)
    (hq : Model (Fin (m+1)) true) (hb : Law63.HasModel m) :
    Model (Fin (k*m+1)) true := by
  obtain ⟨v,hv,hi⟩ := hv
  obtain ⟨q,hq,hqi⟩ := hq.relabel (finSuccEquiv m)
  obtain ⟨b,hb,_⟩ := model_of_hasModel hb
  have h : Model (Option (Fin k × Fin m)) true :=
    ⟨singularOp v q b,
      singular_law v q b hv (hi rfl) hq hb (hqi rfl none),
      fun _ => singular_idem v q b (hqi rfl)⟩
  exact h.relabel (Fintype.equivFinOfCardEq (by simp))

theorem Design.idem {A I B : Type*} (D : Design A I B)
    (g : ∀ i, {x // D.group x = i} → {x // D.group x = i} → {x // D.group x = i})
    (b : ∀ j, D.block j → D.block j → D.block j)
    (hg : ∀ i, Idem (g i)) : Idem (D.op g b) := by
  intro x
  let X : {z // D.group z = D.group x} := ⟨x,rfl⟩
  change D.op g b X X = X.val
  rw [D.op_group, hg]

theorem Design.idempotent_model {A I B : Type*} [Finite A] (D : Design A I B)
    (hg : ∀ i, Model {x // D.group x = i} true)
    (hb : ∀ j, Model (D.block j) true) : Model A true := by
  choose g hgl hgi using hg
  choose b hbl hbi using hb
  exact ⟨D.op g b, D.lawful g b hgl hbl (fun j => hbi j rfl),
    fun _ => D.idem g b (fun i => hgi i rfl)⟩

/-- Seven idempotent full groups and one idempotent truncated group, with
idempotent transversal blocks of orders seven and eight. -/
theorem Transversal.seven_idempotent {Q T : Type*} [Fintype Q] [Fintype T]
    (D : Transversal Groups Q T) (s : Set Q) (g : Model Q true) (r : Model s true)
    (h7 : Model (Fin 7) true) (h8 : Model (Fin 8) true) :
    Model (Fin (7 * Fintype.card Q + Fintype.card s)) true := by
  let keep := select s
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
  have hm : Model A true := (D.restrict keep).idempotent_model hg hb
  apply hm.relabel
  apply Fintype.equivFinOfCardEq
  change Fintype.card (Σ i : Groups, {x // keep i x}) = _
  rw [Fintype.card_sigma]
  simp [keep, select, Fintype.sum_option, Nat.mul_comm, Nat.add_comm]
  exact Fintype.card_congr (Equiv.refl s)

theorem Transversal.idempotent_models {q r : ℕ} {T : Type*} [Fintype T]
    (D : Transversal Groups (Fin q) T) (hr : r ≤ q)
    (g : Model (Fin q) true) (h : Model (Fin r) true)
    (h7 : Model (Fin 7) true) (h8 : Model (Fin 8) true) : Model (Fin (7*q+r)) true := by
  let s : Set (Fin q) := {x | x.val < r}
  let e : s ≃ Fin r := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hr⟩,x.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hh := D.seven_idempotent s g (h.relabel e.symm) h7 h8
  convert hh using 1
  simp only [Fintype.card_fin]
  congr 1
  rw [Fintype.card_eq_nat_card, Nat.card_congr e, Nat.card_fin]

theorem seven_idempotent {q r : ℕ} (hq : 0 < q) (hc : q.Coprime 60) (hr : r ≤ q)
    (g : Model (Fin q) true) (h : Model (Fin r) true) : Model (Fin (7*q+r)) true := by
  letI : NeZero q := ⟨by omega⟩
  exact ((designZMod q hc).relabel (ZMod.finEquiv q).toEquiv.symm).idempotent_models
    hr g h idem7 idem8

end Spectrum.E63
