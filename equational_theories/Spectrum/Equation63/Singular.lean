import equational_theories.Spectrum.Equation63.Gluing

/-! The one-point singular direct product for E63. -/
namespace Spectrum.E63
open Classical
variable {V B : Type*}

def embed (i : V) : Option B → Option (V × B)
  | none => none
  | some a => some (i,a)

def singularOp [DecidableEq V] (v : V → V → V) (q : Option B → Option B → Option B)
    (b : B → B → B) : Option (V × B) → Option (V × B) → Option (V × B)
  | none, none => none
  | none, some (j,c) => embed j (q none (some c))
  | some (i,a), none => embed i (q (some a) none)
  | some (i,a), some (j,c) =>
    if i = j then embed i (q (some a) (some c)) else some (v i j, b a c)

theorem singular_embed [DecidableEq V] (v q b) (hq : q none none = none)
    (i : V) (a c : Option B) :
    singularOp v q b (embed i a) (embed i c) = embed i (q a c) := by
  cases a <;> cases c <;> simp [embed, singularOp, hq]

theorem singular_law [Finite V] [DecidableEq V] (v : V → V → V)
    (q : Option B → Option B → Option B) (b : B → B → B)
    (hv : Lawful v) (hi : Idem v) (hq : Lawful q) (hb : Lawful b)
    (h0 : q none none = none) : Lawful (singularOp v q b) := by
  have fiber (i : V) (a c : Option B) :
      singularOp v q b (embed i c)
        (singularOp v q b (embed i a) (singularOp v q b (embed i a) (embed i c))) =
          embed i a := by
    rw [singular_embed _ _ _ h0, singular_embed _ _ _ h0,
      singular_embed _ _ _ h0, hq]
  rintro (_ | ⟨i,a⟩) (_ | ⟨j,c⟩)
  · rfl
  · exact fiber j none (some c)
  · exact fiber i (some a) none
  · by_cases he : i = j
    · subst j
      exact fiber i (some a) (some c)
    · have hd := discrete hv hi he
      simp only [singularOp, if_neg he, if_neg hd.1, if_neg hd.2, hv, hb]

def Pointed (A : Type*) : Prop := ∃ op : A → A → A, Lawful op ∧ ∃ p, op p p = p

theorem Pointed.relabel {A C : Type*} (h : Pointed A) (e : A ≃ C) : Pointed C := by
  obtain ⟨op,hl,p,hp⟩ := h
  refine ⟨fun x y => e (op (e.symm x) (e.symm y)), ?_, e p, ?_⟩
  · intro x y
    simp only [Equiv.symm_apply_apply, hl, Equiv.apply_symm_apply]
  · simp only [Equiv.symm_apply_apply, hp]

theorem Pointed.product {A C : Type*} (h : Pointed A) (k : Pointed C) : Pointed (A × C) := by
  obtain ⟨op,hl,p,hp⟩ := h
  obtain ⟨op',hl',p',hp'⟩ := k
  exact ⟨fun x y => (op x.1 y.1, op' x.2 y.2),
    fun x y => Prod.ext (hl x.1 y.1) (hl' x.2 y.2), (p,p'), Prod.ext hp hp'⟩

theorem Pointed.hasModel {n : ℕ} (h : Pointed (Fin n)) : Law63.HasModel n := by
  obtain ⟨op,hl,_⟩ := h
  exact (show Model (Fin n) from ⟨op,hl,by simp⟩).hasModel

/-- Relabel a specified point as `none`. -/
theorem Pointed.option {n : ℕ} (h : Pointed (Fin (n+1))) :
    ∃ q : Option (Fin n) → Option (Fin n) → Option (Fin n), Lawful q ∧ q none none = none := by
  obtain ⟨op,hl,p,hp⟩ := h
  let e : Fin (n+1) ≃ Option (Fin n) := (Equiv.swap p 0).trans (finSuccEquiv n)
  have he : e p = none := by simp [e, finSuccEquiv]
  refine ⟨fun x y => e (op (e.symm x) (e.symm y)), ?_, ?_⟩
  · intro x y
    simp only [Equiv.symm_apply_apply, hl, Equiv.apply_symm_apply]
  · have hep : e.symm none = p := by rw [← he, Equiv.symm_apply_apply]
    simp only [hep, hp, he]

theorem singular_model {k m : ℕ} (hv : Model (Fin k) true)
    (hq : Pointed (Fin (m+1))) (hb : Law63.HasModel m) : Law63.HasModel (k*m+1) := by
  obtain ⟨v,hv,hi⟩ := hv
  obtain ⟨q,hq,h0⟩ := hq.option
  obtain ⟨b,hb,_⟩ := model_of_hasModel hb
  have h : Model (Option (Fin k × Fin m)) :=
    ⟨singularOp v q b, singular_law v q b hv (hi rfl) hq hb h0, by simp⟩
  exact (h.relabel (Fintype.equivFinOfCardEq (by simp))).hasModel

end Spectrum.E63
