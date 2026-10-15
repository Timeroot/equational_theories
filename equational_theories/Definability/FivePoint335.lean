import equational_theories.Definability.CloneTraps
import equational_theories.Equations.All

/-! A five-point E335 source separating three term-definability arrows.
The small binary relations are closed under the source operation. Hence every
binary term obeys their restrictions on selected table entries. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Law Law.MagmaLaw
namespace Definability.FivePoint335

@[implicit_reducible] def source : Magma (Fin 5) where
  op := ![![0, 4, 0, 1, 3], ![3, 1, 1, 4, 0], ![0, 1, 2, 2, 2],
    ![4, 0, 2, 2, 1], ![1, 3, 2, 0, 2]]

theorem source_law : @Equation335 (Fin 5) source := by decide

/-- In every E335 magma, `x` and its square multiply to the square in either
order, and the square is idempotent. This explains the unary-term invariant. -/
theorem square_absorption {M : Type*} [Magma M] (h : Equation335 M) (x : M) :
    x ◇ (x ◇ x) = x ◇ x ∧ (x ◇ x) ◇ x = x ◇ x ∧
      (x ◇ x) ◇ (x ◇ x) = x ◇ x := by
  have hx : x ◇ (x ◇ x) = x ◇ x := (h x x).symm
  have hqx : (x ◇ x) ◇ x = x ◇ x := by
    calc
      (x ◇ x) ◇ x = x ◇ (x ◇ (x ◇ x)) := h _ _
      _ = x ◇ x := by rw [hx, hx]
  refine ⟨hx, hqx, ?_⟩
  calc
    (x ◇ x) ◇ (x ◇ x) = (x ◇ x) ◇ ((x ◇ x) ◇ x) := by rw [hqx]
    _ = x ◇ (x ◇ x) := (h _ _).symm
    _ = x ◇ x := hx

abbrev Index := Fin 7

def firstCell : Index → Fin 5 × Fin 5 := ![(0, 1), (1, 0), (0, 2), (2, 0), (1, 0), (2, 0), (2, 4)]

def secondCell : Index → Fin 5 × Fin 5 := ![(1, 0), (2, 1), (2, 0), (4, 2), (2, 0), (2, 1), (3, 3)]

def relation (i : Index) (a b : Fin 5) : Prop :=
  match i.val with
  | 0 => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)
  | 1 => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 1) ∨ (a = 4 ∧ b = 1)
  | 2 => (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)
  | 3 => (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 4)
  | 4 => (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 3 ∧ b = 0) ∨ (a = 4 ∧ b = 0)
  | 5 => (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 2)
  | _ => (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 4 ∧ b = 3)

instance (i : Index) (a b : Fin 5) : Decidable (relation i a b) := by
  unfold relation
  split <;> infer_instance

def Constraints (f : Fin 5 → Fin 5 → Fin 5) : Prop :=
  ∀ i, relation i (f (firstCell i).1 (firstCell i).2)
    (f (secondCell i).1 (secondCell i).2)

theorem closed : ∀ (i : Index) (a b c d : Fin 5), relation i a b → relation i c d →
    relation i (source.op a c) (source.op b d) := by decide

theorem source_constraints : source.IsCloneInvariant Constraints where
  fst := by unfold Constraints; decide
  snd := by unfold Constraints; decide
  comp f g hf hg i := closed i _ _ _ _ (hf i) (hg i)

/-- Every nonvariable unary term is the square map in this source. -/
def Shape (f : Fin 5 → Fin 5 → Fin 5) : Prop :=
  f = (fun x _ => x) ∨ f = (fun _ y => y) ∨ ∀ x, f x x = source.op x x

theorem shape_weak (f : Fin 5 → Fin 5 → Fin 5) (hf : Shape f) (x : Fin 5) :
    f x x = x ∨ f x x = source.op x x := by
  rcases hf with rfl | rfl | hf
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (hf x)

theorem diagonal_clamp : ∀ x a b : Fin 5,
    (a = x ∨ a = source.op x x) → (b = x ∨ b = source.op x x) →
    source.op a b = source.op x x := by
  intro x a b ha hb
  obtain ⟨h1, h2, h3⟩ := @square_absorption (Fin 5) source source_law x
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact h1
  · exact h2
  · exact h3

theorem source_shape : source.IsCloneInvariant Shape where
  fst := Or.inl rfl
  snd := Or.inr (Or.inl rfl)
  comp f g hf hg := Or.inr (Or.inr fun x =>
    diagonal_clamp x _ _ (shape_weak f hf x) (shape_weak g hg x))

theorem source_invariant : source.IsCloneInvariant (fun f => Constraints f ∧ Shape f) where
  fst := ⟨source_constraints.fst, source_shape.fst⟩
  snd := ⟨source_constraints.snd, source_shape.snd⟩
  comp f g hf hg := ⟨source_constraints.comp f g hf.1 hg.1,
    source_shape.comp f g hf.2 hg.2⟩

theorem five_cases (z : Fin 5) : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 := by omega

theorem refute3352 (f : Fin 5 → Fin 5 → Fin 5) (hf : Constraints f)
    (hq : ∀ x, f x x = source.op x x)
    (h : ∀ x y, f x y = f y (f y (f x x))) : False := by
  have swap : (f 0 1 = 0 ∧ f 1 0 = 1) ∨ (f 0 1 = 1 ∧ f 1 0 = 0) ∨
      (f 0 1 = 2 ∧ f 1 0 = 2) ∨ (f 0 1 = 3 ∧ f 1 0 = 4) ∨
      (f 0 1 = 4 ∧ f 1 0 = 3) := hf 0
  have column : (f 1 0 = 0 ∧ f 2 1 = 1) ∨ (f 1 0 = 1 ∧ f 2 1 = 1) ∨
      (f 1 0 = 1 ∧ f 2 1 = 2) ∨ (f 1 0 = 2 ∧ f 2 1 = 1) ∨
      (f 1 0 = 3 ∧ f 2 1 = 1) ∨ (f 1 0 = 4 ∧ f 2 1 = 1) := hf 1
  have h01 := h 0 1
  have h10 := h 1 0
  have h13 := h 1 3
  have h14 := h 1 4
  have h21 := h 2 1
  have h31 := h 3 1
  have h41 := h 4 1
  have q0 : f 0 0 = 0 := hq 0
  have q1 : f 1 1 = 1 := hq 1
  have q2 : f 2 2 = 2 := hq 2
  have q3 : f 3 3 = 2 := hq 3
  have q4 : f 4 4 = 2 := hq 4
  clear h hf hq
  rcases swap with ht | ht | ht | ht | ht <;> grind only

/-- The target law would force the column at 2 to contain 4, but every one
of its five positions is excluded by the same law and three local relations. -/
theorem refute3748 (f : Fin 5 → Fin 5 → Fin 5) (hf : Constraints f)
    (hq : ∀ x, f x x = source.op x x)
    (h : ∀ x y, f x y = f (f y x) (f x x)) : False := by
  have swap : (f 0 1 = 0 ∧ f 1 0 = 1) ∨ (f 0 1 = 1 ∧ f 1 0 = 0) ∨
      (f 0 1 = 2 ∧ f 1 0 = 2) ∨ (f 0 1 = 3 ∧ f 1 0 = 4) ∨
      (f 0 1 = 4 ∧ f 1 0 = 3) := hf 0
  have zeroTwo : (f 0 2 = 0 ∧ f 2 0 = 0) ∨ (f 0 2 = 0 ∧ f 2 0 = 2) ∨
      (f 0 2 = 2 ∧ f 2 0 = 0) := hf 2
  have column : (f 2 0 = 0 ∧ f 4 2 = 2) ∨ (f 2 0 = 2 ∧ f 4 2 = 2) ∨
      (f 2 0 = 2 ∧ f 4 2 = 4) := hf 3
  have q0 : f 0 0 = 0 := hq 0
  have q1 : f 1 1 = 1 := hq 1
  have q2 : f 2 2 = 2 := hq 2
  have q3 : f 3 3 = 2 := hq 3
  have h01 := h 0 1
  have h10 := h 1 0
  have h12 := h 1 2
  have h20 := h 2 0
  have h21 := h 2 1
  have h23 := h 2 3
  have h30 := h 3 0
  have h31 := h 3 1
  have h32 := h 3 2
  clear h hf hq
  have z02 : f 0 2 = 0 ∧ f 2 0 = 0 := by
    rcases zeroTwo with ht | ht | ht <;> grind only
  have c42 : f 4 2 = 2 := by grind only
  have noFour (x : Fin 5) : f x 2 ≠ 4 := by
    fin_cases x <;> intro hx <;> grind only
  rcases swap with ht | ht | ht | ht | ht
  · grind only
  · grind only
  · grind only
  · have hn := noFour (f 1 3)
    grind only
  · have hn := noFour (f 0 3)
    grind only

/-- The two surviving orientations of `(f 0 1, f 1 0)` each force an
impossible square of the row map `f 4`. Five cases on one entry suffice. -/
theorem refute4408 (f : Fin 5 → Fin 5 → Fin 5) (hf : Constraints f)
    (hq : ∀ x, f x x = source.op x x)
    (h : ∀ x y, f x (f x y) = f (f y y) x) : False := by
  have swap : (f 0 1 = 0 ∧ f 1 0 = 1) ∨ (f 0 1 = 1 ∧ f 1 0 = 0) ∨
      (f 0 1 = 2 ∧ f 1 0 = 2) ∨ (f 0 1 = 3 ∧ f 1 0 = 4) ∨
      (f 0 1 = 4 ∧ f 1 0 = 3) := hf 0
  have column : (f 1 0 = 0 ∧ f 2 0 = 0) ∨ (f 1 0 = 1 ∧ f 2 0 = 0) ∨
      (f 1 0 = 1 ∧ f 2 0 = 2) ∨ (f 1 0 = 2 ∧ f 2 0 = 0) ∨
      (f 1 0 = 3 ∧ f 2 0 = 0) ∨ (f 1 0 = 4 ∧ f 2 0 = 0) := hf 4
  have rowTwo : (f 2 0 = 0 ∧ f 2 1 = 1) ∨ (f 2 0 = 2 ∧ f 2 1 = 2) := hf 5
  have toFour : (f 2 4 = 2 ∧ f 3 3 = 2) ∨ (f 2 4 = 2 ∧ f 3 3 = 3) ∨
      (f 2 4 = 4 ∧ f 3 3 = 3) := hf 6
  have h01 := h 0 1
  have h03 := h 0 3
  have h04 := h 0 4
  have h10 := h 1 0
  have h13 := h 1 3
  have h14 := h 1 4
  have h20 := h 2 0
  have h40 := h 4 0
  have h41 := h 4 1
  have h43 := h 4 3
  have h44 := h 4 4
  have q0 : f 0 0 = 0 := hq 0
  have q1 : f 1 1 = 1 := hq 1
  have q2 : f 2 2 = 2 := hq 2
  have q3 : f 3 3 = 2 := hq 3
  have q4 : f 4 4 = 2 := hq 4
  clear h hf hq
  have c42 : f 4 2 = 2 := by grind only
  rcases swap with ht | ht | ht | ht | ht
  · grind only
  · grind only
  · grind only
  · rcases five_cases (f 4 1) with he | he | he | he | he <;> grind only
  · rcases five_cases (f 4 0) with he | he | he | he | he <;> grind only

end Definability.FivePoint335

theorem Law.MagmaLaw.Equation3352_not_termDefinableFromFin_Equation335_fivePoint :
    ¬ Law3352.TermDefinableFromFin Law335 := by
  apply not_termDefinableFromFin_of_invariant Definability.FivePoint335.source
    ((@Law335.models_iff (Fin 5) Definability.FivePoint335.source).mpr
      Definability.FivePoint335.source_law)
    Definability.FivePoint335.source_invariant
  intro f hf ht
  have h := (@Law3352.models_iff (Fin 5) ⟨f⟩).mp ht
  rcases hf.2 with rfl | rfl | hq
  · have he := h 0 1
    change (0 : Fin 5) = 1 at he
    exact (by decide : (0 : Fin 5) ≠ 1) he
  · have he := h 0 1
    change (1 : Fin 5) = 0 at he
    exact (by decide : (1 : Fin 5) ≠ 0) he
  · exact Definability.FivePoint335.refute3352 f hf.1 hq h

theorem Law.MagmaLaw.Equation3352_not_termDefinableFrom_Equation335_fivePoint :
    ¬ Law3352.TermDefinableFrom Law335 :=
  fun h => Equation3352_not_termDefinableFromFin_Equation335_fivePoint
    (termDefinableFin_of_termDefinable h)

/-- info: 'Law.MagmaLaw.Equation3352_not_termDefinableFromFin_Equation335_fivePoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.Equation3352_not_termDefinableFromFin_Equation335_fivePoint

theorem Law.MagmaLaw.Equation3748_not_termDefinableFromFin_Equation335_fivePoint :
    ¬ Law3748.TermDefinableFromFin Law335 := by
  apply not_termDefinableFromFin_of_invariant Definability.FivePoint335.source
    ((@Law335.models_iff (Fin 5) Definability.FivePoint335.source).mpr
      Definability.FivePoint335.source_law)
    Definability.FivePoint335.source_invariant
  intro f hf ht
  have h := (@Law3748.models_iff (Fin 5) ⟨f⟩).mp ht
  rcases hf.2 with rfl | rfl | hq
  · have he := h 0 1
    change (0 : Fin 5) = 1 at he
    exact (by decide : (0 : Fin 5) ≠ 1) he
  · have he := h 0 1
    change (1 : Fin 5) = 0 at he
    exact (by decide : (1 : Fin 5) ≠ 0) he
  · exact Definability.FivePoint335.refute3748 f hf.1 hq h

theorem Law.MagmaLaw.Equation3748_not_termDefinableFrom_Equation335_fivePoint :
    ¬ Law3748.TermDefinableFrom Law335 :=
  fun h => Equation3748_not_termDefinableFromFin_Equation335_fivePoint
    (termDefinableFin_of_termDefinable h)

/-- info: 'Law.MagmaLaw.Equation3748_not_termDefinableFromFin_Equation335_fivePoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.Equation3748_not_termDefinableFromFin_Equation335_fivePoint

theorem Law.MagmaLaw.Equation4408_not_termDefinableFromFin_Equation335_fivePoint :
    ¬ Law4408.TermDefinableFromFin Law335 := by
  apply not_termDefinableFromFin_of_invariant Definability.FivePoint335.source
    ((@Law335.models_iff (Fin 5) Definability.FivePoint335.source).mpr
      Definability.FivePoint335.source_law)
    Definability.FivePoint335.source_invariant
  intro f hf ht
  have h := (@Law4408.models_iff (Fin 5) ⟨f⟩).mp ht
  rcases hf.2 with rfl | rfl | hq
  · have he := h 0 1
    change (0 : Fin 5) = 1 at he
    exact (by decide : (0 : Fin 5) ≠ 1) he
  · have he := h 0 1
    change (1 : Fin 5) = 0 at he
    exact (by decide : (1 : Fin 5) ≠ 0) he
  · exact Definability.FivePoint335.refute4408 f hf.1 hq h

theorem Law.MagmaLaw.Equation4408_not_termDefinableFrom_Equation335_fivePoint :
    ¬ Law4408.TermDefinableFrom Law335 :=
  fun h => Equation4408_not_termDefinableFromFin_Equation335_fivePoint
    (termDefinableFin_of_termDefinable h)

/-- info: 'Law.MagmaLaw.Equation4408_not_termDefinableFromFin_Equation335_fivePoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.Equation4408_not_termDefinableFromFin_Equation335_fivePoint

