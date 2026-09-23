import equational_theories.Spectrum.Mendelsohn
import equational_theories.Spectrum.Equation1719Twist

/-! # A Bose construction with a two-point hole

Use the existing cross-fibre construction on `Q × Fin 3`. Each fibre shares
its two added points with a fixed five-point semisymmetric quasigroup. All
points except the second shared point are idempotent. A three-cycle through
that point gives an E1719 model on `3 * |Q| + 2` points.
-/

open Classical
namespace Spectrum.MendelsohnTwoHole

abbrev Carrier (Q : Type*) := Option (Option (Q × Fin 3))

def core5 (i j : Fin 5) : Fin 5 :=
  ![![0,1,3,4,2], ![1,0,4,2,3], ![4,3,2,0,1], ![2,4,1,3,0], ![3,2,0,1,4]] i j

theorem core5_semi (i j : Fin 5) : core5 j (core5 i j) = i := by
  fin_cases i <;> fin_cases j <;> decide

def index (i : Fin 3) : Fin 5 := ⟨i.val+2, by omega⟩

def embed {Q : Type*} (a : Q) : Fin 5 → Carrier Q :=
  ![none, some none, some (some (a,0)), some (some (a,1)), some (some (a,2))]

noncomputable def op {Q : Type*} (L : IdempotentLatin Q) : Carrier Q → Carrier Q → Carrier Q
  | none, none => none
  | none, some none => some none
  | some none, none => some none
  | some none, some none => none
  | none, some (some (a,j)) => embed a (core5 0 (index j))
  | some none, some (some (a,j)) => embed a (core5 1 (index j))
  | some (some (a,i)), none => embed a (core5 (index i) 0)
  | some (some (a,i)), some none => embed a (core5 (index i) 1)
  | some (some (a,i)), some (some (b,j)) =>
    if a = b then embed a (core5 (index i) (index j))
    else some (some (Mendelsohn.cross L (a,i) (b,j)))

theorem semi {Q : Type*} (L : IdempotentLatin Q) (x y : Carrier Q) :
    op L y (op L x y) = x := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      cases y with
      | none => rfl
      | some y => obtain ⟨a,i⟩ := y; fin_cases i <;> simp [op, embed, core5, index]
  | some x =>
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        cases y with
        | none => rfl
        | some y => obtain ⟨a,i⟩ := y; fin_cases i <;> simp [op, embed, core5, index]
    | some x =>
      obtain ⟨a,i⟩ := x
      cases y with
      | none => fin_cases i <;> simp [op, embed, core5, index]
      | some y =>
        cases y with
        | none => fin_cases i <;> simp [op, embed, core5, index]
        | some y =>
          obtain ⟨b,j⟩ := y
          by_cases h : a = b
          · subst b
            fin_cases i <;> fin_cases j <;> simp [op, embed, core5, index]
          · have hc := (Mendelsohn.cross_ne_right L (x := (a,i)) (y := (b,j)) h).symm
            simp only [op, if_neg h]
            change (if b = (Mendelsohn.cross L (a,i) (b,j)).1 then _ else _) = _
            rw [if_neg hc]
            exact congrArg (fun z => some (some z)) (Mendelsohn.cross_semi L (a,i) (b,j))

theorem idem {Q : Type*} (L : IdempotentLatin Q) (x : Carrier Q)
    (hx : x ≠ some none) : op L x x = x := by
  cases x with
  | none => rfl
  | some x =>
    cases x with
    | none => exact (hx rfl).elim
    | some x => obtain ⟨a,i⟩ := x; fin_cases i <;> simp [op, embed, core5, index]

noncomputable def twist {Q : Type*} (L : IdempotentLatin Q) (a : Q) :
    SemisymmetricTwist (Carrier Q) :=
  SemisymmetricTwist.ofTriangle (op L) (some none) (some (some (a,0))) (some (some (a,2)))
    (by simp) (by simp) (by simp) (semi L) (idem L)
    (by simp [op, embed, core5, index])
    (by simp [op, embed, core5, index])
    (by simp [op, embed, core5, index])

/-- The constructive two-hole specialization needed for E1719. -/
theorem models {m : ℕ} (hm : 0 < m) (hm2 : m ≠ 2) : Law1719.HasModel (3*m+2) := by
  obtain ⟨Q, f, ⟨L⟩, hc⟩ := IdempotentLatin.exists_card m hm hm2
  letI : Fintype Q := f
  haveI : Nonempty Q := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Q)
  let a : Q := Classical.choice inferInstance
  exact Law.MagmaLaw.hasModel_of_card (twist L a).magma
    ((@Law1719.models_iff _ (twist L a).magma).mpr (twist L a).equation1719)
    (by simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, hc]; omega)

spectrum_assert models complete
end Spectrum.MendelsohnTwoHole
