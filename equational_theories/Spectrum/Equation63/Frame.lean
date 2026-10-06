import equational_theories.Spectrum.Equation63.Gluing

/-! An E63 frame is a partial algebra whose holes are the fibers of the first
coordinate. Inflate it by any E63 algebra, adjoin one common point, and fill
the enlarged holes. Idempotence is needed only in the final hole fillings.
This includes Bennett's constructions using partial C3 quasigroups. -/
namespace Spectrum.E63
open Classical

structure Frame (I H : Type*) where
  op : (I × H) → (I × H) → (I × H)
  law : ∀ x y, x.1 ≠ y.1 → op y (op x (op x y)) = x
  first : ∀ x y, x.1 ≠ y.1 → x.1 ≠ (op x y).1
  second : ∀ x y, x.1 ≠ y.1 → y.1 ≠ (op x (op x y)).1

namespace Frame
variable {I H B : Type*}

def embed (i : I) : Option (H × B) → Option ((I × H) × B)
  | none => none
  | some (a,b) => some ((i,a),b)

def fill [DecidableEq I] (F : Frame I H)
    (q : Option (H × B) → Option (H × B) → Option (H × B)) (b : B → B → B) :
    Option ((I × H) × B) → Option ((I × H) × B) → Option ((I × H) × B)
  | none, none => none
  | none, some ((j,c),t) => embed j (q none (some (c,t)))
  | some ((i,a),s), none => embed i (q (some (a,s)) none)
  | some ((i,a),s), some ((j,c),t) =>
    if i = j then embed i (q (some (a,s)) (some (c,t)))
    else some (F.op (i,a) (j,c), b s t)

theorem fill_embed [DecidableEq I] (F : Frame I H) (q b)
    (hq : q none none = none) (i : I) (a c : Option (H × B)) :
    F.fill q b (embed i a) (embed i c) = embed i (q a c) := by
  cases a with
  | none => cases c <;> simp [embed, fill, hq]
  | some a => cases c <;> simp [embed, fill]

theorem fill_law [DecidableEq I] (F : Frame I H)
    (q : Option (H × B) → Option (H × B) → Option (H × B)) (b : B → B → B)
    (hq : Lawful q) (hb : Lawful b) (h0 : q none none = none) :
    Lawful (F.fill q b) := by
  have fiber (i : I) (a c : Option (H × B)) :
      F.fill q b (embed i c)
        (F.fill q b (embed i a) (F.fill q b (embed i a) (embed i c))) =
          embed i a := by
    rw [fill_embed _ _ _ h0, fill_embed _ _ _ h0, fill_embed _ _ _ h0, hq]
  rintro (_ | ⟨⟨i,a⟩,s⟩) (_ | ⟨⟨j,c⟩,t⟩)
  · rfl
  · exact fiber j none (some (c,t))
  · exact fiber i (some (a,s)) none
  · by_cases he : i = j
    · subst j
      exact fiber i (some (a,s)) (some (c,t))
    · have h1 := F.first (i,a) (j,c) he
      have h2 := F.second (i,a) (j,c) he
      simp only [fill, if_neg he, if_neg h1, if_neg h2, F.law (i,a) (j,c) he, hb]

theorem fill_idem [DecidableEq I] (F : Frame I H)
    (q : Option (H × B) → Option (H × B) → Option (H × B)) (b : B → B → B)
    (hq : Idem q) :
    Idem (F.fill q b) := by
  rintro (_ | ⟨⟨i,a⟩,s⟩)
  · rfl
  · simp [fill, hq, embed]

/-- The factor algebra need not be idempotent: squares are evaluated in the
enlarged hole, not in the factor algebra. -/
theorem model [DecidableEq I] (F : Frame I H)
    (hq : Model (Option (H × B)) true) (hb : Model B) :
    Model (Option ((I × H) × B)) true := by
  obtain ⟨q,hq,hqi⟩ := hq
  obtain ⟨b,hb,_⟩ := hb
  exact ⟨F.fill q b, F.fill_law q b hq hb (hqi rfl none),
    fun _ => F.fill_idem q b (hqi rfl)⟩

theorem models {k h m : ℕ} (F : Frame (Fin k) (Fin h))
    (hq : Model (Fin (h*m+1)) true) (hb : Law63.HasModel m) :
    Model (Fin (k*h*m+1)) true := by
  have hq' : Model (Option (Fin h × Fin m)) true := hq.of_card (by simp)
  exact (F.model hq' (model_of_hasModel hb)).relabel
    (Fintype.equivFinOfCardEq (by simp))

end Frame
end Spectrum.E63
