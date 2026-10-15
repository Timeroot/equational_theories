import equational_theories.Definability.RecoverySubmagmas
import Mathlib.Tactic.FinCases

/-! A six-element E960 obstruction to term-structural recovery through E72.
The source has exactly three unary term operations. A nonidentity square map
of an E72 companion then forces every row to be the same permutation. -/
open Law Law.MagmaLaw
namespace SixElementCyclicRecovery
abbrev Point := Fin 6

def q : Point → Point := ![2,3,4,5,0,1]
def q2 (x : Point) : Point := q (q x)
def diagonal (reverse : Bool) : Point → Point := if reverse then q2 else q

theorem period : ∀ x, q (q (q x)) = x := by decide
theorem fourth : ∀ x, q2 (q2 x) = q x := by decide
theorem diagonal_period : ∀ r x, diagonal r (diagonal r (diagonal r x)) = x := by decide

def row (a b : Point) : Point → Point := ![a,b,q a,q b,q2 a,q2 b]

/-- Commutation leaves just two entries to choose. This checks 432 small cases,
not the 6^36 possible multiplication tables. -/
theorem row_check : ∀ (r : Bool) (y a b : Point),
    row a b y = diagonal r y →
    (∀ x, row a b (row a b (diagonal r x)) = x) →
    ∀ x, row a b x = diagonal r x := by decide

theorem row_of_commutes (f : Point → Point) (h : ∀ x, f (q x) = q (f x)) :
    f = row (f 0) (f 1) := by
  funext x
  fin_cases x
  · rfl
  · rfl
  · exact h 0
  · exact h 1
  · exact (h 2).trans (congrArg q (h 0))
  · exact (h 3).trans (congrArg q (h 1))

/-- If f²q=id and q³=id, then f commutes with q. -/
theorem row_commutes {G : Type} (f p : G → G)
    (hp : ∀ x, p (p (p x)) = x) (h : ∀ x, f (f (p x)) = x) :
    ∀ x, f (p x) = p (f x) := by
  have h2 (x : G) : f (f x) = p (p x) := by
    simpa only [hp] using h (p (p x))
  have hc2 (x : G) : f (p (p x)) = p (p (f x)) :=
    (congrArg f (h2 x).symm).trans (h2 (f x))
  intro x
  calc
    f (p x) = f (p (p (p (p x)))) := congrArg f (hp (p x)).symm
    _ = p (p (f (p (p x)))) := hc2 (p (p x))
    _ = p (p (p (p (f x)))) := congrArg (fun z => p (p z)) (hc2 x)
    _ = p (f x) := hp (p (f x))

theorem commutes_q_of_q2 (f : Point → Point) (h : ∀ x, f (q2 x) = q2 (f x)) :
    ∀ x, f (q x) = q (f x) := by
  intro x
  calc
    f (q x) = f (q2 (q2 x)) := congrArg f (fourth x).symm
    _ = q2 (f (q2 x)) := h (q2 x)
    _ = q2 (q2 (f x)) := congrArg q2 (h x)
    _ = q (f x) := fourth (f x)

theorem target_rows (N : Magma Point) (h : @Equation72 Point N) (r : Bool)
    (hd : ∀ x, N.op x x = diagonal r x) : ∀ x y, N.op x y = diagonal r y := by
  intro y z
  let f := N.op y
  have hh (x : Point) : f (f (diagonal r x)) = x := by
    simpa only [← hd] using (h x y).symm
  have hc := row_commutes f (diagonal r) (diagonal_period r) hh
  have hcq : ∀ x, f (q x) = q (f x) := by
    cases r
    · exact hc
    · exact commutes_q_of_q2 f hc
  have he := row_of_commutes f hcq
  have hdiag : row (f 0) (f 1) y = diagonal r y := by
    rw [← he]
    exact hd y
  have hrow : ∀ x, row (f 0) (f 1) (row (f 0) (f 1) (diagonal r x)) = x := by
    simpa only [← he] using hh
  simpa only [← he] using row_check r y (f 0) (f 1) hdiag hrow z

@[implicit_reducible] def source : Magma Point :=
  ⟨![![2,3,4,5,0,1], ![2,3,0,5,4,1], ![2,3,4,5,0,1],
      ![4,3,2,5,0,1], ![2,3,4,5,0,1], ![0,3,4,5,2,1]]⟩

theorem source_law : @Equation960 Point source := by decide

def unary (k : Fin 3) (x : Point) : Point := ![x,q x,q2 x] k
def next : Fin 3 → Fin 3 := ![1,2,0]
theorem unary_closed : ∀ i j x,
    source.op (unary i x) (unary j x) = unary (next j) x := by decide

def UnaryDiagonal (f : Point → Point → Point) : Prop :=
  ∃ k : Fin 3, ∀ x, f x x = unary k x

theorem unary_invariant : source.IsCloneInvariant UnaryDiagonal where
  fst := ⟨0,fun _ => rfl⟩
  snd := ⟨0,fun _ => rfl⟩
  comp := by
    rintro f g ⟨i,hi⟩ ⟨j,hj⟩
    refine ⟨next j, ?_⟩
    intro x
    change source.op (f x x) (g x x) = _
    rw [hi,hj]
    exact unary_closed i j x

def Independent (f : Point → Point → Point) : Prop :=
  (∀ a b c, f a b = f a c) ∨ (∀ a b c, f a c = f b c)

theorem independent_invariant (N : Magma Point) (d : Point → Point)
    (h : ∀ x y, N.op x y = d y) : N.IsCloneInvariant Independent where
  fst := Or.inl (fun _ _ _ => rfl)
  snd := Or.inr (fun _ _ _ => rfl)
  comp := by
    rintro f g _ (hl | hr)
    · left
      intro a b c
      change N.op (f a b) (g a b) = N.op (f a c) (g a c)
      rw [h,h,hl]
    · right
      intro a b c
      change N.op (f a c) (g a c) = N.op (f b c) (g b c)
      rw [h,h,hr]

theorem no_recovery (N : Magma Point) (d : Point → Point)
    (h : ∀ x y, N.op x y = d y)
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ source.FinArityOp) : False := by
  rcases (independent_invariant N d h).of_termDefinable hr with hl | hr
  · have hh := hl 0 0 1
    exact (by decide : (2 : Point) ≠ 3) hh
  · have hh := hr 0 1 2
    exact (by decide : (4 : Point) ≠ 0) hh

theorem Equation72_not_termStructuralFromFin_Equation960 :
    ¬ Law72.TermStructuralFromFin Law960 := by
  intro h
  obtain ⟨N,hN,hf,hr⟩ := h source ((@Law960.models_iff Point source).mpr source_law)
  obtain ⟨k,hk⟩ := unary_invariant.of_termDefinable hf
  have hn := (@Law72.models_iff Point N).mp hN
  fin_cases k
  · have hi : N.op 0 0 = 0 := hk 0
    have hh := RecoverySubmagmas.idempotent_of_termDefinable 0 hr hi
    exact (by decide : (2 : Point) ≠ 0) hh
  · exact no_recovery N (diagonal false) (target_rows N hn false hk) hr
  · exact no_recovery N (diagonal true) (target_rows N hn true hk) hr

/-- info: 'SixElementCyclicRecovery.Equation72_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation72_not_termStructuralFromFin_Equation960
end SixElementCyclicRecovery
