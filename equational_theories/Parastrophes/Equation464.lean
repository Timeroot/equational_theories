import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All
import equational_theories.Superposition
import equational_theories.ManuallyProved.Equation464Idempotent
import equational_theories.Parastrophes.Attributes

/-! E464 has surjective translations on both sides, without finiteness.
Its left and right bijectivity questions are equivalent. The infinite
idempotent countermodel imported above now refutes both universal claims. -/
namespace Parastrophes.Equation464
variable {G : Type*} [Magma G]

/-- A specified right inverse of left translation. -/
def sectionTerm (a x : G) : G := x ◇ (x ◇ (x ◇ a))

theorem left_section (h : Equation464 G) (a x : G) :
    a ◇ sectionTerm a x = x := (h x a).symm

theorem left_surjective (h : Equation464 G) (a : G) :
    Function.Surjective (fun x => a ◇ x) :=
  fun x => ⟨sectionTerm a x, left_section h a x⟩

/-- Three applications of the left section give a right section. -/
theorem right_section (h : Equation464 G) (a x : G) :
    sectionTerm x (sectionTerm x (sectionTerm x a)) ◇ a = x := by
  let t := sectionTerm x (sectionTerm x (sectionTerm x a))
  have hc : x ◇ (x ◇ (x ◇ t)) = a := by
    dsimp [t]
    rw [left_section h, left_section h, left_section h]
  have ht := h x t
  rw [hc] at ht
  exact ht.symm

theorem right_surjective (h : Equation464 G) (a : G) :
    Function.Surjective (fun x => x ◇ a) :=
  fun x => ⟨sectionTerm x (sectionTerm x (sectionTerm x a)), right_section h a x⟩

theorem right_injective_of_left (h : Equation464 G)
    (hl : ∀ a : G, Function.Injective (fun x => a ◇ x)) :
    ∀ a : G, Function.Injective (fun x => x ◇ a) := by
  intro a b c he
  let z := b ◇ a
  have hb : z ◇ (z ◇ (z ◇ b)) = a := hl b (h z b).symm
  have hc : z ◇ (z ◇ (z ◇ c)) = a := hl c ((h z c).symm.trans he)
  exact hl z (hl z (hl z (hb.trans hc.symm)))

theorem left_injective_of_right (h : Equation464 G)
    (hr : ∀ a : G, Function.Injective (fun x => x ◇ a)) :
    ∀ a : G, Function.Injective (fun x => a ◇ x) := by
  intro a b c he
  have hf : a ◇ (a ◇ (a ◇ b)) = a ◇ (a ◇ (a ◇ c)) :=
    congrArg (fun t => a ◇ (a ◇ t)) he
  apply hr (a ◇ (a ◇ (a ◇ b)))
  exact (h a b).symm.trans ((h a c).trans (congrArg (fun t => c ◇ t) hf.symm))

/-- For a fixed E464 model, either side's bijectivity settles both. -/
theorem left_iff_right (h : Equation464 G) :
    IsSideQuasigroup .left (inferInstance : Magma G) ↔
      IsSideQuasigroup .right (inferInstance : Magma G) := by
  constructor
  · intro hl a
    exact ⟨right_injective_of_left h (fun x => (hl x).1) a, right_surjective h a⟩
  · intro hr a
    exact ⟨left_injective_of_right h (fun x => (hr x).1) a, left_surjective h a⟩

/-- The fixed left-division term, whenever E464 has cancellative translations. -/
def leftDivisionTerm : FreeMagma (Fin 2) :=
  .Leaf 1 ⋆ (.Leaf 1 ⋆ (.Leaf 1 ⋆ .Leaf 0))

/-- Three successive applications of left division give right division.
This is a fixed multiplication term, independent of the model. -/
def rightDivisionTerm : FreeMagma (Fin 2) :=
  let u := leftDivisionTerm
  let v := u ⋆ (u ⋆ (u ⋆ .Leaf 0))
  v ⋆ (v ⋆ (v ⋆ .Leaf 0))

theorem left_division_of_injective (h : Equation464 G)
    (hl : ∀ a : G, Function.Injective (fun x => a ◇ x)) :
    IsDivision .left (inferInstance : Magma G)
      (termMagma inferInstance leftDivisionTerm) := by
  exact ⟨left_section h, fun a x => hl a (left_section h a (a ◇ x))⟩

theorem right_division_of_injective (h : Equation464 G)
    (hr : ∀ a : G, Function.Injective (fun x => x ◇ a)) :
    IsDivision .right (inferInstance : Magma G)
      (termMagma inferInstance rightDivisionTerm) := by
  exact ⟨fun x y => right_section h y x,
    fun x y => hr y (right_section h y (x ◇ y))⟩

/-- Conditional uniform recovery on arbitrary carriers. Either side's
bijectivity suffices, since E464 makes the two sides equivalent. -/
theorem divisions_of_leftQuasigroup (h : Equation464 G)
    (hq : IsSideQuasigroup .left (inferInstance : Magma G)) :
    IsDivision .left (inferInstance : Magma G)
      (termMagma inferInstance leftDivisionTerm) ∧
    IsDivision .right (inferInstance : Magma G)
      (termMagma inferInstance rightDivisionTerm) := by
  have hl := fun a => (hq a).1
  exact ⟨left_division_of_injective h hl,
    right_division_of_injective h (right_injective_of_left h hl)⟩

/-- With commutativity, every left translation has order dividing six.
This is a short equational replay of the Vampire derivation; no external
certificate or solver is needed to check it. -/
theorem commutative_period (h : Equation464 G) (comm : ∀ x y : G, x ◇ y = y ◇ x) (x y : G) :
    x ◇ (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y))))) = y := by
  have e5 (x0 x1 : G) : (x1 ◇ (x0 ◇ (x0 ◇ (x0 ◇ x1)))) = x0 := (h ..).symm
  have e6 (x0 x1 : G) : (x0 ◇ x1) = (x1 ◇ x0) := comm ..
  have e10 (x0 x1 : G) : (x0 ◇ (x1 ◇ (x1 ◇ (x0 ◇ x1)))) = x1 :=
    superpose e6 e5
  have e11 (x0 x1 : G) : ((x0 ◇ (x0 ◇ (x0 ◇ x1))) ◇ (x1 ◇ (x1 ◇ x0))) = x1 :=
    superpose e5 e5
  have e70 (x0 x1 : G) : (((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ x1))) ◇ (x1 ◇ x0)) = x1 :=
    superpose e10 e11
  have e72 (x0 x1 : G) : (x1 ◇ (x1 ◇ (x1 ◇ x0))) = (((x0 ◇ (x0 ◇ x1)) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ (x1 ◇ (x1 ◇ (x1 ◇ x0)))))) ◇ ((x1 ◇ (x1 ◇ (x1 ◇ x0))) ◇ x0)) :=
    superpose e11 e11
  have e84 (x0 x1 : G) : ((x0 ◇ (x0 ◇ x1)) ◇ (x1 ◇ (x1 ◇ (x1 ◇ x0)))) = x0 :=
    superpose e6 e11
  have e93 (x0 x1 : G) : (x1 ◇ (x1 ◇ (x1 ◇ x0))) = (((x1 ◇ (x1 ◇ (x1 ◇ x0))) ◇ x0) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ (x1 ◇ (x1 ◇ (x1 ◇ x0))))))) :=
    superpose e72 e6
  have e95 (x0 x1 : G) : ((x1 ◇ x0) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ x1)))) = x1 :=
    superpose e70 e6
  have e115 (x0 x1 : G) : (x1 ◇ (x1 ◇ (x1 ◇ x0))) = (((x1 ◇ (x1 ◇ (x1 ◇ x0))) ◇ x0) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ x0))) :=
    superpose e84 e93
  have e117 (x0 x1 : G) : ((x1 ◇ x0) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ (x1 ◇ (x0 ◇ (x0 ◇ (x1 ◇ x0))))))) = x1 :=
    superpose e6 e95
  have e134 (x0 x1 : G) : (x1 ◇ (x1 ◇ (x1 ◇ x0))) = (((x1 ◇ (x1 ◇ (x1 ◇ x0))) ◇ x0) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ (x0 ◇ (x0 ◇ (x0 ◇ x1))))) :=
    superpose e6 e115
  have e136 (x0 x1 : G) : ((x1 ◇ x0) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ x0))) = x1 :=
    superpose e10 e117
  have e149 (x0 x1 : G) : (x1 ◇ (x1 ◇ (x1 ◇ x0))) = ((x0 ◇ (x1 ◇ (x1 ◇ (x1 ◇ x0)))) ◇ ((x0 ◇ (x0 ◇ x1)) ◇ (x0 ◇ (x0 ◇ (x0 ◇ x1))))) :=
    superpose e6 e134
  have e151 (x0 x1 : G) : ((x1 ◇ x0) ◇ ((x0 ◇ (x0 ◇ (x1 ◇ x0))) ◇ (x0 ◇ (x0 ◇ (x0 ◇ (x1 ◇ x0)))))) = x1 :=
    superpose e6 e136
  have e158 (x0 x1 : G) : (x1 ◇ (x1 ◇ (x1 ◇ x0))) = (x1 ◇ ((x0 ◇ (x0 ◇ x1)) ◇ (x0 ◇ (x0 ◇ (x0 ◇ x1))))) :=
    superpose e5 e149
  have e1398 (x0 x1 : G) : (x0 ◇ (((x0 ◇ (x0 ◇ (x0 ◇ x1))) ◇ ((x0 ◇ (x0 ◇ (x0 ◇ x1))) ◇ x0)) ◇ ((x0 ◇ (x0 ◇ (x0 ◇ x1))) ◇ ((x0 ◇ (x0 ◇ (x0 ◇ x1))) ◇ ((x0 ◇ (x0 ◇ (x0 ◇ x1))) ◇ x0))))) = x1 :=
    superpose e5 e151
  have e1474 (x0 x1 : G) : (x0 ◇ (x0 ◇ (x0 ◇ (x0 ◇ (x0 ◇ (x0 ◇ x1)))))) = x1 :=
    superpose e1398 e158
  exact e1474 x y

/-- The commutative E464 case cannot provide an infinite collision model. -/
theorem commutative_left_bijective (h : Equation464 G)
    (comm : ∀ x y : G, x ◇ y = y ◇ x) (a : G) :
    Function.Bijective (fun x => a ◇ x) := by
  refine ⟨?_, left_surjective h a⟩
  intro b c he
  have hh := congrArg (fun z => a ◇ (a ◇ (a ◇ (a ◇ (a ◇ z))))) he
  simpa only [commutative_period h comm] using hh

/-- Under commutativity E669 becomes E464. -/
theorem of_commutative669 (h : Equation669 G)
    (comm : ∀ x y : G, x ◇ y = y ◇ x) : Equation464 G := by
  intro x y
  simpa only [comm (x ◇ y) x] using h x y

/-- Under commutativity E1075 becomes E464. -/
theorem of_commutative1075 (h : Equation1075 G)
    (comm : ∀ x y : G, x ◇ y = y ◇ x) : Equation464 G := by
  intro x y
  simpa only [comm (x ◇ (x ◇ y)) x] using h x y

/-- Under commutativity E1285 becomes E464. -/
theorem of_commutative1285 (h : Equation1285 G)
    (comm : ∀ x y : G, x ◇ y = y ◇ x) : Equation464 G := by
  intro x y
  have hh := h x y
  rw [comm (x ◇ y) x, comm (x ◇ (x ◇ y)) x] at hh
  exact hh

end Parastrophes.Equation464

namespace Parastrophes.Catalogue

/-- E464's infinite idempotent free-group model retains a row collision. -/
@[parastrophe_result] theorem not_leftQuasigroup464_all :
    ¬ SideQuasigroupLaw .all Law464 .left := by
  intro h
  obtain ⟨M,hM,_,hc⟩ := Eq464Idempotent.countermodel
  have hq := h (FreeGroup Nat) M trivial ((@Law464.models_iff _ M).mpr hM)
  exact hc (hq 1).1

/-- In E464, right bijectivity would imply left bijectivity. The same
infinite countermodel therefore refutes the right-side universal claim. -/
@[parastrophe_result] theorem not_rightQuasigroup464_all :
    ¬ SideQuasigroupLaw .all Law464 .right := by
  intro h
  obtain ⟨M,hM,_,hc⟩ := Eq464Idempotent.countermodel
  have hq := h (FreeGroup Nat) M trivial ((@Law464.models_iff _ M).mpr hM)
  have hl := (@Parastrophes.Equation464.left_iff_right (FreeGroup Nat) M hM).mpr hq
  exact hc (hl 1).1

end Parastrophes.Catalogue
