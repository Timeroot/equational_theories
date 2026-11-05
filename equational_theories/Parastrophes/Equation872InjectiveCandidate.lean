import equational_theories.Parastrophes.Equation872ImageBasis
import equational_theories.Parastrophes.Equation872ImageShape

/-!
# An E872 candidate which supplies its own row cancellation

This candidate is REFUTED by the six-element model in
`Equation872InjectiveCounterexample.lean`; it is not a catalogue
characterization. The forward implication and reductions below remain valid.
Write
`c(x)=x*((x*x)*x)`, `u(x)=x*c(x)`,
`a(x)=x*((x*x)*u(x))`, and `h(z,y)=y*(c(z)*(u(y)*z))`.
The proposed identity is

    x = a(z*x) * (h(z,y) * (z*x)).

It has 28 operations after expansion. Unlike the earlier 26-operation
candidate, it makes every row injective immediately: all occurrences of x
on the right pass through z*x. On finite carriers it therefore supplies
actual division and can be rewritten with z*x as an independent variable.
The converse is proved below for idempotent magmas only; the general
converse is false.

The general frame lemmas retain arbitrary A and H. In particular, independent
parameters identify the ROWS indexed by H(z,y), not the indices themselves.
Confusing these assertions would incorrectly exclude repeated-row examples.
-/
namespace Parastrophes.Eq872InjectiveCandidate
open Law Eq872Image

variable {G : Type} (D : Magma G)

def Frame (A : G → G) (H : G → G → G) : Prop := ∀ x y z,
  x = D.op (A (D.op z x)) (D.op (H z y) (D.op z x))

theorem frame_injective (A : G → G) (H : G → G → G)
    (h : Frame D A H) (z : G) : Function.Injective (D.op z) := by
  intro x x' he
  have hx := h x z z
  rw [he] at hx
  exact hx.trans (h x' z z).symm

theorem frame_rows_fin [Finite G] (A : G → G) (H : G → G → G)
    (h : Frame D A H) : IsSideQuasigroup .left D := by
  intro z
  have hi := frame_injective D A H h z
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The only use of finiteness is making the row's range the whole carrier. -/
theorem frame_normalized_fin [Finite G] (A : G → G) (H : G → G → G)
    (h : Frame D A H) (x y z : G) :
    D.op z (D.op (A x) (D.op (H z y) x)) = x := by
  obtain ⟨v, rfl⟩ := (frame_rows_fin D A H h z).2 x
  exact congrArg (D.op z) (h v y z).symm

/-- The frame gives an explicit inverse without assuming an image law. -/
theorem frame_division_fin [Finite G] (A : G → G) (H : G → G → G)
    (h : Frame D A H) :
    IsDivision .left D ⟨fun z x => D.op (A x) (D.op (H z z) x)⟩ := by
  exact ⟨fun z x => frame_normalized_fin D A H h x z z,
    fun z x => (h x z z).symm⟩

/-- Cancellation gives equality of complete row maps, not of row indices. -/
theorem frame_same_rows_fin [Finite G] (A : G → G) (H : G → G → G)
    (h : Frame D A H) (z y y' : G) : D.op (H z y) = D.op (H z y') := by
  funext x
  have he := (frame_normalized_fin D A H h x y z).trans
    (frame_normalized_fin D A H h x y' z).symm
  exact frame_injective D A H h (A x) (frame_injective D A H h z he)

/-- The induced map on distinct rows is injective. It need not be an
injective map on the underlying elements. -/
theorem frame_row_eq_iff_fin [Finite G] (A : G → G) (H : G → G → G)
    (h : Frame D A H) (z z' y : G) :
    D.op (H z y) = D.op (H z' y) ↔ D.op z = D.op z' := by
  constructor
  · intro he
    funext v
    have hv := h v y z
    rw [he] at hv
    exact (frame_normalized_fin D A H h (D.op z v) y z').symm.trans
      (congrArg (D.op z') hv.symm)
  · intro he
    funext x
    have hz := frame_normalized_fin D A H h x y z
    rw [he] at hz
    exact frame_injective D A H h (A x) (frame_injective D A H h z'
      (hz.trans (frame_normalized_fin D A H h x y z').symm))

/-- Finiteness makes the induced injection on the set of rows a permutation.
The inverse equations here are row equalities, not point equalities. -/
theorem frame_row_inverse_fin [Finite G] (A : G → G) (H : G → G → G)
    (h : Frame D A H) (o : G) : ∃ j : G → G,
    (∀ z, D.op (H (j z) o) = D.op z) ∧
      (∀ z, D.op (j (H z o)) = D.op z) := by
  classical
  have hp := Eq872ImageShape.row_predecessor D A (fun z => H z o)
    (frame_rows_fin D A H h)
    (fun x z => (frame_normalized_fin D A H h x o z).symm)
  let j := fun z => Classical.choose (hp z)
  have hj (z : G) : D.op (H (j z) o) = D.op z :=
    funext (Classical.choose_spec (hp z))
  exact ⟨j, hj, fun z => (frame_row_eq_iff_fin D A H h _ _ o).mp (hj (H z o))⟩

def unit (x : G) : G := D.op x (core D x)
def adjustedCore (x : G) : G := D.op x (D.op (D.op x x) (unit D x))
def bridge (z y : G) : G := D.op y (D.op (core D z) (D.op (unit D y) z))
def Candidate : Prop := Frame D (adjustedCore D) (bridge D)

/-- Soundness needs no finiteness hypothesis. -/
theorem forward (h : InImage Law872 .left D) : Candidate D := by
  obtain ⟨M, hm, hd⟩ := h
  have hb := Eq872Image.forward M D hd ((@Law872.models_iff G M).mp hm)
  have hu (x : G) : unit D x = x := (hb.1 x).symm
  have ha (x : G) : adjustedCore D x = core D x := by
    simp only [adjustedCore, hu, core]
  have hh (z y : G) : bridge D z y = z := by
    simp only [bridge, hu]
    exact (hb.2 z y).symm
  intro x y z
  rw [ha, hh]
  exact (multiplication_eq M D hd ((@Law872.models_iff G M).mp hm)
    z (D.op z x)).symm.trans (hd.1 z x) |>.symm

theorem rows_fin [Finite G] (h : Candidate D) : IsSideQuasigroup .left D :=
  frame_rows_fin D _ _ h

theorem characterizes_idempotent_fin [Finite G]
    (hid : ∀ x, D.op x x = x) : Candidate D ↔ InImage Law872 .left D := by
  refine ⟨fun h => (characterizes_fin D).mp ⟨?_, ?_⟩, forward D⟩
  · intro x
    change x = D.op x (core D x)
    simp only [core, hid]
  · intro x y
    have he := frame_normalized_fin D _ _ h x y y
    simpa only [adjustedCore, bridge, unit, core, hid] using he.symm

end Parastrophes.Eq872InjectiveCandidate
