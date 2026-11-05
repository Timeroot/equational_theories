import equational_theories.Parastrophes.Equation872GaussianAffine
import equational_theories.Parastrophes.Equation872ImageCandidate

/-! The final 26-operation candidate, written with small auxiliary terms.
Its unrestricted converse is under investigation; no characterization attribute
is attached to the candidate. Research indices: 24237 and its renaming 24455. -/
namespace Parastrophes.Eq872FinalCandidate
open Law Eq872Image

def recovery {G : Type} (D : Magma G) (x : G) : G :=
  D.op (D.op (core D x) (core D x)) (D.op x (D.op x x))

def middle {G : Type} (D : Magma G) (a y u : G) : G :=
  D.op y (D.op (D.op a a) (D.op y (D.op a (D.op (D.op a a) u))))

def Candidate {G : Type} (D : Magma G) : Prop := ∀ x y z,
  x = D.op (middle D (D.op z x) y (D.op z (recovery D x))) (D.op z (D.op z x))

def candidateLaw : NatMagmaLaw :=
  AffineIdentityCertificate.identity (Eq872GaussianAffine.candidates26[0])

theorem models_iff {G : Type} (D : Magma G) :
    @satisfies _ G D candidateLaw ↔ Candidate D := by
  constructor
  · intro h x y z
    have he := h (fun n => if n=0 then x else if n=1 then y else z)
    simpa [candidateLaw, AffineIdentityCertificate.identity, Eq872GaussianAffine.candidates26,
      FreeMagma.fmapFreeMagma, FreeMagma.evalInMagma, middle, recovery, core] using he
  · intro h v
    simpa [candidateLaw, AffineIdentityCertificate.identity, Eq872GaussianAffine.candidates26,
      FreeMagma.fmapFreeMagma, FreeMagma.evalInMagma, middle, recovery, core] using h (v 0) (v 1) (v 2)

/-- The unary recovery term is the identity in every actual image. -/
theorem recovery_eq {G : Type} (D : Magma G) (h : InImage Law872 .left D) (x : G) :
    recovery D x = x := by
  obtain ⟨M, hM, hd⟩ := h
  have hh : InImage Law872 .left D := ⟨M,hM,hd⟩
  have hb := Eq872Image.forward M D hd ((@Law872.models_iff _ M).mp hM)
  have hcs := core_core_eq_square D hh (core D x)
  rw [core_core_eq_square D hh x] at hcs
  have he := hb.2 (D.op x x) x
  rw [hcs] at he
  have hi : Function.Injective (D.op x) := by
    intro a b hh
    have ht := congrArg (M.op x) hh
    simpa only [hd.1] using ht
  exact (hi he).symm

/-- Soundness of the candidate needs no finiteness assumption. -/
theorem forward {G : Type} (D : Magma G) (h : InImage Law872 .left D) : Candidate D := by
  obtain ⟨M,hM,hd⟩ := h
  have hh : InImage Law872 .left D := ⟨M,hM,hd⟩
  have hb := Eq872Image.forward M D hd ((@Law872.models_iff _ M).mp hM)
  have hi (z : G) : Function.Injective (D.op z) := by
    intro a b he
    have ht := congrArg (M.op z) he
    simpa only [hd.1] using ht
  have hm (a y : G) : middle D a y a = core D a := by
    have he := hb.2 (core D a) y
    rw [core_core_eq_square D hh a] at he
    exact he.symm
  intro x y z
  rw [recovery_eq D hh, hm]
  apply hi z
  exact hb.2 (D.op z x) z

/-- If the unary recovery identity can be proved from the candidate, row
injectivity follows immediately, without finiteness. -/
theorem left_injective_of_recovery {G : Type} (D : Magma G) (h : Candidate D)
    (hr : ∀ x, recovery D x=x) : ∀ z, Function.Injective (D.op z) := by
  intro z a b he
  have ha := h a z z
  have hb := h b z z
  rw [hr, he] at ha
  rw [hr] at hb
  exact ha.trans hb.symm

theorem left_quasigroup_of_recovery_fin {G : Type} [Finite G] (D : Magma G)
    (h : Candidate D) (hr : ∀ x, recovery D x=x) : IsSideQuasigroup .left D := by
  intro z
  have hi := left_injective_of_recovery D h hr z
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

/-- Idempotence makes the unary recovery term trivial. -/
theorem recovery_of_idempotent {G : Type} (D : Magma G)
    (hid : ∀ x, D.op x x=x) (x : G) : recovery D x=x := by
  simp only [recovery, core, hid]

/-- Substituting y=z*x gives an explicit left inverse to every row. -/
theorem inverse_of_idempotent {G : Type} (D : Magma G)
    (hid : ∀ x, D.op x x=x) (h : Candidate D) (x z : G) :
    x = D.op (D.op z x) (D.op z (D.op z x)) := by
  have he := h x (D.op z x) z
  simpa only [recovery, core, middle, hid] using he

/-- The candidate is sufficient in every finite idempotent magma. Reversing
its one-sided row inverse is the only use of finiteness. -/
theorem image_of_idempotent_fin {G : Type} [Finite G] (D : Magma G)
    (hid : ∀ x, D.op x x=x) (h : Candidate D) : InImage Law872 .left D := by
  have hq := left_quasigroup_of_recovery_fin D h (recovery_of_idempotent D hid)
  apply (characterizes_fin D).mp
  constructor
  · intro x
    change x = D.op x (core D x)
    simp only [core, hid]
  · intro x y
    obtain ⟨a, ha⟩ := (hq y).2 x
    have he := inverse_of_idempotent D hid h a y
    rw [ha] at he
    have ht := congrArg (D.op y) he
    rw [ha] at ht
    simpa only [core, hid] using ht

theorem characterizes_idempotent_fin {G : Type} [Finite G] (D : Magma G)
    (hid : ∀ x, D.op x x=x) : Candidate D ↔ InImage Law872 .left D :=
  ⟨image_of_idempotent_fin D hid, forward D⟩
end Parastrophes.Eq872FinalCandidate
