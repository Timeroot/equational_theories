import equational_theories.Parastrophes.Equation872ImageBasis
import Mathlib.Tactic.Abel

/-!
# An E872 image candidate and a restricted converse

The 20-operation identity below is candidate 3652 in the 2026-10-29 rewrite
audit. It holds in every left-division image of E872. A 25-element counterexample
to its general converse is in `Equation872ImageCandidateCounterexample.lean`.
Here we prove the converse when all rows are commuting involutions. This
includes every operation `t(x)+y` over an abelian group of exponent two, with
an arbitrary function `t`, on finite or infinite carriers.
-/
namespace Parastrophes.Eq872ImageCandidate
open Law Eq872Image

def middle {G : Type} (D : Magma G) (x z : G) : G :=
  D.op z (D.op (D.op x x) (D.op z (core D x)))

def index {G : Type} (D : Magma G) (z y : G) : G :=
  D.op (core D (D.op z y)) (D.op z (D.op z y))

def Candidate {G : Type} (D : Magma G) : Prop :=
  ∀ x y z, x = D.op y (D.op (middle D x z) (D.op (index D z y) x))

theorem forward_of_image {G : Type} (D : Magma G)
    (hD : InImage Law872 .left D) : Candidate D := by
  obtain ⟨M, hM, hd⟩ := hD
  have h := Eq872Image.forward M D hd ((@Law872.models_iff G M).mp hM)
  have hi (z : G) : Function.Injective (D.op z) := by
    intro a b he
    have ht := congrArg (M.op z) he
    simpa only [hd.1] using ht
  have hk (x z : G) : middle D x z = core D x := by
    have he := (h.2 (core D x) z).symm
    rwa [core_core_eq_square D ⟨M, hM, hd⟩ x] at he
  have ht (z y : G) : index D z y = y := by
    apply hi z
    exact (h.2 (D.op z y) z).symm
  intro x y z
  rw [hk, ht]
  exact h.2 x y

theorem forward {G : Type} [Finite G] (D : Magma G) (h : Basis D) : Candidate D :=
  forward_of_image D ((characterizes_fin D).mp h)

/-- The outer variable supplies row surjectivity directly. -/
theorem left_quasigroup_fin {G : Type} [Finite G] (D : Magma G)
    (h : Candidate D) : IsSideQuasigroup .left D := by
  intro y
  have hs : Function.Surjective (D.op y) := fun x => ⟨_, (h x y x).symm⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

/-- For commuting involutive rows, the candidate forces the exact image basis.
The auxiliary map `U(x)=(x*x)*x` is a central involution. The candidate then
identifies the row at `U(x)`, which forces `U(x)=x`. -/
theorem basis_of_commuting_involutions {G : Type} (D : Magma G)
    (hi : ∀ x y, D.op x (D.op x y) = y)
    (hc : ∀ x y z, D.op x (D.op y z) = D.op y (D.op x z))
    (h : Candidate D) : Basis D := by
  let S (x : G) := D.op x x
  let U (x : G) := D.op (S x) x
  have hK (x z : G) : middle D x z = S x := by
    unfold middle
    rw [hc z (D.op x x), hi]
    change D.op (S x) (D.op x (D.op (S x) x)) = S x
    rw [hc (S x) x, hi]
  have hcore (x : G) : core D x = S (S x) := hc x (S x) x
  have hR (z y x : G) : D.op (index D z y) x = D.op y (U x) := by
    have he := congrArg (fun v => D.op (S x) (D.op y v)) (h x y z)
    simp only [hK, hi] at he
    exact he.symm.trans (hc (S x) y x)
  have hrepr (a b x : G) : U x = D.op a (D.op (index D b a) x) := by
    rw [hR, hi]
  have hUc (a x : G) : U (D.op a x) = D.op a (U x) := by
    rw [hrepr a a (D.op a x), hrepr a a x, hc (index D a a) a x]
  have hUU (x : G) : U (U x) = x := by
    rw [hrepr x x (U x), hrepr x x x, hc (index D x x) x, hi, hi]
  have hUs (x : G) : U (S x) = core D x := hUc x x
  have hSU (x : G) : D.op (S x) (U x) = x :=
    (hUc (S x) x).symm.trans (hUU x)
  have hcS (x : G) : core D (S x) = S x := by
    change D.op (S x) (U (S x)) = S x
    rw [hUs]
    change D.op (S x) (D.op x (U x)) = S x
    rw [hc (S x) x, hSU]
  have hIx (x : G) : index D x x = U x := by
    change D.op (core D (S x)) (D.op x (D.op x x)) = U x
    rw [hi, hcS]
  have hUrow (x y : G) : D.op (U x) y = D.op x (U y) := by
    have he := hR x x y
    rwa [hIx] at he
  have hfix (x : G) : D.op (core D x) x = x := by
    rw [← hUs, hUrow, hSU]
  have hU (x : G) : U x = x := by
    calc
      U x = D.op x (core D x) := (hi x (U x)).symm
      _ = D.op x (U (S x)) := congrArg (D.op x) (hUs x).symm
      _ = D.op x (D.op (core D x) (S x)) := by rw [hcore]
      _ = D.op (core D x) (D.op x (S x)) := hc x (core D x) (S x)
      _ = D.op (core D x) x := by dsimp [S]; rw [hi]
      _ = x := hfix x
  constructor
  · intro x
    change x = D.op x (core D x)
    change x = D.op x (D.op x (U x))
    rw [hi, hU]
  · intro x y
    rw [hc y (core D x), hi, hfix]

/-- The exact image equivalence within the commuting-involution class, on
arbitrary carriers. The assumptions concern the candidate division operation. -/
theorem characterizes_commuting_involutions {G : Type} (D : Magma G)
    (hi : ∀ x y, D.op x (D.op x y) = y)
    (hc : ∀ x y z, D.op x (D.op y z) = D.op y (D.op x z)) :
    Candidate D ↔ InImage Law872 .left D := by
  have hd : IsDivision .left D D := ⟨hi, hi⟩
  exact ⟨fun h => ⟨D, (@Law872.models_iff G D).mpr
      (backward D D hd (basis_of_commuting_involutions D hi hc h)), hd⟩,
    forward_of_image D⟩

/-- Arbitrary functions are allowed; this need not be an affine operation. -/
@[implicit_reducible] def translation {G : Type} [AddCommGroup G] (t : G → G) :
    Magma G := ⟨fun x y => t x + y⟩

/-- A concrete family covered by the general commuting-row theorem. -/
theorem characterizes_boolean_translations {G : Type} [AddCommGroup G]
    (t : G → G) (h₂ : ∀ x : G, x + x = 0) :
    Candidate (translation t) ↔ InImage Law872 .left (translation t) := by
  apply characterizes_commuting_involutions
  · intro x y
    change t x + (t x + y) = y
    rw [← add_assoc, h₂, zero_add]
  · intro x y z
    change t x + (t y + z) = t y + (t x + z)
    abel

/-- info: 'Parastrophes.Eq872ImageCandidate.characterizes_commuting_involutions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms characterizes_commuting_involutions

end Parastrophes.Eq872ImageCandidate
