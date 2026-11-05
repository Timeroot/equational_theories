import equational_theories.Parastrophes.Equation917DoubleCandidate

/-!
# An unproved 46-operation compression for E917

This candidate uses two independently parameterized copies of B1 and one
copy of B2. All eight variables are universally quantified. Its forward
implication and common-permutation reduction are proved below. The general
converse is NOT proved, and no characterization attribute is attached.

With the notation of Equation917DoubleCandidate, put
  K=(B1(x,z,w)*(B1(x,v,t)*U(x)))*B2(x,r,s).
The proposed equation is x=y*(K*(x*y)). The three bridge terms have twelve
operations each, U has four, joining them adds three, and the outer frame
adds three: 3*12+4+3+3=46.

Unlike the refuted 34-operation placements, this arrangement has survived
the recorded affine tests and extensions of the ten saved finite seed
tables. These restricted tests are evidence only, not a converse proof.
-/
namespace Parastrophes.Eq917Image.TripleCandidate
open DoubleCandidate (U B1 B2)
open SplitCandidate (F)

variable {G : Type} (D : Magma G)

def K (x z w v t r s : G) :=
  D.op (D.op (B1 D x z w) (D.op (B1 D x v t) (U D x))) (B2 D x r s)

def Identity : Prop := ∀ x y z w v t r s,
  x = D.op y (D.op (K D x z w v t r s) (D.op x y))

theorem of_basis (h : Basis D) : Identity D := by
  have hf (x z) : F D x z = x := (h.2 x z).symm
  have hb1 (x z w) : B1 D x z w = x := by
    simp only [B1, hf]
    exact (h.2 x z).symm
  have hb2 (x v t) : B2 D x v t = x := by
    simp only [B2, hf]
    exact (h.2 x v).symm
  have hu (x : G) : U D x = x := (h.1 x).symm
  intro x y z w v t r s
  simp only [K, hb1, hb2, hu]
  exact h.2 x y

theorem quasigroup [Finite G] (h : Identity D) : IsQuasigroup D :=
  Candidate.quasigroup_of_frame D (fun x z => K D x z x x x x x)
    (fun x y z => h x y z x x x x x)

theorem B1_independent [Finite G] (h : Identity D) (x z w z' w' : G) :
    B1 D x z w = B1 D x z' w' := by
  have hq := quasigroup D h
  have he := (h x x z w x x x x).symm.trans (h x x z' w' x x x x)
  have hk := (hq.2 (D.op x x)).1 ((hq.1 x).1 he)
  exact (hq.2 (D.op (B1 D x x x) (U D x))).1 ((hq.2 (B2 D x x x)).1 hk)

theorem F_independent [Finite G] (h : Identity D) (x z w : G) :
    F D x z = F D x w := by
  apply ((quasigroup D h).2 (D.op (core D x) (D.op x x))).1
  exact B1_independent D h x x z x w

/-- This is the precise finite reduction available for the new candidate.
The common permutations are not asserted to be identity maps. -/
theorem common_maps [Finite G] (h : Identity D) :
    ∃ g f : G → G, Function.Bijective g ∧ Function.Bijective f ∧
      (∀ x z, F D x z = g x) ∧
      (∀ x y, D.op (g x) y = f (D.op x y)) ∧
      (∀ x z w, B1 D x z w = f (g x)) ∧
      (∀ x v t, f (B2 D x v t) = g x) := by
  let g := fun x => F D x x
  let b := fun x => B1 D x x x
  have hf (x z) : F D x z = g x := F_independent D h x z x
  have hb (x y) : D.op (g y) (D.op (core D x) (D.op x y)) = b x :=
    B1_independent D h x y y x x
  obtain ⟨f, hg, hfb, hbf, ha⟩ := SplitCandidate.common_permutations D
    (core D) g b (quasigroup D h) hf hb
  refine ⟨g, f, hg, hfb, hf, ha, ?_, ?_⟩
  · intro x z w
    exact (B1_independent D h x z w x x).trans (hbf x)
  · intro x v t
    simp only [B2, hf]
    rw [← ha]
    exact hf x (g v)

theorem basis_of_fixed_point [Finite G] (h : Identity D) (a : G)
    (hfix : F D a a = a) : Basis D := by
  obtain ⟨g, f, _, _, hf, ha, hb1, hb2⟩ := common_maps D h
  have hq := quasigroup D h
  obtain ⟨hg, hfi⟩ := SplitCandidate.autotopy_fixed_point D g f hq ha a
    ((hf a a).symm.trans hfix)
  have hF (x y) : F D x y = x := (hf x y).trans (hg x)
  have hB1 (x z w) : B1 D x z w = x := by simpa only [hg, hfi] using hb1 x z w
  have hB2 (x v t) : B2 D x v t = x := by simpa only [hg, hfi] using hb2 x v t
  refine ⟨?_, fun x y => (hF x y).symm⟩
  intro x
  have hk : K D x x x x x x x = core D x := by
    apply (hq.2 (D.op x x)).1
    apply (hq.1 x).1
    exact (h x x x x x x x x).symm.trans (hF x x).symm
  have hu : U D x = x := by
    apply (hq.1 x).1
    apply (hq.1 x).1
    apply (hq.2 x).1
    simpa only [K, hB1, hB2, core] using hk
  exact hu.symm

end Parastrophes.Eq917Image.TripleCandidate
