import equational_theories.Parastrophes.Equation917SplitCandidate

/-!
# A refuted 34-operation E917 compression candidate

This is candidate 5 of the double-bridge family. All 24 placements have explicit
affine counterexamples. For this placement, Equation917DoubleCounterexample
proves the counterexample 43*x + 209*y + 1 on ZMod 251. The present file retains
the valid forward implication, finite quasigroup status, and reduction to two
common permutations. No characterization attribute is attached, and these
conditional results do not close a catalogue field.

Put c(x)=(x*(x*x))*x and F(x,z)=z*(c(x)*(x*z)). The two bridges are
  B1(x,z,w)=F(z,w)*(c(x)*(x*z)),
  B2(x,v,t)=v*(c(x)*(x*F(v,t))).
With U(x)=x*c(x), the candidate is
  x=y*(((x*(B2(x,v,t)*B1(x,z,w)))*U(x))*(x*y)).

Independent bridge parameters are what permit cancellation. They imply that
F(x,-) is a common permutation g(x). A second permutation f satisfies
m(g(x),y)=f(m(x,y)); the bridges then equal f(g(x)) and f⁻¹(g(x)). Finite
surjectivity of both maps must be retained in any attempt at the converse.
-/
namespace Parastrophes.Eq917Image.DoubleCandidate
open SplitCandidate (F)

variable {G : Type} (D : Magma G)

def U (x : G) := D.op x (core D x)
def B1 (x z w : G) := D.op (F D z w) (D.op (core D x) (D.op x z))
def B2 (x v t : G) := D.op v (D.op (core D x) (D.op x (F D v t)))
def K (x z w v t : G) := D.op (D.op x (D.op (B2 D x v t) (B1 D x z w))) (U D x)
def Identity : Prop := ∀ x y z w v t,
  x = D.op y (D.op (K D x z w v t) (D.op x y))

theorem of_basis (h : Basis D) : Identity D := by
  have hf (x z) : F D x z = x := (h.2 x z).symm
  have hb1 (x z w) : B1 D x z w = x := by
    simp only [B1, hf]
    exact (h.2 x z).symm
  have hb2 (x v t) : B2 D x v t = x := by
    simp only [B2, hf]
    exact (h.2 x v).symm
  have hu (x : G) : D.op x (core D x) = x := (h.1 x).symm
  intro x y z w v t
  simp only [K, hb1, hb2, U, hu]
  exact h.2 x y

theorem quasigroup [Finite G] (h : Identity D) : IsQuasigroup D :=
  Candidate.quasigroup_of_frame D (fun x z => K D x z x x x)
    (fun x y z => h x y z x x x)

theorem K_independent [Finite G] (h : Identity D) (x z w v t z' w' v' t' : G) :
    K D x z w v t = K D x z' w' v' t' := by
  have hq := quasigroup D h
  apply (hq.2 (D.op x x)).1
  apply (hq.1 x).1
  exact (h x x z w v t).symm.trans (h x x z' w' v' t')

theorem B1_independent [Finite G] (h : Identity D) (x z w z' w' : G) :
    B1 D x z w = B1 D x z' w' := by
  have hq := quasigroup D h
  have he := K_independent D h x z w x x z' w' x x
  exact (hq.1 (B2 D x x x)).1 ((hq.1 x).1 ((hq.2 (U D x)).1 he))

theorem B2_independent [Finite G] (h : Identity D) (x v t v' t' : G) :
    B2 D x v t = B2 D x v' t' := by
  have hq := quasigroup D h
  have he := K_independent D h x x x v t x x v' t'
  exact (hq.2 (B1 D x x x)).1 ((hq.1 x).1 ((hq.2 (U D x)).1 he))

theorem F_independent [Finite G] (h : Identity D) (x z w : G) :
    F D x z = F D x w := by
  apply ((quasigroup D h).2 (D.op (core D x) (D.op x x))).1
  exact B1_independent D h x x z x w

/-- This is the finite common-map reduction, not a proof that the maps are
identity maps. It exposes all bijectivity assumptions required downstream. -/
theorem common_maps [Finite G] (h : Identity D) :
    ∃ g f : G → G, Function.Bijective g ∧ Function.Bijective f ∧
      (∀ x z, F D x z = g x) ∧
      (∀ x y, D.op (g x) y = f (D.op x y)) ∧
      (∀ x z w, B1 D x z w = f (g x)) ∧
      (∀ x v t, f (B2 D x v t) = g x) := by
  let g := fun x => F D x x
  let b := fun x => B1 D x x x
  have hf (x z) : F D x z = g x := F_independent D h x z x
  have hb (x y) : D.op (g y) (D.op (core D x) (D.op x y)) = b x := by
    change B1 D x y y = b x
    exact B1_independent D h x y y x x
  obtain ⟨f, hg, hfb, hbf, ha⟩ := SplitCandidate.common_permutations D
    (core D) g b (quasigroup D h) hf hb
  refine ⟨g, f, hg, hfb, hf, ha, ?_, ?_⟩
  · intro x z w
    exact (B1_independent D h x z w x x).trans (hbf x)
  · intro x v t
    rw [B2_independent D h x v t x x]
    change f (D.op x (D.op (core D x) (D.op x (g x)))) = g x
    rw [← ha]
    exact hf x (g x)

/-- A single fixed point of the common map completes the converse. This extra
hypothesis is essential: in the ZMod 251 counterexample the common map is
x ↦ x + 211 and has no fixed point. -/
theorem basis_of_fixed_point [Finite G] (h : Identity D) (a : G)
    (hfix : F D a a = a) : Basis D := by
  obtain ⟨g, f, _, _, hf, ha, hb1, hb2⟩ := common_maps D h
  have hq := quasigroup D h
  have hga : g a = a := (hf a a).symm.trans hfix
  obtain ⟨hg, hfi⟩ := SplitCandidate.autotopy_fixed_point D g f hq ha a hga
  have hF (x y) : F D x y = x := (hf x y).trans (hg x)
  have hB1 (x z w) : B1 D x z w = x := by simpa only [hg, hfi] using hb1 x z w
  have hB2 (x v t) : B2 D x v t = x := by simpa only [hg, hfi] using hb2 x v t
  refine ⟨?_, fun x y => (hF x y).symm⟩
  intro x
  have hk : K D x x x x x = core D x := by
    apply (hq.2 (D.op x x)).1
    apply (hq.1 x).1
    exact (h x x x x x x).symm.trans (hF x x).symm
  have hu : U D x = x := by
    apply (hq.1 (D.op x (D.op x x))).1
    simpa only [K, hB1, hB2, core] using hk
  exact hu.symm

/-- In particular, the candidate characterizes the image on finite
idempotent magmas; one idempotent element already suffices for the converse. -/
theorem basis_of_idempotent [Finite G] (h : Identity D) (a : G)
    (haa : D.op a a = a) : Basis D := by
  apply basis_of_fixed_point D h a
  simp only [SplitCandidate.F, core, haa]

end Parastrophes.Eq917Image.DoubleCandidate
