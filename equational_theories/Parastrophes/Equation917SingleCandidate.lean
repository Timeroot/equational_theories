import equational_theories.Parastrophes.Equation917ImageBasis

/-!
# What a refuted E917 image-compression candidate still forces

Put c(x)=(x*(x*x))*x and u(x)=x*c(x). The proposed single identity is

    x = y*((u(z)*(c(c(x))*(c(x)*z)))*(x*y)).

It has 28 operations after expansion. Every actual division image satisfies
it, and every finite model is a quasigroup. The inner bridge is independent
of z. Nevertheless the converse is FALSE: the independently checked order-25
central extension in `data/parastrophes/e917_image_compression_20261103.json`
satisfies this identity and E1020 but fails the cross identity. That research
counterexample is not itself formalized here. Accordingly there is no
characterization attribute on this candidate. The lemmas below are ordinary
Lean proofs and do not depend on the model search.
-/
namespace Parastrophes.Eq917Image.Candidate

variable {G : Type} (D : Magma G)

def unit (x : G) := D.op x (core D x)
def bridge (x z : G) :=
  D.op (unit D z) (D.op (core D (core D x)) (D.op (core D x) z))
def Identity : Prop := ∀ x y z, x = D.op y (D.op (bridge D x z) (D.op x y))

theorem of_basis (h : Basis D) : Identity D := by
  have hu (z : G) : unit D z = z := (h.1 z).symm
  have hb (x z : G) : bridge D x z = core D x := by
    simp only [bridge, hu]
    exact (h.2 (core D x) z).symm
  intro x y z
  rw [hb]
  exact h.2 x y

/-- More generally, any identity with this frame forces finite quasigroups;
the bridge can be an arbitrary function of the displayed two arguments. -/
theorem quasigroup_of_frame [Finite G] (K : G → G → G)
    (h : ∀ x y z, x = D.op y (D.op (K x z) (D.op x y))) : IsQuasigroup D := by
  have hi (a : G) : Function.Injective (D.op a) :=
    Finite.injective_iff_surjective.mpr fun b =>
      ⟨D.op (K b b) (D.op b a), (h b a b).symm⟩
  let N := fun a b => D.op (K b b) (D.op b a)
  have hn (a b : G) : D.op a (N a b) = b := (h b a b).symm
  have nh (a b : G) : N a (D.op a b) = b := hi a (hn a (D.op a b))
  have hni (b : G) : Function.Injective (fun a => N a b) :=
    (hi (K b b)).comp (hi b)
  constructor
  · intro a
    exact ⟨hi a, Finite.injective_iff_surjective.mp (hi a)⟩
  · intro b
    have hri : Function.Injective (fun a => D.op a b) := by
      intro a a' he
      apply hni (D.op a b)
      change N a (D.op a b) = N a' (D.op a b)
      change D.op a b = D.op a' b at he
      rw [nh, he, nh]
    exact ⟨hri, Finite.injective_iff_surjective.mp hri⟩

theorem quasigroup [Finite G] (h : Identity D) : IsQuasigroup D :=
  quasigroup_of_frame D (bridge D) h

/-- Both row and column cancellation are available here. This is stronger
than the repeated-row situation encountered in the E872 compression attempt. -/
theorem bridge_independent [Finite G] (h : Identity D) (x z w : G) :
    bridge D x z = bridge D x w := by
  have hq := quasigroup D h
  apply (hq.2 (D.op x x)).1
  apply (hq.1 x).1
  exact (h x x z).symm.trans (h x x w)

end Parastrophes.Eq917Image.Candidate
