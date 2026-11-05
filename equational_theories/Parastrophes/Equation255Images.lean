import equational_theories.Parastrophes.GoldenImageObstructions

/-!
# E255's actual division images are not defined by a single identity

E255 does not force either division to exist. Even when restricting to
models where the chosen division exists, neither finite image has a
single-equation characterization. The idempotent golden-ratio family
supplies the obstruction on each side.
-/
namespace Parastrophes
open Law FreeMagma

private theorem golden_idempotent {R : Type*} [CommRing R] (x : Fin 2 → R) :
    (GoldenImage.source (R := R)).op x x = x := by
  ext i
  fin_cases i <;> simp [GoldenImage.T, GoldenImage.Ti]

namespace Catalogue

/-- The positive-weight division family obstructs any identity for E255's
finite left image, even though all source models used here are idempotent. -/
@[parastrophe_result] theorem left_noSingleEquation255_fin :
    ¬ SingleEquation .fin Law255 .left := by
  apply GoldenImage.obstruction
  intro n _
  apply (@Law255.models_iff _ (GoldenImage.source (R := ZMod n))).mpr
  intro x
  simp only [golden_idempotent]

/-- The dual unary law has the same idempotent-family obstruction. -/
@[parastrophe_result] theorem left_noSingleEquation47_fin :
    ¬ SingleEquation .fin Law47 .left := by
  apply GoldenImage.obstruction
  intro n _
  apply (@Law47.models_iff _ (GoldenImage.source (R := ZMod n))).mpr
  intro x
  simp only [golden_idempotent]

/-- Consequently E255's finite right image also has no defining identity. -/
@[parastrophe_result] theorem right_noSingleEquation255_fin :
    ¬ SingleEquation .fin Law255 .right := by
  intro h
  exact left_noSingleEquation47_fin (singleEquation_dual h)

/-- On magmas that possess right division, E255 itself is preserved: it
says the third iterate of the column permutation fixes its index. -/
theorem right_division255_iff {G : Type} (M D : Magma G) (hd : IsDivision .right M D) :
    @Equation255 G M ↔ @Equation255 G D := by
  constructor
  · intro h x
    have he := congrArg (fun v => D.op (D.op (D.op v x) x) x) (h x)
    simpa only [hd.2] using he.symm
  · intro h x
    have he := congrArg (fun v => M.op (M.op (M.op v x) x) x) (h x)
    simpa only [hd.1] using he.symm

end Catalogue

/-- For left division, E255 means that the entries with value `x` contain
the triangle `x → a → b → x`. This statement is valid without E677. -/
theorem left_division255_at_iff_triangle {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (x : G) :
    x = M.op (M.op (M.op x x) x) x ↔
      ∃ a b, D.op x a = x ∧ D.op a b = x ∧ D.op b x = x := by
  constructor
  · intro h
    refine ⟨M.op x x, M.op (M.op x x) x, hd.2 x x, hd.2 _ x, ?_⟩
    have he := congrArg (D.op (M.op (M.op x x) x)) h
    simpa only [hd.2] using he
  · rintro ⟨a, b, ha, hb, hc⟩
    have ha' := congrArg (M.op x) ha
    have hb' := congrArg (M.op a) hb
    have hc' := congrArg (M.op b) hc
    simp only [hd.1] at ha' hb' hc'
    rw [hb', ha'] at hc'
    exact hc'

/-- E203 is not a general left-parastrophic translation of E255. Addition
on Z/3 satisfies E255, but its left division `y-x` does not satisfy E203. -/
theorem left_division255_not203 :
    ∃ M D : Magma (ZMod 3), @Equation255 (ZMod 3) M ∧
      IsDivision .left M D ∧ ¬ @Equation203 (ZMod 3) D := by
  let M : Magma (ZMod 3) := ⟨fun x y => x + y⟩
  let D : Magma (ZMod 3) := ⟨fun x y => y - x⟩
  refine ⟨M, D, ?_, ?_, ?_⟩
  · decide +kernel
  · constructor
    · intro x y
      change x + (y - x) = y
      ring
    · intro x y
      change (x + y) - x = y
      ring
  · decide +kernel

end Parastrophes
