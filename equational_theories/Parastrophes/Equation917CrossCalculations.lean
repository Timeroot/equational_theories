import equational_theories.Parastrophes.Equation917SingleCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# E917's crossed identity does not suffice by itself

With c(x)=(x*(x*x))*x, the crossed identity x=y*(c(x)*(x*y))
forces c(c(x))=x*x on finite carriers. This follows by two substitutions
and column cancellation, not by model enumeration. Nevertheless the unit
identity x=x*c(x) is independent: x*y=x+3*y modulo 7 satisfies the
crossed identity and has x*c(x)=0. Both facts are useful when testing
compressions of the two-equation image basis.
-/
namespace Parastrophes.Eq917Image.CrossCalculations

theorem core_core {G : Type} [Finite G] (D : Magma G) (h : Cross D) (x : G) :
    core D (core D x) = D.op x x := by
  have hq := Candidate.quasigroup_of_frame D (fun x _ => core D x)
    (fun x y _ => h x y)
  let p := D.op x (D.op x x)
  have he : D.op (core D (core D x)) (D.op (core D x) p) = x := by
    apply (hq.1 p).1
    exact (h (core D x) p).symm
  apply (hq.2 (D.op (core D x) p)).1
  exact he.trans (h x (D.op x x))

@[implicit_reducible] def counterexample : Magma (ZMod 7) :=
  ⟨fun x y => x + 3*y⟩

theorem counterexample_core (x : ZMod 7) : core counterexample x = 2*x := by
  change (x + 3*(x + 3*x)) + 3*x = 2*x
  ring_nf
  reduce_mod_char

theorem counterexample_cross : Cross counterexample := by
  intro x y
  change x = y + 3*(core counterexample x + 3*(x+3*y))
  rw [counterexample_core]
  ring_nf
  reduce_mod_char

theorem counterexample_not_basis : ¬ Basis counterexample := by
  intro h
  have he := h.1 (1 : ZMod 7)
  change (1 : ZMod 7) = 1+3*(core counterexample 1) at he
  rw [counterexample_core] at he
  exact (by decide : (1 : ZMod 7) ≠ 1+3*(2*1)) he

theorem counterexample_not_image : ¬ InImage Law917 .left counterexample :=
  fun h => counterexample_not_basis ((characterizes_fin counterexample).2 h)

end Parastrophes.Eq917Image.CrossCalculations
