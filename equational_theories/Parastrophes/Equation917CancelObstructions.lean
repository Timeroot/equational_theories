import equational_theories.Parastrophes.Equation917CancelComparison
import equational_theories.Parastrophes.Equation917RegularUnit

/-! Further necessary conditions for a counterexample to the 48-operation
comparison. These exclude fixed points of its other common maps; they do
not assert that a fixed point exists. -/
namespace Parastrophes.Eq917Image.CancelComparison
open SandwichCandidate (U H)

variable {A : Type} [Finite A] (D : Magma A) (h : Identity D)
    (d g c : A → A)
    (hd : ∀ x y, D.op x (U D y)=d (D.op x y))
    (hg : ∀ x y, D.op (U D x) y=g (U D (D.op x (d y))))
    (hc : ∀ x y, D.op (g x) y=c (D.op x y))
    (hf : ∀ x y, D.op (c y) (H D x y)=x)

include h hd hg hc hf in
/-- A fixed point of the input map g forces the whole image basis. -/
theorem basis_of_g_fixed (o : A) (ho : g o=o) : Basis D := by
  have hq := quasigroup D h
  have cid (x : A) : c x=x := by
    obtain ⟨y, rfl⟩ := (hq.1 o).2 x
    rw [← hc, ho]
  have gid (x : A) : g x=x := by
    apply (hq.2 o).1
    change D.op (g x) o=D.op x o
    rw [hc, cid]
  have cross : Cross D := by
    intro x y
    simpa only [cid, H] using (hf x y).symm
  obtain ⟨hu, _, _, ud, left, _, _⟩ := RegularUnit.reduction D cross d hd
  have right (x y : A) : D.op x (d y)=U D (D.op x y) := by
    have he := congrArg (U D) (hd x (d y))
    simpa only [ud] using he.symm
  have he := hg o o
  rw [left, gid, right] at he
  exact basis_of_fixed_point D h (D.op o o) (hu.1 he).symm

include h hd hg hc hf in
/-- The output map c cannot have a fixed point in a counterexample either.
Column surjectivity transfers such a fixed point to g. -/
theorem basis_of_c_fixed (o : A) (ho : c o=o) : Basis D := by
  have hq := quasigroup D h
  obtain ⟨x, hx⟩ := (hq.2 o).2 o
  change D.op x o=o at hx
  have hgx : g x=x := by
    apply (hq.2 o).1
    change D.op (g x) o=D.op x o
    rw [hc, hx, ho]
  exact basis_of_g_fixed D h d g c hd hg hc hf x hgx

include h hd in
theorem basis_of_d_fixed (o : A) (ho : d o=o) : Basis D := by
  have hq := quasigroup D h
  obtain ⟨x, hx⟩ := (hq.1 o).2 o
  have hux : U D x=x := by
    apply (hq.1 o).1
    rw [hd, hx, ho]
  exact basis_of_fixed_point D h x hux

end Parastrophes.Eq917Image.CancelComparison
