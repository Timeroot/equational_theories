import equational_theories.Parastrophes.Equation917SandwichCandidate

/-!
# Bijective auxiliary columns in a shorter E917 comparison

For q(x)=(x*(x*x))*x, U(x)=x*q(x), H(x,y)=q(x)*(x*y), and
F(x,y)=y*H(x,y), consider x=U(y)*H(x,F(y,z)). This is a different candidate
from the front-product and double-crossed comparisons. Its unrestricted
converse and even its unconditional finite quasigroup property remain open.

Every finite model nevertheless has all columns x ↦ H(x,c) bijective.
The proof uses a closed set of column indices, not presumed cancellation
of D. The final lemma explains one sufficient condition for recovering
row cancellation: one injective row of H. It does not assert that such a
row exists in every candidate. No catalogue attribute is registered.
-/

namespace Parastrophes.Eq917Image.ShortFront
open SandwichCandidate (U H F)
variable {A : Type} (D : Magma A)
def Identity : Prop := ∀ x y z, x=D.op (U D y) (H D x (F D y z))
theorem of_basis (h : Basis D) : Identity D := by
  intro x y z
  have hu (t) : U D t=t := (h.1 t).symm
  have hf (s t) : F D s t=s := (h.2 s t).symm
  rw [hu,hf]
  exact h.2 x y

theorem unit_rows [Finite A] (h : Identity D) (y : A) :
    Function.Bijective (D.op (U D y)) := by
  have hs : Function.Surjective (D.op (U D y)) := fun x => ⟨_,(h x y y).symm⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩

/-- Surjective columns first propagate through their own rows. A unit row
inside that set is bijective, so its F-column covers every column index. -/
theorem columns [Finite A] (h : Identity D) (c : A) :
    Function.Bijective (fun x => H D x c) := by
  let good := fun t => Function.Bijective (fun x => H D x t)
  have hg (y z : A) : good (F D y z) := by
    have hi : Function.Injective (fun x => H D x (F D y z)) := by
      intro x w he
      exact (h x y z).trans ((congrArg (D.op (U D y)) he).trans (h w y z).symm)
    exact ⟨hi,Finite.surjective_of_injective hi⟩
  have closed (t : A) (ht : good t) (v : A) : good (D.op t v) := by
    obtain ⟨x,hx⟩ := ht.2 v
    have he := hg x t
    simpa only [F,hx] using he
  let t := F D c c
  have ht : good t := hg c c
  have hd : good (U D t) := closed t ht (core D t)
  have hs : Function.Surjective (fun x => F D x (U D t)) :=
    (unit_rows D h t).2.comp hd.2
  obtain ⟨x,hx⟩ := hs c
  simpa only [hx] using hg x (U D t)

/-- One injective row of H suffices to make every row of D bijective.
Existence of that row is an explicit additional condition. -/
theorem rows_of_injective_H_row [Finite A] (h : Identity D) (o : A)
    (ho : Function.Injective (H D o)) : IsSideQuasigroup .left D := by
  have independent (x y z) : F D x y=F D x z := by
    apply ho
    apply (unit_rows D h x).1
    exact (h o x y).symm.trans (h o x z)
  have fb : Function.Bijective (fun x => F D x (U D o)) :=
    (unit_rows D h o).comp (columns D h (U D o))
  intro y
  have hs : Function.Surjective (D.op y) := by
    intro z
    obtain ⟨x,hx⟩ := fb.2 z
    exact ⟨H D x y, (independent x y (U D o)).trans hx⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩

end Parastrophes.Eq917Image.ShortFront
