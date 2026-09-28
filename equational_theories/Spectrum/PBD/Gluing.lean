import equational_theories.Spectrum.PBD.Transversal

/-! Truncate groups of a transversal design, optionally adjoining one common
point to the group fillings. Every transversal block is filled independently. -/
namespace Spectrum.PBD.Transversal
open Classical
variable {I Q : Type*} (D : Transversal I Q) (A : I → Set Q) (e : ℕ)

abbrev Points := Fin e ⊕ (Σ i, A i)

def block : I ⊕ (Q × Q) → Set (Points A e)
  | .inl i => fun x => match x with
    | .inl _ => True
    | .inr p => p.1 = i
  | .inr p => fun x => match x with
    | .inl _ => False
    | .inr x => x.2.val = D.line p x.1

theorem point_eq {x y : Σ i, A i} (hi : x.1 = y.1) (hv : x.2.val = y.2.val) : x = y := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  dsimp at hi hv
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext hv)

theorem cover (he : e ≤ 1) (x y : Points A e) (hxy : x ≠ y) :
    ∃! b, x ∈ block D A e b ∧ y ∈ block D A e b := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact (hxy (congrArg Sum.inl (Fin.ext (by omega)))).elim
    | inr y =>
      refine ⟨.inl y.1, ⟨trivial,rfl⟩, ?_⟩
      intro b hb
      cases b with
      | inl i => exact congrArg Sum.inl hb.2.symm
      | inr p => exact hb.1.elim
  | inr x =>
    cases y with
    | inl y =>
      refine ⟨.inl x.1, ⟨rfl,trivial⟩, ?_⟩
      intro b hb
      cases b with
      | inl i => exact congrArg Sum.inl hb.1.symm
      | inr p => exact hb.2.elim
    | inr y =>
      by_cases hi : x.1 = y.1
      · refine ⟨.inl x.1, ⟨rfl,hi.symm⟩, ?_⟩
        intro b hb
        cases b with
        | inl i => exact congrArg Sum.inl hb.1.symm
        | inr p =>
          exact (hxy (congrArg Sum.inr (point_eq A hi
            (hb.1.trans ((congrArg (D.line p) hi).trans hb.2.symm))))).elim
      · obtain ⟨p,hp⟩ := (D.pair x.1 y.1 hi).surjective (x.2.val,y.2.val)
        obtain ⟨hx,hy⟩ := Prod.mk.inj hp
        refine ⟨.inr p, ⟨hx.symm,hy.symm⟩, ?_⟩
        intro b hb
        cases b with
        | inl i => exact (hi (hb.1.trans hb.2.symm)).elim
        | inr q =>
          apply congrArg Sum.inr
          apply (D.pair x.1 y.1 hi).injective
          exact Prod.ext (hb.1.symm.trans hx.symm) (hb.2.symm.trans hy.symm)

def groupEquiv (i : I) : block D A e (.inl i) ≃ Fin e ⊕ A i where
  toFun x := match x with
    | ⟨.inl x,_⟩ => .inl x
    | ⟨.inr p,hp⟩ => .inr ⟨p.2.val, (congrArg (fun j => p.2.val ∈ A j) hp).mp p.2.property⟩
  invFun x := match x with
    | .inl x => ⟨.inl x,trivial⟩
    | .inr x => ⟨.inr ⟨i,x⟩,rfl⟩
  left_inv x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl x => rfl
    | inr x =>
      apply Subtype.ext
      apply congrArg Sum.inr
      exact point_eq A hx.symm rfl
  right_inv x := by cases x <;> rfl

def lineEquiv (p : Q × Q) : block D A e (.inr p) ≃ {i // D.line p i ∈ A i} where
  toFun x := match x with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr x,h⟩ => ⟨x.1, h ▸ x.2.property⟩
  invFun i := ⟨.inr ⟨i.val,⟨D.line p i,i.property⟩⟩,rfl⟩
  left_inv x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl x => exact hx.elim
    | inr x =>
      apply Subtype.ext
      apply congrArg Sum.inr
      exact point_eq A rfl hx.symm
  right_inv _ := rfl

noncomputable def glue {L : BinaryLaw} (he : e ≤ 1)
    (groups : ∀ i, Model L (Fin e ⊕ A i))
    (lines : ∀ p, Model L {i // D.line p i ∈ A i}) : Model L (Points A e) := by
  apply Model.glue (block D A e) _ (cover D A e he)
  intro b
  cases b with
  | inl i => exact (groups i).transport (groupEquiv D A e i).symm
  | inr p => exact (lines p).transport (lineEquiv D A e p).symm

end Spectrum.PBD.Transversal
