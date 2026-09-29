import equational_theories.Spectrum.Equation1083_1286.DesignModels

/-! Glue pointed, possibly nonidempotent groups along a transversal design,
identifying their distinguished idempotent points. -/
namespace Spectrum.E1083E1286.CommonPoint
open Classical
variable {I Q : Type*}

def embed (i : I) : Option Q → Option (I × Q)
  | none => none
  | some x => some (i,x)

noncomputable def through (D : PBD.Transversal I Q) (i j : I) (h : i ≠ j) (u v : Q) :
    Q × Q := ((D.pair i j h).surjective (u,v)).choose

theorem through_line (D : PBD.Transversal I Q) (i j : I) (h : i ≠ j) (p : Q × Q) :
    through D i j h (D.line p i) (D.line p j) = p :=
  (D.pair i j h).injective (((D.pair i j h).surjective _).choose_spec)

noncomputable def op (D : PBD.Transversal I Q) (b : I → I → I)
    (g : Option Q → Option Q → Option Q) : Option (I × Q) → Option (I × Q) → Option (I × Q)
  | none, none => none
  | none, some (j,v) => embed j (g none (some v))
  | some (i,u), none => embed i (g (some u) none)
  | some (i,u), some (j,v) =>
    if h : i = j then embed i (g (some u) (some v))
    else some (b i j, D.line (through D i j h u v) (b i j))

theorem op_group (D : PBD.Transversal I Q) (b g) (hg : g none none = none)
    (i : I) (u v : Option Q) :
    op D b g (embed i u) (embed i v) = embed i (g u v) := by
  cases u <;> cases v <;> simp [embed, op, hg]

theorem op_line (D : PBD.Transversal I Q) (b g) (p : Q × Q)
    (i j : I) (h : i ≠ j) :
    op D b g (some (i,D.line p i)) (some (j,D.line p j)) =
      some (b i j, D.line p (b i j)) := by
  simp only [op, dif_neg h, through_line]

theorem lawful [Finite I] {which : Bool} (D : PBD.Transversal I Q) (b g)
    (hb : Lawful which b) (hi : Idem b) (hg : Lawful which g) (hg0 : g none none = none) :
    Lawful which (op D b g) := by
  cases which with
  | false =>
    have group (i : I) (x y : Option Q) :
        op D b g (embed i y) (op D b g (op D b g (embed i x)
          (op D b g (embed i y) (embed i x))) (embed i y)) = embed i x := by
      rw [op_group D b g hg0, op_group D b g hg0, op_group D b g hg0,
        op_group D b g hg0, hg x y]
    intro x y
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact group y.1 none (some y.2)
    | some x =>
      cases y with
      | none => exact group x.1 (some x.2) none
      | some y =>
        rcases x with ⟨i,u⟩
        rcases y with ⟨j,v⟩
        by_cases he : i = j
        · subst j; exact group i (some u) (some v)
        obtain ⟨p,hp⟩ := (D.pair i j he).surjective (u,v)
        obtain ⟨hu,hv⟩ := Prod.mk.inj hp
        rw [← hu, ← hv]
        have hd := discrete1083 hb hi he
        rw [op_line D b g p j i (Ne.symm he), op_line D b g p _ _ hd.1,
          op_line D b g p _ _ hd.2.1, op_line D b g p _ _ hd.2.2, hb i j]
  | true =>
    have group (i : I) (x y : Option Q) :
        op D b g (embed i y) (op D b g (op D b g (op D b g (embed i x)
          (embed i y)) (embed i x)) (embed i y)) = embed i x := by
      rw [op_group D b g hg0, op_group D b g hg0, op_group D b g hg0,
        op_group D b g hg0, hg x y]
    intro x y
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact group y.1 none (some y.2)
    | some x =>
      cases y with
      | none => exact group x.1 (some x.2) none
      | some y =>
        rcases x with ⟨i,u⟩
        rcases y with ⟨j,v⟩
        by_cases he : i = j
        · subst j; exact group i (some u) (some v)
        obtain ⟨p,hp⟩ := (D.pair i j he).surjective (u,v)
        obtain ⟨hu,hv⟩ := Prod.mk.inj hp
        rw [← hu, ← hv]
        have hd := discrete1286 hb hi he
        rw [op_line D b g p i j he, op_line D b g p _ _ hd.1,
          op_line D b g p _ _ hd.2.1, op_line D b g p _ _ hd.2.2, hb i j]

end Spectrum.E1083E1286.CommonPoint

namespace Spectrum.E1083E1286
open Classical Law Law.MagmaLaw

structure Pointed (which : Bool) (A : Type*) where
  op : A → A → A
  lawful : Lawful which op
  point : A
  fixed : op point point = point

variable {which : Bool}

def Pointed.transport {A C : Type*} (M : Pointed which A) (e : A ≃ C) : Pointed which C where
  op x y := e (M.op (e.symm x) (e.symm y))
  lawful := by
    cases which <;> intro x y <;>
      simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        congrArg e (M.lawful (e.symm x) (e.symm y))
  point := e M.point
  fixed := by simp only [Equiv.symm_apply_apply, M.fixed]

def Pointed.product {A C : Type*} (M : Pointed which A) (N : Pointed which C) :
    Pointed which (A × C) where
  op x y := (M.op x.1 y.1, N.op x.2 y.2)
  lawful := by cases which <;> exact fun x y => Prod.ext (M.lawful x.1 y.1) (N.lawful x.2 y.2)
  point := (M.point,N.point)
  fixed := Prod.ext M.fixed N.fixed

theorem Pointed.hasModel {A : Type*} [Fintype A] {n : ℕ}
    (G : Pointed which A) (hc : Fintype.card A = n) : (law which).HasModel n :=
  ((show Model which A from ⟨G.op,G.lawful,by simp⟩).relabel
    (Fintype.equivFinOfCardEq hc)).hasModel

theorem common_point_model {k q : ℕ} (hD : PBD.HasTD k q)
    (B : Model which (Fin k) true) {A : Type*} [Fintype A]
    (G : Pointed which A) (hc : Fintype.card A = q+1) :
    (law which).HasModel (k*q+1) := by
  obtain ⟨D⟩ := hD
  obtain ⟨b,hb,hi⟩ := B
  let e : A ≃ Option (Fin q) := Fintype.equivOfCardEq (by simpa using hc)
  let e' := e.trans (Equiv.swap (e G.point) none)
  have he : e' G.point = none := by simp [e']
  let H := G.transport e'
  have h0 : H.op none none = none := by
    have h := H.fixed
    change H.op (e' G.point) (e' G.point) = e' G.point at h
    simpa only [he] using h
  have M : Model which (Option (Fin k × Fin q)) :=
    ⟨CommonPoint.op D b H.op, CommonPoint.lawful D b H.op hb (hi rfl) H.lawful h0, by simp⟩
  exact (M.relabel (Fintype.equivFinOfCardEq (by simp))).hasModel

end Spectrum.E1083E1286
