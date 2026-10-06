import equational_theories.Spectrum.SemisymmetricLoop
import equational_theories.Spectrum.Equation667GroupConstructions
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.ReduceModChar

/-! Nonabelian groups in a directed-triangle construction. Three copies of
any group, with a common point, are filled by a Mendelsohn system on the
group plus one point. Cross-copy products retain the group multiplication. -/
namespace Spectrum.E667.GroupMendelsohn
open Classical
variable {G : Type*} [Group G] (M : Mendelsohn (Option G))
abbrev Points (G : Type*) := Option (Fin 3 × G)

def embed (i : Fin 3) : Option G → Points G := Option.map (fun a => (i,a))

def cross (i j : Fin 3) (a b : G) : Fin 3 × G :=
  if i = 2 then (if j = 0 then 1 else 0, b⁻¹ * a)
  else if j = 2 then (if i = 0 then 1 else 0, b * a⁻¹)
  else (2,a*b)

noncomputable def op : Points G → Points G → Points G
  | none, none => none
  | some (i,a), none => embed i (M.op (some a) none)
  | none, some (j,b) => embed j (M.op none (some b))
  | some (i,a), some (j,b) =>
    if i = j then embed i (M.op (some a) (some b)) else some (cross i j a b)

theorem embed_hom (i : Fin 3) (a b : Option G) :
    op M (embed i a) (embed i b) = embed i (M.op a b) := by
  cases a <;> cases b <;> simp [embed, op, M.idem]

theorem cross_color (i j : Fin 3) (hij : i ≠ j) (a b : G) :
    j ≠ (cross i j a b).1 := by
  fin_cases i <;> fin_cases j <;> simp_all [cross]

theorem cross_semi (i j : Fin 3) (hij : i ≠ j) (a b : G) :
    cross j (cross i j a b).1 b (cross i j a b).2 = (i,a) := by
  fin_cases i <;> fin_cases j <;> simp_all [cross, mul_assoc]

noncomputable def construction : Mendelsohn (Points G) where
  op := op M
  idem x := by
    cases x with
    | none => rfl
    | some x => rcases x with ⟨i,a⟩; simpa [embed, M.idem] using embed_hom M i (some a) (some a)
  semi x y := by
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        rcases y with ⟨j,b⟩
        change op M (embed j (some b)) (op M (embed j none) (embed j (some b))) = embed j none
        rw [embed_hom, embed_hom, M.semi]
    | some x =>
      rcases x with ⟨i,a⟩
      cases y with
      | none =>
        change op M (embed i none) (op M (embed i (some a)) (embed i none)) = embed i (some a)
        rw [embed_hom, embed_hom, M.semi]
      | some y =>
        rcases y with ⟨j,b⟩
        by_cases hij : i = j
        · subst j
          change op M (embed i (some b)) (op M (embed i (some a)) (embed i (some b))) = embed i (some a)
          rw [embed_hom, embed_hom, M.semi]
        · simp only [op, if_neg hij, if_neg (cross_color i j hij a b)]
          rw [cross_semi i j hij]

/-- Noncommuting group elements remain visible in opposite cross-copy products. -/
theorem noncommutative (a b : G) (hab : a*b ≠ b*a) :
    ¬ ∀ x y, (construction M).op x y = (construction M).op y x := by
  intro hc
  have hh := hc (some (0,a)) (some (1,b))
  simp only [construction, op, show (0 : Fin 3) ≠ 1 by decide, if_false,
    show (1 : Fin 3) ≠ 0 by decide, cross, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide] at hh
  exact hab (congrArg Prod.snd (Option.some.inj hh))

/-- Adding an identity yields a constant-square E667 algebra. -/
noncomputable def loop : SemisymmetricLoop (Option (Points G)) := (construction M).adjoin

theorem law : @Equation667 (Option (Points G)) (loop M).magma := by
  intro x y
  change x = (loop M).op y ((loop M).op x ((loop M).op ((loop M).op x x) y))
  rw [(loop M).square, (loop M).left_unit, (loop M).semi]

theorem loop_noncommutative (a b : G) (hab : a*b ≠ b*a) :
    ¬ ∀ x y, (loop M).op x y = (loop M).op y x := by
  intro hc
  apply hab
  have hh := hc (some (some (0,a))) (some (some (1,b)))
  simpa [loop, Mendelsohn.adjoin, Mendelsohn.adjoinOp, construction, op, cross] using hh

/-- A medial loop is commutative, so nonabelian input also forces nonmediality. -/
theorem loop_nonmedial (a b : G) (hab : a*b ≠ b*a) :
    ¬ ∀ x y z w, (loop M).op ((loop M).op x y) ((loop M).op z w) =
      (loop M).op ((loop M).op x z) ((loop M).op y w) := by
  intro hm
  apply loop_noncommutative M a b hab
  intro x y
  simpa only [(loop M).left_unit, (loop M).right_unit] using
    hm (loop M).unit x y (loop M).unit

theorem idempotent_iff (x : Option (Points G)) : (loop M).op x x = x ↔ x = none := by
  rw [(loop M).square]
  exact eq_comm

omit [Group G] in
theorem card [Finite G] : Nat.card (Option (Points G)) = 3 * Nat.card G + 2 := by
  letI := Fintype.ofFinite G
  simp [Points, Nat.card_eq_fintype_card]

/-- The seven-point filling uses the affine Mendelsohn law 5x+3y over F7. -/
def fieldSeven : Mendelsohn (ZMod 7) where
  op x y := 5*x+3*y
  idem x := by ring_nf; reduce_mod_char
  semi x y := by ring_nf; reduce_mod_char

noncomputable def transport {A B : Type*} (e : A ≃ B) (N : Mendelsohn B) : Mendelsohn A where
  op x y := e.symm (N.op (e x) (e y))
  idem x := by rw [N.idem, e.symm_apply_apply]
  semi x y := by rw [e.apply_symm_apply, N.semi, e.symm_apply_apply]

/-- An explicit algebraic construction of the noncommutative twenty-point example.
Only the arbitrary labelling of the six group elements is noncomputable. -/
noncomputable def s3Filling : Mendelsohn (Option (Equiv.Perm (Fin 3))) :=
  transport (Fintype.equivOfCardEq (by norm_num [Fintype.card_perm, Nat.factorial])) fieldSeven

theorem s3_noncommutative :
    ¬ ∀ x y, (loop s3Filling).op x y = (loop s3Filling).op y x := by
  apply loop_noncommutative s3Filling (Equiv.swap 0 1) (Equiv.swap 1 2)
  intro hh
  have hn : ((Equiv.swap 0 1) * (Equiv.swap 1 2) : Equiv.Perm (Fin 3)) 0 ≠
      ((Equiv.swap 1 2) * (Equiv.swap 0 1) : Equiv.Perm (Fin 3)) 0 := by decide
  exact hn (congrArg (fun e => e 0) hh)

theorem s3_card : Nat.card (Option (Points (Equiv.Perm (Fin 3)))) = 20 := by
  rw [card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

spectrum_assert s3_noncommutative complete
spectrum_assert s3_card complete
spectrum_assert loop_nonmedial complete
spectrum_assert law complete
spectrum_assert loop_noncommutative complete
end Spectrum.E667.GroupMendelsohn
