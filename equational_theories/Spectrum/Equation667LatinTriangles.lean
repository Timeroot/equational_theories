import equational_theories.Spectrum.SemisymmetricLoop
import equational_theories.Spectrum.Equation667GroupConstructions

/-! Two entirely independent Latin squares supply the two orientations of
a directed-triangle construction. Associativity and idempotence of the
Latin squares are unnecessary. -/
namespace Spectrum.E667.LatinTriangles
open Classical

structure Latin (Q : Type*) where
  op : Q → Q → Q
  row : ∀ x, Function.Bijective (op x)
  col : ∀ y, Function.Bijective (fun x => op x y)

namespace Latin
variable {Q : Type*} (L : Latin Q)
noncomputable def left (x z : Q) : Q := (Equiv.ofBijective (L.op x) (L.row x)).symm z
noncomputable def right (y z : Q) : Q := (Equiv.ofBijective (fun x => L.op x y) (L.col y)).symm z
@[simp] theorem op_left (x z : Q) : L.op x (L.left x z) = z :=
  (Equiv.ofBijective (L.op x) (L.row x)).apply_symm_apply z
@[simp] theorem left_op (x y : Q) : L.left x (L.op x y) = y :=
  (Equiv.ofBijective (L.op x) (L.row x)).symm_apply_apply y
@[simp] theorem op_right (y z : Q) : L.op (L.right y z) y = z :=
  (Equiv.ofBijective (fun x => L.op x y) (L.col y)).apply_symm_apply z
@[simp] theorem right_op (x y : Q) : L.right y (L.op x y) = x :=
  (Equiv.ofBijective (fun x => L.op x y) (L.col y)).symm_apply_apply x
@[simp] theorem left_right (x y : Q) : L.left (L.right x y) y = x := by
  exact (congrArg (L.left (L.right x y)) (L.op_right x y)).symm.trans (L.left_op _ _)
end Latin

variable {Q : Type*} (L R : Latin Q) (M : Mendelsohn (Option Q))
abbrev Points (Q : Type*) := Option (Fin 3 × Q)
def embed (i : Fin 3) : Option Q → Points Q := Option.map (fun a => (i,a))

noncomputable def cross (i j : Fin 3) (a b : Q) : Fin 3 × Q :=
  if i = 2 then if j = 0 then (1,L.left b a) else (0,R.left b a)
  else if j = 2 then if i = 0 then (1,R.right a b) else (0,L.right a b)
  else if i = 0 then (2,L.op a b) else (2,R.op a b)

noncomputable def op : Points Q → Points Q → Points Q
  | none, none => none
  | some (i,a), none => embed i (M.op (some a) none)
  | none, some (j,b) => embed j (M.op none (some b))
  | some (i,a), some (j,b) =>
    if i = j then embed i (M.op (some a) (some b)) else some (cross L R i j a b)

theorem embed_hom (i : Fin 3) (a b : Option Q) :
    op L R M (embed i a) (embed i b) = embed i (M.op a b) := by
  cases a <;> cases b <;> simp [embed, op, M.idem]

theorem cross_color (i j : Fin 3) (hij : i ≠ j) (a b : Q) :
    j ≠ (cross L R i j a b).1 := by
  fin_cases i <;> fin_cases j <;> simp_all [cross]

theorem cross_semi (i j : Fin 3) (hij : i ≠ j) (a b : Q) :
    cross L R j (cross L R i j a b).1 b (cross L R i j a b).2 = (i,a) := by
  fin_cases i <;> fin_cases j <;> simp_all [cross]

/-- Completely independent Latin squares may be used in the two orientations. -/
noncomputable def construction : Mendelsohn (Points Q) where
  op := op L R M
  idem x := by
    cases x with
    | none => rfl
    | some x => rcases x with ⟨i,a⟩; simpa [embed, M.idem] using embed_hom L R M i (some a) (some a)
  semi x y := by
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        rcases y with ⟨j,b⟩
        change op L R M (embed j (some b)) (op L R M (embed j none) (embed j (some b))) = embed j none
        rw [embed_hom, embed_hom, M.semi]
    | some x =>
      rcases x with ⟨i,a⟩
      cases y with
      | none =>
        change op L R M (embed i none) (op L R M (embed i (some a)) (embed i none)) = embed i (some a)
        rw [embed_hom, embed_hom, M.semi]
      | some y =>
        rcases y with ⟨j,b⟩
        by_cases hij : i = j
        · subst j
          change op L R M (embed i (some b)) (op L R M (embed i (some a)) (embed i (some b))) = embed i (some a)
          rw [embed_hom, embed_hom, M.semi]
        · simp only [op, if_neg hij, if_neg (cross_color L R i j hij a b)]
          rw [cross_semi L R i j hij]

noncomputable def loop : SemisymmetricLoop (Option (Points Q)) := (construction L R M).adjoin

theorem law : @Equation667 (Option (Points Q)) (loop L R M).magma := by
  intro x y
  change x = (loop L R M).op y ((loop L R M).op x ((loop L R M).op ((loop L R M).op x x) y))
  rw [(loop L R M).square, (loop L R M).left_unit, (loop L R M).semi]

theorem noncommutative (a b : Q) (hab : L.op a b ≠ R.op b a) :
    ¬ ∀ x y, (loop L R M).op x y = (loop L R M).op y x := by
  intro hc
  apply hab
  have hh := hc (some (some (0,a))) (some (some (1,b)))
  simpa [loop, Mendelsohn.adjoin, Mendelsohn.adjoinOp, construction, op, cross] using hh

/-- The two input Latin squares can be recovered from the labelled result. -/
theorem recover_left (a b : Q) :
    (construction L R M).op (some (0,a)) (some (1,b)) = some (2,L.op a b) := by
  simp [construction, op, cross]

theorem recover_right (a b : Q) :
    (construction L R M).op (some (1,a)) (some (0,b)) = some (2,R.op a b) := by
  simp [construction, op, cross]

spectrum_assert law complete
spectrum_assert noncommutative complete
spectrum_assert recover_left complete
spectrum_assert recover_right complete
end Spectrum.E667.LatinTriangles
