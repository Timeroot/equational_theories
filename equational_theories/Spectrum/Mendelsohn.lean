import equational_theories.Spectrum.IdempotentLatin
import equational_theories.Spectrum.Basic
import equational_theories.Equations.All

/-!
# Mendelsohn quasigroups and Bose's construction

An idempotent Latin square of order `n` gives Mendelsohn quasigroups of orders
`3*n` and `3*n+1`. Directed triples between distinct fibres are supplied by
the Latin square; fibres are filled by the three- or four-point system.
-/

open Classical

namespace Spectrum

structure Mendelsohn (Q : Type*) where
  op : Q → Q → Q
  idem : ∀ x, op x x = x
  semi : ∀ x y, op y (op x y) = x

namespace Mendelsohn

variable {Q : Type*}

@[implicit_reducible] def magma (M : Mendelsohn Q) : Magma Q := ⟨M.op⟩

theorem equation66 (M : Mendelsohn Q) : @Equation66 Q M.magma := by
  intro x y
  change x = M.op y (M.op x (M.op y y))
  rw [M.idem, M.semi]

noncomputable def cross (L : IdempotentLatin Q) (x y : Q × Fin 3) : Q × Fin 3 :=
  if x.2 = y.2 then (L.op x.1 y.1, x.2+1)
  else if y.2 = x.2+1 then (L.right x.1 y.1, x.2)
  else (L.left y.1 x.1, y.2)

theorem cross_semi (L : IdempotentLatin Q) (x y : Q × Fin 3) :
    cross L y (cross L x y) = x := by
  obtain ⟨a,i⟩ := x
  obtain ⟨b,j⟩ := y
  fin_cases i <;> fin_cases j <;> simp [cross]

theorem cross_ne_left (L : IdempotentLatin Q) {x y : Q × Fin 3}
    (h : x.1 ≠ y.1) : (cross L x y).1 ≠ x.1 := by
  unfold cross
  split_ifs
  · exact L.op_ne_left h
  · exact L.right_ne_left h
  · exact L.left_ne_right h.symm

theorem cross_ne_right (L : IdempotentLatin Q) {x y : Q × Fin 3}
    (h : x.1 ≠ y.1) : (cross L x y).1 ≠ y.1 := by
  unfold cross
  split_ifs
  · exact L.op_ne_right h
  · exact L.right_ne_right h
  · exact L.left_ne_left h.symm

def core3 (i j : Fin 3) : Fin 3 := ![![0,2,1], ![2,1,0], ![1,0,2]] i j

@[simp] theorem core3_idem (i : Fin 3) : core3 i i = i := by fin_cases i <;> decide
@[simp] theorem core3_semi (i j : Fin 3) : core3 j (core3 i j) = i := by
  fin_cases i <;> fin_cases j <;> decide

noncomputable def boseOp (L : IdempotentLatin Q) (x y : Q × Fin 3) : Q × Fin 3 :=
  if x.1 = y.1 then (x.1, core3 x.2 y.2) else cross L x y

noncomputable def bose (L : IdempotentLatin Q) : Mendelsohn (Q × Fin 3) where
  op := boseOp L
  idem x := by simp [boseOp]
  semi x y := by
    classical
    by_cases h : x.1 = y.1
    · simpa [boseOp, h] using (show (y.1,x.2) = x from Prod.ext h.symm rfl)
    · simpa only [boseOp, if_neg h, if_neg (cross_ne_right L h).symm] using cross_semi L x y

/-- The fourth point in each fibre is shared between all fibres. -/
noncomputable def bosePlusOp (L : IdempotentLatin Q) :
    Option (Q × Fin 3) → Option (Q × Fin 3) → Option (Q × Fin 3)
  | none, none => none
  | some (a,i), none => some (a,i+1)
  | none, some (a,j) => some (a,j+2)
  | some (a,i), some (b,j) =>
    if a = b then
      if i = j then some (a,i)
      else if j = i+1 then some (a,i+2) else none
    else some (cross L (a,i) (b,j))

noncomputable def bosePlus (L : IdempotentLatin Q) : Mendelsohn (Option (Q × Fin 3)) where
  op := bosePlusOp L
  idem x := by cases x <;> simp [bosePlusOp]
  semi x y := by
    classical
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => obtain ⟨a,i⟩ := y; fin_cases i <;> simp [bosePlusOp]
    | some x =>
      obtain ⟨a,i⟩ := x
      cases y with
      | none => fin_cases i <;> simp [bosePlusOp]
      | some y =>
        obtain ⟨b,j⟩ := y
        by_cases h : a = b
        · subst b
          fin_cases i <;> fin_cases j <;> simp [bosePlusOp]
        · have hc := (cross_ne_right L (x := (a,i)) (y := (b,j)) h).symm
          simp only [bosePlusOp, if_neg h]
          change (if b = (cross L (a,i) (b,j)).1 then _ else _) = _
          rw [if_neg hc]
          exact congrArg some (cross_semi L (a,i) (b,j))

end Mendelsohn
end Spectrum
