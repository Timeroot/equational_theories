import equational_theories.Definability.Reversible

/-! Store the diagonal in a definable zero row, then replace the diagonal by
that zero. This quantifier-free change is reversible on every carrier. -/
open Law Law.MagmaLaw FreeMagma
namespace ZeroRowEncoding

private abbrev x : FreeMagma (Fin 2) := .Leaf 0
private abbrev y : FreeMagma (Fin 2) := .Leaf 1

/-- Move the old diagonal to the zero row. -/
def forward (root : FreeMagma (Fin 2)) : QFOp :=
  .ite x y (.leaf root) (.ite x root (.leaf (y ⋆ y)) (.leaf (x ⋆ y)))

/-- The new common square names the old zero, so no parameter is needed. -/
def backward : QFOp :=
  .ite x y (.leaf ((x ⋆ x) ⋆ x))
    (.ite x (x ⋆ x) (.leaf (x ⋆ x)) (.leaf (x ⋆ y)))

variable {G : Type} (M : Magma G) (root : FreeMagma (Fin 2)) (c : G)
variable (hr : ∀ a b : G, @FreeMagma.evalInMagma _ _ M ![a,b] root = c)

include hr in
open scoped Classical in
theorem forward_apply (a b : G) :
    ((forward root).magma M).op a b =
      if a = b then c else if a = c then M.op b b else M.op a b := by
  change (if a = b then _ else if a = _ then _ else _) = _
  simp only [QFOp.eval, hr]
  rfl

include hr in
theorem square (a : G) : ((forward root).magma M).op a a = c := by
  classical
  rw [forward_apply M root c hr]
  simp

include hr in
theorem root_row (hc : M.op c c = c) (a : G) :
    ((forward root).magma M).op c a = M.op a a := by
  classical
  rw [forward_apply M root c hr]
  by_cases ha : c = a
  · subst a
    simp [hc]
  · simp [ha]

include hr in
theorem recover (hc : ∀ a, M.op c a = c) :
    backward.magma ((forward root).magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change (if a = b then ((forward root).magma M).op (((forward root).magma M).op a a) a
    else if a = ((forward root).magma M).op a a then ((forward root).magma M).op a a
    else ((forward root).magma M).op a b) = M.op a b
  rw [square M root c hr, root_row M root c hr (hc c)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    by_cases ha : a = c
    · subst a
      simp [hc]
    · rw [if_neg ha, forward_apply M root c hr, if_neg hab, if_neg ha]

include hr in
theorem equation40 : @Equation40 G ((forward root).magma M) := by
  intro a b
  rw [square M root c hr, square M root c hr]

include hr in
theorem equation3485 (hc : ∀ a, M.op c a = c)
    (hcu : ∀ a, M.op a (M.op a a) = c) :
    @Equation3485 G ((forward root).magma M) := by
  classical
  intro a b
  rw [square M root c hr, square M root c hr, root_row M root c hr (hc c)]
  rw [forward_apply M root c hr]
  split_ifs with hb hbc
  · rfl
  · subst b
    simp [hc]
  · exact (hcu b).symm

include hr in
theorem equation3473 (hc : ∀ a, M.op c a = c)
    (hs : ∀ a b, M.op a (M.op b b) = c) :
    @Equation3473 G ((forward root).magma M) := by
  classical
  intro a b d
  rw [square M root c hr, root_row M root c hr (hc c)]
  rw [forward_apply M root c hr]
  split_ifs with hb hbc
  · rfl
  · subst b
    exact (hs (M.op d d) d).symm
  · exact (hs b d).symm

/-- A common value for both cubes follows from E4390. Its value is a left zero. -/
theorem source4390 (h : @Equation4390 G M) (a : G) :
    let c := M.op a (M.op a a)
    (∀ b, M.op b (M.op b b) = c) ∧ (∀ b, M.op c b = c) := by
  dsimp
  have cubes (b : G) : M.op b (M.op b b) = M.op a (M.op a a) :=
    (h b a a).trans (h a a a).symm
  have sq : M.op (M.op a a) (M.op a a) = M.op a (M.op a a) := (h a a (M.op a a)).symm
  refine ⟨cubes, ?_⟩
  intro b
  rw [← sq]
  exact (h a (M.op a a) b).symm.trans sq.symm

/-- E4484 has a common annihilator for every product involving a square. -/
theorem source4484 (h : @Equation4484 G M) (a : G) :
    let c := M.op (M.op a a) (M.op a a)
    (∀ b d, M.op b (M.op d d) = c) ∧
    (∀ b d, M.op (M.op b b) d = c) := by
  dsimp
  have rows (b d : G) : M.op (M.op b b) d = M.op (M.op a a) (M.op a a) :=
    (h (M.op a a) b d).symm.trans (h (M.op a a) a (M.op b b)).symm
  exact ⟨fun b d => (h b d a).trans (rows d a), rows⟩

/-- The source's left cube names the zero. -/
def cube : FreeMagma (Fin 2) := x ⋆ (x ⋆ x)
/-- The source's iterated square names the zero. -/
def squareSquare : FreeMagma (Fin 2) := (x ⋆ x) ⋆ (x ⋆ x)

end ZeroRowEncoding

open ZeroRowEncoding in
theorem Equation3485_structuralFrom_Equation4390_zeroRow :
    Law3485.StructuralFrom Law4390 := by
  apply structuralFrom_of_qfInverse (forward cube) backward
  · intro G M hM
    have h := (@Law4390.models_iff G M).mp hM
    change Magma.mk _ = Magma.mk M.op
    congr 1
    funext a b
    have hc := source4390 M h a
    have hr : ∀ u v : G, @FreeMagma.evalInMagma _ _ M ![u,v] cube = M.op a (M.op a a) :=
      fun u _ => hc.1 u
    exact congrFun (congrFun (congrArg (fun N : Magma G => N.op) (recover M cube _ hr hc.2)) a) b
  · intro G M hM
    apply (@Law3485.models_iff G ((forward cube).magma M)).mpr
    intro a b
    have hc := source4390 M ((@Law4390.models_iff G M).mp hM) a
    exact equation3485 M cube _ (fun u _ => hc.1 u) hc.2 hc.1 a b

open ZeroRowEncoding in
theorem Equation3473_structuralFrom_Equation4484_zeroRow :
    Law3473.StructuralFrom Law4484 := by
  apply structuralFrom_of_qfInverse (forward squareSquare) backward
  · intro G M hM
    have h := (@Law4484.models_iff G M).mp hM
    change Magma.mk _ = Magma.mk M.op
    congr 1
    funext a b
    have hc := source4484 M h a
    have hr : ∀ u v : G, @FreeMagma.evalInMagma _ _ M ![u,v] squareSquare = M.op (M.op a a) (M.op a a) :=
      fun u _ => hc.1 (M.op u u) u
    have hz : ∀ u, M.op (M.op (M.op a a) (M.op a a)) u = M.op (M.op a a) (M.op a a) :=
      hc.2 (M.op a a)
    exact congrFun (congrFun (congrArg (fun N : Magma G => N.op) (recover M squareSquare _ hr hz)) a) b
  · intro G M hM
    apply (@Law3473.models_iff G ((forward squareSquare).magma M)).mpr
    intro a b d
    have hc := source4484 M ((@Law4484.models_iff G M).mp hM) a
    exact equation3473 M squareSquare _ (fun u _ => hc.1 (M.op u u) u)
      (hc.2 (M.op a a)) hc.1 a b d

/-- info: 'Equation3485_structuralFrom_Equation4390_zeroRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3485_structuralFrom_Equation4390_zeroRow
/-- info: 'Equation3473_structuralFrom_Equation4484_zeroRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3473_structuralFrom_Equation4484_zeroRow
