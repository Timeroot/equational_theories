import equational_theories.Definability.CubeReverse
import equational_theories.Definability.IdempotentPower
import equational_theories.Definability.DivisionFO
import equational_theories.Definability.FiniteFlavour

/-! A uniform first-order E3545 → E3342 construction, reversible on finite
carriers. The inverse on the cube image is specified by a single existential
formula, not by an iteration bound or a chosen parameter. -/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw CubeTwists

namespace CubeReverse

variable {G : Type}

/-- The companion magma. -/
@[implicit_reducible]
noncomputable def companionMagma (M : Magma G) : Magma G := ⟨companion M.op⟩

/-- Read back the original operation using the companion's left cube. -/
@[implicit_reducible]
noncomputable def recoveryMagma (M : Magma G) : Magma G := by
  classical
  exact ⟨fun x y => if square M.op x = square M.op y then M.op x y
    else forwardInverse (leftCube M.op) (M.op x y)⟩

private def cubeTerm {α : Type} (left : Bool)
    (t : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  if left then DivisionFO.ap G t (DivisionFO.ap G t t)
  else DivisionFO.ap G (DivisionFO.ap G t t) t

private def cubeOp (f : G → G → G) (left : Bool) : G → G :=
  if left then leftCube f else rightCube f

private theorem realize_cubeTerm (M : Magma G) {α : Type} (left : Bool)
    (t : (MagmaLanguage[[(∅ : Set G)]]).Term α) (v : α → G) :
    @Term.realize _ G M.FOStructure₀ _ v (cubeTerm left t) =
      cubeOp M.op left (@Term.realize _ G M.FOStructure₀ _ v t) := by
  cases left <;> rfl

/-- Membership in the range of the chosen cube, or its second iterate. -/
private def rangeFormula (left twice : Bool)
    (t : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  let a : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
    Term.var (Sum.inr 0)
  BoundedFormula.ex (Term.bdEqual
    (if twice then cubeTerm left (cubeTerm left a) else cubeTerm left a)
    (t.relabel Sum.inl))

private theorem realize_rangeFormula (M : Magma G) (left twice : Bool)
    (t : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2)))
    (v : Option (Fin 2) → G) :
    @Formula.Realize _ G M.FOStructure₀ _ (rangeFormula left twice t) v ↔
      ∃ a : G, (if twice then cubeOp M.op left (cubeOp M.op left a)
        else cubeOp M.op left a) = @Term.realize _ G M.FOStructure₀ _ v t := by
  cases twice <;>
    simp [rangeFormula, Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.realize_bdEqual, realize_cubeTerm, Term.realize_relabel, Fin.snoc]

/-- The graph of the conditional partial inverse construction. -/
def companionFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  let x := Term.var (some (0 : Fin 2))
  let y := Term.var (some (1 : Fin 2))
  let z := Term.var none
  let p := DivisionFO.ap G x y
  let eqQ := Term.equal (DivisionFO.ap G x x) (DivisionFO.ap G y y)
  (eqQ ⊓ Term.equal p z) ⊔ (∼eqQ ⊓
    ((rangeFormula false false z ⊓ Term.equal (cubeTerm false z) p) ⊔
      (∼(rangeFormula false true p) ⊓ Term.equal z p)))

private theorem realize_companionFormula (M : Magma G) (v : Option (Fin 2) → G) :
    @Formula.Realize _ G M.FOStructure₀ _ (companionFormula G) v ↔
      (square M.op (v (some 0)) = square M.op (v (some 1)) ∧
        M.op (v (some 0)) (v (some 1)) = v none) ∨
      (square M.op (v (some 0)) ≠ square M.op (v (some 1)) ∧
        (((∃ a, rightCube M.op a = v none) ∧
          rightCube M.op (v none) = M.op (v (some 0)) (v (some 1))) ∨
         ((¬ ∃ a, rightCube M.op (rightCube M.op a) = M.op (v (some 0)) (v (some 1))) ∧
           v none = M.op (v (some 0)) (v (some 1))))) := by
  simp only [companionFormula, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_not, Formula.realize_equal, realize_rangeFormula,
    realize_cubeTerm, cubeOp, Bool.false_eq_true, if_false]
  rfl

/-- The forward graph is definable without finiteness. -/
theorem companion_definable (M : Magma G) (h : @Equation3545 G M) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ (companionMagma M).Graph := by
  classical
  refine ⟨companionFormula G, Set.ext fun v => ?_⟩
  show companion M.op (v (some 0)) (v (some 1)) = v none ↔ _
  rw [Set.mem_setOf_eq, realize_companionFormula]
  have hs : ∀ {a b : G}, rightCube M.op (rightCube M.op a) =
      rightCube M.op (rightCube M.op b) → rightCube M.op a = rightCube M.op b :=
    rightCube_kernel_stable M.op h
  by_cases he : square M.op (v (some 0)) = square M.op (v (some 1))
  · simp [companion, he]
  · simp only [companion, ne_eq, he, if_false, false_and, not_false_eq_true, true_and, false_or]
    exact partialInverse_graph (rightCube M.op) hs _ _

/-- The recovery uses the left cube, visible directly in the companion. -/
def recoveryFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  let x := Term.var (some (0 : Fin 2))
  let y := Term.var (some (1 : Fin 2))
  let z := Term.var none
  let p := DivisionFO.ap G x y
  let eqQ := Term.equal (DivisionFO.ap G x x) (DivisionFO.ap G y y)
  (eqQ ⊓ Term.equal p z) ⊔ (∼eqQ ⊓
    ((rangeFormula true false p ⊓ Term.equal (cubeTerm true p) z) ⊔
      (∼(rangeFormula true false p) ⊓ Term.equal p z)))

/-- The recovery formula is definable in any magma. -/
theorem recovery_definable (M : Magma G) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ (recoveryMagma M).Graph := by
  classical
  refine ⟨recoveryFormula G, Set.ext fun v => ?_⟩
  show (recoveryMagma M).op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, recoveryFormula, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_not, Formula.realize_equal, realize_rangeFormula,
    realize_cubeTerm, cubeOp, if_true]
  change (if square M.op (v (some 0)) = square M.op (v (some 1)) then _ else _) = _ ↔ _
  by_cases he : square M.op (v (some 0)) = square M.op (v (some 1))
  · dsimp only [square] at he
    simp [he, square]
  · dsimp only [square] at he
    by_cases hr : ∃ a, leftCube M.op a = M.op (v (some 0)) (v (some 1))
    · simp [forwardInverse, he, hr, square]
    · simp [forwardInverse, he, hr, square]

theorem recovery_companion [Finite G] (M : Magma G) (h : @Equation3545 G M) :
    recoveryMagma (companionMagma M) = M := by
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext x y
  exact recover M.op h x y

end CubeReverse

open CubeReverse

/-- Every E3545 magma defines an E3342 operation by the canonical partial
inverse of its right cube. -/
theorem Equation3342_definableFrom_Equation3545_cubeInverse :
    Law3342.DefinableFrom Law3545 := by
  intro G M hM
  have h := (@Law3545.models_iff G M).mp hM
  refine ⟨companionMagma M, (@Law3342.models_iff G (companionMagma M)).mpr ?_,
    companion_definable M h⟩
  exact companion_law M.op h

/-- On finite carriers the cube inverse is a permutation on its image, so the
conditional construction retains enough information to recover the source. -/
theorem Equation3342_structuralFromFin_Equation3545_cubeInverse :
    Law3342.StructuralFromFin Law3545 := by
  intro G _ M hM
  have h := (@Law3545.models_iff G M).mp hM
  refine ⟨companionMagma M, (@Law3342.models_iff G (companionMagma M)).mpr ?_,
    companion_definable M h, ?_⟩
  · exact companion_law M.op h
  · simpa only [recovery_companion M h] using recovery_definable (companionMagma M)

/-- info: 'Equation3342_definableFrom_Equation3545_cubeInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3342_definableFrom_Equation3545_cubeInverse

/-- info: 'Equation3342_structuralFromFin_Equation3545_cubeInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3342_structuralFromFin_Equation3545_cubeInverse
