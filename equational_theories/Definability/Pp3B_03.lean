import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq61 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | (have j0 := eq61 X0
       grind)
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq89 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (k X1 (τ X0))
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq60
    | exact resolve eq60 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq145 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X2 X3 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq30
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30
  have eq617 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq656 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq617 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq617
    | (have j0 := eq617 X0 X1
       grind)
    | exact resolve eq617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq674 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (k X1 X0)
       have i₂ := eq656 X1 X0
       grind)
    | exact superpose eq656 eq26
    | (have j1 := eq656 (k (τ X2) (k X1 X0)) (τ (k X2 (σ (M.op X0 X1))))
       grind)
    | exact resolve eq26 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 (k X1 X0) X2
       have i₂ := eq656 X1 X0
       grind)
    | exact superpose eq656 eq32
    | (have j1 := eq656 (k (k X1 X0) (τ X2)) (τ (k (σ (M.op X0 X1)) X2))
       grind)
    | exact resolve eq32 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq679 X0 X1 X2
       have i₂ := eq32 (M.op X0 X1) X2
       grind)
    | exact superpose eq32 eq679
    | (have j0 := eq679 X0 X1 X2
       grind)
    | exact resolve eq679 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq679
  have eq698 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (k (τ X2) (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 X0 X1 X2
       have i₂ := eq26 X2 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq674
    | (have j0 := eq674 X0 X1 X2
       grind)
    | exact resolve eq674 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq707 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq724 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq707 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq707
    | (have j0 := eq707 X0
       grind)
    | exact resolve eq707 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq773 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (τ (k X0 X0))) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq724 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq724
    | (have j0 := eq724 (τ X0)
       grind)
    | exact resolve eq724 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq2624 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    grind
  clear eq133
  have eq2648 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2624 X0 X1
       have i₂ := eq145 X0 X1 X0 X1
       grind)
    | exact superpose eq145 eq2624
    | (have j0 := eq2624 X0 X1
       grind)
    | exact resolve eq2624 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq2624
  have eq2649 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2648 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq2949 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2649 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2649
    | exact resolve eq2649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq9578 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ (τ (k X0 X0))) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq773
  have eq9593 : ∀ X0 : G, (τ (τ (k X0 X0))) = (τ (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9578 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq9578
    | (have j0 := eq9578 X0
       grind)
    | exact resolve eq9578 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9578
  have eq14280 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X2 X1) X0) ∨ X1 = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq693 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq693
    | (have j0 := eq693 (k (k X1 X2) X0) (k (M.op X2 X1) X0) X2
       grind)
    | exact resolve eq693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq14614 : ∀ X0 X1 : G, (M.op (k X1 X0) (k X1 X0)) = (k (M.op X0 X1) (k X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2949 X1 X0
       have i₂ := eq14280 (k X1 X0) X1 X0
       grind)
    | exact superpose eq14280 eq2949
    | (have j1 := eq14280 X0 (M.op (k X1 X0) (k X1 X0)) (k (M.op X0 X1) (k X1 X0))
       grind)
    | exact resolve eq2949 eq14280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949 eq14280
  have eq14741 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X2 X1)) ∨ X1 = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq698 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq698
    | (have j0 := eq698 (k X0 (k X1 X2)) (k X0 (M.op X2 X1)) X2
       grind)
    | exact resolve eq698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq332263 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (σ (τ (τ (k X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (τ X0) (τ X0))
       have i₂ := eq9593 X0
       grind)
    | exact superpose eq9593 eq11
    | (have j1 := eq9593 X0
       grind)
    | exact resolve eq11 eq9593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9593
  have eq332657 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq332263 X0
       have i₂ := eq11 (τ (k X0 X0))
       grind)
    | exact superpose eq11 eq332263
    | (have j0 := eq332263 X0
       grind)
    | exact resolve eq332263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332263
  have eq332658 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq332657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332657
  have eq333472 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq332658 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq332658
    | exact resolve eq332658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333774 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (k X0 X0)) (M.op X1 (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq332658 X0
       grind)
    | exact superpose eq332658 eq9
    | exact resolve eq9 eq332658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332658
  have eq334031 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq333472 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq333472
    | exact resolve eq333472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333472
  have eq334147 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq334031 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq334031
    | exact resolve eq334031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334031
  have eq334569 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq334147 (σ X0)
       grind)
    | exact superpose eq334147 eq15
    | exact resolve eq15 eq334147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334788 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq334569 X0
       have i₂ := eq334147 X0
       grind)
    | exact superpose eq334147 eq334569
    | exact resolve eq334569 eq334147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334569
  have eq336744 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq337026 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq336744 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq336744
    | exact resolve eq336744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336744
  have eq337291 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq337026
  have eq343787 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (τ (τ (k X0 X0))) (M.op X1 (τ (τ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq333774 (τ X0) X1
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq333774
    | exact resolve eq333774 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq333774
  have eq344372 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (τ (τ (M.op X0 X0))) (M.op X1 (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq343787 X0 X1
       have i₂ := eq334147 X0
       grind)
    | exact superpose eq334147 eq343787
    | exact resolve eq343787 eq334147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343787
  have eq1338569 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X1 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14741 (M.op X1 X0) X0 X1
       have i₂ := eq14614 X1 X0
       grind)
    | exact superpose eq14614 eq14741
    | (have j0 := eq14741 X0 X0 X1
       have j1 := eq14614 (k (M.op X1 X0) (M.op X1 X0)) (M.op (k X0 X1) (k X0 X1))
       grind)
    | exact resolve eq14741 eq14614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14614 eq14741
  have eq1338673 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X1 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1338569 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338569
  have eq1338742 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1338673 X0 X1
       have i₂ := eq334147 (M.op X1 X0)
       grind)
    | exact superpose eq334147 eq1338673
    | (have j0 := eq1338673 X0 X1
       grind)
    | exact resolve eq1338673 eq334147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334147 eq1338673
  have eq1377344 : ∀ X0 X1 X2 : G, (τ (τ (k X1 X0))) = (M.op (τ (τ (M.op (M.op X0 X1) (M.op X0 X1)))) (M.op X2 (τ (τ (M.op (M.op X0 X1) (M.op X0 X1)))))) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344372 (k X0 X1) X1
       have i₂ := eq1338742 X0 X1
       grind)
    | exact superpose eq1338742 eq344372
    | (have j1 := eq1338742 (τ (τ (k X1 X0))) (M.op (τ (τ (M.op (M.op X0 X1) (M.op X0 X1)))) (M.op X2 (τ (τ (M.op (M.op X0 X1) (M.op X0 X1))))))
       grind)
    | exact resolve eq344372 eq1338742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338742
  have eq1377493 : ∀ X0 X1 : G, (τ (τ (k X1 X0))) = (τ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1377344 X0 X1 x
       have i₂ := eq344372 (M.op X0 X1) x
       grind)
    | exact superpose eq344372 eq1377344
    | (have j0 := eq1377344 X0 X1 x
       grind)
    | exact resolve eq1377344 eq344372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344372 eq1377344
  have eq1380171 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (τ (M.op (σ X1) X0))) ∨ (σ X1) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1377493 (σ X1) X0
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq1377493
    | (have j0 := eq1377493 (σ X1) X0
       grind)
    | exact resolve eq1377493 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1377493
  have eq1380921 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (τ (M.op (σ X1) X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1380171 X0 X1
       have i₂ := eq334788 X1
       grind)
    | exact superpose eq334788 eq1380171
    | (have j0 := eq1380171 X0 X1
       grind)
    | exact resolve eq1380171 eq334788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380171
  have eq1397043 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) = (σ (τ (k (τ X0) X1))) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ (M.op (σ X1) X0))
       have i₂ := eq1380921 X0 X1
       grind)
    | exact superpose eq1380921 eq11
    | (have j1 := eq1380921 X0 X1
       grind)
    | exact resolve eq11 eq1380921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380921
  have eq1397727 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1397043 X0 X1
       have i₂ := eq11 (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq1397043
    | (have j0 := eq1397043 X0 X1
       grind)
    | exact resolve eq1397043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397043
  have eq1400753 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq1397727 X0 X1
       grind)
    | exact superpose eq1397727 eq11
    | (have j1 := eq1397727 X0 X1
       grind)
    | exact resolve eq11 eq1397727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397727
  have eq1401345 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1400753 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1400753
    | (have j0 := eq1400753 X0 X1
       grind)
    | exact resolve eq1400753 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1400753
  have eq1402830 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1401345 (σ X1) X0
       grind)
    | exact superpose eq1401345 eq15
    | (have j1 := eq1401345 (σ X1) X0
       grind)
    | exact resolve eq15 eq1401345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401345
  have eq1419092 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1402830 x y
       grind)
    | exact superpose eq1402830 eq16
    | (have j1 := eq1402830 x y
       grind)
    | exact resolve eq16 eq1402830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402830
  have eq1420708 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1419092
       have i₂ := eq656 y x
       grind)
    | exact superpose eq656 eq1419092
    | (have j1 := eq656 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq1419092
       have r₂ := eq656 y x
       grind)
    | (have r₁ := eq1419092
       have r₂ := eq656 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1419092
       have r₂ := eq656 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1419092 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq1419092
  have eq1420709 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1420708
  have eq1422681 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1420709
       grind)
    | exact superpose eq1420709 eq16
    | exact resolve eq16 eq1420709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420709
  have eq1422682 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1422681
       have r₂ := eq334788 x
       grind)
    | exact resolve eq1422681 eq334788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422681
  have eq1422901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq337291 x
       have i₂ := eq1422682
       grind)
    | exact superpose eq1422682 eq337291
    | exact resolve eq337291 eq1422682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422682
  have eq1423095 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1422901
       have r₂ := eq16
       grind)
    | exact resolve eq1422901 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422901
  have eq1425258 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1423095
       grind)
    | exact superpose eq1423095 eq10
    | exact resolve eq10 eq1423095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423095
  have eq1425975 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1425258
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1425258
    | exact resolve eq1425258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425258
  have eq1426276 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1425975
       grind)
    | exact superpose eq1425975 eq16
    | exact resolve eq16 eq1425975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425975
  have eq1426277 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1426276
       have r₂ := eq334788 x
       grind)
    | exact resolve eq1426276 eq334788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334788 eq1426276
  have eq1428261 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1426277
       grind)
    | exact superpose eq1426277 eq10
    | exact resolve eq10 eq1426277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426277
  have eq1428984 : y = (M.op x x) := by
    first
    | (have i₁ := eq1428261
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1428261
    | exact resolve eq1428261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428261
  have eq1429806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq337291 x
       have i₂ := eq1428984
       grind)
    | exact superpose eq1428984 eq337291
    | exact resolve eq337291 eq1428984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337291 eq1428984
  have eq1429944 : False := by grind
  exact eq1429944

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyx_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 x)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (M.op X2 (M.op X0 (M.op X0 X1))) = (k X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X0 X1))
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq79 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq155 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq74 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq74 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq158 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq157 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq160 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq161 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq160 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq3637 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq75 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3638 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3643 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3638 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3638
    | (have j0 := eq3638 X0
       grind)
    | exact resolve eq3638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq3649 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3643 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3643
    | exact resolve eq3643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq3685 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3649 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3649
    | (have j0 := eq3649 X0
       grind)
    | exact resolve eq3649 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3649
  have eq3690 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3685 X0
       grind)
    | exact superpose eq3685 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3685 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3685 X0
       grind)
    | exact resolve eq12 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq3710 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3690 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690
  have eq3800 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3710 X0 X1
       grind)
    | exact superpose eq3710 eq11
    | (have j1 := eq3710 X0 X1
       grind)
    | exact resolve eq11 eq3710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3907 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3800 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3800
    | (have j0 := eq3800 X0 X0
       grind)
    | exact resolve eq3800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800
  have eq4003 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3907 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907
  have eq4004 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4003 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003
  have eq4126 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq4004 X0
       grind)
    | exact superpose eq4004 eq158
    | (have j0 := eq158 X0
       grind)
    | exact resolve eq158 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq4127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq4004 X0
       grind)
    | exact superpose eq4004 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq4162 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4004 (σ X0)
       grind)
    | exact superpose eq4004 eq15
    | exact resolve eq15 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4226 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4162 X0
       have i₂ := eq4004 X0
       grind)
    | exact superpose eq4004 eq4162
    | exact resolve eq4162 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004 eq4162
  have eq4386 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq4434 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4386 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq4386
    | (have j0 := eq4386 X0 X0
       grind)
    | exact resolve eq4386 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq4386
  have eq4536 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq4226 X0
       grind)
    | exact superpose eq4226 eq9
    | exact resolve eq9 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7357 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X0
       have i₂ := eq4434 X0 X1
       grind)
    | exact superpose eq4434 eq67
    | (have j1 := eq4434 X0 X1
       grind)
    | exact resolve eq67 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434
  have eq35848 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 (M.op X1 X1)) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq7357 X1 X0
       grind)
    | exact superpose eq7357 eq11
    | (have j1 := eq7357 X1 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7357
  have eq36045 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35848 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq35848
    | (have j0 := eq35848 (M.op X1 X1) X1
       grind)
    | exact resolve eq35848 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35848
  have eq36138 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X1 X1 X2
       have i₂ := eq36045 X0 X1
       grind)
    | exact superpose eq36045 eq33
    | (have j1 := eq36045 X2 X0
       grind)
    | (have r₁ := eq33 X1 X1 X2
       have r₂ := eq36045 X0 X1
       grind)
    | (have r₁ := eq33 X1 X1 X2
       have r₂ := eq36045 (M.op X1 X1) X1
       grind)
    | exact resolve eq33 eq36045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq36045
  have eq36288 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq36138 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36138
  have eq37733 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36288 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36288
  have eq37734 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37733 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37733
  have eq37837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq37734 (σ X0) (σ X1)
       grind)
    | exact superpose eq37734 eq15
    | (have j1 := eq37734 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq37734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37841 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq37734 (τ X0) X1
       grind)
    | exact superpose eq37734 eq17
    | (have j1 := eq37734 (τ X0) X1
       grind)
    | exact resolve eq17 eq37734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq37734
  have eq39411 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37841 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37841
    | exact resolve eq37841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37841
  have eq39701 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39411 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39411
    | (have j0 := eq39411 X0 X1
       grind)
    | exact resolve eq39411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39411
  have eq45986 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37837 x y
       grind)
    | exact superpose eq37837 eq16
    | (have j1 := eq37837 x y
       grind)
    | exact resolve eq16 eq37837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37837
  have eq46349 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq45986
       have i₂ := eq39701 x y
       grind)
    | exact superpose eq39701 eq45986
    | (have j1 := eq39701 (σ x) (σ y)
       grind)
    | (have r₁ := eq45986
       have r₂ := eq39701 x y
       grind)
    | exact resolve eq45986 eq39701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39701 eq45986
  have eq46352 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq46349
  have eq46672 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq67 y x
       have i₂ := eq46352
       grind)
    | exact superpose eq46352 eq67
    | exact resolve eq67 eq46352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46352
  have eq46749 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq67 (σ y) (σ x)
       have i₂ := eq46672
       grind)
    | exact superpose eq46672 eq67
    | exact resolve eq67 eq46672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq46672
  have eq46816 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq46749
       have i₂ := eq4226 y
       grind)
    | exact superpose eq4226 eq46749
    | exact resolve eq46749 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46749
  have eq48214 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq4536 y (σ (M.op y y))
       have i₂ := eq46816
       grind)
    | exact superpose eq46816 eq4536
    | exact resolve eq4536 eq46816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536 eq46816
  have eq48311 : y = (M.op y (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq48214
       have i₂ := eq4226 y
       grind)
    | exact superpose eq4226 eq48214
    | exact resolve eq48214 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48214
  have eq48751 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq48311
       grind)
    | exact superpose eq48311 eq9
    | exact resolve eq9 eq48311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48886 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq48751 (M.op y y)
       have i₂ := eq48311
       grind)
    | exact superpose eq48311 eq48751
    | exact resolve eq48751 eq48311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48311 eq48751
  have eq48959 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq48886
  have eq49357 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4126 y
       have i₂ := eq48959
       grind)
    | exact superpose eq48959 eq4126
    | (have j0 := eq4126 y
       grind)
    | (have r₁ := eq4126 y
       have r₂ := eq48959
       grind)
    | exact resolve eq4126 eq48959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49358 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq4127 y X0
       have i₂ := eq48959
       grind)
    | exact superpose eq48959 eq4127
    | (have j0 := eq4127 y X0
       grind)
    | (have r₁ := eq4127 y x
       have r₂ := eq48959
       grind)
    | exact resolve eq4127 eq48959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48959
  have eq49459 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq49358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49358
  have eq49460 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq49357
  have eq49493 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq49459 X0
       have j1 := eq4127 y X0
       grind)
    | (have r₁ := eq49459 X0
       have r₂ := eq4127 y x
       grind)
    | exact resolve eq49459 eq4127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127 eq49459
  have eq49494 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq4126 y
       grind)
    | (have r₁ := eq49460
       have r₂ := eq4126 y
       grind)
    | exact resolve eq49460 eq4126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126 eq49460
  have eq49516 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq49494
       have i₂ := eq4226 y
       grind)
    | exact superpose eq4226 eq49494
    | exact resolve eq49494 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226 eq49494
  have eq49541 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq49516
       grind)
    | exact superpose eq49516 eq10
    | exact resolve eq10 eq49516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49516
  have eq49714 : y = (M.op y y) := by
    first
    | (have i₁ := eq49541
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq49541
    | exact resolve eq49541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49541
  have eq50197 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq49714
       grind)
    | exact superpose eq49714 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq49714
       grind)
    | exact resolve eq12 eq49714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49714
  have eq50304 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq50197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50197
  have eq51785 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq49493 (σ X0)
       grind)
    | exact superpose eq49493 eq15
    | exact resolve eq15 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49493
  have eq51882 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq51785 X0
       have i₂ := eq50304 X0
       grind)
    | exact superpose eq50304 eq51785
    | exact resolve eq51785 eq50304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50304 eq51785
  have eq54145 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51882 x
       grind)
    | exact superpose eq51882 eq16
    | (have r₁ := eq16
       have r₂ := eq51882 x
       grind)
    | exact resolve eq16 eq51882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51882
  have eq54282 : False := by grind
  exact eq54282

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k (σ X0) X1)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq243 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103 x y
       grind)
    | exact superpose eq103 eq16
    | (have j1 := eq103 x y
       grind)
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq2042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq243
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq243
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq243
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq243
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq243 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq2043 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2042
  have eq2265 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 (τ X0) (τ X1)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq251
    | (have j0 := eq251 (τ X0) (τ X1)
       grind)
    | exact resolve eq251 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2290 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2265 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2265
    | (have j0 := eq2265 X0 X1
       grind)
    | exact resolve eq2265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq2304 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2290 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq2290
    | (have j0 := eq2290 X0 X1
       grind)
    | exact resolve eq2290 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2313 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2304 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2304
    | (have j0 := eq2304 X0 X1
       grind)
    | exact resolve eq2304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq2316 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2313 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2313
    | (have j0 := eq2313 X0 X1
       grind)
    | exact resolve eq2313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313
  have eq2318 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2316 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq2316
    | (have j0 := eq2316 X0 X1
       grind)
    | exact resolve eq2316 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2316
  have eq2319 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2318 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2318
    | (have j0 := eq2318 X0 X1
       grind)
    | exact resolve eq2318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2320 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2319 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2319
    | (have j0 := eq2319 X0 X1
       grind)
    | exact resolve eq2319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq31473 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq16
    | exact resolve eq16 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq31474 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq31473
       have r₂ := eq22 x
       grind)
    | exact resolve eq31473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31473
  have eq45456 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq31474
       grind)
    | exact superpose eq31474 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq31474
       grind)
    | exact resolve eq13 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31474
  have eq45527 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq45456
  have eq715146 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45527
       grind)
    | exact superpose eq45527 eq16
    | exact resolve eq16 eq45527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45527
  have eq715147 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq715146
       have r₂ := eq22 x
       grind)
    | exact resolve eq715146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715146
  have eq715157 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq251 x y
       have i₂ := eq715147
       grind)
    | exact superpose eq715147 eq251
    | (have j0 := eq251 x y
       grind)
    | exact resolve eq251 eq715147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq715147
  have eq715237 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq715157
  have eq715238 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq715237
  have eq716208 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq715238
       grind)
    | exact superpose eq715238 eq16
    | exact resolve eq16 eq715238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716211 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63 x (σ y)
       have i₂ := eq715238
       grind)
    | exact superpose eq715238 eq63
    | (have j0 := eq63 x (σ y)
       grind)
    | (have r₁ := eq63 x (σ y)
       have r₂ := eq715238
       grind)
    | exact resolve eq63 eq715238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq715238
  have eq716615 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq716211
  have eq716616 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq716615
  have eq716824 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq716616
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq716616
    | exact resolve eq716616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716616
  have eq717846 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq716824
       grind)
    | exact superpose eq716824 eq10
    | exact resolve eq10 eq716824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716824
  have eq718504 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq717846
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq717846
    | exact resolve eq717846 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717846
  have eq718506 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq718504
       grind)
    | exact superpose eq718504 eq16
    | exact resolve eq16 eq718504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718504
  have eq718507 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq718506
       have r₂ := eq22 x
       grind)
    | exact resolve eq718506 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718506
  have eq719918 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq718507
       grind)
    | exact superpose eq718507 eq10
    | exact resolve eq10 eq718507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718507
  have eq720580 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq719918
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq719918
    | exact resolve eq719918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719918
  have eq720605 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2320 x y
       have i₂ := eq720580
       grind)
    | exact superpose eq720580 eq2320
    | (have j0 := eq2320 x y
       grind)
    | (have r₁ := eq2320 x y
       have r₂ := eq720580
       grind)
    | exact resolve eq2320 eq720580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320 eq720580
  have eq720653 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq720605
  have eq722057 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq720653
       grind)
    | exact superpose eq720653 eq16
    | exact resolve eq16 eq720653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720653
  have eq722060 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq722057
       have r₂ := eq22 x
       grind)
    | exact resolve eq722057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722057
  have eq722061 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq716208
       have i₂ := eq722060
       grind)
    | exact superpose eq722060 eq716208
    | exact resolve eq716208 eq722060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716208
  have eq722361 : (σ x) = (σ y) := by grind
  clear eq722061
  have eq723335 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq722361
       grind)
    | exact superpose eq722361 eq16
    | exact resolve eq16 eq722361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722361
  have eq724000 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq723335
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq723335
    | exact resolve eq723335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq723335
  have eq724005 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq724000
       have i₂ := eq722060
       grind)
    | exact superpose eq722060 eq724000
    | exact resolve eq724000 eq722060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722060 eq724000
  have eq724006 : False := by grind
  exact eq724006

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq528 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq531 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3334 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq528 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq528
    | exact resolve eq528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq3385 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3334 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3334
    | (have j0 := eq3334 X0 X1
       grind)
    | exact resolve eq3334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3427 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq531 x y
       grind)
    | exact superpose eq531 eq16
    | (have j1 := eq531 y x
       grind)
    | exact resolve eq16 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3442 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3427
       have i₂ := eq3385 x y
       grind)
    | exact superpose eq3385 eq3427
    | (have j1 := eq3385 (σ x) (σ y)
       grind)
    | (have r₁ := eq3427
       have r₂ := eq3385 x y
       grind)
    | (have r₁ := eq3427
       have r₂ := eq3385 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3427
       have r₂ := eq3385 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3427 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq6191 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq6190
  have eq7358 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3442 X1 X0
       have i₂ := eq531 X0 X1
       grind)
    | exact superpose eq531 eq3442
    | (have j0 := eq3442 X0 X1
       have j1 := eq531 X0 X1
       grind)
    | (have r₁ := eq3442 X0 X0
       have r₂ := eq531 X0 X0
       grind)
    | exact resolve eq3442 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq7359 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7358
  have eq7360 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7359 X0 X1
       have j1 := eq3442 X0 X1
       grind)
    | (have r₁ := eq7359 X0 X1
       have r₂ := eq3442 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq7359 X0 X1
       have r₂ := eq3442 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq7359 X1 X0
       have r₂ := eq3442 X0 X1
       grind)
    | exact resolve eq7359 eq3442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442 eq7359
  have eq19040 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6191
       grind)
    | exact superpose eq6191 eq16
    | exact resolve eq16 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq19041 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19040
       have r₂ := eq22 x
       grind)
    | exact resolve eq19040 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19040
  have eq19044 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19041
       grind)
    | exact superpose eq19041 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19041
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19041
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19041
       grind)
    | exact resolve eq13 eq19041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19041
  have eq19046 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19044
  have eq19269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19046
       grind)
    | exact superpose eq19046 eq16
    | exact resolve eq16 eq19046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19046
  have eq19270 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq19269
       have r₂ := eq22 x
       grind)
    | exact resolve eq19269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269
  have eq19275 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19270
       grind)
    | exact superpose eq19270 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19270
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19270
       grind)
    | exact resolve eq13 eq19270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19276 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19270
       grind)
    | exact superpose eq19270 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19270
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19270
       grind)
    | exact resolve eq13 eq19270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19270
  have eq19278 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq19276
  have eq19279 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq19278
  have eq19280 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq19275
  have eq19281 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq19280
  have eq19284 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq19279
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19279
    | exact resolve eq19279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19279
  have eq19285 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq19281
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19281
    | exact resolve eq19281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19281
  have eq19321 : (σ (k y x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq19284
       have i₂ := eq19285
       grind)
    | exact superpose eq19285 eq19284
    | exact resolve eq19284 eq19285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19284 eq19285
  have eq19342 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq19321
  have eq19353 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq3427
       have i₂ := eq19342
       grind)
    | exact superpose eq19342 eq3427
    | exact resolve eq3427 eq19342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427
  have eq19365 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq19353
  have eq19366 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq19365
  have eq19369 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq7360 x y
       grind)
    | (have r₁ := eq19366
       have r₂ := eq7360 y x
       grind)
    | (have r₁ := eq19366
       have r₂ := eq7360 x y
       grind)
    | exact resolve eq19366 eq7360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7360 eq19366
  have eq19375 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19369
       grind)
    | exact superpose eq19369 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19369
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19369
       grind)
    | exact resolve eq13 eq19369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19369
  have eq19377 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq19375
  have eq19378 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq19377
  have eq19383 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19378
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19378
    | exact resolve eq19378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19378
  have eq19389 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19383
       grind)
    | exact superpose eq19383 eq16
    | exact resolve eq16 eq19383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19383
  have eq19420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq19389
       have i₂ := eq19342
       grind)
    | exact superpose eq19342 eq19389
    | exact resolve eq19389 eq19342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19342
  have eq19425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq19420
  have eq19426 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq19425
  have eq19428 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19426
       grind)
    | exact superpose eq19426 eq10
    | exact resolve eq10 eq19426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19426
  have eq19598 : x = y ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq19428
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19428
    | exact resolve eq19428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19428
  have eq19600 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19598
       grind)
    | exact superpose eq19598 eq16
    | exact resolve eq16 eq19598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19598
  have eq19601 : (σ (k y x)) = (σ (k x y)) := by
    first
    | (have r₁ := eq19600
       have r₂ := eq22 x
       grind)
    | exact resolve eq19600 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19600
  have eq19614 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19389
       have i₂ := eq19601
       grind)
    | exact superpose eq19601 eq19389
    | exact resolve eq19389 eq19601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19389
  have eq19626 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq19601
       grind)
    | exact superpose eq19601 eq10
    | exact resolve eq10 eq19601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19601
  have eq19798 : (k y x) = (k x y) := by
    first
    | (have i₁ := eq19626
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq19626
    | exact resolve eq19626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19626
  have eq19804 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19798
       grind)
    | exact superpose eq19798 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq19798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19798
  have eq19850 : x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq19804
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq19804
       have r₂ := eq13 y x
       grind)
    | exact resolve eq19804 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19804
  have eq19861 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19850
       grind)
    | exact superpose eq19850 eq16
    | exact resolve eq16 eq19850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19850
  have eq19862 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq19861
       have r₂ := eq22 x
       grind)
    | exact resolve eq19861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19861
  have eq21941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19614
       have i₂ := eq19862
       grind)
    | exact superpose eq19862 eq19614
    | exact resolve eq19614 eq19862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19614 eq19862
  have eq21944 : (σ x) = (σ y) := by grind
  clear eq21941
  have eq21945 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21944
       grind)
    | exact superpose eq21944 eq16
    | exact resolve eq16 eq21944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21946 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21944
       grind)
    | exact superpose eq21944 eq10
    | exact resolve eq10 eq21944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21944
  have eq22116 : x = y := by
    first
    | (have i₁ := eq21946
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21946
    | exact resolve eq21946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21946
  have eq22117 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21945
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq21945
    | exact resolve eq21945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21945
  have eq22118 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22117
       have i₂ := eq22116
       grind)
    | exact superpose eq22116 eq22117
    | exact resolve eq22117 eq22116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22116 eq22117
  have eq22119 : False := by grind
  exact eq22119

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq516 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq561 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq3539 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq16
    | (have j1 := eq561 x y
       grind)
    | exact resolve eq16 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3554 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq3589 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq552
    | exact resolve eq552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq3640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3589 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3589
    | (have j0 := eq3589 X0 X1
       grind)
    | exact resolve eq3589 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq7071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3539
       have i₂ := eq3640 y x
       grind)
    | exact superpose eq3640 eq3539
    | (have j1 := eq3640 y x
       grind)
    | (have r₁ := eq3539
       have r₂ := eq3640 y x
       grind)
    | (have r₁ := eq3539
       have r₂ := eq3640 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3539
       have r₂ := eq3640 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3539 eq3640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539 eq3640
  have eq7072 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7071
  have eq7090 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3554 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3554
    | (have j0 := eq3554 (τ X1) (τ X0)
       grind)
    | exact resolve eq3554 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7148 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7090 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7090
    | (have j0 := eq7090 X0 X1
       grind)
    | exact resolve eq7090 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7090
  have eq7183 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7148 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7148
    | (have j0 := eq7148 X0 X1
       grind)
    | exact resolve eq7148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7148
  have eq7215 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7183 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7183
    | (have j0 := eq7183 X0 X1
       grind)
    | exact resolve eq7183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7183
  have eq7241 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7215 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7215
    | (have j0 := eq7215 X0 X1
       grind)
    | exact resolve eq7215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7215
  have eq7261 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7241 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7241
    | (have j0 := eq7241 X0 X1
       grind)
    | exact resolve eq7241 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7241
  have eq7280 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7261 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7261
    | (have j0 := eq7261 X0 X1
       grind)
    | exact resolve eq7261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7261
  have eq7293 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7280 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7280
    | (have j0 := eq7280 X0 X1
       grind)
    | exact resolve eq7280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7280
  have eq15199 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7072
       grind)
    | exact superpose eq7072 eq16
    | exact resolve eq16 eq7072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7072
  have eq15200 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15199
       have r₂ := eq22 x
       grind)
    | exact resolve eq15199 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15199
  have eq15203 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15200
       grind)
    | exact superpose eq15200 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15200
       grind)
    | exact resolve eq13 eq15200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15200
  have eq15205 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15203
  have eq16885 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15205
       grind)
    | exact superpose eq15205 eq16
    | exact resolve eq16 eq15205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15205
  have eq16886 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq16885
       have r₂ := eq22 x
       grind)
    | exact resolve eq16885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16885
  have eq16889 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq516 x (σ y)
       have i₂ := eq16886
       grind)
    | exact superpose eq16886 eq516
    | (have j0 := eq516 x (σ y)
       grind)
    | (have r₁ := eq516 x (σ y)
       have r₂ := eq16886
       grind)
    | exact resolve eq516 eq16886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16886
  have eq16903 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq16889
  have eq16904 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq16903
  have eq16910 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16904
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16904
    | exact resolve eq16904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16904
  have eq16922 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3554 x y
       have i₂ := eq16910
       grind)
    | exact superpose eq16910 eq3554
    | (have j0 := eq3554 x y
       grind)
    | (have r₁ := eq3554 x y
       have r₂ := eq16910
       grind)
    | exact resolve eq3554 eq16910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16910
  have eq16948 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq16922
  have eq16949 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq16948
  have eq16953 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3554 x y
       grind)
    | (have r₁ := eq16949
       have r₂ := eq3554 x y
       grind)
    | exact resolve eq16949 eq3554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554 eq16949
  have eq16956 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16953
       grind)
    | exact superpose eq16953 eq16
    | exact resolve eq16 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16957 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq516 x (σ y)
       have i₂ := eq16953
       grind)
    | exact superpose eq16953 eq516
    | (have j0 := eq516 x (σ y)
       grind)
    | (have r₁ := eq516 x (σ y)
       have r₂ := eq16953
       grind)
    | exact resolve eq516 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq16953
  have eq16971 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq16957
  have eq16972 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq16971
  have eq16978 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16972
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16972
    | exact resolve eq16972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16972
  have eq16988 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16978
       grind)
    | exact superpose eq16978 eq10
    | exact resolve eq10 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16978
  have eq17156 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16988
    | exact resolve eq16988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16988
  have eq17158 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17156
       grind)
    | exact superpose eq17156 eq16
    | exact resolve eq16 eq17156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17156
  have eq17159 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17158
       have r₂ := eq22 x
       grind)
    | exact resolve eq17158 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17158
  have eq17172 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq17159
       grind)
    | exact superpose eq17159 eq10
    | exact resolve eq10 eq17159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17159
  have eq17341 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq17172
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17172
    | exact resolve eq17172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17172
  have eq17370 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7293 y x
       have i₂ := eq17341
       grind)
    | exact superpose eq17341 eq7293
    | (have j0 := eq7293 y x
       grind)
    | (have r₁ := eq7293 y x
       have r₂ := eq17341
       grind)
    | exact resolve eq7293 eq17341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293 eq17341
  have eq17373 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17370
  have eq17377 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16956
       have i₂ := eq17373
       grind)
    | exact superpose eq17373 eq16956
    | exact resolve eq16956 eq17373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16956 eq17373
  have eq17386 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17377
  have eq17387 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17386
       grind)
    | exact superpose eq17386 eq16
    | exact resolve eq16 eq17386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17386
  have eq17390 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17387
       have r₂ := eq22 x
       grind)
    | exact resolve eq17387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387
  have eq17391 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17390
       grind)
    | exact superpose eq17390 eq16
    | exact resolve eq16 eq17390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17392 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17390
       grind)
    | exact superpose eq17390 eq10
    | exact resolve eq10 eq17390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17390
  have eq17560 : x = y := by
    first
    | (have i₁ := eq17392
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17392
    | exact resolve eq17392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq17561 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17391
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17391
    | exact resolve eq17391 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17391
  have eq17562 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17561
       have i₂ := eq17560
       grind)
    | exact superpose eq17560 eq17561
    | exact resolve eq17561 eq17560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17560 eq17561
  have eq17563 : False := by grind
  exact eq17563

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxy_pyx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq175 eq180
    | exact resolve eq180 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq594 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq612 : x = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq593 eq180
    | exact resolve eq180 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : x = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq593 eq16
    | exact resolve eq16 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq620 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq594 eq180
    | exact resolve eq180 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq621 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq594 eq16
    | exact resolve eq16 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq703 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq713 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq723 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq763 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq703
       grind)
    | exact superpose eq703 eq41
    | exact resolve eq41 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq703
  have eq764 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq763
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq763
    | exact resolve eq763 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq766 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq764
    | exact resolve eq764 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq766 eq713
    | exact resolve eq713 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq766
  have eq783 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq776
       have r₂ := eq27
       grind)
    | exact resolve eq776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq793 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq783 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq783
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq783
       grind)
    | exact resolve eq13 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq796 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq793
  have eq800 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq796 eq142
    | exact resolve eq142 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq796
  have eq803 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq800
    | exact resolve eq800 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq800
  have eq806 : x = (M.op x x) := by
    first
    | (have j1 := eq723 x
       grind)
    | (have r₁ := eq803
       have r₂ := eq723 x
       grind)
    | exact resolve eq803 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq810 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq188
    | exact resolve eq188 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq815 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq806
       grind)
    | exact resolve eq13 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : x = (k x x) := by grind
  clear eq815
  have eq821 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq40
    | exact resolve eq40 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq818
  have eq824 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq821
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq821
    | exact resolve eq821 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq829 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq824 eq723
    | (have j0 := eq723 (σ x)
       grind)
    | (have r₁ := eq723 (σ x)
       have r₂ := eq824
       grind)
    | exact resolve eq723 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq824
  have eq830 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq829
  have eq835 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq830 eq195
    | exact resolve eq195 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq848 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq810 eq178
    | exact resolve eq178 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq810
  have eq856 : (M.op x (M.op x y)) = (M.op x x) := by
    first
    | exact superpose eq613 eq848
    | exact resolve eq848 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq848
  have eq858 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq856
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq856
    | exact resolve eq856 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq863 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq858 eq612
    | exact resolve eq612 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq858
  have eq877 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq863 eq186
    | exact resolve eq186 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq863
  have eq889 : x = (M.op x y) := by
    first
    | (have i₁ := eq806
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq806
    | exact resolve eq806 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq877
  have eq903 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq22
    | exact resolve eq22 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq889
  have eq929 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq903 eq20
    | exact resolve eq20 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq903
  have eq1087 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq835 eq179
    | exact resolve eq179 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq835
  have eq1095 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq621 eq1087
    | exact resolve eq1087 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq1087
  have eq1097 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq830 eq1095
    | exact resolve eq1095 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1102 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1097 eq620
    | exact resolve eq620 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq1097
  have eq1116 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1102 eq193
    | exact resolve eq193 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq1102
  have eq1126 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq830 eq1116
    | exact resolve eq1116 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq1116
  have eq1128 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1126 eq27
    | exact resolve eq27 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1126
  have eq1147 : False := by grind
  exact eq1147

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq82 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq93
  have eq234 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq266 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq234
  have eq270 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq266 X0 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq266 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq266
  have eq274 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq270
  have eq963 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq274
    | exact resolve eq274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq1058 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq963 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq963 X0 X1
       grind)
    | exact superpose eq963 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq963 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq963 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq963 X0 X1
       grind)
    | exact resolve eq13 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1058 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1112 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1102 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1102 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1194 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1198 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1194 X0 X1
       have j1 := eq963 X1 X0
       grind)
    | (have r₁ := eq1194 X0 X0
       have r₂ := eq963 X0 X0
       grind)
    | (have r₁ := eq1194 X1 X0
       have r₂ := eq963 X0 X1
       grind)
    | exact resolve eq1194 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq1194
  have eq1332 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1198 (σ X0) (σ X1)
       grind)
    | exact superpose eq1198 eq15
    | exact resolve eq15 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1332 X0 X1
       have i₂ := eq1198 X0 X1
       grind)
    | exact superpose eq1198 eq1332
    | exact resolve eq1332 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq1332
  have eq1998 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1359 x y
       grind)
    | exact superpose eq1359 eq16
    | (have r₁ := eq16
       have r₂ := eq1359 x y
       grind)
    | exact resolve eq16 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq2034 : False := by grind
  exact eq2034

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq57
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80
    | (have j0 := eq80 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq80 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq141
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq141
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | (have r₁ := eq141
       have r₂ := eq80 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq141
       have r₂ := eq80 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq141 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq141
  have eq270 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq267
  have eq271 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270
       grind)
    | exact superpose eq270 eq16
    | exact resolve eq16 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq272 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq271
       have r₂ := eq66 x
       grind)
    | exact resolve eq271 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq308 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq272
       grind)
    | exact superpose eq272 eq10
    | exact resolve eq10 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq325 : x = y := by
    first
    | (have i₁ := eq308
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq308
    | exact resolve eq308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq369 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq325
       grind)
    | exact superpose eq325 eq16
    | exact resolve eq16 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq370 : False := by grind
  exact eq370
