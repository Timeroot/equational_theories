import equational_theories.Definability.ArgumentSwap
import equational_theories.Definability.Jb_104
import equational_theories.Definability.Jb_3735_pxy_x_pxy_y_y_x_pxy
import equational_theories.Definability.Jb_4343_pxy_x_pxy_y_y_x_pxy
import equational_theories.Definability.Jb_4470
import equational_theories.Definability.Jc_3634_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Jlf3_433
import equational_theories.Definability.Jr_3587
import equational_theories.Definability.Lc_224
import equational_theories.Definability.Lc_23
import equational_theories.Definability.Lc_31_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Lc_3272
import equational_theories.Definability.Lc_332
import equational_theories.Definability.Lc_335
import equational_theories.Definability.Lc_3484_pxy_y_pxy_x_x_y_pxy
import equational_theories.Definability.Lc_359_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Lc_365_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Lc_3715
import equational_theories.Definability.Lc_3735
import equational_theories.Definability.Lc_377_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Lc_384
import equational_theories.Definability.Lc_4439
import equational_theories.Definability.Lc_53
import equational_theories.Definability.Lc_633
import equational_theories.Definability.Le_1101_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Le_2105
import equational_theories.Definability.Le_2739
import equational_theories.Definability.Le_3147_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Le_3566
import equational_theories.Definability.Le_3863_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Le_3919_pxy_y_pxy_x_x_y_pxy
import equational_theories.Definability.Le_3919_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Le_3926_pxy_y_pxy_x_x_y_pxy
import equational_theories.Definability.Le_3926_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Le_3929_pxy_y_pxy_x_x_y_pxy
import equational_theories.Definability.Le_3929_pyx_y_pyx_x_x_y_pyx
import equational_theories.Definability.Mwf_3145
import equational_theories.Definability.Mwf_3907
import equational_theories.Definability.Wkg_854

/-!
# Arbitrary-carrier structural consequences of argument swapping

These 47 statements generate every upgrade found among the 1,547 previously
open finite certificates for the four argument-swap syntaxes. Two high-impact
cases have elementary proofs in ArgumentSwap.lean. For the remaining 45,
`recover_argument_swap` reuses existing closed target-law proofs, which already
quantify over arbitrary carriers, and supplies the explicit inverse instead of
finite automorphism recovery. See ArgumentSwap.lean and
docs/definability_argument_swap.md for the construction and validation.

Arrows are source → target, whereas Lean writes the target first.
The list is a generating set, not a claim of mathematical independence.
-/

open Law Law.MagmaLaw

theorem Equation312_structuralFrom_Equation31_argumentSwap :
    Law312.StructuralFrom Law31 :=
  structuralFrom_argumentSwap true true fun {G} M hM ↦
    (@Law312.models_iff G ((QFOp.argumentSwap true true).magma M)).mpr
      (ArgumentSwap.equation312 M (Law31.models_iff.mp hM))

theorem Equation8_structuralFrom_Equation359_argumentSwap :
    Law8.StructuralFrom Law359 :=
  structuralFrom_argumentSwap true true fun {G} M hM ↦
    (@Law8.models_iff G ((QFOp.argumentSwap true true).magma M)).mpr
      (ArgumentSwap.equation8 M (Law359.models_iff.mp hM))

theorem Equation4484_structuralFrom_Equation2105_argumentSwap :
    Law4484.StructuralFrom Law2105 := by
  recover_argument_swap Equation4484_StructuralFromFin_Equation2105

theorem Equation658_structuralFrom_Equation3907_argumentSwap :
    Law658.StructuralFrom Law3907 := by
  recover_argument_swap Equation658_StructuralFromFin_Equation3907

theorem Equation316_structuralFrom_Equation1101_argumentSwap :
    Law316.StructuralFrom Law1101 := by
  recover_argument_swap Equation316_StructuralFromFin_Equation1101

theorem Equation307_structuralFrom_Equation23_argumentSwap :
    Law307.StructuralFrom Law23 := by
  recover_argument_swap Equation307_StructuralFromFin_Equation23

theorem Equation643_structuralFrom_Equation3863_argumentSwap :
    Law643.StructuralFrom Law3863 := by
  recover_argument_swap Equation643_StructuralFromFin_Equation3863

theorem Equation316_structuralFrom_Equation3147_argumentSwap :
    Law316.StructuralFrom Law3147 := by
  recover_argument_swap Equation316_StructuralFromFin_Equation3147

theorem Equation3473_structuralFrom_Equation2105_argumentSwap :
    Law3473.StructuralFrom Law2105 := by
  recover_argument_swap Equation3473_StructuralFromFin_Equation2105

theorem Equation817_structuralFrom_Equation4470_argumentSwap :
    Law817.StructuralFrom Law4470 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation4470

theorem Equation1020_structuralFrom_Equation104_argumentSwap :
    Law1020.StructuralFrom Law104 := by
  recover_argument_swap Equation1020_StructuralFromFin_Equation104

theorem Equation1426_structuralFrom_Equation3715_argumentSwap :
    Law1426.StructuralFrom Law3715 := by
  recover_argument_swap Equation1426_StructuralFromFin_Equation3715

theorem Equation614_structuralFrom_Equation3715_argumentSwap :
    Law614.StructuralFrom Law3715 := by
  recover_argument_swap Equation614_StructuralFromFin_Equation3715

theorem Equation647_structuralFrom_Equation3587_argumentSwap :
    Law647.StructuralFrom Law3587 := by
  recover_argument_swap Equation647_StructuralFromFin_Equation3587

theorem Equation1023_structuralFrom_Equation2739_argumentSwap :
    Law1023.StructuralFrom Law2739 := by
  recover_argument_swap Equation1023_StructuralFromFin_Equation2739

theorem Equation817_structuralFrom_Equation3484_argumentSwap :
    Law817.StructuralFrom Law3484 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation3484

theorem Equation817_structuralFrom_Equation4343_argumentSwap :
    Law817.StructuralFrom Law4343 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation4343

theorem Equation3461_structuralFrom_Equation433_argumentSwap :
    Law3461.StructuralFrom Law433 := by
  recover_argument_swap Equation3461_StructuralFromFin_Equation433

theorem Equation3318_structuralFrom_Equation3145_argumentSwap :
    Law3318.StructuralFrom Law3145 := by
  recover_argument_swap Equation3318_StructuralFromFin_Equation3145

theorem Equation1429_structuralFrom_Equation3929_argumentSwap :
    Law1429.StructuralFrom Law3929 := by
  recover_argument_swap Equation1429_StructuralFromFin_Equation3929

theorem Equation622_structuralFrom_Equation3926_argumentSwap :
    Law622.StructuralFrom Law3926 := by
  recover_argument_swap Equation622_StructuralFromFin_Equation3926

theorem Equation1515_structuralFrom_Equation3926_argumentSwap :
    Law1515.StructuralFrom Law3926 := by
  recover_argument_swap Equation1515_StructuralFromFin_Equation3926

theorem Equation1023_structuralFrom_Equation854_argumentSwap :
    Law1023.StructuralFrom Law854 := by
  recover_argument_swap Equation1023_StructuralFromFin_Equation854

theorem Equation1223_structuralFrom_Equation53_argumentSwap :
    Law1223.StructuralFrom Law53 := by
  recover_argument_swap Equation1223_StructuralFromFin_Equation53

theorem Equation823_structuralFrom_Equation224_argumentSwap :
    Law823.StructuralFrom Law224 := by
  recover_argument_swap Equation823_StructuralFromFin_Equation224

theorem Equation1020_structuralFrom_Equation633_argumentSwap :
    Law1020.StructuralFrom Law633 := by
  recover_argument_swap Equation1020_StructuralFromFin_Equation633

theorem Equation817_structuralFrom_Equation3272_argumentSwap :
    Law817.StructuralFrom Law3272 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation3272

theorem Equation1023_structuralFrom_Equation3735_argumentSwap :
    Law1023.StructuralFrom Law3735 := by
  recover_argument_swap Equation1023_StructuralFromFin_Equation3735

theorem Equation1691_structuralFrom_Equation3735_argumentSwap :
    Law1691.StructuralFrom Law3735 := by
  recover_argument_swap Equation1691_StructuralFromFin_Equation3735

theorem Equation817_structuralFrom_Equation4439_argumentSwap :
    Law817.StructuralFrom Law4439 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation4439

theorem Equation1223_structuralFrom_Equation332_argumentSwap :
    Law1223.StructuralFrom Law332 := by
  recover_argument_swap Equation1223_StructuralFromFin_Equation332

theorem Equation614_structuralFrom_Equation335_argumentSwap :
    Law614.StructuralFrom Law335 := by
  recover_argument_swap Equation614_StructuralFromFin_Equation335

theorem Equation1426_structuralFrom_Equation335_argumentSwap :
    Law1426.StructuralFrom Law335 := by
  recover_argument_swap Equation1426_StructuralFromFin_Equation335

theorem Equation817_structuralFrom_Equation365_argumentSwap :
    Law817.StructuralFrom Law365 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation365

theorem Equation817_structuralFrom_Equation377_argumentSwap :
    Law817.StructuralFrom Law377 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation377

theorem Equation817_structuralFrom_Equation384_argumentSwap :
    Law817.StructuralFrom Law384 := by
  recover_argument_swap Equation817_StructuralFromFin_Equation384

theorem Equation1223_structuralFrom_Equation384_argumentSwap :
    Law1223.StructuralFrom Law384 := by
  recover_argument_swap Equation1223_StructuralFromFin_Equation384

theorem Equation820_structuralFrom_Equation3735_argumentSwap :
    Law820.StructuralFrom Law3735 := by
  recover_argument_swap Equation820_StructuralFromFin_Equation3735

theorem Equation439_structuralFrom_Equation3145_argumentSwap :
    Law439.StructuralFrom Law3145 := by
  recover_argument_swap Equation439_StructuralFromFin_Equation3145

theorem Equation1429_structuralFrom_Equation3919_argumentSwap :
    Law1429.StructuralFrom Law3919 := by
  recover_argument_swap Equation1429_StructuralFromFin_Equation3919

theorem Equation1429_structuralFrom_Equation3926_argumentSwap :
    Law1429.StructuralFrom Law3926 := by
  recover_argument_swap Equation1429_StructuralFromFin_Equation3926

theorem Equation1691_structuralFrom_Equation3634_argumentSwap :
    Law1691.StructuralFrom Law3634 := by
  recover_argument_swap Equation1691_StructuralFromFin_Equation3634

theorem Equation622_structuralFrom_Equation3929_argumentSwap :
    Law622.StructuralFrom Law3929 := by
  recover_argument_swap Equation622_StructuralFromFin_Equation3929

theorem Equation3712_structuralFrom_Equation3566_argumentSwap :
    Law3712.StructuralFrom Law3566 := by
  recover_argument_swap Equation3712_StructuralFromFin_Equation3566

theorem Equation1515_structuralFrom_Equation3929_argumentSwap :
    Law1515.StructuralFrom Law3929 := by
  recover_argument_swap Equation1515_StructuralFromFin_Equation3929

theorem Equation1515_structuralFrom_Equation3919_argumentSwap :
    Law1515.StructuralFrom Law3919 := by
  recover_argument_swap Equation1515_StructuralFromFin_Equation3919

theorem Equation622_structuralFrom_Equation3919_argumentSwap :
    Law622.StructuralFrom Law3919 := by
  recover_argument_swap Equation622_StructuralFromFin_Equation3919

/-- info: Checked 47 argument-swap structural proofs: only the standard Lean axioms. -/
#guard_msgs in
run_elab do
  let names : List Lean.Name := [
    ``Equation312_structuralFrom_Equation31_argumentSwap,
    ``Equation8_structuralFrom_Equation359_argumentSwap,
    ``Equation4484_structuralFrom_Equation2105_argumentSwap,
    ``Equation658_structuralFrom_Equation3907_argumentSwap,
    ``Equation316_structuralFrom_Equation1101_argumentSwap,
    ``Equation307_structuralFrom_Equation23_argumentSwap,
    ``Equation643_structuralFrom_Equation3863_argumentSwap,
    ``Equation316_structuralFrom_Equation3147_argumentSwap,
    ``Equation3473_structuralFrom_Equation2105_argumentSwap,
    ``Equation817_structuralFrom_Equation4470_argumentSwap,
    ``Equation1020_structuralFrom_Equation104_argumentSwap,
    ``Equation1426_structuralFrom_Equation3715_argumentSwap,
    ``Equation614_structuralFrom_Equation3715_argumentSwap,
    ``Equation647_structuralFrom_Equation3587_argumentSwap,
    ``Equation1023_structuralFrom_Equation2739_argumentSwap,
    ``Equation817_structuralFrom_Equation3484_argumentSwap,
    ``Equation817_structuralFrom_Equation4343_argumentSwap,
    ``Equation3461_structuralFrom_Equation433_argumentSwap,
    ``Equation3318_structuralFrom_Equation3145_argumentSwap,
    ``Equation1429_structuralFrom_Equation3929_argumentSwap,
    ``Equation622_structuralFrom_Equation3926_argumentSwap,
    ``Equation1515_structuralFrom_Equation3926_argumentSwap,
    ``Equation1023_structuralFrom_Equation854_argumentSwap,
    ``Equation1223_structuralFrom_Equation53_argumentSwap,
    ``Equation823_structuralFrom_Equation224_argumentSwap,
    ``Equation1020_structuralFrom_Equation633_argumentSwap,
    ``Equation817_structuralFrom_Equation3272_argumentSwap,
    ``Equation1023_structuralFrom_Equation3735_argumentSwap,
    ``Equation1691_structuralFrom_Equation3735_argumentSwap,
    ``Equation817_structuralFrom_Equation4439_argumentSwap,
    ``Equation1223_structuralFrom_Equation332_argumentSwap,
    ``Equation614_structuralFrom_Equation335_argumentSwap,
    ``Equation1426_structuralFrom_Equation335_argumentSwap,
    ``Equation817_structuralFrom_Equation365_argumentSwap,
    ``Equation817_structuralFrom_Equation377_argumentSwap,
    ``Equation817_structuralFrom_Equation384_argumentSwap,
    ``Equation1223_structuralFrom_Equation384_argumentSwap,
    ``Equation820_structuralFrom_Equation3735_argumentSwap,
    ``Equation439_structuralFrom_Equation3145_argumentSwap,
    ``Equation1429_structuralFrom_Equation3919_argumentSwap,
    ``Equation1429_structuralFrom_Equation3926_argumentSwap,
    ``Equation1691_structuralFrom_Equation3634_argumentSwap,
    ``Equation622_structuralFrom_Equation3929_argumentSwap,
    ``Equation3712_structuralFrom_Equation3566_argumentSwap,
    ``Equation1515_structuralFrom_Equation3929_argumentSwap,
    ``Equation1515_structuralFrom_Equation3919_argumentSwap,
    ``Equation622_structuralFrom_Equation3919_argumentSwap]
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name}: unexpected axiom {ax}"
  Lean.logInfo "Checked 47 argument-swap structural proofs: only the standard Lean axioms."

/-- Regression checks: an unrelated goal and a certificate with the wrong proof
shape must not be accepted by the recovery tactic. No failed proof is admitted. -/
example : True := by
  fail_if_success recover_argument_swap Equation312_StructuralFromFin_Equation31
  fail_if_success recover_argument_swap Equation312_structuralFrom_Equation31_argumentSwap
  trivial
