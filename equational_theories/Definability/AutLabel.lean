import equational_theories.Definability.Lab_lab18h720a
import equational_theories.Definability.Lab_lab18h720a_L3279
import equational_theories.Definability.Lab_lab18h720a_L3345
import equational_theories.Definability.Lab_lab18h720a_L3475
import equational_theories.Definability.Lab_lab18h720a_L3482

/-!
# Refutations from the labelled coordinate frame

`AutPattern.lean` chooses a symmetry rather than a model: `Sym(S)` acting on `S^m` diagonally is a
group of automorphisms of every operation that only shuffles coordinates. That frame is rigid --
the group moves every point of the carrier the same way, so an invariant operation has nowhere to
keep information the symmetry cannot see. Adjoining a factor the group fixes pointwise,

    `Sym(S)` acting on `S^m × T`, trivially on `T`,

gives it somewhere: a label, a mode, a sign. The family grows in the way a source needs, and for
`m = 1` the frame does not depend on `|S|` at all -- the orbits are `(t₁, t₂, a = b?)` and the
assignments are equality patterns times label words, so `|S| = 6` decides it for every larger `S`.

With three labels the carrier is `Fin 18`, the group is `Sym(6)` of order 720, and the invariant
family has 198,359,290,368 members, searched rather than walked.
-/

open Law Law.MagmaLaw

theorem Equation3279_not_definableFrom_Equation3269 :
    ¬ Law3279.DefinableFrom Law3269 :=
  not_definableFrom_transportSearch (lab18h720aM3269 : Magma (Fin 18)) lab18h720aM3269_models
    lab18h720a.E lab18h720a.Einv lab18h720a.rep lab18h720a.tr lab18h720a.z lab18h720a.st envlab18h720a_Law3279
    ordlab18h720a_Law3279 lab18h720a.hl lab18h720a.hr lab18h720aM3269_endo lab18h720a.htr lab18h720a.hz lab18h720a.hst
    nolab18h720a_Law3279

theorem Equation3345_not_definableFrom_Equation3269 :
    ¬ Law3345.DefinableFrom Law3269 :=
  not_definableFrom_transportSearch (lab18h720aM3269 : Magma (Fin 18)) lab18h720aM3269_models
    lab18h720a.E lab18h720a.Einv lab18h720a.rep lab18h720a.tr lab18h720a.z lab18h720a.st envlab18h720a_Law3345
    ordlab18h720a_Law3345 lab18h720a.hl lab18h720a.hr lab18h720aM3269_endo lab18h720a.htr lab18h720a.hz lab18h720a.hst
    nolab18h720a_Law3345

theorem Equation3475_not_definableFrom_Equation3269 :
    ¬ Law3475.DefinableFrom Law3269 :=
  not_definableFrom_transportSearch (lab18h720aM3269 : Magma (Fin 18)) lab18h720aM3269_models
    lab18h720a.E lab18h720a.Einv lab18h720a.rep lab18h720a.tr lab18h720a.z lab18h720a.st envlab18h720a_Law3475
    ordlab18h720a_Law3475 lab18h720a.hl lab18h720a.hr lab18h720aM3269_endo lab18h720a.htr lab18h720a.hz lab18h720a.hst
    nolab18h720a_Law3475

theorem Equation3482_not_definableFrom_Equation3269 :
    ¬ Law3482.DefinableFrom Law3269 :=
  not_definableFrom_transportSearch (lab18h720aM3269 : Magma (Fin 18)) lab18h720aM3269_models
    lab18h720a.E lab18h720a.Einv lab18h720a.rep lab18h720a.tr lab18h720a.z lab18h720a.st envlab18h720a_Law3482
    ordlab18h720a_Law3482 lab18h720a.hl lab18h720a.hr lab18h720aM3269_endo lab18h720a.htr lab18h720a.hz lab18h720a.hst
    nolab18h720a_Law3482

