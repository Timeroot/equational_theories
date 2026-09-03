import equational_theories.Definability.Shp_shp9h6s2k3
import equational_theories.Definability.Shp_shp9h6s2k3_L3475
import equational_theories.Definability.Shp_shp9h6s2k3_L3482

/-!
# Refutations from the mixed-arity coordinate frames

`AutPattern.lean` chooses the symmetry rather than the model: `Sym(S)` acting diagonally on `S^m`
is a group of automorphisms of every operation invariant under it, and such an operation is
*conservative* -- each output slot copies a value it was handed. That is what refutes targets, and
it is a property of the group, not of the carrier. (The control is instructive: `GL_k(q)` on
`F_q^k` models seventy of the open sources and refutes nothing at all, because a family containing
`a x + b y` contains something for every target.)

The carrier need not be a single power. A disjoint union `S^{m_1} ⊔ ... ⊔ S^{m_r}` is still a
`Sym(S)`-set, and its parts behave differently enough to matter: `S` alone carries one value, `S^2`
carries a pair the operation can hide things in, and the two together have the invariant family of
neither. Nor does `|S|` want to be large. A *smaller* set gives a *larger* invariant family, which
is the wrong trade for refuting a target and the right one for modelling a source, and since a cell
needs both halves the sweet spot is small: `Sym(3)` on `S^2` models fifty-three of the open sources
where `Sym(6)` on the same shape models ten, and it still leaves two targets no room at all.
-/

open Law Law.MagmaLaw

theorem Equation3475_not_definableFrom_Equation667 :
    ¬ Law3475.DefinableFrom Law667 :=
  not_definableFrom_transportKernel (shp9h6s2k3M667 : Magma (Fin 9)) shp9h6s2k3M667_models
    shp9h6s2k3.E shp9h6s2k3.Einv shp9h6s2k3.rep shp9h6s2k3.tr shp9h6s2k3.z shp9h6s2k3.st envshp9h6s2k3_Law3475
    ordshp9h6s2k3_Law3475 shp9h6s2k3.hl shp9h6s2k3.hr shp9h6s2k3M667_endo shp9h6s2k3.htr shp9h6s2k3.hz shp9h6s2k3.hst
    noshp9h6s2k3_Law3475

theorem Equation3482_not_definableFrom_Equation667 :
    ¬ Law3482.DefinableFrom Law667 :=
  not_definableFrom_transportKernel (shp9h6s2k3M667 : Magma (Fin 9)) shp9h6s2k3M667_models
    shp9h6s2k3.E shp9h6s2k3.Einv shp9h6s2k3.rep shp9h6s2k3.tr shp9h6s2k3.z shp9h6s2k3.st envshp9h6s2k3_Law3482
    ordshp9h6s2k3_Law3482 shp9h6s2k3.hl shp9h6s2k3.hr shp9h6s2k3M667_endo shp9h6s2k3.htr shp9h6s2k3.hz shp9h6s2k3.hst
    noshp9h6s2k3_Law3482

theorem Equation3475_not_definableFrom_Equation3279 :
    ¬ Law3475.DefinableFrom Law3279 :=
  not_definableFrom_transportKernel (shp9h6s2k3M3279 : Magma (Fin 9)) shp9h6s2k3M3279_models
    shp9h6s2k3.E shp9h6s2k3.Einv shp9h6s2k3.rep shp9h6s2k3.tr shp9h6s2k3.z shp9h6s2k3.st envshp9h6s2k3_Law3475
    ordshp9h6s2k3_Law3475 shp9h6s2k3.hl shp9h6s2k3.hr shp9h6s2k3M3279_endo shp9h6s2k3.htr shp9h6s2k3.hz shp9h6s2k3.hst
    noshp9h6s2k3_Law3475

theorem Equation3482_not_definableFrom_Equation3279 :
    ¬ Law3482.DefinableFrom Law3279 :=
  not_definableFrom_transportKernel (shp9h6s2k3M3279 : Magma (Fin 9)) shp9h6s2k3M3279_models
    shp9h6s2k3.E shp9h6s2k3.Einv shp9h6s2k3.rep shp9h6s2k3.tr shp9h6s2k3.z shp9h6s2k3.st envshp9h6s2k3_Law3482
    ordshp9h6s2k3_Law3482 shp9h6s2k3.hl shp9h6s2k3.hr shp9h6s2k3M3279_endo shp9h6s2k3.htr shp9h6s2k3.hz shp9h6s2k3.hst
    noshp9h6s2k3_Law3482

