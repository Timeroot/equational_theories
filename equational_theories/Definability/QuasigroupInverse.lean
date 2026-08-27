import equational_theories.Definability.QuasigroupStructural
import equational_theories.Equations.All
import equational_theories.Superposition
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
-- a cell rarely needs all four division axioms, and which ones it needs is Vampire's business
set_option linter.unusedVariables false

/-!
# Division witnesses that are undone, so term-structural

`Definability/QuasigroupCover.lean` places cells on the term-definability board with a witness
written over `◇`, `/` and `\`. This file places them on the term-*structural* one, which is where
the open cells are, by exhibiting the inverse construction as well: a second term over the new
operation and *its* divisions that gives `◇` back.

Both halves rest on the same exponent. `exists_uniform_period` produces one `N` that inverts every
injective self-map of the carrier at once, so the same `N` that spells `◇`'s divisions out inside
the witness spells the witness's divisions out inside the new magma.

Each cell contributes replayed lemmas on the sides its source actually proves bijective -- most of
these laws invert the left translations alone: `inj<s>R`/`inj<s>L` for the source's own
translations, `winj<s>_<i>R`/`winj<s>_<i>L` for the witness's, which is what makes its divisions
exist, `back<s>_<i>` for `◇` itself, and `qaux<s>_<t>_<i>` for the target law.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- On a finite carrier a one-sided inverse is two-sided: this is what turns a source law into its
cyclic rotations. Applied with `f` the outer part of the chain and `g` its first factor, it moves
`g` from the inside of the composite to the outside. -/
private theorem rot_of_finite [Finite G] {f g : G → G} (hfg : ∀ z, f (g z) = z) (x : G) :
    g (f x) = x := by
  have hs : Function.Surjective f := fun z ↦ ⟨g z, hfg z⟩
  exact Finite.injective_iff_surjective.mpr hs (hfg (f x))

/-- Right translation by `t` is injective in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj467R [Finite G] [Magma G] (h : Equation467 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : t = (p ◇ t) ◇ ((p ◇ t) ◇ (q ◇ q)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X1) = X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef8 ef8
  have ef15 : (p ◇ t) ◇ (q ◇ q) = t ◇ (t ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef16 : (p ◇ t) ◇ (q ◇ q) = (p ◇ t) ◇ (p ◇ p) := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef21 : q ◇ q = ((p ◇ t) ◇ (p ◇ p)) ◇ (((p ◇ t) ◇ (p ◇ p)) ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef22 : q ◇ q = p ◇ p := by
    first | exact superpose ef8 ef21 | exact superpose ef21 ef8
  have ef46 : q = (p ◇ p) ◇ ((p ◇ p) ◇ (p ◇ p)) := by
    first | exact superpose ef22 ef8 | exact superpose ef8 ef22
  have ef47 : p = q := by
    first | exact superpose ef8 ef46 | exact superpose ef46 ef8
  subsumption ef47 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj467L [Finite G] [Magma G] (h : Equation467 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : q = (t ◇ p) ◇ ((t ◇ p) ◇ (t ◇ t)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef14 : p = q := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  subsumption ef14 ef10

/-- Right translation of `x □ y := (x/(x◇y))` by `t` is injective in every finite magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj467_16R [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef19 : wf p t = wf q t := mod_symm hhyp
  have ef20 : p ≠ q := mod_symm nh
  have ef22 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef14 ef17 | exact superpose ef17 ef14
  have ef29 (X0 X1 : G) : X0 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef33 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef12 ef17 | exact superpose ef17 ef12
  have ef85 : q ◇ t = dl (wf p t) q := by
    first | exact superpose ef19 ef29 | exact superpose ef29 ef19
  have ef103 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef33 ef17 | exact superpose ef17 ef33
  have ef278 (X0 X1 : G) : dr (dl X0 (dl X1 X0)) (X1 ◇ X1) = X0 := by
    first | exact superpose ef103 ef15 | exact superpose ef15 ef103
  have ef379 (X0 X1 : G) : dr (dl X0 (X0 ◇ X1)) ((wf X0 X1) ◇ (wf X0 X1)) = X0 := by
    first | exact superpose ef29 ef278 | exact superpose ef278 ef29
  have ef380 : q = dr (dl q (q ◇ t)) ((wf p t) ◇ (wf p t)) := by
    first | exact superpose ef85 ef278 | exact superpose ef278 ef85
  have ef391 : q = dr t ((wf p t) ◇ (wf p t)) := by
    first | exact superpose ef17 ef380 | exact superpose ef380 ef17
  have ef392 (X0 X1 : G) : dr X1 ((wf X0 X1) ◇ (wf X0 X1)) = X0 := by
    first | exact superpose ef17 ef379 | exact superpose ef379 ef17
  have ef556 : p = q := by
    first | exact superpose ef392 ef391 | exact superpose ef391 ef392
  subsumption ef556 ef20

/-- Left translation of `x □ y := (x/(x◇y))` by `t` is injective in every finite magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj467_16L [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef19 : wf t p = wf t q := mod_symm hhyp
  have ef20 : p ≠ q := mod_symm nh
  have ef22 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef14 ef17 | exact superpose ef17 ef14
  have ef29 (X0 X1 : G) : X0 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef85 : t ◇ q = dl (wf t p) t := by
    first | exact superpose ef19 ef29 | exact superpose ef29 ef19
  have ef89 : t ◇ q = t ◇ p := by
    first | exact superpose ef29 ef85 | exact superpose ef85 ef29
  have ef115 : q = dl t (t ◇ p) := by
    first | exact superpose ef89 ef17 | exact superpose ef17 ef89
  have ef117 : p = q := by
    first | exact superpose ef17 ef115 | exact superpose ef115 ef17
  subsumption ef117 ef20

/-- The operation comes back: `x ◇ y = (x\(y\y))` read in `□` and its divisions, where
`x □ y := (x/(x◇y))`. With `winj467_16` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back467_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wdl x (wdl y y)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef17 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef20 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef21 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef23 (X0 X1 : G) : wdr (wf X0 X1) X1 = X0 := mod_symm (hwri ..)
  have ef25 (X0 X1 : G) : wdl X0 (wf X0 X1) = X1 := mod_symm (hwli ..)
  have ef26 : wdl x (wdl y y) ≠ x ◇ y := mod_symm nh
  have ef33 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef21 ef17 | exact superpose ef17 ef21
  have ef36 (X0 X1 : G) : dr X0 (X1 ◇ X1) = X1 ◇ ((dr X0 (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef17 ef15 | exact superpose ef15 ef17
  have ef39 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef15 ef18 | exact superpose ef18 ef15
  have ef40 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef21 ef39 | exact superpose ef39 ef21
  have ef48 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef83 (X0 X1 : G) : wf (dr X0 (X1 ◇ X1)) X0 = X1 := by
    first | exact superpose ef17 ef40 | exact superpose ef40 ef17
  have ef86 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = wdl X1 X0 := by
    first | exact superpose ef40 ef25 | exact superpose ef25 ef40
  have ef133 (X0 : G) : wf (X0 ◇ X0) ((X0 ◇ X0) ◇ X0) = dr (X0 ◇ X0) (X0 ◇ X0) := by
    first | exact superpose ef48 ef21 | exact superpose ef21 ef48
  have ef240 (X0 : G) : dr (X0 ◇ X0) (X0 ◇ X0) = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef17 ef36 | exact superpose ef36 ef17
  have ef252 (X0 : G) : dr (X0 ◇ X0) (X0 ◇ X0) = wdl X0 X0 := by
    first | exact superpose ef86 ef240 | exact superpose ef240 ef86
  have ef308 (X0 X1 : G) : wdr X0 X1 = dr X1 (X0 ◇ X0) := by
    first | exact superpose ef83 ef23 | exact superpose ef23 ef83
  have ef344 (X0 X1 : G) : X1 ◇ X1 = dl X0 (wdl X0 X1) := by
    first | exact superpose ef86 ef20 | exact superpose ef20 ef86
  have ef345 (X0 X1 : G) : wf X0 (X1 ◇ X1) = dr X0 (wdl X0 X1) := by
    first | exact superpose ef86 ef21 | exact superpose ef21 ef86
  have ef346 (X0 X1 : G) : (wf X0 (X1 ◇ X1)) ◇ (wdl X0 X1) = X0 := by
    first | exact superpose ef86 ef33 | exact superpose ef33 ef86
  have ef593 (X0 X1 : G) : dr (dl X0 (wdl X0 X1)) X1 = X1 := by
    first | exact superpose ef344 ef18 | exact superpose ef18 ef344
  have ef719 (X0 X1 : G) : wf X1 X0 = dr (dl X1 X0) (wf X1 X0) := by
    first | exact superpose ef25 ef593 | exact superpose ef593 ef25
  have ef786 (X0 : G) : wdl X0 X0 = wdr X0 (X0 ◇ X0) := by
    first | exact superpose ef252 ef308 | exact superpose ef308 ef252
  have ef5677 (X0 : G) :
      dr (X0 ◇ X0) (X0 ◇ X0) = dr (dl (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)) (dr (X0 ◇ X0) (X0 ◇ X0)) := by
    first | exact superpose ef133 ef719 | exact superpose ef719 ef133
  have ef5701 (X0 : G) :
      wdr X0 (X0 ◇ X0) = dr (dl (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)) (wdr X0 (X0 ◇ X0)) := by
    first | exact superpose ef308 ef5677 | exact superpose ef5677 ef308
  have ef5724 (X0 : G) : wdl X0 X0 = dr (dl (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)) (wdl X0 X0) := by
    first | exact superpose ef786 ef5701 | exact superpose ef5701 ef786
  have ef5731 (X0 : G) : wdl X0 X0 = dr X0 (wdl X0 X0) := by
    first | exact superpose ef20 ef5724 | exact superpose ef5724 ef20
  have ef5734 (X0 : G) : wdl X0 X0 = wf X0 (X0 ◇ X0) := by
    first | exact superpose ef345 ef5731 | exact superpose ef5731 ef345
  have ef5992 (X0 : G) : (wdl X0 X0) ◇ (wdl X0 X0) = X0 := by
    first | exact superpose ef5734 ef346 | exact superpose ef346 ef5734
  have ef6084 (X0 X1 : G) : X1 ◇ X0 = wdl X1 (wdl X0 X0) := by
    first | exact superpose ef5992 ef86 | exact superpose ef86 ef5992
  have ef7049 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef6084 ef26 | exact superpose ef26 ef6084
  exact absurd rfl ef7049

/-- Equation 23 `x = (x ◇ x) ◇ x` holds of the operation `x □ y := (x/(x◇y))` in every magma
satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that law
forces. -/
private theorem qaux467_23_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x : G) :
    x = wf (wf x x) x := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : x ≠ wf (wf x x) x := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : x ≠ x := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  exact absurd rfl ef78

theorem Equation23_termStructuralFromFin_Equation467_qdiv :
    Law23.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law23.models_iff]
    exact fun x ↦
      @qaux467_23_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the operation `x □ y := (x/(x◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_1629_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x : G) :
    x = wf (wf x x) (wf (wf x x) x) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : x ≠ wf (wf x x) (wf (wf x x) x) := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : x ≠ wf (wf x x) x := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  subsumption ef78 ef66

theorem Equation1629_termStructuralFromFin_Equation467_qdiv :
    Law1629.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1629.models_iff]
    exact fun x ↦
      @qaux467_1629_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 2441 `x = (x ◇ ((x ◇ x) ◇ x)) ◇ x` holds of the operation `x □ y := (x/(x◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_2441_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x : G) :
    x = wf (wf x (wf (wf x x) x)) x := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : x ≠ wf (wf x (wf (wf x x) x)) x := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : x ≠ wf (wf x x) x := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  subsumption ef78 ef66

theorem Equation2441_termStructuralFromFin_Equation467_qdiv :
    Law2441.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2441.models_iff]
    exact fun x ↦
      @qaux467_2441_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the operation `x □ y := (x/(x◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_3456_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x : G) :
    wf x x = wf x (wf (wf x x) x) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x x ≠ wf x (wf (wf x x) x) := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : wf x x ≠ wf x x := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  exact absurd rfl ef78

theorem Equation3456_termStructuralFromFin_Equation467_qdiv :
    Law3456.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3456.models_iff]
    exact fun x ↦
      @qaux467_3456_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the operation `x □ y := (x/(x◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_3522_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x y : G) :
    wf x y = wf x (wf (wf y y) y) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x y ≠ wf x (wf (wf y y) y) := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : wf x y ≠ wf x y := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  exact absurd rfl ef78

theorem Equation3522_termStructuralFromFin_Equation467_qdiv :
    Law3522.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3522.models_iff]
    exact fun x y ↦
      @qaux467_3522_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 4065 `x ◇ x = ((x ◇ x) ◇ x) ◇ x` holds of the operation `x □ y := (x/(x◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_4065_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x : G) :
    wf x x = wf (wf (wf x x) x) x := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x x ≠ wf (wf (wf x x) x) x := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : wf x x ≠ wf x x := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  exact absurd rfl ef78

theorem Equation4065_termStructuralFromFin_Equation467_qdiv :
    Law4065.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4065.models_iff]
    exact fun x ↦
      @qaux467_4065_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 4118 `x ◇ y = ((x ◇ x) ◇ x) ◇ y` holds of the operation `x □ y := (x/(x◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_4118_16 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (a ◇ b))
    (x y : G) :
    wf x y = wf (wf (wf x x) x) y := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X0 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x y ≠ wf (wf (wf x x) x) y := mod_symm nh
  have ef23 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef29 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef11 ef14 | exact superpose ef14 ef11
  have ef30 (X0 X1 : G) : wf X0 (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef17 ef29 | exact superpose ef29 ef17
  have ef66 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef78 : wf x y ≠ wf x y := by
    first | exact superpose ef66 ef18 | exact superpose ef18 ef66
  exact absurd rfl ef78

theorem Equation4118_termStructuralFromFin_Equation467_qdiv :
    Law4118.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 0) (.var 1))) (.ldv (.var 0) (.ldv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4118.models_iff]
    exact fun x y ↦
      @qaux467_4118_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_16R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_16L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_16 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := (x/(y◇y))` by `t` is injective in every finite magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj467_17R [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef19 : wf p t = wf q t := mod_symm hhyp
  have ef20 : p ≠ q := mod_symm nh
  have ef26 (X0 X1 : G) : (wf X0 X1) ◇ (X1 ◇ X1) = X0 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef35 : q = (wf p t) ◇ (t ◇ t) := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef39 : p = q := by
    first | exact superpose ef26 ef35 | exact superpose ef35 ef26
  subsumption ef39 ef20

/-- Left translation of `x □ y := (x/(y◇y))` by `t` is injective in every finite magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj467_17L [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef19 : wf t p = wf t q := mod_symm hhyp
  have ef20 : p ≠ q := mod_symm nh
  have ef22 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef14 ef17 | exact superpose ef17 ef14
  have ef29 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef33 (X0 X1 : G) : dr X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef69 : q ◇ q = dl (wf t p) t := by
    first | exact superpose ef19 ef29 | exact superpose ef29 ef19
  have ef89 : q ◇ q = p ◇ p := by
    first | exact superpose ef29 ef69 | exact superpose ef69 ef29
  have ef110 (X0 : G) : q = dr X0 (X0 ◇ (X0 ◇ (p ◇ p))) := by
    first | exact superpose ef89 ef33 | exact superpose ef33 ef89
  have ef115 : p = q := by
    first | exact superpose ef33 ef110 | exact superpose ef110 ef33
  subsumption ef115 ef20

/-- The operation comes back: `x ◇ y = (x/(y/y))` read in `□` and its divisions, where
`x □ y := (x/(y◇y))`. With `winj467_17` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back467_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wdr x (wdr y y)) = x ◇ y := by
  by_contra nh
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef20 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef21 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef22 (X0 X1 : G) : wf (wdr X0 X1) X1 = X0 := mod_symm (hwrs ..)
  have ef24 (X0 X1 : G) : wf X0 (wdl X0 X1) = X1 := mod_symm (hwls ..)
  have ef26 : wdr x (wdr y y) ≠ x ◇ y := mod_symm nh
  have ef28 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef32 (X0 X1 : G) : (wf X0 X1) ◇ (X1 ◇ X1) = X0 := by
    first | exact superpose ef21 ef17 | exact superpose ef17 ef21
  have ef36 (X0 X1 : G) : dr X0 (X1 ◇ X1) = X1 ◇ ((dr X0 (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef17 ef15 | exact superpose ef15 ef17
  have ef39 (X0 X1 : G) : wf X0 X1 = X1 ◇ ((wf X0 X1) ◇ X0) := by
    first | exact superpose ef21 ef36 | exact superpose ef36 ef21
  have ef41 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef21 ef28 | exact superpose ef28 ef21
  have ef55 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = wdr X0 X1 := by
    first | exact superpose ef22 ef32 | exact superpose ef32 ef22
  have ef77 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef41 ef20 | exact superpose ef20 ef41
  have ef78 (X0 X1 : G) : dr (dl (wf X0 X1) X0) X1 = X1 := by
    first | exact superpose ef41 ef18 | exact superpose ef18 ef41
  have ef109 (X0 X1 X2 : G) : X2 ◇ (dl (wf X0 X1) X0) = wdr X2 X1 := by
    first | exact superpose ef41 ef55 | exact superpose ef55 ef41
  have ef170 (X0 X1 : G) : (wdl X1 X0) ◇ (X0 ◇ X1) = X0 := by
    first | exact superpose ef24 ef39 | exact superpose ef39 ef24
  have ef315 (X0 X1 : G) : X0 ◇ X1 = dl (wdl X1 X0) X0 := by
    first | exact superpose ef170 ef20 | exact superpose ef20 ef170
  have ef542 (X0 X1 : G) : wdl X1 X0 = dl (wdl X1 X0) (dl X0 X1) := by
    first | exact superpose ef24 ef77 | exact superpose ef77 ef24
  have ef570 (X0 X1 : G) : wdl X1 X0 = dr (dl X0 X1) (wdl X1 X0) := by
    first | exact superpose ef24 ef78 | exact superpose ef78 ef24
  have ef3625 (X0 X1 : G) : wdl (dl (wf X1 X0) X1) X0 = dl (wdl (dl (wf X1 X0) X1) X0) X0 := by
    first | exact superpose ef77 ef542 | exact superpose ef542 ef77
  have ef3669 (X0 X1 : G) : wdl (dl (wf X1 X0) X1) X0 = X0 ◇ (dl (wf X1 X0) X1) := by
    first | exact superpose ef315 ef3625 | exact superpose ef3625 ef315
  have ef3677 (X0 X1 : G) : wdr X0 X0 = wdl (dl (wf X1 X0) X1) X0 := by
    first | exact superpose ef109 ef3669 | exact superpose ef3669 ef109
  have ef3780 (X0 X1 : G) : wdl (dl (wf X1 X0) X1) X0 = dr X0 (wdl (dl (wf X1 X0) X1) X0) := by
    first | exact superpose ef77 ef570 | exact superpose ef570 ef77
  have ef3833 (X0 : G) : wdr X0 X0 = dr X0 (wdr X0 X0) := by
    first | exact superpose ef3677 ef3780 | exact superpose ef3780 ef3677
  have ef3957 (X0 : G) : (wdr X0 X0) ◇ (wdr X0 X0) = X0 := by
    first | exact superpose ef3833 ef17 | exact superpose ef17 ef3833
  have ef4211 (X0 X1 : G) : X1 ◇ X0 = wdr X1 (wdr X0 X0) := by
    first | exact superpose ef3957 ef55 | exact superpose ef55 ef3957
  have ef5521 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef4211 ef26 | exact superpose ef26 ef4211
  exact absurd rfl ef5521

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the operation `x □ y := (x/(y◇y))` in every magma
satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that law
forces. -/
private theorem qaux467_8_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (x : G) :
    x = wf x (wf x x) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : x ≠ wf x (wf x x) := mod_symm nh
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef13 ef16 | exact superpose ef16 ef13
  have ef23 (X0 X1 : G) : wf (X0 ◇ (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef27 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef31 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef56 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef31 ef16 | exact superpose ef16 ef31
  have ef75 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef27 ef16 | exact superpose ef16 ef27
  have ef211 (X0 X1 : G) : wf (dl X0 (dl X1 X0)) X1 = X0 := by
    first | exact superpose ef75 ef23 | exact superpose ef23 ef75
  have ef262 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef56 ef211 | exact superpose ef211 ef56
  have ef313 : x ≠ x := by
    first | exact superpose ef262 ef18 | exact superpose ef18 ef262
  exact absurd rfl ef313

theorem Equation8_termStructuralFromFin_Equation467_qdiv :
    Law8.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 1) (.var 1))) (.rdv (.var 0) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law8.models_iff]
    exact fun x ↦
      @qaux467_8_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_17R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_17L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the operation `x □ y := (x/(y◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_1020_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (x : G) :
    x = wf x (wf (wf x (wf x x)) x) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : x ≠ wf x (wf (wf x (wf x x)) x) := mod_symm nh
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef13 ef16 | exact superpose ef16 ef13
  have ef23 (X0 X1 : G) : wf (X0 ◇ (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef27 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef31 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef56 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef31 ef16 | exact superpose ef16 ef31
  have ef75 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef27 ef16 | exact superpose ef16 ef27
  have ef211 (X0 X1 : G) : wf (dl X0 (dl X1 X0)) X1 = X0 := by
    first | exact superpose ef75 ef23 | exact superpose ef23 ef75
  have ef262 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef56 ef211 | exact superpose ef211 ef56
  have ef313 : x ≠ wf x (wf x x) := by
    first | exact superpose ef262 ef18 | exact superpose ef18 ef262
  subsumption ef313 ef262

theorem Equation1020_termStructuralFromFin_Equation467_qdiv :
    Law1020.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 1) (.var 1))) (.rdv (.var 0) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1020.models_iff]
    exact fun x ↦
      @qaux467_1020_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_17R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_17L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the operation `x □ y := (x/(y◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_3253_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (x : G) :
    wf x x = wf x (wf x (wf x x)) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x x ≠ wf x (wf x (wf x x)) := mod_symm nh
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef13 ef16 | exact superpose ef16 ef13
  have ef23 (X0 X1 : G) : wf (X0 ◇ (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef27 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef31 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef56 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef31 ef16 | exact superpose ef16 ef31
  have ef75 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef27 ef16 | exact superpose ef16 ef27
  have ef211 (X0 X1 : G) : wf (dl X0 (dl X1 X0)) X1 = X0 := by
    first | exact superpose ef75 ef23 | exact superpose ef23 ef75
  have ef262 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef56 ef211 | exact superpose ef211 ef56
  have ef313 : wf x x ≠ wf x x := by
    first | exact superpose ef262 ef18 | exact superpose ef18 ef262
  exact absurd rfl ef313

theorem Equation3253_termStructuralFromFin_Equation467_qdiv :
    Law3253.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 1) (.var 1))) (.rdv (.var 0) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3253.models_iff]
    exact fun x ↦
      @qaux467_3253_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_17R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_17L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the operation `x □ y := (x/(y◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_3319_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (x y : G) :
    wf x y = wf x (wf y (wf y y)) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x y ≠ wf x (wf y (wf y y)) := mod_symm nh
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef13 ef16 | exact superpose ef16 ef13
  have ef23 (X0 X1 : G) : wf (X0 ◇ (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef27 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef31 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef56 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef31 ef16 | exact superpose ef16 ef31
  have ef75 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef27 ef16 | exact superpose ef16 ef27
  have ef211 (X0 X1 : G) : wf (dl X0 (dl X1 X0)) X1 = X0 := by
    first | exact superpose ef75 ef23 | exact superpose ef23 ef75
  have ef262 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef56 ef211 | exact superpose ef211 ef56
  have ef313 : wf x y ≠ wf x y := by
    first | exact superpose ef262 ef18 | exact superpose ef18 ef262
  exact absurd rfl ef313

theorem Equation3319_termStructuralFromFin_Equation467_qdiv :
    Law3319.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 1) (.var 1))) (.rdv (.var 0) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3319.models_iff]
    exact fun x y ↦
      @qaux467_3319_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_17R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_17L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3862 `x ◇ x = (x ◇ (x ◇ x)) ◇ x` holds of the operation `x □ y := (x/(y◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_3862_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (x : G) :
    wf x x = wf (wf x (wf x x)) x := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x x ≠ wf (wf x (wf x x)) x := mod_symm nh
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef13 ef16 | exact superpose ef16 ef13
  have ef23 (X0 X1 : G) : wf (X0 ◇ (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef27 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef31 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef56 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef31 ef16 | exact superpose ef16 ef31
  have ef75 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef27 ef16 | exact superpose ef16 ef27
  have ef211 (X0 X1 : G) : wf (dl X0 (dl X1 X0)) X1 = X0 := by
    first | exact superpose ef75 ef23 | exact superpose ef23 ef75
  have ef262 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef56 ef211 | exact superpose ef211 ef56
  have ef313 : wf x x ≠ wf x x := by
    first | exact superpose ef262 ef18 | exact superpose ef18 ef262
  exact absurd rfl ef313

theorem Equation3862_termStructuralFromFin_Equation467_qdiv :
    Law3862.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 1) (.var 1))) (.rdv (.var 0) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3862.models_iff]
    exact fun x ↦
      @qaux467_3862_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_17R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_17L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3915 `x ◇ y = (x ◇ (x ◇ x)) ◇ y` holds of the operation `x □ y := (x/(y◇y))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_3915_17 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dr a (b ◇ b))
    (x y : G) :
    wf x y = wf (wf x (wf x x)) y := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef14 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dr X0 (X1 ◇ X1) := mod_symm (hwdef ..)
  have ef18 : wf x y ≠ wf (wf x (wf x x)) y := mod_symm nh
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef13 ef16 | exact superpose ef16 ef13
  have ef23 (X0 X1 : G) : wf (X0 ◇ (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef27 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef31 (X0 X1 : G) : X1 ◇ X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef56 (X0 X1 : G) : dl X1 (dl (wf X0 X1) X0) = X1 := by
    first | exact superpose ef31 ef16 | exact superpose ef16 ef31
  have ef75 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef27 ef16 | exact superpose ef16 ef27
  have ef211 (X0 X1 : G) : wf (dl X0 (dl X1 X0)) X1 = X0 := by
    first | exact superpose ef75 ef23 | exact superpose ef23 ef75
  have ef262 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef56 ef211 | exact superpose ef211 ef56
  have ef313 : wf x y ≠ wf x y := by
    first | exact superpose ef262 ef18 | exact superpose ef18 ef262
  exact absurd rfl ef313

theorem Equation3915_termStructuralFromFin_Equation467_qdiv :
    Law3915.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.rdv (.var 0) (.op (.var 1) (.var 1))) (.rdv (.var 0) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3915.models_iff]
    exact fun x y ↦
      @qaux467_3915_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_17R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_17L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_17 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := (x\(y\x))` by `t` is injective in every finite magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj467_39R [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl a (dl b a))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 (X0 X1 : G) : wf X0 X1 = dl X0 (dl X1 X0) := mod_symm (hwdef ..)
  have ef19 : wf p t = wf q t := mod_symm hhyp
  have ef20 : p ≠ q := mod_symm nh
  have ef25 (X0 X1 : G) : wf (X1 ◇ X0) X1 = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef17 ef18 | exact superpose ef18 ef17
  have ef57 (X0 X1 : G) : wf X0 X1 = dl X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef69 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = wf X0 X1 := by
    first | exact superpose ef17 ef57 | exact superpose ef57 ef17
  have ef132 (X0 X1 : G) : dr (wf X0 X1) (X1 ◇ X1) = X0 := by
    first | exact superpose ef69 ef15 | exact superpose ef15 ef69
  have ef374 : q = dr (wf p t) (t ◇ t) := by
    first | exact superpose ef19 ef132 | exact superpose ef132 ef19
  have ef384 : p = q := by
    first | exact superpose ef132 ef374 | exact superpose ef374 ef132
  subsumption ef384 ef20

/-- Left translation of `x □ y := (x\(y\x))` by `t` is injective in every finite magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj467_39L [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl a (dl b a))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : wf X0 X1 = dl X0 (dl X1 X0) := mod_symm (hwdef ..)
  have ef19 : wf t p = wf t q := mod_symm hhyp
  have ef20 : p ≠ q := mod_symm nh
  have ef21 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef28 (X0 X1 : G) : dl X1 X0 = X0 ◇ (wf X0 X1) := by
    first | exact superpose ef18 ef16 | exact superpose ef16 ef18
  have ef35 : dl q t = t ◇ (wf t p) := by
    first | exact superpose ef19 ef28 | exact superpose ef28 ef19
  have ef38 : dl q t = dl p t := by
    first | exact superpose ef28 ef35 | exact superpose ef35 ef28
  have ef50 : q = dr t (dl p t) := by
    first | exact superpose ef38 ef21 | exact superpose ef21 ef38
  have ef52 : p = q := by
    first | exact superpose ef21 ef50 | exact superpose ef50 ef21
  subsumption ef52 ef20

/-- The operation comes back: `x ◇ y = (x◇(y◇y))` read in `□` and its divisions, where
`x □ y := (x\(y\x))`. With `winj467_39` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back467_39 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl a (dl b a))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wf x (wf y y)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef17 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef21 (X0 X1 : G) : wf X0 X1 = dl X0 (dl X1 X0) := mod_symm (hwdef ..)
  have ef26 : wf x (wf y y) ≠ x ◇ y := mod_symm nh
  have ef31 (X0 X1 : G) : wf (X1 ◇ X0) X1 = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef20 ef21 | exact superpose ef21 ef20
  have ef32 (X0 X1 : G) : wf (dl X1 X0) X0 = dl (dl X1 X0) (wf X0 X1) := by
    first | exact superpose ef21 ef21
  have ef37 (X0 X1 : G) : dr X0 (X1 ◇ X1) = X1 ◇ ((dr X0 (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef17 ef15 | exact superpose ef15 ef17
  have ef63 (X0 X1 : G) : wf X0 X1 = dl X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    first | exact superpose ef15 ef31 | exact superpose ef31 ef15
  have ef74 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = wf X0 X1 := by
    first | exact superpose ef20 ef63 | exact superpose ef63 ef20
  have ef144 (X0 X1 : G) : wf (wf X1 X0) (dl X0 X1) = dl (wf X1 X0) (wf (dl X0 X1) X1) := by
    first | exact superpose ef32 ef21 | exact superpose ef21 ef32
  have ef163 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = X0 := by
    first | exact superpose ef74 ef16 | exact superpose ef16 ef74
  have ef171 (X0 X1 : G) : X1 ◇ X1 = dl X0 (wf X0 X1) := by
    first | exact superpose ef74 ef20 | exact superpose ef20 ef74
  have ef369 (X0 : G) : dr (X0 ◇ X0) (X0 ◇ X0) = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef17 ef37 | exact superpose ef37 ef17
  have ef382 (X0 : G) : dr (X0 ◇ X0) (X0 ◇ X0) = wf X0 X0 := by
    first | exact superpose ef74 ef369 | exact superpose ef369 ef74
  have ef610 (X0 : G) : X0 ◇ X0 = (wf X0 X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef382 ef17 | exact superpose ef17 ef382
  have ef611 (X0 : G) : X0 ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef74 ef610 | exact superpose ef610 ef74
  have ef1357 (X0 : G) :
      wf (X0 ◇ X0) (dl X0 (wf X0 X0)) = dl (X0 ◇ X0) (wf (dl X0 (wf X0 X0)) (wf X0 X0)) := by
    first | exact superpose ef611 ef144 | exact superpose ef144 ef611
  have ef1399 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = dl (X0 ◇ X0) (wf (X0 ◇ X0) (wf X0 X0)) := by
    first | exact superpose ef171 ef1357 | exact superpose ef1357 ef171
  have ef1411 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = (wf X0 X0) ◇ (wf X0 X0) := by
    first | exact superpose ef171 ef1399 | exact superpose ef1399 ef171
  have ef1415 (X0 : G) : (wf X0 X0) ◇ (wf X0 X0) = X0 := by
    first | exact superpose ef163 ef1411 | exact superpose ef1411 ef163
  have ef1579 (X0 X1 : G) : X1 ◇ X0 = wf X1 (wf X0 X0) := by
    first | exact superpose ef1415 ef74 | exact superpose ef74 ef1415
  have ef1869 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef1579 ef26 | exact superpose ef26 ef1579
  exact absurd rfl ef1869

/-- Equation 4380 `x ◇ (x ◇ x) = (x ◇ x) ◇ x` holds of the operation `x □ y := (x\(y\x))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with the divisions that
law forces. -/
private theorem qaux467_4380_39 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl a (dl b a))
    (x : G) :
    wf x (wf x x) = wf (wf x x) x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = dl X0 (dl X1 X0) := mod_symm (hwdef ..)
  have ef18 : wf x (wf x x) ≠ wf (wf x x) x := mod_symm nh
  have ef21 (X0 X1 : G) : wf (X1 ◇ X0) X1 = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef16 ef17 | exact superpose ef17 ef16
  have ef22 (X0 X1 : G) : wf (dl X1 X0) X0 = dl (dl X1 X0) (wf X0 X1) := by
    first | exact superpose ef17 ef17
  have ef27 (X0 X1 : G) : dr X0 (X1 ◇ X1) = X1 ◇ ((dr X0 (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef47 (X0 X1 : G) : wf X0 X1 = dl X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    first | exact superpose ef11 ef21 | exact superpose ef21 ef11
  have ef56 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = wf X0 X1 := by
    first | exact superpose ef16 ef47 | exact superpose ef47 ef16
  have ef112 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = X0 := by
    first | exact superpose ef56 ef12 | exact superpose ef12 ef56
  have ef117 (X0 X1 : G) : wf (dr X0 (X1 ◇ X1)) X1 = X0 := by
    first | exact superpose ef56 ef13 | exact superpose ef13 ef56
  have ef120 (X0 X1 : G) : X1 ◇ X1 = dl X0 (wf X0 X1) := by
    first | exact superpose ef56 ef16 | exact superpose ef16 ef56
  have ef139 (X0 X1 : G) : wf (wf X1 X0) (dl X0 X1) = dl (wf X1 X0) (wf (dl X0 X1) X1) := by
    first | exact superpose ef22 ef17 | exact superpose ef17 ef22
  have ef347 (X0 : G) : dr (X0 ◇ X0) (X0 ◇ X0) = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef13 ef27 | exact superpose ef27 ef13
  have ef359 (X0 : G) : dr (X0 ◇ X0) (X0 ◇ X0) = wf X0 X0 := by
    first | exact superpose ef56 ef347 | exact superpose ef347 ef56
  have ef434 (X0 : G) : X0 ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef359 ef117 | exact superpose ef117 ef359
  have ef481 : wf x (wf x x) ≠ x ◇ x := by
    first | exact superpose ef434 ef18 | exact superpose ef18 ef434
  have ef1068 (X0 : G) :
      wf (X0 ◇ X0) (dl X0 (wf X0 X0)) = dl (X0 ◇ X0) (wf (dl X0 (wf X0 X0)) (wf X0 X0)) := by
    first | exact superpose ef434 ef139 | exact superpose ef139 ef434
  have ef1099 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = dl (X0 ◇ X0) (wf (X0 ◇ X0) (wf X0 X0)) := by
    first | exact superpose ef120 ef1068 | exact superpose ef1068 ef120
  have ef1109 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = (wf X0 X0) ◇ (wf X0 X0) := by
    first | exact superpose ef120 ef1099 | exact superpose ef1099 ef120
  have ef1111 (X0 : G) : (wf X0 X0) ◇ (wf X0 X0) = X0 := by
    first | exact superpose ef112 ef1109 | exact superpose ef1109 ef112
  have ef1122 (X0 X1 : G) : X1 ◇ X0 = wf X1 (wf X0 X0) := by
    first | exact superpose ef1111 ef56 | exact superpose ef56 ef1111
  have ef1203 : x ◇ x ≠ x ◇ x := by
    first | exact superpose ef1122 ef481 | exact superpose ef481 ef1122
  exact absurd rfl ef1203

theorem Equation4380_termStructuralFromFin_Equation467_qdiv :
    Law4380.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_qterm (.ldv (.var 0) (.ldv (.var 1) (.var 0))) (.op (.var 0) (.op (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4380.models_iff]
    exact fun x ↦
      @qaux467_4380_39 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj467_39R G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj467_39L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back467_39 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 873
`x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj873R [Finite G] [Magma G] (h : Equation873 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef14 : t = ((p ◇ t) ◇ (p ◇ t)) ◇ (q ◇ q) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef15 (X0 X1 : G) :
      X1 ◇ X1 = (X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef10 ef10
  have ef17 : q ◇ q = (t ◇ t) ◇ (((p ◇ t) ◇ (p ◇ t)) ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef18 : q ◇ q = p ◇ p := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef31 : q = ((p ◇ p) ◇ (p ◇ p)) ◇ (p ◇ p) := by
    first | exact superpose ef18 ef10 | exact superpose ef10 ef18
  have ef32 : p = q := by
    first | exact superpose ef10 ef31 | exact superpose ef31 ef10
  subsumption ef32 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 873
`x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj873L [Finite G] [Magma G] (h : Equation873 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef14 : q = ((t ◇ p) ◇ (t ◇ p)) ◇ (t ◇ t) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef16 : p = q := by
    first | exact superpose ef10 ef14 | exact superpose ef14 ef10
  subsumption ef16 ef12

/-- Right translation of `x □ y := ((x◇x)\y)` by `t` is injective in every finite magma satisfying
equation 873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj873_4R [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (a ◇ a) b)
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef15 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = dl (X0 ◇ X0) X1 := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef23 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef18 ef17 | exact superpose ef17 ef18
  have ef28 (X0 X1 : G) : X0 ◇ X0 = dr X1 (wf X0 X1) := by
    first | exact superpose ef20 ef23 | exact superpose ef23 ef20
  have ef146 : q ◇ q = dr t (wf p t) := by
    first | exact superpose ef21 ef28 | exact superpose ef28 ef21
  have ef181 : q ◇ q = p ◇ p := by
    first | exact superpose ef28 ef146 | exact superpose ef146 ef28
  have ef222 : q = ((p ◇ p) ◇ (p ◇ p)) ◇ (p ◇ p) := by
    first | exact superpose ef181 ef15 | exact superpose ef15 ef181
  have ef225 : p = q := by
    first | exact superpose ef15 ef222 | exact superpose ef222 ef15
  subsumption ef225 ef22

/-- Left translation of `x □ y := ((x◇x)\y)` by `t` is injective in every finite magma satisfying
equation 873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj873_4L [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (a ◇ a) b)
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = dl (X0 ◇ X0) X1 := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef29 (X0 X1 : G) : (X0 ◇ X0) ◇ (wf X0 X1) = X1 := by
    first | exact superpose ef20 ef18 | exact superpose ef18 ef20
  have ef36 : q = (t ◇ t) ◇ (wf t p) := by
    first | exact superpose ef21 ef29 | exact superpose ef29 ef21
  have ef39 : p = q := by
    first | exact superpose ef29 ef36 | exact superpose ef36 ef29
  subsumption ef39 ef22

/-- The operation comes back: `x ◇ y = ((x\x)\y)` read in `□` and its divisions, where
`x □ y := ((x◇x)\y)`. With `winj873_4` that makes the witness term-structural rather than merely
term-definable. -/
private theorem back873_4 [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (a ◇ a) b)
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wdl (wdl x x) y) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef16 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 : G) :
      (X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = dl (X0 ◇ X0) X1 := mod_symm (hwdef ..)
  have ef26 (X0 X1 : G) : wf X0 (wdl X0 X1) = X1 := mod_symm (hwls ..)
  have ef28 : wdl (wdl x x) y ≠ x ◇ y := mod_symm nh
  have ef34 (X0 X1 : G) : (X0 ◇ X0) ◇ (wf X0 X1) = X1 := by
    first | exact superpose ef23 ef21 | exact superpose ef21 ef23
  have ef59 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ X0) = X2 := by
    first | exact superpose ef17 ef16 | exact superpose ef16 ef17
  have ef62 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef17 ef18 | exact superpose ef18 ef17
  have ef74 (X0 X1 : G) : wdl X1 X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef26 ef34 | exact superpose ef34 ef26
  have ef749 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0) = X2 := by
    first | exact superpose ef62 ef59 | exact superpose ef59 ef62
  have ef808 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) ◇ (wdl X2 X0) = X2 := by
    first | exact superpose ef74 ef749 | exact superpose ef749 ef74
  have ef840 (X0 X2 : G) : (wdl X0 X0) ◇ (wdl X2 X0) = X2 := by
    first | exact superpose ef74 ef808 | exact superpose ef808 ef74
  have ef1469 (X0 X1 : G) : X0 ◇ X1 = wdl (wdl X0 X0) X1 := by
    first | exact superpose ef840 ef74 | exact superpose ef74 ef840
  have ef3369 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef1469 ef28 | exact superpose ef28 ef1469
  exact absurd rfl ef3369

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the operation `x □ y := ((x◇x)\y)` in every
magma satisfying equation 873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))` and equipped with the divisions that
law forces. -/
private theorem qaux873_4273_4 [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (a ◇ a) b)
    (x y : G) :
    wf x (wf x x) = wf y (wf x y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef12 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = dl (X0 ◇ X0) X1 := mod_symm (hwdef ..)
  have ef20 : wf x (wf x x) ≠ wf y (wf x y) := mod_symm nh
  have ef24 (X0 X1 : G) : (X0 ◇ X0) ◇ (wf X0 X1) = X1 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef30 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef37 (X0 X1 : G) : X1 ◇ X1 = dl ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef39 (X0 X1 : G) : X1 ◇ X1 = wf (X1 ◇ X0) X0 := by
    first | exact superpose ef19 ef37 | exact superpose ef37 ef19
  have ef78 (X0 X1 : G) : (X1 ◇ X1) ◇ (X1 ◇ X1) = wf X0 (wf X1 X0) := by
    first | exact superpose ef24 ef39 | exact superpose ef39 ef24
  have ef98 (X0 X1 : G) : wf X0 (wf X1 X0) = dl X1 X1 := by
    first | exact superpose ef30 ef78 | exact superpose ef78 ef30
  have ef400 : wf x (wf x x) ≠ dl x x := by
    first | exact superpose ef98 ef20 | exact superpose ef20 ef98
  subsumption ef400 ef98

theorem Equation4273_termStructuralFromFin_Equation873_qdiv :
    Law4273.TermStructuralFromFin Law873 := by
  refine termStructuralFromFin_of_qterm (.ldv (.op (.var 0) (.var 0)) (.var 1)) (.ldv (.ldv (.var 0) (.var 0)) (.var 1)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj873R G _ M (Law873.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj873L G _ M (Law873.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @qaux873_4273_4 G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj873_4R G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj873_4L G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back873_4 G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := ((y◇y)\x)` by `t` is injective in every finite magma satisfying
equation 873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj873_5R [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (b ◇ b) a)
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X1) X0 := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef29 (X0 X1 : G) : (X1 ◇ X1) ◇ (wf X0 X1) = X0 := by
    first | exact superpose ef20 ef18 | exact superpose ef18 ef20
  have ef36 : q = (t ◇ t) ◇ (wf p t) := by
    first | exact superpose ef21 ef29 | exact superpose ef29 ef21
  have ef39 : p = q := by
    first | exact superpose ef29 ef36 | exact superpose ef36 ef29
  subsumption ef39 ef22

/-- Left translation of `x □ y := ((y◇y)\x)` by `t` is injective in every finite magma satisfying
equation 873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. That is what makes `□`'s own divisions terms, and so
what lets `◇` be sought inside `□`. -/
private theorem winj873_5L [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (b ◇ b) a)
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef15 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X1) X0 := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef23 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef18 ef17 | exact superpose ef17 ef18
  have ef28 (X0 X1 : G) : X1 ◇ X1 = dr X0 (wf X0 X1) := by
    first | exact superpose ef20 ef23 | exact superpose ef23 ef20
  have ef146 : q ◇ q = dr t (wf t p) := by
    first | exact superpose ef21 ef28 | exact superpose ef28 ef21
  have ef181 : q ◇ q = p ◇ p := by
    first | exact superpose ef28 ef146 | exact superpose ef146 ef28
  have ef222 : q = ((p ◇ p) ◇ (p ◇ p)) ◇ (p ◇ p) := by
    first | exact superpose ef181 ef15 | exact superpose ef15 ef181
  have ef225 : p = q := by
    first | exact superpose ef15 ef222 | exact superpose ef222 ef15
  subsumption ef225 ef22

/-- The operation comes back: `x ◇ y = (y/(x/x))` read in `□` and its divisions, where
`x □ y := ((y◇y)\x)`. With `winj873_5` that makes the witness term-structural rather than merely
term-definable. -/
private theorem back873_5 [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (b ◇ b) a)
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wdr y (wdr x x)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef16 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 : G) :
      (X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X1) X0 := mod_symm (hwdef ..)
  have ef24 (X0 X1 : G) : wf (wdr X0 X1) X1 = X0 := mod_symm (hwrs ..)
  have ef28 : wdr y (wdr x x) ≠ x ◇ y := mod_symm nh
  have ef34 (X0 X1 : G) : (X1 ◇ X1) ◇ (wf X0 X1) = X0 := by
    first | exact superpose ef23 ef21 | exact superpose ef21 ef23
  have ef59 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ X0) = X2 := by
    first | exact superpose ef17 ef16 | exact superpose ef16 ef17
  have ef62 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef17 ef18 | exact superpose ef18 ef17
  have ef73 (X0 X1 : G) : wdr X0 X1 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef24 ef34 | exact superpose ef34 ef24
  have ef722 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0) = X2 := by
    first | exact superpose ef62 ef59 | exact superpose ef59 ef62
  have ef785 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) ◇ (wdr X0 X2) = X2 := by
    first | exact superpose ef73 ef722 | exact superpose ef722 ef73
  have ef823 (X0 X2 : G) : (wdr X0 X0) ◇ (wdr X0 X2) = X2 := by
    first | exact superpose ef73 ef785 | exact superpose ef785 ef73
  have ef1488 (X0 X1 : G) : X0 ◇ X1 = wdr X1 (wdr X0 X0) := by
    first | exact superpose ef823 ef73 | exact superpose ef73 ef823
  have ef3296 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef1488 ef28 | exact superpose ef28 ef1488
  exact absurd rfl ef3296

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the operation `x □ y := ((y◇y)\x)` in every
magma satisfying equation 873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))` and equipped with the divisions that
law forces. -/
private theorem qaux873_4588_5 [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = dl (b ◇ b) a)
    (x y : G) :
    wf (wf x x) x = wf (wf y x) y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef12 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X1) X0 := mod_symm (hwdef ..)
  have ef20 : wf (wf x x) x ≠ wf (wf y x) y := mod_symm nh
  have ef24 (X0 X1 : G) : (X1 ◇ X1) ◇ (wf X0 X1) = X0 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef30 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef37 (X0 X1 : G) : X1 ◇ X1 = dl ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef39 (X0 X1 : G) : X1 ◇ X1 = wf X0 (X1 ◇ X0) := by
    first | exact superpose ef19 ef37 | exact superpose ef37 ef19
  have ef78 (X0 X1 : G) : (X1 ◇ X1) ◇ (X1 ◇ X1) = wf (wf X0 X1) X0 := by
    first | exact superpose ef24 ef39 | exact superpose ef39 ef24
  have ef98 (X0 X1 : G) : wf (wf X0 X1) X0 = dl X1 X1 := by
    first | exact superpose ef30 ef78 | exact superpose ef78 ef30
  have ef397 : wf (wf x x) x ≠ dl x x := by
    first | exact superpose ef98 ef20 | exact superpose ef20 ef98
  subsumption ef397 ef98

theorem Equation4588_termStructuralFromFin_Equation873_qdiv :
    Law4588.TermStructuralFromFin Law873 := by
  refine termStructuralFromFin_of_qterm (.ldv (.op (.var 1) (.var 1)) (.var 0)) (.rdv (.var 1) (.rdv (.var 0) (.var 0))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj873R G _ M (Law873.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj873L G _ M (Law873.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @qaux873_4588_5 G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj873_5R G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj873_5L G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back873_5 G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj898R [Finite G] [Magma G] (h : Equation898 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 (X0 : G) : q = X0 ◇ ((p ◇ t) ◇ (t ◇ X0)) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef18 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef18 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj898L [Finite G] [Magma G] (h : Equation898 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef25 (X0 : G) : q = ((t ◇ p) ◇ X0) ◇ (X0 ◇ t) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef38 : p = q := by
    first | exact superpose ef10 ef25 | exact superpose ef25 ef10
  subsumption ef38 ef12

/-- Right translation of `x □ y := (x◇(y◇(x/x)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_0R [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (b ◇ (dr a a)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X0 ◇ (X1 ◇ (dr X0 X0)) := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef28 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef30 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef31 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef34 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef41 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef44 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef63 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef66 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef69 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef15 ef15
  have ef71 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef74 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef87 (X0 X1 : G) : ((dr X0 X0) ◇ (wf X0 X1)) ◇ X1 = X0 := by
    first | exact superpose ef20 ef14 | exact superpose ef14 ef20
  have ef95 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((X2 ◇ (dr (X0 ◇ X1) (X0 ◇ X1))) ◇ X0) = X1 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef96 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = X1 := by
    first | exact superpose ef44 ef95 | exact superpose ef95 ef44
  have ef103 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef104 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef18 ef27 | exact superpose ef27 ef18
  have ef107 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef27 ef27
  have ef108 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef14 ef27 | exact superpose ef27 ef14
  have ef109 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef15 ef27 | exact superpose ef27 ef15
  have ef127 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef27 ef19 | exact superpose ef19 ef27
  have ef134 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef44 ef109 | exact superpose ef109 ef44
  have ef135 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef44 ef108 | exact superpose ef108 ef44
  have ef153 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef161 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef28 ef19 | exact superpose ef19 ef28
  have ef162 (X0 X1 X2 X3 : G) : dr X3 X2 = (X1 ◇ ((dl X0 X1) ◇ X2)) ◇ (X3 ◇ X0) := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef198 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef30 ef19 | exact superpose ef19 ef30
  have ef230 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef14 ef31 | exact superpose ef31 ef14
  have ef246 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef31 ef19 | exact superpose ef19 ef31
  have ef247 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef31 ef27 | exact superpose ef27 ef31
  have ef282 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef283 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef34 ef34
  have ef285 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef294 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) X2 = (X2 ◇ (X1 ◇ X3)) ◇ (dl X0 X1) := by
    first | exact superpose ef34 ef34
  have ef296 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef307 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef314 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef34 ef15 | exact superpose ef15 ef34
  have ef327 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef247 ef314 | exact superpose ef314 ef247
  have ef434 (X0 X1 : G) : (wf X0 X1) ◇ (dr (dr X0 X0) X0) = X1 := by
    first | exact superpose ef20 ef40 | exact superpose ef40 ef20
  have ef445 (X0 X1 : G) : X1 ◇ X0 = wf X1 (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef40 ef20 | exact superpose ef20 ef40
  have ef453 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef40 ef27 | exact superpose ef27 ef40
  have ef455 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef40 ef34 | exact superpose ef34 ef40
  have ef465 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef44 ef453 | exact superpose ef453 ef44
  have ef523 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((dl X1 X3) ◇ (X0 ◇ X3)) := by
    first | exact superpose ef41 ef27 | exact superpose ef27 ef41
  have ef530 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef41 ef31 | exact superpose ef31 ef41
  have ef553 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ X3) ◇ X2) ◇ (dl X1 X3) := by
    first | exact superpose ef44 ef523 | exact superpose ef523 ef44
  have ef598 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef15 ef44 | exact superpose ef44 ef15
  have ef613 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef247 ef598 | exact superpose ef598 ef247
  have ef637 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef63 ef40 | exact superpose ef40 ef63
  have ef820 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef27 ef66 | exact superpose ef66 ef27
  have ef914 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef40 ef74 | exact superpose ef74 ef40
  have ef916 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef74 | exact superpose ef74 ef31
  have ef946 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef282 ef916 | exact superpose ef916 ef282
  have ef947 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef127 ef914 | exact superpose ef914 ef127
  have ef960 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef34 ef946 | exact superpose ef946 ef34
  have ef970 : q = ((dr q q) ◇ (wf p t)) ◇ t := by
    first | exact superpose ef21 ef87 | exact superpose ef87 ef21
  have ef992 (X0 X1 : G) : dr X0 X0 = (dl (wf X0 X1) X1) ◇ X0 := by
    first | exact superpose ef87 ef31 | exact superpose ef31 ef87
  have ef994 (X0 X1 X2 : G) : X0 ◇ (dr X2 ((dr X0 X0) ◇ (wf X0 (X1 ◇ X2)))) = X1 := by
    first | exact superpose ef87 ef40 | exact superpose ef40 ef87
  have ef1004 (X0 X1 X2 : G) : X0 ◇ (((wf X0 (X1 ◇ X2)) ◇ X2) ◇ (dr X0 X0)) = X1 := by
    first | exact superpose ef44 ef994 | exact superpose ef994 ef44
  have ef1023 : q = q ◇ (q ◇ (dl (wf p t) t)) := by
    first | exact superpose ef820 ef970 | exact superpose ef970 ef820
  have ef1026 (X0 X1 X2 : G) : wf X0 ((wf X0 (X1 ◇ X2)) ◇ X2) = X1 := by
    first | exact superpose ef20 ef1004 | exact superpose ef1004 ef20
  have ef1112 (X0 X1 X2 X3 : G) :
      (((X2 ◇ X0) ◇ X3) ◇ ((wf X0 X1) ◇ X2)) ◇ (X1 ◇ (dr X0 X0)) = X3 := by
    first | exact superpose ef20 ef69 | exact superpose ef69 ef20
  have ef1233 (X0 X1 X2 X3 : G) :
      (dr X3 (X1 ◇ (dr X0 X0))) ◇ (((wf X0 X1) ◇ X2) ◇ (X2 ◇ X0)) = X3 := by
    first | exact superpose ef465 ef1112 | exact superpose ef1112 ef465
  have ef1316 (X0 X1 X2 X3 : G) :
      X0 ◇ (((wf X0 X1) ◇ X2) ◇ (X2 ◇ (dr X3 (X1 ◇ (dr X0 X0))))) = X3 := by
    first | exact superpose ef947 ef1233 | exact superpose ef1233 ef947
  have ef1371 (X0 X1 X3 : G) : X0 ◇ (dl (dr X3 (X1 ◇ (dr X0 X0))) (wf X0 X1)) = X3 := by
    first | exact superpose ef34 ef1316 | exact superpose ef1316 ef34
  have ef1412 (X0 X1 X3 : G) : X0 ◇ (dl (((dr X0 X0) ◇ X3) ◇ X1) (wf X0 X1)) = X3 := by
    first | exact superpose ef44 ef1371 | exact superpose ef1371 ef44
  have ef1437 (X0 X1 X3 : G) : X0 ◇ (((wf X0 X1) ◇ (dl X3 X1)) ◇ (dr X0 X0)) = X3 := by
    first | exact superpose ef296 ef1412 | exact superpose ef1412 ef296
  have ef1444 (X0 X1 X3 : G) : wf X0 ((wf X0 X1) ◇ (dl X3 X1)) = X3 := by
    first | exact superpose ef20 ef1437 | exact superpose ef1437 ef20
  have ef1465 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef15 ef104 | exact superpose ef104 ef15
  have ef1466 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef34 ef104 | exact superpose ef104 ef34
  have ef1467 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef40 ef104 | exact superpose ef104 ef40
  have ef1468 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef16 ef104 | exact superpose ef104 ef16
  have ef1535 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef127 ef1467 | exact superpose ef1467 ef127
  have ef1536 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef960 ef1466 | exact superpose ef1466 ef960
  have ef1565 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef246 ef1536 | exact superpose ef1536 ef246
  have ef1575 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef27 ef1565 | exact superpose ef1565 ef27
  have ef1688 (X0 X1 X2 X3 X4 : G) :
      (dl X1 ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3)) ◇ X0 = dr (X4 ◇ X2) X1 := by
    first | exact superpose ef71 ef104 | exact superpose ef104 ef71
  have ef1699 (X0 X1 X2 X3 X4 : G) :
      dr (X4 ◇ X2) X1 = (((X2 ◇ X3) ◇ X4) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X0 := by
    first | exact superpose ef282 ef1688 | exact superpose ef1688 ef282
  have ef1791 (X0 X1 X2 X3 X4 : G) :
      dr (X4 ◇ X2) X1 = (dr X4 X0) ◇ (((X3 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) := by
    first | exact superpose ef465 ef1699 | exact superpose ef1699 ef465
  have ef1855 (X0 X1 X2 X4 : G) : dr (X4 ◇ X2) X1 = (dr X4 X0) ◇ (dr X2 (dl X0 X1)) := by
    first | exact superpose ef247 ef1791 | exact superpose ef1791 ef247
  have ef3198 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef27 ef153 | exact superpose ef153 ef27
  have ef3214 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef153 ef27 | exact superpose ef27 ef153
  have ef3296 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef44 ef3214 | exact superpose ef3214 ef44
  have ef3307 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1575 ef3198 | exact superpose ef3198 ef1575
  have ef3341 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef44 ef3307 | exact superpose ef3307 ef44
  have ef3359 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef104 ef3341 | exact superpose ef3341 ef104
  have ef3622 (X0 X1 : G) : wf X0 (dl X1 X0) = dl (dr X0 X0) X1 := by
    first | exact superpose ef161 ef20 | exact superpose ef20 ef161
  have ef3631 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef161 ef19 | exact superpose ef19 ef161
  have ef4663 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef198 ef14 | exact superpose ef14 ef198
  have ef4868 (X0 X1 X2 X3 : G) : (dl X0 X2) ◇ ((X1 ◇ X0) ◇ (dr (X2 ◇ X3) X1)) = X3 := by
    first | exact superpose ef65 ef230 | exact superpose ef230 ef65
  have ef4976 (X1 X2 X3 : G) : dl (dr (X2 ◇ X3) X1) (X2 ◇ X1) = X3 := by
    first | exact superpose ef283 ef4868 | exact superpose ef4868 ef283
  have ef5487 (X0 X1 : G) : dr (dr X0 X0) X0 = dl (wf X0 X1) X1 := by
    first | exact superpose ef20 ef307 | exact superpose ef307 ef20
  have ef5498 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef153 ef307 | exact superpose ef307 ef153
  have ef5549 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef44 ef5498 | exact superpose ef5498 ef44
  have ef5559 (X0 X1 : G) : dl (wf X0 X1) X1 = (dl X0 X0) ◇ X0 := by
    first | exact superpose ef1468 ef5487 | exact superpose ef5487 ef1468
  have ef5604 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef637 ef5549 | exact superpose ef5549 ef637
  have ef5633 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef34 ef5604 | exact superpose ef5604 ef34
  have ef5840 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef327 ef74 | exact superpose ef74 ef327
  have ef5858 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3631 ef5840 | exact superpose ef5840 ef3631
  have ef6242 (X0 X1 : G) : X0 ◇ (dl X1 X0) = wf X0 (dl X0 X1) := by
    first | exact superpose ef161 ef445 | exact superpose ef445 ef161
  have ef6406 (X0 X1 X2 X3 : G) : dl X1 X2 = (dl X0 X1) ◇ ((X3 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef65 ef530 | exact superpose ef530 ef65
  have ef6572 (X1 X2 X3 : G) : dl X1 X2 = dl (dr X2 X3) (X1 ◇ X3) := by
    first | exact superpose ef283 ef6406 | exact superpose ef6406 ef283
  have ef6733 (X0 X1 X2 : G) : dr X1 (dr (dr X2 X2) X2) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef434 ef613 | exact superpose ef613 ef434
  have ef6774 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ (dr X2 X2)) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef103 ef6733 | exact superpose ef6733 ef103
  have ef6816 (X0 X1 X2 : G) : wf X2 X1 = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef20 ef6774 | exact superpose ef6774 ef20
  have ef8896 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (dr X0 X0)) = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef992 ef27 | exact superpose ef27 ef992
  have ef9003 (X0 X1 X2 : G) : wf X0 X1 = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef20 ef8896 | exact superpose ef8896 ef20
  have ef9181 : dl (wf p t) t = (dl q q) ◇ q := by
    first | exact superpose ef1023 ef230 | exact superpose ef230 ef1023
  have ef9268 : (dl q q) ◇ q = (dl p p) ◇ p := by
    first | exact superpose ef5559 ef9181 | exact superpose ef9181 ef5559
  have ef12016 (X0 : G) : dr X0 (dl (wf p t) t) = q ◇ (X0 ◇ (dr q q)) := by
    first | exact superpose ef1023 ef107 | exact superpose ef107 ef1023
  have ef12224 (X0 : G) : wf q X0 = dr X0 (dl (wf p t) t) := by
    first | exact superpose ef20 ef12016 | exact superpose ef12016 ef20
  have ef12386 (X0 : G) : wf q X0 = wf p X0 := by
    first | exact superpose ef9003 ef12224 | exact superpose ef12224 ef9003
  have ef18460 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = dr ((X0 ◇ X2) ◇ X4) (X1 ◇ X3) := by
    first | exact superpose ef134 ef1575 | exact superpose ef1575 ef134
  have ef18497 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = (dl (X1 ◇ X3) (X4 ◇ X0)) ◇ X2 := by
    first | exact superpose ef1465 ef18460 | exact superpose ef18460 ef1465
  have ef18885 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) := by
    first | exact superpose ef5858 ef18497 | exact superpose ef18497 ef5858
  have ef19153 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X2 := by
    first | exact superpose ef1535 ef18885 | exact superpose ef18885 ef1535
  have ef21399 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ ((dl X4 X3) ◇ X1))) = ((dr X0 X1) ◇ X2) ◇ X4 := by
    first | exact superpose ef162 ef135 | exact superpose ef135 ef162
  have ef21565 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ ((dl X4 X3) ◇ X1))) = X0 ◇ (X1 ◇ (dl X2 X4)) := by
    first | exact superpose ef820 ef21399 | exact superpose ef21399 ef820
  have ef21769 (X0 X1 X2 X4 : G) : X0 ◇ (X2 ◇ (dl X1 X4)) = X0 ◇ (X1 ◇ (dl X2 X4)) := by
    first | exact superpose ef161 ef21565 | exact superpose ef21565 ef161
  have ef43655 (X0 : G) : q ◇ (dl X0 q) = wf p (dl q X0) := by
    first | exact superpose ef6242 ef12386 | exact superpose ef12386 ef6242
  have ef44682 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = dl ((X2 ◇ (X0 ◇ X3)) ◇ X1) X4 := by
    first | exact superpose ef135 ef6572 | exact superpose ef6572 ef135
  have ef44867 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (dl (X0 ◇ X3) X1)) ◇ X2 := by
    first | exact superpose ef296 ef44682 | exact superpose ef44682 ef296
  have ef44963 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = X1 ◇ (dr (X2 ◇ X4) (X0 ◇ X3)) := by
    first | exact superpose ef4663 ef44867 | exact superpose ef44867 ef4663
  have ef45037 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = X1 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X0) := by
    first | exact superpose ef44 ef44963 | exact superpose ef44963 ef44
  have ef45082 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((dr X2 X0) ◇ (dr X4 X3)) = X1 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X0) := by
    first | exact superpose ef455 ef45037 | exact superpose ef45037 ef455
  have ef47100 (X0 X1 X2 X3 X4 : G) :
      dl (X1 ◇ (dr (X2 ◇ X0) X3)) X4 = (X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0 := by
    first | exact superpose ef4976 ef294 | exact superpose ef294 ef4976
  have ef47365 (X0 X1 X2 X3 X4 : G) :
      dl (X1 ◇ (dr (X2 ◇ X0) X3)) X4 = X2 ◇ (dr (X3 ◇ X4) (dl X0 X1)) := by
    first | exact superpose ef19153 ef47100 | exact superpose ef47100 ef19153
  have ef47638 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr (X3 ◇ X4) (dl X0 X1)) = (dr (X2 ◇ X0) X3) ◇ (dr X1 X4) := by
    first | exact superpose ef637 ef47365 | exact superpose ef47365 ef637
  have ef48401 (X0 X1 X2 X3 : G) : (wf X0 X1) ◇ X3 = (dr X2 X3) ◇ (dl (wf X0 X2) X1) := by
    first | exact superpose ef6816 ef3359 | exact superpose ef3359 ef6816
  have ef65791 (X0 X1 X2 X3 X4 : G) :
      (wf X0 X1) ◇ (X3 ◇ X4) = ((X4 ◇ X2) ◇ X3) ◇ (dl (wf X0 X2) X1) := by
    first | exact superpose ef6816 ef465 | exact superpose ef465 ef6816
  have ef69380 (X0 X1 X2 X3 X4 : G) :
      ((dr X0 X1) ◇ X3) ◇ (dl X2 X4) = X2 ◇ (X3 ◇ ((dl X4 X1) ◇ X0)) := by
    first | exact superpose ef153 ef553 | exact superpose ef553 ef153
  have ef69996 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X1 ◇ (dl X3 (dl X2 X4))) = X2 ◇ (X3 ◇ ((dl X4 X1) ◇ X0)) := by
    first | exact superpose ef820 ef69380 | exact superpose ef69380 ef820
  have ef70227 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X1 ◇ ((dl X4 X3) ◇ X2)) = X2 ◇ (X3 ◇ ((dl X4 X1) ◇ X0)) := by
    first | exact superpose ef3631 ef69996 | exact superpose ef69996 ef3631
  have ef70828 (X0 : G) :
      q = (wf ((dl p p) ◇ p) X0) ◇ ((X0 ◇ ((q ◇ ((dl p p) ◇ p)) ◇ (dl q q))) ◇ (dl q q)) := by
    first | exact superpose ef9268 ef96 | exact superpose ef96 ef9268
  have ef70972 (X0 : G) :
      q = (wf ((dl p p) ◇ p) X0) ◇ (q ◇ (dl (X0 ◇ ((q ◇ ((dl p p) ◇ p)) ◇ (dl q q))) q)) := by
    first | exact superpose ef21769 ef70828 | exact superpose ef70828 ef21769
  have ef71062 (X0 : G) :
      q = (wf ((dl p p) ◇ p) X0) ◇ (q ◇ (((q ◇ ((dl p p) ◇ p)) ◇ (dl q q)) ◇ (dr X0 q))) := by
    first | exact superpose ef637 ef70972 | exact superpose ef70972 ef637
  have ef71141 (X0 : G) :
      q = (dr X0 q) ◇ (q ◇ (((q ◇ ((dl p p) ◇ p)) ◇ (dl q q)) ◇ (wf ((dl p p) ◇ p) X0))) := by
    first | exact superpose ef947 ef71062 | exact superpose ef71062 ef947
  have ef71199 (X0 : G) :
      q = (dr X0 q) ◇ (dl (wf ((dl p p) ◇ p) X0) (dl ((dl p p) ◇ p) (dl q q))) := by
    first | exact superpose ef285 ef71141 | exact superpose ef71141 ef285
  have ef71245 : q = (wf ((dl p p) ◇ p) (dl ((dl p p) ◇ p) (dl q q))) ◇ q := by
    first | exact superpose ef48401 ef71199 | exact superpose ef71199 ef48401
  have ef71276 : q = (((dl p p) ◇ p) ◇ (dl (dl q q) ((dl p p) ◇ p))) ◇ q := by
    first | exact superpose ef6242 ef71245 | exact superpose ef71245 ef6242
  have ef71301 : q = (dr p q) ◇ ((dl (dl q q) ((dl p p) ◇ p)) ◇ (dl p p)) := by
    first | exact superpose ef465 ef71276 | exact superpose ef71276 ef465
  have ef71321 : q = (dr p q) ◇ (p ◇ (dl (dl (dl q q) ((dl p p) ◇ p)) p)) := by
    first | exact superpose ef21769 ef71301 | exact superpose ef71301 ef21769
  have ef71335 : q = (dr p q) ◇ (p ◇ ((p ◇ (dl q q)) ◇ ((dl p p) ◇ p))) := by
    first | exact superpose ef246 ef71321 | exact superpose ef71321 ef246
  have ef71344 : q = (dr p q) ◇ (p ◇ (p ◇ ((dl p (p ◇ (dl q q))) ◇ p))) := by
    first | exact superpose ef70227 ef71335 | exact superpose ef71335 ef70227
  have ef71349 : q = (dr p q) ◇ (dr p (dl p (p ◇ (dl q q)))) := by
    first | exact superpose ef27 ef71344 | exact superpose ef71344 ef27
  have ef71354 : q = (dr p q) ◇ (dr p (dl q q)) := by
    first | exact superpose ef19 ef71349 | exact superpose ef71349 ef19
  have ef71358 : q = dr (p ◇ p) q := by
    first | exact superpose ef1855 ef71354 | exact superpose ef71354 ef1855
  have ef73128 : q ◇ q = p ◇ p := by
    first | exact superpose ef71358 ef16 | exact superpose ef16 ef71358
  have ef75594 (X0 : G) : q = (wf (p ◇ p) X0) ◇ ((X0 ◇ ((q ◇ (p ◇ p)) ◇ q)) ◇ q) := by
    first | exact superpose ef73128 ef96 | exact superpose ef96 ef73128
  have ef75719 (X0 : G) : q = (wf (p ◇ p) X0) ◇ ((dr (q ◇ (p ◇ p)) q) ◇ (dr q X0)) := by
    first | exact superpose ef45082 ef75594 | exact superpose ef75594 ef45082
  have ef75780 (X0 : G) : q = (wf (p ◇ p) X0) ◇ (q ◇ (dr (q ◇ X0) (dl (p ◇ p) q))) := by
    first | exact superpose ef47638 ef75719 | exact superpose ef75719 ef47638
  have ef75826 (X0 : G) : q = ((q ◇ X0) ◇ q) ◇ (dl (wf (p ◇ p) X0) (dl (p ◇ p) q)) := by
    first | exact superpose ef3296 ef75780 | exact superpose ef75780 ef3296
  have ef75859 : q = (wf (p ◇ p) (dl (p ◇ p) q)) ◇ (q ◇ q) := by
    first | exact superpose ef65791 ef75826 | exact superpose ef75826 ef65791
  have ef75878 : q = (wf (p ◇ p) (dl (p ◇ p) q)) ◇ (p ◇ p) := by
    first | exact superpose ef73128 ef75859 | exact superpose ef75859 ef73128
  have ef75893 : q = ((p ◇ p) ◇ (dl q (p ◇ p))) ◇ (p ◇ p) := by
    first | exact superpose ef6242 ef75878 | exact superpose ef75878 ef6242
  have ef75901 : q = dr p (dl p (dl q (p ◇ p))) := by
    first | exact superpose ef247 ef75893 | exact superpose ef75893 ef247
  have ef75905 : q = dr p ((dl (p ◇ p) p) ◇ q) := by
    first | exact superpose ef3631 ef75901 | exact superpose ef75901 ef3631
  have ef75907 : q = (q ◇ p) ◇ (dl (p ◇ p) p) := by
    first | exact superpose ef44 ef75905 | exact superpose ef75905 ef44
  have ef75909 : q = (p ◇ p) ◇ (dl (q ◇ p) p) := by
    first | exact superpose ef960 ef75907 | exact superpose ef75907 ef960
  have ef75911 : q = (p ◇ p) ◇ (p ◇ (dr q p)) := by
    first | exact superpose ef637 ef75909 | exact superpose ef75909 ef637
  have ef75913 : q = dl (dr q p) p := by
    first | exact superpose ef34 ef75911 | exact superpose ef75911 ef34
  have ef75915 : q = dl (dr p p) q := by
    first | exact superpose ef5633 ef75913 | exact superpose ef75913 ef5633
  have ef75916 : q = wf p (dl q p) := by
    first | exact superpose ef3622 ef75915 | exact superpose ef75915 ef3622
  have ef75917 : q = q ◇ (dl p q) := by
    first | exact superpose ef43655 ef75916 | exact superpose ef75916 ef43655
  have ef75918 : q = p ◇ (dl q q) := by
    first | exact superpose ef960 ef75917 | exact superpose ef75917 ef960
  have ef81640 (X0 : G) : p = wf X0 ((wf X0 q) ◇ (dl q q)) := by
    first | exact superpose ef75918 ef1026 | exact superpose ef1026 ef75918
  have ef81668 : p = q := by
    first | exact superpose ef1444 ef81640 | exact superpose ef81640 ef1444
  subsumption ef81668 ef22

/-- Left translation of `x □ y := (x◇(y◇(x/x)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_0L [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (b ◇ (dr a a)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X0 ◇ (X1 ◇ (dr X0 X0)) := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef24 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef112 (X0 X1 : G) : dr X0 X1 = (dr X0 X0) ◇ (wf X0 X1) := by
    first | exact superpose ef20 ef27 | exact superpose ef27 ef20
  have ef1938 : (dr t t) ◇ (wf t p) = dr t q := by
    first | exact superpose ef21 ef112 | exact superpose ef112 ef21
  have ef1987 : dr t q = dr t p := by
    first | exact superpose ef112 ef1938 | exact superpose ef1938 ef112
  have ef2488 : q = dl (dr t p) t := by
    first | exact superpose ef1987 ef24 | exact superpose ef24 ef1987
  have ef2490 : p = q := by
    first | exact superpose ef24 ef2488 | exact superpose ef2488 ef24
  subsumption ef2490 ef22

/-- The operation comes back: `x ◇ y = ((x/x)◇(x◇y))` read in `□` and its divisions, where
`x □ y := (x◇(y◇(x/x)))`. With `winj898_0` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back898_0 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (b ◇ (dr a a)))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wf (wdr x x) (wf x y)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef16 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef19 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef22 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = X0 ◇ (X1 ◇ (dr X0 X0)) := mod_symm (hwdef ..)
  have ef24 (X0 X1 : G) : wf (wdr X0 X1) X1 = X0 := mod_symm (hwrs ..)
  have ef28 : wf (wdr x x) (wf x y) ≠ x ◇ y := mod_symm nh
  have ef33 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef34 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef36 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef37 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef40 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef46 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef50 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef71 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef80 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef18 ef17 | exact superpose ef17 ef18
  have ef82 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef97 (X0 X1 : G) : ((dr X0 X0) ◇ (wf X0 X1)) ◇ X1 = X0 := by
    first | exact superpose ef23 ef17 | exact superpose ef17 ef23
  have ef115 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef19 ef33 | exact superpose ef33 ef19
  have ef116 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef21 ef33 | exact superpose ef33 ef21
  have ef121 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef18 ef33 | exact superpose ef33 ef18
  have ef124 (X0 X1 : G) : dr X0 X1 = (dr X0 X0) ◇ (wf X0 X1) := by
    first | exact superpose ef23 ef33 | exact superpose ef33 ef23
  have ef146 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef50 ef121 | exact superpose ef121 ef50
  have ef154 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (dl X2 X3))) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef16 ef34 | exact superpose ef34 ef16
  have ef165 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef34 ef33 | exact superpose ef33 ef34
  have ef173 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef34 ef22 | exact superpose ef22 ef34
  have ef188 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) ◇ ((X1 ◇ (dl X2 X3)) ◇ X0) = X2 := by
    first | exact superpose ef146 ef154 | exact superpose ef154 ef146
  have ef258 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef37 ef22 | exact superpose ef22 ef37
  have ef259 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef37 ef33 | exact superpose ef33 ef37
  have ef294 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef18 ef40 | exact superpose ef40 ef18
  have ef308 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef37 ef40 | exact superpose ef40 ef37
  have ef319 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef40 ef33 | exact superpose ef33 ef40
  have ef322 (X0 X1 : G) : wf (X0 ◇ X1) X1 = dl (dr (X0 ◇ X1) (X0 ◇ X1)) X0 := by
    first | exact superpose ef40 ef23 | exact superpose ef23 ef40
  have ef326 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef40 ef18 | exact superpose ef18 ef40
  have ef329 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef40 ef22 | exact superpose ef22 ef40
  have ef339 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef259 ef326 | exact superpose ef326 ef259
  have ef342 (X0 X1 : G) : wf (X0 ◇ X1) X1 = dl ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0 := by
    first | exact superpose ef50 ef322 | exact superpose ef322 ef50
  have ef359 (X0 X1 : G) : wf (X0 ◇ X1) X1 = (X0 ◇ (dl (X0 ◇ X1) X0)) ◇ X1 := by
    first | exact superpose ef308 ef342 | exact superpose ef342 ef308
  have ef446 (X0 X1 : G) : (wf X0 X1) ◇ (dr (dr X0 X0) X0) = X1 := by
    first | exact superpose ef23 ef46 | exact superpose ef46 ef23
  have ef467 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef46 ef40 | exact superpose ef40 ef46
  have ef610 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef18 ef50 | exact superpose ef50 ef18
  have ef625 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef259 ef610 | exact superpose ef610 ef259
  have ef649 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef71 ef46 | exact superpose ef46 ef71
  have ef928 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef37 ef82 | exact superpose ef82 ef37
  have ef958 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef294 ef928 | exact superpose ef928 ef294
  have ef972 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef958 | exact superpose ef958 ef40
  have ef1009 (X0 X1 : G) : dr X0 X0 = (dl (wf X0 X1) X1) ◇ X0 := by
    first | exact superpose ef97 ef37 | exact superpose ef37 ef97
  have ef1813 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef40 ef116 | exact superpose ef116 ef40
  have ef1890 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef972 ef1813 | exact superpose ef1813 ef972
  have ef1922 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef258 ef1890 | exact superpose ef1890 ef258
  have ef1935 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef33 ef1922 | exact superpose ef1922 ef33
  have ef3425 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef33 ef165 | exact superpose ef165 ef33
  have ef3485 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef165 ef36 | exact superpose ef36 ef165
  have ef3538 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1935 ef3425 | exact superpose ef3425 ef1935
  have ef3574 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef50 ef3538 | exact superpose ef3538 ef50
  have ef3592 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef116 ef3574 | exact superpose ef3574 ef116
  have ef3931 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef173 ef22 | exact superpose ef22 ef173
  have ef5512 (X0 X1 X2 X3 : G) : dr X1 ((X1 ◇ X2) ◇ (X0 ◇ X3)) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef80 ef319 | exact superpose ef319 ef80
  have ef5517 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef165 ef319 | exact superpose ef319 ef165
  have ef5568 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef50 ef5517 | exact superpose ef5517 ef50
  have ef5573 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef50 ef5512 | exact superpose ef5512 ef50
  have ef5623 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef649 ef5568 | exact superpose ef5568 ef649
  have ef5626 (X0 X2 X3 : G) : dl X2 (X0 ◇ X3) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef40 ef5573 | exact superpose ef5573 ef40
  have ef5652 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef40 ef5623 | exact superpose ef5623 ef40
  have ef5694 (X0 X1 X2 : G) : (wf X0 X1) ◇ X2 = dl (dr X0 X1) (dl X2 (dr X0 X0)) := by
    first | exact superpose ef124 ef329 | exact superpose ef329 ef124
  have ef5741 (X0 X1 X2 : G) : (wf X0 X1) ◇ X2 = (dl (dr X0 X0) (dr X0 X1)) ◇ X2 := by
    first | exact superpose ef3931 ef5694 | exact superpose ef5694 ef3931
  have ef5778 (X0 X1 X2 : G) : (wf X0 X1) ◇ X2 = X0 ◇ ((dr X2 (dr X0 X1)) ◇ X0) := by
    first | exact superpose ef3485 ef5741 | exact superpose ef5741 ef3485
  have ef5801 (X0 X1 X2 : G) : (wf X0 X1) ◇ X2 = X0 ◇ ((dr X2 X0) ◇ (dr X0 X1)) := by
    first | exact superpose ef3592 ef5778 | exact superpose ef5778 ef3592
  have ef5839 (X0 X1 X2 : G) : dr X1 (dl X2 X0) = dr X0 (dl X2 X1) := by
    first | exact superpose ef339 ef20 | exact superpose ef20 ef339
  have ef6748 (X0 X1 X2 : G) : dr X1 (dr (dr X2 X2) X2) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef446 ef625 | exact superpose ef625 ef446
  have ef6789 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ (dr X2 X2)) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef115 ef6748 | exact superpose ef6748 ef115
  have ef6831 (X0 X1 X2 : G) : wf X2 X1 = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef23 ef6789 | exact superpose ef6789 ef23
  have ef9361 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (dr X0 X0)) = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef1009 ef33 | exact superpose ef33 ef1009
  have ef9405 (X0 X1 X2 : G) :
      dl (dr (X0 ◇ X1) (X0 ◇ X1)) X0 = dr X1 (dl (wf (X0 ◇ X1) X2) X2) := by
    first | exact superpose ef1009 ef319 | exact superpose ef319 ef1009
  have ef9436 (X0 X1 X2 : G) :
      dr X1 (dl (wf (X0 ◇ X1) X2) X2) = dl (dr X0 (X0 ◇ X1)) (X0 ◇ X1) := by
    first | exact superpose ef5652 ef9405 | exact superpose ef9405 ef5652
  have ef9472 (X0 X1 X2 : G) : wf X0 X1 = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef23 ef9361 | exact superpose ef9361 ef23
  have ef9501 (X0 X1 X2 : G) :
      dr X1 (dl (wf (X0 ◇ X1) X2) X2) = dl X0 ((dr X0 (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef5626 ef9436 | exact superpose ef9436 ef5626
  have ef9548 (X0 X1 X2 : G) :
      dr X1 (dl (wf (X0 ◇ X1) X2) X2) = dl X0 ((dr X0 X1) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef3592 ef9501 | exact superpose ef9501 ef3592
  have ef9575 (X0 X1 X2 : G) :
      dr X1 (dl (wf (X0 ◇ X1) X2) X2) = X0 ◇ ((dr X1 (dr X0 X1)) ◇ X0) := by
    first | exact superpose ef467 ef9548 | exact superpose ef9548 ef467
  have ef9597 (X0 X1 X2 : G) :
      dr X1 (dl (wf (X0 ◇ X1) X2) X2) = X0 ◇ ((dr X1 X0) ◇ (dr X0 X1)) := by
    first | exact superpose ef3592 ef9575 | exact superpose ef9575 ef3592
  have ef9613 (X0 X1 X2 : G) : (wf X0 X1) ◇ X1 = dr X1 (dl (wf (X0 ◇ X1) X2) X2) := by
    first | exact superpose ef5801 ef9597 | exact superpose ef9597 ef5801
  have ef9626 (X0 X1 : G) : wf (X0 ◇ X1) X1 = (wf X0 X1) ◇ X1 := by
    first | exact superpose ef9472 ef9613 | exact superpose ef9613 ef9472
  have ef52334 (X0 X1 X2 : G) : dr X1 (dl X0 X2) = wf (wdr X0 X1) X2 := by
    first | exact superpose ef24 ef6831 | exact superpose ef6831 ef24
  have ef57657 (X0 X1 : G) : X0 ◇ X1 = ((X1 ◇ X0) ◇ X0) ◇ (wf (X0 ◇ X1) X1) := by
    first | exact superpose ef359 ef188 | exact superpose ef188 ef359
  have ef57770 (X0 X1 : G) : X0 ◇ X1 = ((X1 ◇ X0) ◇ X0) ◇ ((wf X0 X1) ◇ X1) := by
    first | exact superpose ef9626 ef57657 | exact superpose ef57657 ef9626
  have ef58037 (X0 X1 : G) : X0 ◇ X1 = dr (wf X0 X1) (dl X0 X0) := by
    first | exact superpose ef259 ef57770 | exact superpose ef57770 ef259
  have ef58301 (X0 X1 : G) : X0 ◇ X1 = dr X0 (dl X0 (wf X0 X1)) := by
    first | exact superpose ef5839 ef58037 | exact superpose ef58037 ef5839
  have ef58553 (X0 X1 : G) : X0 ◇ X1 = wf (wdr X0 X0) (wf X0 X1) := by
    first | exact superpose ef52334 ef58301 | exact superpose ef58301 ef52334
  have ef159576 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef58553 ef28 | exact superpose ef28 ef58553
  exact absurd rfl ef159576

set_option maxHeartbeats 800000 in
/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the operation `x □ y := (x◇(y◇(x/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_614_0 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (b ◇ (dr a a)))
    (x : G) :
    x = wf x (wf x (wf (wf x x) x)) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (X1 ◇ (dr X0 X0)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf x (wf x (wf (wf x x) x)) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef84 (X0 X1 : G) : (dr (X0 ◇ X1) (X0 ◇ X1)) ◇ (wf (X0 ◇ X1) X1) = X0 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef85 (X0 X1 : G) : ((dr X0 X0) ◇ (wf X0 X1)) ◇ X1 = X0 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef87 (X0 X1 X2 : G) : (X1 ◇ (dr X0 X0)) ◇ ((X2 ◇ X0) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef93 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((X2 ◇ (dr (X0 ◇ X1) (X0 ◇ X1))) ◇ X0) = X1 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef94 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = X1 := by
    first | exact superpose ef40 ef93 | exact superpose ef93 ef40
  have ef98 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (wf (X0 ◇ X1) X1) = X0 := by
    first | exact superpose ef40 ef84 | exact superpose ef84 ef40
  have ef101 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef102 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef110 (X0 X1 : G) : dr X0 X1 = (dr X0 X0) ◇ (wf X0 X1) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef111 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef23
  have ef125 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef151 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef159 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef196 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef26 ef18 | exact superpose ef18 ef26
  have ef244 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef245 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef280 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef291 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef294 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef432 (X0 X1 : G) : (wf X0 X1) ◇ (dr (dr X0 X0) X0) = X1 := by
    first | exact superpose ef19 ef36 | exact superpose ef36 ef19
  have ef443 (X0 X1 : G) : X1 ◇ X0 = wf X1 (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef596 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef14 ef40 | exact superpose ef40 ef14
  have ef611 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef245 ef596 | exact superpose ef596 ef245
  have ef635 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef739 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ ((X2 ◇ X0) ◇ (dr X3 X2))) ◇ X0 := by
    first | exact superpose ef63 ef30 | exact superpose ef30 ef63
  have ef764 (X1 X2 X3 : G) : dl X3 X1 = dl ((dr X3 X2) ◇ X2) X1 := by
    first | exact superpose ef291 ef739 | exact superpose ef739 ef291
  have ef795 (X1 X2 X3 : G) : dl X3 X1 = X2 ◇ (dr (dr X3 X2) X1) := by
    first | exact superpose ef635 ef764 | exact superpose ef764 ef635
  have ef912 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef914 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef944 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef280 ef914 | exact superpose ef914 ef280
  have ef945 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef125 ef912 | exact superpose ef912 ef125
  have ef958 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef944 | exact superpose ef944 ef30
  have ef989 (X0 X1 : G) : dr X0 X0 = (dl (wf X0 X1) X1) ◇ X0 := by
    first | exact superpose ef85 ef27 | exact superpose ef27 ef85
  have ef1452 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ ((dr X0 X0) ◇ (wf X0 X1)))) ◇ X3) = X2 := by
    first | exact superpose ef85 ef69 | exact superpose ef69 ef85
  have ef1634 (X0 X1 X2 : G) : X0 ◇ (dl (((dr X0 X0) ◇ (wf X0 X1)) ◇ X1) X2) = X2 := by
    first | exact superpose ef291 ef1452 | exact superpose ef1452 ef291
  have ef1694 (X0 X1 X2 : G) : X0 ◇ ((X2 ◇ (dl (wf X0 X1) X1)) ◇ (dr X0 X0)) = X2 := by
    first | exact superpose ef294 ef1634 | exact superpose ef1634 ef294
  have ef1732 (X0 X1 X2 : G) : wf X0 (X2 ◇ (dl (wf X0 X1) X1)) = X2 := by
    first | exact superpose ef19 ef1694 | exact superpose ef1694 ef19
  have ef1788 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef102 | exact superpose ef102 ef30
  have ef1791 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef102 | exact superpose ef102 ef15
  have ef1802 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef102 ef23 | exact superpose ef23 ef102
  have ef1865 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef958 ef1788 | exact superpose ef1788 ef958
  have ef1897 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef244 ef1865 | exact superpose ef1865 ef244
  have ef1910 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1897 | exact superpose ef1897 ef23
  have ef2392 (X0 X1 X2 : G) : dl (wf X0 X1) X2 = (X2 ◇ (dr X0 X0)) ◇ (dr X0 X1) := by
    first | exact superpose ef110 ef30 | exact superpose ef30 ef110
  have ef2531 (X0 X1 X2 X3 : G) :
      X1 ◇ (X2 ◇ (dr X3 X3)) = dl (X0 ◇ X1) ((X0 ◇ X3) ◇ (wf X3 X2)) := by
    first | exact superpose ef87 ef72 | exact superpose ef72 ef87
  have ef2548 (X0 X1 X2 X3 : G) :
      X1 ◇ (X2 ◇ (dr X3 X3)) = X3 ◇ (((wf X3 X2) ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef280 ef2531 | exact superpose ef2531 ef280
  have ef2613 (X1 X2 X3 : G) : X1 ◇ (X2 ◇ (dr X3 X3)) = X3 ◇ (dl X1 (wf X3 X2)) := by
    first | exact superpose ef30 ef2548 | exact superpose ef2548 ef30
  have ef2731 (X0 X1 X2 : G) : dr (wf X0 X1) X2 = (dr X0 X1) ◇ (dr X2 (dr X0 X0)) := by
    first | exact superpose ef110 ef111 | exact superpose ef111 ef110
  have ef2747 (X0 X1 : G) : wf X1 (X1 ◇ X0) = X1 ◇ (dr X0 X1) := by
    first | exact superpose ef111 ef19 | exact superpose ef19 ef111
  have ef2776 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ X0) = dl ((dr X0 X1) ◇ X2) (dr X1 X3) := by
    first | exact superpose ef111 ef72 | exact superpose ef72 ef111
  have ef2803 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ X0) = X1 ◇ (X3 ◇ ((dr X0 X1) ◇ X2)) := by
    first | exact superpose ef125 ef2776 | exact superpose ef2776 ef125
  have ef2834 (X0 X1 X2 : G) : dr (wf X0 X1) X2 = (dr X0 X1) ◇ (X0 ◇ (X2 ◇ X0)) := by
    first | exact superpose ef101 ef2731 | exact superpose ef2731 ef101
  have ef2882 (X0 X1 X2 : G) : dr (wf X0 X1) X2 = X0 ◇ (X0 ◇ (X2 ◇ (dr X0 X1))) := by
    first | exact superpose ef945 ef2834 | exact superpose ef2834 ef945
  have ef3435 (X0 X1 X2 X3 : G) : (X2 ◇ (dr X0 X1)) ◇ X3 = (dl (X3 ◇ X2) X1) ◇ X0 := by
    first | exact superpose ef151 ef13 | exact superpose ef13 ef151
  have ef3448 (X0 X1 X2 X3 : G) : (X2 ◇ (dr X0 X1)) ◇ X3 = (X2 ◇ (dr X3 X1)) ◇ X0 := by
    first | exact superpose ef635 ef3435 | exact superpose ef3435 ef635
  have ef3631 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (dl X0 (wf (X0 ◇ X1) X1)) ◇ X0 := by
    first | exact superpose ef98 ef27 | exact superpose ef27 ef98
  have ef3877 (X0 X1 : G) : wf X0 (dl X1 X0) = dl (dr X0 X0) X1 := by
    first | exact superpose ef159 ef19 | exact superpose ef19 ef159
  have ef4099 (X0 X1 X2 : G) :
      (wf ((dr X0 X1) ◇ X1) X2) ◇ ((X2 ◇ (dr ((dr X0 X1) ◇ X1) X0)) ◇ (dr X0 X1)) = X1 := by
    first | exact superpose ef111 ef94 | exact superpose ef94 ef111
  have ef4204 (X0 X1 X2 : G) :
      (wf ((dr X0 X1) ◇ X1) X2) ◇ ((X2 ◇ (dr (dr X0 X1) X0)) ◇ ((dr X0 X1) ◇ X1)) = X1 := by
    first | exact superpose ef3448 ef4099 | exact superpose ef4099 ef3448
  have ef4276 (X0 X1 X2 : G) :
      X1 ◇ ((X2 ◇ (dr (dr X0 X1) X0)) ◇ ((dr X0 X1) ◇ (wf ((dr X0 X1) ◇ X1) X2))) = X1 := by
    first | exact superpose ef945 ef4204 | exact superpose ef4204 ef945
  have ef4336 (X0 X1 X2 : G) :
      (wf ((dr X0 X1) ◇ X1) X2) ◇ ((X2 ◇ (dr (dr X0 X1) X0)) ◇ X0) = X1 := by
    first | exact superpose ef2803 ef4276 | exact superpose ef4276 ef2803
  have ef4379 (X0 X1 X2 : G) :
      (wf ((dr X0 X1) ◇ X1) X2) ◇ ((X2 ◇ (dr X0 X0)) ◇ (dr X0 X1)) = X1 := by
    first | exact superpose ef3448 ef4336 | exact superpose ef4336 ef3448
  have ef4411 (X0 X1 X2 : G) : (wf ((dr X0 X1) ◇ X1) X2) ◇ (dl (wf X0 X1) X2) = X1 := by
    first | exact superpose ef2392 ef4379 | exact superpose ef4379 ef2392
  have ef4439 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl (wf ((dr X0 X1) ◇ X1) X2) X2) = X1 := by
    first | exact superpose ef958 ef4411 | exact superpose ef4411 ef958
  have ef4455 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl (wf X0 X2) X2) = X1 := by
    first | exact superpose ef15 ef4439 | exact superpose ef4439 ef15
  have ef4634 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef196 ef13 | exact superpose ef13 ef196
  have ef6209 (X0 X1 : G) : X0 ◇ (dl X1 X0) = wf X0 (dl X0 X1) := by
    first | exact superpose ef159 ef443 | exact superpose ef443 ef159
  have ef6700 (X0 X1 X2 : G) : dr X1 (dr (dr X2 X2) X2) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef432 ef611 | exact superpose ef611 ef432
  have ef6741 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ (dr X2 X2)) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef101 ef6700 | exact superpose ef6700 ef101
  have ef6783 (X0 X1 X2 : G) : wf X2 X1 = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef19 ef6741 | exact superpose ef6741 ef19
  have ef7305 (X0 X1 : G) : wf (dr X0 X1) X1 = (dr X0 X1) ◇ (dl X0 (dr X0 X1)) := by
    first | exact superpose ef795 ef19 | exact superpose ef19 ef795
  have ef7419 (X0 X1 : G) : wf (dr X0 X1) X1 = X0 ◇ (dl (dr X0 X1) (dr X0 X1)) := by
    first | exact superpose ef958 ef7305 | exact superpose ef7305 ef958
  have ef7479 (X0 X1 : G) : wf (dr X0 X1) X1 = X0 ◇ (X0 ◇ (X1 ◇ (dr X0 X1))) := by
    first | exact superpose ef125 ef7419 | exact superpose ef7419 ef125
  have ef7514 (X0 X1 : G) : dr (wf X0 X1) X1 = wf (dr X0 X1) X1 := by
    first | exact superpose ef2882 ef7479 | exact superpose ef7479 ef2882
  have ef8886 (X0 X1 X2 : G) : dl (dr X0 X0) X2 = X0 ◇ (dr (dl (wf X0 X1) X1) X2) := by
    first | exact superpose ef989 ef635 | exact superpose ef635 ef989
  have ef8933 (X0 X1 X2 : G) : dl (dr X0 X0) X2 = X0 ◇ (X1 ◇ (dr X2 (wf X0 X1))) := by
    first | exact superpose ef1802 ef8886 | exact superpose ef8886 ef1802
  have ef8995 (X0 X1 X2 : G) : wf X0 (dl X2 X0) = X0 ◇ (X1 ◇ (dr X2 (wf X0 X1))) := by
    first | exact superpose ef3877 ef8933 | exact superpose ef8933 ef3877
  have ef9716 (X0 X1 X2 X3 : G) : wf X2 (dl X0 X1) = X1 ◇ (dr (dl (wf X2 X3) X3) X0) := by
    first | exact superpose ef196 ef1732 | exact superpose ef1732 ef196
  have ef9756 (X0 X1 X2 X3 : G) : wf X2 (dl X0 X1) = X1 ◇ (X3 ◇ (dr X0 (wf X2 X3))) := by
    first | exact superpose ef1802 ef9716 | exact superpose ef9716 ef1802
  have ef19189 (X0 X1 : G) : wf X0 (wf X0 X1) = X0 ◇ (dr (X1 ◇ (dr X0 X0)) X0) := by
    first | exact superpose ef19 ef2747 | exact superpose ef2747 ef19
  have ef19318 (X0 X1 : G) : wf X0 (wf X0 X1) = X0 ◇ (dr (X1 ◇ X0) (dr X0 X0)) := by
    first | exact superpose ef1910 ef19189 | exact superpose ef19189 ef1910
  have ef19376 (X0 X1 : G) : wf X0 (wf X0 X1) = X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    first | exact superpose ef101 ef19318 | exact superpose ef19318 ef101
  have ef19423 (X0 X1 : G) : wf X0 (wf X0 X1) = dr X0 (X1 ◇ X0) := by
    first | exact superpose ef23 ef19376 | exact superpose ef19376 ef23
  have ef19452 (X0 X1 : G) : (X0 ◇ X0) ◇ X1 = wf X0 (wf X0 X1) := by
    first | exact superpose ef40 ef19423 | exact superpose ef19423 ef40
  have ef27659 (X0 X1 X2 : G) :
      wf (wf X1 X0) X0 = (wf X1 X0) ◇ (dr (dl (wf X1 X2) X2) (wf X1 X0)) := by
    first | exact superpose ef4455 ef2747 | exact superpose ef2747 ef4455
  have ef27663 (X0 X1 X2 : G) :
      wf (wf X1 X0) X0 = (wf X1 X0) ◇ (X2 ◇ (dr (wf X1 X0) (wf X1 X2))) := by
    first | exact superpose ef1802 ef27659 | exact superpose ef27659 ef1802
  have ef27729 (X0 X1 : G) : wf (wf X1 X0) X0 = wf X1 (dl (wf X1 X0) (wf X1 X0)) := by
    first | exact superpose ef9756 ef27663 | exact superpose ef27663 ef9756
  have ef45822 (X0 X1 X2 X3 : G) : dl X3 (wf X0 X1) = X2 ◇ ((dl (wf X0 X2) X1) ◇ X3) := by
    first | exact superpose ef6783 ef125 | exact superpose ef125 ef6783
  have ef51700 (X0 X1 X2 : G) : dr (wf (dr X0 X1) X1) X2 = (dl X2 X1) ◇ (wf X0 X1) := by
    first | exact superpose ef7514 ef1791 | exact superpose ef1791 ef7514
  have ef73196 : x ≠ (x ◇ x) ◇ (wf (wf x x) x) := by
    first | exact superpose ef19452 ef20 | exact superpose ef20 ef19452
  have ef132951 (X0 X1 : G) :
      X0 ◇ (dr X0 X0) = (dl (dl (wf X0 X1) X1) (wf (dr X0 X0) X0)) ◇ (dl (wf X0 X1) X1) := by
    first | exact superpose ef989 ef3631 | exact superpose ef3631 ef989
  have ef133385 (X0 X1 : G) :
      X0 ◇ (dr X0 X0) = (wf X0 X1) ◇ (dl (dl (dl (wf X0 X1) X1) (wf (dr X0 X0) X0)) X1) := by
    first | exact superpose ef958 ef132951 | exact superpose ef132951 ef958
  have ef133701 (X0 X1 : G) :
      X0 ◇ (dr X0 X0) = (wf X0 X1) ◇ ((X1 ◇ (dl (wf X0 X1) X1)) ◇ (wf (dr X0 X0) X0)) := by
    first | exact superpose ef244 ef133385 | exact superpose ef133385 ef244
  have ef134005 (X0 X1 : G) :
      X0 ◇ (dr X0 X0) = (wf X0 X1) ◇ (X1 ◇ (dr ((wf (dr X0 X0) X0) ◇ X1) (wf X0 X1))) := by
    first | exact superpose ef4634 ef133701 | exact superpose ef133701 ef4634
  have ef134277 (X0 X1 : G) :
      X0 ◇ (dr X0 X0) = wf X0 (dl ((wf (dr X0 X0) X0) ◇ X1) (wf X0 X1)) := by
    first | exact superpose ef9756 ef134005 | exact superpose ef134005 ef9756
  have ef134514 (X0 X1 : G) :
      X0 ◇ (dr X0 X0) = wf X0 (X1 ◇ (dr (wf (dr X0 X0) X0) (wf X0 X1))) := by
    first | exact superpose ef635 ef134277 | exact superpose ef134277 ef635
  have ef134728 (X0 X1 : G) : X0 ◇ (dr X0 X0) = wf X0 (X1 ◇ ((dl (wf X0 X1) X0) ◇ (wf X0 X0))) := by
    first | exact superpose ef51700 ef134514 | exact superpose ef134514 ef51700
  have ef134917 (X0 : G) : X0 ◇ (dr X0 X0) = wf X0 (dl (wf X0 X0) (wf X0 X0)) := by
    first | exact superpose ef45822 ef134728 | exact superpose ef134728 ef45822
  have ef135079 (X0 : G) : X0 ◇ (dr X0 X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef27729 ef134917 | exact superpose ef134917 ef27729
  have ef135813 : x ≠ (x ◇ x) ◇ (x ◇ (dr x x)) := by
    first | exact superpose ef135079 ef73196 | exact superpose ef73196 ef135079
  have ef135816 : x ≠ x ◇ (dl (x ◇ x) (wf x x)) := by
    first | exact superpose ef2613 ef135813 | exact superpose ef135813 ef2613
  have ef135859 : x ≠ x ◇ (x ◇ (dr x (wf x x))) := by
    first | exact superpose ef635 ef135816 | exact superpose ef135816 ef635
  have ef135897 : x ≠ wf x (dl x x) := by
    first | exact superpose ef8995 ef135859 | exact superpose ef135859 ef8995
  have ef135929 : x ≠ x ◇ (dl x x) := by
    first | exact superpose ef6209 ef135897 | exact superpose ef135897 ef6209
  subsumption ef135929 ef17

theorem Equation614_termStructuralFromFin_Equation898_qdiv :
    Law614.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.op (.var 1) (.rdv (.var 0) (.var 0)))) (.op (.rdv (.var 0) (.var 0)) (.op (.var 0) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law614.models_iff]
    exact fun x ↦
      @qaux898_614_0 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_0R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_0L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_0 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := (x◇(x/(y/x)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_6R [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef23 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef18 ef17 | exact superpose ef17 ef18
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef28 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef30 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef31 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef34 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef41 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef44 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef63 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef66 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef74 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef84 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef89 (X0 X1 X2 : G) : (((dr X0 (dr X1 X0)) ◇ X2) ◇ X0) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef91 (X0 X1 : G) : dr (wf X0 X1) (dr X0 (dr X1 X0)) = X0 := by
    first | exact superpose ef20 ef17 | exact superpose ef17 ef20
  have ef92 (X0 X1 : G) : dr X0 (dr X1 X0) = dl X0 (wf X0 X1) := by
    first | exact superpose ef20 ef19 | exact superpose ef19 ef20
  have ef93 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((dr (X0 ◇ X1) (dr X2 (X0 ◇ X1))) ◇ X0) = X1 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef94 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((dr (X0 ◇ X1) ((X1 ◇ X2) ◇ X0)) ◇ X0) = X1 := by
    first | exact superpose ef44 ef93 | exact superpose ef93 ef44
  have ef97 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X0) = X1 := by
    first | exact superpose ef44 ef94 | exact superpose ef94 ef44
  have ef98 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef99 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef18 ef27 | exact superpose ef27 ef18
  have ef101 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef27 ef27
  have ef103 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef14 ef27 | exact superpose ef27 ef14
  have ef104 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef15 ef27 | exact superpose ef27 ef15
  have ef107 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef27 ef27
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef27 ef19 | exact superpose ef19 ef27
  have ef128 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef44 ef104 | exact superpose ef104 ef44
  have ef129 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef44 ef103 | exact superpose ef103 ef44
  have ef146 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef154 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef28 ef19 | exact superpose ef19 ef28
  have ef174 (X0 X1 : G) : (dr X1 X0) ◇ ((wf X0 X1) ◇ X0) = X0 := by
    first | exact superpose ef20 ef30 | exact superpose ef30 ef20
  have ef187 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef30 ef19 | exact superpose ef19 ef30
  have ef190 (X0 X1 X2 X3 : G) : ((X0 ◇ (dr X1 (dl X2 X3))) ◇ X1) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef30 ef28 | exact superpose ef28 ef30
  have ef219 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef14 ef31 | exact superpose ef31 ef14
  have ef235 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef31 ef19 | exact superpose ef19 ef31
  have ef236 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef31 ef27 | exact superpose ef27 ef31
  have ef266 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef27 ef34 | exact superpose ef34 ef27
  have ef269 (X0 X1 X2 : G) : dl X2 X0 = (wf X0 X1) ◇ ((dr X0 (dr X1 X0)) ◇ X2) := by
    first | exact superpose ef20 ef34 | exact superpose ef34 ef20
  have ef271 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef272 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef34 ef34
  have ef274 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef277 (X0 X1 X2 X3 : G) : dl (X0 ◇ (X1 ◇ X3)) X2 = (X2 ◇ X3) ◇ (dr X0 X1) := by
    first | exact superpose ef27 ef34 | exact superpose ef34 ef27
  have ef280 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (dr X0 (dr X1 X0)) X2 := by
    first | exact superpose ef20 ef34 | exact superpose ef34 ef20
  have ef282 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef285 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef295 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef301 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef34 ef15 | exact superpose ef15 ef34
  have ef305 (X0 X1 X2 X3 : G) : dr X3 (X1 ◇ X2) = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef311 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef44 ef305 | exact superpose ef305 ef44
  have ef314 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef236 ef301 | exact superpose ef301 ef236
  have ef323 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (X0 ◇ (X0 ◇ X1)) X2 := by
    first | exact superpose ef98 ef280 | exact superpose ef280 ef98
  have ef328 (X0 X1 X2 : G) : dl X2 X0 = (wf X0 X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    first | exact superpose ef98 ef269 | exact superpose ef269 ef98
  have ef334 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (dr X0 X0) := by
    first | exact superpose ef277 ef323 | exact superpose ef323 ef277
  have ef439 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef40 ef34 | exact superpose ef34 ef40
  have ef440 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef40 ef34 | exact superpose ef34 ef40
  have ef513 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef41 ef31 | exact superpose ef31 ef41
  have ef579 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2) = dr X3 (dl X0 X1) := by
    first | exact superpose ef34 ef44 | exact superpose ef44 ef34
  have ef620 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef63 ef40 | exact superpose ef40 ef63
  have ef720 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef65 ef27 | exact superpose ef27 ef65
  have ef723 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ ((X2 ◇ X0) ◇ (dr X3 X2))) ◇ X0 := by
    first | exact superpose ef65 ef34 | exact superpose ef34 ef65
  have ef746 (X1 X2 X3 : G) : dl X3 X1 = dl ((dr X3 X2) ◇ X2) X1 := by
    first | exact superpose ef282 ef723 | exact superpose ef723 ef282
  have ef749 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef44 ef720 | exact superpose ef720 ef44
  have ef777 (X1 X2 X3 : G) : dl X3 X1 = X2 ◇ (dr (dr X3 X2) X1) := by
    first | exact superpose ef620 ef746 | exact superpose ef746 ef620
  have ef797 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef27 ef66 | exact superpose ef66 ef27
  have ef816 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef66 ef34 | exact superpose ef34 ef66
  have ef845 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef282 ef816 | exact superpose ef816 ef282
  have ef867 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef620 ef845 | exact superpose ef845 ef620
  have ef892 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef40 ef74 | exact superpose ef74 ef40
  have ef894 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef74 | exact superpose ef74 ef31
  have ef924 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef271 ef894 | exact superpose ef894 ef271
  have ef925 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef121 ef892 | exact superpose ef892 ef121
  have ef939 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef34 ef924 | exact superpose ef924 ef34
  have ef956 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef65 ef84 | exact superpose ef84 ef65
  have ef965 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef44 ef956 | exact superpose ef956 ef44
  have ef976 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef749 ef965 | exact superpose ef965 ef749
  have ef984 : q = dr (wf p t) (dr q (dr t q)) := by
    first | exact superpose ef21 ef91 | exact superpose ef91 ef21
  have ef1004 : q = (dr t q) ◇ ((wf p t) ◇ q) := by
    first | exact superpose ef98 ef984 | exact superpose ef984 ef98
  have ef1023 : dr q (dr t q) = dl q (wf p t) := by
    first | exact superpose ef21 ef92 | exact superpose ef92 ef21
  have ef1035 : dl q (wf p t) = q ◇ (q ◇ t) := by
    first | exact superpose ef98 ef1023 | exact superpose ef1023 ef98
  have ef1428 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef18 ef99 | exact superpose ef99 ef18
  have ef1440 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef15 ef99 | exact superpose ef99 ef15
  have ef1441 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef34 ef99 | exact superpose ef99 ef34
  have ef1442 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef40 ef99 | exact superpose ef99 ef40
  have ef1443 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef16 ef99 | exact superpose ef99 ef16
  have ef1445 (X0 X1 X2 X3 : G) : dr (dl X1 X3) X2 = (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) := by
    first | exact superpose ef99 ef99
  have ef1453 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef99 ef27 | exact superpose ef27 ef99
  have ef1509 (X0 X1 X2 X3 : G) : (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) = X3 ◇ (dr X2 X1) := by
    first | exact superpose ef1453 ef1445 | exact superpose ef1445 ef1453
  have ef1511 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef121 ef1442 | exact superpose ef1442 ef121
  have ef1512 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef939 ef1441 | exact superpose ef1441 ef939
  have ef1541 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef235 ef1512 | exact superpose ef1512 ef235
  have ef1551 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef27 ef1541 | exact superpose ef1541 ef27
  have ef2804 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef27 ef146 | exact superpose ef146 ef27
  have ef2912 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1551 ef2804 | exact superpose ef2804 ef1551
  have ef2946 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef44 ef2912 | exact superpose ef2912 ef44
  have ef2963 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef99 ef2946 | exact superpose ef2946 ef99
  have ef3242 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef63 ef154 | exact superpose ef154 ef63
  have ef3266 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef154 ef19 | exact superpose ef19 ef154
  have ef3345 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef620 ef3242 | exact superpose ef3242 ef620
  have ef3378 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1453 ef3345 | exact superpose ef3345 ef1453
  have ef3402 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef867 ef3378 | exact superpose ef3378 ef867
  have ef3446 (X0 X1 : G) : dr X1 X0 = (X0 ◇ X0) ◇ (wf X0 X1) := by
    first | exact superpose ef16 ef89 | exact superpose ef89 ef16
  have ef3676 (X0 X1 : G) : dr (dr X1 X0) (wf X0 X1) = X0 ◇ X0 := by
    first | exact superpose ef174 ef27 | exact superpose ef27 ef174
  have ef3684 (X0 X1 : G) : (wf X0 X1) ◇ X0 = dl (dr X1 X0) X0 := by
    first | exact superpose ef174 ef19 | exact superpose ef19 ef174
  have ef3738 (X0 X1 : G) : X0 ◇ X0 = (dl (wf X0 X1) X0) ◇ X1 := by
    first | exact superpose ef1443 ef3676 | exact superpose ef3676 ef1443
  have ef3858 (X0 X1 : G) : (wf (X1 ◇ X0) (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0 = X0 := by
    first | exact superpose ef14 ef97 | exact superpose ef97 ef14
  have ef3931 (X0 X1 : G) : (wf (X1 ◇ X0) (wf X1 X0)) ◇ X0 = X0 := by
    first | exact superpose ef976 ef3858 | exact superpose ef3858 ef976
  have ef4401 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef187 ef14 | exact superpose ef14 ef187
  have ef5497 (X0 X1 X2 : G) : dr X1 (dl X2 X0) = dr X0 (dl X2 X1) := by
    first | exact superpose ef314 ef17 | exact superpose ef17 ef314
  have ef5517 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef314 ef74 | exact superpose ef74 ef314
  have ef5538 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3266 ef5517 | exact superpose ef5517 ef3266
  have ef5781 (X0 X1 X2 X3 : G) : dl X1 X2 = (dl X0 X1) ◇ ((X3 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef65 ef513 | exact superpose ef513 ef65
  have ef5841 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dl X0 X1) = dr (dl (X3 ◇ X1) X0) X2 := by
    first | exact superpose ef513 ef99 | exact superpose ef99 ef513
  have ef5882 (X0 X1 X2 X3 : G) : X0 ◇ (dr X2 (X3 ◇ X1)) = (dl X2 X3) ◇ (dl X0 X1) := by
    first | exact superpose ef1453 ef5841 | exact superpose ef5841 ef1453
  have ef5931 (X1 X2 X3 : G) : dl X1 X2 = dl (dr X2 X3) (X1 ◇ X3) := by
    first | exact superpose ef272 ef5781 | exact superpose ef5781 ef272
  have ef5956 (X0 X1 X2 X3 : G) : X0 ◇ ((X1 ◇ X2) ◇ X3) = (dl X2 X3) ◇ (dl X0 X1) := by
    first | exact superpose ef44 ef5882 | exact superpose ef5882 ef44
  have ef6665 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (dr X3 X2) = dr (dr (dr X0 X2) X1) X3 := by
    first | exact superpose ef777 ef107 | exact superpose ef107 ef777
  have ef6706 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (dr X3 X2) = (dl X3 X1) ◇ (dr X0 X2) := by
    first | exact superpose ef1443 ef6665 | exact superpose ef6665 ef1443
  have ef8071 (X0 X1 X2 : G) : X2 ◇ (X2 ◇ (dr X0 X1)) = wf X2 (X0 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef27 ef976 | exact superpose ef976 ef27
  have ef8490 : q = (dl q (wf p t)) ◇ (dr t q) := by
    first | exact superpose ef1004 ef219 | exact superpose ef219 ef1004
  have ef8493 : dr t q = (q ◇ q) ◇ (wf p t) := by
    first | exact superpose ef1004 ef14 | exact superpose ef14 ef1004
  have ef8578 : q = (dl t (wf p t)) ◇ (dr q q) := by
    first | exact superpose ef6706 ef8490 | exact superpose ef8490 ef6706
  have ef8849 : wf p t = q ◇ (q ◇ (q ◇ t)) := by
    first | exact superpose ef1035 ef18 | exact superpose ef18 ef1035
  have ef8883 : wf p t = t ◇ (q ◇ (q ◇ q)) := by
    first | exact superpose ef925 ef8849 | exact superpose ef8849 ef925
  have ef10139 (X0 X1 : G) : wf X1 X0 = dl (X1 ◇ X1) (dr X0 X1) := by
    first | exact superpose ef3446 ef19 | exact superpose ef19 ef3446
  have ef10140 (X0 X1 X2 : G) : (wf X1 X0) ◇ (X2 ◇ (dr X0 X1)) = dr X2 (X1 ◇ X1) := by
    first | exact superpose ef3446 ef27 | exact superpose ef27 ef3446
  have ef10219 (X0 X1 X2 : G) : (X1 ◇ X2) ◇ X1 = (wf X1 X0) ◇ (X2 ◇ (dr X0 X1)) := by
    first | exact superpose ef44 ef10140 | exact superpose ef10140 ef44
  have ef10220 (X0 X1 : G) : wf X1 X0 = X0 ◇ (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef121 ef10139 | exact superpose ef10139 ef121
  have ef10365 (X0 X1 : G) : dr X0 X0 = wf (X1 ◇ X0) (wf X1 X0) := by
    first | exact superpose ef3931 ef17 | exact superpose ef17 ef3931
  have ef18277 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef2963 ef939 | exact superpose ef939 ef2963
  have ef21403 (X0 X1 X2 X3 : G) : X3 ◇ (dl X2 (X0 ◇ X1)) = X2 ◇ (dl X0 (X3 ◇ X1)) := by
    first | exact superpose ef3402 ef3402
  have ef21437 (X0 X1 X2 : G) : X2 ◇ (wf X1 X0) = (X1 ◇ X1) ◇ (dl X2 (dr X0 X1)) := by
    first | exact superpose ef3446 ef3402 | exact superpose ef3402 ef3446
  have ef21630 (X0 X1 X2 : G) : X2 ◇ (wf X1 X0) = (X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef121 ef21437 | exact superpose ef21437 ef121
  have ef24040 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (wf X0 X1) := by
    first | exact superpose ef3738 ef154 | exact superpose ef154 ef3738
  have ef33866 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = dr ((X2 ◇ (dr X5 (dl X0 X1))) ◇ X5) (dl X3 X4) := by
    first | exact superpose ef190 ef236 | exact superpose ef236 ef190
  have ef33898 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ (dr X0 X1) = dr (dl X1 (dl X0 X2)) (dl X3 X4) := by
    first | exact superpose ef1428 ef236 | exact superpose ef236 ef1428
  have ef34006 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X4) ◇ (dr X0 (dl X1 X2)) = (X3 ◇ ((X5 ◇ X1) ◇ X2)) ◇ (X4 ◇ (X0 ◇ X5)) := by
    first | exact superpose ef236 ef128 | exact superpose ef128 ef236
  have ef34108 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X4) ◇ (dr X0 (dl X1 X2)) = X5 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X5 ◇ X1) ◇ X2)))) := by
    first | exact superpose ef925 ef34006 | exact superpose ef34006 ef925
  have ef34205 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ (dr X0 X1) = (dl X0 X2) ◇ (dr (dl X3 X4) X1) := by
    first | exact superpose ef1453 ef33898 | exact superpose ef33898 ef1453
  have ef34237 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = (dl (dl X3 X4) (X5 ◇ X2)) ◇ (dr X5 (dl X0 X1)) := by
    first | exact superpose ef1440 ef33866 | exact superpose ef33866 ef1440
  have ef34498 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ (dr X0 X1) = (dl X0 X2) ◇ (X4 ◇ (dr X1 X3)) := by
    first | exact superpose ef1453 ef34205 | exact superpose ef34205 ef1453
  have ef34525 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr (dl X3 X4) (dl X0 X1)) = (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 := by
    first | exact superpose ef1509 ef34237 | exact superpose ef34237 ef1509
  have ef34754 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (dr (dl X0 X1) X3)) := by
    first | exact superpose ef1453 ef34525 | exact superpose ef34525 ef1453
  have ef34913 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (X1 ◇ (dr X3 X0))) := by
    first | exact superpose ef1453 ef34754 | exact superpose ef34754 ef1453
  have ef35275 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = dl (((dr X1 (dr X2 X1)) ◇ X0) ◇ X1) X3 := by
    first | exact superpose ef89 ef5931 | exact superpose ef5931 ef89
  have ef35404 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = (X3 ◇ (dl X0 X1)) ◇ (dr X1 (dr X2 X1)) := by
    first | exact superpose ef285 ef35275 | exact superpose ef35275 ef285
  have ef35492 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (dr ((dr X1 (dr X2 X1)) ◇ X3) X0) := by
    first | exact superpose ef4401 ef35404 | exact superpose ef35404 ef4401
  have ef35563 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (dr ((X1 ◇ (X1 ◇ X2)) ◇ X3) X0) := by
    first | exact superpose ef98 ef35492 | exact superpose ef35492 ef98
  have ef35608 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ ((dl X0 (X3 ◇ X1)) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef1440 ef35563 | exact superpose ef35563 ef1440
  have ef35636 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (dr X0 (dl (X1 ◇ X2) X3))) := by
    first | exact superpose ef5538 ef35608 | exact superpose ef35608 ef5538
  have ef35653 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (dr X0 (X2 ◇ (dr X1 X3)))) := by
    first | exact superpose ef620 ef35636 | exact superpose ef35636 ef620
  have ef35661 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (((dr X1 X3) ◇ X0) ◇ X2)) := by
    first | exact superpose ef44 ef35653 | exact superpose ef35653 ef44
  have ef35664 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (dl X0 X2)))) := by
    first | exact superpose ef797 ef35661 | exact superpose ef35661 ef797
  have ef35666 (X0 X1 X2 X3 : G) : dl (dr X3 (wf X1 X2)) X0 = wf X1 (X3 ◇ (dl X0 X2)) := by
    first | exact superpose ef976 ef35664 | exact superpose ef35664 ef976
  have ef35931 (X0 X1 X2 X3 X4 : G) :
      dr ((X2 ◇ (X3 ◇ X1)) ◇ X0) X4 = dl (X4 ◇ (dl X0 X1)) (dr X2 X3) := by
    first | exact superpose ef266 ef295 | exact superpose ef295 ef266
  have ef35972 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = dr ((X2 ◇ (X3 ◇ X1)) ◇ X0) X4 := by
    first | exact superpose ef121 ef35931 | exact superpose ef35931 ef121
  have ef36239 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = (dl X4 (X0 ◇ X2)) ◇ (X3 ◇ X1) := by
    first | exact superpose ef1440 ef35972 | exact superpose ef35972 ef1440
  have ef36475 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr X4 (dl (X3 ◇ X1) X0)) = X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) := by
    first | exact superpose ef5538 ef36239 | exact superpose ef36239 ef5538
  have ef36669 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr X4 (X1 ◇ (dr X3 X0))) = X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) := by
    first | exact superpose ef620 ef36475 | exact superpose ef36475 ef620
  have ef36812 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = X2 ◇ (((dr X3 X0) ◇ X4) ◇ X1) := by
    first | exact superpose ef44 ef36669 | exact superpose ef36669 ef44
  have ef36903 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = X2 ◇ (X3 ◇ (X0 ◇ (dl X4 X1))) := by
    first | exact superpose ef797 ef36812 | exact superpose ef36812 ef797
  have ef42179 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (dr X4 X5) = X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) := by
    first | exact superpose ef277 ef271 | exact superpose ef271 ef277
  have ef42194 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) = X1 ◇ (X3 ◇ (X0 ◇ (dr X2 (dr X4 X5)))) := by
    first | exact superpose ef34913 ef42179 | exact superpose ef42179 ef34913
  have ef42375 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) = X1 ◇ (X3 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X4)))) := by
    first | exact superpose ef98 ef42194 | exact superpose ef42194 ef98
  have ef51286 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ (dr X2 X0)) ◇ X3) ◇ X4 = (dl X0 X1) ◇ (X3 ◇ (dl X2 X4)) := by
    first | exact superpose ef187 ef311 | exact superpose ef311 ef187
  have ef52712 (X0 X1 : G) : (q ◇ q) ◇ (X0 ◇ X1) = ((X1 ◇ (dr t q)) ◇ X0) ◇ (wf p t) := by
    first | exact superpose ef8493 ef129 | exact superpose ef129 ef8493
  have ef52829 (X0 X1 : G) : (q ◇ q) ◇ (X0 ◇ X1) = (dl q X1) ◇ (X0 ◇ (dl t (wf p t))) := by
    first | exact superpose ef51286 ef52712 | exact superpose ef52712 ef51286
  have ef52912 (X0 X1 : G) : (q ◇ q) ◇ (X0 ◇ X1) = (dl q X1) ◇ (X0 ◇ (p ◇ (p ◇ p))) := by
    first | exact superpose ef24040 ef52829 | exact superpose ef52829 ef24040
  have ef52975 (X0 X1 : G) : (q ◇ q) ◇ (X0 ◇ X1) = (p ◇ p) ◇ (X0 ◇ (p ◇ (dl q X1))) := by
    first | exact superpose ef925 ef52912 | exact superpose ef52912 ef925
  have ef53020 (X0 X1 : G) : (q ◇ q) ◇ (X0 ◇ X1) = (dl q X1) ◇ (wf p X0) := by
    first | exact superpose ef21630 ef52975 | exact superpose ef52975 ef21630
  have ef53242 (X0 X1 X2 : G) : dl (X0 ◇ (dr X2 X2)) X2 = (wf X2 X1) ◇ (dr X0 X1) := by
    first | exact superpose ef101 ef328 | exact superpose ef328 ef101
  have ef53526 (X0 X1 X2 : G) : (wf X2 X1) ◇ (dr X0 X1) = (dr X2 X2) ◇ (dr X0 X2) := by
    first | exact superpose ef620 ef53242 | exact superpose ef53242 ef620
  have ef57903 (X0 : G) : X0 ◇ (dl t (wf p t)) = dl (q ◇ X0) (dr q q) := by
    first | exact superpose ef8578 ef74 | exact superpose ef74 ef8578
  have ef58045 (X0 : G) : X0 ◇ (dl t (wf p t)) = q ◇ (q ◇ (q ◇ X0)) := by
    first | exact superpose ef121 ef57903 | exact superpose ef57903 ef121
  have ef58142 (X0 : G) : wf q X0 = X0 ◇ (dl t (wf p t)) := by
    first | exact superpose ef976 ef58045 | exact superpose ef58045 ef976
  have ef58223 (X0 : G) : wf q X0 = X0 ◇ (p ◇ (p ◇ p)) := by
    first | exact superpose ef24040 ef58142 | exact superpose ef58142 ef24040
  have ef58284 (X0 : G) : wf q X0 = wf p X0 := by
    first | exact superpose ef10220 ef58223 | exact superpose ef58223 ef10220
  have ef60632 (X0 : G) : q ◇ (dr q X0) = wf p (X0 ◇ q) := by
    first | exact superpose ef58284 ef84 | exact superpose ef84 ef58284
  have ef69200 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = dr X4 (dl (X1 ◇ (dl X3 X2)) X5) := by
    first | exact superpose ef311 ef579 | exact superpose ef579 ef311
  have ef69554 (X0 X1 X2 X3 X4 : G) :
      (dr X0 (dl X1 X2)) ◇ (wf (X2 ◇ X3) X4) = (((X3 ◇ X1) ◇ X0) ◇ X4) ◇
      (dr (X2 ◇ X3) (X2 ◇ X3)) := by
    first | exact superpose ef579 ef334 | exact superpose ef334 ef579
  have ef69683 (X0 X1 X2 X3 X4 : G) :
      (dr X0 (dl X1 X2)) ◇ (wf (X2 ◇ X3) X4) = X1 ◇
      (X4 ◇ (X3 ◇ (dr X0 (dr (X2 ◇ X3) (X2 ◇ X3))))) := by
    first | exact superpose ef34913 ef69554 | exact superpose ef69554 ef34913
  have ef70015 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = dr X4 ((dl X3 X2) ◇ (dr X1 X5)) := by
    first | exact superpose ef620 ef69200 | exact superpose ef69200 ef620
  have ef70114 (X0 X1 X2 X3 X4 : G) :
      (dr X0 (dl X1 X2)) ◇ (wf (X2 ◇ X3) X4) = X1 ◇
      (X4 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X3))))) := by
    first | exact superpose ef98 ef69683 | exact superpose ef69683 ef98
  have ef70396 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = ((dr X1 X5) ◇ X4) ◇ (dl X3 X2) := by
    first | exact superpose ef44 ef70015 | exact superpose ef70015 ef44
  have ef70484 (X0 X1 X2 X3 X4 : G) :
      (dr X0 (dl X1 X2)) ◇ (wf (X2 ◇ X3) X4) = X1 ◇
      (X4 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))))) := by
    first | exact superpose ef42375 ef70114 | exact superpose ef70114 ef42375
  have ef70708 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = X1 ◇ (X5 ◇ (dl X4 (dl X3 X2))) := by
    first | exact superpose ef797 ef70396 | exact superpose ef70396 ef797
  have ef70778 (X0 X1 X2 X3 X4 : G) :
      (dr X0 (dl X1 X2)) ◇ (wf (X2 ◇ X3) X4) = X1 ◇ (X4 ◇ (wf X3 (X2 ◇ (X2 ◇ X0)))) := by
    first | exact superpose ef976 ef70484 | exact superpose ef70484 ef976
  have ef70942 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef3266 ef70708 | exact superpose ef70708 ef3266
  have ef70990 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ (wf X3 (X2 ◇ (X2 ◇ X0)))) = X1 ◇ (dl (dr X0 (wf (X2 ◇ X3) X4)) X2) := by
    first | exact superpose ef18277 ef70778 | exact superpose ef70778 ef18277
  have ef71107 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ (X0 ◇ (dr X2 (X5 ◇ (X0 ◇ X3))))) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef34913 ef70942 | exact superpose ef70942 ef34913
  have ef71138 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ (wf X3 (X2 ◇ (X2 ◇ X0)))) = X1 ◇ (wf (X2 ◇ X3) (X0 ◇ (dl X2 X4))) := by
    first | exact superpose ef35666 ef70990 | exact superpose ef70990 ef35666
  have ef71212 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ (X0 ◇ (((X0 ◇ X3) ◇ X2) ◇ X5))) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef44 ef71107 | exact superpose ef71107 ef44
  have ef71276 (X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ (dl X5 (dl X3 X2))) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef274 ef71212 | exact superpose ef71212 ef274
  have ef71322 (X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ ((dl X2 X5) ◇ X3)) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef3266 ef71276 | exact superpose ef71276 ef3266
  have ef71603 (X0 X1 : G) : wf X1 (X0 ◇ (X0 ◇ X0)) = X1 ◇ (X1 ◇ (wf X0 X1)) := by
    first | exact superpose ef10220 ef976 | exact superpose ef976 ef10220
  have ef81316 : dr (q ◇ (q ◇ q)) (q ◇ (q ◇ q)) = wf (wf p t) (wf t (q ◇ (q ◇ q))) := by
    first | exact superpose ef8883 ef10365 | exact superpose ef10365 ef8883
  have ef81369 : dr (q ◇ (q ◇ q)) (q ◇ (q ◇ q)) = wf (wf p t) (t ◇ (t ◇ (wf q t))) := by
    first | exact superpose ef71603 ef81316 | exact superpose ef81316 ef71603
  have ef81479 : dr (q ◇ (q ◇ q)) (q ◇ (q ◇ q)) = wf (wf p t) (t ◇ (t ◇ (wf p t))) := by
    first | exact superpose ef21 ef81369 | exact superpose ef81369 ef21
  have ef81566 : dr (q ◇ (q ◇ q)) (q ◇ (q ◇ q)) = (wf p t) ◇ ((wf p t) ◇ (dr t t)) := by
    first | exact superpose ef8071 ef81479 | exact superpose ef81479 ef8071
  have ef81635 : dr (q ◇ (q ◇ q)) (q ◇ (q ◇ q)) = (wf p t) ◇ ((dr p p) ◇ (dr t p)) := by
    first | exact superpose ef53526 ef81566 | exact superpose ef81566 ef53526
  have ef81692 : (p ◇ (dr p p)) ◇ p = dr (q ◇ (q ◇ q)) (q ◇ (q ◇ q)) := by
    first | exact superpose ef10219 ef81635 | exact superpose ef81635 ef10219
  have ef81741 : (p ◇ (dr p p)) ◇ p = (q ◇ (q ◇ (q ◇ (q ◇ q)))) ◇ q := by
    first | exact superpose ef1511 ef81692 | exact superpose ef81692 ef1511
  have ef81778 : (p ◇ (dr p p)) ◇ p = dl (dr (q ◇ q) q) q := by
    first | exact superpose ef440 ef81741 | exact superpose ef81741 ef440
  have ef81809 : (p ◇ (dr p p)) ◇ p = (wf q (q ◇ q)) ◇ q := by
    first | exact superpose ef3684 ef81778 | exact superpose ef81778 ef3684
  have ef81834 : (p ◇ (dr p p)) ◇ p = (wf p (q ◇ q)) ◇ q := by
    first | exact superpose ef58284 ef81809 | exact superpose ef81809 ef58284
  have ef81853 : (p ◇ (dr p p)) ◇ p = (q ◇ (dr q q)) ◇ q := by
    first | exact superpose ef60632 ef81834 | exact superpose ef81834 ef60632
  have ef81869 : dl q q = (p ◇ (dr p p)) ◇ p := by
    first | exact superpose ef187 ef81853 | exact superpose ef81853 ef187
  have ef81882 : dl q q = dl p p := by
    first | exact superpose ef187 ef81869 | exact superpose ef81869 ef187
  have ef83521 : q = q ◇ (dl p p) := by
    first | exact superpose ef81882 ef18 | exact superpose ef18 ef81882
  have ef83522 : q = dr q (dl p p) := by
    first | exact superpose ef81882 ef23 | exact superpose ef23 ef81882
  have ef83590 : q = dr p (dl p q) := by
    first | exact superpose ef5497 ef83522 | exact superpose ef83522 ef5497
  have ef83591 : q = p ◇ (dl q p) := by
    first | exact superpose ef939 ef83521 | exact superpose ef83521 ef939
  have ef85988 (X0 : G) : dl p X0 = (dl p q) ◇ (dr q X0) := by
    first | exact superpose ef83590 ef777 | exact superpose ef777 ef83590
  have ef90443 (X0 : G) : p = (wf (X0 ◇ p) (dl q p)) ◇ (((X0 ◇ (X0 ◇ p)) ◇ q) ◇ X0) := by
    first | exact superpose ef83591 ef97 | exact superpose ef97 ef83591
  have ef90604 (X0 : G) : p = (dl q X0) ◇ (dl (wf (X0 ◇ p) (dl q p)) (X0 ◇ (X0 ◇ p))) := by
    first | exact superpose ef5956 ef90443 | exact superpose ef90443 ef5956
  have ef90690 (X0 : G) : p = X0 ◇ (dl (dl q X0) ((wf (X0 ◇ p) (dl q p)) ◇ (X0 ◇ p))) := by
    first | exact superpose ef21403 ef90604 | exact superpose ef90604 ef21403
  have ef90751 (X0 : G) : p = X0 ◇ (X0 ◇ ((dr p (wf (X0 ◇ p) (dl q p))) ◇ (dl q X0))) := by
    first | exact superpose ef439 ef90690 | exact superpose ef90690 ef439
  have ef90791 (X0 : G) : p = X0 ◇ (X0 ◇ (q ◇ (dl (dr p (wf (X0 ◇ p) (dl q p))) X0))) := by
    first | exact superpose ef36903 ef90751 | exact superpose ef90751 ef36903
  have ef90813 (X0 : G) : p = X0 ◇ (X0 ◇ (q ◇ (wf (X0 ◇ p) (p ◇ (dl X0 (dl q p)))))) := by
    first | exact superpose ef35666 ef90791 | exact superpose ef90791 ef35666
  have ef90827 (X0 : G) : p = X0 ◇ (X0 ◇ (q ◇ ((dl q p) ◇ (wf p (X0 ◇ (X0 ◇ p)))))) := by
    first | exact superpose ef71138 ef90813 | exact superpose ef90813 ef71138
  have ef90838 (X0 : G) : p = X0 ◇ (X0 ◇ (p ◇ ((dl q q) ◇ (wf p (X0 ◇ (X0 ◇ p)))))) := by
    first | exact superpose ef71322 ef90827 | exact superpose ef90827 ef71322
  have ef90846 (X0 : G) : p = X0 ◇ (X0 ◇ (p ◇ ((q ◇ q) ◇ ((X0 ◇ (X0 ◇ p)) ◇ q)))) := by
    first | exact superpose ef53020 ef90838 | exact superpose ef90838 ef53020
  have ef90852 (X0 : G) : p = ((q ◇ q) ◇ X0) ◇ (dr p (dl (X0 ◇ p) q)) := by
    first | exact superpose ef34108 ef90846 | exact superpose ef90846 ef34108
  have ef90857 (X0 : G) : p = (dl p q) ◇ (X0 ◇ (dr (dl (X0 ◇ p) q) q)) := by
    first | exact superpose ef34498 ef90852 | exact superpose ef90852 ef34498
  have ef90861 (X0 : G) : p = (dl p q) ◇ (X0 ◇ (q ◇ (dr q (X0 ◇ p)))) := by
    first | exact superpose ef1453 ef90857 | exact superpose ef90857 ef1453
  have ef90863 (X0 : G) : p = (dl p q) ◇ (X0 ◇ (q ◇ ((p ◇ q) ◇ X0))) := by
    first | exact superpose ef44 ef90861 | exact superpose ef90861 ef44
  have ef90864 : p = (dl p q) ◇ (dr q (p ◇ q)) := by
    first | exact superpose ef27 ef90863 | exact superpose ef90863 ef27
  have ef90865 : p = dl p (p ◇ q) := by
    first | exact superpose ef85988 ef90864 | exact superpose ef90864 ef85988
  have ef90866 : p = q := by
    first | exact superpose ef19 ef90865 | exact superpose ef90865 ef19
  subsumption ef90866 ef22

/-- Left translation of `x □ y := (x◇(x/(y/x)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_6L [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef31 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef92 (X0 X1 : G) : dr X0 (dr X1 X0) = dl X0 (wf X0 X1) := by
    first | exact superpose ef20 ef19 | exact superpose ef19 ef20
  have ef98 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef219 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef14 ef31 | exact superpose ef31 ef14
  have ef1023 : dr t (dr q t) = dl t (wf t p) := by
    first | exact superpose ef21 ef92 | exact superpose ef92 ef21
  have ef1035 : dr t (dr q t) = dr t (dr p t) := by
    first | exact superpose ef92 ef1023 | exact superpose ef1023 ef92
  have ef1038 : dr t (dr q t) = t ◇ (t ◇ p) := by
    first | exact superpose ef98 ef1035 | exact superpose ef1035 ef98
  have ef1039 : t ◇ (t ◇ p) = t ◇ (t ◇ q) := by
    first | exact superpose ef98 ef1038 | exact superpose ef1038 ef98
  have ef8884 : q = (dl (t ◇ (t ◇ p)) t) ◇ t := by
    first | exact superpose ef1039 ef219 | exact superpose ef219 ef1039
  have ef8972 : p = q := by
    first | exact superpose ef219 ef8884 | exact superpose ef8884 ef219
  subsumption ef8972 ef22

/-- The operation comes back: `x ◇ y = ((y◇(y◇y))◇x)` read in `□` and its divisions, where
`x □ y := (x◇(x/(y/x)))`. With `winj898_6` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back898_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wf (wf y (wf y y)) x) = x ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef16 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef19 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef22 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef24 (X0 X1 : G) : wf (wdr X0 X1) X1 = X0 := mod_symm (hwrs ..)
  have ef25 (X0 X1 : G) : wdr (wf X0 X1) X1 = X0 := mod_symm (hwri ..)
  have ef26 (X0 X1 : G) : wf X0 (wdl X0 X1) = X1 := mod_symm (hwls ..)
  have ef27 (X0 X1 : G) : wdl X0 (wf X0 X1) = X1 := mod_symm (hwli ..)
  have ef28 : wf (wf y (wf y y)) x ≠ x ◇ y := mod_symm nh
  have ef29 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef21 ef20 | exact superpose ef20 ef21
  have ef32 (X0 X1 : G) : wdl (wdr X0 X1) X0 = X1 := by
    first | exact superpose ef24 ef27 | exact superpose ef27 ef24
  have ef33 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef34 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef36 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef37 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef40 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef46 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef50 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef71 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef73 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef19 ef18 | exact superpose ef18 ef19
  have ef74 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef82 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef94 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef20 ef23 | exact superpose ef23 ef20
  have ef98 (X0 X1 X2 : G) : ((dr X0 (dr X1 X0)) ◇ (X2 ◇ (wf X0 X1))) ◇ X0 = X2 := by
    first | exact superpose ef23 ef17 | exact superpose ef17 ef23
  have ef99 (X0 X1 X2 : G) : (((dr X0 (dr X1 X0)) ◇ X2) ◇ X0) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef101 (X0 X1 : G) : dr (wf X0 X1) (dr X0 (dr X1 X0)) = X0 := by
    first | exact superpose ef23 ef20 | exact superpose ef20 ef23
  have ef102 (X0 X1 : G) : dr X0 (dr X1 X0) = dl X0 (wf X0 X1) := by
    first | exact superpose ef23 ef22 | exact superpose ef22 ef23
  have ef110 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef19 ef33 | exact superpose ef33 ef19
  have ef111 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef21 ef33 | exact superpose ef33 ef21
  have ef113 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef33 ef33
  have ef115 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef17 ef33 | exact superpose ef33 ef17
  have ef133 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef33 ef22 | exact superpose ef22 ef33
  have ef141 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef50 ef115 | exact superpose ef115 ef50
  have ef158 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef34 ef33 | exact superpose ef33 ef34
  have ef166 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef34 ef22 | exact superpose ef22 ef34
  have ef168 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ ((dl X0 X3) ◇ (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef34 ef18 | exact superpose ef18 ef34
  have ef186 (X0 X1 : G) : (dr X1 X0) ◇ ((wf X0 X1) ◇ X0) = X0 := by
    first | exact superpose ef23 ef36 | exact superpose ef36 ef23
  have ef231 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef37 | exact superpose ef37 ef17
  have ef247 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef37 ef22 | exact superpose ef22 ef37
  have ef248 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef37 ef33 | exact superpose ef33 ef37
  have ef283 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef18 ef40 | exact superpose ef40 ef18
  have ef286 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef37 ef40 | exact superpose ef40 ef37
  have ef289 (X0 X1 X2 X3 : G) : dl (X0 ◇ (X1 ◇ X3)) X2 = (X2 ◇ X3) ◇ (dr X0 X1) := by
    first | exact superpose ef33 ef40 | exact superpose ef40 ef33
  have ef292 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (dr X0 (dr X1 X0)) X2 := by
    first | exact superpose ef23 ef40 | exact superpose ef40 ef23
  have ef294 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef18 ef40 | exact superpose ef40 ef18
  have ef307 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef40 ef33 | exact superpose ef33 ef40
  have ef313 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef40 ef18 | exact superpose ef18 ef40
  have ef316 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef40 ef22 | exact superpose ef22 ef40
  have ef317 (X0 X1 X2 X3 : G) : dr X3 (X1 ◇ X2) = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef40 ef33 | exact superpose ef33 ef40
  have ef323 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef50 ef317 | exact superpose ef317 ef50
  have ef326 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef248 ef313 | exact superpose ef313 ef248
  have ef335 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (X0 ◇ (X0 ◇ X1)) X2 := by
    first | exact superpose ef110 ef292 | exact superpose ef292 ef110
  have ef346 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (dr X0 X0) := by
    first | exact superpose ef289 ef335 | exact superpose ef335 ef289
  have ef449 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef46 ef33 | exact superpose ef33 ef46
  have ef461 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef50 ef449 | exact superpose ef449 ef50
  have ef590 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef18 ef50 | exact superpose ef50 ef18
  have ef606 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef248 ef590 | exact superpose ef590 ef248
  have ef632 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef71 ef46 | exact superpose ef46 ef71
  have ef732 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef73 ef33 | exact superpose ef33 ef73
  have ef735 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ ((X2 ◇ X0) ◇ (dr X3 X2))) ◇ X0 := by
    first | exact superpose ef73 ef40 | exact superpose ef40 ef73
  have ef758 (X1 X2 X3 : G) : dl X3 X1 = dl ((dr X3 X2) ◇ X2) X1 := by
    first | exact superpose ef294 ef735 | exact superpose ef735 ef294
  have ef761 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef50 ef732 | exact superpose ef732 ef50
  have ef789 (X1 X2 X3 : G) : dl X3 X1 = X2 ◇ (dr (dr X3 X2) X1) := by
    first | exact superpose ef632 ef758 | exact superpose ef758 ef632
  have ef809 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef33 ef74 | exact superpose ef74 ef33
  have ef828 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef74 ef40 | exact superpose ef40 ef74
  have ef857 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef294 ef828 | exact superpose ef828 ef294
  have ef879 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef632 ef857 | exact superpose ef857 ef632
  have ef895 (X0 X1 X2 X3 : G) : X1 ◇ X2 = dl (X0 ◇ X1) ((X0 ◇ (dr X3 X2)) ◇ X3) := by
    first | exact superpose ef36 ef82 | exact superpose ef82 ef36
  have ef904 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef46 ef82 | exact superpose ef82 ef46
  have ef906 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef37 ef82 | exact superpose ef82 ef37
  have ef936 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef283 ef906 | exact superpose ef906 ef283
  have ef937 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef133 ef904 | exact superpose ef904 ef133
  have ef946 (X0 X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef283 ef895 | exact superpose ef895 ef283
  have ef951 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef936 | exact superpose ef936 ef40
  have ef954 (X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef946 | exact superpose ef946 ef40
  have ef968 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef73 ef94 | exact superpose ef94 ef73
  have ef974 (X0 X1 : G) : X1 ◇ X0 = wdl X0 (X0 ◇ (dr X0 X1)) := by
    first | exact superpose ef94 ef27 | exact superpose ef27 ef94
  have ef975 (X0 X1 : G) : wdr (X0 ◇ (dr X0 X1)) (X1 ◇ X0) = X0 := by
    first | exact superpose ef94 ef25 | exact superpose ef25 ef94
  have ef979 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef50 ef968 | exact superpose ef968 ef50
  have ef990 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef761 ef979 | exact superpose ef979 ef761
  have ef999 (X0 X1 : G) : dr X0 (dr X1 (dr (wdl X1 X0) X1)) = X1 := by
    first | exact superpose ef26 ef101 | exact superpose ef101 ef26
  have ef1019 (X0 X1 : G) : (dr (wdl X1 X0) X1) ◇ (X0 ◇ X1) = X1 := by
    first | exact superpose ef110 ef999 | exact superpose ef999 ef110
  have ef1040 (X0 X1 : G) : dl X1 X0 = dr X1 (dr (wdl X1 X0) X1) := by
    first | exact superpose ef26 ef102 | exact superpose ef102 ef26
  have ef1052 (X0 X1 : G) : dl X1 X0 = X1 ◇ (X1 ◇ (wdl X1 X0)) := by
    first | exact superpose ef110 ef1040 | exact superpose ef1040 ef110
  have ef1773 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef18 ef111 | exact superpose ef111 ef18
  have ef1774 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef40 ef111 | exact superpose ef111 ef40
  have ef1777 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef19 ef111 | exact superpose ef111 ef19
  have ef1788 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef111 ef33 | exact superpose ef33 ef111
  have ef1852 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef951 ef1774 | exact superpose ef1774 ef951
  have ef1884 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef247 ef1852 | exact superpose ef1852 ef247
  have ef1897 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef33 ef1884 | exact superpose ef1884 ef33
  have ef2844 (X0 X1 X2 : G) :
      wf X1 X0 = X1 ◇ (dr X1 ((dr X1 (dr X2 X1)) ◇ (X0 ◇ (wf X1 X2)))) := by
    first | exact superpose ef98 ef94 | exact superpose ef94 ef98
  have ef2878 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((X0 ◇ (wf X1 X2)) ◇ X1) ◇ (dr X1 (dr X2 X1))) := by
    first | exact superpose ef50 ef2844 | exact superpose ef2844 ef50
  have ef2933 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((X0 ◇ (wf X1 X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := by
    first | exact superpose ef110 ef2878 | exact superpose ef2878 ef110
  have ef2975 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (wf X1 X2)) ◇ X1)))) := by
    first | exact superpose ef937 ef2933 | exact superpose ef2933 ef937
  have ef3007 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (X2 ◇ (dr X1 (X0 ◇ (wf X1 X2)))) := by
    first | exact superpose ef33 ef2975 | exact superpose ef2975 ef33
  have ef3027 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (X2 ◇ (((wf X1 X2) ◇ X1) ◇ X0)) := by
    first | exact superpose ef50 ef3007 | exact superpose ef3007 ef50
  have ef3062 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef33 ef158 | exact superpose ef158 ef33
  have ef3120 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef158 ef36 | exact superpose ef36 ef158
  have ef3172 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1897 ef3062 | exact superpose ef3062 ef1897
  have ef3207 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef50 ef3172 | exact superpose ef3172 ef50
  have ef3224 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef111 ef3207 | exact superpose ef3207 ef111
  have ef3246 (X0 X1 : G) : dr X1 X0 = (X0 ◇ X0) ◇ (wf X0 X1) := by
    first | exact superpose ef19 ef99 | exact superpose ef99 ef19
  have ef3480 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef71 ef166 | exact superpose ef166 ef71
  have ef3504 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef166 ef22 | exact superpose ef22 ef166
  have ef3585 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef632 ef3480 | exact superpose ef3480 ef632
  have ef3618 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1788 ef3585 | exact superpose ef3585 ef1788
  have ef3642 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef879 ef3618 | exact superpose ef3618 ef879
  have ef4224 (X0 X1 : G) : dr (dr X1 X0) (wf X0 X1) = X0 ◇ X0 := by
    first | exact superpose ef186 ef33 | exact superpose ef33 ef186
  have ef4290 (X0 X1 : G) : X0 ◇ X0 = (dl (wf X0 X1) X0) ◇ X1 := by
    first | exact superpose ef1777 ef4224 | exact superpose ef4224 ef1777
  have ef5181 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) (dl X1 X2) = dr ((X0 ◇ X1) ◇ X2) X3 := by
    first | exact superpose ef37 ef307 | exact superpose ef307 ef37
  have ef5263 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) (dl X1 X2) = (dl X3 (X2 ◇ X0)) ◇ X1 := by
    first | exact superpose ef1773 ef5181 | exact superpose ef5181 ef1773
  have ef5308 (X0 X1 X2 X3 : G) : (dl X3 (X2 ◇ X0)) ◇ X1 = (dl X2 (X3 ◇ X0)) ◇ X1 := by
    first | exact superpose ef3504 ef5263 | exact superpose ef5263 ef3504
  have ef5538 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef326 ef82 | exact superpose ef82 ef326
  have ef5559 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3504 ef5538 | exact superpose ef5538 ef3504
  have ef6090 (X0 X1 X2 : G) : dr X1 X2 = dr X0 (dl (dr X0 X2) X1) := by
    first | exact superpose ef19 ef606 | exact superpose ef606 ef19
  have ef8090 (X0 X1 : G) : (dl X0 X1) ◇ X1 = wdl X1 (X1 ◇ X0) := by
    first | exact superpose ef29 ef974 | exact superpose ef974 ef29
  have ef8128 (X0 X1 : G) : wdr (X1 ◇ X0) ((dl X0 X1) ◇ X1) = X1 := by
    first | exact superpose ef29 ef975 | exact superpose ef975 ef29
  have ef8408 (X0 X1 : G) : X0 ◇ (wf X0 X1) = wf X0 (X0 ◇ X1) := by
    first | exact superpose ef990 ef990
  have ef8412 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef990 ef33 | exact superpose ef33 ef990
  have ef8413 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef990 ef17 | exact superpose ef17 ef990
  have ef8416 (X0 X1 : G) : (wf X0 X1) ◇ (dr (X0 ◇ X1) X0) = X0 := by
    first | exact superpose ef990 ef46 | exact superpose ef46 ef990
  have ef8808 (X0 X1 : G) : X0 ◇ X0 = dr (dr (wdl X0 X1) X0) X1 := by
    first | exact superpose ef1019 ef33 | exact superpose ef33 ef1019
  have ef8818 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ X0) = dr X2 (dr (wdl X0 X1) X0) := by
    first | exact superpose ef1019 ef33 | exact superpose ef33 ef1019
  have ef8820 (X0 X1 X2 : G) : X0 ◇ ((X1 ◇ X0) ◇ X2) = dl X2 (dr (wdl X0 X1) X0) := by
    first | exact superpose ef1019 ef40 | exact superpose ef40 ef1019
  have ef8882 (X0 X1 X2 : G) : X0 ◇ ((X1 ◇ X0) ◇ X2) = (wdl X0 X1) ◇ (X0 ◇ X2) := by
    first | exact superpose ef133 ef8820 | exact superpose ef8820 ef133
  have ef8884 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ X0) = X0 ◇ (X2 ◇ (wdl X0 X1)) := by
    first | exact superpose ef110 ef8818 | exact superpose ef8818 ef110
  have ef8892 (X0 X1 : G) : X0 ◇ X0 = (dl X1 X0) ◇ (wdl X0 X1) := by
    first | exact superpose ef1777 ef8808 | exact superpose ef8808 ef1777
  have ef9153 (X0 X1 : G) : X1 ◇ X0 = (wf X0 X0) ◇ (dl X1 X0) := by
    first | exact superpose ef8412 ef954 | exact superpose ef954 ef8412
  have ef9202 (X0 X1 : G) : wdl X0 X1 = (dl (dl X0 X1) X0) ◇ X0 := by
    first | exact superpose ef1052 ef231 | exact superpose ef231 ef1052
  have ef9214 (X0 X1 : G) : X0 ◇ (wdl X0 X1) = dl X0 (dl X0 X1) := by
    first | exact superpose ef1052 ef22 | exact superpose ef22 ef1052
  have ef9308 (X0 X1 : G) : X0 ◇ (wdl X0 X1) = (dl X1 X0) ◇ X0 := by
    first | exact superpose ef3504 ef9214 | exact superpose ef9214 ef3504
  have ef9320 (X0 X1 : G) : wdl X0 X1 = ((X0 ◇ X0) ◇ X1) ◇ X0 := by
    first | exact superpose ef247 ef9202 | exact superpose ef9202 ef247
  have ef9375 (X0 X1 : G) : wdl X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := by
    first | exact superpose ef461 ef9320 | exact superpose ef9320 ef461
  have ef9411 (X0 X1 : G) : wdl X0 X1 = (wf X0 X0) ◇ (X1 ◇ X0) := by
    first | exact superpose ef8412 ef9375 | exact superpose ef9375 ef8412
  have ef9533 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8413 ef990 | exact superpose ef990 ef8413
  have ef9559 (X0 : G) : wf (wf X0 X0) X0 = wdl X0 (wf X0 X0) := by
    first | exact superpose ef9411 ef9533 | exact superpose ef9533 ef9411
  have ef9599 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef27 ef9559 | exact superpose ef9559 ef27
  have ef10010 (X0 : G) : wf X0 X0 = wdr X0 X0 := by
    first | exact superpose ef9599 ef25 | exact superpose ef25 ef9599
  have ef10954 (X0 X1 : G) : wf X1 X0 = dl (X1 ◇ X1) (dr X0 X1) := by
    first | exact superpose ef3246 ef22 | exact superpose ef22 ef3246
  have ef11039 (X0 X1 : G) : wf X1 X0 = X0 ◇ (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef133 ef10954 | exact superpose ef10954 ef133
  have ef18291 (X0 X1 : G) : (dr X0 X1) ◇ X0 = (wf X0 X0) ◇ X1 := by
    first | exact superpose ef8412 ef3224 | exact superpose ef3224 ef8412
  have ef21819 (X0 X1 X2 X3 : G) :
      dl X0 ((dr X2 (dr X3 X2)) ◇ X1) = ((X0 ◇ X1) ◇ X2) ◇ (wf X2 X3) := by
    first | exact superpose ef3642 ef99 | exact superpose ef99 ef3642
  have ef21825 (X0 X1 X2 X3 : G) :
      ((X0 ◇ X1) ◇ X2) ◇ (wf X2 X3) = dl X0 ((X2 ◇ (X2 ◇ X3)) ◇ X1) := by
    first | exact superpose ef110 ef21819 | exact superpose ef21819 ef110
  have ef21936 (X0 X1 X2 X3 : G) :
      ((X0 ◇ X1) ◇ X2) ◇ (wf X2 X3) = (X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0) := by
    first | exact superpose ef283 ef21825 | exact superpose ef21825 ef283
  have ef22137 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) ◇ X0 = (wf X0 X0) ◇ (X1 ◇ X2) := by
    first | exact superpose ef8413 ef141 | exact superpose ef141 ef8413
  have ef24279 (X0 X1 X2 X3 : G) :
      (X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0) = dr (dl (wf X0 (dr X1 X2)) X0) X3 := by
    first | exact superpose ef4290 ef113 | exact superpose ef113 ef4290
  have ef24294 (X0 X1 X2 X3 : G) :
      (X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0) = X0 ◇ (dr X3 (wf X0 (dr X1 X2))) := by
    first | exact superpose ef1788 ef24279 | exact superpose ef24279 ef1788
  have ef24610 (X0 X1 X2 X3 : G) :
      wf X1 X0 = X2 ◇ ((X3 ◇ ((dl X2 X3) ◇ (dr X0 X1))) ◇ (X1 ◇ X1)) := by
    first | exact superpose ef3246 ef168 | exact superpose ef168 ef3246
  have ef24928 (X0 X1 X2 X3 : G) :
      wf X1 X0 = X2 ◇ (X1 ◇ (dr (dr X0 X1) (wf X1 (dr X3 (dl X2 X3))))) := by
    first | exact superpose ef24294 ef24610 | exact superpose ef24610 ef24294
  have ef25119 (X0 X1 X2 X3 : G) : wf X1 X0 = X2 ◇ (dl X0 (wf X1 (dr X3 (dl X2 X3)))) := by
    first | exact superpose ef789 ef24928 | exact superpose ef24928 ef789
  have ef25268 (X0 X1 X2 : G) : wf X1 X0 = X2 ◇ (dl X0 (wf X1 X2)) := by
    first | exact superpose ef29 ef25119 | exact superpose ef25119 ef29
  have ef37269 (X0 X1 X2 : G) : (dl (dr X2 X1) X0) ◇ X2 = wdl X2 (X2 ◇ (dr X0 X1)) := by
    first | exact superpose ef6090 ef974 | exact superpose ef974 ef6090
  have ef37302 (X0 X1 X2 : G) : (dl (dr X2 X1) X0) ◇ X2 = (dl (dr X0 X1) X2) ◇ X2 := by
    first | exact superpose ef8090 ef37269 | exact superpose ef37269 ef8090
  have ef37362 (X0 X1 X2 : G) : (dl (dr X2 X1) X0) ◇ X2 = X2 ◇ (wdl X2 (dr X0 X1)) := by
    first | exact superpose ef9308 ef37302 | exact superpose ef37302 ef9308
  have ef37395 (X0 X1 X2 : G) : X1 ◇ ((dr X2 X0) ◇ X2) = X2 ◇ (wdl X2 (dr X0 X1)) := by
    first | exact superpose ef3120 ef37362 | exact superpose ef37362 ef3120
  have ef50321 (X0 X1 : G) :
      wf X0 X1 = wdr X0 ((dl (dr (X0 ◇ X1) X0) (wf X0 X1)) ◇ (wf X0 X1)) := by
    first | exact superpose ef8416 ef8128 | exact superpose ef8128 ef8416
  have ef50324 (X0 X1 : G) :
      wf X0 X1 = wdr X0 ((wf X0 X1) ◇ (wdl (wf X0 X1) (dr (X0 ◇ X1) X0))) := by
    first | exact superpose ef9308 ef50321 | exact superpose ef50321 ef9308
  have ef50492 (X0 X1 : G) : wf X0 X1 = wdr X0 (X0 ◇ ((dr (wf X0 X1) (X0 ◇ X1)) ◇ (wf X0 X1))) := by
    first | exact superpose ef37395 ef50324 | exact superpose ef50324 ef37395
  have ef50629 (X0 X1 : G) : wf X0 X1 = wdr X0 (X0 ◇ ((wf (wf X0 X1) (wf X0 X1)) ◇ (X0 ◇ X1))) := by
    first | exact superpose ef18291 ef50492 | exact superpose ef50492 ef18291
  have ef50735 (X0 X1 : G) : wf X0 X1 = wdr X0 (X0 ◇ (((X1 ◇ (wf X0 X1)) ◇ X0) ◇ (wf X0 X1))) := by
    first | exact superpose ef22137 ef50629 | exact superpose ef50629 ef22137
  have ef50820 (X0 X1 : G) : wf X0 X1 = wdr X0 (X0 ◇ ((X0 ◇ X1) ◇ (((wf X0 X1) ◇ X0) ◇ X1))) := by
    first | exact superpose ef21936 ef50735 | exact superpose ef50735 ef21936
  have ef50887 (X0 X1 : G) : wf X0 X1 = wdr X0 (X0 ◇ (X1 ◇ (((wf X0 X1) ◇ X0) ◇ (wdl X1 X0)))) := by
    first | exact superpose ef8884 ef50820 | exact superpose ef50820 ef8884
  have ef50939 (X0 X1 : G) : wf X0 X1 = wdr X0 (wf X0 (wdl X1 X0)) := by
    first | exact superpose ef3027 ef50887 | exact superpose ef50887 ef3027
  have ef54213 (X0 X1 X2 X3 : G) :
      ((dr (wdl X0 X1) X0) ◇ X2) ◇ X3 = X0 ◇ (X2 ◇ (dl (X1 ◇ X0) X3)) := by
    first | exact superpose ef1019 ef323 | exact superpose ef323 ef1019
  have ef54701 (X0 X1 X2 X3 : G) :
      ((dr (wdl X0 X1) X0) ◇ X2) ◇ X3 = X0 ◇ (X2 ◇ (X0 ◇ (dr X1 X3))) := by
    first | exact superpose ef632 ef54213 | exact superpose ef54213 ef632
  have ef54949 (X0 X1 X2 X3 : G) :
      X0 ◇ (X2 ◇ (X0 ◇ (dr X1 X3))) = (wdl X0 X1) ◇ (X0 ◇ (dl X2 X3)) := by
    first | exact superpose ef809 ef54701 | exact superpose ef54701 ef809
  have ef55151 (X0 X1 X2 X3 : G) :
      X0 ◇ (X2 ◇ (X0 ◇ (dr X1 X3))) = X0 ◇ ((X1 ◇ X0) ◇ (dl X2 X3)) := by
    first | exact superpose ef8882 ef54949 | exact superpose ef54949 ef8882
  have ef60733 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = dl (X0 ◇ X0) (dl X2 (dl X1 X0)) := by
    first | exact superpose ef8892 ef316 | exact superpose ef316 ef8892
  have ef60798 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = (dl (dl X1 X0) (X0 ◇ X0)) ◇ X2 := by
    first | exact superpose ef3504 ef60733 | exact superpose ef60733 ef3504
  have ef60903 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = (dl X0 ((dl X1 X0) ◇ X0)) ◇ X2 := by
    first | exact superpose ef5308 ef60798 | exact superpose ef60798 ef5308
  have ef60986 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = X0 ◇ (dr X0 (dl X2 (dl X1 X0))) := by
    first | exact superpose ef5559 ef60903 | exact superpose ef60903 ef5559
  have ef61052 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = X0 ◇ (dr X0 ((dl X0 X2) ◇ X1)) := by
    first | exact superpose ef3504 ef60986 | exact superpose ef60986 ef3504
  have ef61099 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = X0 ◇ ((X1 ◇ X0) ◇ (dl X0 X2)) := by
    first | exact superpose ef50 ef61052 | exact superpose ef61052 ef50
  have ef61131 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = X0 ◇ (X0 ◇ (X0 ◇ (dr X1 X2))) := by
    first | exact superpose ef55151 ef61099 | exact superpose ef61099 ef55151
  have ef61153 (X0 X1 X2 : G) : (wdl X0 X1) ◇ X2 = wf X0 (dr X1 X2) := by
    first | exact superpose ef990 ef61131 | exact superpose ef61131 ef990
  have ef74756 (X0 X1 X2 X3 : G) :
      dl X2 (dl (X0 ◇ (X0 ◇ X0)) X3) = X1 ◇ (((wf X0 X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef11039 ef286 | exact superpose ef286 ef11039
  have ef74963 (X0 X1 X2 X3 : G) :
      X1 ◇ (((wf X0 X1) ◇ X3) ◇ X2) = (dl X3 X2) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef3504 ef74756 | exact superpose ef74756 ef3504
  have ef75217 (X0 X1 X2 X3 : G) : wf X0 (dl X3 X2) = X1 ◇ (((wf X0 X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef11039 ef74963 | exact superpose ef74963 ef11039
  have ef93591 (X0 X1 X2 : G) : X1 ◇ (dl X2 X0) = wf (wdr X0 X1) X2 := by
    first | exact superpose ef24 ef25268 | exact superpose ef25268 ef24
  have ef93726 (X0 X1 X2 : G) : wf X2 (wf X0 X1) = X2 ◇ (wf X2 (dl X1 (wf X0 X2))) := by
    first | exact superpose ef25268 ef8408 | exact superpose ef8408 ef25268
  have ef152138 (X0 X1 X2 : G) :
      wf X0 (dr X2 X2) = X0 ◇ (X1 ◇ (((wf X0 X1) ◇ X2) ◇ (wf X2 X0))) := by
    first | exact superpose ef346 ef3027 | exact superpose ef3027 ef346
  have ef152782 (X0 X2 : G) : wf X0 (dr X2 X2) = X0 ◇ (wf X0 (dl X2 (wf X2 X0))) := by
    first | exact superpose ef75217 ef152138 | exact superpose ef152138 ef75217
  have ef153108 (X0 X2 : G) : wf X0 (wf X2 X2) = wf X0 (dr X2 X2) := by
    first | exact superpose ef93726 ef152782 | exact superpose ef152782 ef93726
  have ef153386 (X0 X2 : G) : wf X0 (wf X2 X2) = (wdl X0 X2) ◇ X2 := by
    first | exact superpose ef61153 ef153108 | exact superpose ef153108 ef61153
  have ef154342 : x ◇ y ≠ wf ((wdl y y) ◇ y) x := by
    first | exact superpose ef153386 ef28 | exact superpose ef28 ef153386
  have ef228673 (X0 X1 : G) : wf X1 (wdr X1 X0) = wdr X1 (wf X1 X0) := by
    first | exact superpose ef32 ef50939 | exact superpose ef50939 ef32
  have ef285602 (X0 X1 X2 : G) : wdr X2 X0 = wdr (X0 ◇ (dl X1 X2)) X1 := by
    first | exact superpose ef93591 ef25 | exact superpose ef25 ef93591
  have ef372964 (X0 X1 : G) : wdr (X0 ◇ X1) X0 = wdr X1 (wf X1 X1) := by
    first | exact superpose ef9153 ef285602 | exact superpose ef285602 ef9153
  have ef372998 (X0 X1 : G) : wdr (X0 ◇ X1) X0 = wf X1 (wdr X1 X1) := by
    first | exact superpose ef228673 ef372964 | exact superpose ef372964 ef228673
  have ef373047 (X0 X1 : G) : wf X1 (wf X1 X1) = wdr (X0 ◇ X1) X0 := by
    first | exact superpose ef10010 ef372998 | exact superpose ef372998 ef10010
  have ef373061 (X0 X1 : G) : (wdl X1 X1) ◇ X1 = wdr (X0 ◇ X1) X0 := by
    first | exact superpose ef153386 ef373047 | exact superpose ef373047 ef153386
  have ef389238 (X0 X1 : G) : X1 ◇ X0 = wf ((wdl X0 X0) ◇ X0) X1 := by
    first | exact superpose ef373061 ef24 | exact superpose ef24 ef373061
  have ef397703 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef389238 ef154342 | exact superpose ef154342 ef389238
  exact absurd rfl ef397703

/-- Equation 23 `x = (x ◇ x) ◇ x` holds of the operation `x □ y := (x◇(x/(y/x)))` in every magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the divisions that law
forces. -/
private theorem qaux898_23_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    x = wf (wf x x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf (wf x x) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef172 (X0 X1 : G) : (dr X1 X0) ◇ ((wf X0 X1) ◇ X0) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8062 (X0 X1 : G) : wf (dr X0 X1) X1 = (dr X0 X1) ◇ ((dr X0 X1) ◇ X0) := by
    first | exact superpose ef15 ef974 | exact superpose ef974 ef15
  have ef8081 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef974 ef23 | exact superpose ef23 ef974
  have ef8765 (X0 : G) : (dr X0 X0) ◇ ((dr X0 X0) ◇ X0) = X0 := by
    first | exact superpose ef8081 ef172 | exact superpose ef172 ef8081
  have ef8772 : x ≠ wf (dr x x) x := by
    first | exact superpose ef8081 ef20 | exact superpose ef20 ef8081
  have ef8779 (X0 : G) : wf (dr X0 X0) X0 = X0 := by
    first | exact superpose ef8062 ef8765 | exact superpose ef8765 ef8062
  have ef9816 : x ≠ x := by
    first | exact superpose ef8779 ef8772 | exact superpose ef8772 ef8779
  exact absurd rfl ef9816

theorem Equation23_termStructuralFromFin_Equation898_qdiv :
    Law23.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law23.models_iff]
    exact fun x ↦
      @qaux898_23_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_1629_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    x = wf (wf x x) (wf (wf x x) x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf (wf x x) (wf (wf x x) x) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : x ≠ wf (wf x x) x := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  subsumption ef9610 ef9311

theorem Equation1629_termStructuralFromFin_Equation898_qdiv :
    Law1629.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1629.models_iff]
    exact fun x ↦
      @qaux898_1629_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

set_option maxHeartbeats 1600000 in
/-- Equation 1832 `x = (x ◇ (x ◇ x)) ◇ (x ◇ x)` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_1832_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    x = wf (wf x (wf x x)) (wf x x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf (wf x (wf x x)) (wf x x) := mod_symm nh
  have ef21 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef17 ef16 | exact superpose ef16 ef17
  have ef22 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef15 ef18 | exact superpose ef18 ef15
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef37 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef64 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef67 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef14 ef14
  have ef69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef70 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef85 (X0 X1 X2 : G) : (dr X0 (dr X1 X0)) ◇ ((X2 ◇ X0) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef86 (X0 X1 X2 : G) : ((dr X0 (dr X1 X0)) ◇ (X2 ◇ (wf X0 X1))) ◇ X0 = X2 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef87 (X0 X1 X2 : G) : (((dr X0 (dr X1 X0)) ◇ X2) ◇ X0) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef89 (X0 X1 : G) : dr (wf X0 X1) (dr X0 (dr X1 X0)) = X0 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef91 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((dr (X0 ◇ X1) (dr X2 (X0 ◇ X1))) ◇ X0) = X1 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef92 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ ((dr (X0 ◇ X1) ((X1 ◇ X2) ◇ X0)) ◇ X0) = X1 := by
    first | exact superpose ef40 ef91 | exact superpose ef91 ef40
  have ef95 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X0) = X1 := by
    first | exact superpose ef40 ef92 | exact superpose ef92 ef40
  have ef96 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef97 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef99 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef23 ef23
  have ef100 (X0 X1 X2 : G) : dr X2 X0 = (dr X0 (dr X1 X0)) ◇ (X2 ◇ (wf X0 X1)) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef101 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef13 ef23 | exact superpose ef23 ef13
  have ef102 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef14 ef23 | exact superpose ef23 ef14
  have ef105 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef23
  have ef114 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (dr X0 X1)) = X3 := by
    first | exact superpose ef23 ef12 | exact superpose ef12 ef23
  have ef119 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef120 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef126 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef40 ef102 | exact superpose ef102 ef40
  have ef127 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef40 ef101 | exact superpose ef101 ef40
  have ef144 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef152 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef154 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ ((dl X0 X3) ◇ (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef24 ef14 | exact superpose ef14 ef24
  have ef172 (X0 X1 : G) : (dr X1 X0) ◇ ((wf X0 X1) ◇ X0) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef185 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef26 ef18 | exact superpose ef18 ef26
  have ef188 (X0 X1 X2 X3 : G) : ((X0 ◇ (dr X1 (dl X2 X3))) ◇ X1) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef26 ef24 | exact superpose ef24 ef26
  have ef217 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef13 ef27 | exact superpose ef27 ef13
  have ef224 (X0 X1 X2 : G) :
      (dl X1 (dr (X0 ◇ X1) (dr X2 (X0 ◇ X1)))) ◇ (wf (X0 ◇ X1) X2) = X0 := by
    first | exact superpose ef19 ef27 | exact superpose ef27 ef19
  have ef233 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef234 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef242 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((dr X2 (X0 ◇ X1)) ◇ X1)) ◇ (wf (X0 ◇ X1) X2) = X0 := by
    first | exact superpose ef119 ef224 | exact superpose ef224 ef119
  have ef256 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (wf (X0 ◇ X1) X2) = X0 := by
    first | exact superpose ef40 ef242 | exact superpose ef242 ef40
  have ef264 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef267 (X0 X1 X2 : G) : dl X2 X0 = (wf X0 X1) ◇ ((dr X0 (dr X1 X0)) ◇ X2) := by
    first | exact superpose ef19 ef30 | exact superpose ef30 ef19
  have ef269 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef270 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef30 ef30
  have ef272 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef275 (X0 X1 X2 X3 : G) : dl (X0 ◇ (X1 ◇ X3)) X2 = (X2 ◇ X3) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef278 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (dr X0 (dr X1 X0)) X2 := by
    first | exact superpose ef19 ef30 | exact superpose ef30 ef19
  have ef280 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef283 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef293 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef298 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1))) ◇ (X1 ◇ X2) = X3 := by
    first | exact superpose ef30 ef13 | exact superpose ef13 ef30
  have ef299 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef30 ef14 | exact superpose ef14 ef30
  have ef302 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef30 ef18 | exact superpose ef18 ef30
  have ef303 (X0 X1 X2 X3 : G) : dr X3 (X1 ◇ X2) = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef309 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef40 ef303 | exact superpose ef303 ef40
  have ef312 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef234 ef299 | exact superpose ef299 ef234
  have ef313 (X0 X1 X3 : G) : dr X1 (dl X0 (X3 ◇ (dl X0 X1))) = X3 := by
    first | exact superpose ef234 ef298 | exact superpose ef298 ef234
  have ef321 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (X0 ◇ (X0 ◇ X1)) X2 := by
    first | exact superpose ef96 ef278 | exact superpose ef278 ef96
  have ef326 (X0 X1 X2 : G) : dl X2 X0 = (wf X0 X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    first | exact superpose ef96 ef267 | exact superpose ef267 ef96
  have ef332 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (dr X0 X0) := by
    first | exact superpose ef275 ef321 | exact superpose ef321 ef275
  have ef430 (X0 X1 X2 X3 : G) : ((dr X1 X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef36 ef13 | exact superpose ef13 ef36
  have ef435 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef36 ef23 | exact superpose ef23 ef36
  have ef437 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef438 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef447 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef40 ef435 | exact superpose ef435 ef40
  have ef504 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((dl X1 X3) ◇ (X0 ◇ X3)) := by
    first | exact superpose ef37 ef23 | exact superpose ef23 ef37
  have ef511 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef37 ef27 | exact superpose ef27 ef37
  have ef532 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ X3) ◇ X2) ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef504 | exact superpose ef504 ef40
  have ef573 (X0 X1 X2 : G) : ((dr X0 (dr X1 X0)) ◇ X2) ◇ X0 = dr X2 (wf X0 X1) := by
    first | exact superpose ef19 ef40 | exact superpose ef40 ef19
  have ef576 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef14 ef40 | exact superpose ef40 ef14
  have ef577 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2) = dr X3 (dl X0 X1) := by
    first | exact superpose ef30 ef40 | exact superpose ef40 ef30
  have ef578 (X0 X1 X2 X3 : G) : ((dr X1 X2) ◇ X3) ◇ (X2 ◇ (X0 ◇ X1)) = dr X3 X0 := by
    first | exact superpose ef36 ef40 | exact superpose ef40 ef36
  have ef592 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef234 ef576 | exact superpose ef576 ef234
  have ef595 (X0 X1 X2 : G) : dr X2 (wf X0 X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0 := by
    first | exact superpose ef96 ef573 | exact superpose ef573 ef96
  have ef601 (X0 X1 X2 : G) : dr X2 (wf X0 X1) = (dr (X0 ◇ X1) X0) ◇ (X2 ◇ X0) := by
    first | exact superpose ef447 ef595 | exact superpose ef595 ef447
  have ef618 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef721 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ ((X2 ◇ X0) ◇ (dr X3 X2))) ◇ X0 := by
    first | exact superpose ef63 ef30 | exact superpose ef30 ef63
  have ef730 (X0 X1 X2 X3 : G) : X0 ◇ (dr X3 ((X1 ◇ X0) ◇ (dr (X2 ◇ X3) X1))) = X2 := by
    first | exact superpose ef63 ef36 | exact superpose ef36 ef63
  have ef737 (X0 X1 X2 X3 : G) : X0 ◇ (((dr (X2 ◇ X3) X1) ◇ X3) ◇ (X1 ◇ X0)) = X2 := by
    first | exact superpose ef40 ef730 | exact superpose ef730 ef40
  have ef744 (X1 X2 X3 : G) : dl X3 X1 = dl ((dr X3 X2) ◇ X2) X1 := by
    first | exact superpose ef280 ef721 | exact superpose ef721 ef280
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef771 (X1 X2 X3 : G) : dr ((dr (X2 ◇ X3) X1) ◇ X3) X1 = X2 := by
    first | exact superpose ef23 ef737 | exact superpose ef737 ef23
  have ef775 (X1 X2 X3 : G) : dl X3 X1 = X2 ◇ (dr (dr X3 X2) X1) := by
    first | exact superpose ef618 ef744 | exact superpose ef744 ef618
  have ef795 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef23 ef64 | exact superpose ef64 ef23
  have ef799 (X0 X1 X2 : G) :
      dr (dl X0 X1) (dr X2 (dl X0 X1)) = ((wf (dl X0 X1) X2) ◇ X0) ◇ X1 := by
    first | exact superpose ef19 ef64 | exact superpose ef64 ef19
  have ef811 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (((dl X3 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef64 ef23 | exact superpose ef23 ef64
  have ef814 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef64 ef30 | exact superpose ef30 ef64
  have ef843 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef280 ef814 | exact superpose ef814 ef280
  have ef846 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((dl X3 X1) ◇ X0) := by
    first | exact superpose ef40 ef811 | exact superpose ef811 ef40
  have ef854 (X0 X1 X2 : G) : ((wf (dl X0 X1) X2) ◇ X0) ◇ X1 = (dl X0 X1) ◇ ((dl X0 X1) ◇ X2) := by
    first | exact superpose ef96 ef799 | exact superpose ef799 ef96
  have ef865 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef618 ef843 | exact superpose ef843 ef618
  have ef881 (X0 X1 X2 X3 : G) : X1 ◇ X2 = dl (X0 ◇ X1) ((X0 ◇ (dr X3 X2)) ◇ X3) := by
    first | exact superpose ef26 ef72 | exact superpose ef72 ef26
  have ef890 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef892 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef902 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2 = dl (dr X0 X1) X3 := by
    first | exact superpose ef23 ef72 | exact superpose ef72 ef23
  have ef903 (X0 X1 X2 X3 : G) : dl X0 X3 = (X1 ◇ ((dl X0 X1) ◇ (X2 ◇ X3))) ◇ X2 := by
    first | exact superpose ef24 ef72 | exact superpose ef72 ef24
  have ef918 (X0 X1 X3 : G) : dl X0 X3 = dl (dr X3 (dl X0 X1)) X1 := by
    first | exact superpose ef438 ef903 | exact superpose ef903 ef438
  have ef922 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef269 ef892 | exact superpose ef892 ef269
  have ef923 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef119 ef890 | exact superpose ef890 ef119
  have ef932 (X0 X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef269 ef881 | exact superpose ef881 ef269
  have ef937 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef922 | exact superpose ef922 ef30
  have ef940 (X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef932 | exact superpose ef932 ef30
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef984 (X0 X1 : G) : dl X0 X1 = dr (wf (dl X0 X1) X1) (dr (dl X0 X1) X0) := by
    first | exact superpose ef21 ef89 | exact superpose ef89 ef21
  have ef998 (X0 X1 : G) : dl X0 X1 = X0 ◇ ((wf (dl X0 X1) X1) ◇ (dl X0 X1)) := by
    first | exact superpose ef96 ef984 | exact superpose ef984 ef96
  have ef1005 (X0 X1 : G) : dl X0 X1 = X0 ◇ (X0 ◇ (dl (wf (dl X0 X1) X1) X1)) := by
    first | exact superpose ef937 ef998 | exact superpose ef998 ef937
  have ef1064 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) ◇ (dl X2 X0) = X3 := by
    first | exact superpose ef17 ef67 | exact superpose ef67 ef17
  have ef1109 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X0) = dr X2 (((X3 ◇ X4) ◇ X0) ◇ ((X4 ◇ X1) ◇ X3)) := by
    first | exact superpose ef67 ef23 | exact superpose ef23 ef67
  have ef1121 (X0 X1 X2 X3 : G) :
      wf X1 X0 = X1 ◇ (dr X1 (((X2 ◇ X3) ◇ X0) ◇ ((X3 ◇ X1) ◇ X2))) := by
    first | exact superpose ef67 ef82 | exact superpose ef82 ef67
  have ef1138 (X0 X1 X2 X3 : G) : wf X1 X0 = X1 ◇ ((((X3 ◇ X1) ◇ X2) ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) := by
    first | exact superpose ef40 ef1121 | exact superpose ef1121 ef40
  have ef1150 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X0) = (((X4 ◇ X1) ◇ X3) ◇ X2) ◇ ((X3 ◇ X4) ◇ X0) := by
    first | exact superpose ef40 ef1109 | exact superpose ef1109 ef40
  have ef1188 (X0 X1 X2 X3 : G) : X2 ◇ (dl (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) X0) = X3 := by
    first | exact superpose ef937 ef1064 | exact superpose ef1064 ef937
  have ef1267 (X0 X1 X2 X3 : G) : X2 ◇ ((X0 ◇ (dl X3 (X0 ◇ X1))) ◇ (X1 ◇ X2)) = X3 := by
    first | exact superpose ef283 ef1188 | exact superpose ef1188 ef283
  have ef1318 (X0 X1 X3 : G) : dr (X0 ◇ (dl X3 (X0 ◇ X1))) X1 = X3 := by
    first | exact superpose ef23 ef1267 | exact superpose ef1267 ef23
  have ef1425 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X3 ◇ ((X1 ◇ X4) ◇ ((dl X1 X2) ◇ (X0 ◇ X2)))) ◇ X4) = X3 := by
    first | exact superpose ef37 ef69 | exact superpose ef69 ef37
  have ef1600 (X0 X1 X2 X3 : G) : X0 ◇ (dl (((dl X1 X2) ◇ (X0 ◇ X2)) ◇ X1) X3) = X3 := by
    first | exact superpose ef280 ef1425 | exact superpose ef1425 ef280
  have ef1656 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ (dl (X0 ◇ X2) X1)) ◇ (dl X1 X2)) = X3 := by
    first | exact superpose ef283 ef1600 | exact superpose ef1600 ef283
  have ef1693 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl (X3 ◇ (dl (X0 ◇ X2) X1)) X2)) = X3 := by
    first | exact superpose ef937 ef1656 | exact superpose ef1656 ef937
  have ef1716 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ ((dl (X0 ◇ X2) X1) ◇ (dr X3 X2))) = X3 := by
    first | exact superpose ef618 ef1693 | exact superpose ef1693 ef618
  have ef1728 (X0 X2 X3 : G) : X0 ◇ (dl (dr X3 X2) (X0 ◇ X2)) = X3 := by
    first | exact superpose ef152 ef1716 | exact superpose ef1716 ef152
  have ef1737 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef17 ef97 | exact superpose ef97 ef17
  have ef1740 (X0 X1 X2 X3 : G) : dr X3 X1 = (dl X1 (X2 ◇ ((dl X0 X2) ◇ X3))) ◇ X0 := by
    first | exact superpose ef24 ef97 | exact superpose ef97 ef24
  have ef1749 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef14 ef97 | exact superpose ef97 ef14
  have ef1750 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef97 | exact superpose ef97 ef30
  have ef1752 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef36 ef97 | exact superpose ef97 ef36
  have ef1753 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef97 | exact superpose ef97 ef15
  have ef1755 (X0 X1 X2 X3 : G) : dr (dl X1 X3) X2 = (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) := by
    first | exact superpose ef97 ef97
  have ef1764 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef97 ef23 | exact superpose ef23 ef97
  have ef1776 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef97 ef23 | exact superpose ef23 ef97
  have ef1824 (X0 X1 X2 X3 : G) : X3 ◇ (dr X2 X1) = (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) := by
    first | exact superpose ef1764 ef1755 | exact superpose ef1755 ef1764
  have ef1826 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef119 ef1752 | exact superpose ef1752 ef119
  have ef1828 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef937 ef1750 | exact superpose ef1750 ef937
  have ef1837 (X0 X1 X2 X3 : G) : dr X3 X1 = ((dl X0 X2) ◇ ((dr X3 X2) ◇ X1)) ◇ X0 := by
    first | exact superpose ef437 ef1740 | exact superpose ef1740 ef437
  have ef1860 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef233 ef1828 | exact superpose ef1828 ef233
  have ef1863 (X1 X2 X3 : G) : dr X3 X1 = dr ((dr X3 X2) ◇ X1) X2 := by
    first | exact superpose ef144 ef1837 | exact superpose ef1837 ef144
  have ef1873 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1860 | exact superpose ef1860 ef23
  have ef1939 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) ◇ (X0 ◇ X1) = X3 := by
    first | exact superpose ef26 ef70 | exact superpose ef70 ef26
  have ef1941 (X0 X1 X2 X3 : G) :
      ((X2 ◇ X0) ◇ (X3 ◇ (dr X0 (dr X1 X0)))) ◇ ((wf X0 X1) ◇ X2) = X3 := by
    first | exact superpose ef19 ef70 | exact superpose ef70 ef19
  have ef1967 (X0 X1 X2 X3 X4 : G) :
      (((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ (X4 ◇ X3)) ◇ (dr X0 X1) = X4 := by
    first | exact superpose ef23 ef70 | exact superpose ef70 ef23
  have ef1985 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = dl ((X1 ◇ X2) ◇ (X0 ◇ X3)) X0 := by
    first | exact superpose ef70 ef18 | exact superpose ef18 ef70
  have ef1988 (X0 X1 X2 X3 X4 : G) :
      dl X4 ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4) := by
    first | exact superpose ef70 ef30 | exact superpose ef30 ef70
  have ef2033 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4) = X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X4) := by
    first | exact superpose ef269 ef1988 | exact superpose ef1988 ef269
  have ef2036 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X0 ◇ (dl X2 (X0 ◇ X3))) ◇ X1 := by
    first | exact superpose ef283 ef1985 | exact superpose ef1985 ef283
  have ef2049 (X0 X1 X2 X3 X4 : G) :
      (dr X2 (dr X0 X1)) ◇ ((X4 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := by
    first | exact superpose ef447 ef1967 | exact superpose ef1967 ef447
  have ef2073 (X0 X1 X3 : G) : dr (wf X0 X1) (dl X0 (X3 ◇ (dr X0 (dr X1 X0)))) = X3 := by
    first | exact superpose ef234 ef1941 | exact superpose ef1941 ef234
  have ef2075 (X0 X2 X3 X4 : G) : dr X0 (dl X2 (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) = X3 := by
    first | exact superpose ef234 ef1939 | exact superpose ef1939 ef234
  have ef2152 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X0)) ◇ ((X4 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := by
    first | exact superpose ef96 ef2049 | exact superpose ef2049 ef96
  have ef2171 (X0 X1 X3 : G) : dr (wf X0 X1) (dl X0 (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := by
    first | exact superpose ef96 ef2073 | exact superpose ef2073 ef96
  have ef2173 (X0 X2 X3 X4 : G) : dr X0 ((X0 ◇ (dr X4 X2)) ◇ ((dr X4 X3) ◇ X2)) = X3 := by
    first | exact superpose ef437 ef2075 | exact superpose ef2075 ef437
  have ef2242 (X0 X1 X3 : G) : dr (wf X0 X1) (X0 ◇ ((dr (X0 ◇ X1) X3) ◇ X0)) = X3 := by
    first | exact superpose ef437 ef2171 | exact superpose ef2171 ef437
  have ef2244 (X0 X2 X3 X4 : G) : (((dr X4 X3) ◇ X2) ◇ X0) ◇ (X0 ◇ (dr X4 X2)) = X3 := by
    first | exact superpose ef40 ef2173 | exact superpose ef2173 ef40
  have ef2287 (X0 X1 X3 : G) : (((dr (X0 ◇ X1) X3) ◇ X0) ◇ (wf X0 X1)) ◇ X0 = X3 := by
    first | exact superpose ef40 ef2242 | exact superpose ef2242 ef40
  have ef2289 (X2 X3 X4 : G) : dl (dr X4 X2) ((dr X4 X3) ◇ X2) = X3 := by
    first | exact superpose ef30 ef2244 | exact superpose ef2244 ef30
  have ef2312 (X0 X1 X3 : G) : (dr X0 X0) ◇ ((wf X0 X1) ◇ (dr (X0 ◇ X1) X3)) = X3 := by
    first | exact superpose ef447 ef2287 | exact superpose ef2287 ef447
  have ef2372 (X0 X1 X2 X3 : G) : dl X3 (X2 ◇ X0) = (dr X0 X1) ◇ ((dr X1 X2) ◇ X3) := by
    first | exact superpose ef105 ef30 | exact superpose ef30 ef105
  have ef2586 (X0 X1 X2 X3 : G) :
      X1 ◇ (dr X2 (dr X3 X2)) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ (wf X2 X3)) := by
    first | exact superpose ef85 ef72 | exact superpose ef72 ef85
  have ef2593 (X0 X1 X2 X3 : G) :
      X1 ◇ (dr X2 (dr X3 X2)) = X2 ◇ (((wf X2 X3) ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef269 ef2586 | exact superpose ef2586 ef269
  have ef2656 (X1 X2 X3 : G) : X1 ◇ (dr X2 (dr X3 X2)) = X2 ◇ (dl X1 (wf X2 X3)) := by
    first | exact superpose ef30 ef2593 | exact superpose ef2593 ef30
  have ef2703 (X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X2 ◇ X3)) = X2 ◇ (dl X1 (wf X2 X3)) := by
    first | exact superpose ef96 ef2656 | exact superpose ef2656 ef96
  have ef2812 (X0 X1 X2 : G) :
      wf X1 X0 = X1 ◇ (dr X1 ((dr X1 (dr X2 X1)) ◇ (X0 ◇ (wf X1 X2)))) := by
    first | exact superpose ef86 ef82 | exact superpose ef82 ef86
  have ef2846 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((X0 ◇ (wf X1 X2)) ◇ X1) ◇ (dr X1 (dr X2 X1))) := by
    first | exact superpose ef40 ef2812 | exact superpose ef2812 ef40
  have ef2899 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((X0 ◇ (wf X1 X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := by
    first | exact superpose ef96 ef2846 | exact superpose ef2846 ef96
  have ef2939 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (wf X1 X2)) ◇ X1)))) := by
    first | exact superpose ef923 ef2899 | exact superpose ef2899 ef923
  have ef2969 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (X2 ◇ (dr X1 (X0 ◇ (wf X1 X2)))) := by
    first | exact superpose ef23 ef2939 | exact superpose ef2939 ef23
  have ef2989 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (X2 ◇ (((wf X1 X2) ◇ X1) ◇ X0)) := by
    first | exact superpose ef40 ef2969 | exact superpose ef2969 ef40
  have ef3024 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef23 ef144 | exact superpose ef144 ef23
  have ef3042 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef144 ef23 | exact superpose ef23 ef144
  have ef3044 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ (X2 ◇ X3) = dl X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef144 ef30 | exact superpose ef30 ef144
  have ef3063 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dr X0 X1) = dr ((dl X3 X1) ◇ X0) X2 := by
    first | exact superpose ef144 ef97 | exact superpose ef97 ef144
  have ef3082 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef144 ef26 | exact superpose ef26 ef144
  have ef3121 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef40 ef3042 | exact superpose ef3042 ef40
  have ef3134 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1873 ef3024 | exact superpose ef3024 ef1873
  have ef3169 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef40 ef3134 | exact superpose ef3134 ef40
  have ef3186 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef97 ef3169 | exact superpose ef3169 ef97
  have ef3208 (X0 X1 : G) : dr X1 X0 = (X0 ◇ X0) ◇ (wf X0 X1) := by
    first | exact superpose ef15 ef87 | exact superpose ef87 ef15
  have ef3248 (X0 X1 X2 X3 : G) :
      dr (wf X1 X2) X3 = X0 ◇ (dr X3 (((dr X1 (dr X2 X1)) ◇ X0) ◇ X1)) := by
    first | exact superpose ef87 ef105 | exact superpose ef105 ef87
  have ef3263 (X0 X1 X2 X3 : G) :
      dr (wf X1 X2) X3 = X0 ◇ ((X1 ◇ X3) ◇ ((dr X1 (dr X2 X1)) ◇ X0)) := by
    first | exact superpose ef40 ef3248 | exact superpose ef3248 ef40
  have ef3313 (X1 X2 X3 : G) : dr (wf X1 X2) X3 = dr (X1 ◇ X3) (dr X1 (dr X2 X1)) := by
    first | exact superpose ef23 ef3263 | exact superpose ef3263 ef23
  have ef3355 (X1 X2 X3 : G) : dr (wf X1 X2) X3 = (dr X2 X1) ◇ ((X1 ◇ X3) ◇ X1) := by
    first | exact superpose ef96 ef3313 | exact superpose ef3313 ef96
  have ef3434 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef61 ef152 | exact superpose ef152 ef61
  have ef3458 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef152 ef18 | exact superpose ef18 ef152
  have ef3539 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef618 ef3434 | exact superpose ef3434 ef618
  have ef3572 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1764 ef3539 | exact superpose ef3539 ef1764
  have ef3596 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef865 ef3572 | exact superpose ef3572 ef865
  have ef3697 (X0 X1 : G) : (wf (X1 ◇ X0) (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0 = X0 := by
    first | exact superpose ef13 ef95 | exact superpose ef95 ef13
  have ef3701 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2) = X0 ◇ (dr X1 (wf (X1 ◇ X0) X2)) := by
    first | exact superpose ef95 ef36 | exact superpose ef36 ef95
  have ef3766 (X0 X1 X2 : G) : X0 ◇ (dr X1 (wf (X1 ◇ X0) X2)) = (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2) := by
    first | exact superpose ef126 ef3701 | exact superpose ef3701 ef126
  have ef3770 (X0 X1 : G) : (wf (X1 ◇ X0) (wf X1 X0)) ◇ X0 = X0 := by
    first | exact superpose ef974 ef3697 | exact superpose ef3697 ef974
  have ef4172 (X0 X1 : G) : dr (dr X1 X0) (wf X0 X1) = X0 ◇ X0 := by
    first | exact superpose ef172 ef23 | exact superpose ef23 ef172
  have ef4180 (X0 X1 : G) : (wf X0 X1) ◇ X0 = dl (dr X1 X0) X0 := by
    first | exact superpose ef172 ef18 | exact superpose ef18 ef172
  have ef4238 (X0 X1 : G) : X0 ◇ X0 = (dl (wf X0 X1) X0) ◇ X1 := by
    first | exact superpose ef1753 ef4172 | exact superpose ef4172 ef1753
  have ef4335 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (X2 ◇ X3) = dl X3 (X1 ◇ (dr X2 X0)) := by
    first | exact superpose ef185 ef30 | exact superpose ef30 ef185
  have ef4352 (X0 X1 X2 : G) : X2 ◇ (dr X2 (X1 ◇ (dr X2 X0))) = wf X2 (dl X0 X1) := by
    first | exact superpose ef185 ef82 | exact superpose ef82 ef185
  have ef4370 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef185 ef13 | exact superpose ef13 ef185
  have ef4374 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X3 X2) X0) = X2 ◇ ((dl X0 X1) ◇ X3) := by
    first | exact superpose ef185 ef26 | exact superpose ef26 ef185
  have ef4377 (X0 X1 X2 X3 : G) : X2 ◇ ((dl X0 X1) ◇ X3) = X1 ◇ ((dl X0 X2) ◇ X3) := by
    first | exact superpose ef1753 ef4374 | exact superpose ef4374 ef1753
  have ef4393 (X0 X1 X2 : G) : wf X2 (dl X0 X1) = X2 ◇ (((dr X2 X0) ◇ X2) ◇ X1) := by
    first | exact superpose ef40 ef4352 | exact superpose ef4352 ef40
  have ef4444 (X0 X1 X2 : G) : wf X2 (dl X0 X1) = X2 ◇ (X2 ◇ (X0 ◇ (dl X2 X1))) := by
    first | exact superpose ef795 ef4393 | exact superpose ef4393 ef795
  have ef4554 (X0 X1 X2 X3 : G) : (dl X0 X2) ◇ ((X1 ◇ X0) ◇ (dr (X2 ◇ X3) X1)) = X3 := by
    first | exact superpose ef63 ef217 | exact superpose ef217 ef63
  have ef4657 (X1 X2 X3 : G) : dl (dr (X2 ◇ X3) X1) (X2 ◇ X1) = X3 := by
    first | exact superpose ef270 ef4554 | exact superpose ef4554 ef270
  have ef5129 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) (dl X1 X2) = dr ((X0 ◇ X1) ◇ X2) X3 := by
    first | exact superpose ef27 ef293 | exact superpose ef293 ef27
  have ef5141 (X0 X1 X2 X3 : G) : dr X1 ((X1 ◇ X2) ◇ (X0 ◇ X3)) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef70 ef293 | exact superpose ef293 ef70
  have ef5146 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef144 ef293 | exact superpose ef293 ef144
  have ef5196 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef40 ef5146 | exact superpose ef5146 ef40
  have ef5201 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef40 ef5141 | exact superpose ef5141 ef40
  have ef5211 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) (dl X1 X2) = (dl X3 (X2 ◇ X0)) ◇ X1 := by
    first | exact superpose ef1749 ef5129 | exact superpose ef5129 ef1749
  have ef5248 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef618 ef5196 | exact superpose ef5196 ef618
  have ef5251 (X0 X2 X3 : G) : dl X2 (X0 ◇ X3) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef30 ef5201 | exact superpose ef5201 ef30
  have ef5256 (X0 X1 X2 X3 : G) : (dl X3 (X2 ◇ X0)) ◇ X1 = (dl X2 (X3 ◇ X0)) ◇ X1 := by
    first | exact superpose ef3458 ef5211 | exact superpose ef5211 ef3458
  have ef5276 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef30 ef5248 | exact superpose ef5248 ef30
  have ef5486 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef312 ef72 | exact superpose ef72 ef312
  have ef5507 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3458 ef5486 | exact superpose ef5486 ef3458
  have ef5615 (X0 X1 X2 : G) : dl X0 X1 = dl X2 (X0 ◇ (dl X2 X1)) := by
    first | exact superpose ef313 ef22 | exact superpose ef22 ef313
  have ef5750 (X0 X1 X2 X3 : G) : dl X1 X2 = (dl X0 X1) ◇ ((X3 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef63 ef511 | exact superpose ef511 ef63
  have ef5755 (X0 X1 X2 X3 X4 : G) :
      dl X1 ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) = (dl X0 X1) ◇ (X4 ◇ X2) := by
    first | exact superpose ef69 ef511 | exact superpose ef511 ef69
  have ef5810 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dl X0 X1) = dr (dl (X3 ◇ X1) X0) X2 := by
    first | exact superpose ef511 ef97 | exact superpose ef97 ef511
  have ef5851 (X0 X1 X2 X3 : G) : X0 ◇ (dr X2 (X3 ◇ X1)) = (dl X2 X3) ◇ (dl X0 X1) := by
    first | exact superpose ef1764 ef5810 | exact superpose ef5810 ef1764
  have ef5896 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ ((X3 ◇ X0) ◇ X1) = (dl X0 X1) ◇ (X4 ◇ X2) := by
    first | exact superpose ef269 ef5755 | exact superpose ef5755 ef269
  have ef5900 (X1 X2 X3 : G) : dl X1 X2 = dl (dr X2 X3) (X1 ◇ X3) := by
    first | exact superpose ef270 ef5750 | exact superpose ef5750 ef270
  have ef5925 (X0 X1 X2 X3 : G) : X0 ◇ ((X1 ◇ X2) ◇ X3) = (dl X2 X3) ◇ (dl X0 X1) := by
    first | exact superpose ef40 ef5851 | exact superpose ef5851 ef40
  have ef6040 (X0 X1 X2 : G) : dr X1 ((wf X0 X2) ◇ X0) = dr X0 (dl (dr X2 X0) X1) := by
    first | exact superpose ef172 ef592 | exact superpose ef592 ef172
  have ef6106 (X0 X1 X2 : G) : dr X0 (dl (dr X2 X0) X1) = (X0 ◇ X1) ◇ (wf X0 X2) := by
    first | exact superpose ef40 ef6040 | exact superpose ef6040 ef40
  have ef6434 (X0 X1 X2 : G) : X0 ◇ X2 = (dr (X0 ◇ X1) X2) ◇ X1 := by
    first | exact superpose ef771 ef15 | exact superpose ef15 ef771
  have ef8077 (X0 X1 : G) : X0 ◇ (wf X0 X1) = wf X0 (X0 ◇ X1) := by
    first | exact superpose ef974 ef974
  have ef8081 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef974 ef23 | exact superpose ef23 ef974
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef8083 (X0 X1 : G) : dr (X0 ◇ X1) X0 = dl (wf X0 X1) X0 := by
    first | exact superpose ef974 ef293 | exact superpose ef293 ef974
  have ef8085 (X0 X1 : G) : (wf X0 X1) ◇ (dr (X0 ◇ X1) X0) = X0 := by
    first | exact superpose ef974 ef36 | exact superpose ef36 ef974
  have ef8097 (X0 X1 X2 : G) : dr X2 X0 = (X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (wf X0 X1)) := by
    first | exact superpose ef974 ef23 | exact superpose ef23 ef974
  have ef8468 (X0 X1 X2 X3 : G) : dr X1 (dl X0 (X2 ◇ X3)) = dr (X2 ◇ (dl X0 X1)) X3 := by
    first | exact superpose ef918 ef1318 | exact superpose ef1318 ef918
  have ef9646 (X0 X1 : G) : dl (wf X0 X0) ((dr X0 X1) ◇ X0) = X1 := by
    first | exact superpose ef8081 ef2289 | exact superpose ef2289 ef8081
  have ef9848 (X0 X1 : G) : wf X1 X0 = dl (X1 ◇ X1) (dr X0 X1) := by
    first | exact superpose ef3208 ef18 | exact superpose ef18 ef3208
  have ef9929 (X0 X1 : G) : wf X1 X0 = X0 ◇ (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef119 ef9848 | exact superpose ef9848 ef119
  have ef10104 (X0 X1 X2 : G) : (wf (X1 ◇ X0) (wf X1 X0)) ◇ (dl (dr X2 X0) X0) = X2 := by
    first | exact superpose ef3770 ef1728 | exact superpose ef1728 ef3770
  have ef10126 (X0 X1 X2 : G) : (wf (X1 ◇ X0) (wf X1 X0)) ◇ ((wf X0 X2) ◇ X0) = X2 := by
    first | exact superpose ef4180 ef10104 | exact superpose ef10104 ef4180
  have ef13125 (X0 X1 X2 X3 X4 : G) :
      dl ((X0 ◇ X4) ◇ (dr X2 X3)) X1 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef114 ef30 | exact superpose ef30 ef114
  have ef13153 (X0 X1 X2 X3 X4 : G) :
      dr X1 ((X0 ◇ X2) ◇ (dr X3 X4)) = dr X0 (dl (X3 ◇ (X4 ◇ X2)) X1) := by
    first | exact superpose ef114 ef592 | exact superpose ef592 ef114
  have ef13182 (X0 X1 X2 X3 X4 : G) :
      dr X1 ((X0 ◇ X2) ◇ (dr X3 X4)) = dr X0 ((X4 ◇ X2) ◇ (dr X3 X1)) := by
    first | exact superpose ef618 ef13153 | exact superpose ef13153 ef618
  have ef13210 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X1 ◇ (dl X4 (dr X2 X3))) ◇ X0 := by
    first | exact superpose ef283 ef13125 | exact superpose ef13125 ef283
  have ef13388 (X0 X1 X2 X3 X4 : G) :
      dr X1 ((X0 ◇ X2) ◇ (dr X3 X4)) = ((dr X3 X1) ◇ X0) ◇ (X4 ◇ X2) := by
    first | exact superpose ef40 ef13182 | exact superpose ef13182 ef40
  have ef13413 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (dr X2 X3) ◇ (dr (X0 ◇ X1) X4) := by
    first | exact superpose ef4370 ef13210 | exact superpose ef13210 ef4370
  have ef13567 (X0 X1 X2 X3 X4 : G) :
      dr X1 ((X0 ◇ X2) ◇ (dr X3 X4)) = X3 ◇ (X1 ◇ (dl X0 (X4 ◇ X2))) := by
    first | exact superpose ef795 ef13388 | exact superpose ef13388 ef795
  have ef13709 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (X1 ◇ (dl X0 (X4 ◇ X2))) = ((dr X3 X4) ◇ X1) ◇ (X0 ◇ X2) := by
    first | exact superpose ef40 ef13567 | exact superpose ef13567 ef40
  have ef13807 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (X1 ◇ (dl X0 (X4 ◇ X2))) = X3 ◇ (X4 ◇ (dl X1 (X0 ◇ X2))) := by
    first | exact superpose ef795 ef13709 | exact superpose ef13709 ef795
  have ef15316 (X0 X1 X2 X3 : G) : dr (X0 ◇ (dl X1 X2)) X3 = dr (X1 ◇ X3) (dl X0 X2) := by
    first | exact superpose ef937 ef1873 | exact superpose ef1873 ef937
  have ef16863 (X0 X1 : G) : (dr X0 X1) ◇ X0 = (wf X0 X0) ◇ X1 := by
    first | exact superpose ef8081 ef3186 | exact superpose ef3186 ef8081
  have ef17034 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef3186 ef937 | exact superpose ef937 ef3186
  have ef17563 (X0 X1 : G) : (dr X0 X0) ◇ ((wf X0 X1) ◇ X0) = X1 := by
    first | exact superpose ef974 ef120 | exact superpose ef120 ef974
  have ef17662 (X0 X1 X2 X3 X4 : G) :
      dr X1 ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) = dr X0 (dl (dr X2 X3) X1) := by
    first | exact superpose ef120 ef592 | exact superpose ef592 ef120
  have ef17687 (X0 X1 X2 X3 X4 : G) :
      dr X0 (dl (dr X2 X3) X1) = (X4 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))) := by
    first | exact superpose ef40 ef17662 | exact superpose ef17662 ef40
  have ef17780 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X0 X1) ◇ X0) = X1 := by
    first | exact superpose ef8081 ef17563 | exact superpose ef17563 ef8081
  have ef18941 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = dr ((X0 ◇ X2) ◇ X4) (X1 ◇ X3) := by
    first | exact superpose ef126 ef1873 | exact superpose ef1873 ef126
  have ef18972 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = (dl (X1 ◇ X3) (X4 ◇ X0)) ◇ X2 := by
    first | exact superpose ef1749 ef18941 | exact superpose ef18941 ef1749
  have ef19333 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) := by
    first | exact superpose ef5507 ef18972 | exact superpose ef18972 ef5507
  have ef19593 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X2 := by
    first | exact superpose ef1826 ef19333 | exact superpose ef19333 ef1826
  have ef20160 (X0 X1 X2 X3 : G) : X3 ◇ (dl X2 (X0 ◇ X1)) = X2 ◇ (dl X0 (X3 ◇ X1)) := by
    first | exact superpose ef3596 ef3596
  have ef20199 (X0 X1 X2 : G) : (dr X2 X0) ◇ (dl X1 X0) = X1 ◇ ((wf X0 X2) ◇ X0) := by
    first | exact superpose ef172 ef3596 | exact superpose ef3596 ef172
  have ef20260 (X0 X1 X2 X3 X4 : G) :
      dr X2 (dl X0 (X3 ◇ X1)) = (X4 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (dr X4 X3)) := by
    first | exact superpose ef3596 ef99 | exact superpose ef99 ef3596
  have ef20331 (X0 X1 X2 X3 : G) : dr X2 (dl X0 (X3 ◇ X1)) = dr X2 (dl X3 (X0 ◇ X1)) := by
    first | exact superpose ef1776 ef20260 | exact superpose ef20260 ef1776
  have ef20621 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X1 ◇ (dr (X2 ◇ X4) X0))) = ((dl X0 X1) ◇ X3) ◇ X4 := by
    first | exact superpose ef185 ef127 | exact superpose ef127 ef185
  have ef20721 (X0 X1 X2 X3 : G) :
      wf X3 (X0 ◇ (X1 ◇ X2)) = X3 ◇ (dr X3 ((X2 ◇ (X0 ◇ X3)) ◇ X1)) := by
    first | exact superpose ef127 ef82 | exact superpose ef82 ef127
  have ef20864 (X0 X1 X2 X3 : G) :
      wf X3 (X0 ◇ (X1 ◇ X2)) = X3 ◇ ((X1 ◇ X3) ◇ (X2 ◇ (X0 ◇ X3))) := by
    first | exact superpose ef40 ef20721 | exact superpose ef20721 ef40
  have ef21049 (X0 X1 X2 X3 : G) :
      wf X3 (X0 ◇ (X1 ◇ X2)) = X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    first | exact superpose ef923 ef20864 | exact superpose ef20864 ef923
  have ef22683 (X0 X1 X2 X3 : G) :
      (X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0) = dr (dl (wf X0 (dr X1 X2)) X0) X3 := by
    first | exact superpose ef4238 ef99 | exact superpose ef99 ef4238
  have ef22698 (X0 X1 X2 X3 : G) :
      (X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0) = X0 ◇ (dr X3 (wf X0 (dr X1 X2))) := by
    first | exact superpose ef1764 ef22683 | exact superpose ef22683 ef1764
  have ef23008 (X0 X1 X2 X3 : G) :
      wf X1 X0 = X2 ◇ ((X3 ◇ ((dl X2 X3) ◇ (dr X0 X1))) ◇ (X1 ◇ X1)) := by
    first | exact superpose ef3208 ef154 | exact superpose ef154 ef3208
  have ef23318 (X0 X1 X2 X3 : G) :
      wf X1 X0 = X2 ◇ (X1 ◇ (dr (dr X0 X1) (wf X1 (dr X3 (dl X2 X3))))) := by
    first | exact superpose ef22698 ef23008 | exact superpose ef23008 ef22698
  have ef23504 (X0 X1 X2 X3 : G) : wf X1 X0 = X2 ◇ (dl X0 (wf X1 (dr X3 (dl X2 X3)))) := by
    first | exact superpose ef775 ef23318 | exact superpose ef23318 ef775
  have ef23648 (X0 X1 X2 : G) : wf X1 X0 = X2 ◇ (dl X0 (wf X1 X2)) := by
    first | exact superpose ef21 ef23504 | exact superpose ef23504 ef21
  have ef24071 (X0 X1 X2 : G) : dl (dr ((dl (wf X0 X1) X0) ◇ X2) X1) (X0 ◇ X0) = X2 := by
    first | exact superpose ef4238 ef4657 | exact superpose ef4657 ef4238
  have ef24144 (X0 X1 X2 : G) : dl X0 ((dr ((dl (wf X0 X1) X0) ◇ X2) X1) ◇ X0) = X2 := by
    first | exact superpose ef5251 ef24071 | exact superpose ef24071 ef5251
  have ef24284 (X0 X1 X2 : G) : dl X0 (((dl X1 (wf X0 X1)) ◇ (dr X2 X0)) ◇ X0) = X2 := by
    first | exact superpose ef3063 ef24144 | exact superpose ef24144 ef3063
  have ef24392 (X0 X1 X2 : G) : (dr X2 X0) ◇ ((X0 ◇ (dl X1 (wf X0 X1))) ◇ X0) = X2 := by
    first | exact superpose ef269 ef24284 | exact superpose ef24284 ef269
  have ef24465 (X0 X1 X2 : G) : dr (wf X0 X2) (dl X1 (wf X0 X1)) = X2 := by
    first | exact superpose ef3355 ef24392 | exact superpose ef24392 ef3355
  have ef27901 (X0 X1 : G) : (wf X0 X1) ◇ X0 = dl (dr X0 X0) X1 := by
    first | exact superpose ef5276 ef4180 | exact superpose ef4180 ef5276
  have ef27972 (X0 X1 : G) : (wf X0 X1) ◇ X0 = dl (wf X0 X0) X1 := by
    first | exact superpose ef8081 ef27901 | exact superpose ef27901 ef8081
  have ef33353 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = dl (((dr X1 (dr X2 X1)) ◇ X0) ◇ X1) X3 := by
    first | exact superpose ef87 ef5900 | exact superpose ef5900 ef87
  have ef33480 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = (X3 ◇ (dl X0 X1)) ◇ (dr X1 (dr X2 X1)) := by
    first | exact superpose ef283 ef33353 | exact superpose ef33353 ef283
  have ef33567 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (dr ((dr X1 (dr X2 X1)) ◇ X3) X0) := by
    first | exact superpose ef4370 ef33480 | exact superpose ef33480 ef4370
  have ef33636 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (dr ((X1 ◇ (X1 ◇ X2)) ◇ X3) X0) := by
    first | exact superpose ef96 ef33567 | exact superpose ef33567 ef96
  have ef33680 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ ((dl X0 (X3 ◇ X1)) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef1749 ef33636 | exact superpose ef33636 ef1749
  have ef33707 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (dr X0 (dl (X1 ◇ X2) X3))) := by
    first | exact superpose ef5507 ef33680 | exact superpose ef33680 ef5507
  have ef33724 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (dr X0 (X2 ◇ (dr X1 X3)))) := by
    first | exact superpose ef618 ef33707 | exact superpose ef33707 ef618
  have ef33732 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (((dr X1 X3) ◇ X0) ◇ X2)) := by
    first | exact superpose ef40 ef33724 | exact superpose ef33724 ef40
  have ef33736 (X0 X1 X2 X3 : G) :
      dl (dr X3 (wf X1 X2)) X0 = X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (dl X0 X2)))) := by
    first | exact superpose ef795 ef33732 | exact superpose ef33732 ef795
  have ef33738 (X0 X1 X2 X3 : G) : dl (dr X3 (wf X1 X2)) X0 = wf X1 (X3 ◇ (dl X0 X2)) := by
    first | exact superpose ef974 ef33736 | exact superpose ef33736 ef974
  have ef33807 (X0 X1 X2 : G) : dr X2 (dl X0 X1) = (X0 ◇ X1) ◇ (X2 ◇ (wf X0 X0)) := by
    first | exact superpose ef8082 ef234 | exact superpose ef234 ef8082
  have ef33886 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = dr ((X2 ◇ (dr X5 (dl X0 X1))) ◇ X5) (dl X3 X4) := by
    first | exact superpose ef188 ef234 | exact superpose ef234 ef188
  have ef33917 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ (dr X0 X1) = dr (dl X1 (dl X0 X2)) (dl X3 X4) := by
    first | exact superpose ef1737 ef234 | exact superpose ef234 ef1737
  have ef34226 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ (dr X0 X1) = (dl X0 X2) ◇ (dr (dl X3 X4) X1) := by
    first | exact superpose ef1764 ef33917 | exact superpose ef33917 ef1764
  have ef34257 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = (dl (dl X3 X4) (X5 ◇ X2)) ◇ (dr X5 (dl X0 X1)) := by
    first | exact superpose ef1749 ef33886 | exact superpose ef33886 ef1749
  have ef34516 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ X3) ◇ X4) ◇ (dr X0 X1) = (dl X0 X2) ◇ (X4 ◇ (dr X1 X3)) := by
    first | exact superpose ef1764 ef34226 | exact superpose ef34226 ef1764
  have ef34542 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr (dl X3 X4) (dl X0 X1)) = (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 := by
    first | exact superpose ef1824 ef34257 | exact superpose ef34257 ef1824
  have ef34770 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (dr (dl X0 X1) X3)) := by
    first | exact superpose ef1764 ef34542 | exact superpose ef34542 ef1764
  have ef34929 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (X1 ◇ (dr X3 X0))) := by
    first | exact superpose ef1764 ef34770 | exact superpose ef34770 ef1764
  have ef35751 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = dl (dl X0 X1) (dl X4 (dr X2 X3)) := by
    first | exact superpose ef264 ef302 | exact superpose ef302 ef264
  have ef35790 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = (dl (dr X2 X3) (dl X0 X1)) ◇ X4 := by
    first | exact superpose ef3458 ef35751 | exact superpose ef35751 ef3458
  have ef36057 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ ((dr X4 (dl X0 X1)) ◇ X2) := by
    first | exact superpose ef3082 ef35790 | exact superpose ef35790 ef3082
  have ef36292 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ (X0 ◇ (dl (dr X4 X2) X1)) := by
    first | exact superpose ef17034 ef36057 | exact superpose ef36057 ef17034
  have ef37015 (X0 X1 X2 X3 X4 : G) :
      (dr (X0 ◇ X2) X1) ◇ (X3 ◇ X4) = ((X4 ◇ (X0 ◇ X1)) ◇ X3) ◇ X2 := by
    first | exact superpose ef6434 ef127 | exact superpose ef127 ef6434
  have ef37135 (X0 X1 X2 X3 X4 : G) :
      (dr (X0 ◇ X2) X1) ◇ (X3 ◇ X4) = X0 ◇ (X3 ◇ (dl (dr X2 X4) X1)) := by
    first | exact superpose ef36292 ef37015 | exact superpose ef37015 ef36292
  have ef37472 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (X1 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X2) = dl X2 ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef23 ef269 | exact superpose ef269 ef23
  have ef41957 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (dr X4 X5) = X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) := by
    first | exact superpose ef275 ef269 | exact superpose ef269 ef275
  have ef41972 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) = X1 ◇ (X3 ◇ (X0 ◇ (dr X2 (dr X4 X5)))) := by
    first | exact superpose ef34929 ef41957 | exact superpose ef41957 ef34929
  have ef42151 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) = X1 ◇ (X3 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X4)))) := by
    first | exact superpose ef96 ef41972 | exact superpose ef41972 ef96
  have ef42683 (X0 X1 X2 : G) : X2 ◇ (dr (X0 ◇ X1) X0) = (wf X0 X1) ◇ (dl X2 X0) := by
    first | exact superpose ef8083 ef937 | exact superpose ef937 ef8083
  have ef42686 (X0 X1 X2 : G) : X0 ◇ (dr X2 (wf X0 X1)) = dr (dr (X0 ◇ X1) X0) X2 := by
    first | exact superpose ef8083 ef1764 | exact superpose ef1764 ef8083
  have ef42716 (X0 X1 X2 : G) : X0 ◇ (dr X2 (wf X0 X1)) = (dl X2 X0) ◇ (X0 ◇ X1) := by
    first | exact superpose ef1753 ef42686 | exact superpose ef42686 ef1753
  have ef50965 (X0 X1 X2 X3 : G) :
      (X2 ◇ X3) ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef9929 ef126 | exact superpose ef126 ef9929
  have ef50982 (X0 X1 X2 X3 : G) :
      dl X2 (dl (X0 ◇ (X0 ◇ X0)) X3) = X1 ◇ (((wf X0 X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef9929 ef272 | exact superpose ef272 ef9929
  have ef51008 (X0 X1 X2 : G) : X1 ◇ X2 = (dr (wf X0 X1) X2) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef9929 ef6434 | exact superpose ef6434 ef9929
  have ef51118 (X0 X1 X2 : G) : X1 ◇ X2 = X0 ◇ (X0 ◇ (X0 ◇ (dr (wf X0 X1) X2))) := by
    first | exact superpose ef923 ef51008 | exact superpose ef51008 ef923
  have ef51142 (X0 X1 X2 X3 : G) :
      X1 ◇ (((wf X0 X1) ◇ X3) ◇ X2) = (dl X3 X2) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef3458 ef50982 | exact superpose ef50982 ef3458
  have ef51157 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (wf X0 X3) := by
    first | exact superpose ef9929 ef50965 | exact superpose ef50965 ef9929
  have ef51340 (X0 X1 X2 : G) : X1 ◇ X2 = wf X0 (dr (wf X0 X1) X2) := by
    first | exact superpose ef974 ef51118 | exact superpose ef51118 ef974
  have ef51360 (X0 X1 X2 X3 : G) : X1 ◇ (((wf X0 X1) ◇ X3) ◇ X2) = wf X0 (dl X3 X2) := by
    first | exact superpose ef9929 ef51142 | exact superpose ef51142 ef9929
  have ef53603 (X0 X1 X2 X3 : G) :
      dl (X1 ◇ (dl (X0 ◇ X3) X2)) X0 = (wf X0 X3) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef309 ef326 | exact superpose ef326 ef309
  have ef53879 (X0 X1 X2 X3 : G) :
      (wf X0 X3) ◇ ((X0 ◇ X1) ◇ X2) = (dl (X0 ◇ X3) X2) ◇ (dr X1 X0) := by
    first | exact superpose ef618 ef53603 | exact superpose ef53603 ef618
  have ef54118 (X0 X1 X2 X3 : G) :
      (wf X0 X3) ◇ ((X0 ◇ X1) ◇ X2) = (X3 ◇ (dr X0 X2)) ◇ (dr X1 X0) := by
    first | exact superpose ef618 ef53879 | exact superpose ef53879 ef618
  have ef55866 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (wf X2 X1)) = (X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ (dr X2 X2)) := by
    first | exact superpose ef332 ef126 | exact superpose ef126 ef332
  have ef56303 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (wf X2 X1)) = (X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ (wf X2 X2)) := by
    first | exact superpose ef8081 ef55866 | exact superpose ef55866 ef8081
  have ef59222 (X0 X1 X2 X3 X4 : G) :
      ((dr (X0 ◇ (wf X1 X2)) X3) ◇ (X4 ◇ (dr X1 (dr X2 X1)))) ◇ (X3 ◇ (dr X0 X1)) = X4 := by
    first | exact superpose ef100 ef430 | exact superpose ef430 ef100
  have ef59371 (X0 X1 X2 X3 X4 : G) :
      (dl X1 (X2 ◇ (X3 ◇ X4))) ◇ X0 = dr ((dr X4 X2) ◇ (X0 ◇ X3)) X1 := by
    first | exact superpose ef430 ef97 | exact superpose ef97 ef430
  have ef59407 (X0 X1 X2 X3 X4 X5 : G) :
      (((dr X1 X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ (dl (X2 ◇ (X3 ◇ X1)) X5)) := by
    first | exact superpose ef430 ef309 | exact superpose ef309 ef430
  have ef59500 (X0 X1 X2 X3 X4 X5 : G) :
      (((dr X1 X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) := by
    first | exact superpose ef618 ef59407 | exact superpose ef59407 ef618
  have ef59536 (X0 X1 X2 X3 X4 : G) :
      (dl X1 (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X3 ◇ ((dr X4 X2) ◇ X1)) ◇ X0 := by
    first | exact superpose ef1826 ef59371 | exact superpose ef59371 ef1826
  have ef59680 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ (dl ((dr (X0 ◇ (wf X1 X2)) X3) ◇ (X4 ◇ (dr X1 (dr X2 X1)))) X1) = X4 := by
    first | exact superpose ef3121 ef59222 | exact superpose ef59222 ef3121
  have ef59891 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) = X0 ◇ (X4 ◇ (dl (dr X5 (dr X1 X2)) X3)) := by
    first | exact superpose ef36292 ef59500 | exact superpose ef59500 ef36292
  have ef59927 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ X4) ◇ (dr X1 (dl X0 X2)) = (X3 ◇ ((dr X4 X2) ◇ X1)) ◇ X0 := by
    first | exact superpose ef5507 ef59536 | exact superpose ef59536 ef5507
  have ef60056 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ ((X4 ◇ (dr X1 (dr X2 X1))) ◇ (dr (dr (X0 ◇ (wf X1 X2)) X3) X1)) = X4 := by
    first | exact superpose ef618 ef59680 | exact superpose ef59680 ef618
  have ef60254 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) = X0 ◇ (X4 ◇ (dl (X2 ◇ (X5 ◇ X1)) X3)) := by
    first | exact superpose ef96 ef59891 | exact superpose ef59891 ef96
  have ef60399 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ ((wf X1 X4) ◇ ((X1 ◇ (dr (X0 ◇ (wf X1 X2)) X3)) ◇ (dr X2 X1))) = X4 := by
    first | exact superpose ef54118 ef60056 | exact superpose ef60056 ef54118
  have ef60583 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) = X0 ◇ (X4 ◇ ((X5 ◇ X1) ◇ (dr X2 X3))) := by
    first | exact superpose ef618 ef60254 | exact superpose ef60254 ef618
  have ef60693 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ ((wf X1 X4) ◇ (dr (dr (X0 ◇ (wf X1 X2)) X3) X2)) = X4 := by
    first | exact superpose ef105 ef60399 | exact superpose ef60399 ef105
  have ef60933 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ X3) ◇ ((wf X1 X4) ◇ ((dl X2 X3) ◇ (X0 ◇ (wf X1 X2)))) = X4 := by
    first | exact superpose ef1753 ef60693 | exact superpose ef60693 ef1753
  have ef61105 (X1 X2 X3 X4 : G) : dr (wf X1 X2) (dl (dr (wf X1 X4) (dl X2 X3)) X3) = X4 := by
    first | exact superpose ef17687 ef60933 | exact superpose ef60933 ef17687
  have ef61204 (X1 X2 X4 : G) : dr (wf X1 X2) (dl X2 (wf X1 X4)) = X4 := by
    first | exact superpose ef918 ef61105 | exact superpose ef61105 ef918
  have ef63096 (X0 X1 X2 X3 : G) :
      dl (dl X1 (wf X0 (X2 ◇ (X2 ◇ X3)))) X2 = (wf X2 X3) ◇ (wf X0 X1) := by
    first | exact superpose ef23648 ef326 | exact superpose ef326 ef23648
  have ef63113 (X0 X1 X2 X3 : G) : X3 ◇ (wf X0 X1) = dl (dl X1 (wf X0 (dl X2 X3))) X2 := by
    first | exact superpose ef23648 ef152 | exact superpose ef152 ef23648
  have ef63135 (X0 X1 X2 X3 : G) : X3 ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (wf X0 (dl X2 X3)) := by
    first | exact superpose ef233 ef63113 | exact superpose ef63113 ef233
  have ef63152 (X0 X1 X2 X3 : G) :
      (wf X2 X3) ◇ (wf X0 X1) = (X2 ◇ X1) ◇ (wf X0 (X2 ◇ (X2 ◇ X3))) := by
    first | exact superpose ef233 ef63096 | exact superpose ef63096 ef233
  have ef63397 (X0 X1 X2 X3 X4 : G) :
      dl (dr (dl X1 (wf X0 X2)) X3) X4 = (X4 ◇ (X3 ◇ (wf X0 X1))) ◇ X2 := by
    first | exact superpose ef23648 ef438 | exact superpose ef438 ef23648
  have ef63654 (X0 X1 X2 X3 X4 : G) :
      (dl X3 X4) ◇ (dl (dr X0 X1) X2) = dr (X2 ◇ (X1 ◇ (X4 ◇ X0))) X3 := by
    first | exact superpose ef438 ef97 | exact superpose ef97 ef438
  have ef63696 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X1 ◇ (X5 ◇ X0))) ◇ ((dr X5 X4) ◇ X3) = dl X3 (X4 ◇ (dl (dr X0 X1) X2)) := by
    first | exact superpose ef438 ef437 | exact superpose ef437 ef438
  have ef63905 (X0 X1 X2 X3 X4 X5 : G) :
      dl X3 (X4 ◇ (dl (dr X0 X1) X2)) = (dr X1 X5) ◇ (dr (((dr X5 X4) ◇ X3) ◇ X2) X0) := by
    first | exact superpose ef13413 ef63696 | exact superpose ef63696 ef13413
  have ef63947 (X0 X1 X2 X3 X4 : G) :
      (dl X3 X4) ◇ (dl (dr X0 X1) X2) = ((X4 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1 := by
    first | exact superpose ef1826 ef63654 | exact superpose ef63654 ef1826
  have ef64195 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X3 ◇ (wf X0 X1))) ◇ X2 = dl ((wf X0 X2) ◇ (dr X3 X1)) X4 := by
    first | exact superpose ef1764 ef63397 | exact superpose ef63397 ef1764
  have ef64289 (X0 X1 X2 X3 X4 X5 : G) :
      dl X3 (X4 ◇ (dl (dr X0 X1) X2)) = (dr X1 X5) ◇ ((dl X0 (X2 ◇ (dr X5 X4))) ◇ X3) := by
    first | exact superpose ef1749 ef63905 | exact superpose ef63905 ef1749
  have ef64550 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X3 ◇ (wf X0 X1))) ◇ X2 = (dr X3 X1) ◇ (dr (wf X0 X2) X4) := by
    first | exact superpose ef618 ef64195 | exact superpose ef64195 ef618
  have ef64621 (X0 X1 X2 X3 X4 X5 : G) :
      dl X3 (X4 ◇ (dl (dr X0 X1) X2)) = (dr X1 X5) ◇ ((dr X5 X4) ◇ (dr X0 (dl X3 X2))) := by
    first | exact superpose ef5507 ef64289 | exact superpose ef64289 ef5507
  have ef64893 (X0 X1 X2 X3 X4 : G) :
      dl X3 (X4 ◇ (dl (dr X0 X1) X2)) = dl (dr X0 (dl X3 X2)) (X4 ◇ X1) := by
    first | exact superpose ef2372 ef64621 | exact superpose ef64621 ef2372
  have ef69229 (X0 X1 X2 X3 : G) :
      X1 ◇ (X2 ◇ (wf X0 X3)) = (X0 ◇ X2) ◇ (dl X1 (dr (X0 ◇ X3) X0)) := by
    first | exact superpose ef8085 ef532 | exact superpose ef532 ef8085
  have ef69701 (X0 X1 X2 X3 : G) :
      X1 ◇ (X2 ◇ (wf X0 X3)) = (X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef119 ef69229 | exact superpose ef69229 ef119
  have ef70869 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = dr X4 (dl (X1 ◇ (dl X3 X2)) X5) := by
    first | exact superpose ef309 ef577 | exact superpose ef577 ef309
  have ef71235 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = ((X3 ◇ X1) ◇ X0) ◇
      (((X3 ◇ X1) ◇ X0) ◇ (dr X0 (dl X1 X2))) := by
    first | exact superpose ef577 ef974 | exact superpose ef974 ef577
  have ef71342 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (((((X3 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ (dr X0 (dl X1 X2))) := by
    first | exact superpose ef2033 ef71235 | exact superpose ef71235 ef2033
  have ef71687 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = dr X4 ((dl X3 X2) ◇ (dr X1 X5)) := by
    first | exact superpose ef618 ef70869 | exact superpose ef70869 ef618
  have ef71777 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      ((dl X0 ((X3 ◇ X1) ◇ X0)) ◇ (X0 ◇ (dr (dl X1 X2) X1))) := by
    first | exact superpose ef34516 ef71342 | exact superpose ef71342 ef34516
  have ef72069 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = ((dr X1 X5) ◇ X4) ◇ (dl X3 X2) := by
    first | exact superpose ef40 ef71687 | exact superpose ef71687 ef40
  have ef72148 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (X0 ◇ (dr X0 (dl (X0 ◇ (dr (dl X1 X2) X1)) (X3 ◇ X1)))) := by
    first | exact superpose ef5507 ef71777 | exact superpose ef71777 ef5507
  have ef72379 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = X1 ◇ (X5 ◇ (dl X4 (dl X3 X2))) := by
    first | exact superpose ef795 ef72069 | exact superpose ef72069 ef795
  have ef72445 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (X0 ◇ (dr X0 ((dr (dl X1 X2) X1) ◇ (dr X0 (X3 ◇ X1))))) := by
    first | exact superpose ef618 ef72148 | exact superpose ef72148 ef618
  have ef72615 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X5 ◇ (X0 ◇ X3)) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef3458 ef72379 | exact superpose ef72379 ef3458
  have ef72661 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (X0 ◇ (((dr X0 (X3 ◇ X1)) ◇ X0) ◇ (dr (dl X1 X2) X1))) := by
    first | exact superpose ef40 ef72445 | exact superpose ef72445 ef40
  have ef72782 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ (X0 ◇ (dr X2 (X5 ◇ (X0 ◇ X3))))) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef34929 ef72615 | exact superpose ef72615 ef34929
  have ef72812 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (X0 ◇ ((X1 ◇ X0) ◇ (dr (dl X1 X2) (dr X0 (X3 ◇ X1))))) := by
    first | exact superpose ef60583 ef72661 | exact superpose ef72661 ef60583
  have ef72888 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ (X0 ◇ (((X0 ◇ X3) ◇ X2) ◇ X5))) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef40 ef72782 | exact superpose ef72782 ef40
  have ef72907 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X1) ◇ ((dl X1 X2) ◇ X0)))) := by
    first | exact superpose ef96 ef72812 | exact superpose ef72812 ef96
  have ef72953 (X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ (dl X5 (dl X3 X2))) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef272 ef72888 | exact superpose ef72888 ef272
  have ef72966 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇
      (X0 ◇ (X0 ◇ (X0 ◇ ((dl X1 X2) ◇ (X1 ◇ (X3 ◇ X1)))))) := by
    first | exact superpose ef42151 ef72907 | exact superpose ef72907 ef42151
  have ef72998 (X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X4 ◇ ((dl X2 X5) ◇ X3)) = X1 ◇ (X5 ◇ ((dl X2 X4) ◇ X3)) := by
    first | exact superpose ef3458 ef72953 | exact superpose ef72953 ef3458
  have ef73004 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇ (wf X0 ((dl X1 X2) ◇ (X1 ◇ (X3 ◇ X1)))) := by
    first | exact superpose ef974 ef72966 | exact superpose ef72966 ef974
  have ef73028 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇ (wf X0 (X1 ◇ (X1 ◇ (X3 ◇ (dl X1 X2))))) := by
    first | exact superpose ef923 ef73004 | exact superpose ef73004 ef923
  have ef73042 (X0 X1 X2 X3 : G) :
      wf ((X3 ◇ X1) ◇ X0) (X2 ◇ X3) = X3 ◇ (wf X0 (wf X1 (dl X3 X2))) := by
    first | exact superpose ef4444 ef73028 | exact superpose ef73028 ef4444
  have ef74691 (X0 X1 X2 X3 X4 X5 : G) :
      dl X2 ((dr X0 X1) ◇ X5) = (X4 ◇ (X1 ◇ X3)) ◇ ((X5 ◇ ((dr X3 X4) ◇ X0)) ◇ X2) := by
    first | exact superpose ef578 ef269 | exact superpose ef269 ef578
  have ef74844 (X0 X1 X2 X3 X4 X5 : G) :
      dl X2 ((dr X0 X1) ◇ X5) = (X4 ◇ (X1 ◇ X3)) ◇ ((X5 ◇ X3) ◇ (dr X0 (dl X2 X4))) := by
    first | exact superpose ef59927 ef74691 | exact superpose ef74691 ef59927
  have ef75221 (X0 X1 X2 X4 X5 : G) :
      dl X2 ((dr X0 X1) ◇ X5) = dl (dr X0 (dl X2 X4)) ((dr X4 X1) ◇ X5) := by
    first | exact superpose ef37472 ef74844 | exact superpose ef74844 ef37472
  have ef75542 (X0 X1 X2 X4 X5 : G) :
      dl X2 ((dr X0 X1) ◇ X5) = dl X2 ((dr X4 X1) ◇ (dl (dr X0 X5) X4)) := by
    first | exact superpose ef64893 ef75221 | exact superpose ef75221 ef64893
  have ef75781 (X0 X1 X2 X5 : G) : dl X2 ((dr X0 X1) ◇ X5) = dl X2 ((dr X0 X5) ◇ X1) := by
    first | exact superpose ef940 ef75542 | exact superpose ef75542 ef940
  have ef76655 (X0 X1 X2 X3 : G) :
      dl (dr X0 (wf X1 X2)) X3 = (X3 ◇ X1) ◇ (dr (dr (X1 ◇ X2) X1) X0) := by
    first | exact superpose ef601 ef275 | exact superpose ef275 ef601
  have ef76916 (X0 X1 X2 X3 : G) :
      dl (dr X0 (wf X1 X2)) X3 = (X3 ◇ X1) ◇ ((dl X0 X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef1753 ef76655 | exact superpose ef76655 ef1753
  have ef77263 (X0 X1 X2 X3 : G) :
      X1 ◇ ((dl X0 (X3 ◇ X1)) ◇ (X1 ◇ X2)) = dl (dr X0 (wf X1 X2)) X3 := by
    first | exact superpose ef4377 ef76916 | exact superpose ef76916 ef4377
  have ef77581 (X0 X1 X2 X3 : G) :
      X1 ◇ ((dl X0 (X3 ◇ X1)) ◇ (X1 ◇ X2)) = wf X1 (X0 ◇ (dl X3 X2)) := by
    first | exact superpose ef33738 ef77263 | exact superpose ef77263 ef33738
  have ef77845 (X0 X1 X2 X3 : G) :
      X1 ◇ (X1 ◇ (dr X0 (dl (X1 ◇ X2) X3))) = wf X1 (X0 ◇ (dl X3 X2)) := by
    first | exact superpose ef5507 ef77581 | exact superpose ef77581 ef5507
  have ef78060 (X0 X1 X2 X3 : G) :
      X1 ◇ (X1 ◇ (dr X0 (X2 ◇ (dr X1 X3)))) = wf X1 (X0 ◇ (dl X3 X2)) := by
    first | exact superpose ef618 ef77845 | exact superpose ef77845 ef618
  have ef78241 (X0 X1 X2 X3 : G) :
      X1 ◇ (X1 ◇ (((dr X1 X3) ◇ X0) ◇ X2)) = wf X1 (X0 ◇ (dl X3 X2)) := by
    first | exact superpose ef40 ef78060 | exact superpose ef78060 ef40
  have ef78401 (X0 X1 X2 X3 : G) :
      X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (dl X0 X2)))) = wf X1 (X0 ◇ (dl X3 X2)) := by
    first | exact superpose ef795 ef78241 | exact superpose ef78241 ef795
  have ef78529 (X0 X1 X2 X3 : G) : wf X1 (X3 ◇ (dl X0 X2)) = wf X1 (X0 ◇ (dl X3 X2)) := by
    first | exact superpose ef974 ef78401 | exact superpose ef78401 ef974
  have ef85274 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) ((dl X3 X0) ◇ X2) = (X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    first | exact superpose ef846 ef974 | exact superpose ef974 ef846
  have ef85382 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) ((dl X3 X0) ◇ X2) = X1 ◇ (dr X3 (wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)))) := by
    first | exact superpose ef3766 ef85274 | exact superpose ef85274 ef3766
  have ef87728 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = dr (X0 ◇ (X1 ◇ ((X4 ◇ X3) ◇ X2))) X4 := by
    first | exact superpose ef902 ef23 | exact superpose ef23 ef902
  have ef87825 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = dr (X0 ◇ X4) (X1 ◇ ((X4 ◇ X3) ◇ X2)) := by
    first | exact superpose ef1873 ef87728 | exact superpose ef87728 ef1873
  have ef88289 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = (((X4 ◇ X3) ◇ X2) ◇ (X0 ◇ X4)) ◇ X1 := by
    first | exact superpose ef40 ef87825 | exact superpose ef87825 ef40
  have ef88693 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = (dl X4 (X4 ◇ X3)) ◇ (dl (dr X2 X1) X0) := by
    first | exact superpose ef63947 ef88289 | exact superpose ef88289 ef63947
  have ef89022 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = X3 ◇ (dr X4 (dl (dl (dr X2 X1) X0) X4)) := by
    first | exact superpose ef5507 ef88693 | exact superpose ef88693 ef5507
  have ef89266 (X0 X1 X2 X3 : G) : X3 ◇ (dl (dr X2 X1) X0) = X3 ◇ (dl (dr X0 X1) X2) := by
    first | exact superpose ef21 ef89022 | exact superpose ef89022 ef21
  have ef96313 (X0 X1 X2 : G) : dl X1 ((dr X2 X0) ◇ X2) = dl (wf X2 X2) (X1 ◇ X0) := by
    first | exact superpose ef9646 ef5615 | exact superpose ef5615 ef9646
  have ef96320 (X0 X1 X2 : G) : dl X1 ((dr X2 X0) ◇ X2) = (wf X2 (X1 ◇ X0)) ◇ X2 := by
    first | exact superpose ef27972 ef96313 | exact superpose ef96313 ef27972
  have ef119005 (X0 X1 X2 X3 : G) : dr (wf X1 X0) X2 = dr (X0 ◇ X2) (dl X3 (wf X1 X3)) := by
    first | exact superpose ef24465 ef1863 | exact superpose ef1863 ef24465
  have ef127213 (X0 X1 X2 X3 X4 : G) :
      (dr ((X2 ◇ X3) ◇ X1) ((X2 ◇ X3) ◇ X1)) ◇
      ((wf ((X2 ◇ X3) ◇ X1) (dl X0 X3)) ◇ (dr (X0 ◇ (X1 ◇ X2)) X4)) = X4 := by
    first | exact superpose ef532 ef2312 | exact superpose ef2312 ef532
  have ef127654 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ X3) ◇
      ((wf ((X2 ◇ X3) ◇ X1) (dl X0 X3)) ◇ (dl (dr X1 (dr (X0 ◇ (X1 ◇ X2)) X4)) ((X2 ◇ X3) ◇ X1))) =
      X4 := by
    first | exact superpose ef37135 ef127213 | exact superpose ef127213 ef37135
  have ef127954 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ X3) ◇
      ((X2 ◇ X3) ◇ (dl (wf ((X2 ◇ X3) ◇ X1) (dl X0 X3)) ((dr X1 (dr (X0 ◇ (X1 ◇ X2)) X4)) ◇ X1))) =
      X4 := by
    first | exact superpose ef13807 ef127654 | exact superpose ef127654 ef13807
  have ef128235 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr X2 (wf (X2 ◇
      X3) (dl (wf ((X2 ◇ X3) ◇ X1) (dl X0 X3)) ((dr X1 (dr (X0 ◇ (X1 ◇ X2)) X4)) ◇ X1)))) = X4 := by
    first | exact superpose ef3766 ef127954 | exact superpose ef127954 ef3766
  have ef128478 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr X2 (wf (X2 ◇
      X3) (dl (wf ((X2 ◇ X3) ◇ X1) (dl X0 X3)) ((dr X1 X1) ◇ (dr (X0 ◇ (X1 ◇ X2)) X4))))) = X4 := by
    first | exact superpose ef75781 ef128235 | exact superpose ef128235 ef75781
  have ef128689 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr X2 (wf (X2 ◇ X3) ((dl X4 (dr X1 X1)) ◇
      ((X0 ◇ (X1 ◇ X2)) ◇ (wf ((X2 ◇ X3) ◇ X1) (dl X0 X3)))))) = X4 := by
    first | exact superpose ef4335 ef128478 | exact superpose ef128478 ef4335
  have ef128863 (X1 X2 X3 X4 : G) :
      X3 ◇ (dr X2 (wf (X2 ◇ X3) ((dl X4 (dr X1 X1)) ◇ (X3 ◇ (wf ((X2 ◇ X3) ◇ X1) (X1 ◇ X2)))))) =
      X4 := by
    first | exact superpose ef63135 ef128689 | exact superpose ef128689 ef63135
  have ef129014 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) ((dl X2 (dl X4 (dr X1 X1))) ◇ (wf ((X2 ◇ X3) ◇ X1) (X1 ◇ X2))) = X4 := by
    first | exact superpose ef85382 ef128863 | exact superpose ef128863 ef85382
  have ef129138 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) ((dl X2 (dl X4 (dr X1 X1))) ◇ (X2 ◇ (wf X1 (wf X3 (dl X2 X1))))) = X4 := by
    first | exact superpose ef73042 ef129014 | exact superpose ef129014 ef73042
  have ef129249 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) (((dl (dr X1 X1) X2) ◇ X4) ◇ (X2 ◇ (wf X1 (wf X3 (dl X2 X1))))) = X4 := by
    first | exact superpose ef3458 ef129138 | exact superpose ef129138 ef3458
  have ef129345 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) ((X1 ◇ ((dr X4 X2) ◇ X1)) ◇ (X2 ◇ (wf X1 (wf X3 (dl X2 X1))))) = X4 := by
    first | exact superpose ef3082 ef129249 | exact superpose ef129249 ef3082
  have ef129427 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) ((X1 ◇ X2) ◇ (((dr X4 X2) ◇ (wf X3 (dl X2 X1))) ◇ (wf X1 X1))) = X4 := by
    first | exact superpose ef56303 ef129345 | exact superpose ef129345 ef56303
  have ef129497 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) (dr ((dr X4 X2) ◇ (wf X3 (dl X2 X1))) (dl X1 X2)) = X4 := by
    first | exact superpose ef33807 ef129427 | exact superpose ef129427 ef33807
  have ef129561 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) (dr (X1 ◇ (dl (dr X4 X2) X2)) (wf X3 (dl X2 X1))) = X4 := by
    first | exact superpose ef15316 ef129497 | exact superpose ef129497 ef15316
  have ef129611 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) (dr X2 (dl (dr X4 X2) (X1 ◇ (wf X3 (dl X2 X1))))) = X4 := by
    first | exact superpose ef8468 ef129561 | exact superpose ef129561 ef8468
  have ef129650 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) ((X2 ◇ (X1 ◇ (wf X3 (dl X2 X1)))) ◇ (wf X2 X4)) = X4 := by
    first | exact superpose ef6106 ef129611 | exact superpose ef129611 ef6106
  have ef129682 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) ((dr X1 (dl X2 X1)) ◇ (dr (wf X3 (wf X2 X4)) X2)) = X4 := by
    first | exact superpose ef64550 ef129650 | exact superpose ef129650 ef64550
  have ef129709 (X1 X2 X3 X4 : G) :
      wf (X2 ◇ X3) (X2 ◇ (dl (dr X1 (dr (wf X3 (wf X2 X4)) X2)) X1)) = X4 := by
    first | exact superpose ef17034 ef129682 | exact superpose ef129682 ef17034
  have ef129733 (X2 X3 X4 : G) : wf (X2 ◇ X3) (X2 ◇ (dr (wf X3 (wf X2 X4)) X2)) = X4 := by
    first | exact superpose ef22 ef129709 | exact superpose ef129709 ef22
  have ef135045 (X0 X1 X2 X3 : G) :
      X0 ◇ (dl (X1 ◇ X2) (wf X0 X3)) = (X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef2703 ef126 | exact superpose ef126 ef2703
  have ef135883 (X0 X1 X2 X3 : G) :
      (X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)) = X0 ◇ (X2 ◇ (dr X1 (wf X0 X3))) := by
    first | exact superpose ef618 ef135045 | exact superpose ef135045 ef618
  have ef139326 (X0 X1 X2 X3 : G) : (dr (wf X2 X0) X1) ◇ X3 = wf X2 (dr (X0 ◇ X1) X3) := by
    first | exact superpose ef51340 ef51340
  have ef139385 (X0 X1 X2 X3 : G) : dr (wf X2 X0) X1 = dr (wf X2 X3) (dl X3 (X0 ◇ X1)) := by
    first | exact superpose ef51340 ef61204 | exact superpose ef61204 ef51340
  have ef141943 (X0 X1 X2 : G) : dl (dr X1 X2) X0 = (wf X0 X1) ◇ ((wf X0 X2) ◇ X0) := by
    first | exact superpose ef2989 ef438 | exact superpose ef438 ef2989
  have ef159902 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = (((X0 ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ (dl X1 X0)) ◇
      X4 := by
    first | exact superpose ef256 ef2036 | exact superpose ef2036 ef256
  have ef160009 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = ((X2 ◇ X3) ◇ X0) ◇
      ((dl X1 X0) ◇ (dl (dr X4 (X0 ◇ X2)) X2)) := by
    first | exact superpose ef36292 ef159902 | exact superpose ef159902 ef36292
  have ef160576 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      ((dl X1 ((X2 ◇ X3) ◇ X0)) ◇ (dl (dr X4 (X0 ◇ X2)) X2)) := by
    first | exact superpose ef4377 ef160009 | exact superpose ef160009 ef4377
  have ef161135 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      (X0 ◇ (dr X1 (dl (dl (dr X4 (X0 ◇ X2)) X2) (X2 ◇ X3)))) := by
    first | exact superpose ef5507 ef160576 | exact superpose ef160576 ef5507
  have ef161688 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      (X0 ◇ (dr X1 (dl X2 ((dl (dr X4 (X0 ◇ X2)) X2) ◇ X3)))) := by
    first | exact superpose ef20331 ef161135 | exact superpose ef161135 ef20331
  have ef162220 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      (X0 ◇ (dr X1 ((dr X3 X2) ◇ ((dr X4 (X0 ◇ X2)) ◇ X2)))) := by
    first | exact superpose ef3044 ef161688 | exact superpose ef161688 ef3044
  have ef162730 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      (X0 ◇ ((((dr X4 (X0 ◇ X2)) ◇ X2) ◇ X1) ◇ (dr X3 X2))) := by
    first | exact superpose ef40 ef162220 | exact superpose ef162220 ef40
  have ef163218 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      (X0 ◇ ((X2 ◇ X1) ◇ (dr X3 ((dr X4 (X0 ◇ X2)) ◇ X2)))) := by
    first | exact superpose ef60583 ef162730 | exact superpose ef162730 ef60583
  have ef163677 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇
      (X0 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ (dr X4 (X0 ◇ X2))))) := by
    first | exact superpose ef40 ef163218 | exact superpose ef163218 ef40
  have ef164105 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ X0)))) := by
    first | exact superpose ef40 ef163677 | exact superpose ef163677 ef40
  have ef164511 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = wf X0 ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ (X2 ◇ X1))) := by
    first | exact superpose ef21049 ef164105 | exact superpose ef164105 ef21049
  have ef164889 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (wf (X0 ◇ X2) X3)) ◇ X4 = wf X0 (X1 ◇ (X3 ◇ (wf X2 X4))) := by
    first | exact superpose ef69701 ef164511 | exact superpose ef164511 ef69701
  have ef171287 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X0) ◇
      ((dl ((X0 ◇ X1) ◇ X2) X1) ◇ ((dl ((X0 ◇ X1) ◇ X2) X1) ◇ X3)) := by
    first | exact superpose ef854 ef69 | exact superpose ef69 ef854
  have ef171481 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X0) ◇
      (X1 ◇ ((dl ((X0 ◇ X1) ◇ X2) (dl ((X0 ◇ X1) ◇ X2) X1)) ◇ X3)) := by
    first | exact superpose ef72998 ef171287 | exact superpose ef171287 ef72998
  have ef171792 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X0) ◇
      (X1 ◇ (((dl X1 ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) := by
    first | exact superpose ef3458 ef171481 | exact superpose ef171481 ef3458
  have ef172079 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X0) ◇
      (X1 ◇ (X0 ◇ (dr (X1 ◇ (dl X1 ((X0 ◇ X1) ◇ X2))) (dl X3 X2)))) := by
    first | exact superpose ef19593 ef171792 | exact superpose ef171792 ef19593
  have ef172336 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = X0 ◇
      (X1 ◇ (dr X2 (wf X0 (dr (X1 ◇ (dl X1 ((X0 ◇ X1) ◇ X2))) (dl X3 X2))))) := by
    first | exact superpose ef135883 ef172079 | exact superpose ef172079 ef135883
  have ef172570 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = X0 ◇
      (X1 ◇ (dr X2 ((dr (wf X0 X1) (dl X1 ((X0 ◇ X1) ◇ X2))) ◇ (dl X3 X2)))) := by
    first | exact superpose ef139326 ef172336 | exact superpose ef172336 ef139326
  have ef172782 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = X0 ◇
      (X1 ◇ (((dl X3 X2) ◇ X2) ◇ (dr (wf X0 X1) (dl X1 ((X0 ◇ X1) ◇ X2))))) := by
    first | exact superpose ef40 ef172570 | exact superpose ef172570 ef40
  have ef172977 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = X0 ◇
      (X1 ◇ (((dl X3 X2) ◇ X2) ◇ (dr (wf X0 (X0 ◇ X1)) X2))) := by
    first | exact superpose ef139385 ef172782 | exact superpose ef172782 ef139385
  have ef173144 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = X0 ◇
      (X1 ◇ ((X2 ◇ X2) ◇ (dr (wf X0 (X0 ◇ X1)) (dl X3 X2)))) := by
    first | exact superpose ef60583 ef172977 | exact superpose ef172977 ef60583
  have ef173286 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = X0 ◇
      (X1 ◇ ((X2 ◇ X2) ◇ (dr (X0 ◇ (wf X0 X1)) (dl X3 X2)))) := by
    first | exact superpose ef8077 ef173144 | exact superpose ef173144 ef8077
  have ef173408 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = ((dl (dl X3 X2) (X2 ◇ X2)) ◇ X1) ◇ (wf X0 X1) := by
    first | exact superpose ef20621 ef173286 | exact superpose ef173286 ef20621
  have ef173508 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = ((dl X2 ((dl X3 X2) ◇ X2)) ◇ X1) ◇ (wf X0 X1) := by
    first | exact superpose ef5256 ef173408 | exact superpose ef173408 ef5256
  have ef173588 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ (dr X2 (dl X1 (dl X3 X2)))) ◇ (wf X0 X1) := by
    first | exact superpose ef5507 ef173508 | exact superpose ef173508 ef5507
  have ef173650 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X1) ◇ (wf X0 (dr X2 (dl X1 (dl X3 X2)))) := by
    first | exact superpose ef51157 ef173588 | exact superpose ef173588 ef51157
  have ef173698 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X1) ◇ (wf X0 (dr X2 ((dl X2 X1) ◇ X3))) := by
    first | exact superpose ef3458 ef173650 | exact superpose ef173650 ef3458
  have ef173736 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X1) ◇ (wf X0 ((X3 ◇ X2) ◇ (dl X2 X1))) := by
    first | exact superpose ef40 ef173698 | exact superpose ef173698 ef40
  have ef173770 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X1) ◇ (wf X0 (X2 ◇ (dl (X3 ◇ X2) X1))) := by
    first | exact superpose ef78529 ef173736 | exact superpose ef173736 ef78529
  have ef173795 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (X2 ◇ X1) ◇ (wf X0 (X2 ◇ (X2 ◇ (dr X3 X1)))) := by
    first | exact superpose ef618 ef173770 | exact superpose ef173770 ef618
  have ef173815 (X0 X1 X2 X3 : G) :
      wf (dl ((X0 ◇ X1) ◇ X2) X1) X3 = (wf X2 (dr X3 X1)) ◇ (wf X0 X1) := by
    first | exact superpose ef63152 ef173795 | exact superpose ef173795 ef63152
  have ef173832 (X0 X1 X2 X3 : G) : wf (X2 ◇ X0) X3 = (wf X2 (dr X3 X1)) ◇ (wf X0 X1) := by
    first | exact superpose ef72 ef173815 | exact superpose ef173815 ef72
  have ef203144 (X0 X1 X2 X3 X4 : G) :
      wf X2 (X0 ◇ (X1 ◇ (X3 ◇ X4))) = X2 ◇ ((((X4 ◇ X2) ◇ X3) ◇ X2) ◇ (dr X0 X1)) := by
    first | exact superpose ef23 ef1138 | exact superpose ef1138 ef23
  have ef203771 (X0 X1 X2 X3 X4 : G) :
      wf X2 (X0 ◇ (X1 ◇ (X3 ◇ X4))) = X2 ◇ (X2 ◇ (X2 ◇ (X4 ◇ (dr X3 (dr X0 X1))))) := by
    first | exact superpose ef34929 ef203144 | exact superpose ef203144 ef34929
  have ef204565 (X0 X1 X2 X3 X4 : G) :
      wf X2 (X0 ◇ (X1 ◇ (X3 ◇ X4))) = wf X2 (X4 ◇ (dr X3 (dr X0 X1))) := by
    first | exact superpose ef974 ef203771 | exact superpose ef203771 ef974
  have ef205335 (X0 X1 X2 X3 X4 : G) :
      wf X2 (X0 ◇ (X1 ◇ (X3 ◇ X4))) = wf X2 (X4 ◇ (X1 ◇ (X3 ◇ X0))) := by
    first | exact superpose ef96 ef204565 | exact superpose ef204565 ef96
  have ef209642 (X0 X1 X2 X3 X4 X5 : G) :
      (dl X0 (wf X1 X2)) ◇ (X3 ◇ X4) = (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X5) ◇ X3) ◇
      ((X5 ◇ X1) ◇ X4) := by
    first | exact superpose ef2703 ef1150 | exact superpose ef1150 ef2703
  have ef211164 (X0 X1 X2 X3 X4 : G) :
      (dl X0 (wf X1 X2)) ◇ (X3 ◇ X4) = (dl X1 X4) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    first | exact superpose ef5896 ef209642 | exact superpose ef209642 ef5896
  have ef252205 (X0 X1 X2 X3 : G) :
      (dl X0 X1) ◇ ((X2 ◇ X3) ◇ ((dl (wf (dl X0 X1) X1) X1) ◇ (X0 ◇ (X0 ◇ X3)))) = X2 := by
    first | exact superpose ef1005 ef2152 | exact superpose ef2152 ef1005
  have ef253468 (X0 X1 X2 X3 : G) :
      (dl (dl (wf (dl X0 X1) X1) X1) (wf X0 X3)) ◇ ((X2 ◇ X3) ◇ X1) = X2 := by
    first | exact superpose ef211164 ef252205 | exact superpose ef252205 ef211164
  have ef253915 (X0 X1 X2 X3 : G) :
      (dl X3 X1) ◇ (dl (dl (dl (wf (dl X0 X1) X1) X1) (wf X0 X3)) X2) = X2 := by
    first | exact superpose ef5925 ef253468 | exact superpose ef253468 ef5925
  have ef254317 (X0 X1 X2 X3 : G) :
      (dl X3 X1) ◇ ((X2 ◇ (dl (wf (dl X0 X1) X1) X1)) ◇ (wf X0 X3)) = X2 := by
    first | exact superpose ef233 ef253915 | exact superpose ef253915 ef233
  have ef254668 (X0 X1 X2 X3 : G) :
      (dl X3 X1) ◇ (X1 ◇ (dr ((wf X0 X3) ◇ X2) (wf (dl X0 X1) X1))) = X2 := by
    first | exact superpose ef4370 ef254317 | exact superpose ef254317 ef4370
  have ef254962 (X0 X1 X2 X3 : G) :
      X1 ◇ (dr X3 (wf X1 (dr ((wf X0 X3) ◇ X2) (wf (dl X0 X1) X1)))) = X2 := by
    first | exact superpose ef42716 ef254668 | exact superpose ef254668 ef42716
  have ef255215 (X0 X1 X2 X3 : G) :
      X1 ◇ (dr X3 ((dr (wf X1 (wf X0 X3)) X2) ◇ (wf (dl X0 X1) X1))) = X2 := by
    first | exact superpose ef139326 ef254962 | exact superpose ef254962 ef139326
  have ef255399 (X0 X1 X2 X3 : G) :
      X1 ◇ (((wf (dl X0 X1) X1) ◇ X3) ◇ (dr (wf X1 (wf X0 X3)) X2)) = X2 := by
    first | exact superpose ef40 ef255215 | exact superpose ef255215 ef40
  have ef255533 (X0 X1 X2 X3 : G) : wf (dl X0 X1) (dl X3 (dr (wf X1 (wf X0 X3)) X2)) = X2 := by
    first | exact superpose ef51360 ef255399 | exact superpose ef255399 ef51360
  have ef255626 (X0 X1 X2 X3 : G) : wf (dl X0 X1) ((wf X1 (wf X0 X3)) ◇ (X2 ◇ X3)) = X2 := by
    first | exact superpose ef119 ef255533 | exact superpose ef255533 ef119
  have ef424863 (X0 X1 X2 X3 : G) :
      X2 ◇ ((X0 ◇ (wf X1 X3)) ◇ X1) = (dr X0 X1) ◇ (dl X2 (X1 ◇ X3)) := by
    first | exact superpose ef8097 ef532 | exact superpose ef532 ef8097
  have ef424895 (X0 X1 X2 X3 : G) :
      X1 ◇ (dl (dr X0 X1) (X2 ◇ X3)) = X2 ◇ ((X0 ◇ (wf X1 X3)) ◇ X1) := by
    first | exact superpose ef20160 ef424863 | exact superpose ef424863 ef20160
  have ef448129 (X0 X1 : G) : wf (wf X1 X0) X1 = (wf ((wf X1 X0) ◇ X1) ((wf X1 X0) ◇ X1)) ◇ X0 := by
    first | exact superpose ef10126 ef17780 | exact superpose ef17780 ef10126
  have ef448214 (X0 X1 : G) : wf (wf X1 X0) X1 = (dr ((wf X1 X0) ◇ X1) X0) ◇ ((wf X1 X0) ◇ X1) := by
    first | exact superpose ef16863 ef448129 | exact superpose ef448129 ef16863
  have ef448330 (X0 X1 : G) :
      wf (wf X1 X0) X1 = (dr X0 X1) ◇ (dl (dr ((wf X1 X0) ◇ X1) X0) X1) := by
    first | exact superpose ef20199 ef448214 | exact superpose ef448214 ef20199
  have ef448419 (X0 X1 : G) :
      wf (wf X1 X0) X1 = (dr X0 X1) ◇ (dl (dr X1 X0) ((wf X1 X0) ◇ X1)) := by
    first | exact superpose ef89266 ef448330 | exact superpose ef448330 ef89266
  have ef448463 (X0 X1 : G) :
      wf (wf X1 X0) X1 = (wf X1 X0) ◇ (dl (dr X0 X1) ((dr X1 X0) ◇ X1)) := by
    first | exact superpose ef20160 ef448419 | exact superpose ef448419 ef20160
  have ef448490 (X0 X1 : G) : wf (wf X1 X0) X1 = (wf X1 X0) ◇ ((wf X1 ((dr X0 X1) ◇ X0)) ◇ X1) := by
    first | exact superpose ef96320 ef448463 | exact superpose ef448463 ef96320
  have ef448503 (X0 X1 : G) : wf (wf X1 X0) X1 = dl (dr X0 ((dr X0 X1) ◇ X0)) X1 := by
    first | exact superpose ef141943 ef448490 | exact superpose ef448490 ef141943
  have ef448516 (X0 X1 : G) : wf (wf X1 X0) X1 = dl ((X0 ◇ X0) ◇ (dr X0 X1)) X1 := by
    first | exact superpose ef40 ef448503 | exact superpose ef448503 ef40
  have ef448526 (X0 X1 : G) : wf (wf X1 X0) X1 = (X1 ◇ (dl X0 (dr X0 X1))) ◇ X0 := by
    first | exact superpose ef283 ef448516 | exact superpose ef448516 ef283
  have ef448531 (X0 X1 : G) : wf (wf X1 X0) X1 = (dr X0 X1) ◇ (dr (X0 ◇ X1) X0) := by
    first | exact superpose ef4370 ef448526 | exact superpose ef448526 ef4370
  have ef448534 (X0 X1 : G) : wf (wf X1 X0) X1 = (wf X0 X1) ◇ (dl (dr X0 X1) X0) := by
    first | exact superpose ef42683 ef448531 | exact superpose ef448531 ef42683
  have ef448536 (X0 X1 : G) : (wf X0 X1) ◇ X1 = wf (wf X1 X0) X1 := by
    first | exact superpose ef22 ef448534 | exact superpose ef448534 ef22
  have ef448594 (X0 X1 X2 : G) : wf (wf X1 X0) X2 = X1 ◇ (dl X2 ((wf X0 X1) ◇ X1)) := by
    first | exact superpose ef448536 ef23648 | exact superpose ef23648 ef448536
  have ef448596 (X0 X1 X2 : G) : dr ((wf X0 X1) ◇ X1) (dl X2 (wf (wf X1 X0) X2)) = X1 := by
    first | exact superpose ef448536 ef24465 | exact superpose ef24465 ef448536
  have ef448615 (X0 X1 : G) : dr (wf (wf X1 X0) (wf X0 X1)) X1 = X1 := by
    first | exact superpose ef119005 ef448596 | exact superpose ef448596 ef119005
  have ef518795 (X0 : G) : wf (X0 ◇ (wf X0 X0)) (X0 ◇ X0) = X0 := by
    first | exact superpose ef448615 ef129733 | exact superpose ef129733 ef448615
  have ef535626 (X0 X1 X2 X3 : G) : wf (X1 ◇ X2) (X0 ◇ X3) = (wf X1 X0) ◇ (wf X2 X3) := by
    first | exact superpose ef16 ef173832 | exact superpose ef173832 ef16
  have ef547220 (X0 X1 X2 : G) :
      wf (dl (X0 ◇ (wf X0 X0)) X1) ((wf X1 X0) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := by
    first | exact superpose ef518795 ef255626 | exact superpose ef255626 ef518795
  have ef547465 (X0 X1 X2 : G) :
      wf (dl (X0 ◇ (wf X0 X0)) X1) (X0 ◇ (X2 ◇ (X0 ◇ (wf X1 X0)))) = X2 := by
    first | exact superpose ef205335 ef547220 | exact superpose ef547220 ef205335
  have ef547566 (X0 X1 X2 : G) :
      wf ((wf X0 X0) ◇ (dr X0 X1)) (X0 ◇ (X2 ◇ (X0 ◇ (wf X1 X0)))) = X2 := by
    first | exact superpose ef618 ef547465 | exact superpose ef547465 ef618
  have ef547621 (X0 X1 X2 : G) :
      (wf (wf X0 X0) X0) ◇ (wf (dr X0 X1) (X2 ◇ (X0 ◇ (wf X1 X0)))) = X2 := by
    first | exact superpose ef535626 ef547566 | exact superpose ef547566 ef535626
  have ef547649 (X0 X1 X2 : G) :
      (wf (wf X0 X0) X0) ◇ ((X2 ◇ (wf ((dr X0 X1) ◇ X1) X0)) ◇ X0) = X2 := by
    first | exact superpose ef164889 ef547621 | exact superpose ef547621 ef164889
  have ef547665 (X0 X2 : G) : (wf (wf X0 X0) X0) ◇ ((X2 ◇ (wf X0 X0)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef547649 | exact superpose ef547649 ef15
  have ef547676 (X0 X2 : G) : X0 ◇ (dl (dr X2 X0) ((wf (wf X0 X0) X0) ◇ X0)) = X2 := by
    first | exact superpose ef424895 ef547665 | exact superpose ef547665 ef424895
  have ef547684 (X0 X2 : G) : wf (wf X0 (wf X0 X0)) (dr X2 X0) = X2 := by
    first | exact superpose ef448594 ef547676 | exact superpose ef547676 ef448594
  have ef548259 (X0 X1 : G) : X1 ◇ X0 = wf (wf X0 (wf X0 X0)) X1 := by
    first | exact superpose ef547684 ef51340 | exact superpose ef51340 ef547684
  have ef549151 : x ≠ (wf x x) ◇ x := by
    first | exact superpose ef548259 ef20 | exact superpose ef20 ef548259
  subsumption ef549151 ef8082

theorem Equation1832_termStructuralFromFin_Equation898_qdiv :
    Law1832.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1832.models_iff]
    exact fun x ↦
      @qaux898_1832_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 2441 `x = (x ◇ ((x ◇ x) ◇ x)) ◇ x` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_2441_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    x = wf (wf x (wf (wf x x) x)) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf (wf x (wf (wf x x) x)) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : x ≠ wf (wf x x) x := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  subsumption ef9610 ef9311

theorem Equation2441_termStructuralFromFin_Equation898_qdiv :
    Law2441.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2441.models_iff]
    exact fun x ↦
      @qaux898_2441_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3050 `x = (((x ◇ x) ◇ x) ◇ x) ◇ x` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3050_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    x = wf (wf (wf (wf x x) x) x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf (wf (wf (wf x x) x) x) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : x ≠ wf (wf x x) x := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  subsumption ef9610 ef9311

theorem Equation3050_termStructuralFromFin_Equation898_qdiv :
    Law3050.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3050.models_iff]
    exact fun x ↦
      @qaux898_3050_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3456_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    wf x x = wf x (wf (wf x x) x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : wf x x ≠ wf x (wf (wf x x) x) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : wf x x ≠ wf x x := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  exact absurd rfl ef9610

theorem Equation3456_termStructuralFromFin_Equation898_qdiv :
    Law3456.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3456.models_iff]
    exact fun x ↦
      @qaux898_3456_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3522_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x y : G) :
    wf x y = wf x (wf (wf y y) y) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : wf x y ≠ wf x (wf (wf y y) y) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : wf x y ≠ wf x y := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  exact absurd rfl ef9610

theorem Equation3522_termStructuralFromFin_Equation898_qdiv :
    Law3522.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3522.models_iff]
    exact fun x y ↦
      @qaux898_3522_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 4065 `x ◇ x = ((x ◇ x) ◇ x) ◇ x` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_4065_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x : G) :
    wf x x = wf (wf (wf x x) x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : wf x x ≠ wf (wf (wf x x) x) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : wf x x ≠ wf x x := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  exact absurd rfl ef9610

theorem Equation4065_termStructuralFromFin_Equation898_qdiv :
    Law4065.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4065.models_iff]
    exact fun x ↦
      @qaux898_4065_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 4118 `x ◇ y = ((x ◇ x) ◇ x) ◇ y` holds of the operation `x □ y := (x◇(x/(y/x)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_4118_6 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr a (dr b a)))
    (x y : G) :
    wf x y = wf (wf (wf x x) x) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X0 (dr X1 X0)) := mod_symm (hwdef ..)
  have ef20 : wf x y ≠ wf (wf (wf x x) x) y := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef82 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X1 ◇ (dr X1 X0) := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef718 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef747 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef718 | exact superpose ef718 ef40
  have ef954 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (dr X1 ((X2 ◇ X0) ◇ (dr X1 X2))) := by
    first | exact superpose ef63 ef82 | exact superpose ef82 ef63
  have ef963 (X0 X1 X2 : G) : wf X1 X0 = X1 ◇ (((dr X1 X2) ◇ X1) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef954 | exact superpose ef954 ef40
  have ef974 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef747 ef963 | exact superpose ef963 ef747
  have ef8082 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef974 ef13 | exact superpose ef13 ef974
  have ef9244 (X0 : G) : (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef974 | exact superpose ef974 ef8082
  have ef9272 (X0 : G) : (wf X0 X0) ◇ X0 = wf (wf X0 X0) X0 := by
    first | exact superpose ef8082 ef9244 | exact superpose ef9244 ef8082
  have ef9311 (X0 : G) : wf (wf X0 X0) X0 = X0 := by
    first | exact superpose ef8082 ef9272 | exact superpose ef9272 ef8082
  have ef9610 : wf x y ≠ wf x y := by
    first | exact superpose ef9311 ef20 | exact superpose ef20 ef9311
  exact absurd rfl ef9610

theorem Equation4118_termStructuralFromFin_Equation898_qdiv :
    Law4118.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 0) (.rdv (.var 1) (.var 0)))) (.op (.op (.var 1) (.op (.var 1) (.var 1))) (.var 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4118.models_iff]
    exact fun x y ↦
      @qaux898_4118_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_6R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_6L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_6 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := (x◇(y/(y/y)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_8R [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef30 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef92 (X0 X1 : G) : dr (wf X0 X1) (dr X1 (dr X1 X1)) = X0 := by
    first | exact superpose ef20 ef17 | exact superpose ef17 ef20
  have ef100 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef176 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef20 ef30 | exact superpose ef30 ef20
  have ef968 : q = dr (wf p t) (dr t (dr t t)) := by
    first | exact superpose ef21 ef92 | exact superpose ef92 ef21
  have ef976 : q = (dr t t) ◇ ((wf p t) ◇ t) := by
    first | exact superpose ef100 ef968 | exact superpose ef968 ef100
  have ef978 : p = q := by
    first | exact superpose ef176 ef976 | exact superpose ef976 ef176
  subsumption ef978 ef22

/-- Left translation of `x □ y := (x◇(y/(y/y)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_8L [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef24 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef28 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef30 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef31 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef34 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef41 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef44 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef63 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef66 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef72 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef74 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef88 (X0 X1 X2 : G) : (dr X1 (dr X1 X1)) ◇ ((X2 ◇ X0) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef20 ef13 | exact superpose ef13 ef20
  have ef92 (X0 X1 : G) : dr (wf X0 X1) (dr X1 (dr X1 X1)) = X0 := by
    first | exact superpose ef20 ef17 | exact superpose ef17 ef20
  have ef93 (X0 X1 : G) : dr X1 (dr X1 X1) = dl X0 (wf X0 X1) := by
    first | exact superpose ef20 ef19 | exact superpose ef19 ef20
  have ef100 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef101 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef18 ef27 | exact superpose ef27 ef18
  have ef109 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef27 ef27
  have ef123 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef27 ef19 | exact superpose ef19 ef27
  have ef148 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef156 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef28 ef19 | exact superpose ef19 ef28
  have ef193 (X0 X1 X2 X3 : G) : ((X0 ◇ (dr X1 (dl X2 X3))) ◇ X1) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef30 ef28 | exact superpose ef28 ef30
  have ef239 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef31 ef19 | exact superpose ef19 ef31
  have ef240 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef31 ef27 | exact superpose ef27 ef31
  have ef269 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef27 ef34 | exact superpose ef34 ef27
  have ef274 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef275 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef34 ef34
  have ef285 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef288 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef298 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef304 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef34 ef15 | exact superpose ef15 ef34
  have ef307 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef34 ef19 | exact superpose ef19 ef34
  have ef308 (X0 X1 X2 X3 : G) : dr X3 (X1 ◇ X2) = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef314 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef44 ef308 | exact superpose ef308 ef44
  have ef317 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef240 ef304 | exact superpose ef304 ef240
  have ef432 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef40 ef20 | exact superpose ef20 ef40
  have ef435 (X0 X1 X2 X3 : G) : ((dr X1 X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef40 ef14 | exact superpose ef14 ef40
  have ef442 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef40 ef34 | exact superpose ef34 ef40
  have ef517 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef41 ef31 | exact superpose ef31 ef41
  have ef627 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef63 ef40 | exact superpose ef40 ef63
  have ef722 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef20 ef65 | exact superpose ef65 ef20
  have ef734 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ ((X2 ◇ X0) ◇ (dr X3 X2))) ◇ X0 := by
    first | exact superpose ef65 ef34 | exact superpose ef34 ef65
  have ef743 (X0 X1 X2 X3 : G) : X0 ◇ (dr X3 ((X1 ◇ X0) ◇ (dr (X2 ◇ X3) X1))) = X2 := by
    first | exact superpose ef65 ef40 | exact superpose ef40 ef65
  have ef752 (X0 X1 X2 X3 : G) : X0 ◇ (((dr (X2 ◇ X3) X1) ◇ X3) ◇ (X1 ◇ X0)) = X2 := by
    first | exact superpose ef44 ef743 | exact superpose ef743 ef44
  have ef759 (X1 X2 X3 : G) : dl X3 X1 = dl ((dr X3 X2) ◇ X2) X1 := by
    first | exact superpose ef285 ef734 | exact superpose ef734 ef285
  have ef787 (X1 X2 X3 : G) : dr ((dr (X2 ◇ X3) X1) ◇ X3) X1 = X2 := by
    first | exact superpose ef27 ef752 | exact superpose ef752 ef27
  have ef791 (X1 X2 X3 : G) : dl X3 X1 = X2 ◇ (dr (dr X3 X2) X1) := by
    first | exact superpose ef627 ef759 | exact superpose ef759 ef627
  have ef818 (X0 X1 X2 : G) : (wf ((dl (dr X0 (dr X0 X0)) X1) ◇ X2) X0) ◇ X1 = X2 := by
    first | exact superpose ef20 ef66 | exact superpose ef66 ef20
  have ef875 (X0 X1 X2 : G) : (wf ((dl (X0 ◇ (X0 ◇ X0)) X1) ◇ X2) X0) ◇ X1 = X2 := by
    first | exact superpose ef100 ef818 | exact superpose ef818 ef100
  have ef891 (X0 X1 X2 : G) : (wf (((X0 ◇ X0) ◇ (dr X0 X1)) ◇ X2) X0) ◇ X1 = X2 := by
    first | exact superpose ef627 ef875 | exact superpose ef875 ef627
  have ef904 (X0 X1 X2 X3 : G) : X1 ◇ X2 = dl (X0 ◇ X1) ((X0 ◇ (dr X3 X2)) ◇ X3) := by
    first | exact superpose ef30 ef74 | exact superpose ef74 ef30
  have ef913 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef40 ef74 | exact superpose ef74 ef40
  have ef915 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef74 | exact superpose ef74 ef31
  have ef945 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef274 ef915 | exact superpose ef915 ef274
  have ef946 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef123 ef913 | exact superpose ef913 ef123
  have ef955 (X0 X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef274 ef904 | exact superpose ef904 ef274
  have ef959 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef34 ef945 | exact superpose ef945 ef34
  have ef962 (X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ (dl X1 X3) := by
    first | exact superpose ef34 ef955 | exact superpose ef955 ef34
  have ef968 : t = dr (wf t p) (dr q (dr q q)) := by
    first | exact superpose ef21 ef92 | exact superpose ef92 ef21
  have ef976 : t = (dr q q) ◇ ((wf t p) ◇ q) := by
    first | exact superpose ef100 ef968 | exact superpose ef968 ef100
  have ef981 : dr q (dr q q) = dl t (wf t p) := by
    first | exact superpose ef21 ef93 | exact superpose ef93 ef21
  have ef1002 : dr q (dr q q) = dr p (dr p p) := by
    first | exact superpose ef93 ef981 | exact superpose ef981 ef93
  have ef1006 : dr q (dr q q) = p ◇ (p ◇ p) := by
    first | exact superpose ef100 ef1002 | exact superpose ef1002 ef100
  have ef1008 : p ◇ (p ◇ p) = q ◇ (q ◇ q) := by
    first | exact superpose ef100 ef1006 | exact superpose ef1006 ef100
  have ef1422 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef15 ef101 | exact superpose ef101 ef15
  have ef1423 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef34 ef101 | exact superpose ef101 ef34
  have ef1425 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef16 ef101 | exact superpose ef101 ef16
  have ef1427 (X0 X1 X2 X3 : G) : dr (dl X1 X3) X2 = (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) := by
    first | exact superpose ef101 ef101
  have ef1435 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef101 ef27 | exact superpose ef27 ef101
  have ef1447 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef101 ef27 | exact superpose ef27 ef101
  have ef1490 (X0 X1 X2 X3 : G) : (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) = X3 ◇ (dr X2 X1) := by
    first | exact superpose ef1435 ef1427 | exact superpose ef1427 ef1435
  have ef1493 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef959 ef1423 | exact superpose ef1423 ef959
  have ef1522 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef239 ef1493 | exact superpose ef1493 ef239
  have ef1532 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef27 ef1522 | exact superpose ef1522 ef27
  have ef2117 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) ◇ (X0 ◇ X1) = X3 := by
    first | exact superpose ef30 ef72 | exact superpose ef72 ef30
  have ef2257 (X0 X2 X3 X4 : G) : dr X0 (dl X2 (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) = X3 := by
    first | exact superpose ef240 ef2117 | exact superpose ef2117 ef240
  have ef2360 (X0 X2 X3 X4 : G) : dr X0 ((X0 ◇ (dr X4 X2)) ◇ ((dr X4 X3) ◇ X2)) = X3 := by
    first | exact superpose ef442 ef2257 | exact superpose ef2257 ef442
  have ef2434 (X0 X2 X3 X4 : G) : (((dr X4 X3) ◇ X2) ◇ X0) ◇ (X0 ◇ (dr X4 X2)) = X3 := by
    first | exact superpose ef44 ef2360 | exact superpose ef2360 ef44
  have ef2480 (X2 X3 X4 : G) : dl (dr X4 X2) ((dr X4 X3) ◇ X2) = X3 := by
    first | exact superpose ef34 ef2434 | exact superpose ef2434 ef34
  have ef2586 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (wf X2 X1) = dl (dr X1 (dr X1 X1)) X0 := by
    first | exact superpose ef88 ef19 | exact superpose ef19 ef88
  have ef2629 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (wf X2 X1) = dl (X1 ◇ (X1 ◇ X1)) X0 := by
    first | exact superpose ef100 ef2586 | exact superpose ef2586 ef100
  have ef2684 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (wf X2 X1) = (X1 ◇ X1) ◇ (dr X1 X0) := by
    first | exact superpose ef627 ef2629 | exact superpose ef2629 ef627
  have ef2751 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef27 ef148 | exact superpose ef148 ef27
  have ef2808 (X0 X1 X2 X3 : G) : (X2 ◇ (dr X0 X1)) ◇ X3 = (dl (X3 ◇ X2) X1) ◇ X0 := by
    first | exact superpose ef148 ef14 | exact superpose ef14 ef148
  have ef2810 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef148 ef30 | exact superpose ef30 ef148
  have ef2811 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (dr X2 (dr X2 X2)) ◇ (dr X0 X1) := by
    first | exact superpose ef148 ef88 | exact superpose ef88 ef148
  have ef2812 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ (X2 ◇ X2)) ◇ (dr X0 X1) := by
    first | exact superpose ef100 ef2811 | exact superpose ef2811 ef100
  have ef2814 (X0 X1 X2 X3 : G) : (X2 ◇ (dr X0 X1)) ◇ X3 = (X2 ◇ (dr X3 X1)) ◇ X0 := by
    first | exact superpose ef627 ef2808 | exact superpose ef2808 ef627
  have ef2861 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1532 ef2751 | exact superpose ef2751 ef1532
  have ef2894 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef44 ef2861 | exact superpose ef2861 ef44
  have ef2909 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef101 ef2894 | exact superpose ef2894 ef101
  have ef3173 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef156 ef19 | exact superpose ef19 ef156
  have ef4736 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef148 ef298 | exact superpose ef298 ef148
  have ef4788 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef44 ef4736 | exact superpose ef4736 ef44
  have ef4839 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef627 ef4788 | exact superpose ef4788 ef627
  have ef4866 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef34 ef4839 | exact superpose ef4839 ef34
  have ef5046 (X0 X1 X2 : G) : dr X1 (dl X2 X0) = dr X0 (dl X2 X1) := by
    first | exact superpose ef317 ef17 | exact superpose ef17 ef317
  have ef5277 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef63 ef432 | exact superpose ef432 ef63
  have ef5286 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef123 ef5277 | exact superpose ef5277 ef123
  have ef5853 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) ◇ X2 = dl (X0 ◇ (dr X1 X2)) X3 := by
    first | exact superpose ef627 ef239 | exact superpose ef239 ef627
  have ef5874 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) ◇ X2 = (dr X1 X2) ◇ (dr X0 X3) := by
    first | exact superpose ef627 ef5853 | exact superpose ef5853 ef627
  have ef6177 (X0 X1 X2 : G) : X0 ◇ X2 = (dr (X0 ◇ X1) X2) ◇ X1 := by
    first | exact superpose ef787 ef16 | exact superpose ef16 ef787
  have ef6495 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (dr X3 X2) = dr (dr (dr X0 X2) X1) X3 := by
    first | exact superpose ef791 ef109 | exact superpose ef109 ef791
  have ef6544 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (dr X3 X2) = (dl X3 X1) ◇ (dr X0 X2) := by
    first | exact superpose ef1425 ef6495 | exact superpose ef6495 ef1425
  have ef7848 (X0 X1 : G) : dl X0 X1 = (wf (X0 ◇ X1) X1) ◇ X1 := by
    first | exact superpose ef962 ef722 | exact superpose ef722 ef962
  have ef7986 : dr q q = (q ◇ t) ◇ (wf t p) := by
    first | exact superpose ef976 ef14 | exact superpose ef14 ef976
  have ef8065 : dr q q = (p ◇ p) ◇ (dr p q) := by
    first | exact superpose ef2684 ef7986 | exact superpose ef7986 ef2684
  have ef9211 : q = (q ◇ (p ◇ (p ◇ p))) ◇ q := by
    first | exact superpose ef1008 ef14 | exact superpose ef14 ef1008
  have ef9222 (X0 : G) : (X0 ◇ q) ◇ (p ◇ (p ◇ p)) = dl (q ◇ q) X0 := by
    first | exact superpose ef1008 ef34 | exact superpose ef34 ef1008
  have ef9241 (X0 : G) : dr (q ◇ q) X0 = (p ◇ (p ◇ p)) ◇ (dr X0 q) := by
    first | exact superpose ef1008 ef109 | exact superpose ef109 ef1008
  have ef9262 (X0 : G) : dr (q ◇ q) X0 = dl (wf X0 p) q := by
    first | exact superpose ef2812 ef9241 | exact superpose ef9241 ef2812
  have ef9281 (X0 : G) : (X0 ◇ q) ◇ (p ◇ (p ◇ p)) = q ◇ (dr q X0) := by
    first | exact superpose ef627 ef9222 | exact superpose ef9222 ef627
  have ef9291 : q = (dr p q) ◇ (dr (p ◇ p) q) := by
    first | exact superpose ef5874 ef9211 | exact superpose ef9211 ef5874
  have ef9322 (X0 : G) : q ◇ (dr q X0) = p ◇ (p ◇ (p ◇ (X0 ◇ q))) := by
    first | exact superpose ef946 ef9281 | exact superpose ef9281 ef946
  have ef9353 (X0 : G) : q ◇ (dr q X0) = wf (X0 ◇ q) p := by
    first | exact superpose ef5286 ef9322 | exact superpose ef9322 ef5286
  have ef23875 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef2909 ef959 | exact superpose ef959 ef2909
  have ef34550 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = dr ((X2 ◇ (dr X5 (dl X0 X1))) ◇ X5) (dl X3 X4) := by
    first | exact superpose ef193 ef240 | exact superpose ef240 ef193
  have ef34921 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = (dl (dl X3 X4) (X5 ◇ X2)) ◇ (dr X5 (dl X0 X1)) := by
    first | exact superpose ef1422 ef34550 | exact superpose ef34550 ef1422
  have ef35218 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr (dl X3 X4) (dl X0 X1)) = (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 := by
    first | exact superpose ef1490 ef34921 | exact superpose ef34921 ef1490
  have ef35457 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (dr (dl X0 X1) X3)) := by
    first | exact superpose ef1435 ef35218 | exact superpose ef35218 ef1435
  have ef35620 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (X1 ◇ (dr X3 X0))) := by
    first | exact superpose ef1435 ef35457 | exact superpose ef35457 ef1435
  have ef38243 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = dl (dl X0 X1) (dl X4 (dr X2 X3)) := by
    first | exact superpose ef269 ef307 | exact superpose ef307 ef269
  have ef38280 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = (dl (dr X2 X3) (dl X0 X1)) ◇ X4 := by
    first | exact superpose ef3173 ef38243 | exact superpose ef38243 ef3173
  have ef38564 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ ((dr X4 (dl X0 X1)) ◇ X2) := by
    first | exact superpose ef2810 ef38280 | exact superpose ef38280 ef2810
  have ef38808 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ (X0 ◇ (dl (dr X4 X2) X1)) := by
    first | exact superpose ef23875 ef38564 | exact superpose ef38564 ef23875
  have ef50087 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ (dl X3 X4)) ◇ X5 = X1 ◇ ((X2 ◇ X0) ◇ ((X5 ◇ X3) ◇ X4)) := by
    first | exact superpose ef288 ef274 | exact superpose ef274 ef288
  have ef50118 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ ((X5 ◇ X3) ◇ X4)) = X1 ◇ ((dl X3 X4) ◇ (X0 ◇ (dr X2 X5))) := by
    first | exact superpose ef35620 ef50087 | exact superpose ef50087 ef35620
  have ef55245 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ X2 = dl (dr (X0 ◇ X2) X1) X2 := by
    first | exact superpose ef6177 ef7848 | exact superpose ef7848 ef6177
  have ef55543 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ X2 = dl (dr X2 X1) (X0 ◇ X2) := by
    first | exact superpose ef4866 ef55245 | exact superpose ef55245 ef4866
  have ef60715 (X0 X1 X2 X3 X4 X5 : G) :
      (((dr X1 X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ (dl (X2 ◇ (X3 ◇ X1)) X5)) := by
    first | exact superpose ef435 ef314 | exact superpose ef314 ef435
  have ef60801 (X0 X1 X2 X3 X4 X5 : G) :
      (((dr X1 X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) := by
    first | exact superpose ef627 ef60715 | exact superpose ef60715 ef627
  have ef61205 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) = X0 ◇ (X4 ◇ (dl (dr X5 (dr X1 X2)) X3)) := by
    first | exact superpose ef38808 ef60801 | exact superpose ef60801 ef38808
  have ef61579 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) = X0 ◇ (X4 ◇ (dl (X2 ◇ (X5 ◇ X1)) X3)) := by
    first | exact superpose ef100 ef61205 | exact superpose ef61205 ef100
  have ef61918 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (dr X2 X5))) = X0 ◇ (X4 ◇ ((X5 ◇ X1) ◇ (dr X2 X3))) := by
    first | exact superpose ef627 ef61579 | exact superpose ef61579 ef627
  have ef62874 (X0 : G) : dl (dr p q) (X0 ◇ p) = (dl p X0) ◇ (dr q q) := by
    first | exact superpose ef8065 ef275 | exact superpose ef275 ef8065
  have ef62881 (X0 : G) : (dl p X0) ◇ (dr q q) = (wf (X0 ◇ q) p) ◇ p := by
    first | exact superpose ef55543 ef62874 | exact superpose ef62874 ef55543
  have ef62986 (X0 : G) : (dl p X0) ◇ (dr q q) = (q ◇ (dr q X0)) ◇ p := by
    first | exact superpose ef9353 ef62881 | exact superpose ef62881 ef9353
  have ef63086 (X0 : G) : (dl p X0) ◇ (dr q q) = (q ◇ (dr p X0)) ◇ q := by
    first | exact superpose ef2814 ef62986 | exact superpose ef62986 ef2814
  have ef88699 (X0 : G) : (dl q X0) ◇ (dr p q) = dl X0 (dr (p ◇ p) q) := by
    first | exact superpose ef9291 ef517 | exact superpose ef517 ef9291
  have ef88758 (X0 : G) : (dl q X0) ◇ (dr p q) = (p ◇ p) ◇ (q ◇ X0) := by
    first | exact superpose ef123 ef88699 | exact superpose ef88699 ef123
  have ef88861 (X0 : G) : (dl p X0) ◇ (dr q q) = (p ◇ p) ◇ (q ◇ X0) := by
    first | exact superpose ef6544 ef88758 | exact superpose ef88758 ef6544
  have ef93710 : q = (q ◇ (dr q (dr p p))) ◇ p := by
    first | exact superpose ef9353 ef722 | exact superpose ef722 ef9353
  have ef93775 : q = (q ◇ (dr p (dr p p))) ◇ q := by
    first | exact superpose ef2814 ef93710 | exact superpose ef93710 ef2814
  have ef93843 : q = (dl p (dr p p)) ◇ (dr q q) := by
    first | exact superpose ef63086 ef93775 | exact superpose ef93775 ef63086
  have ef93906 : q = (p ◇ p) ◇ (q ◇ (dr p p)) := by
    first | exact superpose ef88861 ef93843 | exact superpose ef93843 ef88861
  have ef93955 : q = dr q (dl p p) := by
    first | exact superpose ef1447 ef93906 | exact superpose ef93906 ef1447
  have ef93986 : q = dr p (dl p q) := by
    first | exact superpose ef5046 ef93955 | exact superpose ef93955 ef5046
  have ef96740 (X0 : G) : dl X0 q = p ◇ ((dl p q) ◇ X0) := by
    first | exact superpose ef93986 ef123 | exact superpose ef123 ef93986
  have ef96753 (X0 : G) : (wf (((p ◇ p) ◇ q) ◇ X0) p) ◇ (dl p q) = X0 := by
    first | exact superpose ef93986 ef891 | exact superpose ef891 ef93986
  have ef96776 (X0 : G) : p ◇ (dl (wf (((p ◇ p) ◇ q) ◇ X0) p) q) = X0 := by
    first | exact superpose ef959 ef96753 | exact superpose ef96753 ef959
  have ef96802 (X0 : G) : p ◇ (dr (q ◇ q) (((p ◇ p) ◇ q) ◇ X0)) = X0 := by
    first | exact superpose ef9262 ef96776 | exact superpose ef96776 ef9262
  have ef96820 (X0 : G) : p ◇ ((X0 ◇ (q ◇ q)) ◇ ((p ◇ p) ◇ q)) = X0 := by
    first | exact superpose ef44 ef96802 | exact superpose ef96802 ef44
  have ef96829 (X0 : G) : p ◇ ((dl p q) ◇ ((q ◇ q) ◇ (dr X0 p))) = X0 := by
    first | exact superpose ef50118 ef96820 | exact superpose ef96820 ef50118
  have ef96835 (X0 : G) : p ◇ ((dl p q) ◇ ((p ◇ q) ◇ (dr X0 q))) = X0 := by
    first | exact superpose ef61918 ef96829 | exact superpose ef96829 ef61918
  have ef96839 (X0 : G) : dl ((p ◇ q) ◇ (dr X0 q)) q = X0 := by
    first | exact superpose ef96740 ef96835 | exact superpose ef96835 ef96740
  have ef96842 (X0 : G) : (dr X0 q) ◇ p = X0 := by
    first | exact superpose ef74 ef96839 | exact superpose ef96839 ef74
  have ef96845 (X0 : G) : (dr X0 p) ◇ q = X0 := by
    first | exact superpose ef2909 ef96842 | exact superpose ef96842 ef2909
  have ef104598 (X0 : G) : p = dl (dr X0 q) X0 := by
    first | exact superpose ef96845 ef2480 | exact superpose ef2480 ef96845
  have ef104599 : p = q := by
    first | exact superpose ef24 ef104598 | exact superpose ef104598 ef24
  subsumption ef104599 ef22

/-- The operation comes back: `x ◇ y = (x◇((y◇y)◇y))` read in `□` and its divisions, where
`x □ y := (x◇(y/(y/y)))`. With `winj898_8` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back898_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wf x (wf (wf y y) y)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef16 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef19 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef22 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef24 (X0 X1 : G) : wf (wdr X0 X1) X1 = X0 := mod_symm (hwrs ..)
  have ef25 (X0 X1 : G) : wdr (wf X0 X1) X1 = X0 := mod_symm (hwri ..)
  have ef26 (X0 X1 : G) : wf X0 (wdl X0 X1) = X1 := mod_symm (hwls ..)
  have ef27 (X0 X1 : G) : wdl X0 (wf X0 X1) = X1 := mod_symm (hwli ..)
  have ef28 : wf x (wf (wf y y) y) ≠ x ◇ y := mod_symm nh
  have ef29 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef21 ef20 | exact superpose ef20 ef21
  have ef30 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef19 ef22 | exact superpose ef22 ef19
  have ef32 (X0 X1 : G) : wdl (wdr X0 X1) X0 = X1 := by
    first | exact superpose ef24 ef27 | exact superpose ef27 ef24
  have ef33 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef34 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef36 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef37 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef40 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef46 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef50 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef71 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef73 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef19 ef18 | exact superpose ef18 ef19
  have ef74 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef82 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef96 (X0 X1 : G) : wf (dr X0 (dr X1 (dr X1 X1))) X1 = X0 := by
    first | exact superpose ef23 ef19 | exact superpose ef19 ef23
  have ef98 (X0 X1 X2 : G) : (dr X1 (dr X1 X1)) ◇ ((X2 ◇ X0) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef23 ef16 | exact superpose ef16 ef23
  have ef100 (X0 X1 X2 : G) : (((dr X1 (dr X1 X1)) ◇ X2) ◇ X0) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef103 (X0 X1 : G) : dr X1 (dr X1 X1) = dl X0 (wf X0 X1) := by
    first | exact superpose ef23 ef22 | exact superpose ef22 ef23
  have ef112 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef19 ef33 | exact superpose ef33 ef19
  have ef113 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef21 ef33 | exact superpose ef33 ef21
  have ef121 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef33 ef33
  have ef135 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef33 ef22 | exact superpose ef22 ef33
  have ef136 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X3 := by
    first | exact superpose ef33 ef18 | exact superpose ef18 ef33
  have ef160 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef34 ef33 | exact superpose ef33 ef34
  have ef168 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef34 ef22 | exact superpose ef22 ef34
  have ef188 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef23 ef36 | exact superpose ef36 ef23
  have ef202 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef36 ef22 | exact superpose ef22 ef36
  have ef242 (X0 X1 X2 : G) : (dl X1 (dr X2 (dr X2 X2))) ◇ (wf (X0 ◇ X1) X2) = X0 := by
    first | exact superpose ef23 ef37 | exact superpose ef37 ef23
  have ef251 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef37 ef22 | exact superpose ef22 ef37
  have ef252 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef37 ef33 | exact superpose ef33 ef37
  have ef260 (X0 X1 X2 : G) : (X2 ◇ ((dr X2 X2) ◇ X1)) ◇ (wf (X0 ◇ X1) X2) = X0 := by
    first | exact superpose ef135 ef242 | exact superpose ef242 ef135
  have ef284 (X0 X1 X2 : G) : dl X2 X0 = (wf X0 X1) ◇ ((dr X1 (dr X1 X1)) ◇ X2) := by
    first | exact superpose ef23 ef40 | exact superpose ef40 ef23
  have ef286 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef18 ef40 | exact superpose ef40 ef18
  have ef297 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef18 ef40 | exact superpose ef40 ef18
  have ef298 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) X2 = (X2 ◇ (X1 ◇ X3)) ◇ (dl X0 X1) := by
    first | exact superpose ef40 ef40
  have ef300 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef37 ef40 | exact superpose ef40 ef37
  have ef315 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1))) ◇ (X1 ◇ X2) = X3 := by
    first | exact superpose ef40 ef17 | exact superpose ef17 ef40
  have ef316 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef40 ef18 | exact superpose ef18 ef40
  have ef329 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef252 ef316 | exact superpose ef316 ef252
  have ef330 (X0 X1 X3 : G) : dr X1 (dl X0 (X3 ◇ (dl X0 X1))) = X3 := by
    first | exact superpose ef252 ef315 | exact superpose ef315 ef252
  have ef343 (X0 X1 X2 : G) : dl X2 X0 = (wf X0 X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2) := by
    first | exact superpose ef112 ef284 | exact superpose ef284 ef112
  have ef444 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef46 ef23 | exact superpose ef23 ef46
  have ef454 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef46 ef40 | exact superpose ef40 ef46
  have ef455 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef46 ef40 | exact superpose ef40 ef46
  have ef597 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef18 ef50 | exact superpose ef50 ef18
  have ef613 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef252 ef597 | exact superpose ef597 ef252
  have ef639 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef71 ef46 | exact superpose ef46 ef71
  have ef734 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef23 ef73 | exact superpose ef73 ef23
  have ef844 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef74 ef40 | exact superpose ef40 ef74
  have ef875 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef297 ef844 | exact superpose ef844 ef297
  have ef899 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef639 ef875 | exact superpose ef875 ef639
  have ef916 (X0 X1 X2 X3 : G) : X1 ◇ X2 = dl (X0 ◇ X1) ((X0 ◇ (dr X3 X2)) ◇ X3) := by
    first | exact superpose ef36 ef82 | exact superpose ef82 ef36
  have ef925 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef46 ef82 | exact superpose ef82 ef46
  have ef927 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef37 ef82 | exact superpose ef82 ef37
  have ef937 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2 = dl (dr X0 X1) X3 := by
    first | exact superpose ef33 ef82 | exact superpose ef82 ef33
  have ef957 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef286 ef927 | exact superpose ef927 ef286
  have ef958 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef135 ef925 | exact superpose ef925 ef135
  have ef967 (X0 X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef286 ef916 | exact superpose ef916 ef286
  have ef971 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef957 | exact superpose ef957 ef40
  have ef974 (X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef967 | exact superpose ef967 ef40
  have ef979 (X0 X1 : G) : wdr X0 X1 = dr X0 (dr X1 (dr X1 X1)) := by
    first | exact superpose ef96 ef25 | exact superpose ef25 ef96
  have ef980 (X0 X1 : G) : wdr X0 X1 = (dr X1 X1) ◇ (X0 ◇ X1) := by
    first | exact superpose ef112 ef979 | exact superpose ef979 ef112
  have ef999 (X0 X1 X2 : G) : dr (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ X1) = dl X2 (wf X2 (X1 ◇ X0)) := by
    first | exact superpose ef50 ef103 | exact superpose ef103 ef50
  have ef1000 (X0 X1 X2 : G) : dl X0 (wf X0 X1) = dl X2 (wf X2 X1) := by
    first | exact superpose ef103 ef103
  have ef1001 (X0 X1 : G) : dr X1 (dr X1 X1) = dl (wdr X0 X1) X0 := by
    first | exact superpose ef24 ef103 | exact superpose ef103 ef24
  have ef1004 (X0 X1 X2 : G) : wf (dr X2 (dl X0 (wf X0 X1))) X1 = X2 := by
    first | exact superpose ef103 ef96 | exact superpose ef96 ef103
  have ef1005 (X0 X1 X2 : G) : wf X2 X1 = X2 ◇ (dl X0 (wf X0 X1)) := by
    first | exact superpose ef103 ef23 | exact superpose ef23 ef103
  have ef1009 (X0 X1 : G) : dr X1 X1 = dl (dl X0 (wf X0 X1)) X1 := by
    first | exact superpose ef103 ef30 | exact superpose ef30 ef103
  have ef1019 (X0 X1 : G) : dr X1 X1 = (X1 ◇ X0) ◇ (wf X0 X1) := by
    first | exact superpose ef251 ef1009 | exact superpose ef1009 ef251
  have ef1023 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dl (wdr X0 X1) X0 := by
    first | exact superpose ef112 ef1001 | exact superpose ef1001 ef112
  have ef1024 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)) = dl X2 (wf X2 (X1 ◇ X0)) := by
    first | exact superpose ef50 ef999 | exact superpose ef999 ef50
  have ef1028 (X0 X1 X2 : G) : dl X2 (wf X2 (X1 ◇ X0)) = X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef958 ef1024 | exact superpose ef1024 ef958
  have ef1394 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (wf X1 X0) := by
    first | exact superpose ef112 ef103 | exact superpose ef103 ef112
  have ef1397 (X0 X1 : G) : wf X1 X0 = X1 ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef112 ef23 | exact superpose ef23 ef112
  have ef1746 (X0 X1 X2 X3 : G) : dr X3 X1 = (dl X1 (X2 ◇ ((dl X0 X2) ◇ X3))) ◇ X0 := by
    first | exact superpose ef34 ef113 | exact superpose ef113 ef34
  have ef1756 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef40 ef113 | exact superpose ef113 ef40
  have ef1758 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef46 ef113 | exact superpose ef113 ef46
  have ef1770 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef113 ef33 | exact superpose ef33 ef113
  have ef1831 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef135 ef1758 | exact superpose ef1758 ef135
  have ef1833 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef971 ef1756 | exact superpose ef1756 ef971
  have ef1842 (X0 X1 X2 X3 : G) : dr X3 X1 = ((dl X0 X2) ◇ ((dr X3 X2) ◇ X1)) ◇ X0 := by
    first | exact superpose ef454 ef1746 | exact superpose ef1746 ef454
  have ef1865 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef251 ef1833 | exact superpose ef1833 ef251
  have ef1868 (X1 X2 X3 : G) : dr X3 X1 = dr ((dr X3 X2) ◇ X1) X2 := by
    first | exact superpose ef160 ef1842 | exact superpose ef1842 ef160
  have ef1878 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef33 ef1865 | exact superpose ef1865 ef33
  have ef2583 (X0 X1 X2 X3 : G) :
      X1 ◇ (dr X2 (dr X2 X2)) = dl (X0 ◇ X1) ((X0 ◇ X3) ◇ (wf X3 X2)) := by
    first | exact superpose ef98 ef82 | exact superpose ef82 ef98
  have ef2588 (X0 X1 X2 X3 : G) :
      X1 ◇ (dr X2 (dr X2 X2)) = X3 ◇ (((wf X3 X2) ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef286 ef2583 | exact superpose ef2583 ef286
  have ef2647 (X1 X2 X3 : G) : X1 ◇ (dr X2 (dr X2 X2)) = X3 ◇ (dl X1 (wf X3 X2)) := by
    first | exact superpose ef40 ef2588 | exact superpose ef2588 ef40
  have ef2686 (X1 X2 X3 : G) : wf X1 X2 = X3 ◇ (dl X1 (wf X3 X2)) := by
    first | exact superpose ef23 ef2647 | exact superpose ef2647 ef23
  have ef2971 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef33 ef160 | exact superpose ef160 ef33
  have ef3083 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1878 ef2971 | exact superpose ef2971 ef1878
  have ef3117 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef50 ef3083 | exact superpose ef3083 ef50
  have ef3132 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef113 ef3117 | exact superpose ef3117 ef113
  have ef3203 (X0 X1 X2 X3 : G) :
      dr (wf X1 X2) X3 = X0 ◇ (dr X3 (((dr X2 (dr X2 X2)) ◇ X0) ◇ X1)) := by
    first | exact superpose ef100 ef121 | exact superpose ef121 ef100
  have ef3218 (X0 X1 X2 X3 : G) :
      dr (wf X1 X2) X3 = X0 ◇ ((X1 ◇ X3) ◇ ((dr X2 (dr X2 X2)) ◇ X0)) := by
    first | exact superpose ef50 ef3203 | exact superpose ef3203 ef50
  have ef3273 (X1 X2 X3 : G) : dr (wf X1 X2) X3 = dr (X1 ◇ X3) (dr X2 (dr X2 X2)) := by
    first | exact superpose ef33 ef3218 | exact superpose ef3218 ef33
  have ef3319 (X1 X2 X3 : G) : dr (wf X1 X2) X3 = (dr X2 X2) ◇ ((X1 ◇ X3) ◇ X2) := by
    first | exact superpose ef112 ef3273 | exact superpose ef3273 ef112
  have ef3347 (X1 X2 X3 : G) : dr (wf X1 X2) X3 = wdr (X1 ◇ X3) X2 := by
    first | exact superpose ef980 ef3319 | exact superpose ef3319 ef980
  have ef3410 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef168 ef22 | exact superpose ef22 ef168
  have ef4010 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef202 ef17 | exact superpose ef17 ef202
  have ef5091 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef329 ef82 | exact superpose ef82 ef329
  have ef5108 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3410 ef5091 | exact superpose ef5091 ef3410
  have ef5303 (X0 X1 : G) : dl X1 (dr X0 X0) = wf (dl X0 X1) X0 := by
    first | exact superpose ef168 ef444 | exact superpose ef444 ef168
  have ef5304 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef71 ef444 | exact superpose ef444 ef71
  have ef5316 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef135 ef5304 | exact superpose ef5304 ef135
  have ef5317 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = wf (dl X0 X1) X0 := by
    first | exact superpose ef135 ef5303 | exact superpose ef5303 ef135
  have ef6001 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef19 ef734 | exact superpose ef734 ef19
  have ef6172 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef6001 ef20 | exact superpose ef20 ef6001
  have ef6173 (X0 : G) : dl (wf X0 X0) X0 = X0 := by
    first | exact superpose ef6001 ef22 | exact superpose ef22 ef6001
  have ef6203 (X0 X1 : G) : dr X1 X0 = dr X0 (dl (wf X0 X0) X1) := by
    first | exact superpose ef6001 ef613 | exact superpose ef613 ef6001
  have ef6214 (X0 X1 : G) : wf (dl X0 X1) (dl X0 X1) = dr X1 (dl X0 (dl X0 X1)) := by
    first | exact superpose ef6001 ef330 | exact superpose ef330 ef6001
  have ef6217 (X0 X1 : G) : wf (dl X0 X1) (dl X0 X1) = dr X1 ((dl X1 X0) ◇ X0) := by
    first | exact superpose ef3410 ef6214 | exact superpose ef6214 ef3410
  have ef6253 (X0 X1 : G) : wf (dl X0 X1) (dl X0 X1) = (X0 ◇ X1) ◇ (dl X1 X0) := by
    first | exact superpose ef50 ef6217 | exact superpose ef6217 ef50
  have ef6266 (X0 X1 : G) : wf (dl X0 X1) (dl X0 X1) = X1 ◇ (dl (X0 ◇ X1) X0) := by
    first | exact superpose ef971 ef6253 | exact superpose ef6253 ef971
  have ef6273 (X0 X1 : G) : wf (dl X0 X1) (dl X0 X1) = X1 ◇ (X1 ◇ (dr X0 X0)) := by
    first | exact superpose ef639 ef6266 | exact superpose ef6266 ef639
  have ef6276 (X0 X1 : G) : wf (dl X0 X1) (dl X0 X1) = X1 ◇ (X1 ◇ (wf X0 X0)) := by
    first | exact superpose ef6172 ef6273 | exact superpose ef6273 ef6172
  have ef6488 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6172 ef188 | exact superpose ef188 ef6172
  have ef7907 (X0 X1 : G) : (dr X0 X1) ◇ X0 = (wf X0 X0) ◇ X1 := by
    first | exact superpose ef6173 ef974 | exact superpose ef974 ef6173
  have ef8083 (X0 X1 : G) : (dr X1 X1) ◇ X0 = wdr (dr X0 X1) X1 := by
    first | exact superpose ef19 ef980 | exact superpose ef980 ef19
  have ef8110 (X0 X1 : G) : dr X1 X1 = (X1 ◇ (wdr X0 X1)) ◇ X0 := by
    first | exact superpose ef980 ef17 | exact superpose ef17 ef980
  have ef8196 (X0 X1 : G) : wf X1 X1 = (X1 ◇ (wdr X0 X1)) ◇ X0 := by
    first | exact superpose ef6172 ef8110 | exact superpose ef8110 ef6172
  have ef8219 (X0 X1 : G) : wdr (dr X0 X1) X1 = (wf X1 X1) ◇ X0 := by
    first | exact superpose ef6172 ef8083 | exact superpose ef8083 ef6172
  have ef8576 (X0 X1 X2 X3 : G) : dl (wf X2 X1) X3 = (dl X0 (wf X0 X1)) ◇ (dr X2 X3) := by
    first | exact superpose ef1000 ef899 | exact superpose ef899 ef1000
  have ef8668 (X0 X1 X2 : G) : wf (dr X1 (dl X2 X0)) (wdl X2 X0) = X1 := by
    first | exact superpose ef26 ef1004 | exact superpose ef1004 ef26
  have ef8730 (X0 X1 X2 : G) : wf X1 X2 = X1 ◇ (dl (wdr X0 X2) X0) := by
    first | exact superpose ef24 ef1005 | exact superpose ef1005 ef24
  have ef9193 (X0 X1 X2 : G) : dr X2 (X0 ◇ X1) = (wf X1 X0) ◇ (X2 ◇ (dr X0 X0)) := by
    first | exact superpose ef1019 ef33 | exact superpose ef33 ef1019
  have ef9270 (X0 X1 X2 : G) : dr X2 (X0 ◇ X1) = (wf X1 X0) ◇ (X2 ◇ (wf X0 X0)) := by
    first | exact superpose ef6172 ef9193 | exact superpose ef9193 ef6172
  have ef9354 (X0 X1 X2 : G) : (X1 ◇ X2) ◇ X0 = (wf X1 X0) ◇ (X2 ◇ (wf X0 X0)) := by
    first | exact superpose ef50 ef9270 | exact superpose ef9270 ef50
  have ef9572 (X0 X1 X2 : G) : (wdr X1 X0) ◇ X2 = (dr X1 X2) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef1023 ef974 | exact superpose ef974 ef1023
  have ef9574 (X0 X1 X2 : G) : (wdr X1 X0) ◇ X2 = wf (dr X1 X2) X0 := by
    first | exact superpose ef1397 ef9572 | exact superpose ef9572 ef1397
  have ef11249 (X0 X1 X2 : G) : X2 ◇ (dl X1 X0) = wf X1 (wdl X2 X0) := by
    first | exact superpose ef26 ef2686 | exact superpose ef2686 ef26
  have ef12818 (X0 X1 X2 : G) : dr (X1 ◇ X1) X2 = (dl X0 (wf X0 X1)) ◇ (dr X2 X1) := by
    first | exact superpose ef1394 ef121 | exact superpose ef121 ef1394
  have ef12937 (X1 X2 : G) : dl (wf X2 X1) X1 = dr (X1 ◇ X1) X2 := by
    first | exact superpose ef8576 ef12818 | exact superpose ef12818 ef8576
  have ef18303 (X0 X1 X2 : G) : (wf X0 X1) ◇ X1 = (X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2 := by
    first | exact superpose ef136 ef734 | exact superpose ef734 ef136
  have ef18405 (X0 X1 : G) : (wf X0 X1) ◇ X1 = dl (dr X0 X1) X1 := by
    first | exact superpose ef455 ef18303 | exact superpose ef18303 ef455
  have ef27254 (X0 X1 X2 : G) : (dr X1 X1) ◇ ((dr X0 X1) ◇ X2) = wdr (dr X0 X2) X1 := by
    first | exact superpose ef3132 ef980 | exact superpose ef980 ef3132
  have ef27329 (X0 X1 X2 : G) : wdr (dr X0 X2) X1 = (wf X1 X1) ◇ ((dr X0 X1) ◇ X2) := by
    first | exact superpose ef6172 ef27254 | exact superpose ef27254 ef6172
  have ef29030 (X0 X1 X2 : G) : wdl (dr (wf X0 X1) X2) (X0 ◇ X2) = X1 := by
    first | exact superpose ef3347 ef32 | exact superpose ef32 ef3347
  have ef48312 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef6001 ef5316 | exact superpose ef5316 ef6001
  have ef48586 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6488 ef48312 | exact superpose ef48312 ef6488
  have ef51372 (X0 X1 X2 X3 X4 : G) :
      dl ((wf (X0 ◇ X1) X2) ◇ X3) X4 = (X4 ◇ X0) ◇ (dl X3 (X2 ◇ ((dr X2 X2) ◇ X1))) := by
    first | exact superpose ef260 ef298 | exact superpose ef298 ef260
  have ef51409 (X0 X1 X2 : G) : dl ((X1 ◇ X1) ◇ X2) X0 = (wf X0 X1) ◇ (dl X2 X1) := by
    first | exact superpose ef1397 ef298 | exact superpose ef298 ef1397
  have ef51410 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl X2 X1) = dl ((X1 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef5316 ef298 | exact superpose ef298 ef5316
  have ef51482 (X0 X1 X2 X3 : G) :
      dl (X1 ◇ (wdr X2 X0)) X3 = (X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef1023 ef298 | exact superpose ef298 ef1023
  have ef51745 (X0 X1 X2 X3 : G) : dl (X1 ◇ (wdr X2 X0)) X3 = wf (X3 ◇ (X2 ◇ X1)) X0 := by
    first | exact superpose ef1397 ef51482 | exact superpose ef51482 ef1397
  have ef51816 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl X2 X1) = (X1 ◇ (dl X0 X2)) ◇ X1 := by
    first | exact superpose ef300 ef51410 | exact superpose ef51410 ef300
  have ef51817 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl X2 X1) = (X0 ◇ (dl X1 X2)) ◇ X1 := by
    first | exact superpose ef300 ef51409 | exact superpose ef51409 ef300
  have ef51854 (X0 X1 X2 X3 X4 : G) :
      dl ((wf (X0 ◇ X1) X2) ◇ X3) X4 = (X4 ◇ X0) ◇ ((dr X2 X2) ◇ ((dr X1 X2) ◇ X3)) := by
    first | exact superpose ef454 ef51372 | exact superpose ef51372 ef454
  have ef52030 (X0 X1 X2 X3 : G) : wf (X3 ◇ (X2 ◇ X1)) X0 = (wdr X2 X0) ◇ (dr X1 X3) := by
    first | exact superpose ef639 ef51745 | exact superpose ef51745 ef639
  have ef52089 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl X2 X1) = X2 ◇ (dr (X1 ◇ X1) X0) := by
    first | exact superpose ef4010 ef51816 | exact superpose ef51816 ef4010
  have ef52090 (X0 X1 X2 : G) : (wf X0 X1) ◇ (dl X2 X1) = X2 ◇ (dr (X1 ◇ X0) X1) := by
    first | exact superpose ef4010 ef51817 | exact superpose ef51817 ef4010
  have ef52122 (X0 X1 X2 X3 X4 : G) :
      dl ((wf (X0 ◇ X1) X2) ◇ X3) X4 = (X4 ◇ X0) ◇ ((wf X2 X2) ◇ ((dr X1 X2) ◇ X3)) := by
    first | exact superpose ef6172 ef51854 | exact superpose ef51854 ef6172
  have ef52345 (X0 X1 X2 X3 X4 : G) :
      dl ((wf (X0 ◇ X1) X2) ◇ X3) X4 = (X4 ◇ X0) ◇ (wdr (dr X1 X3) X2) := by
    first | exact superpose ef27329 ef52122 | exact superpose ef52122 ef27329
  have ef52519 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ X0) ◇ (wdr (dr X1 X3) X2) = X3 ◇ (dr (wf (X0 ◇ X1) X2) X4) := by
    first | exact superpose ef639 ef52345 | exact superpose ef52345 ef639
  have ef54006 (X0 X1 : G) : wdl (dl X0 X1) (X0 ◇ (X0 ◇ X1)) = X0 := by
    first | exact superpose ef5317 ef27 | exact superpose ef27 ef5317
  have ef68022 (X0 X1 X2 X3 X4 : G) :
      dl (dr (dl X0 (wf X2 X1)) X3) X4 = (X4 ◇ (X3 ◇ (wf X0 X1))) ◇ X2 := by
    first | exact superpose ef2686 ef455 | exact superpose ef455 ef2686
  have ef68270 (X0 X1 X2 X3 X4 : G) :
      (dl X3 X4) ◇ (dl (dr X0 X1) X2) = dr (X2 ◇ (X1 ◇ (X4 ◇ X0))) X3 := by
    first | exact superpose ef455 ef113 | exact superpose ef113 ef455
  have ef68569 (X0 X1 X2 X3 X4 : G) :
      (dl X3 X4) ◇ (dl (dr X0 X1) X2) = ((X4 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1 := by
    first | exact superpose ef1831 ef68270 | exact superpose ef68270 ef1831
  have ef68808 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X3 ◇ (wf X0 X1))) ◇ X2 = dl ((wf X2 X1) ◇ (dr X3 X0)) X4 := by
    first | exact superpose ef1770 ef68022 | exact superpose ef68022 ef1770
  have ef69173 (X0 X1 X2 X3 X4 : G) :
      (X4 ◇ (X3 ◇ (wf X0 X1))) ◇ X2 = (dr X3 X0) ◇ (dr (wf X2 X1) X4) := by
    first | exact superpose ef639 ef68808 | exact superpose ef68808 ef639
  have ef76380 (X0 X1 X2 : G) : (X1 ◇ (wf X0 X0)) ◇ X2 = X0 ◇ (wdr (X2 ◇ X1) X0) := by
    first | exact superpose ef8196 ef17 | exact superpose ef17 ef8196
  have ef76470 (X0 X1 X2 : G) : (X1 ◇ (wf X0 X0)) ◇ X2 = X0 ◇ (dr (wf X2 X0) X1) := by
    first | exact superpose ef3347 ef76380 | exact superpose ef76380 ef3347
  have ef79493 (X0 X1 X2 : G) :
      (wf (dl X2 X0) (dl X2 X0)) ◇ (X2 ◇ X1) = wdr (dr X0 X1) (dl X2 X0) := by
    first | exact superpose ef613 ef8219 | exact superpose ef8219 ef613
  have ef79520 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (X0 ◇ (X0 ◇ (wf X2 X2))) ◇ (X2 ◇ X1) := by
    first | exact superpose ef6276 ef79493 | exact superpose ef79493 ef6276
  have ef79541 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (dr X0 X2) ◇ (dr (wf (X2 ◇ X1) X2) X0) := by
    first | exact superpose ef69173 ef79520 | exact superpose ef79520 ef69173
  have ef79558 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (X0 ◇ X2) ◇ (wdr (dr X1 (dr X0 X2)) X2) := by
    first | exact superpose ef52519 ef79541 | exact superpose ef79541 ef52519
  have ef79572 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (X0 ◇ X2) ◇ (wdr (X2 ◇ (X1 ◇ X0)) X2) := by
    first | exact superpose ef112 ef79558 | exact superpose ef79558 ef112
  have ef79582 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (X0 ◇ X2) ◇ (dr (wf X2 X2) (X1 ◇ X0)) := by
    first | exact superpose ef3347 ef79572 | exact superpose ef79572 ef3347
  have ef79591 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (X0 ◇ X2) ◇ ((X0 ◇ (wf X2 X2)) ◇ X1) := by
    first | exact superpose ef50 ef79582 | exact superpose ef79582 ef50
  have ef79597 (X0 X1 X2 : G) :
      wdr (dr X0 X1) (dl X2 X0) = (X0 ◇ X2) ◇ (X2 ◇ (dr (wf X1 X2) X0)) := by
    first | exact superpose ef76470 ef79591 | exact superpose ef79591 ef76470
  have ef79598 (X0 X1 X2 : G) : wdr (dr X0 X1) (dl X2 X0) = dl (dr (wf X1 X2) X0) X0 := by
    first | exact superpose ef40 ef79597 | exact superpose ef79597 ef40
  have ef79599 (X0 X1 X2 : G) : wdr (dr X0 X1) (dl X2 X0) = (wf (wf X1 X2) X0) ◇ X0 := by
    first | exact superpose ef18405 ef79598 | exact superpose ef79598 ef18405
  have ef96353 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = dr (X0 ◇ (X1 ◇ ((X4 ◇ X3) ◇ X2))) X4 := by
    first | exact superpose ef937 ef33 | exact superpose ef33 ef937
  have ef96451 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = dr (X0 ◇ X4) (X1 ◇ ((X4 ◇ X3) ◇ X2)) := by
    first | exact superpose ef1878 ef96353 | exact superpose ef96353 ef1878
  have ef96932 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = (((X4 ◇ X3) ◇ X2) ◇ (X0 ◇ X4)) ◇ X1 := by
    first | exact superpose ef50 ef96451 | exact superpose ef96451 ef50
  have ef97359 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = (dl X4 (X4 ◇ X3)) ◇ (dl (dr X2 X1) X0) := by
    first | exact superpose ef68569 ef96932 | exact superpose ef96932 ef68569
  have ef97707 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dl (dr X0 X1) X2) = X3 ◇ (dr X4 (dl (dl (dr X2 X1) X0) X4)) := by
    first | exact superpose ef5108 ef97359 | exact superpose ef97359 ef5108
  have ef97964 (X0 X1 X2 X3 : G) : X3 ◇ (dl (dr X2 X1) X0) = X3 ◇ (dl (dr X0 X1) X2) := by
    first | exact superpose ef29 ef97707 | exact superpose ef97707 ef29
  have ef98488 (X0 X1 X2 : G) : wdl X1 X2 = wdl (dr X0 (dl X1 X2)) X0 := by
    first | exact superpose ef8668 ef27 | exact superpose ef27 ef8668
  have ef116315 (X0 X1 : G) : wf (wf X0 X0) X1 = (wdr X0 X1) ◇ X0 := by
    first | exact superpose ef6172 ef9574 | exact superpose ef9574 ef6172
  have ef209557 (X0 X1 : G) :
      (wf (dl (wf X1 X1) X0) (dl (wf X1 X1) X0)) ◇ X1 = wdr (dr X0 X1) (dl (wf X1 X1) X0) := by
    first | exact superpose ef6203 ef8219 | exact superpose ef8219 ef6203
  have ef209589 (X0 X1 : G) :
      (wf (dl (wf X1 X1) X0) (dl (wf X1 X1) X0)) ◇ X1 = (wf (wf X1 (wf X1 X1)) X0) ◇ X0 := by
    first | exact superpose ef79599 ef209557 | exact superpose ef209557 ef79599
  have ef209694 (X0 X1 : G) :
      (wf X1 X0) ◇ X0 = (wf (dl (wf X1 X1) X0) (dl (wf X1 X1) X0)) ◇ X1 := by
    first | exact superpose ef48586 ef209589 | exact superpose ef209589 ef48586
  have ef209778 (X0 X1 : G) :
      (wf X1 X0) ◇ X0 = (dr (dl (wf X1 X1) X0) X1) ◇ (dl (wf X1 X1) X0) := by
    first | exact superpose ef7907 ef209694 | exact superpose ef209694 ef7907
  have ef209839 (X0 X1 : G) :
      (wf X1 X0) ◇ X0 = (wf X1 X1) ◇ (dl (dr (dl (wf X1 X1) X0) X1) X0) := by
    first | exact superpose ef971 ef209778 | exact superpose ef209778 ef971
  have ef209882 (X0 X1 : G) :
      (wf X1 X0) ◇ X0 = (wf X1 X1) ◇ (dl (dr X0 X1) (dl (wf X1 X1) X0)) := by
    first | exact superpose ef97964 ef209839 | exact superpose ef209839 ef97964
  have ef209911 (X0 X1 : G) : (wf X1 X0) ◇ X0 = (wf X1 X1) ◇ ((dl X0 (dr X0 X1)) ◇ (wf X1 X1)) := by
    first | exact superpose ef3410 ef209882 | exact superpose ef209882 ef3410
  have ef209935 (X0 X1 : G) : (wf X1 X0) ◇ X0 = (X1 ◇ (dl X0 (dr X0 X1))) ◇ X1 := by
    first | exact superpose ef9354 ef209911 | exact superpose ef209911 ef9354
  have ef209949 (X0 X1 : G) : (wf X1 X0) ◇ X0 = (dr X0 X1) ◇ (dr (X1 ◇ X1) X0) := by
    first | exact superpose ef4010 ef209935 | exact superpose ef209935 ef4010
  have ef209958 (X0 X1 : G) : (wf X1 X0) ◇ X0 = (wf X0 X1) ◇ (dl (dr X0 X1) X1) := by
    first | exact superpose ef52089 ef209949 | exact superpose ef209949 ef52089
  have ef209962 (X0 X1 : G) : (wf X1 X0) ◇ X0 = (wf X0 X1) ◇ ((wf X0 X1) ◇ X1) := by
    first | exact superpose ef18405 ef209958 | exact superpose ef209958 ef18405
  have ef237492 (X0 X1 X2 : G) :
      X2 ◇ (dl X0 (wf X0 (X1 ◇ X2))) = wf (X1 ◇ (X1 ◇ (X1 ◇ X2))) X2 := by
    first | exact superpose ef1028 ef5316 | exact superpose ef5316 ef1028
  have ef237966 (X0 X1 X2 : G) :
      X2 ◇ (dl X0 (wf X0 (X1 ◇ X2))) = (wdr X1 X2) ◇ (dr (X1 ◇ X2) X1) := by
    first | exact superpose ef52030 ef237492 | exact superpose ef237492 ef52030
  have ef238545 (X0 X1 X2 : G) :
      X2 ◇ (dl X0 (wf X0 (X1 ◇ X2))) = (wf X2 X1) ◇ (dl (wdr X1 X2) X1) := by
    first | exact superpose ef52090 ef237966 | exact superpose ef237966 ef52090
  have ef239112 (X0 X1 X2 : G) : wf (wf X2 X1) X2 = X2 ◇ (dl X0 (wf X0 (X1 ◇ X2))) := by
    first | exact superpose ef8730 ef238545 | exact superpose ef238545 ef8730
  have ef239645 (X1 X2 : G) : wf (wf X2 X1) X2 = wf X2 (X1 ◇ X2) := by
    first | exact superpose ef1005 ef239112 | exact superpose ef239112 ef1005
  have ef279989 (X0 X1 X2 : G) : wdl X1 X0 = wdl (dr X0 X2) (X1 ◇ X2) := by
    first | exact superpose ef26 ef29030 | exact superpose ef29030 ef26
  have ef315282 (X0 X1 : G) :
      wf X1 X0 = wdl (dr (X0 ◇ X0) X1) ((wf X1 X0) ◇ ((wf X1 X0) ◇ X0)) := by
    first | exact superpose ef12937 ef54006 | exact superpose ef54006 ef12937
  have ef315480 (X0 X1 : G) : wf X1 X0 = wdl (dr (X0 ◇ X0) X1) ((wf X0 X1) ◇ X1) := by
    first | exact superpose ef209962 ef315282 | exact superpose ef315282 ef209962
  have ef315572 (X0 X1 : G) : wf X1 X0 = wdl (wf X0 X1) (X0 ◇ X0) := by
    first | exact superpose ef279989 ef315480 | exact superpose ef315480 ef279989
  have ef322367 (X0 X1 : G) : wdl (wf X0 X0) X0 = wdl (dr X1 X0) X1 := by
    first | exact superpose ef6173 ef98488 | exact superpose ef98488 ef6173
  have ef399944 (X0 : G) : (wdr X0 X0) ◇ X0 = wf X0 (X0 ◇ X0) := by
    first | exact superpose ef116315 ef239645 | exact superpose ef239645 ef116315
  have ef400078 : x ◇ y ≠ wf x ((wdr y y) ◇ y) := by
    first | exact superpose ef116315 ef28 | exact superpose ef28 ef116315
  have ef407733 (X0 X1 X2 X3 : G) :
      wdl (wf X1 X2) X3 = wdl (dr X3 ((X2 ◇ (X2 ◇ X2)) ◇ X0)) (dl X0 X1) := by
    first | exact superpose ef343 ef279989 | exact superpose ef279989 ef343
  have ef407790 (X0 X1 X2 X3 : G) :
      wdl (wf X1 X2) X3 = wdl ((X0 ◇ X3) ◇ (X2 ◇ (X2 ◇ X2))) (dl X0 X1) := by
    first | exact superpose ef50 ef407733 | exact superpose ef407733 ef50
  have ef408001 (X0 X1 X2 X3 : G) : wdl (wf X1 X2) X3 = wdl (wf (X0 ◇ X3) X2) (dl X0 X1) := by
    first | exact superpose ef1397 ef407790 | exact superpose ef407790 ef1397
  have ef430719 (X0 X1 : G) : wf X1 (X0 ◇ X0) = wdl (wf (X0 ◇ X0) X1) (dl X0 X0) := by
    first | exact superpose ef40 ef315572 | exact superpose ef315572 ef40
  have ef430743 (X0 X1 : G) : wf X1 (X0 ◇ X0) = wdl (wf X0 X1) X0 := by
    first | exact superpose ef408001 ef430719 | exact superpose ef430719 ef408001
  have ef433496 (X0 X1 X2 : G) : wdl (dr X0 X1) ((dr X0 X2) ◇ X1) = wdl (wf X2 X2) X2 := by
    first | exact superpose ef1868 ef322367 | exact superpose ef322367 ef1868
  have ef433561 (X0 X1 X2 : G) : wf X2 (X2 ◇ X2) = wdl (dr X0 X1) ((dr X0 X2) ◇ X1) := by
    first | exact superpose ef430743 ef433496 | exact superpose ef433496 ef430743
  have ef433588 (X0 X2 : G) : wf X2 (X2 ◇ X2) = wdl (dr X0 X2) X0 := by
    first | exact superpose ef279989 ef433561 | exact superpose ef433561 ef279989
  have ef445544 (X0 X1 : G) : (wdr X1 X1) ◇ X1 = wdl (dr X0 X1) X0 := by
    first | exact superpose ef433588 ef399944 | exact superpose ef399944 ef433588
  have ef454639 (X0 X1 X2 : G) : (dr X1 X0) ◇ (dl X2 X1) = wf X2 ((wdr X0 X0) ◇ X0) := by
    first | exact superpose ef445544 ef11249 | exact superpose ef11249 ef445544
  have ef454662 (X0 X2 : G) : X2 ◇ X0 = wf X2 ((wdr X0 X0) ◇ X0) := by
    first | exact superpose ef974 ef454639 | exact superpose ef454639 ef974
  have ef465790 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef454662 ef400078 | exact superpose ef400078 ef454662
  exact absurd rfl ef465790

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the operation `x □ y := (x◇(y/(y/y)))` in every magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the divisions that law
forces. -/
private theorem qaux898_8_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x : G) :
    x = wf x (wf x x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf x (wf x x) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef64 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef99 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef154 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef272 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef283 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef625 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef830 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef64 ef30 | exact superpose ef30 ef64
  have ef861 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef283 ef830 | exact superpose ef830 ef283
  have ef885 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef625 ef861 | exact superpose ef861 ef625
  have ef902 (X0 X1 X2 X3 : G) : X1 ◇ X2 = dl (X0 ◇ X1) ((X0 ◇ (dr X3 X2)) ◇ X3) := by
    first | exact superpose ef26 ef72 | exact superpose ef72 ef26
  have ef953 (X0 X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef272 ef902 | exact superpose ef902 ef272
  have ef960 (X1 X2 X3 : G) : X1 ◇ X2 = (dr X3 X2) ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef953 | exact superpose ef953 ef30
  have ef1741 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef99 ef23 | exact superpose ef23 ef99
  have ef3330 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef61 ef154 | exact superpose ef154 ef61
  have ef3435 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef625 ef3330 | exact superpose ef3330 ef625
  have ef3469 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1741 ef3435 | exact superpose ef3435 ef1741
  have ef3492 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef885 ef3469 | exact superpose ef3469 ef885
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6411 : x ≠ wf x (dr x x) := by
    first | exact superpose ef6097 ef20 | exact superpose ef20 ef6097
  have ef25990 (X0 X1 X2 : G) : (dr X2 X2) ◇ (dl X1 X0) = X1 ◇ ((wf X0 X2) ◇ X2) := by
    first | exact superpose ef174 ef3492 | exact superpose ef3492 ef174
  have ef39248 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39495 (X0 : G) : wf X0 (wf X0 X0) = (dr X0 X0) ◇ (dl (wf X0 X0) X0) := by
    first | exact superpose ef25990 ef39248 | exact superpose ef39248 ef25990
  have ef39644 (X0 : G) : (wf X0 X0) ◇ X0 = wf X0 (wf X0 X0) := by
    first | exact superpose ef960 ef39495 | exact superpose ef39495 ef960
  have ef39754 (X0 : G) : (dr X0 X0) ◇ X0 = wf X0 (dr X0 X0) := by
    first | exact superpose ef6097 ef39644 | exact superpose ef39644 ef6097
  have ef39833 (X0 : G) : wf X0 (dr X0 X0) = X0 := by
    first | exact superpose ef15 ef39754 | exact superpose ef39754 ef15
  have ef41401 : x ≠ x := by
    first | exact superpose ef39833 ef6411 | exact superpose ef6411 ef39833
  exact absurd rfl ef41401

theorem Equation8_termStructuralFromFin_Equation898_qdiv :
    Law8.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law8.models_iff]
    exact fun x ↦
      @qaux898_8_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 411 `x = x ◇ (x ◇ (x ◇ (x ◇ x)))` holds of the operation `x □ y := (x◇(y/(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_411_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x : G) :
    x = wf x (wf x (wf x (wf x x))) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf x (wf x (wf x (wf x x))) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6412 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6097 ef174 | exact superpose ef174 ef6097
  have ef38943 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39189 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6412 ef38943 | exact superpose ef38943 ef6412
  have ef40648 : x ≠ wf x (wf x x) := by
    first | exact superpose ef39189 ef20 | exact superpose ef20 ef39189
  subsumption ef40648 ef39189

theorem Equation411_termStructuralFromFin_Equation898_qdiv :
    Law411.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law411.models_iff]
    exact fun x ↦
      @qaux898_411_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the operation `x □ y := (x◇(y/(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_1020_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x : G) :
    x = wf x (wf (wf x (wf x x)) x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf x (wf (wf x (wf x x)) x) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6412 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6097 ef174 | exact superpose ef174 ef6097
  have ef38943 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39189 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6412 ef38943 | exact superpose ef38943 ef6412
  have ef40648 : x ≠ wf x (wf x x) := by
    first | exact superpose ef39189 ef20 | exact superpose ef20 ef39189
  subsumption ef40648 ef39189

theorem Equation1020_termStructuralFromFin_Equation898_qdiv :
    Law1020.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1020.models_iff]
    exact fun x ↦
      @qaux898_1020_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the operation `x □ y := (x◇(y/(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3253_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x : G) :
    wf x x = wf x (wf x (wf x x)) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : wf x x ≠ wf x (wf x (wf x x)) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6412 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6097 ef174 | exact superpose ef174 ef6097
  have ef38943 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39189 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6412 ef38943 | exact superpose ef38943 ef6412
  have ef40648 : wf x x ≠ wf x x := by
    first | exact superpose ef39189 ef20 | exact superpose ef20 ef39189
  exact absurd rfl ef40648

theorem Equation3253_termStructuralFromFin_Equation898_qdiv :
    Law3253.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3253.models_iff]
    exact fun x ↦
      @qaux898_3253_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the operation `x □ y := (x◇(y/(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3319_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x y : G) :
    wf x y = wf x (wf y (wf y y)) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : wf x y ≠ wf x (wf y (wf y y)) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6412 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6097 ef174 | exact superpose ef174 ef6097
  have ef38943 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39189 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6412 ef38943 | exact superpose ef38943 ef6412
  have ef40648 : wf x y ≠ wf x y := by
    first | exact superpose ef39189 ef20 | exact superpose ef20 ef39189
  exact absurd rfl ef40648

theorem Equation3319_termStructuralFromFin_Equation898_qdiv :
    Law3319.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3319.models_iff]
    exact fun x y ↦
      @qaux898_3319_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3862 `x ◇ x = (x ◇ (x ◇ x)) ◇ x` holds of the operation `x □ y := (x◇(y/(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3862_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x : G) :
    wf x x = wf (wf x (wf x x)) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : wf x x ≠ wf (wf x (wf x x)) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6412 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6097 ef174 | exact superpose ef174 ef6097
  have ef38943 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39189 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6412 ef38943 | exact superpose ef38943 ef6412
  have ef40648 : wf x x ≠ wf x x := by
    first | exact superpose ef39189 ef20 | exact superpose ef20 ef39189
  exact absurd rfl ef40648

theorem Equation3862_termStructuralFromFin_Equation898_qdiv :
    Law3862.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3862.models_iff]
    exact fun x ↦
      @qaux898_3862_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Equation 3915 `x ◇ y = (x ◇ (x ◇ x)) ◇ y` holds of the operation `x □ y := (x◇(y/(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3915_8 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = a ◇ (dr b (dr b b)))
    (x y : G) :
    wf x y = wf (wf x (wf x x)) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef16 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X0 ◇ (dr X1 (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : wf x y ≠ wf (wf x (wf x x)) y := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef121 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef174 (X0 X1 : G) : (dr X1 X1) ◇ ((wf X0 X1) ◇ X1) = X0 := by
    first | exact superpose ef19 ef26 | exact superpose ef26 ef19
  have ef430 (X0 X1 : G) : wf ((dr X1 X1) ◇ (X0 ◇ X1)) X1 = X0 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef720 (X0 X1 : G) : (wf ((dr X0 X0) ◇ X1) X0) ◇ X0 = X1 := by
    first | exact superpose ef19 ef63 | exact superpose ef63 ef19
  have ef5238 (X0 X1 : G) : wf X0 X1 = dl (X1 ◇ X0) (dr X1 X1) := by
    first | exact superpose ef61 ef430 | exact superpose ef430 ef61
  have ef5247 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef121 ef5238 | exact superpose ef5238 ef121
  have ef5930 (X0 : G) : (wf X0 X0) ◇ X0 = X0 := by
    first | exact superpose ef15 ef720 | exact superpose ef720 ef15
  have ef6097 (X0 : G) : dr X0 X0 = wf X0 X0 := by
    first | exact superpose ef5930 ef16 | exact superpose ef16 ef5930
  have ef6412 (X0 X1 : G) : (wf X0 X0) ◇ ((wf X1 X0) ◇ X0) = X1 := by
    first | exact superpose ef6097 ef174 | exact superpose ef174 ef6097
  have ef38943 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ ((wf X0 X0) ◇ X0) := by
    first | exact superpose ef5930 ef5247 | exact superpose ef5247 ef5930
  have ef39189 (X0 : G) : wf X0 (wf X0 X0) = X0 := by
    first | exact superpose ef6412 ef38943 | exact superpose ef38943 ef6412
  have ef40648 : wf x y ≠ wf x y := by
    first | exact superpose ef39189 ef20 | exact superpose ef20 ef39189
  exact absurd rfl ef40648

theorem Equation3915_termStructuralFromFin_Equation898_qdiv :
    Law3915.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 0) (.rdv (.var 1) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.op (.op (.var 1) (.var 1)) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3915.models_iff]
    exact fun x y ↦
      @qaux898_3915_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_8R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_8L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_8 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := (y◇(x◇(y/y)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_21R [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = b ◇ (a ◇ (dr b b)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X0 ◇ (dr X1 X1)) := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef24 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef112 (X0 X1 : G) : dr X1 X0 = (dr X1 X1) ◇ (wf X0 X1) := by
    first | exact superpose ef20 ef27 | exact superpose ef27 ef20
  have ef1938 : (dr t t) ◇ (wf p t) = dr t q := by
    first | exact superpose ef21 ef112 | exact superpose ef112 ef21
  have ef1987 : dr t q = dr t p := by
    first | exact superpose ef112 ef1938 | exact superpose ef1938 ef112
  have ef2488 : q = dl (dr t p) t := by
    first | exact superpose ef1987 ef24 | exact superpose ef24 ef1987
  have ef2490 : p = q := by
    first | exact superpose ef24 ef2488 | exact superpose ef2488 ef24
  subsumption ef2490 ef22

/-- Left translation of `x □ y := (y◇(x◇(y/y)))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_21L [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = b ◇ (a ◇ (dr b b)))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X0 ◇ (dr X1 X1)) := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef28 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef30 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef31 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef34 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef41 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef44 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef63 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef66 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef69 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef15 ef15
  have ef71 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef74 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef87 (X0 X1 : G) : ((dr X1 X1) ◇ (wf X0 X1)) ◇ X0 = X1 := by
    first | exact superpose ef20 ef14 | exact superpose ef14 ef20
  have ef95 (X0 X1 X2 : G) : (wf X0 (X1 ◇ X2)) ◇ ((X0 ◇ (dr (X1 ◇ X2) (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef96 (X0 X1 X2 : G) : (wf X0 (X1 ◇ X2)) ◇ ((X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = X2 := by
    first | exact superpose ef44 ef95 | exact superpose ef95 ef44
  have ef103 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef104 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef18 ef27 | exact superpose ef27 ef18
  have ef107 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef27 ef27
  have ef108 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef14 ef27 | exact superpose ef27 ef14
  have ef109 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef15 ef27 | exact superpose ef27 ef15
  have ef127 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef27 ef19 | exact superpose ef19 ef27
  have ef134 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef44 ef109 | exact superpose ef109 ef44
  have ef135 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef44 ef108 | exact superpose ef108 ef44
  have ef153 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef161 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef28 ef19 | exact superpose ef19 ef28
  have ef162 (X0 X1 X2 X3 : G) : dr X3 X2 = (X1 ◇ ((dl X0 X1) ◇ X2)) ◇ (X3 ◇ X0) := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef198 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef30 ef19 | exact superpose ef19 ef30
  have ef230 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef14 ef31 | exact superpose ef31 ef14
  have ef246 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef31 ef19 | exact superpose ef19 ef31
  have ef247 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef31 ef27 | exact superpose ef27 ef31
  have ef282 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef283 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef34 ef34
  have ef285 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef294 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) X2 = (X2 ◇ (X1 ◇ X3)) ◇ (dl X0 X1) := by
    first | exact superpose ef34 ef34
  have ef296 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef31 ef34 | exact superpose ef34 ef31
  have ef307 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef314 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef34 ef15 | exact superpose ef15 ef34
  have ef327 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef247 ef314 | exact superpose ef314 ef247
  have ef434 (X0 X1 : G) : (wf X0 X1) ◇ (dr (dr X1 X1) X1) = X0 := by
    first | exact superpose ef20 ef40 | exact superpose ef40 ef20
  have ef445 (X0 X1 : G) : X1 ◇ X0 = wf (X1 ◇ (X0 ◇ X1)) X1 := by
    first | exact superpose ef40 ef20 | exact superpose ef20 ef40
  have ef453 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef40 ef27 | exact superpose ef27 ef40
  have ef455 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef40 ef34 | exact superpose ef34 ef40
  have ef465 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef44 ef453 | exact superpose ef453 ef44
  have ef523 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((dl X1 X3) ◇ (X0 ◇ X3)) := by
    first | exact superpose ef41 ef27 | exact superpose ef27 ef41
  have ef530 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef41 ef31 | exact superpose ef31 ef41
  have ef553 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ X3) ◇ X2) ◇ (dl X1 X3) := by
    first | exact superpose ef44 ef523 | exact superpose ef523 ef44
  have ef598 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef15 ef44 | exact superpose ef44 ef15
  have ef613 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef247 ef598 | exact superpose ef598 ef247
  have ef637 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef63 ef40 | exact superpose ef40 ef63
  have ef820 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef27 ef66 | exact superpose ef66 ef27
  have ef914 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef40 ef74 | exact superpose ef74 ef40
  have ef916 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef74 | exact superpose ef74 ef31
  have ef946 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef282 ef916 | exact superpose ef916 ef282
  have ef947 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef127 ef914 | exact superpose ef914 ef127
  have ef960 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef34 ef946 | exact superpose ef946 ef34
  have ef970 : q = ((dr q q) ◇ (wf t p)) ◇ t := by
    first | exact superpose ef21 ef87 | exact superpose ef87 ef21
  have ef992 (X0 X1 : G) : dr X0 X0 = (dl (wf X1 X0) X1) ◇ X0 := by
    first | exact superpose ef87 ef31 | exact superpose ef31 ef87
  have ef994 (X0 X1 X2 : G) : X0 ◇ (dr X2 ((dr X0 X0) ◇ (wf (X1 ◇ X2) X0))) = X1 := by
    first | exact superpose ef87 ef40 | exact superpose ef40 ef87
  have ef1004 (X0 X1 X2 : G) : X0 ◇ (((wf (X1 ◇ X2) X0) ◇ X2) ◇ (dr X0 X0)) = X1 := by
    first | exact superpose ef44 ef994 | exact superpose ef994 ef44
  have ef1023 : q = q ◇ (q ◇ (dl (wf t p) t)) := by
    first | exact superpose ef820 ef970 | exact superpose ef970 ef820
  have ef1026 (X0 X1 X2 : G) : wf ((wf (X1 ◇ X2) X0) ◇ X2) X0 = X1 := by
    first | exact superpose ef20 ef1004 | exact superpose ef1004 ef20
  have ef1112 (X0 X1 X2 X3 : G) :
      (((X2 ◇ X1) ◇ X3) ◇ ((wf X0 X1) ◇ X2)) ◇ (X0 ◇ (dr X1 X1)) = X3 := by
    first | exact superpose ef20 ef69 | exact superpose ef69 ef20
  have ef1233 (X0 X1 X2 X3 : G) :
      (dr X3 (X0 ◇ (dr X1 X1))) ◇ (((wf X0 X1) ◇ X2) ◇ (X2 ◇ X1)) = X3 := by
    first | exact superpose ef465 ef1112 | exact superpose ef1112 ef465
  have ef1316 (X0 X1 X2 X3 : G) :
      X1 ◇ (((wf X0 X1) ◇ X2) ◇ (X2 ◇ (dr X3 (X0 ◇ (dr X1 X1))))) = X3 := by
    first | exact superpose ef947 ef1233 | exact superpose ef1233 ef947
  have ef1371 (X0 X1 X3 : G) : X1 ◇ (dl (dr X3 (X0 ◇ (dr X1 X1))) (wf X0 X1)) = X3 := by
    first | exact superpose ef34 ef1316 | exact superpose ef1316 ef34
  have ef1412 (X0 X1 X3 : G) : X1 ◇ (dl (((dr X1 X1) ◇ X3) ◇ X0) (wf X0 X1)) = X3 := by
    first | exact superpose ef44 ef1371 | exact superpose ef1371 ef44
  have ef1437 (X0 X1 X3 : G) : X1 ◇ (((wf X0 X1) ◇ (dl X3 X0)) ◇ (dr X1 X1)) = X3 := by
    first | exact superpose ef296 ef1412 | exact superpose ef1412 ef296
  have ef1444 (X0 X1 X3 : G) : wf ((wf X0 X1) ◇ (dl X3 X0)) X1 = X3 := by
    first | exact superpose ef20 ef1437 | exact superpose ef1437 ef20
  have ef1465 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef15 ef104 | exact superpose ef104 ef15
  have ef1466 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef34 ef104 | exact superpose ef104 ef34
  have ef1467 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef40 ef104 | exact superpose ef104 ef40
  have ef1468 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef16 ef104 | exact superpose ef104 ef16
  have ef1535 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef127 ef1467 | exact superpose ef1467 ef127
  have ef1536 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef960 ef1466 | exact superpose ef1466 ef960
  have ef1565 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef246 ef1536 | exact superpose ef1536 ef246
  have ef1575 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef27 ef1565 | exact superpose ef1565 ef27
  have ef1688 (X0 X1 X2 X3 X4 : G) :
      (dl X1 ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3)) ◇ X0 = dr (X4 ◇ X2) X1 := by
    first | exact superpose ef71 ef104 | exact superpose ef104 ef71
  have ef1699 (X0 X1 X2 X3 X4 : G) :
      dr (X4 ◇ X2) X1 = (((X2 ◇ X3) ◇ X4) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X0 := by
    first | exact superpose ef282 ef1688 | exact superpose ef1688 ef282
  have ef1791 (X0 X1 X2 X3 X4 : G) :
      dr (X4 ◇ X2) X1 = (dr X4 X0) ◇ (((X3 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) := by
    first | exact superpose ef465 ef1699 | exact superpose ef1699 ef465
  have ef1855 (X0 X1 X2 X4 : G) : dr (X4 ◇ X2) X1 = (dr X4 X0) ◇ (dr X2 (dl X0 X1)) := by
    first | exact superpose ef247 ef1791 | exact superpose ef1791 ef247
  have ef3198 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef27 ef153 | exact superpose ef153 ef27
  have ef3214 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef153 ef27 | exact superpose ef27 ef153
  have ef3296 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef44 ef3214 | exact superpose ef3214 ef44
  have ef3307 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1575 ef3198 | exact superpose ef3198 ef1575
  have ef3341 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef44 ef3307 | exact superpose ef3307 ef44
  have ef3359 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef104 ef3341 | exact superpose ef3341 ef104
  have ef3622 (X0 X1 : G) : wf (dl X1 X0) X0 = dl (dr X0 X0) X1 := by
    first | exact superpose ef161 ef20 | exact superpose ef20 ef161
  have ef3631 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef161 ef19 | exact superpose ef19 ef161
  have ef4663 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef198 ef14 | exact superpose ef14 ef198
  have ef4868 (X0 X1 X2 X3 : G) : (dl X0 X2) ◇ ((X1 ◇ X0) ◇ (dr (X2 ◇ X3) X1)) = X3 := by
    first | exact superpose ef65 ef230 | exact superpose ef230 ef65
  have ef4976 (X1 X2 X3 : G) : dl (dr (X2 ◇ X3) X1) (X2 ◇ X1) = X3 := by
    first | exact superpose ef283 ef4868 | exact superpose ef4868 ef283
  have ef5487 (X0 X1 : G) : dr (dr X1 X1) X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef20 ef307 | exact superpose ef307 ef20
  have ef5498 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef153 ef307 | exact superpose ef307 ef153
  have ef5549 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef44 ef5498 | exact superpose ef5498 ef44
  have ef5559 (X0 X1 : G) : dl (wf X0 X1) X0 = (dl X1 X1) ◇ X1 := by
    first | exact superpose ef1468 ef5487 | exact superpose ef5487 ef1468
  have ef5604 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef637 ef5549 | exact superpose ef5549 ef637
  have ef5633 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef34 ef5604 | exact superpose ef5604 ef34
  have ef5840 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef327 ef74 | exact superpose ef74 ef327
  have ef5858 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3631 ef5840 | exact superpose ef5840 ef3631
  have ef6242 (X0 X1 : G) : X0 ◇ (dl X1 X0) = wf (dl X0 X1) X0 := by
    first | exact superpose ef161 ef445 | exact superpose ef445 ef161
  have ef6406 (X0 X1 X2 X3 : G) : dl X1 X2 = (dl X0 X1) ◇ ((X3 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef65 ef530 | exact superpose ef530 ef65
  have ef6572 (X1 X2 X3 : G) : dl X1 X2 = dl (dr X2 X3) (X1 ◇ X3) := by
    first | exact superpose ef283 ef6406 | exact superpose ef6406 ef283
  have ef6733 (X0 X1 X2 : G) : dr X1 (dr (dr X2 X2) X2) = dr X0 (dl (wf X0 X2) X1) := by
    first | exact superpose ef434 ef613 | exact superpose ef613 ef434
  have ef6774 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ (dr X2 X2)) = dr X0 (dl (wf X0 X2) X1) := by
    first | exact superpose ef103 ef6733 | exact superpose ef6733 ef103
  have ef6816 (X0 X1 X2 : G) : wf X1 X2 = dr X0 (dl (wf X0 X2) X1) := by
    first | exact superpose ef20 ef6774 | exact superpose ef6774 ef20
  have ef8896 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (dr X0 X0)) = dr X1 (dl (wf X2 X0) X2) := by
    first | exact superpose ef992 ef27 | exact superpose ef27 ef992
  have ef9003 (X0 X1 X2 : G) : wf X1 X0 = dr X1 (dl (wf X2 X0) X2) := by
    first | exact superpose ef20 ef8896 | exact superpose ef8896 ef20
  have ef9181 : dl (wf t p) t = (dl q q) ◇ q := by
    first | exact superpose ef1023 ef230 | exact superpose ef230 ef1023
  have ef9268 : (dl q q) ◇ q = (dl p p) ◇ p := by
    first | exact superpose ef5559 ef9181 | exact superpose ef9181 ef5559
  have ef12017 (X0 : G) : dr X0 (dl (wf t p) t) = q ◇ (X0 ◇ (dr q q)) := by
    first | exact superpose ef1023 ef107 | exact superpose ef107 ef1023
  have ef12225 (X0 : G) : wf X0 q = dr X0 (dl (wf t p) t) := by
    first | exact superpose ef20 ef12017 | exact superpose ef12017 ef20
  have ef12387 (X0 : G) : wf X0 q = wf X0 p := by
    first | exact superpose ef9003 ef12225 | exact superpose ef12225 ef9003
  have ef18465 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = dr ((X0 ◇ X2) ◇ X4) (X1 ◇ X3) := by
    first | exact superpose ef134 ef1575 | exact superpose ef1575 ef134
  have ef18502 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = (dl (X1 ◇ X3) (X4 ◇ X0)) ◇ X2 := by
    first | exact superpose ef1465 ef18465 | exact superpose ef18465 ef1465
  have ef18890 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) := by
    first | exact superpose ef5858 ef18502 | exact superpose ef18502 ef5858
  have ef19158 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X2 := by
    first | exact superpose ef1535 ef18890 | exact superpose ef18890 ef1535
  have ef21407 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ ((dl X4 X3) ◇ X1))) = ((dr X0 X1) ◇ X2) ◇ X4 := by
    first | exact superpose ef162 ef135 | exact superpose ef135 ef162
  have ef21573 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ ((dl X4 X3) ◇ X1))) = X0 ◇ (X1 ◇ (dl X2 X4)) := by
    first | exact superpose ef820 ef21407 | exact superpose ef21407 ef820
  have ef21777 (X0 X1 X2 X4 : G) : X0 ◇ (X2 ◇ (dl X1 X4)) = X0 ◇ (X1 ◇ (dl X2 X4)) := by
    first | exact superpose ef161 ef21573 | exact superpose ef21573 ef161
  have ef43656 (X0 : G) : q ◇ (dl X0 q) = wf (dl q X0) p := by
    first | exact superpose ef6242 ef12387 | exact superpose ef12387 ef6242
  have ef44679 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = dl ((X2 ◇ (X0 ◇ X3)) ◇ X1) X4 := by
    first | exact superpose ef135 ef6572 | exact superpose ef6572 ef135
  have ef44864 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (dl (X0 ◇ X3) X1)) ◇ X2 := by
    first | exact superpose ef296 ef44679 | exact superpose ef44679 ef296
  have ef44960 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = X1 ◇ (dr (X2 ◇ X4) (X0 ◇ X3)) := by
    first | exact superpose ef4663 ef44864 | exact superpose ef44864 ef4663
  have ef45034 (X0 X1 X2 X3 X4 : G) :
      dl (dr X4 X3) (X0 ◇ (X1 ◇ X2)) = X1 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X0) := by
    first | exact superpose ef44 ef44960 | exact superpose ef44960 ef44
  have ef45079 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((dr X2 X0) ◇ (dr X4 X3)) = X1 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X0) := by
    first | exact superpose ef455 ef45034 | exact superpose ef45034 ef455
  have ef47097 (X0 X1 X2 X3 X4 : G) :
      dl (X1 ◇ (dr (X2 ◇ X0) X3)) X4 = (X4 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0 := by
    first | exact superpose ef4976 ef294 | exact superpose ef294 ef4976
  have ef47362 (X0 X1 X2 X3 X4 : G) :
      dl (X1 ◇ (dr (X2 ◇ X0) X3)) X4 = X2 ◇ (dr (X3 ◇ X4) (dl X0 X1)) := by
    first | exact superpose ef19158 ef47097 | exact superpose ef47097 ef19158
  have ef47635 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr (X3 ◇ X4) (dl X0 X1)) = (dr (X2 ◇ X0) X3) ◇ (dr X1 X4) := by
    first | exact superpose ef637 ef47362 | exact superpose ef47362 ef637
  have ef48398 (X0 X1 X2 X3 : G) : (wf X0 X1) ◇ X3 = (dr X2 X3) ◇ (dl (wf X2 X1) X0) := by
    first | exact superpose ef6816 ef3359 | exact superpose ef3359 ef6816
  have ef65777 (X0 X1 X2 X3 X4 : G) :
      (wf X0 X1) ◇ (X3 ◇ X4) = ((X4 ◇ X2) ◇ X3) ◇ (dl (wf X2 X1) X0) := by
    first | exact superpose ef6816 ef465 | exact superpose ef465 ef6816
  have ef69368 (X0 X1 X2 X3 X4 : G) :
      ((dr X0 X1) ◇ X3) ◇ (dl X2 X4) = X2 ◇ (X3 ◇ ((dl X4 X1) ◇ X0)) := by
    first | exact superpose ef153 ef553 | exact superpose ef553 ef153
  have ef69984 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X1 ◇ (dl X3 (dl X2 X4))) = X2 ◇ (X3 ◇ ((dl X4 X1) ◇ X0)) := by
    first | exact superpose ef820 ef69368 | exact superpose ef69368 ef820
  have ef70215 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X1 ◇ ((dl X4 X3) ◇ X2)) = X2 ◇ (X3 ◇ ((dl X4 X1) ◇ X0)) := by
    first | exact superpose ef3631 ef69984 | exact superpose ef69984 ef3631
  have ef70816 (X0 : G) :
      q = (wf X0 ((dl p p) ◇ p)) ◇ ((X0 ◇ ((q ◇ ((dl p p) ◇ p)) ◇ (dl q q))) ◇ (dl q q)) := by
    first | exact superpose ef9268 ef96 | exact superpose ef96 ef9268
  have ef70960 (X0 : G) :
      q = (wf X0 ((dl p p) ◇ p)) ◇ (q ◇ (dl (X0 ◇ ((q ◇ ((dl p p) ◇ p)) ◇ (dl q q))) q)) := by
    first | exact superpose ef21777 ef70816 | exact superpose ef70816 ef21777
  have ef71050 (X0 : G) :
      q = (wf X0 ((dl p p) ◇ p)) ◇ (q ◇ (((q ◇ ((dl p p) ◇ p)) ◇ (dl q q)) ◇ (dr X0 q))) := by
    first | exact superpose ef637 ef70960 | exact superpose ef70960 ef637
  have ef71129 (X0 : G) :
      q = (dr X0 q) ◇ (q ◇ (((q ◇ ((dl p p) ◇ p)) ◇ (dl q q)) ◇ (wf X0 ((dl p p) ◇ p)))) := by
    first | exact superpose ef947 ef71050 | exact superpose ef71050 ef947
  have ef71187 (X0 : G) :
      q = (dr X0 q) ◇ (dl (wf X0 ((dl p p) ◇ p)) (dl ((dl p p) ◇ p) (dl q q))) := by
    first | exact superpose ef285 ef71129 | exact superpose ef71129 ef285
  have ef71233 : q = (wf (dl ((dl p p) ◇ p) (dl q q)) ((dl p p) ◇ p)) ◇ q := by
    first | exact superpose ef48398 ef71187 | exact superpose ef71187 ef48398
  have ef71264 : q = (((dl p p) ◇ p) ◇ (dl (dl q q) ((dl p p) ◇ p))) ◇ q := by
    first | exact superpose ef6242 ef71233 | exact superpose ef71233 ef6242
  have ef71289 : q = (dr p q) ◇ ((dl (dl q q) ((dl p p) ◇ p)) ◇ (dl p p)) := by
    first | exact superpose ef465 ef71264 | exact superpose ef71264 ef465
  have ef71309 : q = (dr p q) ◇ (p ◇ (dl (dl (dl q q) ((dl p p) ◇ p)) p)) := by
    first | exact superpose ef21777 ef71289 | exact superpose ef71289 ef21777
  have ef71321 : q = (dr p q) ◇ (p ◇ ((p ◇ (dl q q)) ◇ ((dl p p) ◇ p))) := by
    first | exact superpose ef246 ef71309 | exact superpose ef71309 ef246
  have ef71329 : q = (dr p q) ◇ (p ◇ (p ◇ ((dl p (p ◇ (dl q q))) ◇ p))) := by
    first | exact superpose ef70215 ef71321 | exact superpose ef71321 ef70215
  have ef71334 : q = (dr p q) ◇ (dr p (dl p (p ◇ (dl q q)))) := by
    first | exact superpose ef27 ef71329 | exact superpose ef71329 ef27
  have ef71339 : q = (dr p q) ◇ (dr p (dl q q)) := by
    first | exact superpose ef19 ef71334 | exact superpose ef71334 ef19
  have ef71343 : q = dr (p ◇ p) q := by
    first | exact superpose ef1855 ef71339 | exact superpose ef71339 ef1855
  have ef73102 : q ◇ q = p ◇ p := by
    first | exact superpose ef71343 ef16 | exact superpose ef16 ef71343
  have ef75570 (X0 : G) : q = (wf X0 (p ◇ p)) ◇ ((X0 ◇ ((q ◇ (p ◇ p)) ◇ q)) ◇ q) := by
    first | exact superpose ef73102 ef96 | exact superpose ef96 ef73102
  have ef75695 (X0 : G) : q = (wf X0 (p ◇ p)) ◇ ((dr (q ◇ (p ◇ p)) q) ◇ (dr q X0)) := by
    first | exact superpose ef45079 ef75570 | exact superpose ef75570 ef45079
  have ef75756 (X0 : G) : q = (wf X0 (p ◇ p)) ◇ (q ◇ (dr (q ◇ X0) (dl (p ◇ p) q))) := by
    first | exact superpose ef47635 ef75695 | exact superpose ef75695 ef47635
  have ef75801 (X0 : G) : q = ((q ◇ X0) ◇ q) ◇ (dl (wf X0 (p ◇ p)) (dl (p ◇ p) q)) := by
    first | exact superpose ef3296 ef75756 | exact superpose ef75756 ef3296
  have ef75833 : q = (wf (dl (p ◇ p) q) (p ◇ p)) ◇ (q ◇ q) := by
    first | exact superpose ef65777 ef75801 | exact superpose ef75801 ef65777
  have ef75851 : q = (wf (dl (p ◇ p) q) (p ◇ p)) ◇ (p ◇ p) := by
    first | exact superpose ef73102 ef75833 | exact superpose ef75833 ef73102
  have ef75865 : q = ((p ◇ p) ◇ (dl q (p ◇ p))) ◇ (p ◇ p) := by
    first | exact superpose ef6242 ef75851 | exact superpose ef75851 ef6242
  have ef75873 : q = dr p (dl p (dl q (p ◇ p))) := by
    first | exact superpose ef247 ef75865 | exact superpose ef75865 ef247
  have ef75877 : q = dr p ((dl (p ◇ p) p) ◇ q) := by
    first | exact superpose ef3631 ef75873 | exact superpose ef75873 ef3631
  have ef75879 : q = (q ◇ p) ◇ (dl (p ◇ p) p) := by
    first | exact superpose ef44 ef75877 | exact superpose ef75877 ef44
  have ef75881 : q = (p ◇ p) ◇ (dl (q ◇ p) p) := by
    first | exact superpose ef960 ef75879 | exact superpose ef75879 ef960
  have ef75883 : q = (p ◇ p) ◇ (p ◇ (dr q p)) := by
    first | exact superpose ef637 ef75881 | exact superpose ef75881 ef637
  have ef75885 : q = dl (dr q p) p := by
    first | exact superpose ef34 ef75883 | exact superpose ef75883 ef34
  have ef75887 : q = dl (dr p p) q := by
    first | exact superpose ef5633 ef75885 | exact superpose ef75885 ef5633
  have ef75888 : q = wf (dl q p) p := by
    first | exact superpose ef3622 ef75887 | exact superpose ef75887 ef3622
  have ef75889 : q = q ◇ (dl p q) := by
    first | exact superpose ef43656 ef75888 | exact superpose ef75888 ef43656
  have ef75890 : q = p ◇ (dl q q) := by
    first | exact superpose ef960 ef75889 | exact superpose ef75889 ef960
  have ef81609 (X0 : G) : p = wf ((wf q X0) ◇ (dl q q)) X0 := by
    first | exact superpose ef75890 ef1026 | exact superpose ef1026 ef75890
  have ef81637 : p = q := by
    first | exact superpose ef1444 ef81609 | exact superpose ef81609 ef1444
  subsumption ef81637 ef22

/-- The operation comes back: `x ◇ y = (x◇((y◇x)\x))` read in `□` and its divisions, where
`x □ y := (y◇(x◇(y/y)))`. With `winj898_21` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back898_21 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = b ◇ (a ◇ (dr b b)))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wf x (wdl (wf y x) x)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef16 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef19 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef22 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X0 ◇ (dr X1 X1)) := mod_symm (hwdef ..)
  have ef25 (X0 X1 : G) : wdr (wf X0 X1) X1 = X0 := mod_symm (hwri ..)
  have ef26 (X0 X1 : G) : wf X0 (wdl X0 X1) = X1 := mod_symm (hwls ..)
  have ef28 : wf x (wdl (wf y x) x) ≠ x ◇ y := mod_symm nh
  have ef33 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef34 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef36 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef37 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef40 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef46 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef50 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef74 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef79 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef18 ef16 | exact superpose ef16 ef18
  have ef82 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef94 (X0 X1 : G) : X1 ◇ X0 = wf (dr X0 (dr X1 X1)) X1 := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef97 (X0 X1 : G) : ((dr X1 X1) ◇ (wf X0 X1)) ◇ X0 = X1 := by
    first | exact superpose ef23 ef17 | exact superpose ef17 ef23
  have ef115 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef19 ef33 | exact superpose ef33 ef19
  have ef116 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef21 ef33 | exact superpose ef33 ef21
  have ef119 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef33 ef33
  have ef173 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef34 ef22 | exact superpose ef22 ef34
  have ef210 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef36 ef22 | exact superpose ef22 ef36
  have ef258 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef37 ef22 | exact superpose ef22 ef37
  have ef259 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef37 ef33 | exact superpose ef33 ef37
  have ef326 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef40 ef18 | exact superpose ef18 ef40
  have ef339 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef259 ef326 | exact superpose ef326 ef259
  have ef446 (X0 X1 : G) : (wf X0 X1) ◇ (dr (dr X1 X1) X1) = X0 := by
    first | exact superpose ef23 ef46 | exact superpose ef46 ef23
  have ef610 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef18 ef50 | exact superpose ef50 ef18
  have ef625 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef259 ef610 | exact superpose ef610 ef259
  have ef832 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef33 ef74 | exact superpose ef74 ef33
  have ef981 (X0 X1 : G) : dr X1 (dr X0 X0) = wdr (X0 ◇ X1) X0 := by
    first | exact superpose ef94 ef25 | exact superpose ef25 ef94
  have ef982 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = wdr (X0 ◇ X1) X0 := by
    first | exact superpose ef115 ef981 | exact superpose ef981 ef115
  have ef1011 (X0 X1 X2 : G) : X0 ◇ (dr X2 ((dr X0 X0) ◇ (wf (X1 ◇ X2) X0))) = X1 := by
    first | exact superpose ef97 ef46 | exact superpose ef46 ef97
  have ef1021 (X0 X1 X2 : G) : X0 ◇ (((wf (X1 ◇ X2) X0) ◇ X2) ◇ (dr X0 X0)) = X1 := by
    first | exact superpose ef50 ef1011 | exact superpose ef1011 ef50
  have ef1044 (X0 X1 X2 : G) : wf ((wf (X1 ◇ X2) X0) ◇ X2) X0 = X1 := by
    first | exact superpose ef23 ef1021 | exact superpose ef1021 ef23
  have ef1525 (X0 X1 X2 : G) : ((dr X2 X2) ◇ X0) ◇ ((wf (X0 ◇ X1) X2) ◇ X1) = X2 := by
    first | exact superpose ef23 ef79 | exact superpose ef79 ef23
  have ef1619 (X0 X1 X2 : G) : X2 ◇ (X2 ◇ (dl X0 ((wf (X0 ◇ X1) X2) ◇ X1))) = X2 := by
    first | exact superpose ef832 ef1525 | exact superpose ef1525 ef832
  have ef1839 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef116 ef33 | exact superpose ef33 ef116
  have ef3931 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef173 ef22 | exact superpose ef22 ef173
  have ef5858 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef339 ef82 | exact superpose ef82 ef339
  have ef5876 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3931 ef5858 | exact superpose ef5858 ef3931
  have ef6747 (X0 X1 X2 : G) : dr X1 (dr (dr X2 X2) X2) = dr X0 (dl (wf X0 X2) X1) := by
    first | exact superpose ef446 ef625 | exact superpose ef625 ef446
  have ef6788 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ (dr X2 X2)) = dr X0 (dl (wf X0 X2) X1) := by
    first | exact superpose ef115 ef6747 | exact superpose ef6747 ef115
  have ef6830 (X0 X1 X2 : G) : wf X1 X2 = dr X0 (dl (wf X0 X2) X1) := by
    first | exact superpose ef23 ef6788 | exact superpose ef6788 ef23
  have ef8893 (X0 X1 : G) : wdr X0 X1 = X1 ◇ ((dl X1 X0) ◇ X1) := by
    first | exact superpose ef21 ef982 | exact superpose ef982 ef21
  have ef9960 (X0 X1 X2 : G) : (wf (X0 ◇ X1) X2) ◇ X1 = wdr X0 X2 := by
    first | exact superpose ef1044 ef25 | exact superpose ef25 ef1044
  have ef54681 (X0 X1 X2 : G) : dr X2 (dl X0 X1) = wf X1 (wdl X2 X0) := by
    first | exact superpose ef26 ef6830 | exact superpose ef6830 ef26
  have ef54727 (X0 X1 X2 X3 : G) : (X3 ◇ (wf X0 X1)) ◇ X2 = dl (dl (wf X2 X1) X0) X3 := by
    first | exact superpose ef6830 ef210 | exact superpose ef210 ef6830
  have ef54765 (X0 X1 X2 X3 : G) : (X3 ◇ (wf X2 X1)) ◇ X0 = (X3 ◇ (wf X0 X1)) ◇ X2 := by
    first | exact superpose ef258 ef54727 | exact superpose ef54727 ef258
  have ef63834 (X0 X1 : G) : X1 ◇ (wdr X0 X1) = dr X1 (dl X1 X0) := by
    first | exact superpose ef8893 ef33 | exact superpose ef33 ef8893
  have ef64117 (X0 X1 : G) : X1 ◇ (wdr X0 X1) = wf X0 (wdl X1 X1) := by
    first | exact superpose ef54681 ef63834 | exact superpose ef63834 ef54681
  have ef115445 (X0 X1 X2 X3 : G) : dr X3 (wdr X0 X1) = (X2 ◇ X3) ◇ (wf (X0 ◇ X2) X1) := by
    first | exact superpose ef9960 ef50 | exact superpose ef50 ef9960
  have ef116409 (X0 X1 X2 X3 X4 : G) :
      dr X1 (X0 ◇ (dl X2 ((wf (X2 ◇ X3) X0) ◇ X3))) = (X4 ◇ X0) ◇ (X1 ◇ (dr X4 X0)) := by
    first | exact superpose ef1619 ef119 | exact superpose ef119 ef1619
  have ef116459 (X0 X1 X2 X3 : G) :
      dr X0 (dl X0 X1) = dr X1 (X0 ◇ (dl X2 ((wf (X2 ◇ X3) X0) ◇ X3))) := by
    first | exact superpose ef1619 ef625 | exact superpose ef625 ef1619
  have ef116620 (X0 X1 X2 X3 : G) :
      dr X0 (dl X0 X1) = ((dl X2 ((wf (X2 ◇ X3) X0) ◇ X3)) ◇ X1) ◇ X0 := by
    first | exact superpose ef50 ef116459 | exact superpose ef116459 ef50
  have ef116670 (X0 X1 X2 X3 : G) :
      dr X1 (dl X0 X0) = dr X1 (X0 ◇ (dl X2 ((wf (X2 ◇ X3) X0) ◇ X3))) := by
    first | exact superpose ef1839 ef116409 | exact superpose ef116409 ef1839
  have ef116961 (X0 X1 X2 X3 : G) :
      dr X0 (dl X0 X1) = (X3 ◇ (dr X2 (dl X1 (wf (X2 ◇ X3) X0)))) ◇ X0 := by
    first | exact superpose ef5876 ef116620 | exact superpose ef116620 ef5876
  have ef117010 (X0 X1 X2 X3 : G) :
      dr X1 (dl X0 X0) = ((dl X2 ((wf (X2 ◇ X3) X0) ◇ X3)) ◇ X1) ◇ X0 := by
    first | exact superpose ef50 ef116670 | exact superpose ef116670 ef50
  have ef117280 (X0 X1 X2 X3 : G) :
      dr X0 (dl X0 X1) = (X3 ◇ (wf (wf (X2 ◇ X3) X0) (wdl X2 X1))) ◇ X0 := by
    first | exact superpose ef54681 ef116961 | exact superpose ef116961 ef54681
  have ef117325 (X0 X1 X2 X3 : G) :
      dr X1 (dl X0 X0) = (X3 ◇ (dr X2 (dl X1 (wf (X2 ◇ X3) X0)))) ◇ X0 := by
    first | exact superpose ef5876 ef117010 | exact superpose ef117010 ef5876
  have ef117541 (X0 X1 X2 X3 : G) :
      dr X0 (dl X0 X1) = (X3 ◇ (wf X0 (wdl X2 X1))) ◇ (wf (X2 ◇ X3) X0) := by
    first | exact superpose ef54765 ef117280 | exact superpose ef117280 ef54765
  have ef117579 (X0 X1 X2 X3 : G) :
      dr X1 (dl X0 X0) = (X3 ◇ (wf (wf (X2 ◇ X3) X0) (wdl X2 X1))) ◇ X0 := by
    first | exact superpose ef54681 ef117325 | exact superpose ef117325 ef54681
  have ef117758 (X0 X1 X2 : G) : dr X0 (dl X0 X1) = dr (wf X0 (wdl X2 X1)) (wdr X2 X0) := by
    first | exact superpose ef115445 ef117541 | exact superpose ef117541 ef115445
  have ef117790 (X0 X1 X2 X3 : G) :
      dr X1 (dl X0 X0) = (X3 ◇ (wf X0 (wdl X2 X1))) ◇ (wf (X2 ◇ X3) X0) := by
    first | exact superpose ef54765 ef117579 | exact superpose ef117579 ef54765
  have ef117942 (X0 X1 X2 : G) : wf X1 (wdl X0 X0) = dr (wf X0 (wdl X2 X1)) (wdr X2 X0) := by
    first | exact superpose ef54681 ef117758 | exact superpose ef117758 ef54681
  have ef117973 (X0 X1 X2 : G) : dr X1 (dl X0 X0) = dr (wf X0 (wdl X2 X1)) (wdr X2 X0) := by
    first | exact superpose ef115445 ef117790 | exact superpose ef117790 ef115445
  have ef118093 (X0 X1 X2 : G) : X0 ◇ (wdr X1 X0) = dr (wf X0 (wdl X2 X1)) (wdr X2 X0) := by
    first | exact superpose ef64117 ef117942 | exact superpose ef117942 ef64117
  have ef118115 (X0 X1 X2 : G) : wf X0 (wdl X1 X0) = dr (wf X0 (wdl X2 X1)) (wdr X2 X0) := by
    first | exact superpose ef54681 ef117973 | exact superpose ef117973 ef54681
  have ef118213 (X0 X1 : G) : X0 ◇ (wdr X1 X0) = wf X0 (wdl X1 X0) := by
    first | exact superpose ef118093 ef118115 | exact superpose ef118115 ef118093
  have ef200424 : x ◇ y ≠ x ◇ (wdr (wf y x) x) := by
    first | exact superpose ef118213 ef28 | exact superpose ef28 ef118213
  have ef200425 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef25 ef200424 | exact superpose ef200424 ef25
  exact absurd rfl ef200425

set_option maxHeartbeats 800000 in
/-- Equation 2847 `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x` holds of the operation `x □ y := (y◇(x◇(y/y)))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_2847_21 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = b ◇ (a ◇ (dr b b)))
    (x : G) :
    x = wf (wf (wf x (wf x x)) x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X0 ◇ (dr X1 X1)) := mod_symm (hwdef ..)
  have ef20 : x ≠ wf (wf (wf x (wf x x)) x) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef37 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef70 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef84 (X0 X1 : G) : (dr (X1 ◇ X0) (X1 ◇ X0)) ◇ (wf X0 (X1 ◇ X0)) = X1 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef85 (X0 X1 : G) : ((dr X1 X1) ◇ (wf X0 X1)) ◇ X0 = X1 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef87 (X0 X1 X2 : G) : (X0 ◇ (dr X1 X1)) ◇ ((X2 ◇ X1) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef93 (X0 X1 X2 : G) : (wf X0 (X1 ◇ X2)) ◇ ((X0 ◇ (dr (X1 ◇ X2) (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef94 (X0 X1 X2 : G) : (wf X0 (X1 ◇ X2)) ◇ ((X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = X2 := by
    first | exact superpose ef40 ef93 | exact superpose ef93 ef40
  have ef98 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (wf X0 (X1 ◇ X0)) = X1 := by
    first | exact superpose ef40 ef84 | exact superpose ef84 ef40
  have ef101 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef102 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef106 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef13 ef23 | exact superpose ef23 ef13
  have ef110 (X0 X1 : G) : dr X1 X0 = (dr X1 X1) ◇ (wf X0 X1) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef111 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef23
  have ef125 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef133 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef40 ef106 | exact superpose ef106 ef40
  have ef151 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef159 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef244 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef245 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef280 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef305 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef315 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef30 ef18 | exact superpose ef18 ef30
  have ef443 (X0 X1 : G) : X1 ◇ X0 = wf (X1 ◇ (X0 ◇ X1)) X1 := by
    first | exact superpose ef36 ef19 | exact superpose ef19 ef36
  have ef453 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef528 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef37 ef27 | exact superpose ef27 ef37
  have ef635 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef912 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef914 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef944 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef280 ef914 | exact superpose ef914 ef280
  have ef945 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef125 ef912 | exact superpose ef912 ef125
  have ef958 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef944 | exact superpose ef944 ef30
  have ef989 (X0 X1 : G) : dr X0 X0 = (dl (wf X1 X0) X1) ◇ X0 := by
    first | exact superpose ef85 ef27 | exact superpose ef27 ef85
  have ef991 (X0 X1 X2 : G) : X0 ◇ (dr X2 ((dr X0 X0) ◇ (wf (X1 ◇ X2) X0))) = X1 := by
    first | exact superpose ef85 ef36 | exact superpose ef36 ef85
  have ef1001 (X0 X1 X2 : G) : X0 ◇ (((wf (X1 ◇ X2) X0) ◇ X2) ◇ (dr X0 X0)) = X1 := by
    first | exact superpose ef40 ef991 | exact superpose ef991 ef40
  have ef1022 (X0 X1 X2 : G) : wf ((wf (X1 ◇ X2) X0) ◇ X2) X0 = X1 := by
    first | exact superpose ef19 ef1001 | exact superpose ef1001 ef19
  have ef1788 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef102 | exact superpose ef102 ef30
  have ef1791 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef102 | exact superpose ef102 ef15
  have ef1802 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef102 ef23 | exact superpose ef23 ef102
  have ef1865 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef958 ef1788 | exact superpose ef1788 ef958
  have ef1897 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef244 ef1865 | exact superpose ef1865 ef244
  have ef1910 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1897 | exact superpose ef1897 ef23
  have ef2392 (X0 X1 X2 : G) : (X2 ◇ (dr X0 X0)) ◇ (dr X0 X1) = dl (wf X1 X0) X2 := by
    first | exact superpose ef110 ef30 | exact superpose ef30 ef110
  have ef2531 (X0 X1 X2 X3 : G) :
      X1 ◇ (X2 ◇ (dr X3 X3)) = dl (X0 ◇ X1) ((X0 ◇ X3) ◇ (wf X2 X3)) := by
    first | exact superpose ef87 ef72 | exact superpose ef72 ef87
  have ef2548 (X0 X1 X2 X3 : G) :
      X1 ◇ (X2 ◇ (dr X3 X3)) = X3 ◇ (((wf X2 X3) ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef280 ef2531 | exact superpose ef2531 ef280
  have ef2613 (X1 X2 X3 : G) : X1 ◇ (X2 ◇ (dr X3 X3)) = X3 ◇ (dl X1 (wf X2 X3)) := by
    first | exact superpose ef30 ef2548 | exact superpose ef2548 ef30
  have ef2747 (X0 X1 : G) : wf (X1 ◇ X0) X1 = X1 ◇ (dr X0 X1) := by
    first | exact superpose ef111 ef19 | exact superpose ef19 ef111
  have ef2776 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ X0) = dl ((dr X0 X1) ◇ X2) (dr X1 X3) := by
    first | exact superpose ef111 ef72 | exact superpose ef72 ef111
  have ef2803 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ X0) = X1 ◇ (X3 ◇ ((dr X0 X1) ◇ X2)) := by
    first | exact superpose ef125 ef2776 | exact superpose ef2776 ef125
  have ef3380 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef23 ef151 | exact superpose ef151 ef23
  have ef3435 (X0 X1 X2 X3 : G) : (X2 ◇ (dr X0 X1)) ◇ X3 = (dl (X3 ◇ X2) X1) ◇ X0 := by
    first | exact superpose ef151 ef13 | exact superpose ef13 ef151
  have ef3440 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef151 ef26 | exact superpose ef26 ef151
  have ef3448 (X0 X1 X2 X3 : G) : (X2 ◇ (dr X0 X1)) ◇ X3 = (X2 ◇ (dr X3 X1)) ◇ X0 := by
    first | exact superpose ef635 ef3435 | exact superpose ef3435 ef635
  have ef3493 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1910 ef3380 | exact superpose ef3380 ef1910
  have ef3529 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef40 ef3493 | exact superpose ef3493 ef40
  have ef3547 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef102 ef3529 | exact superpose ef3529 ef102
  have ef3605 (X0 X1 X2 : G) : wf X1 (X0 ◇ X1) = (X0 ◇ X2) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    first | exact superpose ef98 ef14 | exact superpose ef14 ef98
  have ef3665 (X0 X1 X2 : G) : wf X1 (X0 ◇ X1) = X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) := by
    first | exact superpose ef945 ef3605 | exact superpose ef3605 ef945
  have ef3724 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X0 ◇ (dr (X1 ◇ (X0 ◇ X1)) X0) := by
    first | exact superpose ef23 ef3665 | exact superpose ef3665 ef23
  have ef3767 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X0 ◇ (dr (X1 ◇ X0) (X0 ◇ X1)) := by
    first | exact superpose ef1910 ef3724 | exact superpose ef3724 ef1910
  have ef3797 (X0 X1 : G) : wf X1 (X0 ◇ X1) = X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef40 ef3767 | exact superpose ef3767 ef40
  have ef3877 (X0 X1 : G) : wf (dl X1 X0) X0 = dl (dr X0 X0) X1 := by
    first | exact superpose ef159 ef19 | exact superpose ef19 ef159
  have ef3886 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef159 ef18 | exact superpose ef18 ef159
  have ef4099 (X0 X1 X2 : G) :
      (wf X2 ((dr X0 X1) ◇ X1)) ◇ ((X2 ◇ (dr ((dr X0 X1) ◇ X1) X0)) ◇ (dr X0 X1)) = X1 := by
    first | exact superpose ef111 ef94 | exact superpose ef94 ef111
  have ef4204 (X0 X1 X2 : G) :
      (wf X2 ((dr X0 X1) ◇ X1)) ◇ ((X2 ◇ (dr (dr X0 X1) X0)) ◇ ((dr X0 X1) ◇ X1)) = X1 := by
    first | exact superpose ef3448 ef4099 | exact superpose ef4099 ef3448
  have ef4276 (X0 X1 X2 : G) :
      X1 ◇ ((X2 ◇ (dr (dr X0 X1) X0)) ◇ ((dr X0 X1) ◇ (wf X2 ((dr X0 X1) ◇ X1)))) = X1 := by
    first | exact superpose ef945 ef4204 | exact superpose ef4204 ef945
  have ef4336 (X0 X1 X2 : G) :
      (wf X2 ((dr X0 X1) ◇ X1)) ◇ ((X2 ◇ (dr (dr X0 X1) X0)) ◇ X0) = X1 := by
    first | exact superpose ef2803 ef4276 | exact superpose ef4276 ef2803
  have ef4379 (X0 X1 X2 : G) :
      (wf X2 ((dr X0 X1) ◇ X1)) ◇ ((X2 ◇ (dr X0 X0)) ◇ (dr X0 X1)) = X1 := by
    first | exact superpose ef3448 ef4336 | exact superpose ef4336 ef3448
  have ef4411 (X0 X1 X2 : G) : (wf X2 ((dr X0 X1) ◇ X1)) ◇ (dl (wf X1 X0) X2) = X1 := by
    first | exact superpose ef2392 ef4379 | exact superpose ef4379 ef2392
  have ef4439 (X0 X1 X2 : G) : (wf X1 X0) ◇ (dl (wf X2 ((dr X0 X1) ◇ X1)) X2) = X1 := by
    first | exact superpose ef958 ef4411 | exact superpose ef4411 ef958
  have ef4455 (X0 X1 X2 : G) : (wf X1 X0) ◇ (dl (wf X2 X0) X2) = X1 := by
    first | exact superpose ef15 ef4439 | exact superpose ef4439 ef15
  have ef5458 (X0 X1 : G) : dr (dr X1 X1) X1 = dl (wf X0 X1) X0 := by
    first | exact superpose ef19 ef305 | exact superpose ef305 ef19
  have ef5464 (X0 X1 X2 X3 : G) : dr X1 ((X1 ◇ X2) ◇ (X0 ◇ X3)) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef70 ef305 | exact superpose ef305 ef70
  have ef5469 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef151 ef305 | exact superpose ef305 ef151
  have ef5520 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef40 ef5469 | exact superpose ef5469 ef40
  have ef5525 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef40 ef5464 | exact superpose ef5464 ef40
  have ef5530 (X0 X1 : G) : dl (wf X0 X1) X0 = (dl X1 X1) ◇ X1 := by
    first | exact superpose ef1791 ef5458 | exact superpose ef5458 ef1791
  have ef5575 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef635 ef5520 | exact superpose ef5520 ef635
  have ef5578 (X0 X2 X3 : G) : dl X2 (X0 ◇ X3) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef30 ef5525 | exact superpose ef5525 ef30
  have ef5604 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef30 ef5575 | exact superpose ef5575 ef30
  have ef5646 (X0 X1 X2 : G) : (wf X1 X0) ◇ X2 = dl (dr X0 X1) (dl X2 (dr X0 X0)) := by
    first | exact superpose ef110 ef315 | exact superpose ef315 ef110
  have ef5693 (X0 X1 X2 : G) : (wf X1 X0) ◇ X2 = (dl (dr X0 X0) (dr X0 X1)) ◇ X2 := by
    first | exact superpose ef3886 ef5646 | exact superpose ef5646 ef3886
  have ef5730 (X0 X1 X2 : G) : (wf X1 X0) ◇ X2 = X0 ◇ ((dr X2 (dr X0 X1)) ◇ X0) := by
    first | exact superpose ef3440 ef5693 | exact superpose ef5693 ef3440
  have ef5753 (X0 X1 X2 : G) : (wf X1 X0) ◇ X2 = X0 ◇ ((dr X2 X0) ◇ (dr X0 X1)) := by
    first | exact superpose ef3547 ef5730 | exact superpose ef5730 ef3547
  have ef6209 (X0 X1 : G) : X0 ◇ (dl X1 X0) = wf (dl X0 X1) X0 := by
    first | exact superpose ef159 ef443 | exact superpose ef443 ef159
  have ef6434 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dl X0 X1) = dr (dl (X3 ◇ X1) X0) X2 := by
    first | exact superpose ef528 ef102 | exact superpose ef102 ef528
  have ef6489 (X0 X1 X2 X3 : G) : X0 ◇ (dr X2 (X3 ◇ X1)) = (dl X2 X3) ◇ (dl X0 X1) := by
    first | exact superpose ef1802 ef6434 | exact superpose ef6434 ef1802
  have ef6571 (X0 X1 X2 X3 : G) : X0 ◇ ((X1 ◇ X2) ◇ X3) = (dl X2 X3) ◇ (dl X0 X1) := by
    first | exact superpose ef40 ef6489 | exact superpose ef6489 ef40
  have ef8855 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (dr X0 X0)) = dr X1 (dl (wf X2 X0) X2) := by
    first | exact superpose ef989 ef23 | exact superpose ef23 ef989
  have ef8886 (X0 X1 X2 : G) : dl (dr X0 X0) X2 = X0 ◇ (dr (dl (wf X1 X0) X1) X2) := by
    first | exact superpose ef989 ef635 | exact superpose ef635 ef989
  have ef8896 (X0 X1 X2 : G) :
      dl (dr (X0 ◇ X1) (X0 ◇ X1)) X0 = dr X1 (dl (wf X2 (X0 ◇ X1)) X2) := by
    first | exact superpose ef989 ef305 | exact superpose ef305 ef989
  have ef8927 (X0 X1 X2 : G) :
      dr X1 (dl (wf X2 (X0 ◇ X1)) X2) = dl (dr X0 (X0 ◇ X1)) (X0 ◇ X1) := by
    first | exact superpose ef5604 ef8896 | exact superpose ef8896 ef5604
  have ef8933 (X0 X1 X2 : G) : dl (dr X0 X0) X2 = X0 ◇ (X1 ◇ (dr X2 (wf X1 X0))) := by
    first | exact superpose ef1802 ef8886 | exact superpose ef8886 ef1802
  have ef8962 (X0 X1 X2 : G) : wf X1 X0 = dr X1 (dl (wf X2 X0) X2) := by
    first | exact superpose ef19 ef8855 | exact superpose ef8855 ef19
  have ef8991 (X0 X1 X2 : G) :
      dr X1 (dl (wf X2 (X0 ◇ X1)) X2) = dl X0 ((dr X0 (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef5578 ef8927 | exact superpose ef8927 ef5578
  have ef8995 (X0 X1 X2 : G) : wf (dl X2 X0) X0 = X0 ◇ (X1 ◇ (dr X2 (wf X1 X0))) := by
    first | exact superpose ef3877 ef8933 | exact superpose ef8933 ef3877
  have ef9038 (X0 X1 X2 : G) :
      dr X1 (dl (wf X2 (X0 ◇ X1)) X2) = dl X0 ((dr X0 X1) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef3547 ef8991 | exact superpose ef8991 ef3547
  have ef9064 (X0 X1 X2 : G) :
      dr X1 (dl (wf X2 (X0 ◇ X1)) X2) = X0 ◇ ((dr X1 (dr X0 X1)) ◇ X0) := by
    first | exact superpose ef453 ef9038 | exact superpose ef9038 ef453
  have ef9086 (X0 X1 X2 : G) :
      dr X1 (dl (wf X2 (X0 ◇ X1)) X2) = X0 ◇ ((dr X1 X0) ◇ (dr X0 X1)) := by
    first | exact superpose ef3547 ef9064 | exact superpose ef9064 ef3547
  have ef9103 (X0 X1 X2 : G) : dr X1 (dl (wf X2 (X0 ◇ X1)) X2) = (wf X1 X0) ◇ X1 := by
    first | exact superpose ef5753 ef9086 | exact superpose ef9086 ef5753
  have ef9117 (X0 X1 : G) : wf X1 (X0 ◇ X1) = (wf X1 X0) ◇ X1 := by
    first | exact superpose ef8962 ef9103 | exact superpose ef9103 ef8962
  have ef19193 (X0 X1 : G) : wf (wf X0 X1) X1 = X1 ◇ (dr (X0 ◇ (dr X1 X1)) X1) := by
    first | exact superpose ef19 ef2747 | exact superpose ef2747 ef19
  have ef19322 (X0 X1 : G) : wf (wf X0 X1) X1 = X1 ◇ (dr (X0 ◇ X1) (dr X1 X1)) := by
    first | exact superpose ef1910 ef19193 | exact superpose ef19193 ef1910
  have ef19380 (X0 X1 : G) : wf (wf X0 X1) X1 = X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) := by
    first | exact superpose ef101 ef19322 | exact superpose ef19322 ef101
  have ef19427 (X0 X1 : G) : wf (wf X0 X1) X1 = dr X1 (X0 ◇ X1) := by
    first | exact superpose ef23 ef19380 | exact superpose ef19380 ef23
  have ef19456 (X0 X1 : G) : (X1 ◇ X1) ◇ X0 = wf (wf X0 X1) X1 := by
    first | exact superpose ef40 ef19427 | exact superpose ef19427 ef40
  have ef27642 (X0 X1 X2 X3 X4 : G) :
      (wf X0 X1) ◇ (X2 ◇ X3) = ((X3 ◇ X0) ◇ X2) ◇ (dl (wf X4 X1) X4) := by
    first | exact superpose ef4455 ef133 | exact superpose ef133 ef4455
  have ef33539 (X0 X1 X2 X3 : G) :
      dr (dl X1 X1) (dl X2 X3) = ((X1 ◇ X2) ◇ X3) ◇ (dl (wf X0 X1) X0) := by
    first | exact superpose ef5530 ef245 | exact superpose ef245 ef5530
  have ef33653 (X1 X2 X3 : G) : dr (dl X1 X1) (dl X2 X3) = (wf X2 X1) ◇ (X3 ◇ X1) := by
    first | exact superpose ef27642 ef33539 | exact superpose ef33539 ef27642
  have ef33796 (X1 X2 X3 : G) : (wf X2 X1) ◇ (X3 ◇ X1) = X1 ◇ (dr (dl X2 X3) X1) := by
    first | exact superpose ef1802 ef33653 | exact superpose ef33653 ef1802
  have ef33909 (X1 X2 X3 : G) : (wf X2 X1) ◇ (X3 ◇ X1) = X1 ◇ (X3 ◇ (dr X1 X2)) := by
    first | exact superpose ef1802 ef33796 | exact superpose ef33796 ef1802
  have ef73146 : x ≠ (x ◇ x) ◇ (wf x (wf x x)) := by
    first | exact superpose ef19456 ef20 | exact superpose ef20 ef19456
  have ef140112 (X0 : G) : (wf X0 (X0 ◇ X0)) ◇ ((wf X0 (X0 ◇ X0)) ◇ X0) = X0 := by
    first | exact superpose ef3797 ef94 | exact superpose ef94 ef3797
  have ef140537 (X0 : G) : ((wf X0 X0) ◇ X0) ◇ (((wf X0 X0) ◇ X0) ◇ X0) = X0 := by
    first | exact superpose ef9117 ef140112 | exact superpose ef140112 ef9117
  have ef140922 (X0 : G) : (dl X0 X0) ◇ (dl ((wf X0 X0) ◇ X0) (wf X0 X0)) = X0 := by
    first | exact superpose ef6571 ef140537 | exact superpose ef140537 ef6571
  have ef141286 (X0 : G) : (dl X0 X0) ◇ (X0 ◇ (dr (wf X0 X0) (wf X0 X0))) = X0 := by
    first | exact superpose ef635 ef140922 | exact superpose ef140922 ef635
  have ef141626 (X0 : G) : (wf X0 X0) ◇ (dl (dl X0 X0) (wf X0 (wf X0 X0))) = X0 := by
    first | exact superpose ef2613 ef141286 | exact superpose ef141286 ef2613
  have ef141922 (X0 : G) : (wf X0 X0) ◇ (((wf X0 (wf X0 X0)) ◇ X0) ◇ X0) = X0 := by
    first | exact superpose ef244 ef141626 | exact superpose ef141626 ef244
  have ef142189 (X0 : G) : X0 ◇ (((wf X0 (wf X0 X0)) ◇ X0) ◇ (dr X0 X0)) = X0 := by
    first | exact superpose ef33909 ef141922 | exact superpose ef141922 ef33909
  have ef142419 (X0 : G) : wf ((wf X0 (wf X0 X0)) ◇ X0) X0 = X0 := by
    first | exact superpose ef19 ef142189 | exact superpose ef142189 ef19
  have ef146710 (X0 : G) : wf (X0 ◇ X0) X0 = wf X0 (wf X0 X0) := by
    first | exact superpose ef142419 ef1022 | exact superpose ef1022 ef142419
  have ef146795 (X0 : G) : X0 ◇ (dr X0 X0) = wf X0 (wf X0 X0) := by
    first | exact superpose ef2747 ef146710 | exact superpose ef146710 ef2747
  have ef156023 : x ≠ (x ◇ x) ◇ (x ◇ (dr x x)) := by
    first | exact superpose ef146795 ef73146 | exact superpose ef73146 ef146795
  have ef156026 : x ≠ x ◇ (dl (x ◇ x) (wf x x)) := by
    first | exact superpose ef2613 ef156023 | exact superpose ef156023 ef2613
  have ef156070 : x ≠ x ◇ (x ◇ (dr x (wf x x))) := by
    first | exact superpose ef635 ef156026 | exact superpose ef156026 ef635
  have ef156108 : x ≠ wf (dl x x) x := by
    first | exact superpose ef8995 ef156070 | exact superpose ef156070 ef8995
  have ef156140 : x ≠ x ◇ (dl x x) := by
    first | exact superpose ef6209 ef156108 | exact superpose ef156108 ef6209
  subsumption ef156140 ef17

theorem Equation2847_termStructuralFromFin_Equation898_qdiv :
    Law2847.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.var 1) (.op (.var 0) (.rdv (.var 1) (.var 1)))) (.op (.var 0) (.ldv (.op (.var 1) (.var 0)) (.var 0))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2847.models_iff]
    exact fun x ↦
      @qaux898_2847_21 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_21R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_21L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_21 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

/-- Right translation of `x □ y := ((x/x)◇(y◇x))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_56R [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (t : G) :
    Function.Injective (fun p : G ↦ wf p t) := by
  intro p q hhyp
  replace hhyp : wf p t = wf q t := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef13 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef21 : wf p t = wf q t := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef24 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef27 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef28 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef31 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef18 ef13 | exact superpose ef13 ef18
  have ef34 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef44 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef16 ef14 | exact superpose ef14 ef16
  have ef63 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef18 ef15 | exact superpose ef15 ef18
  have ef71 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef74 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef90 (X0 X1 : G) : dr X0 X0 = (X0 ◇ (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef20 ef14 | exact superpose ef14 ef20
  have ef93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1))) ◇ (dr X0 X0) = X2 := by
    first | exact superpose ef20 ef14 | exact superpose ef14 ef20
  have ef97 (X0 X1 : G) : X1 ◇ X0 = dl (dr X0 X0) (wf X0 X1) := by
    first | exact superpose ef20 ef19 | exact superpose ef19 ef20
  have ef107 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef16 ef27 | exact superpose ef27 ef16
  have ef109 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef18 ef27 | exact superpose ef27 ef18
  have ef113 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef15 ef27 | exact superpose ef27 ef15
  have ef114 (X0 X1 : G) : X0 ◇ (wf X0 X1) = dr (dr X0 X0) X1 := by
    first | exact superpose ef20 ef27 | exact superpose ef27 ef20
  have ef131 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef27 ef19 | exact superpose ef19 ef27
  have ef140 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef44 ef113 | exact superpose ef113 ef44
  have ef148 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (dl X2 X3))) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef13 ef28 | exact superpose ef28 ef13
  have ef158 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef28 ef27 | exact superpose ef27 ef28
  have ef166 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef28 ef19 | exact superpose ef19 ef28
  have ef182 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) ◇ ((X1 ◇ (dl X2 X3)) ◇ X0) = X2 := by
    first | exact superpose ef140 ef148 | exact superpose ef148 ef140
  have ef241 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef14 ef31 | exact superpose ef31 ef14
  have ef258 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef31 ef27 | exact superpose ef27 ef31
  have ef293 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef15 ef34 | exact superpose ef34 ef15
  have ef318 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef34 ef27 | exact superpose ef27 ef34
  have ef323 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1))) ◇ (X1 ◇ X2) = X3 := by
    first | exact superpose ef34 ef14 | exact superpose ef14 ef34
  have ef324 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef34 ef15 | exact superpose ef15 ef34
  have ef339 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef258 ef324 | exact superpose ef324 ef258
  have ef340 (X0 X1 X3 : G) : dr X1 (dl X0 (X3 ◇ (dl X0 X1))) = X3 := by
    first | exact superpose ef258 ef323 | exact superpose ef323 ef258
  have ef446 (X0 X1 : G) : (wf X0 X1) ◇ (dr X0 (dr X0 X0)) = X1 := by
    first | exact superpose ef20 ef40 | exact superpose ef40 ef20
  have ef460 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef40 ef27 | exact superpose ef27 ef40
  have ef472 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef44 ef460 | exact superpose ef460 ef44
  have ef480 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef107 ef446 | exact superpose ef446 ef107
  have ef646 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef63 ef40 | exact superpose ef40 ef63
  have ef926 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef40 ef74 | exact superpose ef74 ef40
  have ef929 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef31 ef74 | exact superpose ef74 ef31
  have ef957 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef293 ef929 | exact superpose ef929 ef293
  have ef959 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef131 ef926 | exact superpose ef926 ef131
  have ef971 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef34 ef957 | exact superpose ef957 ef34
  have ef983 : dr q q = (q ◇ (wf p t)) ◇ t := by
    first | exact superpose ef21 ef90 | exact superpose ef90 ef21
  have ef1007 (X0 X1 : G) : (dl (wf X0 X1) X1) ◇ (dr X0 X0) = X0 := by
    first | exact superpose ef90 ef31 | exact superpose ef31 ef90
  have ef1009 (X0 X1 X2 : G) : (dr X0 X0) ◇ (dr X2 (X0 ◇ (wf X0 (X1 ◇ X2)))) = X1 := by
    first | exact superpose ef90 ef40 | exact superpose ef40 ef90
  have ef1014 (X0 X1 X2 : G) : (dr X0 X0) ◇ (((wf X0 (X1 ◇ X2)) ◇ X2) ◇ X0) = X1 := by
    first | exact superpose ef44 ef1009 | exact superpose ef1009 ef44
  have ef1031 (X0 X1 X2 : G) : wf X0 ((wf X0 (X1 ◇ X2)) ◇ X2) = X1 := by
    first | exact superpose ef20 ef1014 | exact superpose ef1014 ef20
  have ef1041 : t ◇ q = dl (dr q q) (wf p t) := by
    first | exact superpose ef21 ef97 | exact superpose ef97 ef21
  have ef1448 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef18 ef109 | exact superpose ef109 ef18
  have ef1463 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef16 ef109 | exact superpose ef109 ef16
  have ef3163 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef158 ef27 | exact superpose ef27 ef158
  have ef3240 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef44 ef3163 | exact superpose ef3163 ef44
  have ef3399 (X0 X1 X2 : G) : X2 ◇ X1 = ((wf X1 X2) ◇ X0) ◇ (X0 ◇ (dr X1 X1)) := by
    first | exact superpose ef93 ef71 | exact superpose ef71 ef93
  have ef3413 (X0 X1 X2 : G) : X2 ◇ X1 = (X1 ◇ X0) ◇ (dl ((wf X1 X2) ◇ X0) X1) := by
    first | exact superpose ef3240 ef3399 | exact superpose ef3399 ef3240
  have ef3488 (X0 X1 X2 : G) : X2 ◇ X1 = (X1 ◇ X0) ◇ (X0 ◇ (dr (wf X1 X2) X1)) := by
    first | exact superpose ef646 ef3413 | exact superpose ef3413 ef646
  have ef3545 (X1 X2 : G) : X2 ◇ X1 = dl (dr (wf X1 X2) X1) X1 := by
    first | exact superpose ef34 ef3488 | exact superpose ef3488 ef34
  have ef3724 (X0 X1 : G) : dl X0 X1 = wf X0 (dl X1 (dr X0 X0)) := by
    first | exact superpose ef166 ef20 | exact superpose ef20 ef166
  have ef3733 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef166 ef19 | exact superpose ef19 ef166
  have ef3805 (X0 X1 : G) : dl X0 X1 = wf X0 (X0 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef131 ef3724 | exact superpose ef3724 ef131
  have ef7626 (X0 X1 : G) : dr X0 (dr X0 X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef20 ef318 | exact superpose ef318 ef20
  have ef7667 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef107 ef7626 | exact superpose ef7626 ef107
  have ef7983 (X0 X1 X2 : G) : dr X1 (dl X2 X0) = dr X0 (dl X2 X1) := by
    first | exact superpose ef339 ef17 | exact superpose ef17 ef339
  have ef8004 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef339 ef74 | exact superpose ef74 ef339
  have ef8034 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef3733 ef8004 | exact superpose ef8004 ef3733
  have ef8155 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = dr X1 (dl X2 (dr X0 X0)) := by
    first | exact superpose ef90 ef340 | exact superpose ef340 ef90
  have ef8169 (X0 X1 X2 : G) : dl X0 X1 = dl X2 (X0 ◇ (dl X2 X1)) := by
    first | exact superpose ef340 ef24 | exact superpose ef24 ef340
  have ef8199 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = dr X1 (X0 ◇ (X0 ◇ X2)) := by
    first | exact superpose ef131 ef8155 | exact superpose ef8155 ef131
  have ef8222 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = ((X0 ◇ X2) ◇ X1) ◇ X0 := by
    first | exact superpose ef44 ef8199 | exact superpose ef8199 ef44
  have ef8237 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = (dr X2 X0) ◇ (X1 ◇ X0) := by
    first | exact superpose ef472 ef8222 | exact superpose ef8222 ef472
  have ef8261 : t = (wf p t) ◇ (q ◇ (q ◇ q)) := by
    first | exact superpose ef21 ef480 | exact superpose ef480 ef21
  have ef8266 (X0 X1 : G) : X1 ◇ X1 = (dl X0 X1) ◇ (wf X1 X0) := by
    first | exact superpose ef480 ef241 | exact superpose ef241 ef480
  have ef8352 : t = q ◇ (q ◇ (q ◇ (wf p t))) := by
    first | exact superpose ef959 ef8261 | exact superpose ef8261 ef959
  have ef11717 (X0 X1 X2 : G) : (dr X0 X0) ◇ (X1 ◇ X0) = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef1007 ef27 | exact superpose ef27 ef1007
  have ef11797 (X0 X1 X2 : G) : wf X0 X1 = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef20 ef11717 | exact superpose ef11717 ef20
  have ef14695 (X0 X1 X2 : G) : dr (dr (wf X1 X0) X1) X2 = (dl X2 (X0 ◇ X1)) ◇ X1 := by
    first | exact superpose ef3545 ef1448 | exact superpose ef1448 ef3545
  have ef14696 (X0 : G) : dr (dr q q) X0 = (dl X0 (t ◇ q)) ◇ (wf p t) := by
    first | exact superpose ef1041 ef1448 | exact superpose ef1448 ef1041
  have ef14883 (X0 : G) : dr (dr q q) X0 = q ◇ (dr X0 (dl (wf p t) t)) := by
    first | exact superpose ef8034 ef14696 | exact superpose ef14696 ef8034
  have ef14884 (X0 X1 X2 : G) : dr (dr (wf X1 X0) X1) X2 = X1 ◇ (dr X2 (dl X1 X0)) := by
    first | exact superpose ef8034 ef14695 | exact superpose ef14695 ef8034
  have ef14963 (X0 : G) : dr (dr q q) X0 = q ◇ (wf p X0) := by
    first | exact superpose ef11797 ef14883 | exact superpose ef14883 ef11797
  have ef14964 (X0 X1 X2 : G) : (dl X2 X1) ◇ (wf X1 X0) = X1 ◇ (dr X2 (dl X1 X0)) := by
    first | exact superpose ef1463 ef14884 | exact superpose ef14884 ef1463
  have ef15008 (X0 : G) : q ◇ (wf q X0) = q ◇ (wf p X0) := by
    first | exact superpose ef114 ef14963 | exact superpose ef14963 ef114
  have ef40127 (X0 : G) : dr X0 (dl (wf p t) t) = (dr q q) ◇ (X0 ◇ q) := by
    first | exact superpose ef983 ef258 | exact superpose ef258 ef983
  have ef40640 (X0 : G) : wf q X0 = dr X0 (dl (wf p t) t) := by
    first | exact superpose ef20 ef40127 | exact superpose ef40127 ef20
  have ef40948 (X0 : G) : wf q X0 = wf p X0 := by
    first | exact superpose ef11797 ef40640 | exact superpose ef40640 ef11797
  have ef44268 (X0 X1 : G) : dl X0 X0 = wf X0 (dl (wf X0 X1) X1) := by
    first | exact superpose ef7667 ef3805 | exact superpose ef3805 ef7667
  have ef64018 : q = ((q ◇ (wf p t)) ◇ t) ◇ q := by
    first | exact superpose ef8352 ef14 | exact superpose ef14 ef8352
  have ef64229 : q = (dr (wf p t) q) ◇ (t ◇ q) := by
    first | exact superpose ef472 ef64018 | exact superpose ef64018 ef472
  have ef64316 : q = q ◇ (wf q (dl (wf p t) t)) := by
    first | exact superpose ef8237 ef64229 | exact superpose ef64229 ef8237
  have ef64380 : q = q ◇ (wf p (dl (wf p t) t)) := by
    first | exact superpose ef15008 ef64316 | exact superpose ef64316 ef15008
  have ef64439 : q = q ◇ (dl p p) := by
    first | exact superpose ef44268 ef64380 | exact superpose ef64380 ef44268
  have ef64492 : q = p ◇ (dl q p) := by
    first | exact superpose ef971 ef64439 | exact superpose ef64439 ef971
  have ef67110 : dl q q = dl p p := by
    first | exact superpose ef64492 ef8169 | exact superpose ef8169 ef64492
  have ef67111 (X0 : G) : q = ((X0 ◇ p) ◇ p) ◇ (q ◇ X0) := by
    first | exact superpose ef64492 ef182 | exact superpose ef182 ef64492
  have ef67296 : q = dr q (dl p p) := by
    first | exact superpose ef258 ef67111 | exact superpose ef67111 ef258
  have ef67361 : q = dr p (dl p q) := by
    first | exact superpose ef7983 ef67296 | exact superpose ef67296 ef7983
  have ef68498 : q ◇ q = (dl p p) ◇ (wf q q) := by
    first | exact superpose ef67110 ef8266 | exact superpose ef8266 ef67110
  have ef68499 : q ◇ q = (dl p p) ◇ (wf p q) := by
    first | exact superpose ef40948 ef68498 | exact superpose ef68498 ef40948
  have ef68530 : q ◇ q = p ◇ (dr p (dl p q)) := by
    first | exact superpose ef14964 ef68499 | exact superpose ef68499 ef14964
  have ef68550 : q ◇ q = p ◇ q := by
    first | exact superpose ef67361 ef68530 | exact superpose ef68530 ef67361
  have ef77871 (X0 : G) : q = wf X0 ((wf X0 (p ◇ q)) ◇ q) := by
    first | exact superpose ef68550 ef1031 | exact superpose ef1031 ef68550
  have ef77896 : p = q := by
    first | exact superpose ef1031 ef77871 | exact superpose ef77871 ef1031
  subsumption ef77896 ef22

/-- Left translation of `x □ y := ((x/x)◇(y◇x))` by `t` is injective in every finite magma
satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. That is what makes `□`'s own divisions
terms, and so what lets `◇` be sought inside `□`. -/
private theorem winj898_56L [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (t : G) :
    Function.Injective (fun p : G ↦ wf t p) := by
  intro p q hhyp
  replace hhyp : wf t p = wf t q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have ef14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef21 : wf t p = wf t q := mod_symm hhyp
  have ef22 : p ≠ q := mod_symm nh
  have ef41 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef97 (X0 X1 : G) : X1 ◇ X0 = dl (dr X0 X0) (wf X0 X1) := by
    first | exact superpose ef20 ef19 | exact superpose ef19 ef20
  have ef1041 : q ◇ t = dl (dr t t) (wf t p) := by
    first | exact superpose ef21 ef97 | exact superpose ef97 ef21
  have ef1052 : q ◇ t = p ◇ t := by
    first | exact superpose ef97 ef1041 | exact superpose ef1041 ef97
  have ef1072 (X0 : G) : q = ((dl X0 t) ◇ (p ◇ t)) ◇ X0 := by
    first | exact superpose ef1052 ef41 | exact superpose ef41 ef1052
  have ef1081 : p = q := by
    first | exact superpose ef41 ef1072 | exact superpose ef1072 ef41
  subsumption ef1081 ef22

/-- The operation comes back: `x ◇ y = ((x\y)/(y/y))` read in `□` and its divisions, where
`x □ y := ((x/x)◇(y◇x))`. With `winj898_56` that makes the witness term-structural rather than
merely term-definable. -/
private theorem back898_56 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (wdr wdl : G → G → G)
    (hwrs : ∀ a b : G, wf (wdr a b) b = a) (hwri : ∀ a b : G, wdr (wf a b) b = a)
    (hwls : ∀ a b : G, wf a (wdl a b) = b) (hwli : ∀ a b : G, wdl a (wf a b) = b)
    (x y : G) :
    (wdr (wdl x y) (wdr y y)) = x ◇ y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef16 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef19 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef21 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef22 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef23 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef25 (X0 X1 : G) : wdr (wf X0 X1) X1 = X0 := mod_symm (hwri ..)
  have ef27 (X0 X1 : G) : wdl X0 (wf X0 X1) = X1 := mod_symm (hwli ..)
  have ef28 : wdr (wdl x y) (wdr y y) ≠ x ◇ y := mod_symm nh
  have ef29 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef21 ef20 | exact superpose ef20 ef21
  have ef33 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef34 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef36 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef19 ef16 | exact superpose ef16 ef19
  have ef37 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef21 ef16 | exact superpose ef16 ef21
  have ef40 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef46 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef50 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef19 ef17 | exact superpose ef17 ef19
  have ef71 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef74 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef21 ef18 | exact superpose ef18 ef21
  have ef79 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef18 ef16 | exact superpose ef16 ef18
  have ef82 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef18 ef22 | exact superpose ef22 ef18
  have ef94 (X0 X1 : G) : wf X1 (dr X0 X1) = (dr X1 X1) ◇ X0 := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef100 (X0 X1 : G) : dr X0 X0 = (X0 ◇ (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef23 ef17 | exact superpose ef17 ef23
  have ef119 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef19 ef33 | exact superpose ef33 ef19
  have ef121 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef21 ef33 | exact superpose ef33 ef21
  have ef124 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef17 ef33 | exact superpose ef33 ef17
  have ef125 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef18 ef33 | exact superpose ef33 ef18
  have ef126 (X0 X1 : G) : X0 ◇ (wf X0 X1) = dr (dr X0 X0) X1 := by
    first | exact superpose ef23 ef33 | exact superpose ef33 ef23
  have ef143 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef33 ef22 | exact superpose ef22 ef33
  have ef152 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef50 ef125 | exact superpose ef125 ef50
  have ef153 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef50 ef124 | exact superpose ef124 ef50
  have ef170 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef34 ef33 | exact superpose ef33 ef34
  have ef178 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef34 ef22 | exact superpose ef22 ef34
  have ef208 (X0 X1 : G) : wf X1 (X0 ◇ (dr X1 (dr X1 X1))) = X0 := by
    first | exact superpose ef36 ef23 | exact superpose ef23 ef36
  have ef228 (X0 X1 : G) : wf X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    first | exact superpose ef119 ef208 | exact superpose ef208 ef119
  have ef309 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef37 ef40 | exact superpose ef40 ef37
  have ef316 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef18 ef40 | exact superpose ef40 ef18
  have ef320 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef37 ef40 | exact superpose ef40 ef37
  have ef658 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef71 ef46 | exact superpose ef46 ef71
  have ef663 (X0 X1 : G) : wf X1 (dl (X1 ◇ X0) (dr X1 X1)) = X0 := by
    first | exact superpose ef71 ef23 | exact superpose ef23 ef71
  have ef704 (X0 X1 : G) : wf X1 (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    first | exact superpose ef143 ef663 | exact superpose ef663 ef143
  have ef844 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef33 ef74 | exact superpose ef74 ef33
  have ef1022 (X0 X1 : G) : (dl (wf X0 X1) X1) ◇ (dr X0 X0) = X0 := by
    first | exact superpose ef100 ef37 | exact superpose ef37 ef100
  have ef1024 (X0 X1 X2 : G) : (dr X0 X0) ◇ (dr X2 (X0 ◇ (wf X0 (X1 ◇ X2)))) = X1 := by
    first | exact superpose ef100 ef46 | exact superpose ef46 ef100
  have ef1029 (X0 X1 X2 : G) : (dr X0 X0) ◇ (((wf X0 (X1 ◇ X2)) ◇ X2) ◇ X0) = X1 := by
    first | exact superpose ef50 ef1024 | exact superpose ef1024 ef50
  have ef1046 (X0 X1 X2 : G) : wf X0 ((wf X0 (X1 ◇ X2)) ◇ X2) = X1 := by
    first | exact superpose ef23 ef1029 | exact superpose ef1029 ef23
  have ef1469 (X0 X1 X2 X3 : G) :
      (dr X0 X0) ◇ ((X2 ◇ ((X1 ◇ X3) ◇ (X0 ◇ (wf X0 X1)))) ◇ X3) = X2 := by
    first | exact superpose ef100 ef79 | exact superpose ef79 ef100
  have ef1528 (X0 X1 X2 : G) : dr X0 X0 = (X0 ◇ X1) ◇ ((wf X0 (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef23 ef79 | exact superpose ef79 ef23
  have ef1646 (X0 X1 X2 : G) : (dr X0 X0) ◇ (dl ((X0 ◇ (wf X0 X1)) ◇ X1) X2) = X2 := by
    first | exact superpose ef316 ef1469 | exact superpose ef1469 ef316
  have ef1703 (X0 X1 X2 : G) : (dr X0 X0) ◇ ((X2 ◇ (dl (wf X0 X1) X1)) ◇ X0) = X2 := by
    first | exact superpose ef320 ef1646 | exact superpose ef1646 ef320
  have ef1743 (X0 X1 X2 : G) : wf X0 (X2 ◇ (dl (wf X0 X1) X1)) = X2 := by
    first | exact superpose ef23 ef1703 | exact superpose ef1703 ef23
  have ef1827 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef121 ef33 | exact superpose ef33 ef121
  have ef2399 (X0 X1 : G) : wf (dr X0 X0) X1 = (X0 ◇ (wf X0 (dr X0 X0))) ◇ (X1 ◇ (dr X0 X0)) := by
    first | exact superpose ef126 ef23 | exact superpose ef23 ef126
  have ef2418 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 (wf X0 (dr X0 X0))) := by
    first | exact superpose ef1827 ef2399 | exact superpose ef2399 ef1827
  have ef2427 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 ((dr X0 X0) ◇ X0)) := by
    first | exact superpose ef94 ef2418 | exact superpose ef2418 ef94
  have ef2431 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 X0) := by
    first | exact superpose ef19 ef2427 | exact superpose ef2427 ef19
  have ef4118 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef178 ef22 | exact superpose ef22 ef178
  have ef6670 (X0 X1 X2 : G) : (dl (X2 ◇ (X2 ◇ X2)) X1) ◇ X0 = wf X2 (dr X0 X1) := by
    first | exact superpose ef170 ef228 | exact superpose ef228 ef170
  have ef6684 (X0 X1 : G) : wdl X1 X0 = X0 ◇ (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef228 ef27 | exact superpose ef27 ef228
  have ef6707 (X0 X1 X2 : G) : wf X2 (dr X0 X1) = ((X2 ◇ X2) ◇ (dr X2 X1)) ◇ X0 := by
    first | exact superpose ef658 ef6670 | exact superpose ef6670 ef658
  have ef9146 (X0 X1 : G) : wdl X1 X0 = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef704 ef27 | exact superpose ef27 ef704
  have ef11994 (X0 X1 X2 : G) : dl (X0 ◇ X1) (dr X0 X0) = X1 ◇ (dl (wf X0 X2) X2) := by
    first | exact superpose ef1022 ef82 | exact superpose ef82 ef1022
  have ef12041 (X0 X1 X2 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = X1 ◇ (dl (wf X0 X2) X2) := by
    first | exact superpose ef143 ef11994 | exact superpose ef11994 ef143
  have ef12093 (X0 X1 X2 : G) : wdl X0 X1 = X1 ◇ (dl (wf X0 X2) X2) := by
    first | exact superpose ef9146 ef12041 | exact superpose ef12041 ef9146
  have ef12621 (X0 X1 X2 : G) : wdl X1 X0 = (wf X1 (X0 ◇ X2)) ◇ X2 := by
    first | exact superpose ef1046 ef27 | exact superpose ef27 ef1046
  have ef25382 (X0 : G) : wf (dr X0 X0) X0 = X0 := by
    first | exact superpose ef2431 ef29 | exact superpose ef29 ef2431
  have ef25809 (X0 X1 X2 X3 X4 : G) :
      wf X3 (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (dl (wf X3 X4) X4))) ◇ X1 := by
    first | exact superpose ef153 ef1743 | exact superpose ef1743 ef153
  have ef25816 (X0 X1 X2 X3 : G) : wf X3 (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (wdl X3 X0)) ◇ X1 := by
    first | exact superpose ef12093 ef25809 | exact superpose ef25809 ef12093
  have ef26548 (X0 : G) : dr X0 X0 = wdr X0 X0 := by
    first | exact superpose ef25382 ef25 | exact superpose ef25 ef25382
  have ef58127 (X0 X1 X2 X3 : G) :
      dl X3 (dl X2 (X0 ◇ (X0 ◇ X0))) = X1 ◇ ((wdl X0 (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef6684 ef309 | exact superpose ef309 ef6684
  have ef58181 (X0 X1 X2 X3 : G) :
      (dl (X0 ◇ (X0 ◇ X0)) X3) ◇ X2 = X1 ◇ ((wdl X0 (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef4118 ef58127 | exact superpose ef58127 ef4118
  have ef58432 (X0 X1 X2 X3 : G) :
      X1 ◇ ((wdl X0 (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X0) ◇ (dr X0 X3)) ◇ X2 := by
    first | exact superpose ef658 ef58181 | exact superpose ef58181 ef658
  have ef58631 (X0 X1 X2 X3 : G) : wf X0 (dr X2 X3) = X1 ◇ ((wdl X0 (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef6707 ef58432 | exact superpose ef58432 ef6707
  have ef134239 (X0 X1 X2 : G) :
      (wf X0 (X1 ◇ X2)) ◇ X2 = wf (X0 ◇ X1) ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (dr X0 X0))) := by
    first | exact superpose ef1528 ef704 | exact superpose ef704 ef1528
  have ef134374 (X0 X1 X2 : G) :
      (wf X0 (X1 ◇ X2)) ◇ X2 = ((dr X0 X0) ◇ (wdl (X0 ◇ X1) (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef25816 ef134239 | exact superpose ef134239 ef25816
  have ef134836 (X0 X1 X2 : G) :
      (wf X0 (X1 ◇ X2)) ◇ X2 = ((dr X0 X0) ◇ X0) ◇ ((wdl (X0 ◇ X1) (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef152 ef134374 | exact superpose ef134374 ef152
  have ef135250 (X0 X1 X2 : G) :
      (wf X0 (X1 ◇ X2)) ◇ X2 = X0 ◇ (X0 ◇ (dl X0 ((wdl (X0 ◇ X1) (X0 ◇ X1)) ◇ X1))) := by
    first | exact superpose ef844 ef134836 | exact superpose ef134836 ef844
  have ef135583 (X0 X1 X2 : G) :
      (wf X0 (X1 ◇ X2)) ◇ X2 = X0 ◇ ((wdl (X0 ◇ X1) (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef21 ef135250 | exact superpose ef135250 ef21
  have ef135855 (X0 X1 X2 : G) : (wf X0 (X1 ◇ X2)) ◇ X2 = wf (X0 ◇ X1) (dr X1 X1) := by
    first | exact superpose ef58631 ef135583 | exact superpose ef135583 ef58631
  have ef136065 (X0 X1 X2 : G) : (wf X0 (X1 ◇ X2)) ◇ X2 = wf (X0 ◇ X1) (wdr X1 X1) := by
    first | exact superpose ef26548 ef135855 | exact superpose ef135855 ef26548
  have ef136229 (X0 X1 : G) : wdl X0 X1 = wf (X0 ◇ X1) (wdr X1 X1) := by
    first | exact superpose ef12621 ef136065 | exact superpose ef136065 ef12621
  have ef222915 (X0 X1 : G) : X0 ◇ X1 = wdr (wdl X0 X1) (wdr X1 X1) := by
    first | exact superpose ef136229 ef25 | exact superpose ef25 ef136229
  have ef354834 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef222915 ef28 | exact superpose ef28 ef222915
  exact absurd rfl ef354834

set_option maxHeartbeats 1600000 in
/-- Equation 3659 `x ◇ x = (x ◇ x) ◇ (x ◇ x)` holds of the operation `x □ y := ((x/x)◇(y◇x))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3659_56 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (x : G) :
    wf x x = wf (wf x x) (wf x x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef20 : wf x x ≠ wf (wf x x) (wf x x) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef37 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef15 ef14 | exact superpose ef14 ef15
  have ef64 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef67 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef14 ef14
  have ef69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef70 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef82 (X0 X1 : G) : wf X1 (dr X0 X1) = (dr X1 X1) ◇ X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef83 (X0 X1 : G) : wf (X1 ◇ X0) (dr X0 X0) = (dr (X1 ◇ X0) (X1 ◇ X0)) ◇ (wf X0 X1) := by
    first | exact superpose ef19 ef19
  have ef84 (X0 X1 : G) : wf (dl X1 X0) X1 = (dr (dl X1 X0) (dl X1 X0)) ◇ X0 := by
    first | exact superpose ef17 ef19 | exact superpose ef19 ef17
  have ef85 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (dr ((X0 ◇ X1) ◇ (X1 ◇ X2)) ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇
      X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef87 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = (dr (X1 ◇ X2) (X1 ◇ X2)) ◇ X0 := by
    first | exact superpose ef14 ef19 | exact superpose ef19 ef14
  have ef88 (X0 X1 : G) : dr X0 X0 = (X0 ◇ (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef90 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ ((X2 ◇ (dr X0 X0)) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef91 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1))) ◇ (dr X0 X0) = X2 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef92 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (dr X0 X0)) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef99 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0 := by
    first | exact superpose ef40 ef87 | exact superpose ef87 ef40
  have ef101 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef40 ef85 | exact superpose ef85 ef40
  have ef102 (X0 X1 : G) : wf (X1 ◇ X0) (dr X0 X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (wf X0 X1) := by
    first | exact superpose ef40 ef83 | exact superpose ef83 ef40
  have ef104 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = (((X1 ◇ X2) ◇ (dl X2 X0)) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef30 ef101 | exact superpose ef101 ef30
  have ef105 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef106 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1)) = dr X2 (dr X0 X0) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef107 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef109 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef23 ef23
  have ef110 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef13 ef23 | exact superpose ef23 ef13
  have ef111 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef14 ef23 | exact superpose ef23 ef14
  have ef112 (X0 X1 : G) : X0 ◇ (wf X0 X1) = dr (dr X0 X0) X1 := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef115 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef23
  have ef124 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (dr X0 X1)) = X3 := by
    first | exact superpose ef23 ef12 | exact superpose ef12 ef23
  have ef126 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef129 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef131 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef138 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef40 ef111 | exact superpose ef111 ef40
  have ef139 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef40 ef110 | exact superpose ef110 ef40
  have ef146 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (dl X2 X3))) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef12 ef24 | exact superpose ef24 ef12
  have ef149 (X0 X1 : G) : X0 ◇ (wf X0 (dl X1 (dr X0 X0))) = X1 := by
    first | exact superpose ef19 ef24 | exact superpose ef24 ef19
  have ef156 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef164 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef165 (X0 X1 X2 : G) :
      wf (X1 ◇ ((dl X0 X1) ◇ X2)) X2 = (dr (X1 ◇ ((dl X0 X1) ◇ X2)) (X1 ◇ ((dl X0 X1) ◇ X2))) ◇
      X0 := by
    first | exact superpose ef24 ef19 | exact superpose ef19 ef24
  have ef167 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ ((dl X0 X3) ◇ (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef24 ef14 | exact superpose ef14 ef24
  have ef168 (X0 X1 X2 : G) :
      wf (X1 ◇ ((dl X0 X1) ◇ X2)) X2 = ((((dl X0 X1) ◇ X2) ◇ (X1 ◇ ((dl X0 X1) ◇ X2))) ◇ X1) ◇
      X0 := by
    first | exact superpose ef40 ef165 | exact superpose ef165 ef40
  have ef177 (X0 X1 : G) : X0 ◇ (wf X0 (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef129 ef149 | exact superpose ef149 ef129
  have ef180 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) ◇ ((X1 ◇ (dl X2 X3)) ◇ X0) = X2 := by
    first | exact superpose ef138 ef146 | exact superpose ef146 ef138
  have ef182 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = ((((dl X0 X1) ◇ X2) ◇ (dl X2 X0)) ◇ X1) ◇ X0 := by
    first | exact superpose ef164 ef168 | exact superpose ef168 ef164
  have ef194 (X0 X1 : G) : wf X1 (X0 ◇ (dr X1 (dr X1 X1))) = X0 := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef201 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef26 ef18 | exact superpose ef18 ef26
  have ef203 (X0 X1 X2 X3 : G) : dr X3 X2 = ((X0 ◇ (dr X1 X2)) ◇ X1) ◇ (X3 ◇ X0) := by
    first | exact superpose ef26 ef23 | exact superpose ef23 ef26
  have ef205 (X0 X1 X2 X3 : G) : ((X0 ◇ (dr X1 (dl X2 X3))) ◇ X1) ◇ (X3 ◇ X0) = X2 := by
    first | exact superpose ef26 ef24 | exact superpose ef24 ef26
  have ef214 (X0 X1 : G) : wf X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    first | exact superpose ef105 ef194 | exact superpose ef194 ef105
  have ef239 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef13 ef27 | exact superpose ef27 ef13
  have ef241 (X0 X1 X2 : G) : (dl X1 (dl (X2 ◇ X1) X0)) ◇ X0 = X2 := by
    first | exact superpose ef17 ef27 | exact superpose ef27 ef17
  have ef243 (X0 X1 X2 X3 : G) : (dl X2 (X0 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef27 | exact superpose ef27 ef23
  have ef254 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef256 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef287 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef291 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef292 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef30 ef30
  have ef294 (X0 X1 X2 : G) : (wf X0 X1) ◇ ((X1 ◇ X0) ◇ X2) = dl X2 (dr X0 X0) := by
    first | exact superpose ef19 ef30 | exact superpose ef30 ef19
  have ef295 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef298 (X0 X1 X2 X3 : G) : dl (X0 ◇ (X1 ◇ X3)) X2 = (X2 ◇ X3) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef302 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef305 (X0 X1 X2 : G) : (X2 ◇ (dr X0 X0)) ◇ (wf X0 X1) = dl (X1 ◇ X0) X2 := by
    first | exact superpose ef19 ef30 | exact superpose ef30 ef19
  have ef306 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef316 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef321 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1))) ◇ (X1 ◇ X2) = X3 := by
    first | exact superpose ef30 ef13 | exact superpose ef13 ef30
  have ef322 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef30 ef14 | exact superpose ef14 ef30
  have ef325 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef30 ef18 | exact superpose ef18 ef30
  have ef327 (X0 X1 X2 X3 : G) : dr X3 (X1 ◇ X2) = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef333 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef40 ef327 | exact superpose ef327 ef40
  have ef337 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef256 ef322 | exact superpose ef322 ef256
  have ef338 (X0 X1 X3 : G) : dr X1 (dl X0 (X3 ◇ (dl X0 X1))) = X3 := by
    first | exact superpose ef256 ef321 | exact superpose ef321 ef256
  have ef349 (X0 X1 X2 : G) : (wf X0 X1) ◇ ((X1 ◇ X0) ◇ X2) = X0 ◇ (X0 ◇ X2) := by
    first | exact superpose ef129 ef294 | exact superpose ef294 ef129
  have ef444 (X0 X1 : G) : (wf X0 X1) ◇ (dr X0 (dr X0 X0)) = X1 := by
    first | exact superpose ef19 ef36 | exact superpose ef36 ef19
  have ef452 (X0 X1 X2 X3 : G) : ((dr X1 X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef36 ef13 | exact superpose ef13 ef36
  have ef458 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef36 ef23 | exact superpose ef23 ef36
  have ef460 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef461 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef470 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef40 ef458 | exact superpose ef458 ef40
  have ef478 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef105 ef444 | exact superpose ef444 ef105
  have ef531 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((dl X1 X3) ◇ (X0 ◇ X3)) := by
    first | exact superpose ef37 ef23 | exact superpose ef23 ef37
  have ef538 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef37 ef27 | exact superpose ef27 ef37
  have ef559 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ X3) ◇ X2) ◇ (dl X1 X3) := by
    first | exact superpose ef40 ef531 | exact superpose ef531 ef40
  have ef604 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1) = dr X3 X0 := by
    first | exact superpose ef14 ef40 | exact superpose ef40 ef14
  have ef605 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2) = dr X3 (dl X0 X1) := by
    first | exact superpose ef30 ef40 | exact superpose ef40 ef30
  have ef608 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (dr X0 X0) = dr X2 (wf X0 X1) := by
    first | exact superpose ef19 ef40 | exact superpose ef40 ef19
  have ef620 (X0 X2 X3 : G) : dr X3 X0 = dr (X2 ◇ X0) (dl X2 X3) := by
    first | exact superpose ef256 ef604 | exact superpose ef604 ef256
  have ef644 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef649 (X0 X1 : G) : wf X1 (dl (X1 ◇ X0) (dr X1 X1)) = X0 := by
    first | exact superpose ef61 ef19 | exact superpose ef19 ef61
  have ef658 (X0 X1 X2 : G) :
      wf ((dl (X1 ◇ X0) X2) ◇ X1) X2 = (dr ((dl (X1 ◇ X0) X2) ◇ X1) ((dl (X1 ◇ X0) X2) ◇ X1)) ◇
      X0 := by
    first | exact superpose ef61 ef19 | exact superpose ef19 ef61
  have ef683 (X0 X1 X2 : G) :
      wf ((dl (X1 ◇ X0) X2) ◇ X1) X2 = ((X1 ◇ ((dl (X1 ◇ X0) X2) ◇ X1)) ◇ (dl (X1 ◇ X0) X2)) ◇
      X0 := by
    first | exact superpose ef40 ef658 | exact superpose ef658 ef40
  have ef690 (X0 X1 : G) : wf X1 (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    first | exact superpose ef129 ef649 | exact superpose ef649 ef129
  have ef714 (X0 X1 X2 : G) :
      wf ((dl (X1 ◇ X0) X2) ◇ X1) X2 = (dr ((dl (X1 ◇ X0) X2) ◇ X1) X0) ◇
      ((dl (X1 ◇ X0) X2) ◇ X1) := by
    first | exact superpose ef470 ef683 | exact superpose ef683 ef470
  have ef721 (X0 X2 : G) : wf (dl X2 X0) X2 = (dr (dl X2 X0) X0) ◇ (dl X2 X0) := by
    first | exact superpose ef538 ef714 | exact superpose ef714 ef538
  have ef752 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef63 ef23 | exact superpose ef23 ef63
  have ef755 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ ((X2 ◇ X0) ◇ (dr X3 X2))) ◇ X0 := by
    first | exact superpose ef63 ef30 | exact superpose ef30 ef63
  have ef778 (X1 X2 X3 : G) : dl X3 X1 = dl ((dr X3 X2) ◇ X2) X1 := by
    first | exact superpose ef302 ef755 | exact superpose ef755 ef302
  have ef781 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef40 ef752 | exact superpose ef752 ef40
  have ef810 (X1 X2 X3 : G) : dl X3 X1 = X2 ◇ (dr (dr X3 X2) X1) := by
    first | exact superpose ef644 ef778 | exact superpose ef778 ef644
  have ef830 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef23 ef64 | exact superpose ef64 ef23
  have ef846 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (((dl X3 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef64 ef23 | exact superpose ef23 ef64
  have ef849 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef64 ef30 | exact superpose ef30 ef64
  have ef878 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef302 ef849 | exact superpose ef849 ef302
  have ef881 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((dl X3 X1) ◇ X0) := by
    first | exact superpose ef40 ef846 | exact superpose ef846 ef40
  have ef900 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef644 ef878 | exact superpose ef878 ef644
  have ef915 (X0 X1 X2 X3 : G) : X1 ◇ X2 = dl (X0 ◇ X1) (X3 ◇ ((dl X0 X3) ◇ X2)) := by
    first | exact superpose ef24 ef72 | exact superpose ef72 ef24
  have ef924 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef927 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef937 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2 = dl (dr X0 X1) X3 := by
    first | exact superpose ef23 ef72 | exact superpose ef72 ef23
  have ef955 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef291 ef927 | exact superpose ef927 ef291
  have ef957 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef129 ef924 | exact superpose ef924 ef129
  have ef966 (X0 X1 X2 X3 : G) : X1 ◇ X2 = (dl X0 X3) ◇ ((dr X2 X3) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef460 ef915 | exact superpose ef915 ef460
  have ef969 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef955 | exact superpose ef955 ef30
  have ef989 (X0 X1 : G) : dl (X0 ◇ (wf X0 X1)) (dr X0 X0) = X1 := by
    first | exact superpose ef88 ef18 | exact superpose ef18 ef88
  have ef991 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (dr X0 X0)) = dr X2 (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef88 ef23 | exact superpose ef23 ef88
  have ef993 (X0 X1 X2 : G) : dl X2 (X0 ◇ (wf X0 X1)) = (dr X0 X0) ◇ (X1 ◇ X2) := by
    first | exact superpose ef88 ef30 | exact superpose ef30 ef88
  have ef994 (X0 X1 X2 : G) : dl X2 X1 = (X1 ◇ (X0 ◇ (wf X0 X2))) ◇ (dr X0 X0) := by
    first | exact superpose ef88 ef30 | exact superpose ef30 ef88
  have ef999 (X0 X1 X2 : G) : dr X2 (dr X0 X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef88 ef40 | exact superpose ef40 ef88
  have ef1008 (X0 X1 X2 : G) : X0 ◇ (wf X0 (X2 ◇ X1)) = (X1 ◇ (dr X0 X0)) ◇ X2 := by
    first | exact superpose ef88 ef13 | exact superpose ef13 ef88
  have ef1015 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef105 ef999 | exact superpose ef999 ef105
  have ef1021 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (dr X0 X0)) = ((wf X0 X1) ◇ X2) ◇ X0 := by
    first | exact superpose ef40 ef991 | exact superpose ef991 ef40
  have ef1022 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ (wf X0 X1))) = X1 := by
    first | exact superpose ef129 ef989 | exact superpose ef989 ef129
  have ef1765 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef17 ef107 | exact superpose ef107 ef17
  have ef1777 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef14 ef107 | exact superpose ef107 ef14
  have ef1778 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef107 | exact superpose ef107 ef30
  have ef1780 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef36 ef107 | exact superpose ef107 ef36
  have ef1781 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef107 | exact superpose ef107 ef15
  have ef1784 (X0 X1 X2 X3 : G) : dr (dl X1 X3) X2 = (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) := by
    first | exact superpose ef107 ef107
  have ef1793 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1806 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1808 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = (dr X0 X1) ◇ ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef107 ef30 | exact superpose ef30 ef107
  have ef1854 (X0 X1 X2 X3 : G) : X3 ◇ (dr X2 X1) = (dl X2 (X0 ◇ X3)) ◇ (dr X0 X1) := by
    first | exact superpose ef1793 ef1784 | exact superpose ef1784 ef1793
  have ef1857 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef129 ef1780 | exact superpose ef1780 ef129
  have ef1859 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef969 ef1778 | exact superpose ef1778 ef969
  have ef1890 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef254 ef1859 | exact superpose ef1859 ef254
  have ef1903 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1890 | exact superpose ef1890 ef23
  have ef1972 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) ◇ (X0 ◇ X1) = X3 := by
    first | exact superpose ef26 ef70 | exact superpose ef70 ef26
  have ef2019 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = dl ((X1 ◇ X2) ◇ (X0 ◇ X3)) X0 := by
    first | exact superpose ef70 ef18 | exact superpose ef18 ef70
  have ef2023 (X0 X1 X2 X3 X4 : G) :
      dl X4 ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4) := by
    first | exact superpose ef70 ef30 | exact superpose ef30 ef70
  have ef2066 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4) = X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X4) := by
    first | exact superpose ef291 ef2023 | exact superpose ef2023 ef291
  have ef2070 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ X1 = (X0 ◇ (dl X2 (X0 ◇ X3))) ◇ X1 := by
    first | exact superpose ef306 ef2019 | exact superpose ef2019 ef306
  have ef2109 (X0 X2 X3 X4 : G) : dr X0 (dl X2 (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) = X3 := by
    first | exact superpose ef256 ef1972 | exact superpose ef1972 ef256
  have ef2210 (X0 X2 X3 X4 : G) : dr X0 ((X0 ◇ (dr X4 X2)) ◇ ((dr X4 X3) ◇ X2)) = X3 := by
    first | exact superpose ef460 ef2109 | exact superpose ef2109 ef460
  have ef2281 (X0 X2 X3 X4 : G) : (((dr X4 X3) ◇ X2) ◇ X0) ◇ (X0 ◇ (dr X4 X2)) = X3 := by
    first | exact superpose ef40 ef2210 | exact superpose ef2210 ef40
  have ef2327 (X2 X3 X4 : G) : dl (dr X4 X2) ((dr X4 X3) ◇ X2) = X3 := by
    first | exact superpose ef30 ef2281 | exact superpose ef2281 ef30
  have ef2378 (X0 X1 : G) : wf (dr X0 X0) X1 = (X0 ◇ (wf X0 (dr X0 X0))) ◇ (X1 ◇ (dr X0 X0)) := by
    first | exact superpose ef112 ef19 | exact superpose ef19 ef112
  have ef2397 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 (wf X0 (dr X0 X0))) := by
    first | exact superpose ef1806 ef2378 | exact superpose ef2378 ef1806
  have ef2406 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 ((dr X0 X0) ◇ X0)) := by
    first | exact superpose ef82 ef2397 | exact superpose ef2397 ef82
  have ef2410 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 X0) := by
    first | exact superpose ef15 ef2406 | exact superpose ef2406 ef15
  have ef2433 (X0 X1 X2 : G) :
      (X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1)) = dr X2 (wf (dl X0 X1) X0) := by
    first | exact superpose ef84 ef40 | exact superpose ef40 ef84
  have ef2466 (X0 X1 X2 : G) :
      dr X2 (wf (dl X0 X1) X0) = (X1 ◇ X2) ◇ (X1 ◇ (dr (dl X0 X1) X0)) := by
    first | exact superpose ef1793 ef2433 | exact superpose ef2433 ef1793
  have ef2499 (X0 X1 X2 : G) : dr X2 (wf (dl X0 X1) X0) = (X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (dr X0 X0))) := by
    first | exact superpose ef1793 ef2466 | exact superpose ef2466 ef1793
  have ef2553 (X0 X1 X2 : G) : dr X1 X2 = (dr X0 X0) ◇ (dr X2 (X0 ◇ (wf X0 X1))) := by
    first | exact superpose ef88 ef115 | exact superpose ef115 ef88
  have ef2564 (X0 X1 X2 : G) : dr (X1 ◇ X0) X2 = (wf X0 X1) ◇ (dr X2 (dr X0 X0)) := by
    first | exact superpose ef19 ef115 | exact superpose ef115 ef19
  have ef2595 (X0 X1 X2 X3 : G) : dl (dr X1 X3) X2 = (X2 ◇ (X3 ◇ X0)) ◇ (dr X0 X1) := by
    first | exact superpose ef115 ef30 | exact superpose ef30 ef115
  have ef2610 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ X0) = dl ((dr X0 X1) ◇ X2) (dr X1 X3) := by
    first | exact superpose ef115 ef72 | exact superpose ef72 ef115
  have ef2635 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ X0) = X1 ◇ (X3 ◇ ((dr X0 X1) ◇ X2)) := by
    first | exact superpose ef129 ef2610 | exact superpose ef2610 ef129
  have ef2668 (X0 X1 X2 : G) : dr (X1 ◇ X0) X2 = (wf X0 X1) ◇ (X0 ◇ (X2 ◇ X0)) := by
    first | exact superpose ef105 ef2564 | exact superpose ef2564 ef105
  have ef2679 (X0 X1 X2 : G) : dr X1 X2 = (dr X0 X0) ◇ (((wf X0 X1) ◇ X2) ◇ X0) := by
    first | exact superpose ef40 ef2553 | exact superpose ef2553 ef40
  have ef2715 (X0 X1 X2 : G) : dr (X1 ◇ X0) X2 = X0 ◇ (X0 ◇ (X2 ◇ (wf X0 X1))) := by
    first | exact superpose ef957 ef2668 | exact superpose ef2668 ef957
  have ef2725 (X0 X1 X2 : G) : dr X1 X2 = wf X0 ((wf X0 X1) ◇ X2) := by
    first | exact superpose ef19 ef2679 | exact superpose ef2679 ef19
  have ef2779 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ X2) = (X1 ◇ X2) ◇ (X0 ◇ (wf X2 X1)) := by
    first | exact superpose ef36 ef90 | exact superpose ef90 ef36
  have ef2794 (X0 X1 X2 : G) : (wf X1 X2) ◇ X0 = dr (X2 ◇ X1) (X0 ◇ (dr X1 X1)) := by
    first | exact superpose ef90 ef23 | exact superpose ef23 ef90
  have ef2868 (X0 X1 X2 : G) : (wf X1 X2) ◇ X0 = ((dr X1 X1) ◇ (X2 ◇ X1)) ◇ X0 := by
    first | exact superpose ef40 ef2794 | exact superpose ef2794 ef40
  have ef2935 (X0 X1 X2 : G) : (wf X1 X2) ◇ X0 = X1 ◇ (X1 ◇ (dl (X2 ◇ X1) X0)) := by
    first | exact superpose ef830 ef2868 | exact superpose ef2868 ef830
  have ef2986 (X0 X1 X2 : G) : (wf X1 X2) ◇ X0 = X1 ◇ (X1 ◇ (X1 ◇ (dr X2 X0))) := by
    first | exact superpose ef644 ef2935 | exact superpose ef2935 ef644
  have ef3091 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X0 ◇ (X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X3)) := by
    first | exact superpose ef129 ef72 | exact superpose ef72 ef129
  have ef3151 (X0 X1 X2 X3 : G) :
      (dr X1 X1) ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X1) ◇ (X0 ◇ (wf X1 X3))) := by
    first | exact superpose ef91 ef23 | exact superpose ef23 ef91
  have ef3154 (X0 X1 X2 X3 : G) :
      dl (dr X3 X3) X1 = (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (wf X3 X2)))) ◇ X0 := by
    first | exact superpose ef91 ef30 | exact superpose ef30 ef91
  have ef3206 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl (dr (wf X3 X2) (X2 ◇ X3)) X1 := by
    first | exact superpose ef461 ef3154 | exact superpose ef3154 ef461
  have ef3209 (X0 X1 X2 X3 : G) :
      (dr X1 X1) ◇ (X2 ◇ X0) = ((X0 ◇ (wf X1 X3)) ◇ X2) ◇ (X3 ◇ X1) := by
    first | exact superpose ef40 ef3151 | exact superpose ef3151 ef40
  have ef3274 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl ((X3 ◇ (wf X3 X2)) ◇ X2) X1 := by
    first | exact superpose ef40 ef3206 | exact superpose ef3206 ef40
  have ef3326 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = (X1 ◇ (dl (wf X3 X2) X2)) ◇ X3 := by
    first | exact superpose ef306 ef3274 | exact superpose ef3274 ef306
  have ef3463 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef23 ef156 | exact superpose ef156 ef23
  have ef3483 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef156 ef23 | exact superpose ef23 ef156
  have ef3485 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ (X2 ◇ X3) = dl X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef156 ef30 | exact superpose ef30 ef156
  have ef3504 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dr X0 X1) = dr ((dl X3 X1) ◇ X0) X2 := by
    first | exact superpose ef156 ef107 | exact superpose ef107 ef156
  have ef3519 (X0 X1 X2 X3 X4 : G) :
      (dl ((X3 ◇ X4) ◇ X2) X1) ◇ X0 = (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef156 ef69 | exact superpose ef69 ef156
  have ef3523 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef156 ef26 | exact superpose ef26 ef156
  have ef3525 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (dr (dr X0 X0) X1) := by
    first | exact superpose ef156 ef90 | exact superpose ef90 ef156
  have ef3528 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef112 ef3525 | exact superpose ef3525 ef112
  have ef3533 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) = ((X1 ◇ (dl X4 X2)) ◇ X3) ◇ X0 := by
    first | exact superpose ef306 ef3519 | exact superpose ef3519 ef306
  have ef3564 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef40 ef3483 | exact superpose ef3483 ef40
  have ef3578 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1903 ef3463 | exact superpose ef3463 ef1903
  have ef3584 (X0 X1 X2 : G) : dl (wf X0 X1) X2 = dl (wf X0 X2) X1 := by
    first | exact superpose ef30 ef3528 | exact superpose ef3528 ef30
  have ef3614 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef40 ef3578 | exact superpose ef3578 ef40
  have ef3631 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef107 ef3614 | exact superpose ef3614 ef107
  have ef3717 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = dr X3 (((X2 ◇ X1) ◇ X0) ◇ (dr X1 X1)) := by
    first | exact superpose ef92 ef23 | exact superpose ef23 ef92
  have ef3728 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (dr X3 X3))) ◇ X4) ◇ (X0 ◇ X1)) ◇ (wf X3 X2) = X4 := by
    first | exact superpose ef92 ef67 | exact superpose ef67 ef92
  have ef3741 (X0 X1 X2 : G) : (X2 ◇ X1) ◇ X0 = (dl (dr X1 X1) (wf X1 X2)) ◇ X0 := by
    first | exact superpose ef92 ef27 | exact superpose ef27 ef92
  have ef3752 (X0 X1 X2 : G) : (X2 ◇ X1) ◇ X0 = X1 ◇ ((dr X0 (wf X1 X2)) ◇ X1) := by
    first | exact superpose ef3523 ef3741 | exact superpose ef3741 ef3523
  have ef3765 (X0 X1 X2 X3 X4 : G) :
      (dr X4 (wf X3 X2)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (dr X3 X3)))) = X4 := by
    first | exact superpose ef470 ef3728 | exact superpose ef3728 ef470
  have ef3776 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = ((dr X1 X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef3717 | exact superpose ef3717 ef40
  have ef3839 (X0 X1 X2 : G) : (X2 ◇ X1) ◇ X0 = X1 ◇ ((dr X0 X1) ◇ (wf X1 X2)) := by
    first | exact superpose ef3631 ef3752 | exact superpose ef3752 ef3631
  have ef3850 (X0 X2 X3 X4 : G) :
      (dr X4 (wf X3 X2)) ◇ (dl (((X2 ◇ X3) ◇ X0) ◇ (dr X3 X3)) X0) = X4 := by
    first | exact superpose ef30 ef3765 | exact superpose ef3765 ef30
  have ef3858 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (dl X3 ((X2 ◇ X1) ◇ X0))) := by
    first | exact superpose ef830 ef3776 | exact superpose ef3776 ef830
  have ef3913 (X2 X3 X4 : G) : (dr X4 (wf X3 X2)) ◇ ((dr X3 X3) ◇ (X2 ◇ X3)) = X4 := by
    first | exact superpose ef72 ef3850 | exact superpose ef3850 ef72
  have ef3919 (X0 X1 X2 X3 : G) : (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    first | exact superpose ef291 ef3858 | exact superpose ef3858 ef291
  have ef3960 (X2 X3 X4 : G) : X3 ◇ ((dr X3 X3) ◇ (X2 ◇ (dr X4 (wf X3 X2)))) = X4 := by
    first | exact superpose ef957 ef3913 | exact superpose ef3913 ef957
  have ef4054 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef61 ef164 | exact superpose ef164 ef61
  have ef4070 (X0 X1 : G) : dl X0 X1 = wf X0 (dl X1 (dr X0 X0)) := by
    first | exact superpose ef164 ef19 | exact superpose ef19 ef164
  have ef4079 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef164 ef18 | exact superpose ef18 ef164
  have ef4089 (X0 X1 X2 X3 : G) : dr X3 (dl X0 X1) = (((dl X1 X2) ◇ X0) ◇ X3) ◇ X2 := by
    first | exact superpose ef164 ef40 | exact superpose ef40 ef164
  have ef4111 (X0 X1 X2 X3 : G) : ((dl X1 (X2 ◇ X3)) ◇ X0) ◇ X2 = dl (dl X0 X1) X3 := by
    first | exact superpose ef164 ef72 | exact superpose ef72 ef164
  have ef4114 (X0 X1 X2 X3 : G) : (dl X1 (dl X2 X3)) ◇ X0 = ((dl X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef164 ef64 | exact superpose ef64 ef164
  have ef4119 (X0 X1 X2 X3 : G) : (X3 ◇ X0) ◇ X1 = ((dl X1 (X2 ◇ X3)) ◇ X0) ◇ X2 := by
    first | exact superpose ef254 ef4111 | exact superpose ef4111 ef254
  have ef4138 (X0 X1 X2 X3 : G) : dr X3 (dl X0 X1) = (dr X0 X2) ◇ (X3 ◇ (dl X1 X2)) := by
    first | exact superpose ef470 ef4089 | exact superpose ef4089 ef470
  have ef4155 (X0 X1 : G) : dl X0 X1 = wf X0 (X0 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef129 ef4070 | exact superpose ef4070 ef129
  have ef4164 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef644 ef4054 | exact superpose ef4054 ef644
  have ef4199 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1793 ef4164 | exact superpose ef4164 ef1793
  have ef4225 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef900 ef4199 | exact superpose ef4199 ef900
  have ef4289 (X0 X1 X2 X3 : G) :
      wf X0 ((((X0 ◇ (dr X2 X2)) ◇ (wf X2 X1)) ◇ X3) ◇ (X1 ◇ X2)) =
      ((((X0 ◇ (dr X2 X2)) ◇ (wf X2 X1)) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3 := by
    first | exact superpose ef90 ef99 | exact superpose ef99 ef90
  have ef4334 (X0 X1 X2 : G) :
      wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = (((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) ◇ (X1 ◇ X2)) ◇ X1 := by
    first | exact superpose ef14 ef99 | exact superpose ef99 ef14
  have ef4341 (X0 X1 X2 : G) :
      (((X2 ◇ X1) ◇ ((dr X1 X1) ◇ (X2 ◇ X1))) ◇ (dr X1 X1)) ◇ (X0 ◇ (wf X1 X2)) =
      wf ((dr X1 X1) ◇ (X2 ◇ X1)) X0 := by
    first | exact superpose ef91 ef99 | exact superpose ef99 ef91
  have ef4342 (X0 X1 X2 : G) :
      ((((X2 ◇ X1) ◇ X0) ◇ ((wf X1 X2) ◇ ((X2 ◇ X1) ◇ X0))) ◇ (wf X1 X2)) ◇ (dr X1 X1) =
      wf ((wf X1 X2) ◇ ((X2 ◇ X1) ◇ X0)) X0 := by
    first | exact superpose ef92 ef99 | exact superpose ef99 ef92
  have ef4349 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (((dl (X1 ◇ X0) (X2 ◇ X3)) ◇ X1) ◇ X2)) ◇ ((dl (X1 ◇ X0) (X2 ◇ X3)) ◇ X1)) ◇ X3 =
      wf (((dl (X1 ◇ X0) (X2 ◇ X3)) ◇ X1) ◇ X2) X0 := by
    first | exact superpose ef61 ef99 | exact superpose ef99 ef61
  have ef4360 (X0 X1 X2 X3 : G) :
      ((X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X0))) ◇ ((dl (X1 ◇ X0) (X2 ◇ X3)) ◇ X1)) ◇ X3 =
      wf ((X3 ◇ X1) ◇ (X1 ◇ X0)) X0 := by
    first | exact superpose ef4119 ef4349 | exact superpose ef4349 ef4119
  have ef4367 (X0 X1 X2 : G) :
      wf (X1 ◇ (X1 ◇ X0)) X0 = ((((X2 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (wf X1 X2)) ◇
      (dr X1 X1) := by
    first | exact superpose ef349 ef4342 | exact superpose ef4342 ef349
  have ef4368 (X0 X1 X2 : G) :
      (((X2 ◇ X1) ◇ (wf X1 X2)) ◇ (dr X1 X1)) ◇ (X0 ◇ (wf X1 X2)) = wf (wf X1 X2) X0 := by
    first | exact superpose ef19 ef4341 | exact superpose ef4341 ef19
  have ef4375 (X0 X1 X2 : G) :
      wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = (dr ((X1 ◇ X2) ◇ (X2 ◇ X0)) X1) ◇
      ((X1 ◇ X2) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef470 ef4334 | exact superpose ef4334 ef470
  have ef4415 (X0 X1 X2 X3 : G) :
      wf X0 ((((X0 ◇ (dr X2 X2)) ◇ (wf X2 X1)) ◇ X3) ◇ (X1 ◇ X2)) =
      ((dr X2 X2) ◇ (X0 ◇ (X0 ◇ (dr X2 X2)))) ◇ X3 := by
    first | exact superpose ef3209 ef4289 | exact superpose ef4289 ef3209
  have ef4439 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (dl X0 X3)) ◇ ((dl (X1 ◇ X0) (X2 ◇ X3)) ◇ X1)) ◇ X3 = wf (dl X0 X3) X0 := by
    first | exact superpose ef30 ef4360 | exact superpose ef4360 ef30
  have ef4446 (X0 X1 X2 : G) :
      wf (X1 ◇ (X1 ◇ X0)) X0 = (dr (X1 ◇ (X1 ◇ X0)) (dr X1 X1)) ◇
      ((wf X1 X2) ◇ ((X2 ◇ X1) ◇ X0)) := by
    first | exact superpose ef470 ef4367 | exact superpose ef4367 ef470
  have ef4447 (X0 X1 X2 : G) :
      wf (wf X1 X2) X0 = X1 ◇ (wf X1 ((X0 ◇ (wf X1 X2)) ◇ ((X2 ◇ X1) ◇ (wf X1 X2)))) := by
    first | exact superpose ef1008 ef4368 | exact superpose ef4368 ef1008
  have ef4454 (X0 X1 X2 : G) :
      wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = X0 ◇
      ((X1 ◇ X2) ◇ (X2 ◇ (dr ((X1 ◇ X2) ◇ (X2 ◇ X0)) X1))) := by
    first | exact superpose ef957 ef4375 | exact superpose ef4375 ef957
  have ef4488 (X0 X1 X2 X3 : G) :
      wf X0 ((((X0 ◇ (dr X2 X2)) ◇ (wf X2 X1)) ◇ X3) ◇ (X1 ◇ X2)) = X2 ◇
      (X2 ◇ (dl (X0 ◇ (X0 ◇ (dr X2 X2))) X3)) := by
    first | exact superpose ef830 ef4415 | exact superpose ef4415 ef830
  have ef4512 (X0 X1 X2 X3 : G) :
      wf (dl X0 X3) X0 = (dr (dl X0 X3) X3) ◇ (((dl (X1 ◇ X0) (X2 ◇ X3)) ◇ X1) ◇ X2) := by
    first | exact superpose ef470 ef4439 | exact superpose ef4439 ef470
  have ef4519 (X0 X1 X2 : G) :
      wf (X1 ◇ (X1 ◇ X0)) X0 = X0 ◇
      ((wf X1 X2) ◇ ((X2 ◇ X1) ◇ (dr (X1 ◇ (X1 ◇ X0)) (dr X1 X1)))) := by
    first | exact superpose ef957 ef4446 | exact superpose ef4446 ef957
  have ef4520 (X0 X1 X2 : G) :
      wf (wf X1 X2) X0 = X1 ◇ (wf X1 ((X0 ◇ (X2 ◇ X1)) ◇ ((wf X1 X2) ◇ (wf X1 X2)))) := by
    first | exact superpose ef138 ef4447 | exact superpose ef4447 ef138
  have ef4524 (X0 X1 X2 : G) :
      wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = X0 ◇ (dl (dr ((X1 ◇ X2) ◇ (X2 ◇ X0)) X1) X1) := by
    first | exact superpose ef30 ef4454 | exact superpose ef4454 ef30
  have ef4552 (X0 X1 X2 X3 : G) :
      wf X0 ((((X0 ◇ (dr X2 X2)) ◇ (wf X2 X1)) ◇ X3) ◇ (X1 ◇ X2)) = X2 ◇
      (X2 ◇ ((X0 ◇ (dr X2 X2)) ◇ (dr X0 X3))) := by
    first | exact superpose ef644 ef4488 | exact superpose ef4488 ef644
  have ef4572 (X0 X1 X3 : G) : wf (dl X0 X3) X0 = (dr (dl X0 X3) X3) ◇ ((X3 ◇ X1) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef4119 ef4512 | exact superpose ef4512 ef4119
  have ef4578 (X0 X1 : G) :
      wf (X1 ◇ (X1 ◇ X0)) X0 = X0 ◇ (X1 ◇ (X1 ◇ (dr (X1 ◇ (X1 ◇ X0)) (dr X1 X1)))) := by
    first | exact superpose ef349 ef4519 | exact superpose ef4519 ef349
  have ef4581 (X0 X1 X2 : G) :
      wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = X0 ◇ (dl ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) X1) := by
    first | exact superpose ef1857 ef4524 | exact superpose ef4524 ef1857
  have ef4604 (X0 X1 X2 X3 : G) :
      wf X0 ((((X0 ◇ (dr X2 X2)) ◇ (wf X2 X1)) ◇ X3) ◇ (X1 ◇ X2)) = (dr X0 X3) ◇ X0 := by
    first | exact superpose ef3091 ef4552 | exact superpose ef4552 ef3091
  have ef4620 (X0 X1 X3 : G) : wf (dl X0 X3) X0 = X0 ◇ ((X3 ◇ X1) ◇ (X1 ◇ (dr (dl X0 X3) X3))) := by
    first | exact superpose ef957 ef4572 | exact superpose ef4572 ef957
  have ef4624 (X0 X1 : G) :
      wf (X1 ◇ (X1 ◇ X0)) X0 = X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (dr X1 X1))) ◇ X1))) := by
    first | exact superpose ef1857 ef4578 | exact superpose ef4578 ef1857
  have ef4627 (X0 X1 X2 : G) :
      wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = X0 ◇ ((X1 ◇ (dl ((X1 ◇ X2) ◇ X1) X2)) ◇ X0) := by
    first | exact superpose ef306 ef4581 | exact superpose ef4581 ef306
  have ef4649 (X0 X2 X3 : G) : (dr X0 X3) ◇ X0 = wf X0 ((dr X2 X2) ◇ (X3 ◇ (X0 ◇ (dr X2 X2)))) := by
    first | exact superpose ef3209 ef4604 | exact superpose ef4604 ef3209
  have ef4656 (X0 X3 : G) : wf (dl X0 X3) X0 = X0 ◇ (dl (dr (dl X0 X3) X3) X3) := by
    first | exact superpose ef30 ef4620 | exact superpose ef4620 ef30
  have ef4659 (X0 X1 : G) : wf (X1 ◇ (X1 ◇ X0)) X0 = X0 ◇ (dr X1 (X0 ◇ (X1 ◇ (dr X1 X1)))) := by
    first | exact superpose ef23 ef4624 | exact superpose ef4624 ef23
  have ef4662 (X0 X1 X2 : G) : wf ((X1 ◇ X2) ◇ (X2 ◇ X0)) X0 = X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef72 ef4627 | exact superpose ef4627 ef72
  have ef4679 (X0 X3 : G) : wf X0 (dr X3 X0) = (dr X0 X3) ◇ X0 := by
    first | exact superpose ef23 ef4649 | exact superpose ef4649 ef23
  have ef4685 (X0 X3 : G) : wf (dl X0 X3) X0 = X0 ◇ (dl (X3 ◇ (dr X3 X0)) X3) := by
    first | exact superpose ef1793 ef4656 | exact superpose ef4656 ef1793
  have ef4688 (X0 X1 : G) : wf (X1 ◇ (X1 ◇ X0)) X0 = X0 ◇ (((X1 ◇ (dr X1 X1)) ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef4659 | exact superpose ef4659 ef40
  have ef4691 (X0 X1 : G) : wf (dl X0 X1) X0 = X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef30 ef4662 | exact superpose ef4662 ef30
  have ef4708 (X0 X3 : G) : wf (dl X0 X3) X0 = X0 ◇ ((dr X3 X0) ◇ (dr X3 X3)) := by
    first | exact superpose ef644 ef4685 | exact superpose ef4685 ef644
  have ef4710 (X0 X1 : G) : wf (X1 ◇ (X1 ◇ X0)) X0 = X0 ◇ ((dl X1 X1) ◇ X0) := by
    first | exact superpose ef201 ef4688 | exact superpose ef4688 ef201
  have ef4734 (X0 X1 : G) : dl X1 X0 = X1 ◇ (wf X1 (X1 ◇ X0)) := by
    first | exact superpose ef17 ef177 | exact superpose ef177 ef17
  have ef4764 (X0 X1 : G) : X1 ◇ X0 = X0 ◇ (wf X0 (dr X0 X1)) := by
    first | exact superpose ef23 ef177 | exact superpose ef177 ef23
  have ef4765 (X0 X1 : G) : X1 ◇ (wf X1 X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef177 | exact superpose ef177 ef24
  have ef5063 (X0 X1 : G) : (wf X1 X0) ◇ (X1 ◇ (X0 ◇ X1)) = dl (wf (X0 ◇ X1) (dr X1 X1)) X0 := by
    first | exact superpose ef102 ef72 | exact superpose ef72 ef102
  have ef5068 (X0 X1 : G) : dl (wf (X0 ◇ X1) (dr X1 X1)) X0 = X1 ◇ (X1 ◇ (X0 ◇ (wf X1 X0))) := by
    first | exact superpose ef957 ef5063 | exact superpose ef5063 ef957
  have ef5147 (X0 X1 : G) : dr (X0 ◇ X1) X0 = dl (wf (X0 ◇ X1) (dr X1 X1)) X0 := by
    first | exact superpose ef2715 ef5068 | exact superpose ef5068 ef2715
  have ef5475 (X0 X1 X2 : G) : wf X2 (X1 ◇ (dr X2 X0)) = (dr X2 X2) ◇ (dl X0 X1) := by
    first | exact superpose ef201 ef19 | exact superpose ef19 ef201
  have ef5478 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (X2 ◇ X3) = dl X3 (X1 ◇ (dr X2 X0)) := by
    first | exact superpose ef201 ef30 | exact superpose ef30 ef201
  have ef5501 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dl X0 X1) = dr (X1 ◇ (dr X3 X0)) X2 := by
    first | exact superpose ef201 ef107 | exact superpose ef107 ef201
  have ef5518 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef201 ef13 | exact superpose ef13 ef201
  have ef5523 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X3 X2) X0) = X2 ◇ ((dl X0 X1) ◇ X3) := by
    first | exact superpose ef201 ef26 | exact superpose ef26 ef201
  have ef5528 (X0 X1 X2 X3 : G) : X2 ◇ ((dl X0 X1) ◇ X3) = X1 ◇ ((dl X0 X2) ◇ X3) := by
    first | exact superpose ef1781 ef5523 | exact superpose ef5523 ef1781
  have ef6622 (X0 X1 X2 : G) : X1 ◇ (dr (X2 ◇ (X2 ◇ X2)) X0) = wf X2 (dl X0 X1) := by
    first | exact superpose ef201 ef214 | exact superpose ef214 ef201
  have ef6651 (X0 X1 X2 : G) : wf X2 (dl X0 X1) = X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2) := by
    first | exact superpose ef1857 ef6622 | exact superpose ef6622 ef1857
  have ef6770 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = dl X3 (dl (X1 ◇ (X2 ◇ X0)) X2) := by
    first | exact superpose ef239 ef30 | exact superpose ef30 ef239
  have ef6848 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = (dl X2 X3) ◇ (X1 ◇ (X2 ◇ X0)) := by
    first | exact superpose ef4079 ef6770 | exact superpose ef6770 ef4079
  have ef7102 (X0 X1 X2 X3 : G) :
      X2 ◇ X1 = (dl ((X0 ◇ (dr X1 X1)) ◇ (wf X1 X2)) (dl X0 X3)) ◇ X3 := by
    first | exact superpose ef90 ef241 | exact superpose ef241 ef90
  have ef7232 (X0 X1 X2 : G) : X2 ◇ X1 = dr X0 ((X0 ◇ (dr X1 X1)) ◇ (wf X1 X2)) := by
    first | exact superpose ef1765 ef7102 | exact superpose ef7102 ef1765
  have ef7307 (X0 X1 X2 : G) : X2 ◇ X1 = ((wf X1 X2) ◇ X0) ◇ (X0 ◇ (dr X1 X1)) := by
    first | exact superpose ef40 ef7232 | exact superpose ef7232 ef40
  have ef7344 (X0 X1 X2 : G) : X2 ◇ X1 = (X1 ◇ X0) ◇ (dl ((wf X1 X2) ◇ X0) X1) := by
    first | exact superpose ef3564 ef7307 | exact superpose ef7307 ef3564
  have ef7367 (X0 X1 X2 : G) : X2 ◇ X1 = (X1 ◇ X0) ◇ (X0 ◇ (dr (wf X1 X2) X1)) := by
    first | exact superpose ef644 ef7344 | exact superpose ef7344 ef644
  have ef7378 (X1 X2 : G) : X2 ◇ X1 = dl (dr (wf X1 X2) X1) X1 := by
    first | exact superpose ef30 ef7367 | exact superpose ef7367 ef30
  have ef7479 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) (dl X1 X2) = dr ((X0 ◇ X1) ◇ X2) X3 := by
    first | exact superpose ef27 ef316 | exact superpose ef316 ef27
  have ef7490 (X0 X1 X2 X3 : G) : dr X1 ((X1 ◇ X2) ◇ (X0 ◇ X3)) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef70 ef316 | exact superpose ef316 ef70
  have ef7495 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef156 ef316 | exact superpose ef316 ef156
  have ef7503 (X0 X1 : G) : dr X0 (dr X0 X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef19 ef316 | exact superpose ef316 ef19
  have ef7544 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef105 ef7503 | exact superpose ef7503 ef105
  have ef7552 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef40 ef7495 | exact superpose ef7495 ef40
  have ef7557 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef40 ef7490 | exact superpose ef7490 ef40
  have ef7566 (X0 X1 X2 X3 : G) : dl (X3 ◇ X0) (dl X1 X2) = (dl X3 (X2 ◇ X0)) ◇ X1 := by
    first | exact superpose ef1777 ef7479 | exact superpose ef7479 ef1777
  have ef7609 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef644 ef7552 | exact superpose ef7552 ef644
  have ef7612 (X0 X2 X3 : G) : dl X2 (X0 ◇ X3) = dl X0 (X2 ◇ X3) := by
    first | exact superpose ef30 ef7557 | exact superpose ef7557 ef30
  have ef7616 (X0 X1 X2 X3 : G) : (dl X3 (X2 ◇ X0)) ◇ X1 = (dl X2 (X3 ◇ X0)) ◇ X1 := by
    first | exact superpose ef4079 ef7566 | exact superpose ef7566 ef4079
  have ef7639 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef30 ef7609 | exact superpose ef7609 ef30
  have ef7878 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef337 ef72 | exact superpose ef72 ef337
  have ef7908 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef4079 ef7878 | exact superpose ef7878 ef4079
  have ef8029 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = dr X1 (dl X2 (dr X0 X0)) := by
    first | exact superpose ef88 ef338 | exact superpose ef338 ef88
  have ef8073 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = dr X1 (X0 ◇ (X0 ◇ X2)) := by
    first | exact superpose ef129 ef8029 | exact superpose ef8029 ef129
  have ef8096 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = ((X0 ◇ X2) ◇ X1) ◇ X0 := by
    first | exact superpose ef40 ef8073 | exact superpose ef8073 ef40
  have ef8111 (X0 X1 X2 : G) : X0 ◇ (wf X0 (dl X2 X1)) = (dr X2 X0) ◇ (X1 ◇ X0) := by
    first | exact superpose ef470 ef8096 | exact superpose ef8096 ef470
  have ef8141 (X0 X1 : G) : (X1 ◇ X1) ◇ X0 = dr (wf X1 X0) X1 := by
    first | exact superpose ef478 ef23 | exact superpose ef23 ef478
  have ef8152 (X0 X1 X2 : G) : dr X2 (wf X1 X0) = (X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef478 ef23 | exact superpose ef23 ef478
  have ef8154 (X0 X1 X2 : G) : dl X2 (wf X1 X0) = X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2) := by
    first | exact superpose ef478 ef30 | exact superpose ef30 ef478
  have ef8163 (X0 X1 X2 X3 : G) :
      (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2)) = X3 := by
    first | exact superpose ef478 ef67 | exact superpose ef67 ef478
  have ef8205 (X0 X1 X2 X3 : G) :
      X2 ◇ (X2 ◇ (X2 ◇ (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)))) = X3 := by
    first | exact superpose ef957 ef8163 | exact superpose ef8163 ef957
  have ef8238 (X0 X1 X2 X3 : G) : (wf X2 X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (wf X2 X0))) = X3 := by
    first | exact superpose ef3919 ef8205 | exact superpose ef8205 ef3919
  have ef8263 (X0 X2 X3 : G) : (wf X2 X3) ◇ (dl (wf X2 X0) X0) = X3 := by
    first | exact superpose ef30 ef8238 | exact superpose ef8238 ef30
  have ef8669 (X0 X1 X2 : G) : dr X1 X2 = dr X0 (dl (dr X0 X2) X1) := by
    first | exact superpose ef15 ef620 | exact superpose ef620 ef15
  have ef8678 (X0 X1 X2 : G) : dr X1 (X2 ◇ (X2 ◇ X2)) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef478 ef620 | exact superpose ef620 ef478
  have ef8721 (X0 X1 X2 : G) : dr X0 (dl (wf X2 X0) X1) = ((X2 ◇ X2) ◇ X1) ◇ X2 := by
    first | exact superpose ef40 ef8678 | exact superpose ef8678 ef40
  have ef8764 (X0 X1 X2 : G) : (dr X2 X2) ◇ (X1 ◇ X2) = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef470 ef8721 | exact superpose ef8721 ef470
  have ef8798 (X0 X1 X2 : G) : wf X2 X1 = dr X0 (dl (wf X2 X0) X1) := by
    first | exact superpose ef19 ef8764 | exact superpose ef8764 ef19
  have ef8909 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) ◇ X2 = dl (X0 ◇ (dr X1 X2)) X3 := by
    first | exact superpose ef644 ef254 | exact superpose ef254 ef644
  have ef8928 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) ◇ X2 = (dr X1 X2) ◇ (dr X0 X3) := by
    first | exact superpose ef644 ef8909 | exact superpose ef8909 ef644
  have ef9083 (X0 X1 : G) : wf X1 (X1 ◇ X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef690 | exact superpose ef690 ef24
  have ef9101 (X0 X1 : G) : X1 ◇ (wf X1 X0) = wf X1 (X1 ◇ X0) := by
    first | exact superpose ef4765 ef9083 | exact superpose ef9083 ef4765
  have ef9399 (X0 X1 : G) : dl X0 X1 = X0 ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef112 ef810 | exact superpose ef810 ef112
  have ef9418 (X0 X1 X2 : G) :
      wf (dr (dr X0 X2) X1) X2 = (dr (dr (dr X0 X2) X1) (dr (dr X0 X2) X1)) ◇ (dl X0 X1) := by
    first | exact superpose ef810 ef19 | exact superpose ef19 ef810
  have ef9523 (X0 X1 X2 : G) :
      wf (dr (dr X0 X2) X1) X2 = (dr (dr (dr X0 X2) X1) (dl X0 X1)) ◇ (dr (dr X0 X2) X1) := by
    first | exact superpose ef3631 ef9418 | exact superpose ef9418 ef3631
  have ef9590 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = (dr ((dl X1 X2) ◇ X0) (dl X0 X1)) ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef1781 ef9523 | exact superpose ef9523 ef1781
  have ef9630 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((dl X1 (dr ((dl X1 X2) ◇ X0) (dl X0 X1))) ◇ X0) := by
    first | exact superpose ef5528 ef9590 | exact superpose ef9590 ef5528
  have ef9660 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((((dl X1 X2) ◇ X0) ◇ ((dl X0 X1) ◇ X1)) ◇ X0) := by
    first | exact superpose ef129 ef9630 | exact superpose ef9630 ef129
  have ef9678 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((dr X0 X0) ◇ (((dl X0 X1) ◇ X1) ◇ (dl X1 X2))) := by
    first | exact superpose ef470 ef9660 | exact superpose ef9660 ef470
  have ef9690 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((dr X0 X0) ◇ (X1 ◇ (dl ((dl X0 X1) ◇ X1) X2))) := by
    first | exact superpose ef969 ef9678 | exact superpose ef9678 ef969
  have ef9699 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((dr X0 X0) ◇ (X1 ◇ (X1 ◇ (dr (dl X0 X1) X2)))) := by
    first | exact superpose ef644 ef9690 | exact superpose ef9690 ef644
  have ef9704 (X0 X1 X2 : G) :
      wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((dr X0 X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (dr X2 X0))))) := by
    first | exact superpose ef1793 ef9699 | exact superpose ef9699 ef1793
  have ef9707 (X0 X1 X2 : G) : wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ ((dr X0 X0) ◇ ((wf X1 X2) ◇ X0)) := by
    first | exact superpose ef2986 ef9704 | exact superpose ef9704 ef2986
  have ef9710 (X0 X1 X2 : G) : wf ((dl X1 X2) ◇ X0) X2 = X2 ◇ (wf X0 (wf X1 X2)) := by
    first | exact superpose ef19 ef9707 | exact superpose ef9707 ef19
  have ef11613 (X0 X1 X2 : G) : dr X0 (dl X2 X1) = dr X1 (X2 ◇ (X2 ◇ (wf X2 X0))) := by
    first | exact superpose ef1022 ef620 | exact superpose ef620 ef1022
  have ef11646 (X0 X1 X2 : G) : dr X0 (dl X2 X1) = ((X2 ◇ (wf X2 X0)) ◇ X1) ◇ X2 := by
    first | exact superpose ef40 ef11613 | exact superpose ef11613 ef40
  have ef11707 (X0 X1 X2 : G) : dr X0 (dl X2 X1) = (dr (wf X2 X0) X2) ◇ (X1 ◇ X2) := by
    first | exact superpose ef470 ef11646 | exact superpose ef11646 ef470
  have ef11751 (X0 X1 X2 : G) : dr X0 (dl X2 X1) = X2 ◇ (wf X2 (dl (wf X2 X0) X1)) := by
    first | exact superpose ef8111 ef11707 | exact superpose ef11707 ef8111
  have ef13286 (X0 X1 X2 : G) : wf X0 (dr X1 X2) = (dr X0 X0) ◇ ((dr X1 X0) ◇ X2) := by
    first | exact superpose ef2327 ef84 | exact superpose ef84 ef2327
  have ef13289 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = dr X3 ((dr X1 X0) ◇ X2) := by
    first | exact superpose ef2327 ef156 | exact superpose ef156 ef2327
  have ef13311 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = (X2 ◇ X3) ◇ (dr X1 X0) := by
    first | exact superpose ef40 ef13289 | exact superpose ef13289 ef40
  have ef14072 (X0 X1 X2 X3 : G) :
      dl (X0 ◇ (wf X1 X3)) X2 = (X2 ◇ (X3 ◇ X1)) ◇ (dr X0 (dr X1 X1)) := by
    first | exact superpose ef106 ef30 | exact superpose ef30 ef106
  have ef14173 (X0 X1 X2 X3 : G) :
      dl (X0 ◇ (wf X1 X3)) X2 = (X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef105 ef14072 | exact superpose ef14072 ef105
  have ef14323 (X0 X1 X2 X3 : G) :
      dl (X0 ◇ (wf X1 X3)) X2 = X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    first | exact superpose ef957 ef14173 | exact superpose ef14173 ef957
  have ef14444 (X0 X1 X2 X3 : G) :
      X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) = (wf X1 X3) ◇ (dr X0 X2) := by
    first | exact superpose ef644 ef14323 | exact superpose ef14323 ef644
  have ef15145 (X0 X1 X2 X3 : G) :
      dr X2 (wf X1 X0) = (X3 ◇ (wf (X0 ◇ X1) (dr X1 X1))) ◇
      (X2 ◇ (dr X3 ((X1 ◇ (X0 ◇ X1)) ◇ X0))) := by
    first | exact superpose ef102 ef109 | exact superpose ef109 ef102
  have ef15475 (X0 X1 X2 : G) :
      dr X2 (wf X1 X0) = dr X2 (dl ((X1 ◇ (X0 ◇ X1)) ◇ X0) (wf (X0 ◇ X1) (dr X1 X1))) := by
    first | exact superpose ef1806 ef15145 | exact superpose ef15145 ef1806
  have ef15630 (X0 X1 X2 : G) :
      dr X2 (wf X1 X0) = dr X2 (((wf (X0 ◇ X1) (dr X1 X1)) ◇ (dl (X0 ◇ X1) X0)) ◇ X1) := by
    first | exact superpose ef306 ef15475 | exact superpose ef15475 ef306
  have ef15738 (X0 X1 X2 : G) :
      dr X2 (wf X1 X0) = (X1 ◇ X2) ◇ ((wf (X0 ◇ X1) (dr X1 X1)) ◇ (dl (X0 ◇ X1) X0)) := by
    first | exact superpose ef40 ef15630 | exact superpose ef15630 ef40
  have ef15817 (X0 X1 X2 : G) :
      dr X2 (wf X1 X0) = (X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (dl (wf (X0 ◇ X1) (dr X1 X1)) X0)) := by
    first | exact superpose ef969 ef15738 | exact superpose ef15738 ef969
  have ef15865 (X0 X1 X2 : G) : dr X2 (wf X1 X0) = (X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (dr (X0 ◇ X1) X0)) := by
    first | exact superpose ef5147 ef15817 | exact superpose ef15817 ef5147
  have ef15888 (X0 X1 X2 : G) : dr X2 (wf X1 X0) = (X1 ◇ X2) ◇ (dr X1 (X0 ◇ X1)) := by
    first | exact superpose ef115 ef15865 | exact superpose ef15865 ef115
  have ef15903 (X0 X1 X2 : G) : dr X2 (wf X1 X0) = (X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef15888 | exact superpose ef15888 ef40
  have ef16281 (X0 X1 X2 X3 X4 : G) :
      dl ((X0 ◇ X4) ◇ (dr X2 X3)) X1 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef124 ef30 | exact superpose ef30 ef124
  have ef16313 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ X1) ◇ (dr X2 X3)) ◇ X4 = dl X0 (dl X4 (X2 ◇ (X3 ◇ X1))) := by
    first | exact superpose ef124 ef325 | exact superpose ef325 ef124
  have ef16354 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ X1) ◇ (dr X2 X3)) ◇ X4 = (dl (X2 ◇ (X3 ◇ X1)) X0) ◇ X4 := by
    first | exact superpose ef4079 ef16313 | exact superpose ef16313 ef4079
  have ef16386 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X1 ◇ (dl X4 (dr X2 X3))) ◇ X0 := by
    first | exact superpose ef306 ef16281 | exact superpose ef16281 ef306
  have ef16568 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ X1) ◇ (dr X2 X3)) ◇ X4 = ((X3 ◇ X1) ◇ (dr X2 X0)) ◇ X4 := by
    first | exact superpose ef644 ef16354 | exact superpose ef16354 ef644
  have ef16596 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (dr X2 X3) ◇ (dr (X0 ◇ X1) X4) := by
    first | exact superpose ef5518 ef16386 | exact superpose ef16386 ef5518
  have ef19220 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = dr (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) X4 := by
    first | exact superpose ef126 ef109 | exact superpose ef109 ef126
  have ef19234 (X0 X1 X2 X3 X4 : G) :
      (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ X4) := by
    first | exact superpose ef126 ef23 | exact superpose ef23 ef126
  have ef19353 (X0 X1 X2 X3 X4 : G) :
      (dr X1 X2) ◇ (X3 ◇ X0) = (X4 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X4)) ◇ X0) := by
    first | exact superpose ef40 ef19234 | exact superpose ef19234 ef40
  have ef19366 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (dl X4 (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0 := by
    first | exact superpose ef1777 ef19220 | exact superpose ef19220 ef1777
  have ef19571 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (X1 ◇ (X2 ◇ X3)) ◇ (dr X4 (dl X0 X3)) := by
    first | exact superpose ef7908 ef19366 | exact superpose ef19366 ef7908
  have ef20543 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = dl X1 ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef131 ef538 | exact superpose ef538 ef131
  have ef20568 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = (X3 ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X2) ◇ X1) := by
    first | exact superpose ef291 ef20543 | exact superpose ef20543 ef291
  have ef22046 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (X3 ◇ X4) = ((X1 ◇ (dr X2 X0)) ◇ X3) ◇ (X2 ◇ X4) := by
    first | exact superpose ef201 ef138 | exact superpose ef138 ef201
  have ef22325 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X3) ◇ X4) ◇ (X0 ◇ X2) = dr X4 ((X0 ◇ X1) ◇ (X2 ◇ X3)) := by
    first | exact superpose ef138 ef40 | exact superpose ef40 ef138
  have ef22367 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = dr ((X0 ◇ X2) ◇ X4) (X1 ◇ X3) := by
    first | exact superpose ef138 ef1903 | exact superpose ef1903 ef138
  have ef22407 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = (dl (X1 ◇ X3) (X4 ◇ X0)) ◇ X2 := by
    first | exact superpose ef1777 ef22367 | exact superpose ef22367 ef1777
  have ef22449 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X3) ◇ X4) ◇ (X0 ◇ X2) = ((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1) := by
    first | exact superpose ef40 ef22325 | exact superpose ef22325 ef40
  have ef22804 (X0 X1 X2 X3 X4 : G) :
      dr ((X0 ◇ X1) ◇ (X2 ◇ X3)) X4 = X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) := by
    first | exact superpose ef7908 ef22407 | exact superpose ef22407 ef7908
  have ef23089 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (dr (X1 ◇ X3) (dl X2 X4)) = (X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X2 := by
    first | exact superpose ef1857 ef22804 | exact superpose ef22804 ef1857
  have ef23864 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (dr (dl X0 X0) X1) := by
    first | exact superpose ef2410 ef1793 | exact superpose ef1793 ef2410
  have ef23865 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (X0 ◇ (dr X1 X0)) := by
    first | exact superpose ef1793 ef23864 | exact superpose ef23864 ef1793
  have ef23967 (X0 X1 X2 X3 : G) :
      (X0 ◇ (wf X0 X1)) ◇ (X2 ◇ X3) = ((X3 ◇ (dr X0 X0)) ◇ X2) ◇ X1 := by
    first | exact superpose ef88 ef139 | exact superpose ef139 ef88
  have ef23973 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ X3 := by
    first | exact superpose ef139 ef139
  have ef23983 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = ((X5 ◇ (dr X0 X1)) ◇ X4) ◇ (X0 ◇ (dr X2 X3)) := by
    first | exact superpose ef109 ef139 | exact superpose ef139 ef109
  have ef23985 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4) = ((X4 ◇ X0) ◇ X3) ◇ (dr X2 X1) := by
    first | exact superpose ef36 ef139 | exact superpose ef139 ef36
  have ef24021 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1))) = ((dr X0 X1) ◇ X2) ◇ (dr X3 X4) := by
    first | exact superpose ef109 ef139 | exact superpose ef139 ef109
  have ef24024 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ ((dl (X2 ◇ X4) X1) ◇ X0)) = ((dr X0 X1) ◇ X3) ◇ X4 := by
    first | exact superpose ef156 ef139 | exact superpose ef139 ef156
  have ef24208 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ (X0 ◇ (dr X4 X3))) ◇ X1 = X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4) := by
    first | exact superpose ef139 ef26 | exact superpose ef26 ef139
  have ef24374 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ ((dl (X2 ◇ X4) X1) ◇ X0)) = X0 ◇ (X1 ◇ (dl X3 X4)) := by
    first | exact superpose ef830 ef24024 | exact superpose ef24024 ef830
  have ef24376 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1))) = X0 ◇ (X1 ◇ (dl X2 (dr X3 X4))) := by
    first | exact superpose ef830 ef24021 | exact superpose ef24021 ef830
  have ef24400 (X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = (dl X1 X5) ◇ (X4 ◇ (dr X2 X3)) := by
    first | exact superpose ef22046 ef23983 | exact superpose ef23983 ef22046
  have ef24408 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((dr X0 X1) ◇ (dr (X4 ◇ X5) X2)) ◇ X3 := by
    first | exact superpose ef16596 ef23973 | exact superpose ef23973 ef16596
  have ef24414 (X0 X1 X2 X3 : G) :
      (X0 ◇ (wf X0 X1)) ◇ (X2 ◇ X3) = (X0 ◇ (wf X0 (X2 ◇ X3))) ◇ X1 := by
    first | exact superpose ef1008 ef23967 | exact superpose ef23967 ef1008
  have ef24547 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X1 ◇ (dl X3 X4)) = X2 ◇ (X3 ◇ ((X4 ◇ (dr X2 X1)) ◇ X0)) := by
    first | exact superpose ef644 ef24374 | exact superpose ef24374 ef644
  have ef24549 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1))) = X0 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X2))) := by
    first | exact superpose ef129 ef24376 | exact superpose ef24376 ef129
  have ef24565 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = X0 ◇ (X1 ◇ (dl (dr (X4 ◇ X5) X2) X3)) := by
    first | exact superpose ef830 ef24408 | exact superpose ef24408 ef830
  have ef26311 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇
      ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef167 ef99 | exact superpose ef99 ef167
  have ef26424 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) X2) X2)) := by
    first | exact superpose ef24565 ef26311 | exact superpose ef26311 ef24565
  have ef26635 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr X2 X2) ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4))) := by
    first | exact superpose ef7639 ef26424 | exact superpose ef26424 ef7639
  have ef26809 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (((dl X2 X3) ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X3) ◇ (dr X2 X2)))) := by
    first | exact superpose ef291 ef26635 | exact superpose ef26635 ef291
  have ef26934 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ (dl ((dl X2 X3) ◇ (X4 ◇ X0)) X2))) := by
    first | exact superpose ef3564 ef26809 | exact superpose ef26809 ef3564
  have ef27024 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (dr (dl X2 X3) X2)))) := by
    first | exact superpose ef644 ef26934 | exact superpose ef26934 ef644
  have ef27090 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((dl X3 (dr (dl X2 X3) X2)) ◇ (dr X0 X2))) := by
    first | exact superpose ef20568 ef27024 | exact superpose ef27024 ef20568
  have ef27136 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ (((dl X2 X3) ◇ (X2 ◇ X3)) ◇ (dr X0 X2))) := by
    first | exact superpose ef129 ef27090 | exact superpose ef27090 ef129
  have ef27170 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (dr X0 (dl X2 X3)))) := by
    first | exact superpose ef13311 ef27136 | exact superpose ef27136 ef13311
  have ef27198 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := by
    first | exact superpose ef19571 ef27170 | exact superpose ef27170 ef19571
  have ef27224 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (wf X2 (dl X0 X1)) := by
    first | exact superpose ef6651 ef27198 | exact superpose ef27198 ef6651
  have ef27280 (X0 X1 X2 : G) : dl (wf X0 X2) (dr X1 X0) = dl ((dr X0 X1) ◇ X0) X2 := by
    first | exact superpose ef4679 ef3584 | exact superpose ef3584 ef4679
  have ef27346 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = dr (dl (wf X0 X1) X2) X3 := by
    first | exact superpose ef3584 ef1793 | exact superpose ef1793 ef3584
  have ef27349 (X0 X1 X2 X3 : G) : dl (wf X0 (dr X1 X2)) X3 = X1 ◇ (X2 ◇ (wf X0 X3)) := by
    first | exact superpose ef3584 ef129 | exact superpose ef129 ef3584
  have ef27355 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = X2 ◇ (dr X3 (wf X0 X1)) := by
    first | exact superpose ef1793 ef27346 | exact superpose ef27346 ef1793
  have ef27393 (X0 X1 X2 : G) : X0 ◇ (dr (dr X0 X1) X2) = dl (wf X0 X2) (dr X1 X0) := by
    first | exact superpose ef644 ef27280 | exact superpose ef27280 ef644
  have ef27421 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (wf X0 X2)) = X0 ◇ (dr (dr X0 X1) X2) := by
    first | exact superpose ef129 ef27393 | exact superpose ef27393 ef129
  have ef27431 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (wf X0 X2)) = X0 ◇ ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef1781 ef27421 | exact superpose ef27421 ef1781
  have ef27691 (X0 X1 X2 X3 X4 : G) :
      dr ((X1 ◇ (dl X0 X2)) ◇ X3) X4 = dl (X4 ◇ X0) ((X3 ◇ X1) ◇ X2) := by
    first | exact superpose ef180 ef316 | exact superpose ef316 ef180
  have ef27741 (X0 X1 X2 X3 X4 : G) :
      dr ((X1 ◇ (dl X0 X2)) ◇ X3) X4 = X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)) := by
    first | exact superpose ef291 ef27691 | exact superpose ef27691 ef291
  have ef27996 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)) = (dl X4 (X3 ◇ X1)) ◇ (dl X0 X2) := by
    first | exact superpose ef1777 ef27741 | exact superpose ef27741 ef1777
  have ef28233 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)) = X1 ◇ (dr X4 (dl (dl X0 X2) X3)) := by
    first | exact superpose ef7908 ef27996 | exact superpose ef27996 ef7908
  have ef28423 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (dr X4 ((X3 ◇ X0) ◇ X2)) = X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)) := by
    first | exact superpose ef254 ef28233 | exact superpose ef28233 ef254
  have ef28567 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)) = X1 ◇ ((X2 ◇ X4) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef40 ef28423 | exact superpose ef28423 ef40
  have ef29160 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef3631 ef969 | exact superpose ef969 ef3631
  have ef30917 (X0 X1 X2 X3 : G) : (dl X0 (wf X1 X2)) ◇ X3 = dl (wf X1 (dl X3 X0)) X2 := by
    first | exact superpose ef4079 ef3584 | exact superpose ef3584 ef4079
  have ef31271 (X0 X1 X2 X3 X4 X5 : G) :
      dr ((X1 ◇ (dr X2 (dl X0 X3))) ◇ X2) X4 = (((X3 ◇ X1) ◇ (dr X5 X4)) ◇ X5) ◇ X0 := by
    first | exact superpose ef205 ef203 | exact superpose ef203 ef205
  have ef31339 (X0 X1 X2 X3 X4 X5 : G) :
      dr ((X1 ◇ (dr X2 (dl X0 X3))) ◇ X2) X4 = ((dr X1 X5) ◇ ((dr X5 X4) ◇ X3)) ◇ X0 := by
    first | exact superpose ef470 ef31271 | exact superpose ef31271 ef470
  have ef31579 (X0 X1 X2 X3 X4 X5 : G) :
      dr ((X1 ◇ (dr X2 (dl X0 X3))) ◇ X2) X4 = X1 ◇ (X5 ◇ (dl ((dr X5 X4) ◇ X3) X0)) := by
    first | exact superpose ef830 ef31339 | exact superpose ef31339 ef830
  have ef31810 (X0 X1 X2 X3 X4 X5 : G) :
      dr ((X1 ◇ (dr X2 (dl X0 X3))) ◇ X2) X4 = X1 ◇ (X5 ◇ (X3 ◇ (dr (dr X5 X4) X0))) := by
    first | exact superpose ef644 ef31579 | exact superpose ef31579 ef644
  have ef32000 (X0 X1 X2 X3 X4 X5 : G) :
      dr ((X1 ◇ (dr X2 (dl X0 X3))) ◇ X2) X4 = X1 ◇ (X5 ◇ (X3 ◇ ((dl X0 X4) ◇ X5))) := by
    first | exact superpose ef1781 ef31810 | exact superpose ef31810 ef1781
  have ef32143 (X0 X1 X2 X3 X4 : G) :
      dr ((X1 ◇ (dr X2 (dl X0 X3))) ◇ X2) X4 = X1 ◇ (dr X3 (dl X0 X4)) := by
    first | exact superpose ef23 ef32000 | exact superpose ef32000 ef23
  have ef32245 (X0 X1 X2 X3 X4 : G) :
      (dl X4 (X2 ◇ X1)) ◇ (dr X2 (dl X0 X3)) = X1 ◇ (dr X3 (dl X0 X4)) := by
    first | exact superpose ef1777 ef32143 | exact superpose ef32143 ef1777
  have ef32326 (X0 X1 X3 X4 : G) : X1 ◇ (dr X4 (dl X0 X3)) = X1 ◇ (dr X3 (dl X0 X4)) := by
    first | exact superpose ef1854 ef32245 | exact superpose ef32245 ef1854
  have ef32561 (X0 X1 : G) : wf (X0 ◇ X1) X0 = dl (X0 ◇ X1) (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef12 ef4155 | exact superpose ef4155 ef12
  have ef32611 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ ((dr X1 X1) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef460 ef32561 | exact superpose ef32561 ef460
  have ef32693 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ (wf X1 X0) := by
    first | exact superpose ef19 ef32611 | exact superpose ef32611 ef19
  have ef33251 (X0 X1 X2 X3 X4 : G) :
      dl X4 (dl X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 ◇ ((dr X2 X3) ◇ X4) := by
    first | exact superpose ef243 ef30 | exact superpose ef30 ef243
  have ef33383 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = (dl (X2 ◇ (X3 ◇ (X0 ◇ X1))) X4) ◇ X1 := by
    first | exact superpose ef4079 ef33251 | exact superpose ef33251 ef4079
  have ef33637 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = ((X3 ◇ (X0 ◇ X1)) ◇ (dr X2 X4)) ◇ X1 := by
    first | exact superpose ef644 ef33383 | exact superpose ef33383 ef644
  have ef33861 (X0 X2 X3 X4 : G) : X0 ◇ ((dr X2 X3) ◇ X4) = X0 ◇ ((dr X2 X4) ◇ X3) := by
    first | exact superpose ef139 ef33637 | exact superpose ef33637 ef139
  have ef34354 (X0 X1 X2 X3 : G) : X2 ◇ (dl X0 (X3 ◇ X1)) = X3 ◇ (dl X2 (X0 ◇ X1)) := by
    first | exact superpose ef4225 ef4225
  have ef34509 (X0 X1 X2 X3 : G) :
      ((X2 ◇ ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2)) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) (X0 ◇ X1) := by
    first | exact superpose ef4225 ef99 | exact superpose ef99 ef4225
  have ef34531 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) (X0 ◇ X1) := by
    first | exact superpose ef7908 ef34509 | exact superpose ef34509 ef7908
  have ef34668 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 (dl X2 (X2 ◇ X3))) (dl X0 X1)) := by
    first | exact superpose ef27224 ef34531 | exact superpose ef34531 ef27224
  have ef34752 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 X3))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef18 ef34668 | exact superpose ef34668 ef18
  have ef34797 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) := by
    first | exact superpose ef470 ef34752 | exact superpose ef34752 ef470
  have ef34825 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) := by
    first | exact superpose ef7908 ef34797 | exact superpose ef34797 ef7908
  have ef34846 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      (dl (dr (X1 ◇ (dr X0 X3)) X3) (dl X2 (X2 ◇ X3))) := by
    first | exact superpose ef3564 ef34825 | exact superpose ef34825 ef3564
  have ef34862 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      ((dl (X2 ◇ X3) (dr (X1 ◇ (dr X0 X3)) X3)) ◇ X2) := by
    first | exact superpose ef4079 ef34846 | exact superpose ef34846 ef4079
  have ef34873 (X0 X1 X3 : G) :
      (X0 ◇ X1) ◇ (dl (dr (X1 ◇ (dr X0 X3)) X3) X3) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef538 ef34862 | exact superpose ef34862 ef538
  have ef34879 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dl (dr X3 X3) (X1 ◇ (dr X0 X3))) := by
    first | exact superpose ef7639 ef34873 | exact superpose ef34873 ef7639
  have ef34883 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ (dl (X0 ◇ X1) ((dr X3 X3) ◇ (dr X0 X3))) := by
    first | exact superpose ef34354 ef34879 | exact superpose ef34879 ef34354
  have ef34887 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((dl X3 (dr X3 X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef5478 ef34883 | exact superpose ef34883 ef5478
  have ef34890 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef129 ef34887 | exact superpose ef34887 ef129
  have ef34893 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = dl (X0 ◇ (X0 ◇ X1)) (wf X3 X1) := by
    first | exact superpose ef8154 ef34890 | exact superpose ef34890 ef8154
  have ef34895 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dr X0 (wf X3 X1)) := by
    first | exact superpose ef644 ef34893 | exact superpose ef34893 ef644
  have ef34897 (X0 X1 X3 : G) :
      X1 ◇ (dr X0 (wf X3 (X0 ◇ X1))) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef27355 ef34895 | exact superpose ef34895 ef27355
  have ef36777 (X0 X1 : G) : X0 ◇ (wf X0 (dl X0 X1)) = dl X0 (wf X0 (X0 ◇ X1)) := by
    first | exact superpose ef4734 ef4734
  have ef36872 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = ((((wf X0 (X0 ◇ X1)) ◇ X2) ◇ (dl X2 X0)) ◇ (dl X0 X1)) ◇ X0 := by
    first | exact superpose ef4734 ef104 | exact superpose ef104 ef4734
  have ef37003 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = (dr (dl X2 X0) X0) ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ X2)) := by
    first | exact superpose ef470 ef36872 | exact superpose ef36872 ef470
  have ef37089 (X0 X1 : G) : dl X0 (X0 ◇ (wf X0 X1)) = X0 ◇ (wf X0 (dl X0 X1)) := by
    first | exact superpose ef9101 ef36777 | exact superpose ef36777 ef9101
  have ef37165 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (dr (dl X2 X0) X0))) := by
    first | exact superpose ef957 ef37003 | exact superpose ef37003 ef957
  have ef37243 (X0 X1 : G) : wf X0 X1 = X0 ◇ (wf X0 (dl X0 X1)) := by
    first | exact superpose ef18 ef37089 | exact superpose ef37089 ef18
  have ef37308 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (X0 ◇ (dr X0 X2)))) := by
    first | exact superpose ef1793 ef37165 | exact superpose ef37165 ef1793
  have ef37420 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((wf X0 (X0 ◇ X1)) ◇ X1)) := by
    first | exact superpose ef6848 ef37308 | exact superpose ef37308 ef6848
  have ef37501 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((X0 ◇ (wf X0 X1)) ◇ X1)) := by
    first | exact superpose ef9101 ef37420 | exact superpose ef37420 ef9101
  have ef37564 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ (dl X1 (dl X2 (wf X0 X1))) := by
    first | exact superpose ef1808 ef37501 | exact superpose ef37501 ef1808
  have ef37612 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ ((dl (wf X0 X1) X1) ◇ X2) := by
    first | exact superpose ef4079 ef37564 | exact superpose ef37564 ef4079
  have ef37901 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dl X3 (X0 ◇ X2)) = (dr X0 X1) ◇ (X4 ◇ (X2 ◇ (dr X3 X1))) := by
    first | exact superpose ef203 ef256 | exact superpose ef256 ef203
  have ef37969 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = dr ((X2 ◇ (dr X5 (dl X0 X1))) ◇ X5) (dl X3 X4) := by
    first | exact superpose ef205 ef256 | exact superpose ef256 ef205
  have ef38120 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X4) ◇ (dr X0 (dl X1 X2)) = (X3 ◇ ((X5 ◇ X1) ◇ X2)) ◇ (X4 ◇ (X0 ◇ X5)) := by
    first | exact superpose ef256 ef138 | exact superpose ef138 ef256
  have ef38121 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X0 (dl X1 X2)) ◇ (X4 ◇ X5) = (((X3 ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X5) := by
    first | exact superpose ef256 ef138 | exact superpose ef138 ef256
  have ef38230 (X0 X1 X2 X3 X4 X5 : G) :
      (((X3 ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X5) = X1 ◇ (dl (dr X0 (X4 ◇ X5)) X2) := by
    first | exact superpose ef29160 ef38121 | exact superpose ef38121 ef29160
  have ef38231 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ X4) ◇ (dr X0 (dl X1 X2)) = X5 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X5 ◇ X1) ◇ X2)))) := by
    first | exact superpose ef957 ef38120 | exact superpose ef38120 ef957
  have ef38370 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = (dl (dl X3 X4) (X5 ◇ X2)) ◇ (dr X5 (dl X0 X1)) := by
    first | exact superpose ef1777 ef37969 | exact superpose ef37969 ef1777
  have ef38563 (X0 X1 X2 X3 X4 X5 : G) :
      (((X3 ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X5) = X1 ◇ (dl ((X5 ◇ X0) ◇ X4) X2) := by
    first | exact superpose ef40 ef38230 | exact superpose ef38230 ef40
  have ef38678 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr (dl X3 X4) (dl X0 X1)) = (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 := by
    first | exact superpose ef1854 ef38370 | exact superpose ef38370 ef1854
  have ef38836 (X0 X1 X2 X3 X4 X5 : G) :
      (((X3 ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X5) = X1 ◇ ((X2 ◇ (dl X0 X4)) ◇ X5) := by
    first | exact superpose ef306 ef38563 | exact superpose ef38563 ef306
  have ef38931 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (dr (dl X0 X1) X3)) := by
    first | exact superpose ef1793 ef38678 | exact superpose ef38678 ef1793
  have ef39045 (X0 X1 X2 X3 X4 X5 : G) :
      (((X3 ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X5) = X1 ◇ (X4 ◇ (dr (X5 ◇ X2) X0)) := by
    first | exact superpose ef5518 ef38836 | exact superpose ef38836 ef5518
  have ef39112 (X0 X1 X2 X3 X4 : G) :
      (((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0 = X2 ◇ (X4 ◇ (X1 ◇ (dr X3 X0))) := by
    first | exact superpose ef1793 ef38931 | exact superpose ef38931 ef1793
  have ef39497 (X0 X1 X2 : G) : (X2 ◇ X1) ◇ (X0 ◇ X1) = dl (wf X1 (dr X1 X0)) X2 := by
    first | exact superpose ef4764 ef30 | exact superpose ef30 ef4764
  have ef39669 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (wf X1 X2)) = (X2 ◇ X1) ◇ (X0 ◇ X1) := by
    first | exact superpose ef27349 ef39497 | exact superpose ef39497 ef27349
  have ef40205 (X0 X1 X2 X3 X4 : G) :
      dr ((X2 ◇ (X3 ◇ X1)) ◇ X0) X4 = dl (X4 ◇ (dl X0 X1)) (dr X2 X3) := by
    first | exact superpose ef287 ef316 | exact superpose ef316 ef287
  have ef40206 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = dl (dl X0 X1) (dl X4 (dr X2 X3)) := by
    first | exact superpose ef287 ef325 | exact superpose ef325 ef287
  have ef40243 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = (dl (dr X2 X3) (dl X0 X1)) ◇ X4 := by
    first | exact superpose ef4079 ef40206 | exact superpose ef40206 ef4079
  have ef40244 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = dr ((X2 ◇ (X3 ◇ X1)) ◇ X0) X4 := by
    first | exact superpose ef129 ef40205 | exact superpose ef40205 ef129
  have ef40517 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ ((dr X4 (dl X0 X1)) ◇ X2) := by
    first | exact superpose ef3523 ef40243 | exact superpose ef40243 ef3523
  have ef40518 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = (dl X4 (X0 ◇ X2)) ◇ (X3 ◇ X1) := by
    first | exact superpose ef1777 ef40244 | exact superpose ef40244 ef1777
  have ef40756 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ (X0 ◇ (dl (dr X4 X2) X1)) := by
    first | exact superpose ef29160 ef40517 | exact superpose ef40517 ef29160
  have ef40757 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr X4 (dl (X3 ◇ X1) X0)) = X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) := by
    first | exact superpose ef7908 ef40518 | exact superpose ef40518 ef7908
  have ef40956 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (dr X4 (X1 ◇ (dr X3 X0))) = X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) := by
    first | exact superpose ef644 ef40757 | exact superpose ef40757 ef644
  have ef41097 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = X2 ◇ (((dr X3 X0) ◇ X4) ◇ X1) := by
    first | exact superpose ef40 ef40956 | exact superpose ef40956 ef40
  have ef41186 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X4 ◇ (dl X0 X1))) = X2 ◇ (X3 ◇ (X0 ◇ (dl X4 X1))) := by
    first | exact superpose ef830 ef41097 | exact superpose ef41097 ef830
  have ef42047 (X0 X1 X2 X3 : G) :
      (wf X0 (X0 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X2) = dl X2 ((dl X0 X1) ◇ X3) := by
    first | exact superpose ef4734 ef291 | exact superpose ef291 ef4734
  have ef42084 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X4 ◇ (dr X0 X2)) ◇ X3) = dl X3 (((dr X0 X1) ◇ X2) ◇ X4) := by
    first | exact superpose ef3631 ef291 | exact superpose ef291 ef3631
  have ef42100 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((X4 ◇ (dl X1 (dl X0 X3))) ◇ X2) := by
    first | exact superpose ef1765 ef291 | exact superpose ef291 ef1765
  have ef42201 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)) = X4 ◇ (dr X3 ((X2 ◇ X0) ◇ X1)) := by
    first | exact superpose ef291 ef644 | exact superpose ef644 ef291
  have ef42217 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X1 ◇ X2) ◇ (wf X3 X4)) = dl (wf X3 ((X2 ◇ X0) ◇ X1)) X4 := by
    first | exact superpose ef291 ef3584 | exact superpose ef3584 ef291
  have ef42229 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)) = X4 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef40 ef42201 | exact superpose ef42201 ef40
  have ef42320 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((dl X0 X3) ◇ (dr (X2 ◇ X4) X1)) := by
    first | exact superpose ef5518 ef42100 | exact superpose ef42100 ef5518
  have ef42335 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X4 ◇ (dr X0 X2)) ◇ X3) = X2 ◇ ((X4 ◇ (dr X0 X1)) ◇ X3) := by
    first | exact superpose ef291 ef42084 | exact superpose ef42084 ef291
  have ef42368 (X0 X1 X2 X3 : G) :
      (wf X0 (X0 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X2) = (dr X3 X1) ◇ (X0 ◇ X2) := by
    first | exact superpose ef3485 ef42047 | exact superpose ef42047 ef3485
  have ef42460 (X0 X1 X2 X4 : G) : dl (dr (X2 ◇ X4) X1) X0 = dl X2 ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef164 ef42320 | exact superpose ef42320 ef164
  have ef42498 (X0 X1 X2 X3 : G) :
      (dr X3 X1) ◇ (X0 ◇ X2) = (X0 ◇ (wf X0 X1)) ◇ ((X3 ◇ X0) ◇ X2) := by
    first | exact superpose ef9101 ef42368 | exact superpose ef42368 ef9101
  have ef43141 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (dl (X0 ◇ X1) X2) := by
    first | exact superpose ef4734 ef292 | exact superpose ef292 ef4734
  have ef43387 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) := by
    first | exact superpose ef644 ef43141 | exact superpose ef43141 ef644
  have ef43629 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (wf (X0 ◇ X1) (X3 ◇ X0))) := by
    first | exact superpose ef42217 ef43387 | exact superpose ef43387 ef42217
  have ef43837 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (wf X1 (dl X3 X0)))) := by
    first | exact superpose ef27224 ef43629 | exact superpose ef43629 ef27224
  have ef43981 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ (dl (wf X1 (dl X3 X0)) X2) := by
    first | exact superpose ef30 ef43837 | exact superpose ef43837 ef30
  have ef44072 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((dl X0 (wf X1 X2)) ◇ X3) := by
    first | exact superpose ef30917 ef43981 | exact superpose ef43981 ef30917
  have ef44329 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X1) ◇ X2) = dl X2 (dr (wf X1 X0) X1) := by
    first | exact superpose ef7378 ef164 | exact superpose ef164 ef7378
  have ef44390 (X0 X1 X2 : G) : (wf X1 X0) ◇ (X1 ◇ X2) = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef129 ef44329 | exact superpose ef44329 ef129
  have ef44842 (X0 X1 X2 X3 : G) :
      dl X3 (((X3 ◇ X1) ◇ X2) ◇ X0) = X3 ◇ (wf X3 (dl X0 (dl X1 X2))) := by
    first | exact superpose ef295 ef4734 | exact superpose ef4734 ef295
  have ef44897 (X0 X1 X2 X3 : G) :
      dl X3 (((X3 ◇ X1) ◇ X2) ◇ X0) = X3 ◇ (wf X3 ((dl X2 X0) ◇ X1)) := by
    first | exact superpose ef4079 ef44842 | exact superpose ef44842 ef4079
  have ef45228 (X0 X1 X2 X3 : G) :
      X3 ◇ (wf X3 ((dl X2 X0) ◇ X1)) = X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X3) := by
    first | exact superpose ef291 ef44897 | exact superpose ef44897 ef291
  have ef46295 (X0 X1 X2 : G) : dl (wf (X0 ◇ X1) X2) X2 = (X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    first | exact superpose ef138 ef7544 | exact superpose ef7544 ef138
  have ef46365 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (((X0 ◇ X0) ◇ (dl (wf X0 X1) X1)) ◇ X0) ◇
      X2 := by
    first | exact superpose ef7544 ef99 | exact superpose ef99 ef7544
  have ef46594 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (X1 ◇ X0) ◇
      ((dr X2 (X0 ◇ X0)) ◇ (wf X0 X1)) := by
    first | exact superpose ef3533 ef46365 | exact superpose ef46365 ef3533
  have ef46643 (X0 X1 X2 : G) : dl (wf (X0 ◇ X1) X2) X2 = X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef42229 ef46295 | exact superpose ef46295 ef42229
  have ef46727 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 (X0 ◇ X0)) (dr X0 X0) := by
    first | exact superpose ef106 ef46594 | exact superpose ef46594 ef106
  have ef46765 (X0 X1 X2 : G) : dl (wf (X0 ◇ X1) X2) X2 = X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    first | exact superpose ef24549 ef46643 | exact superpose ef46643 ef24549
  have ef46833 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef105 ef46727 | exact superpose ef46727 ef105
  have ef46859 (X0 X1 X2 : G) : (wf X1 X0) ◇ (dr X0 X0) = dl (wf (X0 ◇ X1) X2) X2 := by
    first | exact superpose ef14444 ef46765 | exact superpose ef46765 ef14444
  have ef46914 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef33861 ef46833 | exact superpose ef46833 ef33861
  have ef46968 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 X0) X0 := by
    first | exact superpose ef23 ef46914 | exact superpose ef46914 ef23
  have ef47007 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) := by
    first | exact superpose ef1781 ef46968 | exact superpose ef46968 ef1781
  have ef47035 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) ((dr X0 X0) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef470 ef47007 | exact superpose ef47007 ef470
  have ef47056 (X0 X1 X2 : G) : (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (wf X0 X2) := by
    first | exact superpose ef19 ef47035 | exact superpose ef47035 ef19
  have ef47292 (X0 X1 X2 X3 X4 X5 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (dr X4 X5) = X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) := by
    first | exact superpose ef298 ef291 | exact superpose ef291 ef298
  have ef47303 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) = X1 ◇ (X3 ◇ (X0 ◇ (dr X2 (dr X4 X5)))) := by
    first | exact superpose ef39112 ef47292 | exact superpose ef47292 ef39112
  have ef47475 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X5 ◇ X3))) = X1 ◇ (X3 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X4)))) := by
    first | exact superpose ef105 ef47303 | exact superpose ef47303 ef105
  have ef48107 (X0 X1 X2 X3 X4 : G) :
      dl X4 ((X0 ◇ X1) ◇ (X2 ◇ X3)) = dl (X0 ◇ X2) (X4 ◇ (X1 ◇ X3)) := by
    first | exact superpose ef138 ef7612 | exact superpose ef7612 ef138
  have ef48406 (X0 X1 X2 X3 X4 : G) :
      dl X4 ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X1 ◇ ((dr X3 X4) ◇ (X0 ◇ X2)) := by
    first | exact superpose ef460 ef48107 | exact superpose ef48107 ef460
  have ef48606 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4) = X1 ◇ ((dr X3 X4) ◇ (X0 ◇ X2)) := by
    first | exact superpose ef291 ef48406 | exact superpose ef48406 ef291
  have ef49042 (X0 X1 X2 X3 X4 X5 : G) :
      (X5 ◇ (dl X0 (dl X1 X2))) ◇ X4 = dl (((((X3 ◇ X4) ◇ X1) ◇ X2) ◇ X0) ◇ X3) X5 := by
    first | exact superpose ef295 ef302 | exact superpose ef302 ef295
  have ef49530 (X0 X1 X2 X3 X4 X5 : G) :
      (X5 ◇ (dl X0 (dl X1 X2))) ◇ X4 = (X5 ◇ (dl X0 X3)) ◇ (((X3 ◇ X4) ◇ X1) ◇ X2) := by
    first | exact superpose ef306 ef49042 | exact superpose ef49042 ef306
  have ef49833 (X0 X1 X2 X3 X4 X5 : G) :
      (X5 ◇ (dl X0 (dl X1 X2))) ◇ X4 = X3 ◇ ((((X5 ◇ (dl X0 X3)) ◇ X4) ◇ X1) ◇ X2) := by
    first | exact superpose ef2066 ef49530 | exact superpose ef49530 ef2066
  have ef50072 (X0 X1 X2 X3 X4 X5 : G) :
      (X5 ◇ (dl X0 (dl X1 X2))) ◇ X4 = X3 ◇ ((dl X0 X3) ◇ (X1 ◇ (X5 ◇ (dr X4 X2)))) := by
    first | exact superpose ef39112 ef49833 | exact superpose ef49833 ef39112
  have ef50258 (X0 X1 X2 X4 X5 : G) :
      (X5 ◇ (dl X0 (dl X1 X2))) ◇ X4 = dl (X1 ◇ (X5 ◇ (dr X4 X2))) X0 := by
    first | exact superpose ef164 ef50072 | exact superpose ef50072 ef164
  have ef50395 (X0 X1 X2 X4 X5 : G) :
      (X5 ◇ (dl X0 (dl X1 X2))) ◇ X4 = (X5 ◇ (dr X4 X2)) ◇ (dr X1 X0) := by
    first | exact superpose ef644 ef50258 | exact superpose ef50258 ef644
  have ef50487 (X0 X1 X2 X4 X5 : G) :
      (X5 ◇ (dr X4 X2)) ◇ (dr X1 X0) = (dl X1 X2) ◇ (dr (X4 ◇ X5) X0) := by
    first | exact superpose ef5518 ef50395 | exact superpose ef50395 ef5518
  have ef53235 (X0 X1 X2 X3 : G) :
      dl X3 (wf X1 X0) = (dl (dl (X0 ◇ X1) X2) X3) ◇ (X2 ◇ (dr X1 X1)) := by
    first | exact superpose ef305 ef538 | exact superpose ef538 ef305
  have ef53310 (X0 X1 X2 X3 : G) :
      dl X3 (wf X1 X0) = (X1 ◇ X2) ◇ (dl (dl (dl (X0 ◇ X1) X2) X3) X1) := by
    first | exact superpose ef3564 ef53235 | exact superpose ef53235 ef3564
  have ef53474 (X0 X1 X2 X3 : G) :
      dl X3 (wf X1 X0) = (X1 ◇ X2) ◇ ((X1 ◇ (dl (X0 ◇ X1) X2)) ◇ X3) := by
    first | exact superpose ef254 ef53310 | exact superpose ef53310 ef254
  have ef53625 (X0 X1 X2 X3 : G) :
      dl X3 (wf X1 X0) = (X1 ◇ X2) ◇ (X2 ◇ (dr (X3 ◇ X1) (X0 ◇ X1))) := by
    first | exact superpose ef5518 ef53474 | exact superpose ef53474 ef5518
  have ef53745 (X0 X1 X3 : G) : dl X3 (wf X1 X0) = dl (dr (X3 ◇ X1) (X0 ◇ X1)) X1 := by
    first | exact superpose ef30 ef53625 | exact superpose ef53625 ef30
  have ef53831 (X0 X1 X3 : G) : dl X3 (wf X1 X0) = dl (dr X1 (X0 ◇ X1)) (X3 ◇ X1) := by
    first | exact superpose ef7639 ef53745 | exact superpose ef53745 ef7639
  have ef53897 (X0 X1 X3 : G) : dl X3 (wf X1 X0) = dl ((X1 ◇ X1) ◇ X0) (X3 ◇ X1) := by
    first | exact superpose ef40 ef53831 | exact superpose ef53831 ef40
  have ef53941 (X0 X1 X3 : G) : dl X3 (wf X1 X0) = ((X3 ◇ X1) ◇ (dl X1 X0)) ◇ X1 := by
    first | exact superpose ef306 ef53897 | exact superpose ef53897 ef306
  have ef53976 (X0 X1 X3 : G) : dl X3 (wf X1 X0) = (dr X1 X1) ◇ ((dl X1 X0) ◇ X3) := by
    first | exact superpose ef470 ef53941 | exact superpose ef53941 ef470
  have ef54424 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ (dl (((X4 ◇ X1) ◇ X2) ◇ X0) X5)) ◇ X4 = dl ((dl X0 (dl X1 X2)) ◇ X5) X3 := by
    first | exact superpose ef295 ef306 | exact superpose ef306 ef295
  have ef54448 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ (dl X1 X3)) ◇ (((X4 ◇ X0) ◇ (dl X0 X1)) ◇ (X1 ◇ X4)) =
      dl ((wf (dl X0 X1) X0) ◇ X3) X2 := by
    first | exact superpose ef104 ef306 | exact superpose ef306 ef104
  have ef54450 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ (dl X4 X5)) ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X1) = dl ((X0 ◇ (X1 ◇ X2)) ◇ X5) X3 := by
    first | exact superpose ef139 ef306 | exact superpose ef306 ef139
  have ef54797 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ (dl X4 X5)) ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X1) = (X3 ◇ (dl (X1 ◇ X2) X5)) ◇ X0 := by
    first | exact superpose ef306 ef54450 | exact superpose ef54450 ef306
  have ef54799 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ (dl X1 X3)) ◇ (((X4 ◇ X0) ◇ (dl X0 X1)) ◇ (X1 ◇ X4)) = X3 ◇
      (dr (wf (dl X0 X1) X0) X2) := by
    first | exact superpose ef644 ef54448 | exact superpose ef54448 ef644
  have ef54823 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ (dl (((X4 ◇ X1) ◇ X2) ◇ X0) X5)) ◇ X4 = X5 ◇ (dr (dl X0 (dl X1 X2)) X3) := by
    first | exact superpose ef644 ef54424 | exact superpose ef54424 ef644
  have ef54984 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ (dl X4 X5)) ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X1) = X5 ◇ (dr (X0 ◇ X3) (X1 ◇ X2)) := by
    first | exact superpose ef5518 ef54797 | exact superpose ef54797 ef5518
  have ef54986 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = (X2 ◇ (dl X1 X3)) ◇
      (((X4 ◇ X0) ◇ X1) ◇ ((dl X0 X1) ◇ X4)) := by
    first | exact superpose ef28567 ef54799 | exact superpose ef54799 ef28567
  have ef55010 (X0 X1 X2 X3 X4 X5 : G) :
      (X3 ◇ (dl (((X4 ◇ X1) ◇ X2) ◇ X0) X5)) ◇ X4 = X5 ◇ ((dl X1 X2) ◇ (dr X3 X0)) := by
    first | exact superpose ef1793 ef54823 | exact superpose ef54823 ef1793
  have ef55141 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = (X3 ◇ (dl X4 X5)) ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X1) := by
    first | exact superpose ef40 ef54984 | exact superpose ef54984 ef40
  have ef55143 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇
      (dr ((((X4 ◇ X0) ◇ X1) ◇ ((dl X0 X1) ◇ X4)) ◇ X2) X1) := by
    first | exact superpose ef5518 ef54986 | exact superpose ef54986 ef5518
  have ef55166 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ ((dl X1 X2) ◇ (dr X3 X0)) = X5 ◇ (dr (X4 ◇ X3) (((X4 ◇ X1) ◇ X2) ◇ X0)) := by
    first | exact superpose ef5518 ef55010 | exact superpose ef55010 ef5518
  have ef55266 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = X5 ◇ (dr (((X2 ◇ (X0 ◇ X4)) ◇ X1) ◇ X3) X4) := by
    first | exact superpose ef5518 ef55141 | exact superpose ef55141 ef5518
  have ef55268 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇
      ((dl X1 (X2 ◇ ((X4 ◇ X0) ◇ X1))) ◇ ((dl X0 X1) ◇ X4)) := by
    first | exact superpose ef1777 ef55143 | exact superpose ef55143 ef1777
  have ef55287 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ ((dl X1 X2) ◇ (dr X3 X0)) = X5 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X2)) := by
    first | exact superpose ef40 ef55166 | exact superpose ef55166 ef40
  have ef55358 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = X5 ◇ ((dl X4 (X3 ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X1) := by
    first | exact superpose ef1777 ef55266 | exact superpose ef55266 ef1777
  have ef55360 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇
      (X1 ◇ ((dl X0 (dl X1 (X2 ◇ ((X4 ◇ X0) ◇ X1)))) ◇ X4)) := by
    first | exact superpose ef5528 ef55268 | exact superpose ef55268 ef5528
  have ef55371 (X0 X1 X2 X3 X5 : G) :
      X5 ◇ ((dl X1 X2) ◇ (dr X3 X0)) = X5 ◇ ((dl X3 X2) ◇ (dr X1 X0)) := by
    first | exact superpose ef20568 ef55287 | exact superpose ef55287 ef20568
  have ef55422 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = X5 ◇ ((X2 ◇ (X0 ◇ X4)) ◇ (dr X4 (dl X1 X3))) := by
    first | exact superpose ef7908 ef55358 | exact superpose ef55358 ef7908
  have ef55424 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇
      (X1 ◇ (((dl X4 X0) ◇ X1) ◇ (X2 ◇ ((X4 ◇ X0) ◇ X1)))) := by
    first | exact superpose ef4114 ef55360 | exact superpose ef55360 ef4114
  have ef55461 (X0 X1 X2 X3 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = X5 ◇ (dl (dr (dl X1 X3) X0) X2) := by
    first | exact superpose ef2595 ef55422 | exact superpose ef55422 ef2595
  have ef55462 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇
      (X1 ◇ (X1 ◇ (X1 ◇ ((X4 ◇ X0) ◇ ((dl X4 X0) ◇ X2))))) := by
    first | exact superpose ef47475 ef55424 | exact superpose ef55424 ef47475
  have ef55485 (X0 X1 X2 X3 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = X5 ◇ (dl (X3 ◇ (dr X0 X1)) X2) := by
    first | exact superpose ef1793 ef55461 | exact superpose ef55461 ef1793
  have ef55486 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇ ((wf X1 X0) ◇ (((dl X4 X0) ◇ X2) ◇ X4)) := by
    first | exact superpose ef3919 ef55462 | exact superpose ef55462 ef3919
  have ef55503 (X0 X1 X2 X3 X5 : G) :
      X5 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1) = X5 ◇ ((dr X0 X1) ◇ (dr X3 X2)) := by
    first | exact superpose ef644 ef55485 | exact superpose ef55485 ef644
  have ef55504 (X0 X1 X2 X3 : G) :
      X3 ◇ (dr (wf (dl X0 X1) X0) X2) = X3 ◇ ((wf X1 X0) ◇ (dr X2 X0)) := by
    first | exact superpose ef156 ef55486 | exact superpose ef55486 ef156
  have ef58539 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ (dl ((X2 ◇ X3) ◇ X1) X5)) := by
    first | exact superpose ef70 ef333 | exact superpose ef333 ef70
  have ef58664 (X0 X1 X2 : G) :
      wf (dl X0 X1) X0 = ((((dl (dl X0 X1) X2) ◇ X0) ◇ X1) ◇ X2) ◇ X1 := by
    first | exact superpose ef333 ef104 | exact superpose ef104 ef333
  have ef58983 (X0 X1 X2 : G) :
      wf (dl X0 X1) X0 = (dr X1 X1) ◇ (X2 ◇ ((dl (dl X0 X1) X2) ◇ X0)) := by
    first | exact superpose ef470 ef58664 | exact superpose ef58664 ef470
  have ef59081 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ ((X5 ◇ (dl X3 X1)) ◇ X2)) := by
    first | exact superpose ef306 ef58539 | exact superpose ef58539 ef306
  have ef59253 (X0 X1 : G) : wf (dl X0 X1) X0 = (dr X1 X1) ◇ (dl X0 (dl X0 X1)) := by
    first | exact superpose ef164 ef58983 | exact superpose ef58983 ef164
  have ef59331 (X0 X1 X2 X3 X4 X5 : G) :
      (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5 = X0 ◇ (X4 ◇ (X1 ◇ (dr (X2 ◇ X5) X3))) := by
    first | exact superpose ef5518 ef59081 | exact superpose ef59081 ef5518
  have ef59470 (X0 X1 : G) : wf (dl X0 X1) X0 = (dr X1 X1) ◇ ((dl X1 X0) ◇ X0) := by
    first | exact superpose ef4079 ef59253 | exact superpose ef59253 ef4079
  have ef59521 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ (X1 ◇ (dr (X2 ◇ X5) X3))) = X0 ◇ (X4 ◇ (dl (dr X5 (X1 ◇ X2)) X3)) := by
    first | exact superpose ef40756 ef59331 | exact superpose ef59331 ef40756
  have ef59626 (X0 X1 : G) : wf (dl X0 X1) X0 = dl X0 (wf X1 X0) := by
    first | exact superpose ef53976 ef59470 | exact superpose ef59470 ef53976
  have ef59656 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ (X1 ◇ (dr (X2 ◇ X5) X3))) = X0 ◇ (X4 ◇ (dl ((X2 ◇ X5) ◇ X1) X3)) := by
    first | exact superpose ef40 ef59521 | exact superpose ef59521 ef40
  have ef59748 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ (X1 ◇ (dr (X2 ◇ X5) X3))) = X0 ◇ (X4 ◇ ((X3 ◇ (dl X5 X1)) ◇ X2)) := by
    first | exact superpose ef306 ef59656 | exact superpose ef59656 ef306
  have ef59818 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X4 ◇ (X1 ◇ (dr (X2 ◇ X5) X3))) = X0 ◇ (X4 ◇ (X1 ◇ (dr (X2 ◇ X3) X5))) := by
    first | exact superpose ef5518 ef59748 | exact superpose ef59748 ef5518
  have ef60635 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (X3 ◇ ((((X4 ◇ X3) ◇ X1) ◇ X2) ◇ X0)) = (wf X3 X4) ◇ (dl X0 (dl X1 X2)) := by
    first | exact superpose ef295 ef349 | exact superpose ef349 ef295
  have ef60751 (X0 X1 X2 X3 : G) :
      ((X2 ◇ X0) ◇ X1) ◇ X3 = dl (X0 ◇ (X0 ◇ X1)) (dl X3 (wf X0 X2)) := by
    first | exact superpose ef349 ef325 | exact superpose ef325 ef349
  have ef60794 (X0 X1 X2 X3 : G) :
      ((X2 ◇ X0) ◇ X1) ◇ X3 = (dl (wf X0 X2) (X0 ◇ (X0 ◇ X1))) ◇ X3 := by
    first | exact superpose ef4079 ef60751 | exact superpose ef60751 ef4079
  have ef60903 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (X3 ◇ ((((X4 ◇ X3) ◇ X1) ◇ X2) ◇ X0)) = (wf X3 X4) ◇ ((dl X2 X0) ◇ X1) := by
    first | exact superpose ef4079 ef60635 | exact superpose ef60635 ef4079
  have ef61035 (X0 X1 X2 X3 : G) :
      ((X2 ◇ X0) ◇ X1) ◇ X3 = (dl X0 ((wf X0 X2) ◇ (X0 ◇ X1))) ◇ X3 := by
    first | exact superpose ef7616 ef60794 | exact superpose ef60794 ef7616
  have ef61129 (X0 X1 X2 X3 X4 : G) :
      (wf X3 X4) ◇ ((dl X2 X0) ◇ X1) = X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X4 ◇ (dr X1 X0))))) := by
    first | exact superpose ef39112 ef60903 | exact superpose ef60903 ef39112
  have ef61233 (X0 X1 X2 X3 : G) :
      ((X2 ◇ X0) ◇ X1) ◇ X3 = (X0 ◇ X1) ◇ (dr X0 (dl X3 (wf X0 X2))) := by
    first | exact superpose ef7908 ef61035 | exact superpose ef61035 ef7908
  have ef62940 (X0 X1 X2 X3 X4 : G) :
      (dl X1 (X2 ◇ (X3 ◇ X4))) ◇ X0 = dr ((dr X4 X2) ◇ (X0 ◇ X3)) X1 := by
    first | exact superpose ef452 ef107 | exact superpose ef107 ef452
  have ef63098 (X0 X1 X2 X3 X4 : G) :
      (dl X1 (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X3 ◇ ((dr X4 X2) ◇ X1)) ◇ X0 := by
    first | exact superpose ef1857 ef62940 | exact superpose ef62940 ef1857
  have ef63489 (X0 X1 X2 X3 X4 : G) :
      (X3 ◇ X4) ◇ (dr X1 (dl X0 X2)) = (X3 ◇ ((dr X4 X2) ◇ X1)) ◇ X0 := by
    first | exact superpose ef7908 ef63098 | exact superpose ef63098 ef7908
  have ef65428 (X0 X1 X2 X3 X4 : G) :
      dl X4 (X0 ◇ ((dr X1 X2) ◇ X3)) = (dl (X2 ◇ (X0 ◇ X1)) X4) ◇ X3 := by
    first | exact superpose ef460 ef4079 | exact superpose ef4079 ef460
  have ef65484 (X0 X1 X2 X3 X4 : G) :
      dl X4 (X0 ◇ ((dr X1 X2) ◇ X3)) = ((X0 ◇ X1) ◇ (dr X2 X4)) ◇ X3 := by
    first | exact superpose ef644 ef65428 | exact superpose ef65428 ef644
  have ef65693 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ X1) ◇ (dr X2 X4)) ◇ X3 = (dr X1 X2) ◇ ((dr X3 X0) ◇ X4) := by
    first | exact superpose ef460 ef65484 | exact superpose ef65484 ef460
  have ef66208 (X0 X1 X2 X3 : G) : (wf X2 X0) ◇ X1 = (dr X0 X1) ◇ (dl (wf X2 X3) X3) := by
    first | exact superpose ef2725 ef8263 | exact superpose ef8263 ef2725
  have ef66642 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = (X5 ◇ (X4 ◇ (dr X0 X1))) ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef109 ef461 | exact superpose ef461 ef109
  have ef66851 (X0 X1 X2 X3 X4 : G) :
      (dl X3 X4) ◇ (dl (dr X0 X1) X2) = dr (X2 ◇ (X1 ◇ (X4 ◇ X0))) X3 := by
    first | exact superpose ef461 ef107 | exact superpose ef107 ef461
  have ef67148 (X0 X1 X2 X3 X4 : G) :
      (dl X3 X4) ◇ (dl (dr X0 X1) X2) = ((X4 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1 := by
    first | exact superpose ef1857 ef66851 | exact superpose ef66851 ef1857
  have ef67346 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) := by
    first | exact superpose ef957 ef66642 | exact superpose ef66642 ef957
  have ef67702 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = dl X0 ((dr X5 X4) ◇ (dr X2 X3)) := by
    first | exact superpose ef42460 ef67346 | exact superpose ef67346 ef42460
  have ef67994 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (dl X3 (dr X5 X4)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef5478 ef67702 | exact superpose ef67702 ef5478
  have ef68236 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (X5 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef129 ef67994 | exact superpose ef67994 ef129
  have ef69354 (X0 X1 X2 X3 X4 : G) :
      (dr (X0 ◇ X1) X2) ◇ (X3 ◇ X4) = ((X4 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1 := by
    first | exact superpose ef1903 ef470 | exact superpose ef470 ef1903
  have ef69488 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = (((dr X0 X1) ◇ (X2 ◇ X3)) ◇ X5) ◇ X4 := by
    first | exact superpose ef470 ef470
  have ef69521 (X0 X1 X2 X3 X4 X5 : G) :
      (dr (X2 ◇ X0) X4) ◇ (X5 ◇ (dr X1 X3)) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X5) ◇ X4 := by
    first | exact superpose ef470 ef470
  have ef70418 (X0 X1 X2 X3 X4 X5 : G) :
      (dr (X2 ◇ X0) X4) ◇ (X5 ◇ (dr X1 X3)) = X2 ◇ (X5 ◇ ((X0 ◇ X1) ◇ (dr X3 X4))) := by
    first | exact superpose ef39112 ef69521 | exact superpose ef69521 ef39112
  have ef70449 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (dr X4 (dr X0 X1)) X3)) := by
    first | exact superpose ef40756 ef69488 | exact superpose ef69488 ef40756
  have ef70571 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ (X3 ◇ (dl (dr X1 X4) X2)) = (dr (X0 ◇ X1) X2) ◇ (X3 ◇ X4) := by
    first | exact superpose ef40756 ef69354 | exact superpose ef69354 ef40756
  have ef70975 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (X1 ◇ (X4 ◇ X0)) X3)) := by
    first | exact superpose ef105 ef70449 | exact superpose ef70449 ef105
  have ef71379 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ ((X4 ◇ X0) ◇ (dr X1 X3))) := by
    first | exact superpose ef644 ef70975 | exact superpose ef70975 ef644
  have ef74400 (X0 X1 X2 X3 X4 X5 : G) :
      ((((X1 ◇ (dl X0 X2)) ◇ X3) ◇ X4) ◇ X5) ◇ X0 = dr X5 (dl X4 ((X3 ◇ X1) ◇ X2)) := by
    first | exact superpose ef180 ef605 | exact superpose ef605 ef180
  have ef74594 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X0 (dl X1 X2)) ◇ (X4 ◇ X5) = (((X3 ◇ X1) ◇ X0) ◇ X4) ◇ ((X2 ◇ X3) ◇ X5) := by
    first | exact superpose ef605 ef138 | exact superpose ef138 ef605
  have ef74781 (X0 X1 X2 X4 X5 : G) :
      (dr X0 (dl X1 X2)) ◇ (X4 ◇ X5) = X1 ◇ (X4 ◇ (dr (X5 ◇ X0) X2)) := by
    first | exact superpose ef39045 ef74594 | exact superpose ef74594 ef39045
  have ef74960 (X0 X1 X2 X3 X4 X5 : G) :
      ((((X1 ◇ (dl X0 X2)) ◇ X3) ◇ X4) ◇ X5) ◇ X0 = dr X5 (X1 ◇ ((X2 ◇ X3) ◇ X4)) := by
    first | exact superpose ef291 ef74400 | exact superpose ef74400 ef291
  have ef75228 (X0 X1 X2 X4 X5 : G) :
      X1 ◇ (dl (dr X0 (X4 ◇ X5)) X2) = X1 ◇ (X4 ◇ (dr (X5 ◇ X0) X2)) := by
    first | exact superpose ef29160 ef74781 | exact superpose ef74781 ef29160
  have ef75382 (X0 X1 X2 X3 X4 X5 : G) :
      ((((X1 ◇ (dl X0 X2)) ◇ X3) ◇ X4) ◇ X5) ◇ X0 = (((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X1 := by
    first | exact superpose ef40 ef74960 | exact superpose ef74960 ef40
  have ef75613 (X0 X1 X2 X4 X5 : G) :
      X1 ◇ (dl ((X5 ◇ X0) ◇ X4) X2) = X1 ◇ (X4 ◇ (dr (X5 ◇ X0) X2)) := by
    first | exact superpose ef40 ef75228 | exact superpose ef75228 ef40
  have ef75743 (X0 X1 X2 X3 X4 X5 : G) :
      ((((X1 ◇ (dl X0 X2)) ◇ X3) ◇ X4) ◇ X5) ◇ X0 = X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) := by
    first | exact superpose ef39112 ef75382 | exact superpose ef75382 ef39112
  have ef75919 (X0 X1 X2 X4 X5 : G) :
      X1 ◇ ((X2 ◇ (dl X0 X4)) ◇ X5) = X1 ◇ (X4 ◇ (dr (X5 ◇ X0) X2)) := by
    first | exact superpose ef306 ef75613 | exact superpose ef75613 ef306
  have ef76031 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X4 X0) ◇ (X5 ◇ ((X1 ◇ (dl X0 X2)) ◇ X3)) = X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) := by
    first | exact superpose ef470 ef75743 | exact superpose ef75743 ef470
  have ef76162 (X0 X1 X2 X4 X5 : G) :
      X1 ◇ (X4 ◇ (dr (X5 ◇ X2) X0)) = X1 ◇ (X4 ◇ (dr (X5 ◇ X0) X2)) := by
    first | exact superpose ef5518 ef75919 | exact superpose ef75919 ef5518
  have ef76245 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X4 X0) ◇ (X5 ◇ (X2 ◇ (dr (X3 ◇ X1) X0))) = X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) := by
    first | exact superpose ef5518 ef76031 | exact superpose ef76031 ef5518
  have ef76392 (X1 X2 X3 X4 X5 : G) :
      dr X5 (dl (X3 ◇ X1) (X4 ◇ X2)) = X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) := by
    first | exact superpose ef37901 ef76245 | exact superpose ef76245 ef37901
  have ef76485 (X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) = dr X5 (X1 ◇ (dr X3 (X4 ◇ X2))) := by
    first | exact superpose ef644 ef76392 | exact superpose ef76392 ef644
  have ef76549 (X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) = ((dr X3 (X4 ◇ X2)) ◇ X5) ◇ X1 := by
    first | exact superpose ef40 ef76485 | exact superpose ef76485 ef40
  have ef76589 (X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X5 ◇ (X2 ◇ (dr X4 X1))) = X3 ◇ ((X4 ◇ X2) ◇ (dl X5 X1)) := by
    first | exact superpose ef830 ef76549 | exact superpose ef76549 ef830
  have ef76676 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (wf X0 (X0 ◇ X1))) := by
    first | exact superpose ef4734 ef9101 | exact superpose ef9101 ef4734
  have ef76873 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (X0 ◇ (wf X0 X1))) := by
    first | exact superpose ef9101 ef76676 | exact superpose ef76676 ef9101
  have ef76956 (X0 X1 : G) : wf X0 (dl X0 X1) = dl X0 (wf X0 X1) := by
    first | exact superpose ef4734 ef76873 | exact superpose ef76873 ef4734
  have ef81991 (X0 X1 X2 : G) : (dl (X0 ◇ X1) X2) ◇ X1 = dl ((wf (X0 ◇ X1) X2) ◇ X0) (X0 ◇ X1) := by
    first | exact superpose ef9399 ef302 | exact superpose ef302 ef9399
  have ef82284 (X0 X1 X2 : G) : (dl (X0 ◇ X1) X2) ◇ X1 = dl X0 (((wf (X0 ◇ X1) X2) ◇ X0) ◇ X1) := by
    first | exact superpose ef7612 ef81991 | exact superpose ef81991 ef7612
  have ef82440 (X0 X1 X2 : G) : (dl (X0 ◇ X1) X2) ◇ X1 = X0 ◇ ((X1 ◇ (wf (X0 ◇ X1) X2)) ◇ X0) := by
    first | exact superpose ef291 ef82284 | exact superpose ef82284 ef291
  have ef82562 (X0 X1 X2 : G) : (X1 ◇ (dr X0 X2)) ◇ X1 = X0 ◇ ((X1 ◇ (wf (X0 ◇ X1) X2)) ◇ X0) := by
    first | exact superpose ef644 ef82440 | exact superpose ef82440 ef644
  have ef82892 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) (((dl X0 X1) ◇ X2) ◇ (dr (dl X0 X1) X1)) =
      (((dl X0 X1) ◇ (wf (dl X0 X1) X0)) ◇ (dr (dl X0 X1) X1)) ◇ X2 := by
    first | exact superpose ef721 ef99 | exact superpose ef99 ef721
  have ef83051 (X0 X1 X2 : G) :
      ((X1 ◇ (wf (dl X0 X1) X0)) ◇ (dr (dl X0 X1) (dl X0 X1))) ◇ X2 =
      wf (wf (dl X0 X1) X0) (((dl X0 X1) ◇ X2) ◇ (dr (dl X0 X1) X1)) := by
    first | exact superpose ef16568 ef82892 | exact superpose ef82892 ef16568
  have ef83204 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) =
      ((X1 ◇ (wf (dl X0 X1) X0)) ◇ (dr (dl X0 X1) (dl X0 X1))) ◇ X2 := by
    first | exact superpose ef13311 ef83051 | exact superpose ef83051 ef13311
  have ef83344 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) =
      (dr (wf (dl X0 X1) X0) (dl X0 X1)) ◇ ((dr X2 X1) ◇ (dl X0 X1)) := by
    first | exact superpose ef65693 ef83204 | exact superpose ef83204 ef65693
  have ef83467 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) = (dl X0 X1) ◇
      (wf (dl X0 X1) (dl (wf (dl X0 X1) X0) (dr X2 X1))) := by
    first | exact superpose ef8111 ef83344 | exact superpose ef83344 ef8111
  have ef83558 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) =
      dr X0 (dl (dl X0 X1) (dr X2 X1)) := by
    first | exact superpose ef11751 ef83467 | exact superpose ef83467 ef11751
  have ef83633 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) =
      dr X0 (X2 ◇ (X1 ◇ (dl X0 X1))) := by
    first | exact superpose ef129 ef83558 | exact superpose ef83558 ef129
  have ef83694 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) = ((X1 ◇ (dl X0 X1)) ◇ X0) ◇
      X2 := by
    first | exact superpose ef40 ef83633 | exact superpose ef83633 ef40
  have ef83745 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) = (X1 ◇ X0) ◇
      ((dr X2 X1) ◇ X0) := by
    first | exact superpose ef3533 ef83694 | exact superpose ef83694 ef3533
  have ef83786 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr (dl X0 X1) (dl X0 X1))) = X0 ◇
      ((dr X2 X1) ◇ (wf X0 X1)) := by
    first | exact superpose ef39669 ef83745 | exact superpose ef83745 ef39669
  have ef83819 (X0 X1 X2 : G) :
      X0 ◇ ((dr X2 X1) ◇ (wf X0 X1)) =
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr X1 (dl X0 (dl X0 X1)))) := by
    first | exact superpose ef32326 ef83786 | exact superpose ef83786 ef32326
  have ef83849 (X0 X1 X2 : G) :
      X0 ◇ ((dr X2 X1) ◇ (wf X0 X1)) =
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (dr X1 ((dl X1 X0) ◇ X0))) := by
    first | exact superpose ef4079 ef83819 | exact superpose ef83819 ef4079
  have ef83875 (X0 X1 X2 : G) :
      X0 ◇ ((dr X2 X1) ◇ (wf X0 X1)) =
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (dl X1 X0))) := by
    first | exact superpose ef40 ef83849 | exact superpose ef83849 ef40
  have ef83896 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (dr X0 X0)))) = X0 ◇
      ((dr X2 X1) ◇ (wf X0 X1)) := by
    first | exact superpose ef76589 ef83875 | exact superpose ef83875 ef76589
  have ef83912 (X0 X1 X2 : G) :
      wf (wf (dl X0 X1) X0) (dr X2 (wf (dl X0 X1) X0)) = X0 ◇ ((dr X2 X1) ◇ (wf X0 X1)) := by
    first | exact superpose ef2499 ef83896 | exact superpose ef83896 ef2499
  have ef83926 (X0 X1 X2 : G) :
      (dr (wf (dl X0 X1) X0) (wf (dl X0 X1) X0)) ◇ X2 = X0 ◇ ((dr X2 X1) ◇ (wf X0 X1)) := by
    first | exact superpose ef82 ef83912 | exact superpose ef83912 ef82
  have ef84305 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X4 ◇ (((X5 ◇ X1) ◇ X2) ◇ X0)) = ((dr X3 X5) ◇ X4) ◇ (dl X0 (dl X1 X2)) := by
    first | exact superpose ef295 ef781 | exact superpose ef781 ef295
  have ef84474 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X2) ((dr X0 X3) ◇ X1) = (dr (X3 ◇ X2) (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef781 ef19 | exact superpose ef19 ef781
  have ef84736 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X2) ((dr X0 X3) ◇ X1) = X3 ◇ (X0 ◇ (dl (dr X2 (X1 ◇ X2)) (X3 ◇ X2))) := by
    first | exact superpose ef70571 ef84474 | exact superpose ef84474 ef70571
  have ef84897 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X4 ◇ (((X5 ◇ X1) ◇ X2) ◇ X0)) = X3 ◇ (X5 ◇ (dl X4 (dl X0 (dl X1 X2)))) := by
    first | exact superpose ef830 ef84305 | exact superpose ef84305 ef830
  have ef85064 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X2) ((dr X0 X3) ◇ X1) = X3 ◇ (X0 ◇ (dl ((X2 ◇ X2) ◇ X1) (X3 ◇ X2))) := by
    first | exact superpose ef40 ef84736 | exact superpose ef84736 ef40
  have ef85186 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X4 ◇ (((X5 ◇ X1) ◇ X2) ◇ X0)) = X3 ◇ (X5 ◇ ((dl (dl X1 X2) X4) ◇ X0)) := by
    first | exact superpose ef4079 ef84897 | exact superpose ef84897 ef4079
  have ef85330 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X2) ((dr X0 X3) ◇ X1) = X3 ◇ (X0 ◇ (((X3 ◇ X2) ◇ (dl X2 X1)) ◇ X2)) := by
    first | exact superpose ef306 ef85064 | exact superpose ef85064 ef306
  have ef85403 (X0 X1 X2 X3 X4 X5 : G) :
      X3 ◇ (X4 ◇ (((X5 ◇ X1) ◇ X2) ◇ X0)) = X3 ◇ (X5 ◇ (((X4 ◇ X1) ◇ X2) ◇ X0)) := by
    first | exact superpose ef254 ef85186 | exact superpose ef85186 ef254
  have ef85509 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X2) ((dr X0 X3) ◇ X1) = X3 ◇ (X0 ◇ ((dr X2 X2) ◇ ((dl X2 X1) ◇ X3))) := by
    first | exact superpose ef48606 ef85330 | exact superpose ef85330 ef48606
  have ef85634 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X2) ((dr X0 X3) ◇ X1) = X3 ◇ (X0 ◇ (dl X3 (wf X2 X1))) := by
    first | exact superpose ef53976 ef85509 | exact superpose ef85509 ef53976
  have ef89036 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X1) ◇ (wf (X3 ◇ X1) ((dl X3 X0) ◇ X2)) := by
    first | exact superpose ef881 ef9101 | exact superpose ef9101 ef881
  have ef89114 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = X3 ◇ ((X0 ◇ ((X3 ◇ X1) ◇ X2)) ◇ (X3 ◇ X1)) := by
    first | exact superpose ef45228 ef89036 | exact superpose ef89036 ef45228
  have ef89455 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = X3 ◇ ((X0 ◇ X3) ◇ (((X3 ◇ X1) ◇ X2) ◇ X1)) := by
    first | exact superpose ef28567 ef89114 | exact superpose ef89114 ef28567
  have ef89725 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = X3 ◇ (X3 ◇ ((((X0 ◇ X3) ◇ X1) ◇ X2) ◇ X1)) := by
    first | exact superpose ef85403 ef89455 | exact superpose ef89455 ef85403
  have ef89942 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (dr X1 X1))))) := by
    first | exact superpose ef39112 ef89725 | exact superpose ef89725 ef39112
  have ef90102 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = (wf X3 X0) ◇ ((dl X2 X1) ◇ X1) := by
    first | exact superpose ef61129 ef89942 | exact superpose ef89942 ef61129
  have ef90215 (X0 X1 X2 X3 : G) :
      wf (X3 ◇ X1) (X0 ◇ (X1 ◇ X2)) = (wf X3 X0) ◇ (X1 ◇ (wf X1 X2)) := by
    first | exact superpose ef4765 ef90102 | exact superpose ef90102 ef4765
  have ef94401 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ (X0 ◇ (X1 ◇ (dl X2 (X3 ◇ X4)))) = X4 ◇ (((dr X0 X1) ◇ X2) ◇ (X3 ◇ X5)) := by
    first | exact superpose ef830 ef957 | exact superpose ef957 ef830
  have ef95028 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X1 ◇ (X2 ◇ ((dr X3 X4) ◇ X5))) = X3 ◇ (X4 ◇ (dl X5 (X1 ◇ (X2 ◇ X0)))) := by
    first | exact superpose ef957 ef830 | exact superpose ef830 ef957
  have ef95029 (X0 X1 X2 X3 X4 X5 : G) :
      X0 ◇ (X1 ◇ (X2 ◇ ((dr X3 X4) ◇ X5))) = X3 ◇ (X4 ◇ (X2 ◇ ((dr X0 X1) ◇ X5))) := by
    first | exact superpose ef460 ef95028 | exact superpose ef95028 ef460
  have ef95611 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ (X0 ◇ (X1 ◇ (dl X2 (X3 ◇ X4)))) = X4 ◇ (X0 ◇ (X1 ◇ (dl X2 (X3 ◇ X5)))) := by
    first | exact superpose ef830 ef94401 | exact superpose ef94401 ef830
  have ef98821 (X0 X1 X2 X3 X4 X5 : G) :
      X2 ◇ (((dr X1 X3) ◇ (X4 ◇ X0)) ◇ X5) = (X0 ◇ X1) ◇ ((dl (dl X4 X3) X2) ◇ X5) := by
    first | exact superpose ef966 ef881 | exact superpose ef881 ef966
  have ef98873 (X0 X1 X2 X3 X4 X5 : G) :
      X2 ◇ (((dr X1 X3) ◇ (X4 ◇ X0)) ◇ X5) = (X0 ◇ X1) ◇ (((X2 ◇ X4) ◇ X3) ◇ X5) := by
    first | exact superpose ef254 ef98821 | exact superpose ef98821 ef254
  have ef99198 (X0 X1 X2 X3 X4 X5 : G) :
      (X0 ◇ X1) ◇ (((X2 ◇ X4) ◇ X3) ◇ X5) = X2 ◇ (X1 ◇ (X3 ◇ (dl (X4 ◇ X0) X5))) := by
    first | exact superpose ef830 ef98873 | exact superpose ef98873 ef830
  have ef99465 (X0 X1 X2 X3 X4 X5 : G) :
      (X0 ◇ X1) ◇ (((X2 ◇ X4) ◇ X3) ◇ X5) = X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (dr X4 X5)))) := by
    first | exact superpose ef644 ef99198 | exact superpose ef99198 ef644
  have ef105121 (X0 X1 X2 X3 : G) :
      (X2 ◇ (X2 ◇ X3)) ◇ (dl X0 X1) = dr (X1 ◇ (X2 ◇ (wf X2 X0))) X3 := by
    first | exact superpose ef994 ef109 | exact superpose ef109 ef994
  have ef105429 (X0 X1 X2 X3 : G) :
      (X2 ◇ (X2 ◇ X3)) ◇ (dl X0 X1) = ((wf X2 X0) ◇ (X1 ◇ X3)) ◇ X2 := by
    first | exact superpose ef1857 ef105121 | exact superpose ef105121 ef1857
  have ef105651 (X0 X1 X2 X3 : G) :
      (X2 ◇ (X2 ◇ X3)) ◇ (dl X0 X1) = (dr X1 X2) ◇ (dr X3 (wf X2 X0)) := by
    first | exact superpose ef8928 ef105429 | exact superpose ef105429 ef8928
  have ef106442 (X0 X1 X2 : G) :
      wf (dl X0 X1) (X1 ◇ X2) = (X1 ◇ X2) ◇ (wf (X2 ◇ X0) (X1 ◇ X2)) := by
    first | exact superpose ef30 ef32693 | exact superpose ef32693 ef30
  have ef106495 (X0 X1 X2 : G) :
      wf X0 (wf X1 X0) = (wf X1 X0) ◇ (wf (dl (wf X1 X2) X2) (wf X1 X0)) := by
    first | exact superpose ef8263 ef32693 | exact superpose ef32693 ef8263
  have ef106565 (X0 X1 : G) : wf X0 (wf X1 X0) = (wf X1 X0) ◇ ((dl X1 X1) ◇ X0) := by
    first | exact superpose ef47056 ef106495 | exact superpose ef106495 ef47056
  have ef106601 (X0 X1 X2 : G) :
      wf (dl X0 X1) (X1 ◇ X2) = (X1 ◇ X2) ◇ (X2 ◇ (wf X0 (dl X1 X2))) := by
    first | exact superpose ef27224 ef106442 | exact superpose ef106442 ef27224
  have ef106664 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef5528 ef106565 | exact superpose ef106565 ef5528
  have ef106691 (X0 X1 X2 : G) : wf (dl X0 X1) (X1 ◇ X2) = dl (wf X0 (dl X1 X2)) X1 := by
    first | exact superpose ef30 ef106601 | exact superpose ef106601 ef30
  have ef106737 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef106664 | exact superpose ef106664 ef76956
  have ef106758 (X0 X1 X2 : G) : wf (dl X0 X1) (X1 ◇ X2) = dl (wf X0 X1) (dl X1 X2) := by
    first | exact superpose ef3584 ef106691 | exact superpose ef106691 ef3584
  have ef106810 (X0 X1 X2 : G) : wf (dl X0 X1) (X1 ◇ X2) = (dl X2 (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef4079 ef106758 | exact superpose ef106758 ef4079
  have ef108057 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = dl (wf X0 (dl X0 X1)) X2 := by
    first | exact superpose ef37243 ef30 | exact superpose ef30 ef37243
  have ef108339 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (wf X0 X1) = (dl X1 (wf X0 X2)) ◇ X0 := by
    first | exact superpose ef30917 ef108057 | exact superpose ef108057 ef30917
  have ef109041 (X0 X1 X2 X3 X4 : G) :
      dl (dr (X4 ◇ (dr X0 X0)) X1) X3 = (X0 ◇ (wf X0 ((X1 ◇ (X2 ◇ X3)) ◇ X4))) ◇ X2 := by
    first | exact superpose ef1008 ef937 | exact superpose ef937 ef1008
  have ef109042 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (wf X0 ((X1 ◇ (X2 ◇ X3)) ◇ X4))) ◇ X2 = dl (dr X3 X1) (X4 ◇ (dr X0 X0)) := by
    first | exact superpose ef1008 ef461 | exact superpose ef461 ef1008
  have ef109171 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X4) ◇ (X0 ◇ (dr X3 X1)) = (X0 ◇ (wf X0 ((X1 ◇ (X2 ◇ X3)) ◇ X4))) ◇ X2 := by
    first | exact superpose ef5478 ef109042 | exact superpose ef109042 ef5478
  have ef109172 (X0 X1 X2 X3 X4 : G) :
      dl (dr (X4 ◇ (dr X0 X0)) X1) X3 = (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) := by
    first | exact superpose ef24414 ef109041 | exact superpose ef109041 ef24414
  have ef109525 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X4) ◇ (X0 ◇ (dr X3 X1)) = (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) := by
    first | exact superpose ef24414 ef109171 | exact superpose ef109171 ef24414
  have ef109526 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) = dl X4 ((dr X3 X1) ◇ (dr X0 X0)) := by
    first | exact superpose ef42460 ef109172 | exact superpose ef109172 ef42460
  have ef109811 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) = X0 ◇ ((dl X3 (wf X0 X1)) ◇ X4) := by
    first | exact superpose ef44072 ef109525 | exact superpose ef109525 ef44072
  have ef109812 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) = (dl X0 (dr X3 X1)) ◇ (X0 ◇ X4) := by
    first | exact superpose ef5478 ef109526 | exact superpose ef109526 ef5478
  have ef110034 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) = (X3 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X4) := by
    first | exact superpose ef129 ef109812 | exact superpose ef109812 ef129
  have ef110205 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ (wf X0 X2)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4) = (X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4) := by
    first | exact superpose ef138 ef110034 | exact superpose ef110034 ef138
  have ef110336 (X0 X1 X3 X4 : G) :
      X0 ◇ ((dl X3 (wf X0 X1)) ◇ X4) = (X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4) := by
    first | exact superpose ef109811 ef110205 | exact superpose ef110205 ef109811
  have ef133504 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X2 ◇ (dl X0 X3)) ◇ X4)) ◇ X5 = (((X4 ◇ X2) ◇ X3) ◇ (dl X1 X0)) ◇ X5 := by
    first | exact superpose ef180 ef2070 | exact superpose ef2070 ef180
  have ef134420 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X2 ◇ (dl X0 X3)) ◇ X4)) ◇ X5 = X2 ◇ ((dl X1 X0) ◇ (X4 ◇ (dr X3 X5))) := by
    first | exact superpose ef39112 ef133504 | exact superpose ef133504 ef39112
  have ef134848 (X0 X1 X2 X3 X4 X5 : G) :
      X2 ◇ ((dl X1 X0) ◇ (X4 ◇ (dr X3 X5))) = X2 ◇ (dr ((dl X0 X3) ◇ X1) (dl X5 X4)) := by
    first | exact superpose ef23089 ef134420 | exact superpose ef134420 ef23089
  have ef135215 (X0 X1 X2 X3 X4 X5 : G) :
      X2 ◇ ((dl X1 X0) ◇ (X4 ◇ (dr X3 X5))) = X2 ◇ ((dl (dl X5 X4) X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef3504 ef134848 | exact superpose ef134848 ef3504
  have ef135491 (X0 X1 X2 X3 X4 X5 : G) :
      X2 ◇ ((dl X1 X0) ◇ (X4 ◇ (dr X3 X5))) = X2 ◇ (((X0 ◇ X5) ◇ X4) ◇ (dr X1 X3)) := by
    first | exact superpose ef254 ef135215 | exact superpose ef135215 ef254
  have ef144475 (X0 X1 X2 X3 : G) :
      dl (wf X0 X1) (dl X2 X3) = X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) := by
    first | exact superpose ef2779 ef295 | exact superpose ef295 ef2779
  have ef144800 (X0 X1 X2 X3 : G) :
      dl (wf X0 X1) (dl X2 X3) = X0 ◇ ((dr X2 X0) ◇ (X3 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef48606 ef144475 | exact superpose ef144475 ef48606
  have ef145156 (X0 X1 X2 X3 : G) :
      dl (wf X0 X1) (dl X2 X3) = X0 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (dr X2 X0)))) := by
    first | exact superpose ef24549 ef144800 | exact superpose ef144800 ef24549
  have ef145422 (X0 X1 X2 X3 : G) :
      (dl X3 (wf X0 X1)) ◇ X2 = X0 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (dr X2 X0)))) := by
    first | exact superpose ef4079 ef145156 | exact superpose ef145156 ef4079
  have ef147256 (X0 X1 X2 X3 : G) :
      (wf X3 (dl X2 X0)) ◇ X1 = X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (dr X1 X2)))) := by
    first | exact superpose ef1793 ef2986 | exact superpose ef2986 ef1793
  have ef147381 (X0 X1 X2 X3 : G) :
      (X3 ◇ X0) ◇ ((wf X0 X1) ◇ X2) = dl (X0 ◇ (X0 ◇ (dr X1 X2))) X3 := by
    first | exact superpose ef2986 ef30 | exact superpose ef30 ef2986
  have ef147487 (X0 X1 X2 X3 : G) :
      X0 ◇ (dl X3 ((wf X0 X1) ◇ X2)) = X3 ◇ (X0 ◇ (X0 ◇ (dr X1 X2))) := by
    first | exact superpose ef2986 ef4225 | exact superpose ef4225 ef2986
  have ef147713 (X0 X1 X2 X3 : G) :
      (X0 ◇ (dr X1 X2)) ◇ (dr X0 X3) = (X3 ◇ X0) ◇ ((wf X0 X1) ◇ X2) := by
    first | exact superpose ef644 ef147381 | exact superpose ef147381 ef644
  have ef147988 (X0 X1 X2 X3 : G) :
      (X3 ◇ X0) ◇ ((wf X0 X1) ◇ X2) = (dl X0 X2) ◇ (dr (X1 ◇ X0) X3) := by
    first | exact superpose ef50487 ef147713 | exact superpose ef147713 ef50487
  have ef151560 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X1 ◇ (dl (wf X0 X4) X4))) = ((dl (dr X0 X0) X1) ◇ X3) ◇ (dl X2 X0) := by
    first | exact superpose ef3326 ef559 | exact superpose ef559 ef3326
  have ef151645 (X0 X1 X2 : G) :
      X0 ◇ ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) =
      dl (dr (X0 ◇ (wf X0 X1)) (X0 ◇ (wf X0 X1))) X1 := by
    first | exact superpose ef3326 ef1015 | exact superpose ef1015 ef3326
  have ef151792 (X0 X1 X2 : G) :
      dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) = X0 ◇
      ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) := by
    first | exact superpose ef7639 ef151645 | exact superpose ef151645 ef7639
  have ef151876 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X1 ◇ (dl (wf X0 X4) X4))) = (X0 ◇ ((dr X3 X1) ◇ X0)) ◇ (dl X2 X0) := by
    first | exact superpose ef3523 ef151560 | exact superpose ef151560 ef3523
  have ef152128 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef37612 ef151792 | exact superpose ef151792 ef37612
  have ef152209 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X1 ◇ (dl (wf X0 X4) X4))) = (X0 ◇ X3) ◇ (dr X0 (dl (dl X2 X0) X1)) := by
    first | exact superpose ef63489 ef151876 | exact superpose ef151876 ef63489
  have ef152448 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (dr X1 (X0 ◇ (wf X0 X1)))) := by
    first | exact superpose ef993 ef152128 | exact superpose ef152128 ef993
  have ef152524 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X1 ◇ (dl (wf X0 X4) X4))) = (X0 ◇ X3) ◇ (dr X0 ((X1 ◇ X2) ◇ X0)) := by
    first | exact superpose ef254 ef152209 | exact superpose ef152209 ef254
  have ef152735 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (((wf X0 X1) ◇ X1) ◇ X0)) := by
    first | exact superpose ef40 ef152448 | exact superpose ef152448 ef40
  have ef152793 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ (X3 ◇ (X1 ◇ (dl (wf X0 X4) X4))) = (X0 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef40 ef152524 | exact superpose ef152524 ef40
  have ef152970 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (dr X0 (wf X0 X1)))) := by
    first | exact superpose ef71379 ef152735 | exact superpose ef152735 ef71379
  have ef153007 (X0 X1 X2 X3 X4 : G) :
      dr X3 (wf X0 (X1 ◇ X2)) = X2 ◇ (X3 ◇ (X1 ◇ (dl (wf X0 X4) X4))) := by
    first | exact superpose ef15903 ef152793 | exact superpose ef152793 ef15903
  have ef153148 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (dr X0 (wf X0 (X0 ◇ X1))))) := by
    first | exact superpose ef27355 ef152970 | exact superpose ef152970 ef27355
  have ef153300 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (wf (dr X0 X0) (dl X0 X1)))) := by
    first | exact superpose ef34897 ef153148 | exact superpose ef153148 ef34897
  have ef153425 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (dr X0 X0))))) := by
    first | exact superpose ef23865 ef153300 | exact superpose ef153300 ef23865
  have ef153518 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0) := by
    first | exact superpose ef68236 ef153425 | exact superpose ef153425 ef68236
  have ef153583 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dl X1 X0) ◇ (X1 ◇ (dr X1 X0)) := by
    first | exact superpose ef24400 ef153518 | exact superpose ef153518 ef24400
  have ef153626 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef44072 ef153583 | exact superpose ef153583 ef44072
  have ef153660 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef153626 | exact superpose ef153626 ef76956
  have ef153685 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef106737 ef153660 | exact superpose ef153660 ef106737
  have ef153704 (X0 X1 : G) : wf (wf X0 X1) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef18 ef153685 | exact superpose ef153685 ef18
  have ef153895 (X0 X1 X2 X3 X4 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X1) = dr X3 (dl ((dr X2 X1) ◇ (wf X1 X0)) X4) := by
    first | exact superpose ef3839 ef605 | exact superpose ef605 ef3839
  have ef154088 (X0 X1 X2 X3 X4 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X1) = dr X3 ((wf X1 X0) ◇ (dr (dr X2 X1) X4)) := by
    first | exact superpose ef644 ef153895 | exact superpose ef153895 ef644
  have ef154339 (X0 X1 X2 X3 X4 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X1) = ((dr (dr X2 X1) X4) ◇ X3) ◇ (wf X1 X0) := by
    first | exact superpose ef40 ef154088 | exact superpose ef154088 ef40
  have ef154567 (X0 X1 X2 X3 X4 : G) :
      (((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X1) = (dr X2 X1) ◇ (X4 ◇ (dl X3 (wf X1 X0))) := by
    first | exact superpose ef830 ef154339 | exact superpose ef154339 ef830
  have ef154766 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X1)) = (dr X2 X1) ◇ (X4 ◇ (dl X3 (wf X1 X0))) := by
    first | exact superpose ef22449 ef154567 | exact superpose ef154567 ef22449
  have ef154934 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (dr X2 X1) ◇ (X4 ◇ (dl X3 (wf X1 X0))) := by
    first | exact superpose ef957 ef154766 | exact superpose ef154766 ef957
  have ef155661 (X0 X1 : G) : wf X0 (wf (dr X1 X0) X0) = wf ((dr X0 X0) ◇ X1) X0 := by
    first | exact superpose ef82 ef153704 | exact superpose ef153704 ef82
  have ef155664 (X0 X1 X2 : G) : wf (dr X0 X1) X2 = wf X2 (wf ((wf X2 X0) ◇ X1) X2) := by
    first | exact superpose ef2725 ef153704 | exact superpose ef153704 ef2725
  have ef155712 (X0 X1 X2 : G) : wf (wf X0 X1) X2 = dr X0 (dl (wf X0 (wf X1 X0)) X2) := by
    first | exact superpose ef153704 ef8798 | exact superpose ef8798 ef153704
  have ef156071 (X0 X1 X2 X3 : G) :
      (X0 ◇ X3) ◇
      (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) =
      dr X3 (wf ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) X1) := by
    first | exact superpose ef3960 ef608 | exact superpose ef608 ef3960
  have ef156258 (X0 X1 X2 X3 : G) :
      (X0 ◇ X3) ◇
      (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) =
      dr X3 (wf X1 (wf (dr (X2 ◇ (dr X0 (wf X1 X2))) X1) X1)) := by
    first | exact superpose ef155661 ef156071 | exact superpose ef156071 ef155661
  have ef156516 (X0 X1 X2 X3 : G) :
      (X0 ◇ X3) ◇
      (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) =
      dr X3 (wf X1 (wf (dr (X2 ◇ X1) (dr X0 (wf X1 X2))) X1)) := by
    first | exact superpose ef1903 ef156258 | exact superpose ef156258 ef1903
  have ef156748 (X0 X1 X2 X3 : G) :
      (X0 ◇ X3) ◇
      (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) =
      dr X3 (wf X1 (wf ((wf X1 X2) ◇ ((X2 ◇ X1) ◇ X0)) X1)) := by
    first | exact superpose ef105 ef156516 | exact superpose ef156516 ef105
  have ef156949 (X0 X1 X2 X3 : G) :
      (X0 ◇ X3) ◇
      (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) =
      dr X3 (wf (dr X2 ((X2 ◇ X1) ◇ X0)) X1) := by
    first | exact superpose ef155664 ef156748 | exact superpose ef156748 ef155664
  have ef157128 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) := by
    first | exact superpose ef40 ef156949 | exact superpose ef156949 ef40
  have ef157283 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (((dr X0 (wf X1 X2)) ◇ ((dr X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))))) ◇ X2) := by
    first | exact superpose ef1857 ef157128 | exact superpose ef157128 ef1857
  have ef157403 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dr (dr X1 X1) X2) ◇ (dr ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) (dr X0 (wf X1 X2)))) := by
    first | exact superpose ef55503 ef157283 | exact superpose ef157283 ef55503
  have ef157488 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dr (dr X1 X1) X2) ◇ (dr ((dr X1 X1) ◇ (dr X0 (wf X1 X2))) (X2 ◇ (dr X0 (wf X1 X2))))) := by
    first | exact superpose ef76162 ef157403 | exact superpose ef157403 ef76162
  have ef157555 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dr (dr X1 X1) X2) ◇ ((dl (X2 ◇ (dr X0 (wf X1 X2))) X0) ◇ (dl (wf X1 X2) (dr X1 X1)))) := by
    first | exact superpose ef5501 ef157488 | exact superpose ef157488 ef5501
  have ef157607 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dr (dr X1 X1) X2) ◇ ((wf X1 X2) ◇ (dl (dl (X2 ◇ (dr X0 (wf X1 X2))) X0) (dr X1 X1)))) := by
    first | exact superpose ef41186 ef157555 | exact superpose ef157555 ef41186
  have ef157655 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dr (dr X1 X1) X2) ◇ ((wf X1 X2) ◇ (X1 ◇ (X1 ◇ (dl (X2 ◇ (dr X0 (wf X1 X2))) X0))))) := by
    first | exact superpose ef129 ef157607 | exact superpose ef157607 ef129
  have ef157693 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((X1 ◇ (wf X1 X2)) ◇ ((dl (X2 ◇ (dr X0 (wf X1 X2))) X0) ◇ (X1 ◇ (dr (dr X1 X1) X2)))) := by
    first | exact superpose ef47475 ef157655 | exact superpose ef157655 ef47475
  have ef157721 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((X1 ◇ (wf X1 X2)) ◇ (((X0 ◇ X2) ◇ X1) ◇ (dr (X2 ◇ (dr X0 (wf X1 X2))) (dr X1 X1)))) := by
    first | exact superpose ef135491 ef157693 | exact superpose ef157693 ef135491
  have ef157745 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dr (X0 ◇ X2) X2) ◇ (X1 ◇ (dr (X2 ◇ (dr X0 (wf X1 X2))) (dr X1 X1)))) := by
    first | exact superpose ef42498 ef157721 | exact superpose ef157721 ef42498
  have ef157765 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇ (dr (dr X1 X1) X2)))) := by
    first | exact superpose ef70418 ef157745 | exact superpose ef157745 ef70418
  have ef157784 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (X0 ◇ (X1 ◇ ((wf X1 X2) ◇ ((X2 ◇ ((dr (dr X1 X1) X2) ◇ X2)) ◇ X0)))) := by
    first | exact superpose ef24208 ef157765 | exact superpose ef157765 ef24208
  have ef157802 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (X0 ◇ (X1 ◇ ((wf X1 X2) ◇ ((X2 ◇ (dr X1 X1)) ◇ (dr X2 (dl X0 X2)))))) := by
    first | exact superpose ef63489 ef157784 | exact superpose ef157784 ef63489
  have ef157818 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (X0 ◇ ((dr X2 (dl X0 X2)) ◇ (X1 ◇ (dl (wf X1 X2) X2)))) := by
    first | exact superpose ef24547 ef157802 | exact superpose ef157802 ef24547
  have ef157834 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      (dr (dr X2 (dl X0 X2)) (wf X1 (X1 ◇ X0))) := by
    first | exact superpose ef153007 ef157818 | exact superpose ef157818 ef153007
  have ef157850 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇
      ((dl (wf X1 (X1 ◇ X0)) (dl X0 X2)) ◇ X2) := by
    first | exact superpose ef1781 ef157834 | exact superpose ef157834 ef1781
  have ef157863 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇ (dr X0 (wf X1 (X1 ◇ X0))) := by
    first | exact superpose ef1765 ef157850 | exact superpose ef157850 ef1765
  have ef157874 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇ (dr X0 (X1 ◇ (wf X1 X0))) := by
    first | exact superpose ef9101 ef157863 | exact superpose ef157863 ef9101
  have ef157884 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇ (((wf X1 X0) ◇ X0) ◇ X1) := by
    first | exact superpose ef40 ef157874 | exact superpose ef157874 ef40
  have ef157893 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = (X0 ◇ X3) ◇ (X0 ◇ (X0 ◇ (dr X1 X1))) := by
    first | exact superpose ef1021 ef157884 | exact superpose ef157884 ef1021
  have ef157902 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = X0 ◇ (dl (X0 ◇ X3) ((wf X0 X1) ◇ X1)) := by
    first | exact superpose ef147487 ef157893 | exact superpose ef157893 ef147487
  have ef157911 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = X0 ◇ (X3 ◇ (dr X0 ((wf X0 X1) ◇ X1))) := by
    first | exact superpose ef644 ef157902 | exact superpose ef157902 ef644
  have ef157918 (X0 X1 X2 X3 : G) :
      dr X3 (wf ((X0 ◇ X2) ◇ (X2 ◇ X1)) X1) = X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (wf X0 X1))) := by
    first | exact superpose ef40 ef157911 | exact superpose ef157911 ef40
  have ef157923 (X0 X1 X3 : G) :
      dr X3 (wf (dl X1 X0) X1) = X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (wf X0 X1))) := by
    first | exact superpose ef30 ef157918 | exact superpose ef157918 ef30
  have ef161276 (X0 X1 : G) :
      wf (dl X0 (wf X0 X1)) X0 = X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (dr (wf X0 X1) (wf X0 X1))) := by
    first | exact superpose ef8141 ef4708 | exact superpose ef4708 ef8141
  have ef161768 (X0 X1 : G) :
      wf (dl X0 (wf X0 X1)) X0 = dl (dr (wf X0 X1) (wf X0 X1)) (dl X0 X1) := by
    first | exact superpose ef295 ef161276 | exact superpose ef161276 ef295
  have ef162033 (X0 X1 : G) :
      wf (dl X0 (wf X0 X1)) X0 = (dl X1 (dr (wf X0 X1) (wf X0 X1))) ◇ X0 := by
    first | exact superpose ef4079 ef161768 | exact superpose ef161768 ef4079
  have ef162281 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = ((wf X0 X1) ◇ ((wf X0 X1) ◇ X1)) ◇ X0 := by
    first | exact superpose ef129 ef162033 | exact superpose ef162033 ef129
  have ef162510 (X0 X1 : G) :
      wf (dl X0 (wf X0 X1)) X0 = (dr (wf X0 X1) X0) ◇ (dr X1 (wf X0 X1)) := by
    first | exact superpose ef8928 ef162281 | exact superpose ef162281 ef8928
  have ef162699 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = (X0 ◇ (X0 ◇ X1)) ◇ (dl X1 (wf X0 X1)) := by
    first | exact superpose ef105651 ef162510 | exact superpose ef162510 ef105651
  have ef162862 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = X1 ◇ (dl (X0 ◇ (X0 ◇ X1)) (wf X0 X1)) := by
    first | exact superpose ef969 ef162699 | exact superpose ef162699 ef969
  have ef162994 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = X1 ◇ ((X0 ◇ X1) ◇ (dr X0 (wf X0 X1))) := by
    first | exact superpose ef644 ef162862 | exact superpose ef162862 ef644
  have ef163103 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = X1 ◇ (X1 ◇ (dr X0 (wf X0 (X0 ◇ X1)))) := by
    first | exact superpose ef27355 ef162994 | exact superpose ef162994 ef27355
  have ef163200 (X0 X1 : G) :
      wf (dl X0 (wf X0 X1)) X0 = X1 ◇ (X1 ◇ (wf (dr X0 X0) (dl X0 X1))) := by
    first | exact superpose ef34897 ef163103 | exact superpose ef163103 ef34897
  have ef163277 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (dr X0 X0)))) := by
    first | exact superpose ef23865 ef163200 | exact superpose ef163200 ef23865
  have ef163335 (X0 X1 : G) : wf (dl X0 (wf X0 X1)) X0 = (wf X1 (dl X0 X0)) ◇ X0 := by
    first | exact superpose ef147256 ef163277 | exact superpose ef163277 ef147256
  have ef163378 (X0 X1 : G) : wf (wf X0 (dl X0 X1)) X0 = (wf X1 (dl X0 X0)) ◇ X0 := by
    first | exact superpose ef76956 ef163335 | exact superpose ef163335 ef76956
  have ef163414 (X0 X1 : G) : wf X0 (wf (dl X0 X1) X0) = (wf X1 (dl X0 X0)) ◇ X0 := by
    first | exact superpose ef153704 ef163378 | exact superpose ef163378 ef153704
  have ef163591 (X0 X1 X2 : G) :
      ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇
      ((dl X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) =
      wf (X1 ◇ X0) ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) := by
    first | exact superpose ef3960 ef4710 | exact superpose ef4710 ef3960
  have ef163708 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      wf (wf (dl (X0 ◇ (X0 ◇ X0)) X0) (X0 ◇ (X0 ◇ X0))) (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef4691 ef4710 | exact superpose ef4710 ef4691
  have ef163872 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      wf ((dl (X0 ◇ X0) (wf (X0 ◇ (X0 ◇ X0)) X0)) ◇ X0) (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef106810 ef163708 | exact superpose ef163708 ef106810
  have ef163989 (X0 X1 X2 : G) :
      ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇
      ((dl X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) = X1 ◇
      (X1 ◇ (dl X1 (wf X0 (X2 ◇ (dr X0 (wf X1 X2)))))) := by
    first | exact superpose ef85634 ef163591 | exact superpose ef163591 ef85634
  have ef164082 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      (wf (dl (X0 ◇ X0) (wf (X0 ◇ (X0 ◇ X0)) X0)) X0) ◇ (X0 ◇ (wf X0 X0)) := by
    first | exact superpose ef90215 ef163872 | exact superpose ef163872 ef90215
  have ef164196 (X0 X1 X2 : G) :
      ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇
      ((dl X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) = X1 ◇
      (wf X0 (X2 ◇ (dr X0 (wf X1 X2)))) := by
    first | exact superpose ef17 ef163989 | exact superpose ef163989 ef17
  have ef164278 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 ◇
      ((dl X0 (wf (dl (X0 ◇ X0) (wf (X0 ◇ (X0 ◇ X0)) X0)) X0)) ◇ X0) := by
    first | exact superpose ef27431 ef164082 | exact superpose ef164082 ef27431
  have ef164390 (X0 X1 X2 : G) :
      ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇
      ((dl X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) = X1 ◇
      ((dr X0 X0) ◇ (dl (wf X1 X2) X2)) := by
    first | exact superpose ef5475 ef164196 | exact superpose ef164196 ef5475
  have ef164466 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 ◇
      ((wf (dl X0 (dl (X0 ◇ X0) (wf (X0 ◇ (X0 ◇ X0)) X0))) X0) ◇ X0) := by
    first | exact superpose ef59626 ef164278 | exact superpose ef164278 ef59626
  have ef164575 (X0 X1 X2 : G) :
      ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇
      ((dl X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) = X1 ◇ ((wf X1 X0) ◇ X0) := by
    first | exact superpose ef66208 ef164390 | exact superpose ef164390 ef66208
  have ef164646 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 ◇
      ((wf ((dl (wf (X0 ◇ (X0 ◇ X0)) X0) X0) ◇ (X0 ◇ X0)) X0) ◇ X0) := by
    first | exact superpose ef4079 ef164466 | exact superpose ef164466 ef4079
  have ef164749 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (X2 ◇ (dr X0 (wf X1 X2))) ◇
      ((dl X1 X1) ◇ ((dr X1 X1) ◇ ((dr X1 X1) ◇ (X2 ◇ (dr X0 (wf X1 X2)))))) := by
    first | exact superpose ef957 ef164575 | exact superpose ef164575 ef957
  have ef164816 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 ◇
      ((X0 ◇ (wf (X0 ◇ X0) (wf (wf (X0 ◇ (X0 ◇ X0)) X0) X0))) ◇ X0) := by
    first | exact superpose ef9710 ef164646 | exact superpose ef164646 ef9710
  have ef164913 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ (X1 ◇
      ((dr X1 X1) ◇ ((dr (X2 ◇ (dr X0 (wf X1 X2))) (dl X1 X1)) ◇ (X2 ◇ (dr X0 (wf X1 X2)))))) := by
    first | exact superpose ef95029 ef164749 | exact superpose ef164749 ef95029
  have ef164965 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      (X0 ◇ (dr X0 (wf (wf (X0 ◇ (X0 ◇ X0)) X0) X0))) ◇ X0 := by
    first | exact superpose ef82562 ef164816 | exact superpose ef164816 ef82562
  have ef165055 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) =
      ((dr (X2 ◇ (dr X0 (wf X1 X2))) (dl X1 X1)) ◇ (X2 ◇ (dr X0 (wf X1 X2)))) ◇ (X1 ◇ X1) := by
    first | exact superpose ef2635 ef164913 | exact superpose ef164913 ef2635
  have ef165102 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      dl (wf (wf (X0 ◇ (X0 ◇ X0)) X0) X0) X0 := by
    first | exact superpose ef201 ef164965 | exact superpose ef164965 ef201
  have ef165185 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = ((X1 ◇ X2) ◇ X1) ◇
      (dr (dr X0 (wf X1 X2)) (dr (X2 ◇ (dr X0 (wf X1 X2))) (dl X1 X1))) := by
    first | exact superpose ef23985 ef165055 | exact superpose ef165055 ef23985
  have ef165227 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      dl (wf (X0 ◇ (wf (X0 ◇ X0) X0)) X0) X0 := by
    first | exact superpose ef32693 ef165102 | exact superpose ef165102 ef32693
  have ef165301 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = ((X1 ◇ X2) ◇ X1) ◇
      ((dl X1 X1) ◇ ((dr X0 (wf X1 X2)) ◇ (X2 ◇ (dr X0 (wf X1 X2))))) := by
    first | exact superpose ef105 ef165185 | exact superpose ef165185 ef105
  have ef165341 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      (wf (wf (X0 ◇ X0) X0) X0) ◇ (dr X0 X0) := by
    first | exact superpose ef46859 ef165227 | exact superpose ef165227 ef46859
  have ef165403 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (X2 ◇ (dl X1 X1)) ◇
      (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (dr X0 (wf X1 X2))) ◇ (wf X1 X2)) := by
    first | exact superpose ef99465 ef165301 | exact superpose ef165301 ef99465
  have ef165439 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      (wf (X0 ◇ (wf X0 X0)) X0) ◇ (dr X0 X0) := by
    first | exact superpose ef32693 ef165341 | exact superpose ef165341 ef32693
  have ef165490 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (wf X1 X2) ◇
      (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (dr X0 (X2 ◇ (dl X1 X1)))) ◇ (wf X1 X2)) := by
    first | exact superpose ef42335 ef165403 | exact superpose ef165403 ef42335
  have ef165520 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      (X0 ◇ (wf (wf X0 X0) X0)) ◇ (dr X0 X0) := by
    first | exact superpose ef32693 ef165439 | exact superpose ef165439 ef32693
  have ef165566 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (wf X1 X2) ◇
      ((dr X0 (wf X1 X2)) ◇ ((dr X0 (X2 ◇ (dl X1 X1))) ◇ ((X1 ◇ X2) ◇ X1))) := by
    first | exact superpose ef48606 ef165490 | exact superpose ef165490 ef48606
  have ef165592 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) =
      dr (wf (wf X0 X0) X0) X0 := by
    first | exact superpose ef115 ef165520 | exact superpose ef165520 ef115
  have ef165629 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (wf X1 X2) ◇
      (X1 ◇ ((dr X0 (X2 ◇ (dl X1 X1))) ◇ ((X1 ◇ X2) ◇ (dr X0 (wf X1 X2))))) := by
    first | exact superpose ef24549 ef165566 | exact superpose ef165566 ef24549
  have ef165650 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = (X0 ◇ (X0 ◇ X0)) ◇
      ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef153704 ef165592 | exact superpose ef165592 ef153704
  have ef165682 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇
      ((X2 ◇ X1) ◇ ((dr X0 (X2 ◇ (dl X1 X1))) ◇ ((X1 ◇ X2) ◇ (dr X0 (wf X1 X2))))) := by
    first | exact superpose ef44390 ef165629 | exact superpose ef165629 ef44390
  have ef165698 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = (X0 ◇ X0) ◇
      ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef957 ef165650 | exact superpose ef165650 ef957
  have ef165724 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇
      ((X2 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (dl (dr X0 (X2 ◇ (dl X1 X1))) (wf X1 X2)))) := by
    first | exact superpose ef76589 ef165682 | exact superpose ef165682 ef76589
  have ef165737 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = (X0 ◇ X0) ◇
      ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0)))))) := by
    first | exact superpose ef47475 ef165698 | exact superpose ef165698 ef47475
  have ef165760 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇
      ((dr X0 X1) ◇ (X1 ◇ (dl (dr X0 (X2 ◇ (dl X1 X1))) (wf X1 X2)))) := by
    first | exact superpose ef19353 ef165724 | exact superpose ef165724 ef19353
  have ef165771 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      ((dl X0 (wf X0 X0)) ◇ (X0 ◇ (X0 ◇ (dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0)))))) := by
    first | exact superpose ef110336 ef165737 | exact superpose ef165737 ef110336
  have ef165791 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇
      (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (dr X0 (X2 ◇ (dl X1 X1))))))) := by
    first | exact superpose ef154934 ef165760 | exact superpose ef165760 ef154934
  have ef165800 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (dl X0 (wf X0 X0))))))) := by
    first | exact superpose ef95611 ef165771 | exact superpose ef165771 ef95611
  have ef165817 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (X2 ◇ X1) ◇ (dr X1 (dl X0 (dr X0 (X2 ◇ (dl X1 X1))))) := by
    first | exact superpose ef38231 ef165791 | exact superpose ef165791 ef38231
  have ef165826 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      (dl (X0 ◇ (dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (dl X0 (wf X0 X0))))) X0) := by
    first | exact superpose ef30 ef165800 | exact superpose ef165800 ef30
  have ef165843 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (X2 ◇ X1) ◇ (dr X1 (X0 ◇ ((X2 ◇ (dl X1 X1)) ◇ X0))) := by
    first | exact superpose ef129 ef165817 | exact superpose ef165817 ef129
  have ef165850 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      ((dl (X0 ◇ (X0 ◇ X0)) (X0 ◇ (dl X0 (wf X0 X0)))) ◇ (dr X0 X0)) := by
    first | exact superpose ef644 ef165826 | exact superpose ef165826 ef644
  have ef165865 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = (X2 ◇ X1) ◇ ((((X2 ◇ (dl X1 X1)) ◇ X0) ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef165843 | exact superpose ef165843 ef40
  have ef165872 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      ((dl X0 (X0 ◇ (dl X0 (wf X0 X0)))) ◇ (dr (X0 ◇ (X0 ◇ X0)) X0)) := by
    first | exact superpose ef55371 ef165850 | exact superpose ef165850 ef55371
  have ef165886 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ ((dl X2 (wf X1 ((X2 ◇ (dl X1 X1)) ◇ X0))) ◇ X0) := by
    first | exact superpose ef110336 ef165865 | exact superpose ef165865 ef110336
  have ef165892 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      ((dl X0 (X0 ◇ (dl X0 (wf X0 X0)))) ◇ (dr (X0 ◇ X0) (X0 ◇ X0))) := by
    first | exact superpose ef76162 ef165872 | exact superpose ef165872 ef76162
  have ef165903 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ ((dl X2 (wf X1 (X1 ◇ (dr (X0 ◇ X2) X1)))) ◇ X0) := by
    first | exact superpose ef5518 ef165886 | exact superpose ef165886 ef5518
  have ef165908 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = X0 ◇
      (((X0 ◇ X0) ◇ X0) ◇ ((wf X0 X0) ◇ (X0 ◇ (dl X0 (wf X0 X0))))) := by
    first | exact superpose ef147988 ef165892 | exact superpose ef165892 ef147988
  have ef165917 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ ((dl X2 (X1 ◇ (wf X1 (dr (X0 ◇ X2) X1)))) ◇ X0) := by
    first | exact superpose ef9101 ef165903 | exact superpose ef165903 ef9101
  have ef165921 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = dl ((wf X0 X0) ◇ (X0 ◇ (dl X0 (wf X0 X0)))) (dl X0 X0) := by
    first | exact superpose ef295 ef165908 | exact superpose ef165908 ef295
  have ef165928 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ ((wf X1 (dr (X0 ◇ X2) X1)) ◇ (dr X2 (dl X0 X1))) := by
    first | exact superpose ef7908 ef165917 | exact superpose ef165917 ef7908
  have ef165931 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = (dl X0 ((wf X0 X0) ◇ (X0 ◇ (dl X0 (wf X0 X0))))) ◇ X0 := by
    first | exact superpose ef4079 ef165921 | exact superpose ef165921 ef4079
  have ef165936 (X0 X1 X2 : G) :
      X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ (((dr X1 X1) ◇ (X0 ◇ X2)) ◇ (dr X2 (dl X0 X1))) := by
    first | exact superpose ef82 ef165928 | exact superpose ef165928 ef82
  have ef165938 (X0 : G) :
      dr (wf X0 (wf X0 X0)) X0 = (X0 ◇ (dl X0 (wf X0 X0))) ◇ (dr X0 (dl X0 (wf X0 X0))) := by
    first | exact superpose ef7908 ef165931 | exact superpose ef165931 ef7908
  have ef165943 (X0 X1 : G) : X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ (dl (dr (dl X0 X1) X0) (dr X1 X1)) := by
    first | exact superpose ef2595 ef165936 | exact superpose ef165936 ef2595
  have ef165944 (X0 : G) : dr (wf X0 (wf X0 X0)) X0 = ((X0 ◇ X0) ◇ (dl X0 (wf X0 X0))) ◇ X0 := by
    first | exact superpose ef61233 ef165938 | exact superpose ef165938 ef61233
  have ef165948 (X0 X1 : G) : X1 ◇ ((wf X1 X0) ◇ X0) = X1 ◇ (X1 ◇ (X1 ◇ (dr (dl X0 X1) X0))) := by
    first | exact superpose ef129 ef165943 | exact superpose ef165943 ef129
  have ef165949 (X0 : G) : dr (wf X0 (wf X0 X0)) X0 = (dr X0 X0) ◇ ((dl X0 (wf X0 X0)) ◇ X0) := by
    first | exact superpose ef470 ef165944 | exact superpose ef165944 ef470
  have ef165952 (X0 X1 : G) : (wf X1 (dl X0 X1)) ◇ X0 = X1 ◇ ((wf X1 X0) ◇ X0) := by
    first | exact superpose ef2986 ef165948 | exact superpose ef165948 ef2986
  have ef165953 (X0 : G) : dr (wf X0 (wf X0 X0)) X0 = wf X0 (dl X0 (wf X0 X0)) := by
    first | exact superpose ef19 ef165949 | exact superpose ef165949 ef19
  have ef165956 (X0 : G) : dr (wf X0 (wf X0 X0)) X0 = wf X0 (wf (dl X0 X0) X0) := by
    first | exact superpose ef59626 ef165953 | exact superpose ef165953 ef59626
  have ef165959 (X0 : G) : (wf X0 (dl X0 X0)) ◇ X0 = dr (wf X0 (wf X0 X0)) X0 := by
    first | exact superpose ef163414 ef165956 | exact superpose ef165956 ef163414
  have ef165962 (X0 : G) : (X0 ◇ X0) ◇ (wf X0 X0) = (wf X0 (dl X0 X0)) ◇ X0 := by
    first | exact superpose ef8141 ef165959 | exact superpose ef165959 ef8141
  have ef165965 (X0 : G) : X0 ◇ ((wf X0 X0) ◇ X0) = (X0 ◇ X0) ◇ (wf X0 X0) := by
    first | exact superpose ef165952 ef165962 | exact superpose ef165962 ef165952
  have ef173695 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) =
      ((X1 ◇ (wf (dl X0 X1) X0)) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) ◇ X3 := by
    first | exact superpose ef182 ef99 | exact superpose ef99 ef182
  have ef174124 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = (dl X2 X1) ◇
      (dl (dr (wf (dl X0 X1) X0) X3) (((dl X1 X2) ◇ X0) ◇ (dl X0 X1))) := by
    first | exact superpose ef67148 ef173695 | exact superpose ef173695 ef67148
  have ef174539 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = (dl X2 X1) ◇
      (X0 ◇ (((dl X0 X1) ◇ (dl X1 X2)) ◇ (dr (wf (dl X0 X1) X0) X3))) := by
    first | exact superpose ef291 ef174124 | exact superpose ef174124 ef291
  have ef174953 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = (dl X2 X1) ◇
      (X0 ◇ (((dl X0 X1) ◇ (dl X1 X2)) ◇ ((wf X1 X0) ◇ (dr X3 X0)))) := by
    first | exact superpose ef55504 ef174539 | exact superpose ef174539 ef55504
  have ef175364 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = (dl X2 X1) ◇
      (X0 ◇ (X2 ◇ (dr (((wf X1 X0) ◇ (dr X3 X0)) ◇ (dl X0 X1)) X1))) := by
    first | exact superpose ef5518 ef174953 | exact superpose ef174953 ef5518
  have ef175767 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = (dl X2 X1) ◇
      (X0 ◇ (X2 ◇ (dr (((wf X1 X0) ◇ (dr X3 X0)) ◇ X1) (dl X0 X1)))) := by
    first | exact superpose ef59818 ef175364 | exact superpose ef175364 ef59818
  have ef176150 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) =
      (dr (((wf X1 X0) ◇ (dr X3 X0)) ◇ X1) (dl X0 X1)) ◇ (X0 ◇ X1) := by
    first | exact superpose ef6848 ef175767 | exact superpose ef175767 ef6848
  have ef176502 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) =
      ((X1 ◇ (((wf X1 X0) ◇ (dr X3 X0)) ◇ X1)) ◇ X0) ◇ (dl X0 X1) := by
    first | exact superpose ef470 ef176150 | exact superpose ef176150 ef470
  have ef176815 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = X0 ◇
      (dl ((X1 ◇ (((wf X1 X0) ◇ (dr X3 X0)) ◇ X1)) ◇ X0) X1) := by
    first | exact superpose ef969 ef176502 | exact superpose ef176502 ef969
  have ef177099 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = X0 ◇
      ((X1 ◇ (dl (((wf X1 X0) ◇ (dr X3 X0)) ◇ X1) X0)) ◇ X1) := by
    first | exact superpose ef306 ef176815 | exact superpose ef176815 ef306
  have ef177340 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = X0 ◇
      (X0 ◇ (dr (X1 ◇ X1) (((wf X1 X0) ◇ (dr X3 X0)) ◇ X1))) := by
    first | exact superpose ef5518 ef177099 | exact superpose ef177099 ef5518
  have ef177551 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = X0 ◇
      (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((wf X1 X0) ◇ (dr X3 X0)))) := by
    first | exact superpose ef40 ef177340 | exact superpose ef177340 ef40
  have ef177736 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) =
      (dl (X1 ◇ (X1 ◇ X1)) (wf X0 (wf X1 X0))) ◇ X3 := by
    first | exact superpose ef145422 ef177551 | exact superpose ef177551 ef145422
  have ef177879 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) =
      ((X1 ◇ X1) ◇ (dr X1 (wf X0 (wf X1 X0)))) ◇ X3 := by
    first | exact superpose ef644 ef177736 | exact superpose ef177736 ef644
  have ef177990 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) = (dr X1 X1) ◇
      ((dr X3 X1) ◇ (wf X0 (wf X1 X0))) := by
    first | exact superpose ef65693 ef177879 | exact superpose ef177879 ef65693
  have ef178082 (X0 X1 X2 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((((dl X1 X2) ◇ X0) ◇ (dl X0 X1)) ◇ X2)) =
      wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef13286 ef177990 | exact superpose ef177990 ef13286
  have ef178157 (X0 X1 X2 X3 : G) :
      wf X1 (dr X3 (wf X0 (wf X1 X0))) =
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((dr X0 X2) ◇ ((dl X0 X1) ◇ (dl X1 X2)))) := by
    first | exact superpose ef48606 ef178082 | exact superpose ef178082 ef48606
  have ef178225 (X0 X1 X2 X3 : G) :
      wf X1 (dr X3 (wf X0 (wf X1 X0))) =
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((dr X0 X2) ◇ (X1 ◇ (dl (dl X0 X1) X2)))) := by
    first | exact superpose ef41186 ef178157 | exact superpose ef178157 ef41186
  have ef178286 (X0 X1 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ (dr X1 (dl X0 (dl X0 X1)))) =
      wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef4138 ef178225 | exact superpose ef178225 ef4138
  have ef178333 (X0 X1 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ (dr X1 ((dl X1 X0) ◇ X0))) =
      wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef4079 ef178286 | exact superpose ef178286 ef4079
  have ef178371 (X0 X1 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ (dl X1 X0))) =
      wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef40 ef178333 | exact superpose ef178333 ef40
  have ef178401 (X0 X1 X3 : G) :
      wf (wf (dl X0 X1) X0) ((X1 ◇ X3) ◇ (X1 ◇ (X1 ◇ (dr X0 X0)))) =
      wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef76589 ef178371 | exact superpose ef178371 ef76589
  have ef178430 (X0 X1 X3 : G) :
      wf X1 (dr X3 (wf X0 (wf X1 X0))) =
      wf (wf (dl X0 X1) X0) (X1 ◇ (dl (X1 ◇ X3) ((wf X1 X0) ◇ X0))) := by
    first | exact superpose ef147487 ef178401 | exact superpose ef178401 ef147487
  have ef178457 (X0 X1 X3 : G) :
      wf X1 (dr X3 (wf X0 (wf X1 X0))) =
      wf (wf (dl X0 X1) X0) (X1 ◇ (X3 ◇ (dr X1 ((wf X1 X0) ◇ X0)))) := by
    first | exact superpose ef644 ef178430 | exact superpose ef178430 ef644
  have ef178480 (X0 X1 X3 : G) :
      wf X1 (dr X3 (wf X0 (wf X1 X0))) =
      wf (wf (dl X0 X1) X0) (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (wf X1 X0)))) := by
    first | exact superpose ef40 ef178457 | exact superpose ef178457 ef40
  have ef178498 (X0 X1 X3 : G) :
      wf (wf (dl X0 X1) X0) (dr X3 (wf (dl X0 X1) X0)) = wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef157923 ef178480 | exact superpose ef178480 ef157923
  have ef178513 (X0 X1 X3 : G) :
      (dr (wf (dl X0 X1) X0) (wf (dl X0 X1) X0)) ◇ X3 = wf X1 (dr X3 (wf X0 (wf X1 X0))) := by
    first | exact superpose ef82 ef178498 | exact superpose ef178498 ef82
  have ef178528 (X0 X1 X3 : G) :
      wf X1 (dr X3 (wf X0 (wf X1 X0))) = X0 ◇ ((dr X3 X1) ◇ (wf X0 X1)) := by
    first | exact superpose ef83926 ef178513 | exact superpose ef178513 ef83926
  have ef363631 (X0 : G) : wf (wf X0 X0) X0 = X0 ◇ (wf X0 (dr (wf X0 X0) (wf X0 (wf X0 X0)))) := by
    first | exact superpose ef8152 ef4520 | exact superpose ef4520 ef8152
  have ef363915 (X0 : G) : wf (wf X0 X0) X0 = X0 ◇ (X0 ◇ ((dr (wf X0 X0) X0) ◇ (wf X0 X0))) := by
    first | exact superpose ef178528 ef363631 | exact superpose ef363631 ef178528
  have ef364173 (X0 : G) : (wf X0 X0) ◇ (X0 ◇ (wf X0 X0)) = wf (wf X0 X0) X0 := by
    first | exact superpose ef2635 ef363915 | exact superpose ef363915 ef2635
  have ef364369 (X0 : G) : wf X0 (wf X0 X0) = (wf X0 X0) ◇ (X0 ◇ (wf X0 X0)) := by
    first | exact superpose ef153704 ef364173 | exact superpose ef364173 ef153704
  have ef364492 (X0 : G) : wf X0 (wf X0 X0) = X0 ◇ ((dl X0 (wf X0 X0)) ◇ X0) := by
    first | exact superpose ef27431 ef364369 | exact superpose ef364369 ef27431
  have ef364580 (X0 : G) : wf X0 (wf X0 X0) = X0 ◇ ((X0 ◇ X0) ◇ (wf X0 X0)) := by
    first | exact superpose ef108339 ef364492 | exact superpose ef364492 ef108339
  have ef364634 (X0 : G) : wf X0 (wf X0 X0) = X0 ◇ (X0 ◇ ((wf X0 X0) ◇ X0)) := by
    first | exact superpose ef165965 ef364580 | exact superpose ef364580 ef165965
  have ef364672 (X0 : G) : wf X0 (wf X0 X0) = dr X0 (wf X0 X0) := by
    first | exact superpose ef23 ef364634 | exact superpose ef364634 ef23
  have ef365449 (X0 : G) : (wf X0 (wf X0 X0)) ◇ (wf X0 X0) = X0 := by
    first | exact superpose ef364672 ef15 | exact superpose ef15 ef364672
  have ef365527 (X0 X1 : G) : dr X1 (wf X0 X0) = dr X0 (dl (wf X0 (wf X0 X0)) X1) := by
    first | exact superpose ef364672 ef8669 | exact superpose ef8669 ef364672
  have ef365533 (X0 X1 : G) : dr X1 (wf X0 X0) = wf (wf X0 X0) X1 := by
    first | exact superpose ef155712 ef365527 | exact superpose ef365527 ef155712
  have ef366860 (X0 : G) : wf X0 X0 = dr (wf X0 X0) (wf X0 X0) := by
    first | exact superpose ef365449 ef2725 | exact superpose ef2725 ef365449
  have ef366861 (X0 : G) : wf X0 X0 = wf (wf X0 X0) (wf X0 X0) := by
    first | exact superpose ef365533 ef366860 | exact superpose ef366860 ef365533
  have ef371123 : wf x x ≠ wf x x := by
    first | exact superpose ef366861 ef20 | exact superpose ef20 ef366861
  exact absurd rfl ef371123

theorem Equation3659_termStructuralFromFin_Equation898_qdiv :
    Law3659.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.rdv (.var 0) (.var 0)) (.op (.var 1) (.var 0))) (.rdv (.ldv (.var 0) (.var 1)) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3659.models_iff]
    exact fun x ↦
      @qaux898_3659_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_56R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_56L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

set_option maxHeartbeats 1400000 in
/-- Equation 3667 `x ◇ x = (x ◇ y) ◇ (y ◇ x)` holds of the operation `x □ y := ((x/x)◇(y◇x))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_3667_56 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (x y : G) :
    wf x x = wf (wf x y) (wf y x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef20 : wf x x ≠ wf (wf x y) (wf y x) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef37 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef64 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef67 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef14 ef14
  have ef69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef70 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef82 (X0 X1 : G) : wf X1 (dr X0 X1) = (dr X1 X1) ◇ X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef85 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (dr ((X0 ◇ X1) ◇ (X1 ◇ X2)) ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇
      X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef87 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = (dr (X1 ◇ X2) (X1 ◇ X2)) ◇ X0 := by
    first | exact superpose ef14 ef19 | exact superpose ef19 ef14
  have ef88 (X0 X1 : G) : dr X0 X0 = (X0 ◇ (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef90 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ ((X2 ◇ (dr X0 X0)) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef91 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1))) ◇ (dr X0 X0) = X2 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef92 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (dr X0 X0)) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef99 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0 := by
    first | exact superpose ef40 ef87 | exact superpose ef87 ef40
  have ef101 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef40 ef85 | exact superpose ef85 ef40
  have ef104 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = (((X1 ◇ X2) ◇ (dl X2 X0)) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef30 ef101 | exact superpose ef101 ef30
  have ef105 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef106 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1)) = dr X2 (dr X0 X0) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef107 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef109 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef23 ef23
  have ef110 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef13 ef23 | exact superpose ef23 ef13
  have ef111 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef14 ef23 | exact superpose ef23 ef14
  have ef112 (X0 X1 : G) : X0 ◇ (wf X0 X1) = dr (dr X0 X0) X1 := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef115 (X0 X1 X2 : G) : dr X2 X0 = (X1 ◇ X2) ◇ (dr X0 X1) := by
    first | exact superpose ef23 ef23
  have ef124 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (dr X0 X1)) = X3 := by
    first | exact superpose ef23 ef12 | exact superpose ef12 ef23
  have ef126 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef129 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef131 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef138 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef40 ef111 | exact superpose ef111 ef40
  have ef139 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef40 ef110 | exact superpose ef110 ef40
  have ef149 (X0 X1 : G) : X0 ◇ (wf X0 (dl X1 (dr X0 X0))) = X1 := by
    first | exact superpose ef19 ef24 | exact superpose ef24 ef19
  have ef156 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef164 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef167 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ ((dl X0 X3) ◇ (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef24 ef14 | exact superpose ef14 ef24
  have ef177 (X0 X1 : G) : X0 ◇ (wf X0 (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef129 ef149 | exact superpose ef149 ef129
  have ef194 (X0 X1 : G) : wf X1 (X0 ◇ (dr X1 (dr X1 X1))) = X0 := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef201 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef26 ef18 | exact superpose ef18 ef26
  have ef214 (X0 X1 : G) : wf X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    first | exact superpose ef105 ef194 | exact superpose ef194 ef105
  have ef239 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef13 ef27 | exact superpose ef27 ef13
  have ef243 (X0 X1 X2 X3 : G) : (dl X2 (X0 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef27 | exact superpose ef27 ef23
  have ef254 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef256 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef287 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef291 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef292 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef30 ef30
  have ef302 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef306 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef316 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef322 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef30 ef14 | exact superpose ef14 ef30
  have ef325 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef30 ef18 | exact superpose ef18 ef30
  have ef337 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef256 ef322 | exact superpose ef322 ef256
  have ef444 (X0 X1 : G) : (wf X0 X1) ◇ (dr X0 (dr X0 X0)) = X1 := by
    first | exact superpose ef19 ef36 | exact superpose ef36 ef19
  have ef458 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef36 ef23 | exact superpose ef23 ef36
  have ef460 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef461 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef470 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef40 ef458 | exact superpose ef458 ef40
  have ef478 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef105 ef444 | exact superpose ef444 ef105
  have ef538 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef37 ef27 | exact superpose ef27 ef37
  have ef644 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef649 (X0 X1 : G) : wf X1 (dl (X1 ◇ X0) (dr X1 X1)) = X0 := by
    first | exact superpose ef61 ef19 | exact superpose ef19 ef61
  have ef690 (X0 X1 : G) : wf X1 (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    first | exact superpose ef129 ef649 | exact superpose ef649 ef129
  have ef830 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef23 ef64 | exact superpose ef64 ef23
  have ef849 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef64 ef30 | exact superpose ef30 ef64
  have ef878 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef302 ef849 | exact superpose ef849 ef302
  have ef900 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef644 ef878 | exact superpose ef878 ef644
  have ef924 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef927 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef955 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef291 ef927 | exact superpose ef927 ef291
  have ef957 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef129 ef924 | exact superpose ef924 ef129
  have ef969 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef955 | exact superpose ef955 ef30
  have ef993 (X0 X1 X2 : G) : dl X2 (X0 ◇ (wf X0 X1)) = (dr X0 X0) ◇ (X1 ◇ X2) := by
    first | exact superpose ef88 ef30 | exact superpose ef30 ef88
  have ef999 (X0 X1 X2 : G) : dr X2 (dr X0 X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef88 ef40 | exact superpose ef40 ef88
  have ef1004 (X0 X1 : G) : (dl (wf X0 X1) X1) ◇ (dr X0 X0) = X0 := by
    first | exact superpose ef88 ef27 | exact superpose ef27 ef88
  have ef1015 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef105 ef999 | exact superpose ef999 ef105
  have ef1765 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef17 ef107 | exact superpose ef107 ef17
  have ef1777 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef14 ef107 | exact superpose ef107 ef14
  have ef1778 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef107 | exact superpose ef107 ef30
  have ef1780 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef36 ef107 | exact superpose ef107 ef36
  have ef1781 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef107 | exact superpose ef107 ef15
  have ef1793 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1806 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1808 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = (dr X0 X1) ◇ ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef107 ef30 | exact superpose ef30 ef107
  have ef1857 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef129 ef1780 | exact superpose ef1780 ef129
  have ef1859 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef969 ef1778 | exact superpose ef1778 ef969
  have ef1890 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef254 ef1859 | exact superpose ef1859 ef254
  have ef1903 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1890 | exact superpose ef1890 ef23
  have ef1972 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) ◇ (X0 ◇ X1) = X3 := by
    first | exact superpose ef26 ef70 | exact superpose ef70 ef26
  have ef2109 (X0 X2 X3 X4 : G) : dr X0 (dl X2 (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) = X3 := by
    first | exact superpose ef256 ef1972 | exact superpose ef1972 ef256
  have ef2210 (X0 X2 X3 X4 : G) : dr X0 ((X0 ◇ (dr X4 X2)) ◇ ((dr X4 X3) ◇ X2)) = X3 := by
    first | exact superpose ef460 ef2109 | exact superpose ef2109 ef460
  have ef2281 (X0 X2 X3 X4 : G) : (((dr X4 X3) ◇ X2) ◇ X0) ◇ (X0 ◇ (dr X4 X2)) = X3 := by
    first | exact superpose ef40 ef2210 | exact superpose ef2210 ef40
  have ef2327 (X2 X3 X4 : G) : dl (dr X4 X2) ((dr X4 X3) ◇ X2) = X3 := by
    first | exact superpose ef30 ef2281 | exact superpose ef2281 ef30
  have ef2378 (X0 X1 : G) : wf (dr X0 X0) X1 = (X0 ◇ (wf X0 (dr X0 X0))) ◇ (X1 ◇ (dr X0 X0)) := by
    first | exact superpose ef112 ef19 | exact superpose ef19 ef112
  have ef2397 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 (wf X0 (dr X0 X0))) := by
    first | exact superpose ef1806 ef2378 | exact superpose ef2378 ef1806
  have ef2406 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 ((dr X0 X0) ◇ X0)) := by
    first | exact superpose ef82 ef2397 | exact superpose ef2397 ef82
  have ef2410 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 X0) := by
    first | exact superpose ef15 ef2406 | exact superpose ef2406 ef15
  have ef2553 (X0 X1 X2 : G) : dr X1 X2 = (dr X0 X0) ◇ (dr X2 (X0 ◇ (wf X0 X1))) := by
    first | exact superpose ef88 ef115 | exact superpose ef115 ef88
  have ef2679 (X0 X1 X2 : G) : dr X1 X2 = (dr X0 X0) ◇ (((wf X0 X1) ◇ X2) ◇ X0) := by
    first | exact superpose ef40 ef2553 | exact superpose ef2553 ef40
  have ef2725 (X0 X1 X2 : G) : dr X1 X2 = wf X0 ((wf X0 X1) ◇ X2) := by
    first | exact superpose ef19 ef2679 | exact superpose ef2679 ef19
  have ef3154 (X0 X1 X2 X3 : G) :
      dl (dr X3 X3) X1 = (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (wf X3 X2)))) ◇ X0 := by
    first | exact superpose ef91 ef30 | exact superpose ef30 ef91
  have ef3206 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl (dr (wf X3 X2) (X2 ◇ X3)) X1 := by
    first | exact superpose ef461 ef3154 | exact superpose ef3154 ef461
  have ef3274 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl ((X3 ◇ (wf X3 X2)) ◇ X2) X1 := by
    first | exact superpose ef40 ef3206 | exact superpose ef3206 ef40
  have ef3326 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = (X1 ◇ (dl (wf X3 X2) X2)) ◇ X3 := by
    first | exact superpose ef306 ef3274 | exact superpose ef3274 ef306
  have ef3463 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef23 ef156 | exact superpose ef156 ef23
  have ef3483 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef156 ef23 | exact superpose ef23 ef156
  have ef3519 (X0 X1 X2 X3 X4 : G) :
      (dl ((X3 ◇ X4) ◇ X2) X1) ◇ X0 = (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef156 ef69 | exact superpose ef69 ef156
  have ef3523 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef156 ef26 | exact superpose ef26 ef156
  have ef3525 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (dr (dr X0 X0) X1) := by
    first | exact superpose ef156 ef90 | exact superpose ef90 ef156
  have ef3528 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef112 ef3525 | exact superpose ef3525 ef112
  have ef3533 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) = ((X1 ◇ (dl X4 X2)) ◇ X3) ◇ X0 := by
    first | exact superpose ef306 ef3519 | exact superpose ef3519 ef306
  have ef3564 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef40 ef3483 | exact superpose ef3483 ef40
  have ef3578 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1903 ef3463 | exact superpose ef3463 ef1903
  have ef3584 (X0 X1 X2 : G) : dl (wf X0 X1) X2 = dl (wf X0 X2) X1 := by
    first | exact superpose ef30 ef3528 | exact superpose ef3528 ef30
  have ef3614 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef40 ef3578 | exact superpose ef3578 ef40
  have ef3631 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef107 ef3614 | exact superpose ef3614 ef107
  have ef3717 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = dr X3 (((X2 ◇ X1) ◇ X0) ◇ (dr X1 X1)) := by
    first | exact superpose ef92 ef23 | exact superpose ef23 ef92
  have ef3776 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = ((dr X1 X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef3717 | exact superpose ef3717 ef40
  have ef3858 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (dl X3 ((X2 ◇ X1) ◇ X0))) := by
    first | exact superpose ef830 ef3776 | exact superpose ef3776 ef830
  have ef3919 (X0 X1 X2 X3 : G) : (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    first | exact superpose ef291 ef3858 | exact superpose ef3858 ef291
  have ef4054 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef61 ef164 | exact superpose ef164 ef61
  have ef4070 (X0 X1 : G) : dl X0 X1 = wf X0 (dl X1 (dr X0 X0)) := by
    first | exact superpose ef164 ef19 | exact superpose ef19 ef164
  have ef4079 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef164 ef18 | exact superpose ef18 ef164
  have ef4155 (X0 X1 : G) : dl X0 X1 = wf X0 (X0 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef129 ef4070 | exact superpose ef4070 ef129
  have ef4164 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef644 ef4054 | exact superpose ef4054 ef644
  have ef4199 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1793 ef4164 | exact superpose ef4164 ef1793
  have ef4225 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef900 ef4199 | exact superpose ef4199 ef900
  have ef4734 (X0 X1 : G) : dl X1 X0 = X1 ◇ (wf X1 (X1 ◇ X0)) := by
    first | exact superpose ef17 ef177 | exact superpose ef177 ef17
  have ef4765 (X0 X1 : G) : X1 ◇ (wf X1 X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef177 | exact superpose ef177 ef24
  have ef5478 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (X2 ◇ X3) = dl X3 (X1 ◇ (dr X2 X0)) := by
    first | exact superpose ef201 ef30 | exact superpose ef30 ef201
  have ef5518 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef201 ef13 | exact superpose ef13 ef201
  have ef5523 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X3 X2) X0) = X2 ◇ ((dl X0 X1) ◇ X3) := by
    first | exact superpose ef201 ef26 | exact superpose ef26 ef201
  have ef5528 (X0 X1 X2 X3 : G) : X2 ◇ ((dl X0 X1) ◇ X3) = X1 ◇ ((dl X0 X2) ◇ X3) := by
    first | exact superpose ef1781 ef5523 | exact superpose ef5523 ef1781
  have ef6622 (X0 X1 X2 : G) : X1 ◇ (dr (X2 ◇ (X2 ◇ X2)) X0) = wf X2 (dl X0 X1) := by
    first | exact superpose ef201 ef214 | exact superpose ef214 ef201
  have ef6651 (X0 X1 X2 : G) : wf X2 (dl X0 X1) = X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2) := by
    first | exact superpose ef1857 ef6622 | exact superpose ef6622 ef1857
  have ef6770 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = dl X3 (dl (X1 ◇ (X2 ◇ X0)) X2) := by
    first | exact superpose ef239 ef30 | exact superpose ef30 ef239
  have ef6848 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = (dl X2 X3) ◇ (X1 ◇ (X2 ◇ X0)) := by
    first | exact superpose ef4079 ef6770 | exact superpose ef6770 ef4079
  have ef7495 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef156 ef316 | exact superpose ef316 ef156
  have ef7503 (X0 X1 : G) : dr X0 (dr X0 X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef19 ef316 | exact superpose ef316 ef19
  have ef7544 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef105 ef7503 | exact superpose ef7503 ef105
  have ef7552 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef40 ef7495 | exact superpose ef7495 ef40
  have ef7609 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef644 ef7552 | exact superpose ef7552 ef644
  have ef7639 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef30 ef7609 | exact superpose ef7609 ef30
  have ef7878 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef337 ef72 | exact superpose ef72 ef337
  have ef7908 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef4079 ef7878 | exact superpose ef7878 ef4079
  have ef8154 (X0 X1 X2 : G) : dl X2 (wf X1 X0) = X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2) := by
    first | exact superpose ef478 ef30 | exact superpose ef30 ef478
  have ef8163 (X0 X1 X2 X3 : G) :
      (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2)) = X3 := by
    first | exact superpose ef478 ef67 | exact superpose ef67 ef478
  have ef8205 (X0 X1 X2 X3 : G) :
      X2 ◇ (X2 ◇ (X2 ◇ (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)))) = X3 := by
    first | exact superpose ef957 ef8163 | exact superpose ef8163 ef957
  have ef8238 (X0 X1 X2 X3 : G) : (wf X2 X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (wf X2 X0))) = X3 := by
    first | exact superpose ef3919 ef8205 | exact superpose ef8205 ef3919
  have ef8263 (X0 X2 X3 : G) : (wf X2 X3) ◇ (dl (wf X2 X0) X0) = X3 := by
    first | exact superpose ef30 ef8238 | exact superpose ef8238 ef30
  have ef9083 (X0 X1 : G) : wf X1 (X1 ◇ X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef690 | exact superpose ef690 ef24
  have ef9101 (X0 X1 : G) : X1 ◇ (wf X1 X0) = wf X1 (X1 ◇ X0) := by
    first | exact superpose ef4765 ef9083 | exact superpose ef9083 ef4765
  have ef11337 (X0 X1 X2 : G) : (dr X0 X0) ◇ (X1 ◇ X0) = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef1004 ef23 | exact superpose ef23 ef1004
  have ef11417 (X0 X1 X2 : G) : wf X0 X1 = dr X1 (dl (wf X0 X2) X2) := by
    first | exact superpose ef19 ef11337 | exact superpose ef11337 ef19
  have ef13289 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = dr X3 ((dr X1 X0) ◇ X2) := by
    first | exact superpose ef2327 ef156 | exact superpose ef156 ef2327
  have ef13311 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = (X2 ◇ X3) ◇ (dr X1 X0) := by
    first | exact superpose ef40 ef13289 | exact superpose ef13289 ef40
  have ef16281 (X0 X1 X2 X3 X4 : G) :
      dl ((X0 ◇ X4) ◇ (dr X2 X3)) X1 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef124 ef30 | exact superpose ef30 ef124
  have ef16386 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X1 ◇ (dl X4 (dr X2 X3))) ◇ X0 := by
    first | exact superpose ef306 ef16281 | exact superpose ef16281 ef306
  have ef16596 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (dr X2 X3) ◇ (dr (X0 ◇ X1) X4) := by
    first | exact superpose ef5518 ef16386 | exact superpose ef16386 ef5518
  have ef19220 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = dr (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) X4 := by
    first | exact superpose ef126 ef109 | exact superpose ef109 ef126
  have ef19366 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (dl X4 (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0 := by
    first | exact superpose ef1777 ef19220 | exact superpose ef19220 ef1777
  have ef19571 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (X1 ◇ (X2 ◇ X3)) ◇ (dr X4 (dl X0 X3)) := by
    first | exact superpose ef7908 ef19366 | exact superpose ef19366 ef7908
  have ef20543 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = dl X1 ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef131 ef538 | exact superpose ef538 ef131
  have ef20568 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = (X3 ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X2) ◇ X1) := by
    first | exact superpose ef291 ef20543 | exact superpose ef20543 ef291
  have ef22046 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (X3 ◇ X4) = ((X1 ◇ (dr X2 X0)) ◇ X3) ◇ (X2 ◇ X4) := by
    first | exact superpose ef201 ef138 | exact superpose ef138 ef201
  have ef23864 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (dr (dl X0 X0) X1) := by
    first | exact superpose ef2410 ef1793 | exact superpose ef1793 ef2410
  have ef23865 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (X0 ◇ (dr X1 X0)) := by
    first | exact superpose ef1793 ef23864 | exact superpose ef23864 ef1793
  have ef23973 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ X3 := by
    first | exact superpose ef139 ef139
  have ef23983 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = ((X5 ◇ (dr X0 X1)) ◇ X4) ◇ (X0 ◇ (dr X2 X3)) := by
    first | exact superpose ef109 ef139 | exact superpose ef139 ef109
  have ef24400 (X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = (dl X1 X5) ◇ (X4 ◇ (dr X2 X3)) := by
    first | exact superpose ef22046 ef23983 | exact superpose ef23983 ef22046
  have ef24408 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((dr X0 X1) ◇ (dr (X4 ◇ X5) X2)) ◇ X3 := by
    first | exact superpose ef16596 ef23973 | exact superpose ef23973 ef16596
  have ef24565 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = X0 ◇ (X1 ◇ (dl (dr (X4 ◇ X5) X2) X3)) := by
    first | exact superpose ef830 ef24408 | exact superpose ef24408 ef830
  have ef26311 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇
      ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef167 ef99 | exact superpose ef99 ef167
  have ef26424 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) X2) X2)) := by
    first | exact superpose ef24565 ef26311 | exact superpose ef26311 ef24565
  have ef26635 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr X2 X2) ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4))) := by
    first | exact superpose ef7639 ef26424 | exact superpose ef26424 ef7639
  have ef26809 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (((dl X2 X3) ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X3) ◇ (dr X2 X2)))) := by
    first | exact superpose ef291 ef26635 | exact superpose ef26635 ef291
  have ef26934 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ (dl ((dl X2 X3) ◇ (X4 ◇ X0)) X2))) := by
    first | exact superpose ef3564 ef26809 | exact superpose ef26809 ef3564
  have ef27024 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (dr (dl X2 X3) X2)))) := by
    first | exact superpose ef644 ef26934 | exact superpose ef26934 ef644
  have ef27090 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((dl X3 (dr (dl X2 X3) X2)) ◇ (dr X0 X2))) := by
    first | exact superpose ef20568 ef27024 | exact superpose ef27024 ef20568
  have ef27136 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ (((dl X2 X3) ◇ (X2 ◇ X3)) ◇ (dr X0 X2))) := by
    first | exact superpose ef129 ef27090 | exact superpose ef27090 ef129
  have ef27170 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (dr X0 (dl X2 X3)))) := by
    first | exact superpose ef13311 ef27136 | exact superpose ef27136 ef13311
  have ef27198 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := by
    first | exact superpose ef19571 ef27170 | exact superpose ef27170 ef19571
  have ef27224 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (wf X2 (dl X0 X1)) := by
    first | exact superpose ef6651 ef27198 | exact superpose ef27198 ef6651
  have ef27346 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = dr (dl (wf X0 X1) X2) X3 := by
    first | exact superpose ef3584 ef1793 | exact superpose ef1793 ef3584
  have ef27355 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = X2 ◇ (dr X3 (wf X0 X1)) := by
    first | exact superpose ef1793 ef27346 | exact superpose ef27346 ef1793
  have ef29160 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef3631 ef969 | exact superpose ef969 ef3631
  have ef30917 (X0 X1 X2 X3 : G) : (dl X0 (wf X1 X2)) ◇ X3 = dl (wf X1 (dl X3 X0)) X2 := by
    first | exact superpose ef4079 ef3584 | exact superpose ef3584 ef4079
  have ef32561 (X0 X1 : G) : wf (X0 ◇ X1) X0 = dl (X0 ◇ X1) (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef12 ef4155 | exact superpose ef4155 ef12
  have ef32611 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ ((dr X1 X1) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef460 ef32561 | exact superpose ef32561 ef460
  have ef32693 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ (wf X1 X0) := by
    first | exact superpose ef19 ef32611 | exact superpose ef32611 ef19
  have ef33251 (X0 X1 X2 X3 X4 : G) :
      dl X4 (dl X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 ◇ ((dr X2 X3) ◇ X4) := by
    first | exact superpose ef243 ef30 | exact superpose ef30 ef243
  have ef33383 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = (dl (X2 ◇ (X3 ◇ (X0 ◇ X1))) X4) ◇ X1 := by
    first | exact superpose ef4079 ef33251 | exact superpose ef33251 ef4079
  have ef33637 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = ((X3 ◇ (X0 ◇ X1)) ◇ (dr X2 X4)) ◇ X1 := by
    first | exact superpose ef644 ef33383 | exact superpose ef33383 ef644
  have ef33861 (X0 X2 X3 X4 : G) : X0 ◇ ((dr X2 X3) ◇ X4) = X0 ◇ ((dr X2 X4) ◇ X3) := by
    first | exact superpose ef139 ef33637 | exact superpose ef33637 ef139
  have ef34354 (X0 X1 X2 X3 : G) : X2 ◇ (dl X0 (X3 ◇ X1)) = X3 ◇ (dl X2 (X0 ◇ X1)) := by
    first | exact superpose ef4225 ef4225
  have ef34509 (X0 X1 X2 X3 : G) :
      ((X2 ◇ ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2)) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) (X0 ◇ X1) := by
    first | exact superpose ef4225 ef99 | exact superpose ef99 ef4225
  have ef34531 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) (X0 ◇ X1) := by
    first | exact superpose ef7908 ef34509 | exact superpose ef34509 ef7908
  have ef34668 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 (dl X2 (X2 ◇ X3))) (dl X0 X1)) := by
    first | exact superpose ef27224 ef34531 | exact superpose ef34531 ef27224
  have ef34752 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 X3))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef18 ef34668 | exact superpose ef34668 ef18
  have ef34797 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) := by
    first | exact superpose ef470 ef34752 | exact superpose ef34752 ef470
  have ef34825 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) := by
    first | exact superpose ef7908 ef34797 | exact superpose ef34797 ef7908
  have ef34846 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      (dl (dr (X1 ◇ (dr X0 X3)) X3) (dl X2 (X2 ◇ X3))) := by
    first | exact superpose ef3564 ef34825 | exact superpose ef34825 ef3564
  have ef34862 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      ((dl (X2 ◇ X3) (dr (X1 ◇ (dr X0 X3)) X3)) ◇ X2) := by
    first | exact superpose ef4079 ef34846 | exact superpose ef34846 ef4079
  have ef34873 (X0 X1 X3 : G) :
      (X0 ◇ X1) ◇ (dl (dr (X1 ◇ (dr X0 X3)) X3) X3) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef538 ef34862 | exact superpose ef34862 ef538
  have ef34879 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dl (dr X3 X3) (X1 ◇ (dr X0 X3))) := by
    first | exact superpose ef7639 ef34873 | exact superpose ef34873 ef7639
  have ef34883 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ (dl (X0 ◇ X1) ((dr X3 X3) ◇ (dr X0 X3))) := by
    first | exact superpose ef34354 ef34879 | exact superpose ef34879 ef34354
  have ef34887 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((dl X3 (dr X3 X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef5478 ef34883 | exact superpose ef34883 ef5478
  have ef34890 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef129 ef34887 | exact superpose ef34887 ef129
  have ef34893 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = dl (X0 ◇ (X0 ◇ X1)) (wf X3 X1) := by
    first | exact superpose ef8154 ef34890 | exact superpose ef34890 ef8154
  have ef34895 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dr X0 (wf X3 X1)) := by
    first | exact superpose ef644 ef34893 | exact superpose ef34893 ef644
  have ef34897 (X0 X1 X3 : G) :
      X1 ◇ (dr X0 (wf X3 (X0 ◇ X1))) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef27355 ef34895 | exact superpose ef34895 ef27355
  have ef36872 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = ((((wf X0 (X0 ◇ X1)) ◇ X2) ◇ (dl X2 X0)) ◇ (dl X0 X1)) ◇ X0 := by
    first | exact superpose ef4734 ef104 | exact superpose ef104 ef4734
  have ef37003 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = (dr (dl X2 X0) X0) ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ X2)) := by
    first | exact superpose ef470 ef36872 | exact superpose ef36872 ef470
  have ef37165 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (dr (dl X2 X0) X0))) := by
    first | exact superpose ef957 ef37003 | exact superpose ef37003 ef957
  have ef37308 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (X0 ◇ (dr X0 X2)))) := by
    first | exact superpose ef1793 ef37165 | exact superpose ef37165 ef1793
  have ef37420 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((wf X0 (X0 ◇ X1)) ◇ X1)) := by
    first | exact superpose ef6848 ef37308 | exact superpose ef37308 ef6848
  have ef37501 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((X0 ◇ (wf X0 X1)) ◇ X1)) := by
    first | exact superpose ef9101 ef37420 | exact superpose ef37420 ef9101
  have ef37564 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ (dl X1 (dl X2 (wf X0 X1))) := by
    first | exact superpose ef1808 ef37501 | exact superpose ef37501 ef1808
  have ef37612 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ ((dl (wf X0 X1) X1) ◇ X2) := by
    first | exact superpose ef4079 ef37564 | exact superpose ef37564 ef4079
  have ef40206 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = dl (dl X0 X1) (dl X4 (dr X2 X3)) := by
    first | exact superpose ef287 ef325 | exact superpose ef325 ef287
  have ef40243 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = (dl (dr X2 X3) (dl X0 X1)) ◇ X4 := by
    first | exact superpose ef4079 ef40206 | exact superpose ef40206 ef4079
  have ef40517 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ ((dr X4 (dl X0 X1)) ◇ X2) := by
    first | exact superpose ef3523 ef40243 | exact superpose ef40243 ef3523
  have ef40756 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ (X0 ◇ (dl (dr X4 X2) X1)) := by
    first | exact superpose ef29160 ef40517 | exact superpose ef40517 ef29160
  have ef42100 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((X4 ◇ (dl X1 (dl X0 X3))) ◇ X2) := by
    first | exact superpose ef1765 ef291 | exact superpose ef291 ef1765
  have ef42217 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X1 ◇ X2) ◇ (wf X3 X4)) = dl (wf X3 ((X2 ◇ X0) ◇ X1)) X4 := by
    first | exact superpose ef291 ef3584 | exact superpose ef3584 ef291
  have ef42320 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((dl X0 X3) ◇ (dr (X2 ◇ X4) X1)) := by
    first | exact superpose ef5518 ef42100 | exact superpose ef42100 ef5518
  have ef42460 (X0 X1 X2 X4 : G) : dl (dr (X2 ◇ X4) X1) X0 = dl X2 ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef164 ef42320 | exact superpose ef42320 ef164
  have ef43141 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (dl (X0 ◇ X1) X2) := by
    first | exact superpose ef4734 ef292 | exact superpose ef292 ef4734
  have ef43387 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) := by
    first | exact superpose ef644 ef43141 | exact superpose ef43141 ef644
  have ef43629 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (wf (X0 ◇ X1) (X3 ◇ X0))) := by
    first | exact superpose ef42217 ef43387 | exact superpose ef43387 ef42217
  have ef43837 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (wf X1 (dl X3 X0)))) := by
    first | exact superpose ef27224 ef43629 | exact superpose ef43629 ef27224
  have ef43981 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ (dl (wf X1 (dl X3 X0)) X2) := by
    first | exact superpose ef30 ef43837 | exact superpose ef43837 ef30
  have ef44072 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((dl X0 (wf X1 X2)) ◇ X3) := by
    first | exact superpose ef30917 ef43981 | exact superpose ef43981 ef30917
  have ef46365 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (((X0 ◇ X0) ◇ (dl (wf X0 X1) X1)) ◇ X0) ◇
      X2 := by
    first | exact superpose ef7544 ef99 | exact superpose ef99 ef7544
  have ef46594 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (X1 ◇ X0) ◇
      ((dr X2 (X0 ◇ X0)) ◇ (wf X0 X1)) := by
    first | exact superpose ef3533 ef46365 | exact superpose ef46365 ef3533
  have ef46727 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 (X0 ◇ X0)) (dr X0 X0) := by
    first | exact superpose ef106 ef46594 | exact superpose ef46594 ef106
  have ef46833 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef105 ef46727 | exact superpose ef46727 ef105
  have ef46914 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef33861 ef46833 | exact superpose ef46833 ef33861
  have ef46968 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 X0) X0 := by
    first | exact superpose ef23 ef46914 | exact superpose ef46914 ef23
  have ef47007 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) := by
    first | exact superpose ef1781 ef46968 | exact superpose ef46968 ef1781
  have ef47035 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) ((dr X0 X0) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef470 ef47007 | exact superpose ef47007 ef470
  have ef47056 (X0 X1 X2 : G) : (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (wf X0 X2) := by
    first | exact superpose ef19 ef47035 | exact superpose ef47035 ef19
  have ef66642 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = (X5 ◇ (X4 ◇ (dr X0 X1))) ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef109 ef461 | exact superpose ef461 ef109
  have ef67346 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) := by
    first | exact superpose ef957 ef66642 | exact superpose ef66642 ef957
  have ef67702 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = dl X0 ((dr X5 X4) ◇ (dr X2 X3)) := by
    first | exact superpose ef42460 ef67346 | exact superpose ef67346 ef42460
  have ef67994 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (dl X3 (dr X5 X4)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef5478 ef67702 | exact superpose ef67702 ef5478
  have ef68236 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (X5 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef129 ef67994 | exact superpose ef67994 ef129
  have ef69488 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = (((dr X0 X1) ◇ (X2 ◇ X3)) ◇ X5) ◇ X4 := by
    first | exact superpose ef470 ef470
  have ef70449 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (dr X4 (dr X0 X1)) X3)) := by
    first | exact superpose ef40756 ef69488 | exact superpose ef69488 ef40756
  have ef70975 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (X1 ◇ (X4 ◇ X0)) X3)) := by
    first | exact superpose ef105 ef70449 | exact superpose ef70449 ef105
  have ef71379 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ ((X4 ◇ X0) ◇ (dr X1 X3))) := by
    first | exact superpose ef644 ef70975 | exact superpose ef70975 ef644
  have ef76676 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (wf X0 (X0 ◇ X1))) := by
    first | exact superpose ef4734 ef9101 | exact superpose ef9101 ef4734
  have ef76873 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (X0 ◇ (wf X0 X1))) := by
    first | exact superpose ef9101 ef76676 | exact superpose ef76676 ef9101
  have ef76956 (X0 X1 : G) : wf X0 (dl X0 X1) = dl X0 (wf X0 X1) := by
    first | exact superpose ef4734 ef76873 | exact superpose ef76873 ef4734
  have ef106495 (X0 X1 X2 : G) :
      wf X0 (wf X1 X0) = (wf X1 X0) ◇ (wf (dl (wf X1 X2) X2) (wf X1 X0)) := by
    first | exact superpose ef8263 ef32693 | exact superpose ef32693 ef8263
  have ef106565 (X0 X1 : G) : wf X0 (wf X1 X0) = (wf X1 X0) ◇ ((dl X1 X1) ◇ X0) := by
    first | exact superpose ef47056 ef106495 | exact superpose ef106495 ef47056
  have ef106664 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef5528 ef106565 | exact superpose ef106565 ef5528
  have ef106737 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef106664 | exact superpose ef106664 ef76956
  have ef151645 (X0 X1 X2 : G) :
      X0 ◇ ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) =
      dl (dr (X0 ◇ (wf X0 X1)) (X0 ◇ (wf X0 X1))) X1 := by
    first | exact superpose ef3326 ef1015 | exact superpose ef1015 ef3326
  have ef151792 (X0 X1 X2 : G) :
      dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) = X0 ◇
      ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) := by
    first | exact superpose ef7639 ef151645 | exact superpose ef151645 ef7639
  have ef152128 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef37612 ef151792 | exact superpose ef151792 ef37612
  have ef152448 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (dr X1 (X0 ◇ (wf X0 X1)))) := by
    first | exact superpose ef993 ef152128 | exact superpose ef152128 ef993
  have ef152735 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (((wf X0 X1) ◇ X1) ◇ X0)) := by
    first | exact superpose ef40 ef152448 | exact superpose ef152448 ef40
  have ef152970 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (dr X0 (wf X0 X1)))) := by
    first | exact superpose ef71379 ef152735 | exact superpose ef152735 ef71379
  have ef153148 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (dr X0 (wf X0 (X0 ◇ X1))))) := by
    first | exact superpose ef27355 ef152970 | exact superpose ef152970 ef27355
  have ef153300 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (wf (dr X0 X0) (dl X0 X1)))) := by
    first | exact superpose ef34897 ef153148 | exact superpose ef153148 ef34897
  have ef153425 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (dr X0 X0))))) := by
    first | exact superpose ef23865 ef153300 | exact superpose ef153300 ef23865
  have ef153518 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0) := by
    first | exact superpose ef68236 ef153425 | exact superpose ef153425 ef68236
  have ef153583 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dl X1 X0) ◇ (X1 ◇ (dr X1 X0)) := by
    first | exact superpose ef24400 ef153518 | exact superpose ef153518 ef24400
  have ef153626 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef44072 ef153583 | exact superpose ef153583 ef44072
  have ef153660 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef153626 | exact superpose ef153626 ef76956
  have ef153685 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef106737 ef153660 | exact superpose ef153660 ef106737
  have ef153704 (X0 X1 : G) : wf (wf X0 X1) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef18 ef153685 | exact superpose ef153685 ef18
  have ef155697 (X0 X1 X2 : G) : dr X0 X2 = wf (wf X0 X1) ((wf X0 (wf X1 X0)) ◇ X2) := by
    first | exact superpose ef153704 ef2725 | exact superpose ef2725 ef153704
  have ef714672 (X0 X1 X2 : G) : wf (wf X1 X0) (wf X0 X1) = dr X1 (dl (wf X1 X2) X2) := by
    first | exact superpose ef8263 ef155697 | exact superpose ef155697 ef8263
  have ef714687 (X0 X1 : G) : wf X1 X1 = wf (wf X1 X0) (wf X0 X1) := by
    first | exact superpose ef11417 ef714672 | exact superpose ef714672 ef11417
  have ef714723 : wf x x ≠ wf x x := by
    first | exact superpose ef714687 ef20 | exact superpose ef20 ef714687
  exact absurd rfl ef714723

theorem Equation3667_termStructuralFromFin_Equation898_qdiv :
    Law3667.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.rdv (.var 0) (.var 0)) (.op (.var 1) (.var 0))) (.rdv (.ldv (.var 0) (.var 1)) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3667.models_iff]
    exact fun x y ↦
      @qaux898_3667_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_56R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_56L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

set_option maxHeartbeats 1400000 in
/-- Equation 4380 `x ◇ (x ◇ x) = (x ◇ x) ◇ x` holds of the operation `x □ y := ((x/x)◇(y◇x))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_4380_56 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (x : G) :
    wf x (wf x x) = wf (wf x x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef20 : wf x (wf x x) ≠ wf (wf x x) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef37 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef64 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef67 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef14 ef14
  have ef69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef70 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef82 (X0 X1 : G) : wf X1 (dr X0 X1) = (dr X1 X1) ◇ X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef85 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (dr ((X0 ◇ X1) ◇ (X1 ◇ X2)) ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇
      X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef87 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = (dr (X1 ◇ X2) (X1 ◇ X2)) ◇ X0 := by
    first | exact superpose ef14 ef19 | exact superpose ef19 ef14
  have ef88 (X0 X1 : G) : dr X0 X0 = (X0 ◇ (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef90 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ ((X2 ◇ (dr X0 X0)) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef91 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1))) ◇ (dr X0 X0) = X2 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef92 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (dr X0 X0)) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef99 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0 := by
    first | exact superpose ef40 ef87 | exact superpose ef87 ef40
  have ef101 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef40 ef85 | exact superpose ef85 ef40
  have ef104 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = (((X1 ◇ X2) ◇ (dl X2 X0)) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef30 ef101 | exact superpose ef101 ef30
  have ef105 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef106 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1)) = dr X2 (dr X0 X0) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef107 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef109 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef23 ef23
  have ef110 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef13 ef23 | exact superpose ef23 ef13
  have ef111 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef14 ef23 | exact superpose ef23 ef14
  have ef112 (X0 X1 : G) : X0 ◇ (wf X0 X1) = dr (dr X0 X0) X1 := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef124 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (dr X0 X1)) = X3 := by
    first | exact superpose ef23 ef12 | exact superpose ef12 ef23
  have ef126 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef129 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef131 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef138 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef40 ef111 | exact superpose ef111 ef40
  have ef139 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef40 ef110 | exact superpose ef110 ef40
  have ef149 (X0 X1 : G) : X0 ◇ (wf X0 (dl X1 (dr X0 X0))) = X1 := by
    first | exact superpose ef19 ef24 | exact superpose ef24 ef19
  have ef156 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef164 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef167 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ ((dl X0 X3) ◇ (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef24 ef14 | exact superpose ef14 ef24
  have ef177 (X0 X1 : G) : X0 ◇ (wf X0 (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef129 ef149 | exact superpose ef149 ef129
  have ef194 (X0 X1 : G) : wf X1 (X0 ◇ (dr X1 (dr X1 X1))) = X0 := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef201 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef26 ef18 | exact superpose ef18 ef26
  have ef214 (X0 X1 : G) : wf X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    first | exact superpose ef105 ef194 | exact superpose ef194 ef105
  have ef239 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef13 ef27 | exact superpose ef27 ef13
  have ef243 (X0 X1 X2 X3 : G) : (dl X2 (X0 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef27 | exact superpose ef27 ef23
  have ef254 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef256 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef287 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef291 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef292 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef30 ef30
  have ef302 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef306 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef316 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef322 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef30 ef14 | exact superpose ef14 ef30
  have ef325 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef30 ef18 | exact superpose ef18 ef30
  have ef337 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef256 ef322 | exact superpose ef322 ef256
  have ef444 (X0 X1 : G) : (wf X0 X1) ◇ (dr X0 (dr X0 X0)) = X1 := by
    first | exact superpose ef19 ef36 | exact superpose ef36 ef19
  have ef458 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef36 ef23 | exact superpose ef23 ef36
  have ef460 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef461 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef470 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef40 ef458 | exact superpose ef458 ef40
  have ef478 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef105 ef444 | exact superpose ef444 ef105
  have ef538 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef37 ef27 | exact superpose ef27 ef37
  have ef644 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef649 (X0 X1 : G) : wf X1 (dl (X1 ◇ X0) (dr X1 X1)) = X0 := by
    first | exact superpose ef61 ef19 | exact superpose ef19 ef61
  have ef690 (X0 X1 : G) : wf X1 (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    first | exact superpose ef129 ef649 | exact superpose ef649 ef129
  have ef830 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef23 ef64 | exact superpose ef64 ef23
  have ef849 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef64 ef30 | exact superpose ef30 ef64
  have ef878 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef302 ef849 | exact superpose ef849 ef302
  have ef900 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef644 ef878 | exact superpose ef878 ef644
  have ef924 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef927 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef955 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef291 ef927 | exact superpose ef927 ef291
  have ef957 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef129 ef924 | exact superpose ef924 ef129
  have ef969 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef955 | exact superpose ef955 ef30
  have ef993 (X0 X1 X2 : G) : dl X2 (X0 ◇ (wf X0 X1)) = (dr X0 X0) ◇ (X1 ◇ X2) := by
    first | exact superpose ef88 ef30 | exact superpose ef30 ef88
  have ef999 (X0 X1 X2 : G) : dr X2 (dr X0 X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef88 ef40 | exact superpose ef40 ef88
  have ef1015 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef105 ef999 | exact superpose ef999 ef105
  have ef1765 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef17 ef107 | exact superpose ef107 ef17
  have ef1777 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef14 ef107 | exact superpose ef107 ef14
  have ef1778 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef107 | exact superpose ef107 ef30
  have ef1780 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef36 ef107 | exact superpose ef107 ef36
  have ef1781 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef107 | exact superpose ef107 ef15
  have ef1793 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1806 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1808 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = (dr X0 X1) ◇ ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef107 ef30 | exact superpose ef30 ef107
  have ef1857 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef129 ef1780 | exact superpose ef1780 ef129
  have ef1859 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef969 ef1778 | exact superpose ef1778 ef969
  have ef1890 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef254 ef1859 | exact superpose ef1859 ef254
  have ef1903 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1890 | exact superpose ef1890 ef23
  have ef1972 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) ◇ (X0 ◇ X1) = X3 := by
    first | exact superpose ef26 ef70 | exact superpose ef70 ef26
  have ef2109 (X0 X2 X3 X4 : G) : dr X0 (dl X2 (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) = X3 := by
    first | exact superpose ef256 ef1972 | exact superpose ef1972 ef256
  have ef2210 (X0 X2 X3 X4 : G) : dr X0 ((X0 ◇ (dr X4 X2)) ◇ ((dr X4 X3) ◇ X2)) = X3 := by
    first | exact superpose ef460 ef2109 | exact superpose ef2109 ef460
  have ef2281 (X0 X2 X3 X4 : G) : (((dr X4 X3) ◇ X2) ◇ X0) ◇ (X0 ◇ (dr X4 X2)) = X3 := by
    first | exact superpose ef40 ef2210 | exact superpose ef2210 ef40
  have ef2327 (X2 X3 X4 : G) : dl (dr X4 X2) ((dr X4 X3) ◇ X2) = X3 := by
    first | exact superpose ef30 ef2281 | exact superpose ef2281 ef30
  have ef2378 (X0 X1 : G) : wf (dr X0 X0) X1 = (X0 ◇ (wf X0 (dr X0 X0))) ◇ (X1 ◇ (dr X0 X0)) := by
    first | exact superpose ef112 ef19 | exact superpose ef19 ef112
  have ef2397 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 (wf X0 (dr X0 X0))) := by
    first | exact superpose ef1806 ef2378 | exact superpose ef2378 ef1806
  have ef2406 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 ((dr X0 X0) ◇ X0)) := by
    first | exact superpose ef82 ef2397 | exact superpose ef2397 ef82
  have ef2410 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 X0) := by
    first | exact superpose ef15 ef2406 | exact superpose ef2406 ef15
  have ef3154 (X0 X1 X2 X3 : G) :
      dl (dr X3 X3) X1 = (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (wf X3 X2)))) ◇ X0 := by
    first | exact superpose ef91 ef30 | exact superpose ef30 ef91
  have ef3206 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl (dr (wf X3 X2) (X2 ◇ X3)) X1 := by
    first | exact superpose ef461 ef3154 | exact superpose ef3154 ef461
  have ef3274 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl ((X3 ◇ (wf X3 X2)) ◇ X2) X1 := by
    first | exact superpose ef40 ef3206 | exact superpose ef3206 ef40
  have ef3326 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = (X1 ◇ (dl (wf X3 X2) X2)) ◇ X3 := by
    first | exact superpose ef306 ef3274 | exact superpose ef3274 ef306
  have ef3463 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef23 ef156 | exact superpose ef156 ef23
  have ef3483 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef156 ef23 | exact superpose ef23 ef156
  have ef3519 (X0 X1 X2 X3 X4 : G) :
      (dl ((X3 ◇ X4) ◇ X2) X1) ◇ X0 = (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef156 ef69 | exact superpose ef69 ef156
  have ef3523 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef156 ef26 | exact superpose ef26 ef156
  have ef3525 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (dr (dr X0 X0) X1) := by
    first | exact superpose ef156 ef90 | exact superpose ef90 ef156
  have ef3528 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef112 ef3525 | exact superpose ef3525 ef112
  have ef3533 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) = ((X1 ◇ (dl X4 X2)) ◇ X3) ◇ X0 := by
    first | exact superpose ef306 ef3519 | exact superpose ef3519 ef306
  have ef3564 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef40 ef3483 | exact superpose ef3483 ef40
  have ef3578 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1903 ef3463 | exact superpose ef3463 ef1903
  have ef3584 (X0 X1 X2 : G) : dl (wf X0 X1) X2 = dl (wf X0 X2) X1 := by
    first | exact superpose ef30 ef3528 | exact superpose ef3528 ef30
  have ef3614 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef40 ef3578 | exact superpose ef3578 ef40
  have ef3631 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef107 ef3614 | exact superpose ef3614 ef107
  have ef3717 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = dr X3 (((X2 ◇ X1) ◇ X0) ◇ (dr X1 X1)) := by
    first | exact superpose ef92 ef23 | exact superpose ef23 ef92
  have ef3776 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = ((dr X1 X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef3717 | exact superpose ef3717 ef40
  have ef3858 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (dl X3 ((X2 ◇ X1) ◇ X0))) := by
    first | exact superpose ef830 ef3776 | exact superpose ef3776 ef830
  have ef3919 (X0 X1 X2 X3 : G) : (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    first | exact superpose ef291 ef3858 | exact superpose ef3858 ef291
  have ef4054 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef61 ef164 | exact superpose ef164 ef61
  have ef4070 (X0 X1 : G) : dl X0 X1 = wf X0 (dl X1 (dr X0 X0)) := by
    first | exact superpose ef164 ef19 | exact superpose ef19 ef164
  have ef4079 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef164 ef18 | exact superpose ef18 ef164
  have ef4155 (X0 X1 : G) : dl X0 X1 = wf X0 (X0 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef129 ef4070 | exact superpose ef4070 ef129
  have ef4164 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef644 ef4054 | exact superpose ef4054 ef644
  have ef4199 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1793 ef4164 | exact superpose ef4164 ef1793
  have ef4225 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef900 ef4199 | exact superpose ef4199 ef900
  have ef4734 (X0 X1 : G) : dl X1 X0 = X1 ◇ (wf X1 (X1 ◇ X0)) := by
    first | exact superpose ef17 ef177 | exact superpose ef177 ef17
  have ef4765 (X0 X1 : G) : X1 ◇ (wf X1 X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef177 | exact superpose ef177 ef24
  have ef5478 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (X2 ◇ X3) = dl X3 (X1 ◇ (dr X2 X0)) := by
    first | exact superpose ef201 ef30 | exact superpose ef30 ef201
  have ef5518 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef201 ef13 | exact superpose ef13 ef201
  have ef5523 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X3 X2) X0) = X2 ◇ ((dl X0 X1) ◇ X3) := by
    first | exact superpose ef201 ef26 | exact superpose ef26 ef201
  have ef5528 (X0 X1 X2 X3 : G) : X2 ◇ ((dl X0 X1) ◇ X3) = X1 ◇ ((dl X0 X2) ◇ X3) := by
    first | exact superpose ef1781 ef5523 | exact superpose ef5523 ef1781
  have ef6622 (X0 X1 X2 : G) : X1 ◇ (dr (X2 ◇ (X2 ◇ X2)) X0) = wf X2 (dl X0 X1) := by
    first | exact superpose ef201 ef214 | exact superpose ef214 ef201
  have ef6651 (X0 X1 X2 : G) : wf X2 (dl X0 X1) = X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2) := by
    first | exact superpose ef1857 ef6622 | exact superpose ef6622 ef1857
  have ef6770 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = dl X3 (dl (X1 ◇ (X2 ◇ X0)) X2) := by
    first | exact superpose ef239 ef30 | exact superpose ef30 ef239
  have ef6848 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = (dl X2 X3) ◇ (X1 ◇ (X2 ◇ X0)) := by
    first | exact superpose ef4079 ef6770 | exact superpose ef6770 ef4079
  have ef7495 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef156 ef316 | exact superpose ef316 ef156
  have ef7503 (X0 X1 : G) : dr X0 (dr X0 X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef19 ef316 | exact superpose ef316 ef19
  have ef7544 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef105 ef7503 | exact superpose ef7503 ef105
  have ef7552 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef40 ef7495 | exact superpose ef7495 ef40
  have ef7609 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef644 ef7552 | exact superpose ef7552 ef644
  have ef7639 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef30 ef7609 | exact superpose ef7609 ef30
  have ef7878 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef337 ef72 | exact superpose ef72 ef337
  have ef7908 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef4079 ef7878 | exact superpose ef7878 ef4079
  have ef8154 (X0 X1 X2 : G) : dl X2 (wf X1 X0) = X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2) := by
    first | exact superpose ef478 ef30 | exact superpose ef30 ef478
  have ef8163 (X0 X1 X2 X3 : G) :
      (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2)) = X3 := by
    first | exact superpose ef478 ef67 | exact superpose ef67 ef478
  have ef8205 (X0 X1 X2 X3 : G) :
      X2 ◇ (X2 ◇ (X2 ◇ (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)))) = X3 := by
    first | exact superpose ef957 ef8163 | exact superpose ef8163 ef957
  have ef8238 (X0 X1 X2 X3 : G) : (wf X2 X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (wf X2 X0))) = X3 := by
    first | exact superpose ef3919 ef8205 | exact superpose ef8205 ef3919
  have ef8263 (X0 X2 X3 : G) : (wf X2 X3) ◇ (dl (wf X2 X0) X0) = X3 := by
    first | exact superpose ef30 ef8238 | exact superpose ef8238 ef30
  have ef9083 (X0 X1 : G) : wf X1 (X1 ◇ X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef690 | exact superpose ef690 ef24
  have ef9101 (X0 X1 : G) : X1 ◇ (wf X1 X0) = wf X1 (X1 ◇ X0) := by
    first | exact superpose ef4765 ef9083 | exact superpose ef9083 ef4765
  have ef13289 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = dr X3 ((dr X1 X0) ◇ X2) := by
    first | exact superpose ef2327 ef156 | exact superpose ef156 ef2327
  have ef13311 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = (X2 ◇ X3) ◇ (dr X1 X0) := by
    first | exact superpose ef40 ef13289 | exact superpose ef13289 ef40
  have ef16281 (X0 X1 X2 X3 X4 : G) :
      dl ((X0 ◇ X4) ◇ (dr X2 X3)) X1 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef124 ef30 | exact superpose ef30 ef124
  have ef16386 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X1 ◇ (dl X4 (dr X2 X3))) ◇ X0 := by
    first | exact superpose ef306 ef16281 | exact superpose ef16281 ef306
  have ef16596 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (dr X2 X3) ◇ (dr (X0 ◇ X1) X4) := by
    first | exact superpose ef5518 ef16386 | exact superpose ef16386 ef5518
  have ef19220 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = dr (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) X4 := by
    first | exact superpose ef126 ef109 | exact superpose ef109 ef126
  have ef19366 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (dl X4 (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0 := by
    first | exact superpose ef1777 ef19220 | exact superpose ef19220 ef1777
  have ef19571 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (X1 ◇ (X2 ◇ X3)) ◇ (dr X4 (dl X0 X3)) := by
    first | exact superpose ef7908 ef19366 | exact superpose ef19366 ef7908
  have ef20543 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = dl X1 ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef131 ef538 | exact superpose ef538 ef131
  have ef20568 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = (X3 ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X2) ◇ X1) := by
    first | exact superpose ef291 ef20543 | exact superpose ef20543 ef291
  have ef22046 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (X3 ◇ X4) = ((X1 ◇ (dr X2 X0)) ◇ X3) ◇ (X2 ◇ X4) := by
    first | exact superpose ef201 ef138 | exact superpose ef138 ef201
  have ef23864 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (dr (dl X0 X0) X1) := by
    first | exact superpose ef2410 ef1793 | exact superpose ef1793 ef2410
  have ef23865 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (X0 ◇ (dr X1 X0)) := by
    first | exact superpose ef1793 ef23864 | exact superpose ef23864 ef1793
  have ef23973 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ X3 := by
    first | exact superpose ef139 ef139
  have ef23983 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = ((X5 ◇ (dr X0 X1)) ◇ X4) ◇ (X0 ◇ (dr X2 X3)) := by
    first | exact superpose ef109 ef139 | exact superpose ef139 ef109
  have ef24400 (X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = (dl X1 X5) ◇ (X4 ◇ (dr X2 X3)) := by
    first | exact superpose ef22046 ef23983 | exact superpose ef23983 ef22046
  have ef24408 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((dr X0 X1) ◇ (dr (X4 ◇ X5) X2)) ◇ X3 := by
    first | exact superpose ef16596 ef23973 | exact superpose ef23973 ef16596
  have ef24565 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = X0 ◇ (X1 ◇ (dl (dr (X4 ◇ X5) X2) X3)) := by
    first | exact superpose ef830 ef24408 | exact superpose ef24408 ef830
  have ef26311 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇
      ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef167 ef99 | exact superpose ef99 ef167
  have ef26424 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) X2) X2)) := by
    first | exact superpose ef24565 ef26311 | exact superpose ef26311 ef24565
  have ef26635 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr X2 X2) ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4))) := by
    first | exact superpose ef7639 ef26424 | exact superpose ef26424 ef7639
  have ef26809 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (((dl X2 X3) ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X3) ◇ (dr X2 X2)))) := by
    first | exact superpose ef291 ef26635 | exact superpose ef26635 ef291
  have ef26934 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ (dl ((dl X2 X3) ◇ (X4 ◇ X0)) X2))) := by
    first | exact superpose ef3564 ef26809 | exact superpose ef26809 ef3564
  have ef27024 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (dr (dl X2 X3) X2)))) := by
    first | exact superpose ef644 ef26934 | exact superpose ef26934 ef644
  have ef27090 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((dl X3 (dr (dl X2 X3) X2)) ◇ (dr X0 X2))) := by
    first | exact superpose ef20568 ef27024 | exact superpose ef27024 ef20568
  have ef27136 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ (((dl X2 X3) ◇ (X2 ◇ X3)) ◇ (dr X0 X2))) := by
    first | exact superpose ef129 ef27090 | exact superpose ef27090 ef129
  have ef27170 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (dr X0 (dl X2 X3)))) := by
    first | exact superpose ef13311 ef27136 | exact superpose ef27136 ef13311
  have ef27198 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := by
    first | exact superpose ef19571 ef27170 | exact superpose ef27170 ef19571
  have ef27224 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (wf X2 (dl X0 X1)) := by
    first | exact superpose ef6651 ef27198 | exact superpose ef27198 ef6651
  have ef27346 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = dr (dl (wf X0 X1) X2) X3 := by
    first | exact superpose ef3584 ef1793 | exact superpose ef1793 ef3584
  have ef27355 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = X2 ◇ (dr X3 (wf X0 X1)) := by
    first | exact superpose ef1793 ef27346 | exact superpose ef27346 ef1793
  have ef29160 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef3631 ef969 | exact superpose ef969 ef3631
  have ef30917 (X0 X1 X2 X3 : G) : (dl X0 (wf X1 X2)) ◇ X3 = dl (wf X1 (dl X3 X0)) X2 := by
    first | exact superpose ef4079 ef3584 | exact superpose ef3584 ef4079
  have ef32561 (X0 X1 : G) : wf (X0 ◇ X1) X0 = dl (X0 ◇ X1) (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef12 ef4155 | exact superpose ef4155 ef12
  have ef32611 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ ((dr X1 X1) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef460 ef32561 | exact superpose ef32561 ef460
  have ef32693 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ (wf X1 X0) := by
    first | exact superpose ef19 ef32611 | exact superpose ef32611 ef19
  have ef33251 (X0 X1 X2 X3 X4 : G) :
      dl X4 (dl X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 ◇ ((dr X2 X3) ◇ X4) := by
    first | exact superpose ef243 ef30 | exact superpose ef30 ef243
  have ef33383 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = (dl (X2 ◇ (X3 ◇ (X0 ◇ X1))) X4) ◇ X1 := by
    first | exact superpose ef4079 ef33251 | exact superpose ef33251 ef4079
  have ef33637 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = ((X3 ◇ (X0 ◇ X1)) ◇ (dr X2 X4)) ◇ X1 := by
    first | exact superpose ef644 ef33383 | exact superpose ef33383 ef644
  have ef33861 (X0 X2 X3 X4 : G) : X0 ◇ ((dr X2 X3) ◇ X4) = X0 ◇ ((dr X2 X4) ◇ X3) := by
    first | exact superpose ef139 ef33637 | exact superpose ef33637 ef139
  have ef34354 (X0 X1 X2 X3 : G) : X2 ◇ (dl X0 (X3 ◇ X1)) = X3 ◇ (dl X2 (X0 ◇ X1)) := by
    first | exact superpose ef4225 ef4225
  have ef34509 (X0 X1 X2 X3 : G) :
      ((X2 ◇ ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2)) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) (X0 ◇ X1) := by
    first | exact superpose ef4225 ef99 | exact superpose ef99 ef4225
  have ef34531 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) (X0 ◇ X1) := by
    first | exact superpose ef7908 ef34509 | exact superpose ef34509 ef7908
  have ef34668 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 (dl X2 (X2 ◇ X3))) (dl X0 X1)) := by
    first | exact superpose ef27224 ef34531 | exact superpose ef34531 ef27224
  have ef34752 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 X3))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef18 ef34668 | exact superpose ef34668 ef18
  have ef34797 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) := by
    first | exact superpose ef470 ef34752 | exact superpose ef34752 ef470
  have ef34825 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) := by
    first | exact superpose ef7908 ef34797 | exact superpose ef34797 ef7908
  have ef34846 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      (dl (dr (X1 ◇ (dr X0 X3)) X3) (dl X2 (X2 ◇ X3))) := by
    first | exact superpose ef3564 ef34825 | exact superpose ef34825 ef3564
  have ef34862 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      ((dl (X2 ◇ X3) (dr (X1 ◇ (dr X0 X3)) X3)) ◇ X2) := by
    first | exact superpose ef4079 ef34846 | exact superpose ef34846 ef4079
  have ef34873 (X0 X1 X3 : G) :
      (X0 ◇ X1) ◇ (dl (dr (X1 ◇ (dr X0 X3)) X3) X3) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef538 ef34862 | exact superpose ef34862 ef538
  have ef34879 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dl (dr X3 X3) (X1 ◇ (dr X0 X3))) := by
    first | exact superpose ef7639 ef34873 | exact superpose ef34873 ef7639
  have ef34883 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ (dl (X0 ◇ X1) ((dr X3 X3) ◇ (dr X0 X3))) := by
    first | exact superpose ef34354 ef34879 | exact superpose ef34879 ef34354
  have ef34887 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((dl X3 (dr X3 X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef5478 ef34883 | exact superpose ef34883 ef5478
  have ef34890 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef129 ef34887 | exact superpose ef34887 ef129
  have ef34893 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = dl (X0 ◇ (X0 ◇ X1)) (wf X3 X1) := by
    first | exact superpose ef8154 ef34890 | exact superpose ef34890 ef8154
  have ef34895 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dr X0 (wf X3 X1)) := by
    first | exact superpose ef644 ef34893 | exact superpose ef34893 ef644
  have ef34897 (X0 X1 X3 : G) :
      X1 ◇ (dr X0 (wf X3 (X0 ◇ X1))) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef27355 ef34895 | exact superpose ef34895 ef27355
  have ef36872 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = ((((wf X0 (X0 ◇ X1)) ◇ X2) ◇ (dl X2 X0)) ◇ (dl X0 X1)) ◇ X0 := by
    first | exact superpose ef4734 ef104 | exact superpose ef104 ef4734
  have ef37003 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = (dr (dl X2 X0) X0) ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ X2)) := by
    first | exact superpose ef470 ef36872 | exact superpose ef36872 ef470
  have ef37165 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (dr (dl X2 X0) X0))) := by
    first | exact superpose ef957 ef37003 | exact superpose ef37003 ef957
  have ef37308 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (X0 ◇ (dr X0 X2)))) := by
    first | exact superpose ef1793 ef37165 | exact superpose ef37165 ef1793
  have ef37420 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((wf X0 (X0 ◇ X1)) ◇ X1)) := by
    first | exact superpose ef6848 ef37308 | exact superpose ef37308 ef6848
  have ef37501 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((X0 ◇ (wf X0 X1)) ◇ X1)) := by
    first | exact superpose ef9101 ef37420 | exact superpose ef37420 ef9101
  have ef37564 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ (dl X1 (dl X2 (wf X0 X1))) := by
    first | exact superpose ef1808 ef37501 | exact superpose ef37501 ef1808
  have ef37612 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ ((dl (wf X0 X1) X1) ◇ X2) := by
    first | exact superpose ef4079 ef37564 | exact superpose ef37564 ef4079
  have ef40206 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = dl (dl X0 X1) (dl X4 (dr X2 X3)) := by
    first | exact superpose ef287 ef325 | exact superpose ef325 ef287
  have ef40243 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = (dl (dr X2 X3) (dl X0 X1)) ◇ X4 := by
    first | exact superpose ef4079 ef40206 | exact superpose ef40206 ef4079
  have ef40517 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ ((dr X4 (dl X0 X1)) ◇ X2) := by
    first | exact superpose ef3523 ef40243 | exact superpose ef40243 ef3523
  have ef40756 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ (X0 ◇ (dl (dr X4 X2) X1)) := by
    first | exact superpose ef29160 ef40517 | exact superpose ef40517 ef29160
  have ef42100 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((X4 ◇ (dl X1 (dl X0 X3))) ◇ X2) := by
    first | exact superpose ef1765 ef291 | exact superpose ef291 ef1765
  have ef42217 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X1 ◇ X2) ◇ (wf X3 X4)) = dl (wf X3 ((X2 ◇ X0) ◇ X1)) X4 := by
    first | exact superpose ef291 ef3584 | exact superpose ef3584 ef291
  have ef42320 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((dl X0 X3) ◇ (dr (X2 ◇ X4) X1)) := by
    first | exact superpose ef5518 ef42100 | exact superpose ef42100 ef5518
  have ef42460 (X0 X1 X2 X4 : G) : dl (dr (X2 ◇ X4) X1) X0 = dl X2 ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef164 ef42320 | exact superpose ef42320 ef164
  have ef43141 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (dl (X0 ◇ X1) X2) := by
    first | exact superpose ef4734 ef292 | exact superpose ef292 ef4734
  have ef43387 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) := by
    first | exact superpose ef644 ef43141 | exact superpose ef43141 ef644
  have ef43629 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (wf (X0 ◇ X1) (X3 ◇ X0))) := by
    first | exact superpose ef42217 ef43387 | exact superpose ef43387 ef42217
  have ef43837 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (wf X1 (dl X3 X0)))) := by
    first | exact superpose ef27224 ef43629 | exact superpose ef43629 ef27224
  have ef43981 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ (dl (wf X1 (dl X3 X0)) X2) := by
    first | exact superpose ef30 ef43837 | exact superpose ef43837 ef30
  have ef44072 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((dl X0 (wf X1 X2)) ◇ X3) := by
    first | exact superpose ef30917 ef43981 | exact superpose ef43981 ef30917
  have ef46365 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (((X0 ◇ X0) ◇ (dl (wf X0 X1) X1)) ◇ X0) ◇
      X2 := by
    first | exact superpose ef7544 ef99 | exact superpose ef99 ef7544
  have ef46594 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (X1 ◇ X0) ◇
      ((dr X2 (X0 ◇ X0)) ◇ (wf X0 X1)) := by
    first | exact superpose ef3533 ef46365 | exact superpose ef46365 ef3533
  have ef46727 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 (X0 ◇ X0)) (dr X0 X0) := by
    first | exact superpose ef106 ef46594 | exact superpose ef46594 ef106
  have ef46833 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef105 ef46727 | exact superpose ef46727 ef105
  have ef46914 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef33861 ef46833 | exact superpose ef46833 ef33861
  have ef46968 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 X0) X0 := by
    first | exact superpose ef23 ef46914 | exact superpose ef46914 ef23
  have ef47007 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) := by
    first | exact superpose ef1781 ef46968 | exact superpose ef46968 ef1781
  have ef47035 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) ((dr X0 X0) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef470 ef47007 | exact superpose ef47007 ef470
  have ef47056 (X0 X1 X2 : G) : (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (wf X0 X2) := by
    first | exact superpose ef19 ef47035 | exact superpose ef47035 ef19
  have ef66642 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = (X5 ◇ (X4 ◇ (dr X0 X1))) ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef109 ef461 | exact superpose ef461 ef109
  have ef67346 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) := by
    first | exact superpose ef957 ef66642 | exact superpose ef66642 ef957
  have ef67702 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = dl X0 ((dr X5 X4) ◇ (dr X2 X3)) := by
    first | exact superpose ef42460 ef67346 | exact superpose ef67346 ef42460
  have ef67994 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (dl X3 (dr X5 X4)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef5478 ef67702 | exact superpose ef67702 ef5478
  have ef68236 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (X5 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef129 ef67994 | exact superpose ef67994 ef129
  have ef69488 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = (((dr X0 X1) ◇ (X2 ◇ X3)) ◇ X5) ◇ X4 := by
    first | exact superpose ef470 ef470
  have ef70449 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (dr X4 (dr X0 X1)) X3)) := by
    first | exact superpose ef40756 ef69488 | exact superpose ef69488 ef40756
  have ef70975 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (X1 ◇ (X4 ◇ X0)) X3)) := by
    first | exact superpose ef105 ef70449 | exact superpose ef70449 ef105
  have ef71379 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ ((X4 ◇ X0) ◇ (dr X1 X3))) := by
    first | exact superpose ef644 ef70975 | exact superpose ef70975 ef644
  have ef76676 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (wf X0 (X0 ◇ X1))) := by
    first | exact superpose ef4734 ef9101 | exact superpose ef9101 ef4734
  have ef76873 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (X0 ◇ (wf X0 X1))) := by
    first | exact superpose ef9101 ef76676 | exact superpose ef76676 ef9101
  have ef76956 (X0 X1 : G) : wf X0 (dl X0 X1) = dl X0 (wf X0 X1) := by
    first | exact superpose ef4734 ef76873 | exact superpose ef76873 ef4734
  have ef106495 (X0 X1 X2 : G) :
      wf X0 (wf X1 X0) = (wf X1 X0) ◇ (wf (dl (wf X1 X2) X2) (wf X1 X0)) := by
    first | exact superpose ef8263 ef32693 | exact superpose ef32693 ef8263
  have ef106565 (X0 X1 : G) : wf X0 (wf X1 X0) = (wf X1 X0) ◇ ((dl X1 X1) ◇ X0) := by
    first | exact superpose ef47056 ef106495 | exact superpose ef106495 ef47056
  have ef106664 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef5528 ef106565 | exact superpose ef106565 ef5528
  have ef106737 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef106664 | exact superpose ef106664 ef76956
  have ef151645 (X0 X1 X2 : G) :
      X0 ◇ ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) =
      dl (dr (X0 ◇ (wf X0 X1)) (X0 ◇ (wf X0 X1))) X1 := by
    first | exact superpose ef3326 ef1015 | exact superpose ef1015 ef3326
  have ef151792 (X0 X1 X2 : G) :
      dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) = X0 ◇
      ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) := by
    first | exact superpose ef7639 ef151645 | exact superpose ef151645 ef7639
  have ef152128 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef37612 ef151792 | exact superpose ef151792 ef37612
  have ef152448 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (dr X1 (X0 ◇ (wf X0 X1)))) := by
    first | exact superpose ef993 ef152128 | exact superpose ef152128 ef993
  have ef152735 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (((wf X0 X1) ◇ X1) ◇ X0)) := by
    first | exact superpose ef40 ef152448 | exact superpose ef152448 ef40
  have ef152970 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (dr X0 (wf X0 X1)))) := by
    first | exact superpose ef71379 ef152735 | exact superpose ef152735 ef71379
  have ef153148 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (dr X0 (wf X0 (X0 ◇ X1))))) := by
    first | exact superpose ef27355 ef152970 | exact superpose ef152970 ef27355
  have ef153300 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (wf (dr X0 X0) (dl X0 X1)))) := by
    first | exact superpose ef34897 ef153148 | exact superpose ef153148 ef34897
  have ef153425 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (dr X0 X0))))) := by
    first | exact superpose ef23865 ef153300 | exact superpose ef153300 ef23865
  have ef153518 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0) := by
    first | exact superpose ef68236 ef153425 | exact superpose ef153425 ef68236
  have ef153583 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dl X1 X0) ◇ (X1 ◇ (dr X1 X0)) := by
    first | exact superpose ef24400 ef153518 | exact superpose ef153518 ef24400
  have ef153626 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef44072 ef153583 | exact superpose ef153583 ef44072
  have ef153660 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef153626 | exact superpose ef153626 ef76956
  have ef153685 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef106737 ef153660 | exact superpose ef153660 ef106737
  have ef153704 (X0 X1 : G) : wf (wf X0 X1) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef18 ef153685 | exact superpose ef153685 ef18
  have ef155701 : wf x (wf x x) ≠ wf x (wf x x) := by
    first | exact superpose ef153704 ef20 | exact superpose ef20 ef153704
  exact absurd rfl ef155701

theorem Equation4380_termStructuralFromFin_Equation898_qdiv :
    Law4380.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.rdv (.var 0) (.var 0)) (.op (.var 1) (.var 0))) (.rdv (.ldv (.var 0) (.var 1)) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4380.models_iff]
    exact fun x ↦
      @qaux898_4380_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_56R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_56L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

set_option maxHeartbeats 1400000 in
/-- Equation 4435 `x ◇ (y ◇ x) = (x ◇ y) ◇ x` holds of the operation `x □ y := ((x/x)◇(y◇x))` in
every magma satisfying equation 898 `x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with the
divisions that law forces. -/
private theorem qaux898_4435_56 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = (dr a a) ◇ (b ◇ a))
    (x y : G) :
    wf x (wf y x) = wf (wf x y) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef18 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef19 (X0 X1 : G) : wf X0 X1 = (dr X0 X0) ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef20 : wf x (wf y x) ≠ wf (wf x y) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((dl X2 X0) ◇ X1)) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef26 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef15 ef12 | exact superpose ef12 ef15
  have ef27 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef30 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef18 | exact superpose ef18 ef12
  have ef36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef37 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef17 ef13 | exact superpose ef13 ef17
  have ef40 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef61 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef64 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef17 ef14 | exact superpose ef14 ef17
  have ef67 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef14 ef14
  have ef69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef70 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef72 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef14 ef18 | exact superpose ef18 ef14
  have ef82 (X0 X1 : G) : wf X1 (dr X0 X1) = (dr X1 X1) ◇ X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef85 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (dr ((X0 ◇ X1) ◇ (X1 ◇ X2)) ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇
      X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef87 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = (dr (X1 ◇ X2) (X1 ◇ X2)) ◇ X0 := by
    first | exact superpose ef14 ef19 | exact superpose ef19 ef14
  have ef88 (X0 X1 : G) : dr X0 X0 = (X0 ◇ (wf X0 X1)) ◇ X1 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef90 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ ((X2 ◇ (dr X0 X0)) ◇ (wf X0 X1)) = X2 := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef91 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1))) ◇ (dr X0 X0) = X2 := by
    first | exact superpose ef19 ef13 | exact superpose ef13 ef19
  have ef92 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (dr X0 X0)) ◇ (wf X0 X1) = X2 := by
    first | exact superpose ef19 ef14 | exact superpose ef14 ef19
  have ef99 (X0 X1 X2 : G) : wf (X1 ◇ X2) ((X2 ◇ X0) ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0 := by
    first | exact superpose ef40 ef87 | exact superpose ef87 ef40
  have ef101 (X0 X1 X2 : G) :
      wf ((X0 ◇ X1) ◇ (X1 ◇ X2)) X2 = (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef40 ef85 | exact superpose ef85 ef40
  have ef104 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = (((X1 ◇ X2) ◇ (dl X2 X0)) ◇ (X0 ◇ X1)) ◇ X0 := by
    first | exact superpose ef30 ef101 | exact superpose ef101 ef30
  have ef105 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef15 ef23 | exact superpose ef23 ef15
  have ef106 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X2 ◇ (wf X0 X1)) = dr X2 (dr X0 X0) := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef107 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef17 ef23 | exact superpose ef23 ef17
  have ef109 (X0 X1 X2 X3 : G) : dr X3 X2 = (X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef23 ef23
  have ef110 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (X3 ◇ (X0 ◇ (X1 ◇ X3))) := by
    first | exact superpose ef13 ef23 | exact superpose ef23 ef13
  have ef111 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dr X3 ((X2 ◇ X0) ◇ X1) := by
    first | exact superpose ef14 ef23 | exact superpose ef23 ef14
  have ef112 (X0 X1 : G) : X0 ◇ (wf X0 X1) = dr (dr X0 X0) X1 := by
    first | exact superpose ef19 ef23 | exact superpose ef23 ef19
  have ef124 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (dr X0 X1)) = X3 := by
    first | exact superpose ef23 ef12 | exact superpose ef12 ef23
  have ef126 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef129 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef18 | exact superpose ef18 ef23
  have ef131 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X3 := by
    first | exact superpose ef23 ef14 | exact superpose ef14 ef23
  have ef138 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ X3) ◇ (X2 ◇ X0) := by
    first | exact superpose ef40 ef111 | exact superpose ef111 ef40
  have ef139 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3 := by
    first | exact superpose ef40 ef110 | exact superpose ef110 ef40
  have ef149 (X0 X1 : G) : X0 ◇ (wf X0 (dl X1 (dr X0 X0))) = X1 := by
    first | exact superpose ef19 ef24 | exact superpose ef24 ef19
  have ef156 (X0 X1 X2 : G) : ((dl X0 X1) ◇ X2) ◇ X0 = dr X2 X1 := by
    first | exact superpose ef24 ef23 | exact superpose ef23 ef24
  have ef164 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ ((dl X0 X2) ◇ X1) := by
    first | exact superpose ef24 ef18 | exact superpose ef18 ef24
  have ef167 (X0 X1 X2 X3 : G) : X0 ◇ ((X3 ◇ ((dl X0 X3) ◇ (X1 ◇ X2))) ◇ X1) = X2 := by
    first | exact superpose ef24 ef14 | exact superpose ef14 ef24
  have ef177 (X0 X1 : G) : X0 ◇ (wf X0 (X0 ◇ (X0 ◇ X1))) = X1 := by
    first | exact superpose ef129 ef149 | exact superpose ef149 ef129
  have ef194 (X0 X1 : G) : wf X1 (X0 ◇ (dr X1 (dr X1 X1))) = X0 := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef201 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef26 ef18 | exact superpose ef18 ef26
  have ef214 (X0 X1 : G) : wf X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    first | exact superpose ef105 ef194 | exact superpose ef194 ef105
  have ef239 (X0 X1 X2 : G) : (dl (X0 ◇ (X1 ◇ X2)) X1) ◇ X0 = X2 := by
    first | exact superpose ef13 ef27 | exact superpose ef27 ef13
  have ef243 (X0 X1 X2 X3 : G) : (dl X2 (X0 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ (dr X0 X1) = X3 := by
    first | exact superpose ef23 ef27 | exact superpose ef27 ef23
  have ef254 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef27 ef18 | exact superpose ef18 ef27
  have ef256 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef27 ef23 | exact superpose ef23 ef27
  have ef287 (X0 X1 X2 X3 : G) : dl X3 X2 = (dr X0 X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3) := by
    first | exact superpose ef23 ef30 | exact superpose ef30 ef23
  have ef291 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef292 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef30 ef30
  have ef302 (X0 X1 X2 X3 : G) : dl (X3 ◇ X2) X1 = (X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0 := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef306 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = dl ((X0 ◇ X2) ◇ X3) X1 := by
    first | exact superpose ef27 ef30 | exact superpose ef30 ef27
  have ef316 (X0 X1 X2 : G) : dr X2 X0 = dl (X0 ◇ (X1 ◇ X2)) X1 := by
    first | exact superpose ef30 ef23 | exact superpose ef23 ef30
  have ef322 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef30 ef14 | exact superpose ef14 ef30
  have ef325 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef30 ef18 | exact superpose ef18 ef30
  have ef337 (X0 X1 X3 : G) : (dr X1 (dl X0 X3)) ◇ (dl X0 X1) = X3 := by
    first | exact superpose ef256 ef322 | exact superpose ef322 ef256
  have ef444 (X0 X1 : G) : (wf X0 X1) ◇ (dr X0 (dr X0 X0)) = X1 := by
    first | exact superpose ef19 ef36 | exact superpose ef36 ef19
  have ef458 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef36 ef23 | exact superpose ef23 ef36
  have ef460 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef461 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef36 ef30 | exact superpose ef30 ef36
  have ef470 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef40 ef458 | exact superpose ef458 ef40
  have ef478 (X0 X1 : G) : (wf X0 X1) ◇ (X0 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef105 ef444 | exact superpose ef444 ef105
  have ef538 (X0 X1 X2 : G) : dl X2 X1 = (dl (X0 ◇ X1) X2) ◇ X0 := by
    first | exact superpose ef37 ef27 | exact superpose ef27 ef37
  have ef644 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef61 ef36 | exact superpose ef36 ef61
  have ef649 (X0 X1 : G) : wf X1 (dl (X1 ◇ X0) (dr X1 X1)) = X0 := by
    first | exact superpose ef61 ef19 | exact superpose ef19 ef61
  have ef690 (X0 X1 : G) : wf X1 (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    first | exact superpose ef129 ef649 | exact superpose ef649 ef129
  have ef830 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef23 ef64 | exact superpose ef64 ef23
  have ef849 (X0 X1 X2 X3 : G) : dl X3 X1 = (X1 ◇ (((dl X2 X3) ◇ X0) ◇ X2)) ◇ X0 := by
    first | exact superpose ef64 ef30 | exact superpose ef30 ef64
  have ef878 (X1 X2 X3 : G) : dl X3 X1 = dl (X2 ◇ (dl X2 X3)) X1 := by
    first | exact superpose ef302 ef849 | exact superpose ef849 ef302
  have ef900 (X1 X2 X3 : G) : dl X3 X1 = (dl X2 X3) ◇ (dr X2 X1) := by
    first | exact superpose ef644 ef878 | exact superpose ef878 ef644
  have ef924 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef36 ef72 | exact superpose ef72 ef36
  have ef927 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = dl (X0 ◇ X1) ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef27 ef72 | exact superpose ef72 ef27
  have ef955 (X0 X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef291 ef927 | exact superpose ef927 ef291
  have ef957 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef129 ef924 | exact superpose ef924 ef129
  have ef969 (X1 X2 X3 : G) : X1 ◇ (dl X2 X3) = X2 ◇ (dl X1 X3) := by
    first | exact superpose ef30 ef955 | exact superpose ef955 ef30
  have ef993 (X0 X1 X2 : G) : dl X2 (X0 ◇ (wf X0 X1)) = (dr X0 X0) ◇ (X1 ◇ X2) := by
    first | exact superpose ef88 ef30 | exact superpose ef30 ef88
  have ef999 (X0 X1 X2 : G) : dr X2 (dr X0 X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef88 ef40 | exact superpose ef40 ef88
  have ef1015 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X0) = (X1 ◇ X2) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef105 ef999 | exact superpose ef999 ef105
  have ef1765 (X0 X1 X2 : G) : dr X2 X1 = (dl X1 (dl X2 X0)) ◇ X0 := by
    first | exact superpose ef17 ef107 | exact superpose ef107 ef17
  have ef1777 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef14 ef107 | exact superpose ef107 ef14
  have ef1778 (X0 X1 X2 X3 : G) : (dl X2 (X3 ◇ X0)) ◇ (dl X0 X1) = dr (X1 ◇ X3) X2 := by
    first | exact superpose ef30 ef107 | exact superpose ef107 ef30
  have ef1780 (X0 X1 X2 X3 : G) : (dl X1 (dr X2 X3)) ◇ X0 = dr (X3 ◇ (X0 ◇ X2)) X1 := by
    first | exact superpose ef36 ef107 | exact superpose ef107 ef36
  have ef1781 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef15 ef107 | exact superpose ef107 ef15
  have ef1793 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1806 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef107 ef23 | exact superpose ef23 ef107
  have ef1808 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = (dr X0 X1) ◇ ((X0 ◇ X2) ◇ X3) := by
    first | exact superpose ef107 ef30 | exact superpose ef30 ef107
  have ef1857 (X0 X1 X2 X3 : G) : dr (X3 ◇ (X0 ◇ X2)) X1 = (X2 ◇ (X3 ◇ X1)) ◇ X0 := by
    first | exact superpose ef129 ef1780 | exact superpose ef1780 ef129
  have ef1859 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ (dl (dl X2 (X3 ◇ X0)) X1) := by
    first | exact superpose ef969 ef1778 | exact superpose ef1778 ef969
  have ef1890 (X0 X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)) := by
    first | exact superpose ef254 ef1859 | exact superpose ef1859 ef254
  have ef1903 (X1 X2 X3 : G) : dr (X1 ◇ X3) X2 = dr (X1 ◇ X2) X3 := by
    first | exact superpose ef23 ef1890 | exact superpose ef1890 ef23
  have ef1972 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) ◇ (X0 ◇ X1) = X3 := by
    first | exact superpose ef26 ef70 | exact superpose ef70 ef26
  have ef2109 (X0 X2 X3 X4 : G) : dr X0 (dl X2 (X3 ◇ ((X0 ◇ (dr X4 X2)) ◇ X4))) = X3 := by
    first | exact superpose ef256 ef1972 | exact superpose ef1972 ef256
  have ef2210 (X0 X2 X3 X4 : G) : dr X0 ((X0 ◇ (dr X4 X2)) ◇ ((dr X4 X3) ◇ X2)) = X3 := by
    first | exact superpose ef460 ef2109 | exact superpose ef2109 ef460
  have ef2281 (X0 X2 X3 X4 : G) : (((dr X4 X3) ◇ X2) ◇ X0) ◇ (X0 ◇ (dr X4 X2)) = X3 := by
    first | exact superpose ef40 ef2210 | exact superpose ef2210 ef40
  have ef2327 (X2 X3 X4 : G) : dl (dr X4 X2) ((dr X4 X3) ◇ X2) = X3 := by
    first | exact superpose ef30 ef2281 | exact superpose ef2281 ef30
  have ef2378 (X0 X1 : G) : wf (dr X0 X0) X1 = (X0 ◇ (wf X0 (dr X0 X0))) ◇ (X1 ◇ (dr X0 X0)) := by
    first | exact superpose ef112 ef19 | exact superpose ef19 ef112
  have ef2397 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 (wf X0 (dr X0 X0))) := by
    first | exact superpose ef1806 ef2378 | exact superpose ef2378 ef1806
  have ef2406 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 ((dr X0 X0) ◇ X0)) := by
    first | exact superpose ef82 ef2397 | exact superpose ef2397 ef82
  have ef2410 (X0 X1 : G) : wf (dr X0 X0) X1 = dr X1 (dl X0 X0) := by
    first | exact superpose ef15 ef2406 | exact superpose ef2406 ef15
  have ef3154 (X0 X1 X2 X3 : G) :
      dl (dr X3 X3) X1 = (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (wf X3 X2)))) ◇ X0 := by
    first | exact superpose ef91 ef30 | exact superpose ef30 ef91
  have ef3206 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl (dr (wf X3 X2) (X2 ◇ X3)) X1 := by
    first | exact superpose ef461 ef3154 | exact superpose ef3154 ef461
  have ef3274 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = dl ((X3 ◇ (wf X3 X2)) ◇ X2) X1 := by
    first | exact superpose ef40 ef3206 | exact superpose ef3206 ef40
  have ef3326 (X1 X2 X3 : G) : dl (dr X3 X3) X1 = (X1 ◇ (dl (wf X3 X2) X2)) ◇ X3 := by
    first | exact superpose ef306 ef3274 | exact superpose ef3274 ef306
  have ef3463 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ (X1 ◇ (dl X2 X3))) X3 := by
    first | exact superpose ef23 ef156 | exact superpose ef156 ef23
  have ef3483 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef156 ef23 | exact superpose ef23 ef156
  have ef3519 (X0 X1 X2 X3 X4 : G) :
      (dl ((X3 ◇ X4) ◇ X2) X1) ◇ X0 = (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef156 ef69 | exact superpose ef69 ef156
  have ef3523 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef156 ef26 | exact superpose ef26 ef156
  have ef3525 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (dr (dr X0 X0) X1) := by
    first | exact superpose ef156 ef90 | exact superpose ef90 ef156
  have ef3528 (X0 X1 X2 : G) : dl (wf X0 X2) X1 = (X2 ◇ X0) ◇ (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef112 ef3525 | exact superpose ef3525 ef112
  have ef3533 (X0 X1 X2 X3 X4 : G) :
      (X2 ◇ X3) ◇ ((dr X0 X1) ◇ X4) = ((X1 ◇ (dl X4 X2)) ◇ X3) ◇ X0 := by
    first | exact superpose ef306 ef3519 | exact superpose ef3519 ef306
  have ef3564 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef40 ef3483 | exact superpose ef3483 ef40
  have ef3578 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = dr (X0 ◇ X3) (X1 ◇ (dl X2 X3)) := by
    first | exact superpose ef1903 ef3463 | exact superpose ef3463 ef1903
  have ef3584 (X0 X1 X2 : G) : dl (wf X0 X1) X2 = dl (wf X0 X2) X1 := by
    first | exact superpose ef30 ef3528 | exact superpose ef3528 ef30
  have ef3614 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ X2 = ((dl X2 X3) ◇ (X0 ◇ X3)) ◇ X1 := by
    first | exact superpose ef40 ef3578 | exact superpose ef3578 ef40
  have ef3631 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = (dr X0 X2) ◇ X1 := by
    first | exact superpose ef107 ef3614 | exact superpose ef3614 ef107
  have ef3717 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = dr X3 (((X2 ◇ X1) ◇ X0) ◇ (dr X1 X1)) := by
    first | exact superpose ef92 ef23 | exact superpose ef23 ef92
  have ef3776 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = ((dr X1 X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X0) := by
    first | exact superpose ef40 ef3717 | exact superpose ef3717 ef40
  have ef3858 (X0 X1 X2 X3 : G) :
      (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (dl X3 ((X2 ◇ X1) ◇ X0))) := by
    first | exact superpose ef830 ef3776 | exact superpose ef3776 ef830
  have ef3919 (X0 X1 X2 X3 : G) : (wf X1 X2) ◇ (X3 ◇ X0) = X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    first | exact superpose ef291 ef3858 | exact superpose ef3858 ef291
  have ef4054 (X0 X1 X2 X3 : G) : X3 ◇ X0 = dl ((dl (X1 ◇ X0) (dl X2 X3)) ◇ X1) X2 := by
    first | exact superpose ef61 ef164 | exact superpose ef164 ef61
  have ef4070 (X0 X1 : G) : dl X0 X1 = wf X0 (dl X1 (dr X0 X0)) := by
    first | exact superpose ef164 ef19 | exact superpose ef19 ef164
  have ef4079 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dl X2 (dl X0 X1) := by
    first | exact superpose ef164 ef18 | exact superpose ef18 ef164
  have ef4155 (X0 X1 : G) : dl X0 X1 = wf X0 (X0 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef129 ef4070 | exact superpose ef4070 ef129
  have ef4164 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ (dr (dl (X1 ◇ X0) (dl X2 X3)) X2) := by
    first | exact superpose ef644 ef4054 | exact superpose ef4054 ef644
  have ef4199 (X0 X1 X2 X3 : G) : X3 ◇ X0 = X1 ◇ ((dl X2 X3) ◇ (dr X2 (X1 ◇ X0))) := by
    first | exact superpose ef1793 ef4164 | exact superpose ef4164 ef1793
  have ef4225 (X0 X1 X3 : G) : X3 ◇ X0 = X1 ◇ (dl X3 (X1 ◇ X0)) := by
    first | exact superpose ef900 ef4199 | exact superpose ef4199 ef900
  have ef4734 (X0 X1 : G) : dl X1 X0 = X1 ◇ (wf X1 (X1 ◇ X0)) := by
    first | exact superpose ef17 ef177 | exact superpose ef177 ef17
  have ef4765 (X0 X1 : G) : X1 ◇ (wf X1 X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef177 | exact superpose ef177 ef24
  have ef5478 (X0 X1 X2 X3 : G) : (dl X0 X1) ◇ (X2 ◇ X3) = dl X3 (X1 ◇ (dr X2 X0)) := by
    first | exact superpose ef201 ef30 | exact superpose ef30 ef201
  have ef5518 (X0 X1 X2 X3 : G) : X1 ◇ (dr (X3 ◇ X2) X0) = (X2 ◇ (dl X0 X1)) ◇ X3 := by
    first | exact superpose ef201 ef13 | exact superpose ef13 ef201
  have ef5523 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X3 X2) X0) = X2 ◇ ((dl X0 X1) ◇ X3) := by
    first | exact superpose ef201 ef26 | exact superpose ef26 ef201
  have ef5528 (X0 X1 X2 X3 : G) : X2 ◇ ((dl X0 X1) ◇ X3) = X1 ◇ ((dl X0 X2) ◇ X3) := by
    first | exact superpose ef1781 ef5523 | exact superpose ef5523 ef1781
  have ef6622 (X0 X1 X2 : G) : X1 ◇ (dr (X2 ◇ (X2 ◇ X2)) X0) = wf X2 (dl X0 X1) := by
    first | exact superpose ef201 ef214 | exact superpose ef214 ef201
  have ef6651 (X0 X1 X2 : G) : wf X2 (dl X0 X1) = X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2) := by
    first | exact superpose ef1857 ef6622 | exact superpose ef6622 ef1857
  have ef6770 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = dl X3 (dl (X1 ◇ (X2 ◇ X0)) X2) := by
    first | exact superpose ef239 ef30 | exact superpose ef30 ef239
  have ef6848 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ X3) = (dl X2 X3) ◇ (X1 ◇ (X2 ◇ X0)) := by
    first | exact superpose ef4079 ef6770 | exact superpose ef6770 ef4079
  have ef7495 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = dr X2 ((dl (X3 ◇ X2) X1) ◇ X0) := by
    first | exact superpose ef156 ef316 | exact superpose ef316 ef156
  have ef7503 (X0 X1 : G) : dr X0 (dr X0 X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef19 ef316 | exact superpose ef316 ef19
  have ef7544 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl (wf X0 X1) X1 := by
    first | exact superpose ef105 ef7503 | exact superpose ef7503 ef105
  have ef7552 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (dl (X3 ◇ X2) X1) := by
    first | exact superpose ef40 ef7495 | exact superpose ef7495 ef40
  have ef7609 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (X0 ◇ X2) ◇ (X2 ◇ (dr X3 X1)) := by
    first | exact superpose ef644 ef7552 | exact superpose ef7552 ef644
  have ef7639 (X0 X1 X3 : G) : dl (dr X3 X1) X0 = dl (dr X0 X1) X3 := by
    first | exact superpose ef30 ef7609 | exact superpose ef7609 ef30
  have ef7878 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef337 ef72 | exact superpose ef72 ef337
  have ef7908 (X0 X1 X2 X3 : G) : X1 ◇ (dr X2 (dl X3 X0)) = (dl X2 (X0 ◇ X1)) ◇ X3 := by
    first | exact superpose ef4079 ef7878 | exact superpose ef7878 ef4079
  have ef8154 (X0 X1 X2 : G) : dl X2 (wf X1 X0) = X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2) := by
    first | exact superpose ef478 ef30 | exact superpose ef30 ef478
  have ef8163 (X0 X1 X2 X3 : G) :
      (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2)) = X3 := by
    first | exact superpose ef478 ef67 | exact superpose ef67 ef478
  have ef8205 (X0 X1 X2 X3 : G) :
      X2 ◇ (X2 ◇ (X2 ◇ (((X1 ◇ (wf X2 X0)) ◇ X3) ◇ (X0 ◇ X1)))) = X3 := by
    first | exact superpose ef957 ef8163 | exact superpose ef8163 ef957
  have ef8238 (X0 X1 X2 X3 : G) : (wf X2 X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (wf X2 X0))) = X3 := by
    first | exact superpose ef3919 ef8205 | exact superpose ef8205 ef3919
  have ef8263 (X0 X2 X3 : G) : (wf X2 X3) ◇ (dl (wf X2 X0) X0) = X3 := by
    first | exact superpose ef30 ef8238 | exact superpose ef8238 ef30
  have ef9083 (X0 X1 : G) : wf X1 (X1 ◇ X0) = (dl X0 X1) ◇ X1 := by
    first | exact superpose ef24 ef690 | exact superpose ef690 ef24
  have ef9101 (X0 X1 : G) : X1 ◇ (wf X1 X0) = wf X1 (X1 ◇ X0) := by
    first | exact superpose ef4765 ef9083 | exact superpose ef9083 ef4765
  have ef13289 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = dr X3 ((dr X1 X0) ◇ X2) := by
    first | exact superpose ef2327 ef156 | exact superpose ef156 ef2327
  have ef13311 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (dr X1 X2) = (X2 ◇ X3) ◇ (dr X1 X0) := by
    first | exact superpose ef40 ef13289 | exact superpose ef13289 ef40
  have ef16281 (X0 X1 X2 X3 X4 : G) :
      dl ((X0 ◇ X4) ◇ (dr X2 X3)) X1 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef124 ef30 | exact superpose ef30 ef124
  have ef16386 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (X1 ◇ (dl X4 (dr X2 X3))) ◇ X0 := by
    first | exact superpose ef306 ef16281 | exact superpose ef16281 ef306
  have ef16596 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 = (dr X2 X3) ◇ (dr (X0 ◇ X1) X4) := by
    first | exact superpose ef5518 ef16386 | exact superpose ef16386 ef5518
  have ef19220 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = dr (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) X4 := by
    first | exact superpose ef126 ef109 | exact superpose ef109 ef126
  have ef19366 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (dl X4 (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0 := by
    first | exact superpose ef1777 ef19220 | exact superpose ef19220 ef1777
  have ef19571 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ X4)) ◇ X0 = (X1 ◇ (X2 ◇ X3)) ◇ (dr X4 (dl X0 X3)) := by
    first | exact superpose ef7908 ef19366 | exact superpose ef19366 ef7908
  have ef20543 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = dl X1 ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef131 ef538 | exact superpose ef538 ef131
  have ef20568 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (dr X2 X3) = (X3 ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X2) ◇ X1) := by
    first | exact superpose ef291 ef20543 | exact superpose ef20543 ef291
  have ef22046 (X0 X1 X2 X3 X4 : G) :
      (dl X0 X1) ◇ (X3 ◇ X4) = ((X1 ◇ (dr X2 X0)) ◇ X3) ◇ (X2 ◇ X4) := by
    first | exact superpose ef201 ef138 | exact superpose ef138 ef201
  have ef23864 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (dr (dl X0 X0) X1) := by
    first | exact superpose ef2410 ef1793 | exact superpose ef1793 ef2410
  have ef23865 (X0 X1 X2 : G) : wf (dr X0 X0) (dl X1 X2) = X2 ◇ (X0 ◇ (dr X1 X0)) := by
    first | exact superpose ef1793 ef23864 | exact superpose ef23864 ef1793
  have ef23973 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ X3 := by
    first | exact superpose ef139 ef139
  have ef23983 (X0 X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = ((X5 ◇ (dr X0 X1)) ◇ X4) ◇ (X0 ◇ (dr X2 X3)) := by
    first | exact superpose ef109 ef139 | exact superpose ef139 ef109
  have ef24400 (X1 X2 X3 X4 X5 : G) :
      (X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5) = (dl X1 X5) ◇ (X4 ◇ (dr X2 X3)) := by
    first | exact superpose ef22046 ef23983 | exact superpose ef23983 ef22046
  have ef24408 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = ((dr X0 X1) ◇ (dr (X4 ◇ X5) X2)) ◇ X3 := by
    first | exact superpose ef16596 ef23973 | exact superpose ef23973 ef16596
  have ef24565 (X0 X1 X2 X3 X4 X5 : G) :
      ((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5) = X0 ◇ (X1 ◇ (dl (dr (X4 ◇ X5) X2) X3)) := by
    first | exact superpose ef830 ef24408 | exact superpose ef24408 ef830
  have ef26311 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇
      ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) := by
    first | exact superpose ef167 ef99 | exact superpose ef99 ef167
  have ef26424 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4) X2) X2)) := by
    first | exact superpose ef24565 ef26311 | exact superpose ef26311 ef24565
  have ef26635 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (dl (dr X2 X2) ((X3 ◇ ((dl X2 X3) ◇ (X4 ◇ X0))) ◇ X4))) := by
    first | exact superpose ef7639 ef26424 | exact superpose ef26424 ef7639
  have ef26809 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ (((dl X2 X3) ◇ (X4 ◇ X0)) ◇ ((X4 ◇ X3) ◇ (dr X2 X2)))) := by
    first | exact superpose ef291 ef26635 | exact superpose ef26635 ef291
  have ef26934 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ (dl ((dl X2 X3) ◇ (X4 ◇ X0)) X2))) := by
    first | exact superpose ef3564 ef26809 | exact superpose ef26809 ef3564
  have ef27024 (X0 X1 X2 X3 X4 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇
      (X1 ◇ ((X2 ◇ (X4 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (dr (dl X2 X3) X2)))) := by
    first | exact superpose ef644 ef26934 | exact superpose ef26934 ef644
  have ef27090 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((dl X3 (dr (dl X2 X3) X2)) ◇ (dr X0 X2))) := by
    first | exact superpose ef20568 ef27024 | exact superpose ef27024 ef20568
  have ef27136 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ (((dl X2 X3) ◇ (X2 ◇ X3)) ◇ (dr X0 X2))) := by
    first | exact superpose ef129 ef27090 | exact superpose ef27090 ef129
  have ef27170 (X0 X1 X2 X3 : G) :
      wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (dr X0 (dl X2 X3)))) := by
    first | exact superpose ef13311 ef27136 | exact superpose ef27136 ef13311
  have ef27198 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := by
    first | exact superpose ef19571 ef27170 | exact superpose ef27170 ef19571
  have ef27224 (X0 X1 X2 : G) : wf (X1 ◇ X2) (X0 ◇ X1) = X1 ◇ (wf X2 (dl X0 X1)) := by
    first | exact superpose ef6651 ef27198 | exact superpose ef27198 ef6651
  have ef27346 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = dr (dl (wf X0 X1) X2) X3 := by
    first | exact superpose ef3584 ef1793 | exact superpose ef1793 ef3584
  have ef27355 (X0 X1 X2 X3 : G) : X1 ◇ (dr X3 (wf X0 X2)) = X2 ◇ (dr X3 (wf X0 X1)) := by
    first | exact superpose ef1793 ef27346 | exact superpose ef27346 ef1793
  have ef29160 (X0 X1 X2 X3 : G) : (dr X0 (dl X1 X2)) ◇ X3 = X1 ◇ (dl (dr X0 X3) X2) := by
    first | exact superpose ef3631 ef969 | exact superpose ef969 ef3631
  have ef30917 (X0 X1 X2 X3 : G) : (dl X0 (wf X1 X2)) ◇ X3 = dl (wf X1 (dl X3 X0)) X2 := by
    first | exact superpose ef4079 ef3584 | exact superpose ef3584 ef4079
  have ef32561 (X0 X1 : G) : wf (X0 ◇ X1) X0 = dl (X0 ◇ X1) (X1 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef12 ef4155 | exact superpose ef4155 ef12
  have ef32611 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ ((dr X1 X1) ◇ (X0 ◇ X1)) := by
    first | exact superpose ef460 ef32561 | exact superpose ef32561 ef460
  have ef32693 (X0 X1 : G) : wf (X0 ◇ X1) X0 = X0 ◇ (wf X1 X0) := by
    first | exact superpose ef19 ef32611 | exact superpose ef32611 ef19
  have ef33251 (X0 X1 X2 X3 X4 : G) :
      dl X4 (dl X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 ◇ ((dr X2 X3) ◇ X4) := by
    first | exact superpose ef243 ef30 | exact superpose ef30 ef243
  have ef33383 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = (dl (X2 ◇ (X3 ◇ (X0 ◇ X1))) X4) ◇ X1 := by
    first | exact superpose ef4079 ef33251 | exact superpose ef33251 ef4079
  have ef33637 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((dr X2 X3) ◇ X4) = ((X3 ◇ (X0 ◇ X1)) ◇ (dr X2 X4)) ◇ X1 := by
    first | exact superpose ef644 ef33383 | exact superpose ef33383 ef644
  have ef33861 (X0 X2 X3 X4 : G) : X0 ◇ ((dr X2 X3) ◇ X4) = X0 ◇ ((dr X2 X4) ◇ X3) := by
    first | exact superpose ef139 ef33637 | exact superpose ef33637 ef139
  have ef34354 (X0 X1 X2 X3 : G) : X2 ◇ (dl X0 (X3 ◇ X1)) = X3 ◇ (dl X2 (X0 ◇ X1)) := by
    first | exact superpose ef4225 ef4225
  have ef34509 (X0 X1 X2 X3 : G) :
      ((X2 ◇ ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2)) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) (X0 ◇ X1) := by
    first | exact superpose ef4225 ef99 | exact superpose ef99 ef4225
  have ef34531 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 =
      wf (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) (X0 ◇ X1) := by
    first | exact superpose ef7908 ef34509 | exact superpose ef34509 ef7908
  have ef34668 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3))))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 (dl X2 (X2 ◇ X3))) (dl X0 X1)) := by
    first | exact superpose ef27224 ef34531 | exact superpose ef34531 ef27224
  have ef34752 (X0 X1 X2 X3 : G) :
      ((X2 ◇ (X1 ◇ (dr X0 X3))) ◇ (dl X0 ((X2 ◇ X3) ◇ X1))) ◇ X3 = X1 ◇
      (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef18 ef34668 | exact superpose ef34668 ef18
  have ef34797 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      ((dl X0 ((X2 ◇ X3) ◇ X1)) ◇ X2) := by
    first | exact superpose ef470 ef34752 | exact superpose ef34752 ef470
  have ef34825 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (dr (X1 ◇ (dr X0 X3)) X3) ◇
      (X1 ◇ (dr X0 (dl X2 (X2 ◇ X3)))) := by
    first | exact superpose ef7908 ef34797 | exact superpose ef34797 ef7908
  have ef34846 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      (dl (dr (X1 ◇ (dr X0 X3)) X3) (dl X2 (X2 ◇ X3))) := by
    first | exact superpose ef3564 ef34825 | exact superpose ef34825 ef3564
  have ef34862 (X0 X1 X2 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇
      ((dl (X2 ◇ X3) (dr (X1 ◇ (dr X0 X3)) X3)) ◇ X2) := by
    first | exact superpose ef4079 ef34846 | exact superpose ef34846 ef4079
  have ef34873 (X0 X1 X3 : G) :
      (X0 ◇ X1) ◇ (dl (dr (X1 ◇ (dr X0 X3)) X3) X3) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef538 ef34862 | exact superpose ef34862 ef538
  have ef34879 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dl (dr X3 X3) (X1 ◇ (dr X0 X3))) := by
    first | exact superpose ef7639 ef34873 | exact superpose ef34873 ef7639
  have ef34883 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ (dl (X0 ◇ X1) ((dr X3 X3) ◇ (dr X0 X3))) := by
    first | exact superpose ef34354 ef34879 | exact superpose ef34879 ef34354
  have ef34887 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((dl X3 (dr X3 X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef5478 ef34883 | exact superpose ef34883 ef5478
  have ef34890 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = X1 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef129 ef34887 | exact superpose ef34887 ef129
  have ef34893 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = dl (X0 ◇ (X0 ◇ X1)) (wf X3 X1) := by
    first | exact superpose ef8154 ef34890 | exact superpose ef34890 ef8154
  have ef34895 (X0 X1 X3 : G) :
      X1 ◇ (wf (dr X0 X3) (dl X0 X1)) = (X0 ◇ X1) ◇ (dr X0 (wf X3 X1)) := by
    first | exact superpose ef644 ef34893 | exact superpose ef34893 ef644
  have ef34897 (X0 X1 X3 : G) :
      X1 ◇ (dr X0 (wf X3 (X0 ◇ X1))) = X1 ◇ (wf (dr X0 X3) (dl X0 X1)) := by
    first | exact superpose ef27355 ef34895 | exact superpose ef34895 ef27355
  have ef36872 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = ((((wf X0 (X0 ◇ X1)) ◇ X2) ◇ (dl X2 X0)) ◇ (dl X0 X1)) ◇ X0 := by
    first | exact superpose ef4734 ef104 | exact superpose ef104 ef4734
  have ef37003 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = (dr (dl X2 X0) X0) ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ X2)) := by
    first | exact superpose ef470 ef36872 | exact superpose ef36872 ef470
  have ef37165 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (dr (dl X2 X0) X0))) := by
    first | exact superpose ef957 ef37003 | exact superpose ef37003 ef957
  have ef37308 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dl X0 X1) ◇ ((wf X0 (X0 ◇ X1)) ◇ (X0 ◇ (dr X0 X2)))) := by
    first | exact superpose ef1793 ef37165 | exact superpose ef37165 ef1793
  have ef37420 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((wf X0 (X0 ◇ X1)) ◇ X1)) := by
    first | exact superpose ef6848 ef37308 | exact superpose ef37308 ef6848
  have ef37501 (X0 X1 X2 : G) :
      wf (dl X2 X0) X2 = X2 ◇ ((dr X0 X2) ◇ ((X0 ◇ (wf X0 X1)) ◇ X1)) := by
    first | exact superpose ef9101 ef37420 | exact superpose ef37420 ef9101
  have ef37564 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ (dl X1 (dl X2 (wf X0 X1))) := by
    first | exact superpose ef1808 ef37501 | exact superpose ef37501 ef1808
  have ef37612 (X0 X1 X2 : G) : wf (dl X2 X0) X2 = X2 ◇ ((dl (wf X0 X1) X1) ◇ X2) := by
    first | exact superpose ef4079 ef37564 | exact superpose ef37564 ef4079
  have ef40206 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = dl (dl X0 X1) (dl X4 (dr X2 X3)) := by
    first | exact superpose ef287 ef325 | exact superpose ef325 ef287
  have ef40243 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = (dl (dr X2 X3) (dl X0 X1)) ◇ X4 := by
    first | exact superpose ef4079 ef40206 | exact superpose ef40206 ef4079
  have ef40517 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ ((dr X4 (dl X0 X1)) ◇ X2) := by
    first | exact superpose ef3523 ef40243 | exact superpose ef40243 ef3523
  have ef40756 (X0 X1 X2 X3 X4 : G) :
      ((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4 = X3 ◇ (X0 ◇ (dl (dr X4 X2) X1)) := by
    first | exact superpose ef29160 ef40517 | exact superpose ef40517 ef29160
  have ef42100 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((X4 ◇ (dl X1 (dl X0 X3))) ◇ X2) := by
    first | exact superpose ef1765 ef291 | exact superpose ef291 ef1765
  have ef42217 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X1 ◇ X2) ◇ (wf X3 X4)) = dl (wf X3 ((X2 ◇ X0) ◇ X1)) X4 := by
    first | exact superpose ef291 ef3584 | exact superpose ef3584 ef291
  have ef42320 (X0 X1 X2 X3 X4 : G) :
      dl X2 ((dr X0 X1) ◇ X4) = X3 ◇ ((dl X0 X3) ◇ (dr (X2 ◇ X4) X1)) := by
    first | exact superpose ef5518 ef42100 | exact superpose ef42100 ef5518
  have ef42460 (X0 X1 X2 X4 : G) : dl (dr (X2 ◇ X4) X1) X0 = dl X2 ((dr X0 X1) ◇ X4) := by
    first | exact superpose ef164 ef42320 | exact superpose ef42320 ef164
  have ef43141 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (dl (X0 ◇ X1) X2) := by
    first | exact superpose ef4734 ef292 | exact superpose ef292 ef4734
  have ef43387 (X0 X1 X2 X3 : G) :
      dl (wf (X0 ◇ X1) ((X0 ◇ X1) ◇ X2)) (X3 ◇ X0) = (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) := by
    first | exact superpose ef644 ef43141 | exact superpose ef43141 ef644
  have ef43629 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (wf (X0 ◇ X1) (X3 ◇ X0))) := by
    first | exact superpose ef42217 ef43387 | exact superpose ef43387 ef42217
  have ef43837 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (wf X1 (dl X3 X0)))) := by
    first | exact superpose ef27224 ef43629 | exact superpose ef43629 ef27224
  have ef43981 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ (dl (wf X1 (dl X3 X0)) X2) := by
    first | exact superpose ef30 ef43837 | exact superpose ef43837 ef30
  have ef44072 (X0 X1 X2 X3 : G) :
      (dl X1 X3) ◇ (X1 ◇ (dr X0 X2)) = X1 ◇ ((dl X0 (wf X1 X2)) ◇ X3) := by
    first | exact superpose ef30917 ef43981 | exact superpose ef43981 ef30917
  have ef46365 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (((X0 ◇ X0) ◇ (dl (wf X0 X1) X1)) ◇ X0) ◇
      X2 := by
    first | exact superpose ef7544 ef99 | exact superpose ef99 ef7544
  have ef46594 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = (X1 ◇ X0) ◇
      ((dr X2 (X0 ◇ X0)) ◇ (wf X0 X1)) := by
    first | exact superpose ef3533 ef46365 | exact superpose ef46365 ef3533
  have ef46727 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 (X0 ◇ X0)) (dr X0 X0) := by
    first | exact superpose ef106 ef46594 | exact superpose ef46594 ef106
  have ef46833 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef105 ef46727 | exact superpose ef46727 ef105
  have ef46914 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 ◇ ((dr X2 X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef33861 ef46833 | exact superpose ef46833 ef33861
  have ef46968 (X0 X1 X2 : G) :
      wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) = dr (dr X2 X0) X0 := by
    first | exact superpose ef23 ef46914 | exact superpose ef46914 ef23
  have ef47007 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (((X0 ◇ X0) ◇ X2) ◇ X0) := by
    first | exact superpose ef1781 ef46968 | exact superpose ef46968 ef1781
  have ef47035 (X0 X1 X2 : G) :
      (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) ((dr X0 X0) ◇ (X2 ◇ X0)) := by
    first | exact superpose ef470 ef47007 | exact superpose ef47007 ef470
  have ef47056 (X0 X1 X2 : G) : (dl X0 X0) ◇ X2 = wf (dl (wf X0 X1) X1) (wf X0 X2) := by
    first | exact superpose ef19 ef47035 | exact superpose ef47035 ef19
  have ef66642 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = (X5 ◇ (X4 ◇ (dr X0 X1))) ◇ (X2 ◇ (X3 ◇ X1)) := by
    first | exact superpose ef109 ef461 | exact superpose ef461 ef109
  have ef67346 (X0 X1 X2 X3 X4 X5 : G) :
      dl (dr (X0 ◇ (dr X2 X3)) X4) X5 = X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) := by
    first | exact superpose ef957 ef66642 | exact superpose ef66642 ef957
  have ef67702 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = dl X0 ((dr X5 X4) ◇ (dr X2 X3)) := by
    first | exact superpose ef42460 ef67346 | exact superpose ef67346 ef42460
  have ef67994 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (dl X3 (dr X5 X4)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef5478 ef67702 | exact superpose ef67702 ef5478
  have ef68236 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ (X2 ◇ (X3 ◇ (X5 ◇ (X4 ◇ (dr X0 X1))))) = (X5 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X0) := by
    first | exact superpose ef129 ef67994 | exact superpose ef67994 ef129
  have ef69488 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = (((dr X0 X1) ◇ (X2 ◇ X3)) ◇ X5) ◇ X4 := by
    first | exact superpose ef470 ef470
  have ef70449 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (dr X4 (dr X0 X1)) X3)) := by
    first | exact superpose ef40756 ef69488 | exact superpose ef69488 ef40756
  have ef70975 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ (dl (X1 ◇ (X4 ◇ X0)) X3)) := by
    first | exact superpose ef105 ef70449 | exact superpose ef70449 ef105
  have ef71379 (X0 X1 X2 X3 X4 X5 : G) :
      (dr X1 X4) ◇ (X5 ◇ ((X3 ◇ X0) ◇ X2)) = X2 ◇ (X5 ◇ ((X4 ◇ X0) ◇ (dr X1 X3))) := by
    first | exact superpose ef644 ef70975 | exact superpose ef70975 ef644
  have ef76676 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (wf X0 (X0 ◇ X1))) := by
    first | exact superpose ef4734 ef9101 | exact superpose ef9101 ef4734
  have ef76873 (X0 X1 : G) : wf X0 (dl X0 X1) = X0 ◇ (wf X0 (X0 ◇ (wf X0 X1))) := by
    first | exact superpose ef9101 ef76676 | exact superpose ef76676 ef9101
  have ef76956 (X0 X1 : G) : wf X0 (dl X0 X1) = dl X0 (wf X0 X1) := by
    first | exact superpose ef4734 ef76873 | exact superpose ef76873 ef4734
  have ef106495 (X0 X1 X2 : G) :
      wf X0 (wf X1 X0) = (wf X1 X0) ◇ (wf (dl (wf X1 X2) X2) (wf X1 X0)) := by
    first | exact superpose ef8263 ef32693 | exact superpose ef32693 ef8263
  have ef106565 (X0 X1 : G) : wf X0 (wf X1 X0) = (wf X1 X0) ◇ ((dl X1 X1) ◇ X0) := by
    first | exact superpose ef47056 ef106495 | exact superpose ef106495 ef47056
  have ef106664 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef5528 ef106565 | exact superpose ef106565 ef5528
  have ef106737 (X0 X1 : G) : wf X0 (wf X1 X0) = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef106664 | exact superpose ef106664 ef76956
  have ef151645 (X0 X1 X2 : G) :
      X0 ◇ ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) =
      dl (dr (X0 ◇ (wf X0 X1)) (X0 ◇ (wf X0 X1))) X1 := by
    first | exact superpose ef3326 ef1015 | exact superpose ef1015 ef3326
  have ef151792 (X0 X1 X2 : G) :
      dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) = X0 ◇
      ((dl (wf (X0 ◇ (wf X0 X1)) X2) X2) ◇ X0) := by
    first | exact superpose ef7639 ef151645 | exact superpose ef151645 ef7639
  have ef152128 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = dl (dr X1 (X0 ◇ (wf X0 X1))) (X0 ◇ (wf X0 X1)) := by
    first | exact superpose ef37612 ef151792 | exact superpose ef151792 ef37612
  have ef152448 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (dr X1 (X0 ◇ (wf X0 X1)))) := by
    first | exact superpose ef993 ef152128 | exact superpose ef152128 ef993
  have ef152735 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dr X0 X0) ◇ (X1 ◇ (((wf X0 X1) ◇ X1) ◇ X0)) := by
    first | exact superpose ef40 ef152448 | exact superpose ef152448 ef40
  have ef152970 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (dr X0 (wf X0 X1)))) := by
    first | exact superpose ef71379 ef152735 | exact superpose ef152735 ef71379
  have ef153148 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (dr X0 (wf X0 (X0 ◇ X1))))) := by
    first | exact superpose ef27355 ef152970 | exact superpose ef152970 ef27355
  have ef153300 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (wf (dr X0 X0) (dl X0 X1)))) := by
    first | exact superpose ef34897 ef153148 | exact superpose ef153148 ef34897
  have ef153425 (X0 X1 : G) :
      wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (dr X0 X0))))) := by
    first | exact superpose ef23865 ef153300 | exact superpose ef153300 ef23865
  have ef153518 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0) := by
    first | exact superpose ef68236 ef153425 | exact superpose ef153425 ef68236
  have ef153583 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = (dl X1 X0) ◇ (X1 ◇ (dr X1 X0)) := by
    first | exact superpose ef24400 ef153518 | exact superpose ef153518 ef24400
  have ef153626 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((dl X1 (wf X1 X0)) ◇ X0) := by
    first | exact superpose ef44072 ef153583 | exact superpose ef153583 ef44072
  have ef153660 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = X1 ◇ ((wf X1 (dl X1 X0)) ◇ X0) := by
    first | exact superpose ef76956 ef153626 | exact superpose ef153626 ef76956
  have ef153685 (X0 X1 : G) : wf (dl X0 (X0 ◇ (wf X0 X1))) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef106737 ef153660 | exact superpose ef153660 ef106737
  have ef153704 (X0 X1 : G) : wf (wf X0 X1) X0 = wf X0 (wf X1 X0) := by
    first | exact superpose ef18 ef153685 | exact superpose ef153685 ef18
  have ef155679 : wf x (wf y x) ≠ wf x (wf y x) := by
    first | exact superpose ef153704 ef20 | exact superpose ef20 ef153704
  exact absurd rfl ef155679

theorem Equation4435_termStructuralFromFin_Equation898_qdiv :
    Law4435.TermStructuralFromFin Law898 := by
  refine termStructuralFromFin_of_qterm (.op (.rdv (.var 0) (.var 0)) (.op (.var 1) (.var 0))) (.rdv (.ldv (.var 0) (.var 1)) (.rdv (.var 1) (.var 1))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4435.models_iff]
    exact fun x y ↦
      @qaux898_4435_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y
  · intro G _ M hGL dr dl h1 h2 h3 h4 b
    exact @winj898_56R G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) b
  · intro G _ M hGL dr dl h1 h2 h3 h4 a
    exact @winj898_56L G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) a
  · intro G _ M hGL dr dl h1 h2 h3 h4 wdr wdl g1 g2 g3 g4 x y
    exact @back898_56 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) wdr wdl g1 g2 g3 g4 x y

end Law.MagmaLaw
