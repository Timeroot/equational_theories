import equational_theories.Definability.QuasigroupWitness

/-!
# Division witnesses that give the operation back

`Definability/QuasigroupWitness.lean` compiles a `QTerm` -- a term over `◇`, `/` and `\` -- into an
honest magma term once the carrier is finite, and `termDefinableFromFin_of_qterm` turns that into a
cell of the term-*definability* board. That board has 257 open reduced cells; the term-*structural*
one has 33320, and the whole of the gap is witnesses whose construction has never been undone.

`Definability/DivisionStructural.lean` undoes the bare division for free: `L_a^N` inverts `L_a`, so
`N` iterations of the inverse are `L_a` again. A general `QTerm` witness `w` needs a second term,
and the point of this file is that the second term may again be sought in a division clone -- the
divisions of `w` this time. `exists_uniform_period` produces one exponent `N` that inverts *every*
injective self-map of `G` at once, so the very same `N` that spells out `◇`'s divisions inside `w`
spells out `w`'s divisions inside the new magma. Nothing about `N` has to be chosen twice.

So a cell needs four prover obligations rather than one:

* the target holds of `w` -- as before;
* `w`'s two translations are injective, which is what makes its divisions exist;
* `◇` is the second `QTerm` `v` evaluated in `w` and `w`'s divisions.

All four are unit equational or Horn against source, rotations and division axioms, which is the
shape `Generated/VampireProven` already replays.
-/

open FirstOrder FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- **The compiled term is the evaluated term.** `QTerm.toBTerm N` denotes what `QTerm.eval`
denotes when the divisions are the `N`-fold iterated translations -- which they are, on a finite
magma, as soon as `N + 1` is a period. This is `termDefinableOnMagma_of_qterm`'s `key` step, stated
for a general magma so that it can be used twice: once for the source magma, once for the magma the
witness builds. -/
theorem bsem_toBTerm (M : Magma G) (N : ℕ) (q : QTerm) (x y : G) :
    bsem M (q.toBTerm (G := G) N) x y
      = q.eval M.op (fun a b ↦ (fun u ↦ M.op u b)^[N] a)
          (fun a b ↦ (fun u ↦ M.op a u)^[N] b) x y := by
  induction q with
  | var i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  | op a b iha ihb =>
    rw [show bsem M ((QTerm.op a b).toBTerm (G := G) N) x y
      = M.op (bsem M (a.toBTerm N) x y) (bsem M (b.toBTerm N) x y) from rfl, iha, ihb]
    rfl
  | rdv a b iha ihb =>
    rw [show (QTerm.rdv a b).toBTerm (G := G) N
      = riter (a.toBTerm N) (b.toBTerm N) N from rfl, bsem_riter, iha, ihb]
    rfl
  | ldv a b iha ihb =>
    rw [show (QTerm.ldv a b).toBTerm (G := G) N
      = liter (a.toBTerm N) (b.toBTerm N) N from rfl, bsem_liter, iha, ihb]
    rfl

private theorem vec_eta (w : Fin 2 → G) : ![w 0, w 1] = w := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- **The glue.** On a finite magma whose translations are injective, a pair of `QTerm`s that are
inverse to each other -- `q` naming an operation satisfying `L`, `v` naming `◇` back inside it --
is a term-structural witness. The two obligations about `q`'s translations are what make `v`'s
divisions exist; they are Horn clauses, and like the injectivity of `◇`'s own translations they are
a genuinely finite hypothesis. -/
theorem termStructuralOnMagma_of_qterm [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (q v : QTerm)
    (hr : ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      @satisfies _ G ⟨q.eval M.op rd ld⟩ L)
    (hwr : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      ∀ b : G, Function.Injective fun a ↦ q.eval M.op rd ld a b)
    (hwl : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      ∀ a : G, Function.Injective fun b ↦ q.eval M.op rd ld a b)
    (hback : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      ∀ wrd wld : G → G → G,
        (∀ a b, q.eval M.op rd ld (wrd a b) b = a) →
        (∀ a b, wrd (q.eval M.op rd ld a b) b = a) →
        (∀ a b, q.eval M.op rd ld a (wld a b) = b) →
        (∀ a b, wld a (q.eval M.op rd ld a b) = b) →
        ∀ x y : G, v.eval (q.eval M.op rd ld) wrd wld x y = M.op x y) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  have hrs (a b : G) : M.op (rd a b) b = a := by
    have h := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hri (a b : G) : rd (M.op a b) b = a := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
  have hls (a b : G) : M.op a (ld a b) = b := by
    have h := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hli (a b : G) : ld a (M.op a b) = b := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
  -- the magma the witness builds; `W.op` is `q.eval M.op rd ld` definitionally, and the `show`s
  -- below are what turn that into a syntactic match
  let W : Magma G := ⟨q.eval M.op rd ld⟩
  have hWr := hwr rd ld hrs hri hls hli
  have hWl := hwl rd ld hrs hri hls hli
  -- `N` was chosen for *every* injective self-map of `G`, so it inverts `W`'s translations too
  have hwrs (a b : G) : W.op ((fun u ↦ W.op u b)^[N] a) b = a := by
    have h := congrFun (hN (fun u ↦ W.op u b) (hWr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hwri (a b : G) : (fun u ↦ W.op u b)^[N] (W.op a b) = a :=
    congrFun (hN (fun u ↦ W.op u b) (hWr b)) a
  have hwls (a b : G) : W.op a ((fun u ↦ W.op a u)^[N] b) = b := by
    have h := congrFun (hN (fun u ↦ W.op a u) (hWl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hwli (a b : G) : (fun u ↦ W.op a u)^[N] (W.op a b) = b :=
    congrFun (hN (fun u ↦ W.op a u) (hWl a)) b
  have hback' := hback rd ld hrs hri hls hli
    (fun a b ↦ (fun u ↦ W.op u b)^[N] a) (fun a b ↦ (fun u ↦ W.op a u)^[N] b)
    hwrs hwri hwls hwli
  refine ⟨W, hsat rd ld hrs hri hls hli,
    ⟨q.toBTerm (G := G) N, ?_⟩, ⟨v.toBTerm (G := G) N, ?_⟩⟩
  · funext z
    show q.eval M.op rd ld (z 0) (z 1) = _
    rw [← bsem_toBTerm M N q (z 0) (z 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![z 0, z 1] _ = _
    rw [vec_eta]
  · funext z
    have h2 : v.eval W.op (fun a b ↦ (fun u ↦ W.op u b)^[N] a)
        (fun a b ↦ (fun u ↦ W.op a u)^[N] b) (z 0) (z 1) = M.op (z 0) (z 1) := hback' (z 0) (z 1)
    show M.op (z 0) (z 1) = _
    rw [← h2, ← bsem_toBTerm W N v (z 0) (z 1)]
    show @Term.realize _ G W.FOStructure₀ _ ![z 0, z 1] _ = _
    rw [vec_eta]

/-- The `TermStructuralFromFin` wrapper: the two `QTerm`s are uniform, only the exponent hidden
inside `toBTerm` is chosen after the magma. -/
theorem termStructuralFromFin_of_qterm {β : Type} {L L' : Law.MagmaLaw β} (q v : QTerm)
    (hr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        @satisfies _ G ⟨q.eval M.op rd ld⟩ L)
    (hwr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        ∀ b : G, Function.Injective fun a ↦ q.eval M.op rd ld a b)
    (hwl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        ∀ a : G, Function.Injective fun b ↦ q.eval M.op rd ld a b)
    (hback : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        ∀ wrd wld : G → G → G,
          (∀ a b, q.eval M.op rd ld (wrd a b) b = a) →
          (∀ a b, wrd (q.eval M.op rd ld a b) b = a) →
          (∀ a b, q.eval M.op rd ld a (wld a b) = b) →
          (∀ a b, wld a (q.eval M.op rd ld a b) = b) →
          ∀ x y : G, v.eval (q.eval M.op rd ld) wrd wld x y = M.op x y) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦
    termStructuralOnMagma_of_qterm M q v (hr G M hM) (hl G M hM) (hsat G M hM)
      (hwr G M hM) (hwl G M hM) (hback G M hM)

/-! ## One division only

Most of the sources this device can use are not quasigroups. Of the 130 laws that force a finite
model's translations to be bijections, 53 do it on both sides but 74 do it on the left alone -- and
those 74 are where the cells are. A witness written in `\` alone is still a magma term there, and
the argument above goes through verbatim once `rd` is never consulted. -/

/-- Whether a `QTerm` avoids right division. For a closed term this is decided by `rfl`, which is
how the generated cells discharge it. -/
def QTerm.noRdv : QTerm → Bool
  | .var _ => true
  | .op a b => a.noRdv && b.noRdv
  | .rdv _ _ => false
  | .ldv a b => a.noRdv && b.noRdv

/-- A term that never divides on the right does not depend on what the right division is. -/
theorem eval_noRdv {q : QTerm} (h : q.noRdv = true) (m ld rd rd' : G → G → G) :
    q.eval m rd ld = q.eval m rd' ld := by
  induction q with
  | var i => rfl
  | op a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    funext x y
    show m _ _ = m _ _
    rw [congrFun (congrFun (iha ha) x) y, congrFun (congrFun (ihb hb) x) y]
  | rdv a b _ _ => exact absurd h (by simp [QTerm.noRdv])
  | ldv a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    funext x y
    show ld _ _ = ld _ _
    rw [congrFun (congrFun (iha ha) x) y, congrFun (congrFun (ihb hb) x) y]

/-- **The glue, left-handed.** Only the left translations are asked to be injective, and both
`QTerm`s are asked to keep away from right division; `ld` then stands in for the right division
everywhere, which `eval_noRdv` says the terms cannot tell. -/
theorem termStructuralOnMagma_of_qtermL [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (q v : QTerm) (hq : q.noRdv = true) (hv : v.noRdv = true)
    (hl : ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ ld : G → G → G,
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      @satisfies _ G ⟨q.eval M.op ld ld⟩ L)
    (hwl : ∀ ld : G → G → G,
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      ∀ a : G, Function.Injective fun b ↦ q.eval M.op ld ld a b)
    (hback : ∀ ld : G → G → G,
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      ∀ wld : G → G → G,
        (∀ a b, q.eval M.op ld ld a (wld a b) = b) →
        (∀ a b, wld a (q.eval M.op ld ld a b) = b) →
        ∀ x y : G, v.eval (q.eval M.op ld ld) wld wld x y = M.op x y) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  have hls (a b : G) : M.op a (ld a b) = b := by
    have h := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hli (a b : G) : ld a (M.op a b) = b := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
  -- the compiled term evaluates at `rd`, the obligations were proved at `ld`; the terms cannot
  -- tell the two apart, so the magma is the same either way
  have hq' : q.eval M.op rd ld = q.eval M.op ld ld := eval_noRdv hq M.op ld rd ld
  let W : Magma G := ⟨q.eval M.op ld ld⟩
  have hWl := hwl ld hls hli
  have hwls (a b : G) : W.op a ((fun u ↦ W.op a u)^[N] b) = b := by
    have h := congrFun (hN (fun u ↦ W.op a u) (hWl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hwli (a b : G) : (fun u ↦ W.op a u)^[N] (W.op a b) = b :=
    congrFun (hN (fun u ↦ W.op a u) (hWl a)) b
  have hback' := hback ld hls hli (fun a b ↦ (fun u ↦ W.op a u)^[N] b) hwls hwli
  refine ⟨W, hsat ld hls hli, ⟨q.toBTerm (G := G) N, ?_⟩, ⟨v.toBTerm (G := G) N, ?_⟩⟩
  · funext z
    show q.eval M.op ld ld (z 0) (z 1) = _
    rw [← congrFun (congrFun hq' (z 0)) (z 1), ← bsem_toBTerm M N q (z 0) (z 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![z 0, z 1] _ = _
    rw [vec_eta]
  · funext z
    have hv' : v.eval W.op (fun a b ↦ (fun u ↦ W.op u b)^[N] a)
        (fun a b ↦ (fun u ↦ W.op a u)^[N] b)
      = v.eval W.op (fun a b ↦ (fun u ↦ W.op a u)^[N] b)
          (fun a b ↦ (fun u ↦ W.op a u)^[N] b) := eval_noRdv hv _ _ _ _
    have h2 : v.eval W.op (fun a b ↦ (fun u ↦ W.op u b)^[N] a)
        (fun a b ↦ (fun u ↦ W.op a u)^[N] b) (z 0) (z 1) = M.op (z 0) (z 1) := by
      rw [congrFun (congrFun hv' (z 0)) (z 1)]
      exact hback' (z 0) (z 1)
    show M.op (z 0) (z 1) = _
    rw [← h2, ← bsem_toBTerm W N v (z 0) (z 1)]
    show @Term.realize _ G W.FOStructure₀ _ ![z 0, z 1] _ = _
    rw [vec_eta]

/-- The `TermStructuralFromFin` wrapper for the left-handed glue. -/
theorem termStructuralFromFin_of_qtermL {β : Type} {L L' : Law.MagmaLaw β} (q v : QTerm)
    (hq : q.noRdv = true) (hv : v.noRdv = true)
    (hl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ ld : G → G → G,
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        @satisfies _ G ⟨q.eval M.op ld ld⟩ L)
    (hwl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ ld : G → G → G,
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        ∀ a : G, Function.Injective fun b ↦ q.eval M.op ld ld a b)
    (hback : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ ld : G → G → G,
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        ∀ wld : G → G → G,
          (∀ a b, q.eval M.op ld ld a (wld a b) = b) →
          (∀ a b, wld a (q.eval M.op ld ld a b) = b) →
          ∀ x y : G, v.eval (q.eval M.op ld ld) wld wld x y = M.op x y) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦
    termStructuralOnMagma_of_qtermL M q v hq hv (hl G M hM) (hsat G M hM) (hwl G M hM)
      (hback G M hM)

/-! ## The other side

Three of the 130 sources are right-handed instead, which is few enough that the mirror would not be
worth writing were it not mechanical: swap the two divisions everywhere and `rd` stands in for `ld`.
-/

/-- Whether a `QTerm` avoids left division. -/
def QTerm.noLdv : QTerm → Bool
  | .var _ => true
  | .op a b => a.noLdv && b.noLdv
  | .rdv a b => a.noLdv && b.noLdv
  | .ldv _ _ => false

/-- A term that never divides on the left does not depend on what the left division is. -/
theorem eval_noLdv {q : QTerm} (h : q.noLdv = true) (m rd ld ld' : G → G → G) :
    q.eval m rd ld = q.eval m rd ld' := by
  induction q with
  | var i => rfl
  | op a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    funext x y
    show m _ _ = m _ _
    rw [congrFun (congrFun (iha ha) x) y, congrFun (congrFun (ihb hb) x) y]
  | rdv a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    funext x y
    show rd _ _ = rd _ _
    rw [congrFun (congrFun (iha ha) x) y, congrFun (congrFun (ihb hb) x) y]
  | ldv a b _ _ => exact absurd h (by simp [QTerm.noLdv])

/-- **The glue, right-handed.** The mirror of `termStructuralOnMagma_of_qtermL`. -/
theorem termStructuralOnMagma_of_qtermR [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (q v : QTerm) (hq : q.noLdv = true) (hv : v.noLdv = true)
    (hr : ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hsat : ∀ rd : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      @satisfies _ G ⟨q.eval M.op rd rd⟩ L)
    (hwr : ∀ rd : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      ∀ b : G, Function.Injective fun a ↦ q.eval M.op rd rd a b)
    (hback : ∀ rd : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      ∀ wrd : G → G → G,
        (∀ a b, q.eval M.op rd rd (wrd a b) b = a) →
        (∀ a b, wrd (q.eval M.op rd rd a b) b = a) →
        ∀ x y : G, v.eval (q.eval M.op rd rd) wrd wrd x y = M.op x y) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  have hrs (a b : G) : M.op (rd a b) b = a := by
    have h := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hri (a b : G) : rd (M.op a b) b = a := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
  have hq' : q.eval M.op rd ld = q.eval M.op rd rd := eval_noLdv hq M.op rd ld rd
  let W : Magma G := ⟨q.eval M.op rd rd⟩
  have hWr := hwr rd hrs hri
  have hwrs (a b : G) : W.op ((fun u ↦ W.op u b)^[N] a) b = a := by
    have h := congrFun (hN (fun u ↦ W.op u b) (hWr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hwri (a b : G) : (fun u ↦ W.op u b)^[N] (W.op a b) = a :=
    congrFun (hN (fun u ↦ W.op u b) (hWr b)) a
  have hback' := hback rd hrs hri (fun a b ↦ (fun u ↦ W.op u b)^[N] a) hwrs hwri
  refine ⟨W, hsat rd hrs hri, ⟨q.toBTerm (G := G) N, ?_⟩, ⟨v.toBTerm (G := G) N, ?_⟩⟩
  · funext z
    show q.eval M.op rd rd (z 0) (z 1) = _
    rw [← congrFun (congrFun hq' (z 0)) (z 1), ← bsem_toBTerm M N q (z 0) (z 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![z 0, z 1] _ = _
    rw [vec_eta]
  · funext z
    have hv' : v.eval W.op (fun a b ↦ (fun u ↦ W.op u b)^[N] a)
        (fun a b ↦ (fun u ↦ W.op a u)^[N] b)
      = v.eval W.op (fun a b ↦ (fun u ↦ W.op u b)^[N] a)
          (fun a b ↦ (fun u ↦ W.op u b)^[N] a) := eval_noLdv hv _ _ _ _
    have h2 : v.eval W.op (fun a b ↦ (fun u ↦ W.op u b)^[N] a)
        (fun a b ↦ (fun u ↦ W.op a u)^[N] b) (z 0) (z 1) = M.op (z 0) (z 1) := by
      rw [congrFun (congrFun hv' (z 0)) (z 1)]
      exact hback' (z 0) (z 1)
    show M.op (z 0) (z 1) = _
    rw [← h2, ← bsem_toBTerm W N v (z 0) (z 1)]
    show @Term.realize _ G W.FOStructure₀ _ ![z 0, z 1] _ = _
    rw [vec_eta]

/-- The `TermStructuralFromFin` wrapper for the right-handed glue. -/
theorem termStructuralFromFin_of_qtermR {β : Type} {L L' : Law.MagmaLaw β} (q v : QTerm)
    (hq : q.noLdv = true) (hv : v.noLdv = true)
    (hr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        @satisfies _ G ⟨q.eval M.op rd rd⟩ L)
    (hwr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        ∀ b : G, Function.Injective fun a ↦ q.eval M.op rd rd a b)
    (hback : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        ∀ wrd : G → G → G,
          (∀ a b, q.eval M.op rd rd (wrd a b) b = a) →
          (∀ a b, wrd (q.eval M.op rd rd a b) b = a) →
          ∀ x y : G, v.eval (q.eval M.op rd rd) wrd wrd x y = M.op x y) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦
    termStructuralOnMagma_of_qtermR M q v hq hv (hr G M hM) (hsat G M hM) (hwr G M hM)
      (hback G M hM)

end Law.MagmaLaw
