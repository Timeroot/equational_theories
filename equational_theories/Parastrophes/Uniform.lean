import equational_theories.Parastrophes.Basic
import equational_theories.Completeness
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.OrderOfElement

/-! The free two-generated model makes model-dependent term recovery uniform on
all carriers. In fact, if every model of an identity is a quasigroup, its divisions
already have uniform terms. Neither argument applies to finite carriers alone. -/
namespace Parastrophes
open Law FreeMagma

private theorem map_term {G H : Type} [M : Magma G] [N : Magma H]
    (f : G →◇ H) (t : FreeMagma (Fin 2)) (x y : G) :
    f ((termMagma M t).op x y) = (termMagma N t).op (f x) (f y) := by
  change f (@evalInMagma _ _ M (fun i => if i = 0 then x else y) t) =
    @evalInMagma _ _ N (fun i => if i = 0 then f x else f y) t
  rw [evalInMagma_hom]
  congr 1
  funext i
  simp only [Function.comp_apply]
  split_ifs <;> rfl

private abbrev Free (L : NatMagmaLaw) := FreeMagmaWithLaws (Fin 2) ({L} : Ctx Nat)
private abbrev gen (L : NatMagmaLaw) (i : Fin 2) : Free L := embed {L} (Lf i)

private theorem free_holds (L : NatMagmaLaw) : satisfies (Free L) L :=
  FreeMagmaWithLaws.isModel (Fin 2) {L} L (Set.mem_singleton L)

private def evaluate {G : Type} (M : Magma G) {L : NatMagmaLaw}
    (h : @satisfies _ G M L) (x y : G) : @MagmaHom (Free L) G _ M :=
  @FreeMagmaWithLaws.evalHom _ _ _ {L} (fun i => if i = 0 then x else y) M
    (by intro E he; have : E = L := Set.mem_singleton_iff.mp he; subst E; exact h)

private theorem evaluate_gen {G : Type} (M : Magma G) {L : NatMagmaLaw}
    (h : @satisfies _ G M L) (x y : G) (i : Fin 2) :
    evaluate M h x y (gen L i) = if i = 0 then x else y := rfl

/-- No compactness or bound on term length is needed: use the free two-generated model. -/
theorem termRecovery_iff_uniform_all {L side} :
    TermRecovery .all L side ↔ UniformTermRecovery .all L side := by
  refine ⟨?_, uniform_implies_term⟩
  intro h
  obtain ⟨t, ht⟩ := h (Free L) inferInstance trivial (free_holds L)
  refine ⟨t, ?_⟩
  intro G M _ hM
  letI := M
  cases side <;> constructor <;> intro x y
  all_goals
    let f := evaluate M hM x y
    first
    | simpa only [MagmaHom.map_op, map_term, evaluate_gen, Fin.isValue, ↓reduceIte,
        zero_ne_one, one_ne_zero] using congrArg f (ht.1 (gen L 0) (gen L 1))
    | simpa only [MagmaHom.map_op, map_term, evaluate_gen, Fin.isValue, ↓reduceIte,
        zero_ne_one, one_ne_zero] using congrArg f (ht.2 (gen L 0) (gen L 1))

/-- A variety of quasigroups in the multiplication-only language has uniform division terms. -/
theorem quasigroup_uniform_all {L} (h : QuasigroupLaw .all L) (side : Side) :
    UniformTermRecovery .all L side := by
  have hF := h (Free L) inferInstance trivial (free_holds L)
  have hex : ∃ z : Free L, (match side with
      | .left => (gen L 0) ◇ z = gen L 1
      | .right => z ◇ (gen L 1) = gen L 0) := by
    cases side with
    | left => exact (hF.1 (gen L 0)).2 (gen L 1)
    | right => exact (hF.2 (gen L 1)).2 (gen L 0)
  obtain ⟨z, hz⟩ := hex
  obtain ⟨t, ht⟩ := Quotient.exists_rep z
  have hterm {G : Type} (M : Magma G) (hM : @satisfies _ G M L) (x y : G) :
      evaluate M hM x y z = (termMagma M t).op x y := by rw [← ht]; rfl
  refine ⟨t, ?_⟩
  intro G M _ hM
  letI := M
  have hQ := h G M trivial hM
  cases side with
  | left =>
    have hi (x y : G) : M.op x ((termMagma M t).op x y) = y := by
      have he := congrArg (evaluate M hM x y) hz
      simpa only [MagmaHom.map_op, evaluate_gen, hterm, Fin.isValue, ↓reduceIte,
        one_ne_zero] using he
    exact ⟨hi, fun x y => (hQ.1 x).1 (hi x (M.op x y))⟩
  | right =>
    have hi (x y : G) : M.op ((termMagma M t).op x y) y = x := by
      have he := congrArg (evaluate M hM x y) hz
      simpa only [MagmaHom.map_op, evaluate_gen, hterm, Fin.isValue, ↓reduceIte,
        one_ne_zero] using he
    exact ⟨hi, fun x y => (hQ.2 y).1 (hi (M.op x y) y)⟩

private def iterateTerm : Side → Nat → FreeMagma (Fin 2)
  | .left, 0 => Lf 1
  | .right, 0 => Lf 0
  | .left, n + 1 => Lf 0 ⋆ iterateTerm .left n
  | .right, n + 1 => iterateTerm .right n ⋆ Lf 1

private theorem iterateTerm_left {G : Type} (M : Magma G) (n : Nat) (x y : G) :
    (termMagma M (iterateTerm .left n)).op x y = (M.op x)^[n] y := by
  induction n with
  | zero => rfl
  | succ n hn => exact (congrArg (M.op x) hn).trans (Function.iterate_succ_apply' (M.op x) n y).symm

private theorem iterateTerm_right {G : Type} (M : Magma G) (n : Nat) (x y : G) :
    (termMagma M (iterateTerm .right n)).op x y = (fun z => M.op z y)^[n] x := by
  induction n with
  | zero => rfl
  | succ n hn => exact (congrArg (fun z => M.op z y) hn).trans (Function.iterate_succ_apply' (fun z => M.op z y) n x).symm

/-- In a finite quasigroup, inverse translations are powers of translations.
The exponent depends on the carrier size, so this does not assert a uniform term. -/
theorem quasigroup_term_fin {L} (h : QuasigroupLaw .fin L) (side : Side) :
    TermRecovery .fin L side := by
  intro G M hG hM
  classical
  letI : Finite G := hG
  letI : Fintype G := Fintype.ofFinite G
  let n := Fintype.card (Equiv.Perm G)
  have hn : 0 < n := Fintype.card_pos
  have period (f : G → G) (hf : Function.Bijective f) : f^[n] = id := by
    have hp := congrArg (fun p : Equiv.Perm G => (p : G → G))
      (pow_card_eq_one (x := Equiv.ofBijective f hf))
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one] using hp
  have inv (f : G → G) (hf : Function.Bijective f) (x : G) :
      f (f^[n-1] x) = x ∧ f^[n-1] (f x) = x := by
    have hp := congrFun (period f hf) x
    constructor
    · rw [← Function.iterate_succ_apply' f (n-1) x, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      exact hp
    · rw [← Function.iterate_succ_apply f (n-1) x, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      exact hp
  have hQ := h G M hG hM
  refine ⟨iterateTerm side (n-1), ?_⟩
  cases side <;> constructor <;> intro x y
  · rw [iterateTerm_left]; exact (inv (M.op x) (hQ.1 x) y).1
  · rw [iterateTerm_left]; exact (inv (M.op x) (hQ.1 x) y).2
  · rw [iterateTerm_right]; exact (inv (fun z => M.op z y) (hQ.2 y) x).1
  · rw [iterateTerm_right]; exact (inv (fun z => M.op z y) (hQ.2 y) x).2

end Parastrophes
