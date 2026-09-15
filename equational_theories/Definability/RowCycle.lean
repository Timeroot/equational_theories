import equational_theories.Definability.CaseSplit

/-!
# Reversing distinguished row cycles: E56 → E50 and E440 → E414

Write `d(x) = x ◇ x` and `c(x) = x ◇ d(x)`. E56 says that every `c(y)`
is a right identity. Consequently the row at `x` cycles through
`x → d(x) → c(x) → x`; these three points are either distinct or all equal.

Postcompose that row with the cycle `(x d(x) c(x))`. The resulting operation
`□` has `x □ x = c(x)`, `x □ c(y) = d(x)` and `x □ d(x) = x`, so satisfies E50.
Crucially, postcomposition permutes outputs rather than discarding any entries.
The original distinguished points can be read as `c(x) = x □ x` and
`d(x) = x □ (x □ x)`, so the inverse permutation recovers the entire original row.

Both directions use only equality tests between terms. No finiteness, choice of
a global identity, or cancellation hypothesis is needed.

The four-step version below handles E440. Its distinguished orbit has length
one, two, or four. Postcomposing with its half-turn reverses the orbit, and the
half-turn is its own inverse. Again, no information off the orbit is lost.
-/

open Law Law.MagmaLaw FreeMagma
namespace RowCycle

variable {G : Type}

open scoped Classical in
noncomputable def rotate (x d c a : G) : G :=
  if a = x then d else if a = d then c else if a = c then x else a

open scoped Classical in
noncomputable def unrotate (x d c a : G) : G :=
  if a = d then x else if a = c then d else if a = x then c else a

def Cycle (x d c : G) : Prop :=
  (d = x ∧ c = x) ∨ (d ≠ x ∧ c ≠ x ∧ c ≠ d)

theorem rotate_x (x d c : G) : rotate x d c x = d := by simp [rotate]

theorem rotate_d {x d c : G} (h : Cycle x d c) : rotate x d c d = c := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hd, hc, hcd⟩ <;> simp_all [rotate]

theorem rotate_c {x d c : G} (h : Cycle x d c) : rotate x d c c = x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hd, hc, hcd⟩ <;> simp_all [rotate]

theorem unrotate_rotate {x d c : G} (h : Cycle x d c) (a : G) :
    unrotate x d c (rotate x d c a) = a := by
  classical
  rcases h with ⟨rfl, rfl⟩ | ⟨hd, hc, hcd⟩
  · by_cases ha : a = c <;> simp_all [rotate, unrotate]
  · by_cases ha : a = x
    · rw [ha]; simp [rotate, unrotate]
    by_cases hb : a = d
    · rw [hb]; simp [rotate, unrotate, hd, hcd]
    by_cases he : a = c
    · rw [he]; simp [rotate, unrotate, hc, hcd, Ne.symm hd, Ne.symm hc]
    simp [rotate, unrotate, ha, hb, he]

theorem cycle (M : Magma G) (h : @Equation56 G M) (x : G) :
    Cycle x (M.op x x) (M.op x (M.op x x)) := by
  have hi (a b : G) : M.op a (M.op b (M.op b b)) = a := (h a b).symm
  by_cases hd : M.op x x = x
  · exact Or.inl ⟨hd, by rw [hd, hd]⟩
  refine Or.inr ⟨hd, ?_, ?_⟩
  · intro hc
    exact hd (by simpa only [hc] using hi x x)
  · intro hc
    have hx : M.op x (M.op x x) = x := by simpa only [hc] using hi x x
    exact hd (hc.symm.trans hx)

private abbrev x : FreeMagma (Fin 2) := Lf 0
private abbrev y : FreeMagma (Fin 2) := Lf 1
private abbrev d : FreeMagma (Fin 2) := x ⋆ x
private abbrev c : FreeMagma (Fin 2) := x ⋆ d

/-- Postcompose each source row with its distinguished cycle. -/
def forward : QFOp :=
  .ite (x ⋆ y) x (.leaf d)
    (.ite (x ⋆ y) d (.leaf c) (.ite (x ⋆ y) c (.leaf x) (.leaf (x ⋆ y))))

/-- Read the distinguished points in the companion and undo the permutation. -/
def backward : QFOp :=
  .ite (x ⋆ y) c (.leaf x)
    (.ite (x ⋆ y) d (.leaf c) (.ite (x ⋆ y) x (.leaf d) (.leaf (x ⋆ y))))

theorem forward_apply (M : Magma G) (a b : G) :
    (forward.magma M).op a b = rotate a (M.op a a) (M.op a (M.op a a)) (M.op a b) := rfl

theorem backward_apply (N : Magma G) (a b : G) :
    (backward.magma N).op a b = unrotate a (N.op a (N.op a a)) (N.op a a) (N.op a b) := rfl

theorem square (M : Magma G) (h : @Equation56 G M) (a : G) :
    (forward.magma M).op a a = M.op a (M.op a a) :=
  rotate_d (cycle M h a)

theorem on_cube (M : Magma G) (h : @Equation56 G M) (a b : G) :
    (forward.magma M).op a (M.op b (M.op b b)) = M.op a a := by
  rw [forward_apply, ← h a b, rotate_x]

theorem recover_square (M : Magma G) (h : @Equation56 G M) (a : G) :
    (forward.magma M).op a ((forward.magma M).op a a) = M.op a a := by
  rw [square M h, on_cube M h]

theorem satisfies_50 (M : Magma G) (h : @Equation56 G M) :
    @Equation50 G (forward.magma M) := by
  intro a b
  rw [square M h, on_cube M h, forward_apply]
  exact (rotate_c (cycle M h a)).symm

theorem recover (M : Magma G) (h : @Equation56 G M) :
    backward.magma (forward.magma M) = M := by
  change Magma.mk _ = Magma.mk M.op
  apply congrArg Magma.mk
  funext a b
  change (backward.magma (forward.magma M)).op a b = M.op a b
  rw [backward_apply, recover_square _ h, square _ h, forward_apply]
  exact unrotate_rotate (cycle _ h a) _

namespace Four

/-- A four-step periodic orbit has either period dividing two, or four distinct points. -/
def Cycle (x p q r : G) : Prop :=
  (q = x ∧ r = p) ∨ (p ≠ x ∧ q ≠ x ∧ r ≠ x ∧ q ≠ p ∧ r ≠ p ∧ r ≠ q)

open scoped Classical in
noncomputable def turn (x p q r a : G) : G :=
  if a = x then q else if a = p then r else if a = q then x else if a = r then p else a

theorem turn_x (x p q r : G) : turn x p q r x = q := by simp [turn]

theorem turn_p {x p q r : G} (h : Cycle x p q r) : turn x p q r p = r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hp, hq, hr, hqp, hrp, hrq⟩
  · unfold turn; split_ifs <;> grind
  · simp [turn, hp]

theorem turn_q {x p q r : G} (h : Cycle x p q r) : turn x p q r q = x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hp, hq, hr, hqp, hrp, hrq⟩ <;> simp_all [turn]

theorem turn_r {x p q r : G} (h : Cycle x p q r) : turn x p q r r = p := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hp, hq, hr, hqp, hrp, hrq⟩
  · unfold turn; split_ifs <;> grind
  · simp [turn, hr, hrp, hrq]

theorem turn_turn {x p q r : G} (h : Cycle x p q r) (a : G) :
    turn x p q r (turn x p q r a) = a := by
  classical
  by_cases hx : a = x
  · rw [hx, turn_x, turn_q h]
  by_cases hp : a = p
  · rw [hp, turn_p h, turn_r h]
  by_cases hq : a = q
  · rw [hq, turn_q h, turn_x]
  by_cases hr : a = r
  · rw [hr, turn_r h, turn_p h]
  simp [turn, hx, hp, hq, hr]

theorem cycle (M : Magma G) (h : @Equation440 G M) (a : G) :
    Cycle a (M.op a a) (M.op a (M.op a a)) (M.op a (M.op a (M.op a a))) := by
  have hi := (h a a).symm
  by_cases hq : M.op a (M.op a a) = a
  · exact Or.inl ⟨hq, congrArg (M.op a) hq⟩
  · right
    dsimp only
    grind

private abbrev r : FreeMagma (Fin 2) := x ⋆ c

/-- Half-turn on the four-step source orbit. -/
def forward : QFOp :=
  .ite (x ⋆ y) x (.leaf c)
    (.ite (x ⋆ y) d (.leaf r)
      (.ite (x ⋆ y) c (.leaf x) (.ite (x ⋆ y) r (.leaf d) (.leaf (x ⋆ y)))))

/-- The companion reads the orbit in reverse; apply the same half-turn. -/
def backward : QFOp :=
  .ite (x ⋆ y) x (.leaf c)
    (.ite (x ⋆ y) r (.leaf d)
      (.ite (x ⋆ y) c (.leaf x) (.ite (x ⋆ y) d (.leaf r) (.leaf (x ⋆ y)))))

theorem forward_apply (M : Magma G) (a b : G) :
    (forward.magma M).op a b =
      turn a (M.op a a) (M.op a (M.op a a)) (M.op a (M.op a (M.op a a))) (M.op a b) := rfl

theorem backward_apply (N : Magma G) (a b : G) :
    (backward.magma N).op a b =
      turn a (N.op a (N.op a (N.op a a))) (N.op a (N.op a a)) (N.op a a) (N.op a b) := rfl

theorem square (M : Magma G) (h : @Equation440 G M) (a : G) :
    (forward.magma M).op a a = M.op a (M.op a (M.op a a)) := turn_p (cycle M h a)

theorem on_unit (M : Magma G) (h : @Equation440 G M) (a b : G) :
    (forward.magma M).op a (M.op b (M.op b (M.op b b))) = M.op a (M.op a a) := by
  rw [forward_apply, ← h a b, turn_x]

theorem on_cube (M : Magma G) (h : @Equation440 G M) (a : G) :
    (forward.magma M).op a (M.op a (M.op a a)) = M.op a a := turn_r (cycle M h a)

theorem recover_cube (M : Magma G) (h : @Equation440 G M) (a : G) :
    (forward.magma M).op a ((forward.magma M).op a a) = M.op a (M.op a a) := by
  rw [square M h, on_unit M h]

theorem recover_square (M : Magma G) (h : @Equation440 G M) (a : G) :
    (forward.magma M).op a ((forward.magma M).op a ((forward.magma M).op a a)) = M.op a a := by
  rw [recover_cube M h, on_cube M h]

theorem satisfies_414 (M : Magma G) (h : @Equation440 G M) :
    @Equation414 G (forward.magma M) := by
  intro a b
  rw [square M h, on_unit M h, on_cube M h, forward_apply]
  exact (turn_q (cycle M h a)).symm

theorem recover (M : Magma G) (h : @Equation440 G M) :
    backward.magma (forward.magma M) = M := by
  change Magma.mk _ = Magma.mk M.op
  apply congrArg Magma.mk
  funext a b
  change (backward.magma (forward.magma M)).op a b = M.op a b
  rw [backward_apply, recover_square _ h, recover_cube _ h, square _ h, forward_apply]
  exact turn_turn (cycle _ h a) _

end Four
end RowCycle

namespace Law.MagmaLaw

/-- Reverse each distinguished row cycle, preserving all information in the operation. -/
theorem Equation50_structuralFrom_Equation56_rowCycle : Law50.StructuralFrom Law56 := by
  intro G M hM
  have h := (@Law56.models_iff G M).mp hM
  refine ⟨RowCycle.forward.magma M, (@Law50.models_iff G (RowCycle.forward.magma M)).mpr (RowCycle.satisfies_50 M h),
    RowCycle.forward.definable_graph M, ?_⟩
  simpa only [RowCycle.recover M h] using
    RowCycle.backward.definable_graph (RowCycle.forward.magma M)

/-- info: 'Law.MagmaLaw.Equation50_structuralFrom_Equation56_rowCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation50_structuralFrom_Equation56_rowCycle

/-- The four-step orbit version works on arbitrary, not just finite, magmas. -/
theorem Equation414_structuralFrom_Equation440_rowCycle : Law414.StructuralFrom Law440 := by
  intro G M hM
  have h := (@Law440.models_iff G M).mp hM
  refine ⟨RowCycle.Four.forward.magma M,
    (@Law414.models_iff G (RowCycle.Four.forward.magma M)).mpr (RowCycle.Four.satisfies_414 M h),
    RowCycle.Four.forward.definable_graph M, ?_⟩
  simpa only [RowCycle.Four.recover M h] using
    RowCycle.Four.backward.definable_graph (RowCycle.Four.forward.magma M)

/--
info: 'Law.MagmaLaw.Equation414_structuralFrom_Equation440_rowCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Equation414_structuralFrom_Equation440_rowCycle

end Law.MagmaLaw
