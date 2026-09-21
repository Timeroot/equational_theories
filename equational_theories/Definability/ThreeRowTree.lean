import equational_theories.Definability.UnaryRayCompanions
import Mathlib.Data.List.Chain

/-! An infinite E1133 magma whose square-row transform fails E1167.

Eleven finite states color three copies of the tree of reduced words in three
involutions. The finite transition identities imply E1133 at every vertex.
This refutes a proposed uniform term, not term-structural definability itself.
-/

namespace ThreeRowTree

abbrev Color := Fin 3
abbrev State := Fin 11

def color : State → Color := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 0]
def profile : State → Color → Color :=
  ![![0,0,0], ![1,1,1], ![2,2,2],
    ![0,0,0], ![1,1,1], ![2,2,2],
    ![0,0,0], ![1,1,1], ![2,2,2], ![0,1,0], ![0,1,1]]
def next : State → Color → State :=
  ![![0,0,0], ![3,3,3], ![6,6,6],
    ![1,1,1], ![4,9,4], ![7,7,7],
    ![2,2,2], ![5,5,5], ![8,8,8], ![1,4,10], ![0,3,3]]
def initial : Color → State := ![0,4,8]

theorem next_color : ∀ s j, color (next s j) = profile s j := by decide
theorem next_back : ∀ s j, profile (next s j) j = color s := by decide
theorem profile_idem : ∀ s j, profile s (profile s j) = profile s j := by decide

def toggle (j : Color) : List Color → List Color
  | [] => [j]
  | k :: w => if j = k then w else j :: k :: w

theorem toggle_chain (j : Color) (w : List Color) (h : w.IsChain (· ≠ ·)) :
    (toggle j w).IsChain (· ≠ ·) := by
  cases w with
  | nil => simp [toggle]
  | cons k w =>
    by_cases e : j = k
    · simpa [toggle, e] using h.tail
    · simpa [toggle, e, List.isChain_cons_cons] using And.intro e h

theorem toggle_invol (j : Color) (w : List Color) (h : w.IsChain (· ≠ ·)) :
    toggle j (toggle j w) = w := by
  cases w with
  | nil => simp [toggle]
  | cons k w =>
    by_cases e : j = k
    · subst k
      cases w with
      | nil => simp [toggle]
      | cons k w =>
        have hn : j ≠ k := (List.isChain_cons_cons.mp h).1
        simp [toggle, hn]
    · simp [toggle, e]

abbrev Vertex := Color × {w : List Color // w.IsChain (· ≠ ·)}

def move (j : Color) (v : Vertex) : Vertex :=
  (v.1, ⟨toggle j v.2.val, toggle_chain j v.2.val v.2.property⟩)

theorem move_invol (j : Color) (v : Vertex) : move j (move j v) = v := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact toggle_invol j v.2.val v.2.property

def state (r : Color) : List Color → State
  | [] => initial r
  | j :: w => next (state r w) j

def vertexState (v : Vertex) : State := state v.1 v.2.val
def vertexColor (v : Vertex) : Color := color (vertexState v)

theorem move_color (j : Color) (v : Vertex) :
    vertexColor (move j v) = profile (vertexState v) j := by
  rcases v with ⟨r, ⟨w, hw⟩⟩
  cases w with
  | nil => exact next_color (initial r) j
  | cons k w =>
    by_cases e : j = k
    · subst k
      simpa [vertexColor, vertexState, move, toggle, state] using
        (next_back (state r w) j).symm
    · simpa [vertexColor, vertexState, move, toggle, state, e] using
        next_color (next (state r w) k) j

@[implicit_reducible] def magma : Magma Vertex := ⟨fun x y => move (vertexColor x) y⟩

theorem row_law (y z : Vertex) :
    vertexColor (magma.op y (magma.op z y)) = vertexColor y := by
  let w := move (vertexColor z) y
  have e : profile (vertexState w) (vertexColor z) = vertexColor y := by
    rw [← move_color]
    exact congrArg vertexColor (move_invol (vertexColor z) y)
  change vertexColor (move (vertexColor y) w) = vertexColor y
  rw [move_color, ← e, profile_idem]

theorem source_law : @Equation1133 Vertex magma := by
  intro x y z
  change x = move (vertexColor y)
    (move (vertexColor (magma.op y (magma.op z y))) x)
  rw [row_law, move_invol]

def root (r : Color) : Vertex := (r, ⟨[], by simp⟩)

theorem transformed_not_1167 :
    ¬ @Equation1167 Vertex (SquareRowRecovery.transform magma) := by
  intro h
  have e := h (root 0) (root 1) (root 2)
  have bad : (root 0) ≠
      (SquareRowRecovery.transform magma).op (root 1)
        ((SquareRowRecovery.transform magma).op
          ((SquareRowRecovery.transform magma).op (root 2)
            ((SquareRowRecovery.transform magma).op (root 1) (root 1))) (root 0)) := by
    decide
  exact bad e

theorem recovery (x y : Vertex) :
    (SquareRowRecovery.transform (SquareRowRecovery.transform magma)).op x y = magma.op x y :=
  SquareRowRecovery.recover magma source_law x y

end ThreeRowTree

/-- info: 'ThreeRowTree.source_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeRowTree.source_law
/-- info: 'ThreeRowTree.transformed_not_1167' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeRowTree.transformed_not_1167
/-- info: 'ThreeRowTree.recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeRowTree.recovery
