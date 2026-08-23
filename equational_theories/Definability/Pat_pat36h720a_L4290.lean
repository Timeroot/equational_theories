import equational_theories.Definability.Pat_pat36h720a_data
import equational_theories.Definability.Prune

/-! # No coordinate shuffle on Fin 36 invariant operation satisfies equation 4290 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the pat36h720a group on tuples: enough to prune the
search for equation 4290 exactly as hard as all `36^2` of them. -/
def envtpat36h720a_Law4290 : List (List Nat) := [[0, 0], [0, 1], [0, 6], [0, 7], [0, 8], [1, 0], [1, 1], [1, 2], [1, 6], [1, 7], [1, 8], [1, 12], [1, 13], [1, 14], [1, 15]]

def envpat36h720a_Law4290 : List (ℕ → Fin 36) :=
  envtpat36h720a_Law4290.map fun u i ↦ ⟨u.getD i 0 % 36, Nat.mod_lt _ (by decide)⟩

/-- The order the orbits of the pat36h720a family are assigned in when refuting equation
4290. Any order is sound; this one was searched for. -/
def ordpat36h720a_Law4290 : List (Fin 15) := List.finRange 15

/-- No pat36h720a-invariant operation on `Fin 36` satisfies equation 4290: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem nopat36h720a_Law4290 : Magma.searchT pat36h720a.E Law4290
    envpat36h720a_Law4290 (ordpat36h720a_Law4290.map fun i ↦
      ((i, (List.finRange 36).filter (Magma.orbitOK pat36h720a.E pat36h720a.z pat36h720a.st i ·)),
        Magma.cells pat36h720a.tr i))
    (Array.replicate (36 * 36) none) = true := by
  native_decide
