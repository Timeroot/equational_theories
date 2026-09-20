/-! A compiled, constant-space traversal of a finite interval. -/
namespace DefOrbit

/-- Check every code below `n`, stopping at the first failure. -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => if f n then allBelow f n else false

end DefOrbit
