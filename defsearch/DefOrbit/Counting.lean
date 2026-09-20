/-! Compiled counting over a finite interval, without allocating the interval. -/
namespace DefOrbit

def countAux (f : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countAux f n (acc + if f n then 1 else 0)

def countBelow (f : Nat → Bool) (n : Nat) : Nat := countAux f n 0

end DefOrbit
