import equational_theories.Definability.ExactEnd7

/-!
# The exact-endomorphism class `C` on `Fin 7`

One class of `Definability/ExactEnd7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `24`: `⟨(1 2)(3 4 5 6), (1 3 2 5)(4 6)⟩`

`End(M)` is `25` maps, so `Aut(M)` -- its unit group -- is these `24` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `6` orbit values rather than `49`
independent cells. -/

/-- The `24` elements of the group: `()`, `(3 4)(5 6)`, `(3 5)(4 6)`, `(3 6)(4 5)`, `(1 2)(4 6)`,
`(1 2)(3 4 5 6)`, `(1 2)(3 5)`, `(1 2)(3 6 5 4)`, `(1 3)(2 5)`, `(1 3 2 5)(4 6)`, `(1 3 4)(2 5 6)`,
`(1 3 6)(2 5 4)`, `(1 4 3)(2 6 5)`, `(1 4 5)(2 6 3)`, `(1 4)(2 6)`, `(1 4 2 6)(3 5)`, `(1 5 2 3)(4
6)`, `(1 5)(2 3)`, `(1 5 6)(2 3 4)`, `(1 5 4)(2 3 6)`, `(1 6 3)(2 4 5)`, `(1 6 5)(2 4 3)`, `(1 6)(2
4)`, `(1 6 2 4)(3 5)`. -/
def pE7C0 : Fin 7 → Fin 7 := id
def pE7C1 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pE7C2 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4
def pE7C3 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 3
def pE7C4 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 5 | 6 => 4
def pE7C5 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 3
def pE7C6 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 6
def pE7C7 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 6 | 4 => 3 | 5 => 4 | 6 => 5
def pE7C8 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 2 | 6 => 6
def pE7C9 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 6 | 5 => 1 | 6 => 4
def pE7C10 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 2
def pE7C11 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 4 | 6 => 1
def pE7C12 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 5
def pE7C13 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 1 | 6 => 3
def pE7C14 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 2
def pE7C15 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 1
def pE7C16 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 2 | 6 => 4
def pE7C17 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 1 | 6 => 6
def pE7C18 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 1
def pE7C19 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 6 | 4 => 1 | 5 => 4 | 6 => 2
def pE7C20 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 2 | 6 => 3
def pE7C21 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1 | 6 => 5
def pE7C22 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 1
def pE7C23 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 2

def permE7C : Fin 24 → Fin 7 → Fin 7
  | 0 => pE7C0
  | 1 => pE7C1
  | 2 => pE7C2
  | 3 => pE7C3
  | 4 => pE7C4
  | 5 => pE7C5
  | 6 => pE7C6
  | 7 => pE7C7
  | 8 => pE7C8
  | 9 => pE7C9
  | 10 => pE7C10
  | 11 => pE7C11
  | 12 => pE7C12
  | 13 => pE7C13
  | 14 => pE7C14
  | 15 => pE7C15
  | 16 => pE7C16
  | 17 => pE7C17
  | 18 => pE7C18
  | 19 => pE7C19
  | 20 => pE7C20
  | 21 => pE7C21
  | 22 => pE7C22
  | _ => pE7C23

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `823543` self-maps of `Fin 7`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps7` indexes the self-maps, digit by digit. -/

/-- Indices of the `25` self-maps that must be endomorphisms: `0000000`, `0465231`, `0356241`,
`0643251`, `0534261`, `0645132`, `0536142`, `0463152`, `0354162`, `0462513`, `0641523`, `0126543`,
... (each written as its list of values at `0, 1, ..., 6`). -/
def eidx7C : Fin 25 → Fin 823543
  | 0 => 0
  | 1 => 174909
  | 2 => 192003
  | 3 => 207753
  | 4 => 224847
  | 5 => 290073
  | 6 => 307167
  | 7 => 323085
  | 8 => 340179
  | 9 => 382767
  | 10 => 399147
  | 11 => 434343
  | 12 => 467229
  | 13 => 502761
  | 14 => 519141
  | 15 => 537243
  | 16 => 570129
  | 17 => 613179
  | 18 => 629727
  | 19 => 664797
  | 20 => 697767
  | 21 => 733173
  | 22 => 749721
  | 23 => 767697
  | _ => 800667

def endE7C (j : Fin 25) : Fin 7 → Fin 7 := allMaps7 (eidx7C j)

/-- Indices of the other `823518`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset7C : Array Nat := #[
  0, 174909, 192003, 207753, 224847, 290073, 307167, 323085, 340179, 382767, 399147, 434343,
  467229, 502761, 519141, 537243, 570129, 613179, 629727, 664797, 697767, 733173, 749721, 767697,
  800667]

def xarr7C : Array Nat := Id.run do
  let mut out := Array.mkEmpty 823518
  let mut k := 0
  for i in [0:823543] do
    if k < eset7C.size && eset7C[k]! == i then
      k := k + 1
    else
      out := out.push i
  return out

def xidx7C (j : Fin 823518) : Fin 823543 :=
  ⟨min (xarr7C.getD j.1 0) 823542, by omega⟩

def endX7C (j : Fin 823518) : Fin 7 → Fin 7 := allMaps7 (xidx7C j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end7C` is given. -/
def uidx7C : Fin 24 → Fin 25
  | 0 => 24
  | 1 => 20
  | 2 => 15
  | 3 => 11
  | 4 => 16
  | 5 => 12
  | 6 => 23
  | 7 => 19
  | 8 => 22
  | 9 => 13
  | 10 => 8
  | 11 => 2
  | 12 => 18
  | 13 => 9
  | 14 => 7
  | 15 => 1
  | 16 => 14
  | 17 => 21
  | 18 => 4
  | 19 => 6
  | 20 => 10
  | 21 => 17
  | 22 => 3
  | _ => 5

theorem permE7C_eq_endE7C (i : Fin 24) : permE7C i = endE7C (uidx7C i) := by
  revert i; decide

/-- One representative per orbit of the group on the `49` cells; there are `6`, so an invariant
operation is `6` values. -/
def rep7C : Fin 6 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)
  | 5 => (1, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr7C : Fin 7 → Fin 7 → Fin 6 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 4)
  | 0, 3 => (1, 8)
  | 0, 4 => (1, 12)
  | 0, 5 => (1, 16)
  | 0, 6 => (1, 20)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (5, 0)
  | 1, 4 => (5, 1)
  | 1, 5 => (5, 2)
  | 1, 6 => (5, 3)
  | 2, 0 => (2, 4)
  | 2, 1 => (4, 4)
  | 2, 2 => (3, 4)
  | 2, 3 => (5, 4)
  | 2, 4 => (5, 5)
  | 2, 5 => (5, 6)
  | 2, 6 => (5, 7)
  | 3, 0 => (2, 8)
  | 3, 1 => (5, 8)
  | 3, 2 => (5, 9)
  | 3, 3 => (3, 8)
  | 3, 4 => (5, 10)
  | 3, 5 => (4, 8)
  | 3, 6 => (5, 11)
  | 4, 0 => (2, 12)
  | 4, 1 => (5, 12)
  | 4, 2 => (5, 13)
  | 4, 3 => (5, 14)
  | 4, 4 => (3, 12)
  | 4, 5 => (5, 15)
  | 4, 6 => (4, 12)
  | 5, 0 => (2, 16)
  | 5, 1 => (5, 16)
  | 5, 2 => (5, 17)
  | 5, 3 => (4, 16)
  | 5, 4 => (5, 18)
  | 5, 5 => (3, 16)
  | 5, 6 => (5, 19)
  | 6, 0 => (2, 20)
  | 6, 1 => (5, 20)
  | 6, 2 => (5, 21)
  | 6, 3 => (5, 22)
  | 6, 4 => (4, 20)
  | 6, 5 => (5, 23)
  | 6, 6 => (3, 20)

/-- The `24` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx7C0 : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 15
  | 16 => 16
  | 17 => 17
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 21
  | 22 => 22
  | _ => 23
def val7C0 : Fin 1 → Fin 7
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx7C1 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val7C1 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx7C2 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val7C2 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx7C3 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val7C3 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx7C4 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val7C4 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdx7C5 : Fin 1 → Fin 24
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def dec7C (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Fin 6 → Fin 7
  | 0 => val7C0 a
  | 1 => val7C1 b
  | 2 => val7C2 c
  | 3 => val7C3 d
  | 4 => val7C4 e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab7C_eq_transport`). -/
def tab7C (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => val7C0 a
  | 0, 1 => val7C1 b
  | 0, 2 => pE7C4 (val7C1 b)
  | 0, 3 => pE7C8 (val7C1 b)
  | 0, 4 => pE7C12 (val7C1 b)
  | 0, 5 => pE7C16 (val7C1 b)
  | 0, 6 => pE7C20 (val7C1 b)
  | 1, 0 => val7C2 c
  | 1, 1 => val7C3 d
  | 1, 2 => val7C4 e
  | 1, 3 => f
  | 1, 4 => pE7C1 f
  | 1, 5 => pE7C2 f
  | 1, 6 => pE7C3 f
  | 2, 0 => pE7C4 (val7C2 c)
  | 2, 1 => pE7C4 (val7C4 e)
  | 2, 2 => pE7C4 (val7C3 d)
  | 2, 3 => pE7C4 f
  | 2, 4 => pE7C5 f
  | 2, 5 => pE7C6 f
  | 2, 6 => pE7C7 f
  | 3, 0 => pE7C8 (val7C2 c)
  | 3, 1 => pE7C8 f
  | 3, 2 => pE7C9 f
  | 3, 3 => pE7C8 (val7C3 d)
  | 3, 4 => pE7C10 f
  | 3, 5 => pE7C8 (val7C4 e)
  | 3, 6 => pE7C11 f
  | 4, 0 => pE7C12 (val7C2 c)
  | 4, 1 => pE7C12 f
  | 4, 2 => pE7C13 f
  | 4, 3 => pE7C14 f
  | 4, 4 => pE7C12 (val7C3 d)
  | 4, 5 => pE7C15 f
  | 4, 6 => pE7C12 (val7C4 e)
  | 5, 0 => pE7C16 (val7C2 c)
  | 5, 1 => pE7C16 f
  | 5, 2 => pE7C17 f
  | 5, 3 => pE7C16 (val7C4 e)
  | 5, 4 => pE7C18 f
  | 5, 5 => pE7C16 (val7C3 d)
  | 5, 6 => pE7C19 f
  | 6, 0 => pE7C20 (val7C2 c)
  | 6, 1 => pE7C20 f
  | 6, 2 => pE7C21 f
  | 6, 3 => pE7C22 f
  | 6, 4 => pE7C20 (val7C4 e)
  | 6, 5 => pE7C23 f
  | 6, 6 => pE7C20 (val7C3 d)

theorem tab7C_eq_transport (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) :
    tab7C a b c d e f = Magma.transport permE7C tr7C (dec7C a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `100` magmas on `Fin 7` whose endomorphism monoid is exactly this one, listed under one
index. Of the `567` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def memRow7C0 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 0 0 0 1 4
  | 1 => tab7C 0 0 0 0 1 6
  | 2 => tab7C 0 0 0 0 2 4
  | 3 => tab7C 0 0 0 0 2 6
  | 4 => tab7C 0 0 0 2 0 4
  | 5 => tab7C 0 0 0 2 0 6
  | 6 => tab7C 0 0 0 2 1 4
  | 7 => tab7C 0 0 0 2 1 6
  | 8 => tab7C 0 0 0 2 2 4
  | _ => tab7C 0 0 0 2 2 6
def memRow7C1 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 0 1 0 1 4
  | 1 => tab7C 0 0 1 0 1 6
  | 2 => tab7C 0 0 1 0 2 4
  | 3 => tab7C 0 0 1 0 2 6
  | 4 => tab7C 0 0 1 2 0 4
  | 5 => tab7C 0 0 1 2 0 6
  | 6 => tab7C 0 0 1 2 1 4
  | 7 => tab7C 0 0 1 2 1 6
  | 8 => tab7C 0 0 1 2 2 4
  | _ => tab7C 0 0 1 2 2 6
def memRow7C2 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 0 2 0 0 4
  | 1 => tab7C 0 0 2 0 0 6
  | 2 => tab7C 0 0 2 0 1 4
  | 3 => tab7C 0 0 2 0 1 6
  | 4 => tab7C 0 0 2 0 2 4
  | 5 => tab7C 0 0 2 0 2 6
  | 6 => tab7C 0 0 2 2 0 4
  | 7 => tab7C 0 0 2 2 0 6
  | 8 => tab7C 0 0 2 2 1 4
  | _ => tab7C 0 0 2 2 1 6
def memRow7C3 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 0 2 2 2 4
  | 1 => tab7C 0 0 2 2 2 6
  | 2 => tab7C 0 1 0 0 1 4
  | 3 => tab7C 0 1 0 0 1 6
  | 4 => tab7C 0 1 0 0 2 4
  | 5 => tab7C 0 1 0 0 2 6
  | 6 => tab7C 0 1 0 2 0 4
  | 7 => tab7C 0 1 0 2 0 6
  | 8 => tab7C 0 1 0 2 1 4
  | _ => tab7C 0 1 0 2 1 6
def memRow7C4 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 1 0 2 2 4
  | 1 => tab7C 0 1 0 2 2 6
  | 2 => tab7C 0 1 1 0 1 4
  | 3 => tab7C 0 1 1 0 1 6
  | 4 => tab7C 0 1 1 0 2 4
  | 5 => tab7C 0 1 1 0 2 6
  | 6 => tab7C 0 1 1 2 0 4
  | 7 => tab7C 0 1 1 2 0 6
  | 8 => tab7C 0 1 1 2 1 4
  | _ => tab7C 0 1 1 2 1 6
def memRow7C5 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 1 1 2 2 4
  | 1 => tab7C 0 1 1 2 2 6
  | 2 => tab7C 0 1 2 0 0 4
  | 3 => tab7C 0 1 2 0 0 6
  | 4 => tab7C 0 1 2 0 1 4
  | 5 => tab7C 0 1 2 0 1 6
  | 6 => tab7C 0 1 2 0 2 4
  | 7 => tab7C 0 1 2 0 2 6
  | 8 => tab7C 0 1 2 2 0 4
  | _ => tab7C 0 1 2 2 0 6
def memRow7C6 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 1 2 2 1 4
  | 1 => tab7C 0 1 2 2 1 6
  | 2 => tab7C 0 1 2 2 2 4
  | 3 => tab7C 0 1 2 2 2 6
  | 4 => tab7C 0 2 0 0 0 4
  | 5 => tab7C 0 2 0 0 0 6
  | 6 => tab7C 0 2 0 0 1 4
  | 7 => tab7C 0 2 0 0 1 6
  | 8 => tab7C 0 2 0 0 2 4
  | _ => tab7C 0 2 0 0 2 6
def memRow7C7 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 2 0 2 0 4
  | 1 => tab7C 0 2 0 2 0 6
  | 2 => tab7C 0 2 0 2 1 4
  | 3 => tab7C 0 2 0 2 1 6
  | 4 => tab7C 0 2 0 2 2 4
  | 5 => tab7C 0 2 0 2 2 6
  | 6 => tab7C 0 2 1 0 0 4
  | 7 => tab7C 0 2 1 0 0 6
  | 8 => tab7C 0 2 1 0 1 4
  | _ => tab7C 0 2 1 0 1 6
def memRow7C8 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 2 1 0 2 4
  | 1 => tab7C 0 2 1 0 2 6
  | 2 => tab7C 0 2 1 2 0 4
  | 3 => tab7C 0 2 1 2 0 6
  | 4 => tab7C 0 2 1 2 1 4
  | 5 => tab7C 0 2 1 2 1 6
  | 6 => tab7C 0 2 1 2 2 4
  | 7 => tab7C 0 2 1 2 2 6
  | 8 => tab7C 0 2 2 0 0 4
  | _ => tab7C 0 2 2 0 0 6
def memRow7C9 : Fin 10 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7C 0 2 2 0 1 4
  | 1 => tab7C 0 2 2 0 1 6
  | 2 => tab7C 0 2 2 0 2 4
  | 3 => tab7C 0 2 2 0 2 6
  | 4 => tab7C 0 2 2 2 0 4
  | 5 => tab7C 0 2 2 2 0 6
  | 6 => tab7C 0 2 2 2 1 4
  | 7 => tab7C 0 2 2 2 1 6
  | 8 => tab7C 0 2 2 2 2 4
  | _ => tab7C 0 2 2 2 2 6
def mem7C (i : Fin 100) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 10 : Nat) with
  | 0 => memRow7C0 ⟨i.1 % 10, by omega⟩
  | 1 => memRow7C1 ⟨i.1 % 10, by omega⟩
  | 2 => memRow7C2 ⟨i.1 % 10, by omega⟩
  | 3 => memRow7C3 ⟨i.1 % 10, by omega⟩
  | 4 => memRow7C4 ⟨i.1 % 10, by omega⟩
  | 5 => memRow7C5 ⟨i.1 % 10, by omega⟩
  | 6 => memRow7C6 ⟨i.1 % 10, by omega⟩
  | 7 => memRow7C7 ⟨i.1 % 10, by omega⟩
  | 8 => memRow7C8 ⟨i.1 % 10, by omega⟩
  | _ => memRow7C9 ⟨i.1 % 10, by omega⟩

/-- Which of the `100` members a given invariant tuple is, so that `mem_of_isExact7C` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr7C : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0, 6, 0, 7, 0, 0, 0, 0, 8, 0, 9, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 11, 0, 0, 0, 0, 12, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 15, 0, 0, 0, 0, 16, 0, 17, 0, 0, 0, 0, 18,
  0, 19, 0, 0, 0, 0, 20, 0, 21, 0, 0, 0, 0, 22, 0, 23, 0, 0, 0, 0, 24, 0, 25, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 27, 0, 0, 0, 0, 28, 0, 29, 0,
  0, 0, 0, 30, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 33, 0, 0, 0, 0, 34, 0, 35, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 37, 0, 0, 0, 0, 38, 0,
  39, 0, 0, 0, 0, 40, 0, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 43, 0, 0, 0, 0, 44, 0, 45,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 47, 0, 0, 0,
  0, 48, 0, 49, 0, 0, 0, 0, 50, 0, 51, 0, 0, 0, 0, 52, 0, 53, 0, 0, 0, 0, 54, 0, 55, 0, 0, 0, 0,
  56, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0,
  59, 0, 0, 0, 0, 60, 0, 61, 0, 0, 0, 0, 62, 0, 63, 0, 0, 0, 0, 64, 0, 65, 0, 0, 0, 0, 66, 0, 67,
  0, 0, 0, 0, 68, 0, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 70, 0, 71, 0, 0, 0, 0, 72, 0, 73, 0, 0, 0, 0, 74, 0, 75, 0, 0, 0, 0, 76, 0, 77, 0, 0, 0, 0,
  78, 0, 79, 0, 0, 0, 0, 80, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 82, 0, 83, 0, 0, 0, 0, 84, 0, 85, 0, 0, 0, 0, 86, 0, 87, 0, 0, 0, 0, 88, 0, 89,
  0, 0, 0, 0, 90, 0, 91, 0, 0, 0, 0, 92, 0, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 0, 95, 0, 0, 0, 0, 96, 0, 97, 0, 0, 0, 0, 98, 0, 99]

/-- The arguments as one mixed-radix index, which is how `rankArr7C` is addressed. -/
def encT7C (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Nat :=
  a.1 * 567 +
    b.1 * 189 +
    c.1 * 63 +
    d.1 * 21 +
    e.1 * 7 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank7C (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Fin 100 :=
  ⟨min (rankArr7C.getD (encT7C a b c d e f) 0) 99, by omega⟩


/-- `0` of the `25` demanded maps and `4` of the `823518` forbidden ones, enough to separate the
`100` members from the other `467` invariant tuples between them. The certificate demands all `25`
-- the group has to be among them -- but forbids only these: `mem_rank7C` scans them once per tuple
with a scan quadratic in their length, and nothing else reads the forbidden side. -/
def e0idx7C (j : Fin 0) : Fin 25 := j.elim0
def x0idx7C : Fin 4 → Fin 823518
  | 0 => 137256
  | 1 => 171723
  | 2 => 171835
  | 3 => 174824

def endE07C (j : Fin 0) : Fin 7 → Fin 7 := endE7C (e0idx7C j)

def endX07C (j : Fin 4) : Fin 7 → Fin 7 := endX7C (x0idx7C j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end7C (i : Fin 100) : Magma (Fin 7) := Magma.mk (mem7C i)

theorem end7C_isEndo (i : Fin 100) (j : Fin 25) : (end7C i).IsEndo (endE7C j) := by
  revert i j; native_decide

theorem end7C_not_isEndo (i : Fin 100) (j : Fin 4) : ¬ (end7C i).IsEndo (endX07C j) := by
  revert i j; native_decide

/-- `rank7C` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem7C` for the index would be a comparison per tuple and
member. -/
theorem mem_rank7C (a : Fin 1) (b c d e : Fin 3) (f : Fin 7)
    (hx : Magma.isExact (tab7C a b c d e f) endE07C endX07C = true) :
    mem7C (rank7C a b c d e f) = tab7C a b c d e f := by
  revert hx; revert a b c d e f; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `100` listed
members. -/
theorem mem_of_isExact7C (a : Fin 1) (b c d e : Fin 3) (f : Fin 7)
    (hx : Magma.isExact (tab7C a b c d e f) endE07C endX07C = true) :
    ∃ idx, mem7C idx = tab7C a b c d e f :=
  ⟨_, mem_rank7C a b c d e f hx⟩

/-- A magma on `Fin 7` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end7C`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact7C` turns that into a member index. -/
theorem exists_end7C {M : Magma (Fin 7)} (hE : ∀ j, M.IsEndo (endE7C j))
    (hX : ∀ j, ¬ M.IsEndo (endX07C j)) : ∃ i, end7C i = M := by
  have hP : ∀ i, M.IsEndo (permE7C i) := by
    intro i; rw [permE7C_eq_endE7C]; exact hE (uidx7C i)
  have hop : M.op = Magma.transport permE7C tr7C (fun i ↦ M.op (rep7C i).1 (rep7C i).2) :=
    Magma.op_eq_transport (rep := rep7C) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE7C) (idx := stabIdx7C0) (a := (rep7C 0).1) (b := (rep7C 0).2)
    (val := val7C0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE7C) (idx := stabIdx7C1) (a := (rep7C 1).1) (b := (rep7C 1).2)
    (val := val7C1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE7C) (idx := stabIdx7C2) (a := (rep7C 2).1) (b := (rep7C 2).2)
    (val := val7C2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE7C) (idx := stabIdx7C3) (a := (rep7C 3).1) (b := (rep7C 3).2)
    (val := val7C3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE7C) (idx := stabIdx7C4) (a := (rep7C 4).1) (b := (rep7C 4).2)
    (val := val7C4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE7C) (idx := stabIdx7C5) (a := (rep7C 5).1) (b := (rep7C 5).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec7C a b c d e f = fun i ↦ M.op (rep7C i).1 (rep7C i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tab7C a b c d e f = M.op := by
    rw [tab7C_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab7C a b c d e f) endE07C endX07C = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx7C j), hX⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact7C a b c d e f hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose endomorphism
monoid is exactly the order-`25` monoid of `Magma.endE7C`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end7C {L L' : Law.NatMagmaLaw} {i : Fin 100}
    (hsrc : @satisfies _ (Fin 7) (Magma.end7C i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.end7C j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end7C i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end7C
    (fun k ↦ (Magma.end7C_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end7C_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
