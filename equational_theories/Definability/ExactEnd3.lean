import equational_theories.Definability.ExactAut
import equational_theories.Definability.StructuralRigid3

/-!
# Machinery for exact-endomorphism families on `Fin 3`

`Definability/ExactAut.lean` refutes a *structural* pair by its automorphism group: a structural
companion `M'` of `M` has `Aut(M') = Aut(M)` on the nose, because a first-order-definable graph is
carried along by any automorphism. For the *term*-structural relation the same argument gives much
more. Every operation of `M'` is a term of `M` and vice versa, and `Term.realize_isEndo` says a
term is respected by every endomorphism, so

> a term-structural pair has `End(M') = End(M)` on the nose.

`Magma.IsEndo.of_termDefinable` is that step. It is a strictly finer invariant than the
automorphism group -- an endomorphism need not be injective -- and on `Fin 3` the difference is
the whole point: the `19,683` operations fall into `6` exact-`Aut` classes but `156` exact-`End`
ones, most of them tiny, and a class with a handful of members refutes almost every law at once.

What a class needs is therefore only:

* the maps of `Fin 3` that must be endomorphisms and the ones that must not. Unlike the
  automorphism case there is nothing to choose here: `End(M)` is a submonoid of the `27` self-maps,
  so demanding all of `E` and forbidding all `27 - |E|` others pins it exactly, and `27` is small
  enough to write down. `Magma.isExact` already takes arbitrary maps rather than permutations.
* the classification, which on this carrier is finite enumeration rather than orbit transport:
  every operation *is* its `9` values, `Magma.tab3` reassembles them, and `19,683` tuples is a
  `native_decide` away from a member index.

`Definability/ExactEnd3<X>.lean` is the generated instance of this for each class that buys open
cells; see `endprune3.py`.
-/

namespace Magma

/-- Reading a magma's nine values off and putting them back gives the same operation, where
`Magma.tab3` of `Definability/StructuralRigid3.lean` is the reassembly. This is the `Fin 3`
stand-in for `Magma.op_eq_transport`: there is no group to be invariant under, so the
classification is the whole table, and the family of *all* magmas on `Fin 3` is nine arguments. -/
theorem op_eq_tab3 (M : Magma (Fin 3)) :
    tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2) = M.op := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl

/-! ### The twenty-seven self-maps of `Fin 3`

`End(M)` is a submonoid of these, so demanding a set `E` of them and forbidding all the others
pins `End(M)` to `E` exactly -- no analogue of the exact-`Aut` search for a small set of subgroup
representatives is needed. Each map is its own three-way match so that a table lookup inside
`Magma.isEndoFin` is one match and not two; `m3_xyz` sends `0, 1, 2` to `x, y, z`. -/

def m3_000 : Fin 3 → Fin 3 | 0 => 0 | 1 => 0 | 2 => 0
def m3_001 : Fin 3 → Fin 3 | 0 => 0 | 1 => 0 | 2 => 1
def m3_002 : Fin 3 → Fin 3 | 0 => 0 | 1 => 0 | 2 => 2
def m3_010 : Fin 3 → Fin 3 | 0 => 0 | 1 => 1 | 2 => 0
def m3_011 : Fin 3 → Fin 3 | 0 => 0 | 1 => 1 | 2 => 1
def m3_012 : Fin 3 → Fin 3 | 0 => 0 | 1 => 1 | 2 => 2
def m3_020 : Fin 3 → Fin 3 | 0 => 0 | 1 => 2 | 2 => 0
def m3_021 : Fin 3 → Fin 3 | 0 => 0 | 1 => 2 | 2 => 1
def m3_022 : Fin 3 → Fin 3 | 0 => 0 | 1 => 2 | 2 => 2
def m3_100 : Fin 3 → Fin 3 | 0 => 1 | 1 => 0 | 2 => 0
def m3_101 : Fin 3 → Fin 3 | 0 => 1 | 1 => 0 | 2 => 1
def m3_102 : Fin 3 → Fin 3 | 0 => 1 | 1 => 0 | 2 => 2
def m3_110 : Fin 3 → Fin 3 | 0 => 1 | 1 => 1 | 2 => 0
def m3_111 : Fin 3 → Fin 3 | 0 => 1 | 1 => 1 | 2 => 1
def m3_112 : Fin 3 → Fin 3 | 0 => 1 | 1 => 1 | 2 => 2
def m3_120 : Fin 3 → Fin 3 | 0 => 1 | 1 => 2 | 2 => 0
def m3_121 : Fin 3 → Fin 3 | 0 => 1 | 1 => 2 | 2 => 1
def m3_122 : Fin 3 → Fin 3 | 0 => 1 | 1 => 2 | 2 => 2
def m3_200 : Fin 3 → Fin 3 | 0 => 2 | 1 => 0 | 2 => 0
def m3_201 : Fin 3 → Fin 3 | 0 => 2 | 1 => 0 | 2 => 1
def m3_202 : Fin 3 → Fin 3 | 0 => 2 | 1 => 0 | 2 => 2
def m3_210 : Fin 3 → Fin 3 | 0 => 2 | 1 => 1 | 2 => 0
def m3_211 : Fin 3 → Fin 3 | 0 => 2 | 1 => 1 | 2 => 1
def m3_212 : Fin 3 → Fin 3 | 0 => 2 | 1 => 1 | 2 => 2
def m3_220 : Fin 3 → Fin 3 | 0 => 2 | 1 => 2 | 2 => 0
def m3_221 : Fin 3 → Fin 3 | 0 => 2 | 1 => 2 | 2 => 1
def m3_222 : Fin 3 → Fin 3 | 0 => 2 | 1 => 2 | 2 => 2

end Magma
