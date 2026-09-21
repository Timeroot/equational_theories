#!/usr/bin/env python3
"""Reproduce the finite E3342/E3545 root obstruction certificate.

Run from the repository root. By default compare with the saved artifacts;
--write regenerates them. The generated Lean facts use ordinary decide.
"""

import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--write", action="store_true")
args = parser.parse_args()


# Three successor fibers, each carrying the additive group Z/3Z.
def multiply(x, y):
    i, u = divmod(x, 3)
    j, v = divmod(y, 3)
    if i == j:
        return 3 * ((i + 1) % 3)
    if j == (i + 1) % 3:
        return 3 * i + (u - v + 1) % 3
    assert i == (j + 1) % 3
    return 3 * j + (v - u) % 3


m = [[multiply(x, y) for y in range(9)] for x in range(9)]
U = [tuple(range(9))]
seen_unary = set(U)
k = 0
while k < len(U):
    for j in range(k + 1):
        for a, b in [(U[k], U[j]), (U[j], U[k])]:
            t = tuple(m[x][y] for x, y in zip(a, b))
            if t not in seen_unary:
                seen_unary.add(t)
                U.append(t)
    k += 1
assert len(U) == 27
index = {u: i for i, u in enumerate(U)}
small = [[0, 0, 1], [0, 0, 1], [1, 1, 2]]
C = [
    tuple(x for x in range(3) for y in range(3)),
    tuple(y for x in range(3) for y in range(3)),
]
seen = set(C)
k = 0
while k < len(C):
    for j in range(k + 1):
        t = tuple(small[x][y] for x, y in zip(C[k], C[j]))
        if t not in seen:
            seen.add(t)
            C.append(t)
    k += 1
ci = {v: i for i, v in enumerate(C)}
comp = [[ci[tuple(small[x][y] for x, y in zip(a, b))] for b in C] for a in C]
umul = [[index[tuple(m[x][y] for x, y in zip(a, b))] for b in U] for a in U]


def law(t):
    return all(t[x][y] == t[y][t[t[x][x]][x]] for x in range(9) for y in range(9))


missing = []
hits = []
for flip in [False, True]:
    plane = []
    for i, u in enumerate(U):
        row = []
        for j, v in enumerate(U):
            t = [
                [m[u[y if flip else x]][v[x if flip else y]] for y in range(9)]
                for x in range(9)
            ]
            absent = sorted(set(range(9)) - {z for r in t for z in r})
            if law(t):
                assert len(absent) == 3
                row.append(absent[0])
                hits.append([flip, i, j, absent])
            else:
                row.append(0)
        plane.append(row)
    missing.append(plane)
pa = []
pb = []
for z in range(9):
    a, b = next(
        (a, b) for a in range(9) for b in range(9) if a != z and b != z and m[a][b] == z
    )
    pa.append(a)
    pb.append(b)


def vec(xs):
    return (
        "!["
        + ", ".join(vec(x) if isinstance(x, (list, tuple)) else str(x) for x in xs)
        + "]"
    )


s = """import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-! Finite data for the 27-element E3342/E3545 term-structural obstruction.
All checks below use ordinary `decide`, with no native-computation axiom. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace CubeRoot
"""
s += (
    "@[implicit_reducible] def gate : Magma (Fin 3) where\n  op := " + vec(small) + "\n"
)
s += (
    "def gateOps : Fin 8 → Fin 3 → Fin 3 → Fin 3 :=\n  "
    + vec([[list(v[3 * i : 3 * i + 3]) for i in range(3)] for v in C])
    + "\n"
)
s += "def gateComp : Fin 8 → Fin 8 → Fin 8 :=\n  " + vec(comp) + "\n"
s += """def pureX (i : Fin 8) : Prop := i = 0 ∨ i = 2
def pureY (i : Fin 8) : Prop := i = 1 ∨ i = 4
instance (i : Fin 8) : Decidable (pureX i) := inferInstanceAs (Decidable (i = 0 ∨ i = 2))
instance (i : Fin 8) : Decidable (pureY i) := inferInstanceAs (Decidable (i = 1 ∨ i = 4))
def relation (x y : Fin 3) : Prop := x ≠ y ∨ x = 0
instance (x y : Fin 3) : Decidable (relation x y) := inferInstanceAs (Decidable (x ≠ y ∨ x = 0))
theorem gate_law : @Equation3342 (Fin 3) gate := by decide
theorem gate_main : ∀ x y, gateOps 3 x y = gate.op x y := by decide
theorem gate_fst : ∀ x y, gateOps 0 x y = x := by decide
theorem gate_snd : ∀ x y, gateOps 1 x y = y := by decide
theorem gate_comp : ∀ i j x y, gateOps (gateComp i j) x y = gate.op (gateOps i x y) (gateOps j x y) := by decide
theorem comp_pureX : ∀ i j, pureX (gateComp i j) → pureX i ∧ pureX j := by decide
theorem comp_pureY : ∀ i j, pureY (gateComp i j) → pureY i ∧ pureY j := by decide
theorem comp_main : ∀ i j, gateComp i j = 3 →
    (pureX i ∧ pureY j) ∨ (pureY i ∧ pureX j) := by decide
theorem other_preserves : ∀ i, i ≠ 3 → ∀ a b c d,
    relation a b → relation c d → relation (gateOps i a c) (gateOps i b d) := by decide
"""
s += "@[implicit_reducible] def fiber : Magma (Fin 9) where\n  op := " + vec(m) + "\n"
s += "def unary : Fin 27 → Fin 9 → Fin 9 :=\n  " + vec(U) + "\n"
s += "def unaryComp : Fin 27 → Fin 27 → Fin 27 :=\n  " + vec(umul) + "\n"
s += """theorem fiber_law : @Equation3342 (Fin 9) fiber := by decide
theorem unary_id : ∀ x, unary 0 x = x := by decide
theorem unary_comp : ∀ i j x, unary (unaryComp i j) x = fiber.op (unary i x) (unary j x) := by decide
@[implicit_reducible] def separated (flip : Bool) (i j : Fin 27) : Magma (Fin 9) where
  op x y := if flip then fiber.op (unary i y) (unary j x) else fiber.op (unary i x) (unary j y)
"""
s += (
    "def missing : Bool → Fin 27 → Fin 27 → Fin 9 :=\n  fun flip => if flip then "
    + vec(missing[1])
    + " else "
    + vec(missing[0])
    + "\n"
)
s += """theorem separated_missing : ∀ flip i j,
    @Equation3545 (Fin 9) (separated flip i j) →
    ∀ x y, (separated flip i j).op x y ≠ missing flip i j := by decide
"""
s += (
    "def preLeft : Fin 9 → Fin 9 := "
    + vec(pa)
    + "\ndef preRight : Fin 9 → Fin 9 := "
    + vec(pb)
    + "\n"
)
s += """theorem preimage : ∀ c, fiber.op (preLeft c) (preRight c) = c ∧ preLeft c ≠ c ∧ preRight c ≠ c := by decide
end CubeRoot
"""
data = {
    "gate": small,
    "gate_ops": C,
    "gate_comp": comp,
    "fiber": m,
    "unary": U,
    "unary_comp": umul,
    "missing": missing,
    "target_hits": hits,
    "pre_left": pa,
    "pre_right": pb,
}
assert len(C) == 8 and len(hits) == 54
compatible_tables = {
    tuple(
        m[U[i][y if flip else x]][U[j][x if flip else y]]
        for x in range(9)
        for y in range(9)
    )
    for flip, i, j, _ in hits
}
assert len(compatible_tables) == 6


def source_law(t):
    return all(
        t[x][y] == t[y][t[x][t[x][x]]] for x in range(len(t)) for y in range(len(t))
    )


assert source_law(small) and source_law(m)
# Check every auxiliary relation/shape assertion independently of Lean.
pure_x, pure_y = {0, 2}, {1, 4}
relation = lambda a, b: a != b or a == 0
for i in range(8):
    for j in range(8):
        c = comp[i][j]
        assert c not in pure_x or (i in pure_x and j in pure_x)
        assert c not in pure_y or (i in pure_y and j in pure_y)
        assert c != 3 or (
            (i in pure_x and j in pure_y) or (i in pure_y and j in pure_x)
        )
    if i != 3:
        for a in range(3):
            for b in range(3):
                for c in range(3):
                    for d in range(3):
                        assert not (relation(a, b) and relation(c, d)) or relation(
                            C[i][3 * a + c], C[i][3 * b + d]
                        )
assert not relation(small[0][2], small[2][0])
outputs = {
    Path("equational_theories/Definability/Generated/Cube3342RootData.lean"): s,
    Path("data/definability_cube_root_obstruction.json"): json.dumps(data, indent=2)
    + "\n",
}
for path, content in outputs.items():
    if args.write:
        path.write_text(content)
    else:
        assert path.read_text() == content, f"Stale certificate: {path}"
print(
    f"{'Wrote' if args.write else 'Verified'} root obstruction: "
    "8 gate operations, 27 unary operations, 54 compatible parametrizations (6 distinct operations)."
)
