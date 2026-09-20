#!/usr/bin/env python3
"""Reproduce the five free-orbit permutations used by the E1485 search.

These checks establish permutation data and relation preservation, not the
lexicographic normalization or the model-to-CNF translation.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / 'data/definability_weak_central_recovery_search.json').read_text())
orbits = [[1, 2, 4, 8, 16], [3, 6, 12, 24, 17], [7, 14, 28, 25, 19]]
small = sorted(set(range(32)) - set(sum(orbits, [])))
perms = []
for orbit in orbits:
    p = list(range(32))
    for i, x in enumerate(orbit):
        p[x] = orbit[(i + 1) % 5]
    perms.append(p)
for i, j in [(0, 1), (1, 2)]:
    p = list(range(32))
    for x, y in zip(orbits[i], orbits[j]):
        p[x], p[y] = y, x
    perms.append(p)
inverses = [[p.index(x) for x in range(32)] for p in perms]
for p in perms:
    assert all(p[x] == x for x in small)
    for relation in data['relations']:
        assert {32*p[x//32] + p[x%32] for x in relation} == set(relation)

def vec(xs):
    return '![' + ', '.join(vec(x) if isinstance(x, list) else str(x) for x in xs) + ']'

def cases(tables):
    return '\n'.join(f'  | {i}, {x} => {y}'
                     for i, p in enumerate(tables) for x, y in enumerate(p) if x != y)

source = f'''import equational_theories.Definability.WeakCentralRelations

/-! The five generators of the free-orbit symmetry group fix the seventeen
small points, commute with rotation, and preserve each compatible relation.
This is not a proof of lexicographic normalization or of a SAT exclusion. -/

namespace Magma.WeakCentralSymmetries
open Magma.WeakCentralSource Magma.WeakCentralRelations
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def small : Fin 17 → Fin 32 := {vec(small)}
def forward (i : Fin 5) (x : Fin 32) : Fin 32 :=
  match i.val, x.val with
{cases(perms)}
  | _, _ => x
def backward (i : Fin 5) (x : Fin 32) : Fin 32 :=
  match i.val, x.val with
{cases(inverses)}
  | _, _ => x

theorem inverse : ∀ i x,
    backward i (forward i x) = x ∧ forward i (backward i x) = x := by decide

def perm (i : Fin 5) : Equiv.Perm (Fin 32) where
  toFun := forward i
  invFun := backward i
  left_inv x := (inverse i x).1
  right_inv x := (inverse i x).2

theorem fixes_small : ∀ i j, perm i (small j) = small j := by decide

theorem commutes_rotation : ∀ i x,
    perm i (rotation x) = rotation (perm i x) := by decide

theorem relation_images : ∀ i j, ∀ a ∈ pairs j,
    (perm i a.1, perm i a.2) ∈ pairs j ∧
    ((perm i).symm a.1, (perm i).symm a.2) ∈ pairs j := by native_decide

def relabel {{G : Type}} (f : G → G → G) (p : Equiv.Perm G) : G → G → G :=
  fun x y => p (f (p.symm x) (p.symm y))

theorem relabel_preserves {{G : Type}} (f : G → G → G) (p : Equiv.Perm G)
    (r : List (G × G)) (hr : Preserves f r)
    (hp : ∀ a ∈ r, (p a.1, p a.2) ∈ r ∧ (p.symm a.1, p.symm a.2) ∈ r) :
    Preserves (relabel f p) r := by
  intro a ha b hb
  exact (hp _ (hr _ (hp a ha).2 _ (hp b hb).2)).1

theorem relabel_relations (f : Fin 32 → Fin 32 → Fin 32)
    (hf : ∀ j, Preserves f (pairs j)) (i : Fin 5) :
    ∀ j, Preserves (relabel f (perm i)) (pairs j) :=
  fun j => relabel_preserves f (perm i) (pairs j) (hf j) (relation_images i j)

#print axioms Magma.WeakCentralSymmetries.inverse
#print axioms Magma.WeakCentralSymmetries.fixes_small
#print axioms Magma.WeakCentralSymmetries.commutes_rotation
#print axioms Magma.WeakCentralSymmetries.relation_images
#print axioms Magma.WeakCentralSymmetries.relabel_preserves
#print axioms Magma.WeakCentralSymmetries.relabel_relations
end Magma.WeakCentralSymmetries
'''
config = json.loads((ROOT / 'data/definability_weak_central_foundations.json').read_text())
for name, axiom in config.get('symmetries', {}).get('axioms', {}).items():
    line = '#print axioms ' + name + '\n'
    assert source.count(line) == 1
    source = source.replace(line, '/-- info: ' + axiom + ' -/\n#guard_msgs (whitespace := lax) in\n' + line)
output = ROOT / 'equational_theories/Definability/WeakCentralSymmetries.lean'
if '--write' in sys.argv:
    output.write_text(source)
else:
    assert output.read_text() == source, 'Regenerate with --write'
print('WeakCentralSymmetries: permutation checks and exact source passed')
