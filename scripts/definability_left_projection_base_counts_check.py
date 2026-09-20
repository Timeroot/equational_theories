#!/usr/bin/env python3
"""Check left-projection families with automorphisms on a finite group factor."""
import argparse
import itertools
import json
from pathlib import Path

import numpy as np

from definability_counting_upgrades_check import model_indices
from definability_left_projection_counts_check import render as left_render
from definability_orbit_certificates_check import matrix
from definability_projection_base_counts_check import render as base_render
from definability_projection_kernel_counts_check import kernel_chart
from definability_projection_vector_counts_check import chart
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]


def render(d):
    a = len(d['base_table'])
    maps = d['base_maps']
    m = len(maps)
    bc = d['base_chart']
    r = len(bc['representatives'])
    width = len(bc['stabilizers'][0])
    stub = dict(d, base_modulus=a, base_scalars=list(range(m)))
    s = base_render(stub).replace('ProjectionBaseCounting', 'LeftProjectionBaseCounting')
    s = s.replace('ProjectionBaseFamily', 'LeftProjectionBaseFamily')
    s = s.replace('ProjectionKernelFamily', 'LeftProjectionKernelFamily')
    s = s.replace('import Mathlib.Data.ZMod.Basic',
                  'import Mathlib.Data.ZMod.Basic\nimport Mathlib.Algebra.Group.MinimalAxioms')
    header = left_render(d)
    group = header[header.index('def A :='):header.index('abbrev B :=')]
    s = s.replace(f'abbrev A := ZMod {a}\n', group)
    begin, end = s.index('def baseScalarData'), s.index('def gData')
    s = s[:begin] + f'''def baseMapData : Array (Array A) := {matrix(maps)}
def baseMapFunction (i : Fin {m}) (x : A) : A :=
  (baseMapData.getD i.val #[]).getD x.val 0
theorem baseMap_zero : ∀ i, baseMapFunction i 0 = 0 := by native_decide
theorem baseMap_add : ∀ i x y, baseMapFunction i (x + y) = baseMapFunction i x + baseMapFunction i y := by native_decide
def baseMaps (i : Fin {m}) : A →+ A where
  toFun := baseMapFunction i
  map_zero' := baseMap_zero i
  map_add' := baseMap_add i
''' + s[end:]
    begin, end = s.index('theorem g_coverage'), s.index('theorem h_maps')
    s = s[:begin] + f'''def baseChoiceData : Array (Array A) := {matrix(bc['choices'])}
def baseSizes (i : Fin {r}) : ℕ := (baseChoiceData.getD i.val #[]).size
def baseChoices (i : Fin {r}) (q : Fin (baseSizes i)) : A :=
  (baseChoiceData.getD i.val #[]).getD q.val 0
def baseStabilizerData : Array (Array (Fin {m})) := {matrix(bc['stabilizers'])}
def baseStabilizers (i : Fin {r}) (j : Fin {width}) :=
  (baseStabilizerData.getD i.val #[]).getD j.val 0
theorem base_fixed : ∀ i j, baseMaps (baseStabilizers i j) (baseRepresentative i) = baseRepresentative i := by native_decide
theorem base_choices : ∀ i a, (∀ j, baseMaps (baseStabilizers i j) a = a) →
    ∃ q, baseChoices i q = a := by native_decide
theorem base_covered : ∀ p : (i : Fin {r}) → Fin (baseSizes i), ∃ k, ∀ a,
    gvalues k a = baseMaps (baseTransport a).2 (baseChoices (baseTransport a).1 (p (baseTransport a).1)) := by native_decide
theorem g_coverage : ∀ g : A → A, (∀ j a, baseMaps j (g a) = g (baseMaps j a)) → ∃ p, gvalues p = g :=
  Magma.LeftProjectionKernelFamily.function_coverage_of_chart baseMaps gvalues
    baseRepresentative baseTransport baseSizes baseChoices baseStabilizers
    base_transport base_fixed base_choices base_covered
''' + s[end:]
    s = s.replace('IsEndo (fun x => a + x)', 'IsEndo (Equiv.addLeft a)')
    point = s.index('private def law')
    s = s[:point] + '''theorem move_zero : ∀ a : A × B, Equiv.addLeft a 0 = a := by intro a; exact add_zero a

''' + s[point:]
    s = s.replace('ZeroTest (model p)', 'PointTest (0 : A × B) (model p)')
    s = s.replace('zeroTest_iff_satisfies (model p) (translations p) _',
                  'pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _')
    return s


def check(d, return_models=False):
    GA = np.array(d['base_table'])
    a, b = len(GA), d['kernel_modulus']
    n = a * b
    assert n == d['order']
    ids = np.arange(a)
    assert np.array_equal(GA[0], ids) and np.array_equal(GA[:, 0], ids)
    for x, y, z in itertools.product(ids, repeat=3):
        assert GA[GA[x, y], z] == GA[x, GA[y, z]]
    inverse = np.array(d['base_inverse'])
    assert np.all(GA[ids, inverse] == 0) and np.all(GA[inverse, ids] == 0)
    for p in map(np.array, d['base_maps']):
        assert p[0] == 0 and np.array_equal(p[GA], GA[p[:, None], p[None, :]])
    bc = chart(d['base_maps'], zero=False)
    gs = bc.pop('functions')
    assert bc == d['base_chart'] and gs == d['base_functions']
    kc = kernel_chart(b, d['kernel_scalars'])
    fs = kc.pop('functions')
    assert kc == d['unary_chart'] and fs == d['kernel_functions']
    r = len(bc['representatives'])
    size = len(gs) * len(fs) ** r
    assert size == d['family_count']
    codes = np.arange(size)
    g = np.array(gs)[codes % len(gs)]
    divisor = len(gs)
    h = np.empty((size, r), dtype=np.uint16)
    for i in range(r):
        h[:, i] = codes // divisor % len(fs)
        divisor *= len(fs)
    assert divisor == size
    orbit = np.array([i for i, j in bc['transport']])[np.arange(n) % a]
    f = g[:, np.arange(n) % a] + a * np.array(fs)[h[:, orbit], np.arange(n) // a]
    assert len({tuple(row) for row in f}) == size
    G = np.array([[GA[x % a, y % a] + a * ((x // a + y // a) % b)
                   for y in range(n)] for x in range(n)])
    inv = np.array([next(y for y in range(n) if G[x, y] == 0) for x in range(n)])
    difference = G[inv[:, None], np.arange(n)[None, :]]
    T = G[np.arange(n)[None, :, None], f[:, difference]].astype(np.uint16)
    generators = [np.arange(n) % a]
    generators += [np.array(p)[np.arange(n) % a] + a * (np.arange(n) // a) for p in d['base_maps']]
    generators += [np.arange(n) % a + a * (u * (np.arange(n) // a) % b) for u in d['kernel_scalars']]
    for p in generators:
        assert np.array_equal(p[T], T[:, p[:, None], p[None, :]])
    E = load_equations()
    models = {law: model_indices(E, T, law)
              for law in sorted({e[key] for e in d['candidates'] for key in ['source', 'target']})}
    for e in d['candidates']:
        assert len(models[e['source']]) == e['source_count']
        assert len(models[e['target']]) == e['target_count']
    print(d['namespace'], 'complete family', size, 'full-assignment counts',
          {law: len(indices) for law, indices in models.items()}, flush=True)
    if return_models:
        return T[np.unique(np.concatenate(list(models.values())))]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--only')
    args = parser.parse_args()
    for path in sorted((ROOT / 'data').glob('definability_left_projection_base_count*.json')):
        d = json.loads(path.read_text())
        if args.only and args.only not in d['namespace']:
            continue
        check(d)
        target = ROOT / 'equational_theories/Definability/Generated' / (d['namespace'] + '.lean')
        if args.write:
            target.write_text(render(d))
        else:
            assert target.read_text() == render(d)
