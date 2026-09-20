#!/usr/bin/env python3
"""Reuse a certified target exclusion with another source having its symmetry pattern."""
import argparse
import json
from pathlib import Path

import numpy as np

from definability_counting_upgrades_check import model_indices, preserves
from definability_orbit_certificates_check import matrix
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]


def render(d):
    ns, n = d['namespace'], len(d['source'])
    imports = sorted({e['template_namespace'] for e in d['candidates']})
    s = ''.join(f'import equational_theories.Definability.Generated.{name}\n' for name in imports)
    s += f'''
/-! Reuse complete orbit-family exclusions with an independently checked source. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.{ns}
def sourceData : Array (Array (Fin {n})) := {matrix(d['source'])}
@[implicit_reducible] def source : Magma (Fin {n}) :=
  ⟨fun x y => (sourceData.getD x.val #[]).getD y.val 0⟩
end Magma.{ns}

'''
    for e in d['candidates']:
        a, b, ref = e['source'], e['target'], 'Magma.' + e['template_namespace']
        name = f'Equation{b}_not_structuralFromFin_Equation{a}_{ns[0].lower()+ns[1:]}'
        s += f'''theorem {name} : ¬ Law{b}.StructuralFromFin Law{a} := by
  apply Magma.FiniteSymmetry.not_structuralFromFin Magma.{ns}.source
    {ref}.genPerm {ref}.probePerm {ref}.pattern {ref}.fam {ref}.coverage
  · exact (@Law{a}.models_iff (Fin {n}) Magma.{ns}.source).mpr (by native_decide)
  · native_decide
  · native_decide
  · intro p hp
    exact {ref}.target{b} p ((@Law{b}.models_iff (Fin {n}) ({ref}.fam p)).mp hp)

#print axioms {name}

'''
    for name, axioms in d.get('axioms', {}).items():
        s = s.replace('#print axioms ' + name + '\n', '/-- info: ' + axioms + ' -/\n'
                      '#guard_msgs (whitespace := lax) in\n#print axioms ' + name + '\n')
    return s


def check(d):
    source = np.array(d['source'], dtype=np.uint16)
    E = load_equations()
    for e in d['candidates']:
        template = json.loads((ROOT / e['template_data']).read_text())
        assert template['namespace'] == e['template_namespace']
        assert len(source) == template['order']
        assert any(c['target'] == e['target'] for c in template['candidates'])
        assert len(model_indices(E, source[None], e['source'])) == 1
        assert preserves(source, np.array(template['generators']))
        original = np.array(template['source'], dtype=np.uint16)
        for probe in np.array(template['probes'], dtype=np.uint16):
            assert preserves(source, [probe]) == preserves(original, [probe])
    print(d['namespace'], 'source laws and reused symmetry patterns verified', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    for path in sorted((ROOT / 'data').glob('definability_symmetry_reuse_*.json')):
        d = json.loads(path.read_text())
        check(d)
        target = ROOT / 'equational_theories/Definability/Generated' / (d['namespace'] + '.lean')
        if args.write:
            target.write_text(render(d))
        else:
            assert target.read_text() == render(d)
