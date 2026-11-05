"""Read kernel-checked type conversions exported by parastrophe_result.

No mathematics is inferred here from field names or catalogue descriptions.
The Lean exporter audits each generated theorem before writing these records.
"""
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def load(path=None):
    path = Path(path or os.environ.get('WEBSITE_PARASTROPHES') or
                ROOT / 'home_page/research/data/parastrophes.json')
    data = json.loads(path.read_text())
    if data.get('version') != 2 or 'consequences' not in data or 'consequenceSources' not in data:
        raise ValueError('Regenerate the Lean parastrophe export (scripts/export_parastrophes.lean) '
                         'before generating relation data: ' + str(path))
    refs = {r['name']: r for r in data['consequenceSources']}
    for c in data['consequences']:
        if c['kind'] not in ('structural', 'termStructural', 'fineSpectrum'):
            raise ValueError('Unknown parastrophe consequence kind')
        if c['scope'] not in ('all', 'fin') or c['side'] not in ('left', 'right'):
            raise ValueError('Invalid parastrophe consequence scope/side')
        if not all(type(c[k]) is int and 1 <= c[k] <= 4694 for k in ('source', 'target')):
            raise ValueError('Parastrophe consequence outside catalogue')
        if not c['refs'] or any(r not in refs or refs[r]['status'] != 'PROVED' for r in c['refs']):
            raise ValueError('Missing or unproved parastrophe consequence evidence')
    return data


def arrows(data):
    """Native arrows only; existing graph code handles weakening and transitivity."""
    return [c for c in data['consequences'] if c['kind'] != 'fineSpectrum']
