#!/usr/bin/env python3
"""Attach publication metadata to the small, typed Lean parastrophe export.

For a local preview: lake build equational_theories.Parastrophes;
lake env lean scripts/export_parastrophes.lean;
python3 scripts/generate_parastrophe_site.py --local.
The default publication path rejects uncommitted evidence.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def generate(source, output, local=False):
    data = json.loads(source.read_text())
    if data.get('version') != 1:
        raise ValueError('Unsupported Lean parastrophe export')
    relevant = ['*.lean']
    changed = subprocess.check_output(['git', 'diff', '--name-only', 'HEAD', '--', *relevant],
                                      cwd=ROOT, text=True).strip()
    untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard',
                                        '--', *relevant], cwd=ROOT, text=True).strip()
    dirty = bool(changed or untracked)
    if dirty and not local:
        raise ValueError('Commit parastrophe evidence before publication, or use --local for a preview.')
    for record in [*data['records'], *data['rules']]:
        path = Path(record['file'])
        if path.is_absolute():
            path = path.relative_to(ROOT)
        if '..' in path.parts or not (ROOT / path).is_file():
            raise ValueError(f'Invalid Lean source: {path}')
        record['file'] = path.as_posix()
        if record['status'] not in ['PROVED', 'PROOF_AVAILABLE']:
            raise ValueError('Unsupported evidence status')
    data.update(repository=os.environ.get('GITHUB_REPOSITORY', 'Timeroot/equational_theories'),
                commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                generated=datetime.datetime.now(datetime.timezone.utc).isoformat(), local=dirty)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, ensure_ascii=False, separators=(',', ':')) + '\n')
    print(f'Wrote {len(data["records"])} parastrophe records to {output}' + (' (local preview)' if dirty else ''))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path('/tmp/website-parastrophes.json'))
    parser.add_argument('--output', type=Path, default=ROOT / 'home_page/research/data/parastrophes.json')
    parser.add_argument('--local', action='store_true')
    args = parser.parse_args()
    generate(args.input, args.output, args.local)
