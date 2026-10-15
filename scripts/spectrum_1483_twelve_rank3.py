#!/usr/bin/env python3
"""Audit E1483/order12 rank-three data against the authoritative Lean CNFs.

Run after building RankThree.Encoding. This exports all nine formulas, compares
their hashes with the recorded formulas, and checks both compressed and decoded
payload hashes. The proof itself is checked by `lake build ...RankThree`.

The exported DIMACS files also reproduce the search inputs: CaDiCaL --seed=1
--lrat input.cnf output.lrat. Compact conversion and optional backward trimming
are documented in scripts/spectrum_retrim_certificate.py.
"""
import argparse
import hashlib
import json
import lzma
from pathlib import Path
import subprocess


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=Path('.cache/e1483-rank3-audit'))
    parser.add_argument('--no-export', action='store_true', help='reuse existing Lean exports')
    args = parser.parse_args()
    if not args.no_export:
        subprocess.run([
            'lake', 'env', 'lean', '--run',
            'equational_theories/Spectrum/Equation1483/OrderTwelve/RankThree/Export.lean',
            str(args.work_dir)], check=True)
    manifest = json.loads(Path('data/spectrum/1483_order12_rank3.json').read_text())
    total = 0
    for record in manifest['cases']:
        name = record['tag']
        cnf = (args.work_dir / (name + '.cnf')).read_bytes()
        packed = Path(record['certificate']).read_bytes()
        raw = lzma.decompress(packed)
        assert digest(cnf) == record['cnf_sha256'], (name, 'CNF')
        assert digest(packed) == record['compressed_sha256'], (name, 'compressed payload')
        assert digest(raw) == record['proof_sha256'], (name, 'decoded payload')
        assert len(packed) == record['compressed_bytes'], name
        assert len(raw) == record['proof_bytes'], name
        total += len(packed)
        print(name, 'verified', len(packed), 'bytes')
    assert total == manifest['total_compressed_bytes']
    print('All formulas and payloads match:', total, 'compressed bytes.')


if __name__ == '__main__':
    main()
