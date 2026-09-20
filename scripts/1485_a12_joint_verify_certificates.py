#!/usr/bin/env python3
"""Regenerate six A12 joint-capacity CNFs and replay their archived LRAT proofs."""

import argparse
import hashlib
import json
import lzma
from pathlib import Path
from runpy import run_path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import perf_counter


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / 'data/1485_certificates/a12_joint'
GENERATOR = ROOT / 'scripts/1485_n40_twelve_joint_capacity_cnf.py'
BASE = ROOT / 'scripts/1485_n40_twelve_line_capacity_cnf.py'
HELPER = ROOT / 'scripts/1485_n40_twelve_one_high_cnf.py'


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            result.update(block)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, required=True)
    checker = parser.parse_args().checker.resolve(strict=True)
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    assert digest(GENERATOR) == manifest['generator_sha256']
    assert digest(BASE) == manifest['base_encoder_sha256']
    assert digest(HELPER) == manifest['counter_helper_sha256']
    expected = list(run_path(str(GENERATOR))['cases']())
    actual = [(item['first'], item['second'], item['orbit']) for item in manifest['cases']]
    assert len(expected) == 6 and actual == expected
    started = perf_counter()
    with TemporaryDirectory(prefix='1485-a12-joint-replay-') as temporary:
        work = Path(temporary)
        for item in manifest['cases']:
            first, second, orbit = (item[key] for key in ('first', 'second', 'orbit'))
            name = item['name']
            assert name == f'{first}_{second}_orbit{orbit}'
            compressed = ARCHIVE / f'{name}.lrat.xz'
            assert digest(compressed) == item['xz_sha256']
            assert compressed.stat().st_size == item['xz_bytes']
            cnf, proof = work / 'case.cnf', work / 'case.lrat'
            with lzma.open(compressed, 'rb') as source, proof.open('wb') as target:
                shutil.copyfileobj(source, target)
            assert digest(proof) == item['lrat_sha256']
            assert proof.stat().st_size == item['lrat_bytes']
            subprocess.run([sys.executable, str(GENERATOR), '--first', first,
                            '--second', second, '--orbit', str(orbit), '--output', str(cnf)],
                           check=True, capture_output=True, text=True)
            assert digest(cnf) == item['cnf_sha256']
            checked = subprocess.run([str(checker), str(cnf), str(proof)],
                                     check=True, capture_output=True, text=True)
            assert 'c VERIFIED' in checked.stdout.splitlines(), checked.stdout
            print(f'{name}: hashes match; LRAT VERIFIED', flush=True)
    print(f'All six archived refutations verified in {perf_counter() - started:.3f}s.')


if __name__ == '__main__':
    main()
