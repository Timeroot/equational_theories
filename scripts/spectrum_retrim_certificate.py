#!/usr/bin/env python3
"""Shrink an existing RUP-only binary LRAT certificate by backward replay.

This is an optional certificate-generation tool, never part of a Lean build.
The resulting compact RUP data still require CompactRup.reconstruct followed by
Lean's verified LRAT.check/check_sound against the original, unchanged CNF.

Requires drat-trim and a compiled scripts/spectrum_compact_rup.cpp. For example:
  python3 scripts/spectrum_retrim_certificate.py --cnf case.cnf \
    --lrat case.lrat.trimmed.bin --work-dir .cache/retrim-case \
    --output case.rup.xz --compact-rup .cache/compact-rup
"""
import argparse
import hashlib
import json
import lzma
from pathlib import Path
import subprocess
import time


def words(data):
    """Binary LRAT words, consumed through a shared byte iterator."""
    value = shift = 0
    for byte in data:
        value |= (byte & 127) << shift
        if byte < 128:
            return value
        shift += 7
        if shift >= 70:
            raise ValueError('oversized binary word')
    raise ValueError('truncated binary word')


def put(out, value):
    if value < 0:
        raise ValueError('negative binary word')
    while value >= 128:
        out.append((value & 127) | 128)
        value >>= 7
    out.append(value)


def input_clauses(path):
    clauses, pending, declared = {}, [], None
    for line in path.read_text().splitlines():
        if not line or line.startswith('c'):
            continue
        if line.startswith('p'):
            fields = line.split()
            if len(fields) != 4 or fields[1] != 'cnf':
                raise ValueError('invalid DIMACS header')
            declared = int(fields[3])
            continue
        for literal in map(int, line.split()):
            if literal:
                pending.append(2 * abs(literal) + (literal < 0))
            else:
                clauses[len(clauses) + 1] = pending
                pending = []
    if pending or declared != len(clauses):
        raise ValueError('DIMACS clause count mismatch')
    return clauses


def to_drat(cnf, proof, output):
    clauses = input_clauses(cnf)
    initial = len(clauses)
    data = iter(proof.read_bytes())
    out, count, empty = bytearray(), 0, False
    for tag in data:
        if tag == ord('a'):
            identifier = words(data)
            if identifier % 2 or identifier // 2 <= initial:
                raise ValueError('invalid addition identifier')
            clause = []
            while (literal := words(data)):
                clause.append(literal)
            while (hint := words(data)):
                if hint % 2:
                    raise ValueError('RAT additions are not supported')
            clauses[identifier // 2] = clause
            out.append(tag)
            for literal in clause:
                put(out, literal)
            put(out, 0)
            count += 1
            empty = not clause
        elif tag == ord('d'):
            while (identifier := words(data)):
                if identifier % 2:
                    raise ValueError('invalid deletion identifier')
                clause = clauses.pop(identifier // 2, None)
                if clause is not None:
                    out.append(tag)
                    for literal in clause:
                        put(out, literal)
                    put(out, 0)
        else:
            raise ValueError('expected binary LRAT addition or deletion')
    if not count or not empty:
        raise ValueError('proof does not finish with an empty clause')
    output.write_bytes(out)
    return initial, count


def renumber(proof, initial, output):
    """Keep input IDs fixed; make learned IDs consecutive for compact RUP.

    drat-trim can omit early learned clauses and emit initial deletions. Lean's
    LRAT trimmer infers the input count from the first addition, so feeding that
    sparse trace directly to it would give the wrong input count. No further
    Lean trimming is needed: drat-trim has already retained its backward core.
    """
    names = {i: i for i in range(1, initial + 1)}
    out, count, empty = bytearray(), 0, False
    with proof.open() as stream:
        for line in stream:
            fields = line.split()
            if not fields:
                continue
            old = int(fields[0])
            if fields[1] == 'd':
                if not count:
                    continue  # The compact input mask prunes these inputs.
                ids = [names[int(x)] for x in fields[2:-1] if int(x) in names]
                if ids:
                    out.append(ord('d'))
                    for identifier in ids:
                        put(out, 2 * identifier)
                    put(out, 0)
            else:
                count += 1
                names[old] = initial + count
                split = fields.index('0')
                out.append(ord('a'))
                put(out, 2 * names[old])
                for literal in map(int, fields[1:split]):
                    put(out, 2 * abs(literal) + (literal < 0))
                put(out, 0)
                for hint in map(int, fields[split + 1:-1]):
                    if hint <= 0:
                        raise ValueError('RAT additions are not supported')
                    put(out, 2 * names[hint])
                put(out, 0)
                empty = split == 1
    if not count or not empty:
        raise ValueError('retrimmed proof does not finish with an empty clause')
    output.write_bytes(out)
    return count


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('cnf', 'lrat', 'work-dir', 'output', 'compact-rup'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--drat-trim', default='drat-trim')
    parser.add_argument('--seconds', type=int, default=120)
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('--seconds must be positive')
    work = args.work_dir
    work.mkdir(parents=True, exist_ok=True)
    drat, lrat = work / 'proof.drat', work / 'proof.lrat'
    binary, rup = work / 'proof.renumbered.bin', work / 'proof.rup'
    initial, before = to_drat(args.cnf, args.lrat, drat)
    start = time.monotonic()
    command = [str(args.drat_trim), str(args.cnf), str(drat), '-L', str(lrat),
               '-t', str(args.seconds), '-w']
    with (work / 'drat-trim.log').open('w') as log:
        subprocess.run(command, stdout=log, stderr=log, check=True,
                       timeout=args.seconds + 30)
    if 's VERIFIED' not in (work / 'drat-trim.log').read_text():
        raise RuntimeError('drat-trim did not finish verification')
    seconds = time.monotonic() - start
    after = renumber(lrat, initial, binary)
    with binary.open('rb') as stream, (work / 'pack.log').open('w') as log:
        subprocess.run([str(args.compact_rup), '--input-mask', str(rup)],
                       stdin=stream, stdout=log, stderr=log, check=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(lzma.compress(rup.read_bytes(), preset=6))
    report = dict(cnf_sha256=digest(args.cnf), input_lrat_sha256=digest(args.lrat),
                  certificate_sha256=digest(args.output), clauses=initial,
                  additions_before=before, additions_after=after,
                  drat_trim_seconds=round(seconds, 3),
                  certificate_bytes=args.output.stat().st_size,
                  lean_check='required separately against the original CNF')
    args.output.with_suffix(args.output.suffix + '.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
