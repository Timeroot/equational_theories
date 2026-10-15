#!/usr/bin/env python3
"""Audit or regenerate the compact E63 order-fourteen refutation.

Ordinary Lean builds only replay the bundled data. --solve regenerates 70
bounded row cases, checks their coverage by one final SAT call, and packs the
LRAT proofs as compact RUP while retaining root assumptions. All these external
operations are untrusted: Lean checks the resulting complete refutation.
"""
import argparse
import collections
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
import lzma
from pathlib import Path
import subprocess
import time

from spectrum_63_ten_certificate import clauses as cubic_clauses

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data/spectrum/63_order14_lean.json'
CERTIFICATES = ROOT / 'data/spectrum/63_fourteen_rup'
N = 14

def atom(x, y, z):
    return 1 + (x * N + y) * N + z


def clauses():
    cs = cubic_clauses(N)
    for y in range(N):
        for z in range(y + 1, N):
            cs.append([-atom(0, y, y), -atom(0, z, z)])
    for y in range(N):
        for x in range(N):
            cs.append([-atom(0, y, y)] + [atom(x, z, z) for z in range(N)])
            for z in range(N):
                for w in range(z + 1, N):
                    cs.append([-atom(0, y, y), -atom(x, z, z), -atom(x, w, w)])
    return [c for c in cs if not any(-v in c for v in c)]


def dimacs(cs):
    return (f'p cnf {N**3} {len(cs)}\n' +
            ''.join(' '.join(map(str, c)) + ' 0\n' for c in cs)).encode()


def compositions(n):
    if not n:
        yield []
    for k in range(1, n + 1):
        if k != 2:
            for rest in compositions(n - k):
                yield [k] + rest


def row_cases():
    result = []
    for first in (1, 3):
        for tail in compositions(N - first):
            cycles = [first] + tail
            if cycles.count(1) > 1:
                continue
            row = []
            for k in cycles:
                offset = len(row)
                row.extend(offset + (i + 1) % k for i in range(k))
            result.append({'cycles': cycles, 'row': row})
    return result


def sha(data):
    return hashlib.sha256(data).hexdigest()


def trim_text(path):
    """Keep just the backwards dependency cone of the final empty clause."""
    records = {}
    final = None
    with gzip.open(path, 'rt') as stream:
        for line in stream:
            fields = line.split()
            # CaDiCaL's quiet result line may accompany /dev/stdout proof data.
            if not fields or not fields[0].isdigit() or len(fields) < 3 or fields[1] == 'd':
                continue
            words = list(map(int, fields))
            split = words.index(0)
            idx, clause, hints = words[0], words[1:split], words[split + 1:-1]
            assert all(h > 0 for h in hints), 'RAT steps are unsupported'
            records[idx] = (clause, hints)
            if not clause:
                final = idx
    assert final is not None, f'Incomplete proof: {path}'
    needed, todo = set(), [final]
    while todo:
        idx = todo.pop()
        if idx in needed:
            continue
        needed.add(idx)
        if idx in records:
            todo.extend(records[idx][1])
    return [(idx, *records[idx]) for idx in sorted(needed) if idx in records]


def solve_cases(work, solver, timeout, jobs, base, cases):
    def solve(i):
        case = cases[i]
        cnf = work / f'case{i:02d}.cnf'
        proof = work / f'case{i:02d}.lrat.gz'
        cnf.write_bytes(dimacs(base + [[atom(0, y, z)] for y, z in enumerate(case['row'])]))
        start = time.monotonic()
        with (work / f'case{i:02d}.log').open('wb') as log:
            proc = subprocess.Popen([solver, '-q', '--shrink=0', '--lrat', '--no-binary',
                                     '-t', str(timeout), str(cnf), '/dev/stdout'],
                                    stdout=subprocess.PIPE, stderr=log)
            total = 0
            with gzip.open(proof, 'wb', compresslevel=1) as dest:
                while chunk := proc.stdout.read(1048576):
                    total += len(chunk)
                    if total > 512_000_000:
                        proc.terminate()
                        break
                    dest.write(chunk)
            rc = proc.wait()
        record = {'i': i, **case, 'seconds': round(time.monotonic() - start, 3),
                  'returncode': rc, 'bytes': total, 'gzip_bytes': proof.stat().st_size}
        (work / f'case{i:02d}.json').write_text(json.dumps(record, indent=2) + '\n')
        assert rc == 20, record
        print(f'Case {i:02d}: UNSAT, {record["seconds"]}s', flush=True)
        return record
    with ThreadPoolExecutor(jobs) as pool:
        return list(pool.map(solve, range(len(cases))))


def pack_cases(work, base, cases):
    """Keep assumptions as permanent root units for fast propagation replay."""
    packer = work / 'compact-rup'
    subprocess.run(['c++', '-O3', '-std=c++17', str(ROOT / 'scripts/spectrum_compact_rup.cpp'),
                    '-o', str(packer)], check=True)
    destination = CERTIFICATES
    destination.mkdir(parents=True, exist_ok=True)
    def pack(j):
        name = f'case{j:02d}' if j < len(cases) else 'coverage'
        path = work / f'{name}.lrat.gz' if j < len(cases) else work / 'cover.lrat.gz'
        initial = len(base) + (N if j < len(cases) else len(cases))
        records = trim_text(path)
        renumber = {i: initial + k + 1 for k, (i, _, _) in enumerate(records)}
        records = [(renumber[i], c, [h if h <= initial else renumber[h] for h in hs])
                   for i, c, hs in records]
        last = {}
        for i, _, hints in records:
            for h in hints:
                last[h] = i
        deletions = {}
        for h, i in last.items():
            deletions.setdefault(i, []).append(h)
        buf = bytearray()
        def word(n):
            while n > 127:
                buf.append((n & 127) | 128)
                n >>= 7
            buf.append(n)
        def signed(n):
            word(2 * abs(n) + (n < 0))
        for i, clause, hints in records:
            buf.append(ord('a'))
            signed(i)
            for v in clause:
                signed(v)
            word(0)
            for v in hints:
                signed(v)
            word(0)
            if i != initial + len(records) and i in deletions:
                buf.append(ord('d'))
                for v in deletions[i]:
                    signed(v)
                word(0)
        with (work / f'{name}.compact.log').open('w') as log:
            subprocess.run([str(packer), '--input-mask', str(work / f'{name}.rup')],
                           input=buf, stderr=log, check=True)
        raw = (work / f'{name}.rup').read_bytes()
        compressed = lzma.compress(raw, preset=6)
        target = destination / f'{name}.rup.xz'
        target.write_bytes(compressed)
        print(f'{name}: {len(compressed):,} bytes', flush=True)
        return {'name': name, 'steps': len(records), 'input_clauses': initial,
                'selected_input_clauses': sum(h <= initial for h in last),
                'proof_bytes': len(raw), 'compressed_bytes': len(compressed),
                'proof_sha256': sha(raw), 'compressed_sha256': sha(compressed),
                'certificate': str(target.relative_to(ROOT))}
    with ThreadPoolExecutor(2) as pool:
        return list(pool.map(pack, range(len(cases) + 1)))


def solve_coverage(work, solver, base, cases):
    cover = base + [[-atom(0, y, z) for y, z in enumerate(c['row'])] for c in cases]
    (work / 'cover.cnf').write_bytes(dimacs(cover))
    with (work / 'cover.log').open('w') as log:
        rc = subprocess.run([solver, '-q', '--shrink=0', '--lrat', '--no-binary', '-t', '120',
                             str(work / 'cover.cnf'), str(work / 'cover.lrat')],
                            stdout=log, stderr=log).returncode
    assert rc == 20, 'Row coverage was not refuted'
    with gzip.open(work / 'cover.lrat.gz', 'wb') as stream:
        stream.write((work / 'cover.lrat').read_bytes())


def audit_proof(record):
    compressed = (ROOT / record['certificate']).read_bytes()
    raw = lzma.decompress(compressed)
    assert record['proof_sha256'] == sha(raw) and record['proof_bytes'] == len(raw)
    assert record['compressed_sha256'] == sha(compressed)
    assert record['compressed_bytes'] == len(compressed)
    initial = shift = pos = 0
    while True:
        b = raw[pos]
        pos += 1
        initial |= (b & 127) << shift
        if b < 128:
            break
        shift += 7
    assert initial == 2 * (record['input_clauses'] + 1) and raw[pos] == ord('m')
    mask = raw[pos + 1:pos + 1 + initial // 2]
    assert len(mask) == initial // 2 and mask[0] == 0
    assert all(b in (0, 1) for b in mask)
    assert sum(mask) == record['selected_input_clauses']


def canonical_info(cases, proofs):
    groups = {}
    for i, case in enumerate(cases):
        groups.setdefault((case['cycles'][0], tuple(sorted(case['cycles'][1:]))), []).append(i)
    representatives = [min(group, key=lambda i: proofs[i]['steps']) for group in groups.values()]
    targets = [next(j for j, group in enumerate(groups.values()) if i in group)
               for i in range(len(cases))]
    sigmas, taus = [], []
    for i, case in enumerate(cases):
        ref = cases[representatives[targets[i]]]
        starts = collections.defaultdict(list)
        offset = ref['cycles'][0]
        for length in ref['cycles'][1:]:
            starts[length].append(offset)
            offset += length
        sigma = list(range(case['cycles'][0]))
        for length in case['cycles'][1:]:
            start = starts[length].pop(0)
            sigma.extend(range(start, start + length))
        tau = [0] * N
        for a, b in enumerate(sigma):
            tau[b] = a
        assert all(sigma[case['row'][tau[y]]] == ref['row'][y] for y in range(N))
        sigmas.append(sigma)
        taus.append(tau)
    return {'representatives': representatives, 'target': targets, 'sigma': sigmas, 'tau': taus}


def render_row_data(cases, info):
    def arr(values):
        return '#[' + ', '.join(map(str, values)) + ']'
    text = """import equational_theories.Spectrum.Equation63.OrderFourteen.CaseAssembly

/- Generated by scripts/spectrum_63_fourteen_certificate.py.
Cycle-block permutations connect every ordered row to a checked representative.
CanonicalData verifies all inverse and conjugacy equations in the kernel. -/
namespace Spectrum.E63.OrderFourteen.CanonicalData
abbrev Row := Fin 14 → Fin 14
private def rowData : Array (Array (Fin 14)) := #[
""" + ',\n'.join('  ' + arr(c['row']) for c in cases) + """]
def row (i : Fin 70) : Row := fun j => rowData[i.val]![j.val]!
private def repData : Array (Fin 70) := """ + arr(info['representatives']) + """
def representative (j : Fin 21) : Fin 70 := repData[j.val]!
private def targetData : Array (Fin 21) := """ + arr(info['target']) + """
def target (i : Fin 70) : Fin 21 := targetData[i.val]!
private def sigmaData : Array (Array (Fin 14)) := #[
""" + ',\n'.join('  ' + arr(v) for v in info['sigma']) + """]
private def tauData : Array (Array (Fin 14)) := #[
""" + ',\n'.join('  ' + arr(v) for v in info['tau']) + """]
def sigma (i : Fin 70) (x : Fin 14) : Fin 14 := sigmaData[i.val]![x.val]!
def tau (i : Fin 70) (x : Fin 14) : Fin 14 := tauData[i.val]![x.val]!
end Spectrum.E63.OrderFourteen.CanonicalData
"""
    return text


def render_certificate(info):
    entries = ",\n".join(
        f'  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case{i:02d}.rup.xz"'
        for i in info["representatives"])
    return """import equational_theories.Spectrum.Equation63.OrderFourteen.RowTransfer
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Only 21 cycle types need refutations; CanonicalData proves the relabelings
of all 70 ordered rows. The final small refutation checks row coverage. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E63.OrderFourteen.CanonicalCertificate
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData RowTransfer CanonicalData

private def data : Array ByteArray := #[
""" + entries + """]
private def caseProof (j : Fin 21) : Array IntAction :=
  CompactRup.reconstruct data[j.val]! (rowFormula (row (representative j)))

@[spectrum_native]
theorem checked_cases : (List.finRange 21).all (fun j =>
    check (caseProof j) (rowFormula (row (representative j)))) = true := by native_decide

theorem case_unsat (j : Fin 21) : (rowFormula (row (representative j))).Unsat :=
  check_sound _ _ (List.all_eq_true.mp checked_cases j (List.mem_finRange _))

private def coverageProof : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../data/spectrum/63_fourteen_rup/coverage.rup.xz") coverage

@[spectrum_native]
theorem checked_coverage : check coverageProof coverage = true := by native_decide

theorem coverage_unsat : coverage.Unsat := check_sound _ _ checked_coverage

spectrum_assert case_unsat complete
spectrum_assert coverage_unsat complete
end Spectrum.E63.OrderFourteen.CanonicalCertificate
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--write', action='store_true', help='rewrite generated row data')
    ap.add_argument('--solver', default='cadical')
    ap.add_argument('--timeout', type=int, default=180)
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--work', type=Path, default=ROOT / '.cache/e63-fourteen-reproduce')
    ap.add_argument('--export-cnf', type=Path)
    ap.add_argument('--check-lean-cnf', type=Path)
    args = ap.parse_args()
    base, cases = clauses(), row_cases()
    payload = dimacs(base)
    if args.solve:
        args.work.mkdir(parents=True, exist_ok=True)
        runs = solve_cases(args.work, args.solver, args.timeout, args.jobs, base, cases)
        solve_coverage(args.work, args.solver, base, cases)
        all_proofs = pack_cases(args.work, base, cases)
        info = canonical_info(cases, all_proofs)
        proofs = [all_proofs[i] for i in info['representatives']] + [all_proofs[-1]]
        record = {'law': 63, 'order': N, 'theorem': 'Spectrum.not_order_63_14',
                  'clauses': len(base), 'variables': N**3, 'cases': cases,
                  'steps': sum(p['steps'] for p in proofs),
                  'compressed_bytes': sum(p['compressed_bytes'] for p in proofs),
                  'proof_bytes': sum(p['proof_bytes'] for p in proofs),
                  'cnf_sha256': sha(payload), 'proofs': proofs, 'canonical': info,
                  'solver': subprocess.check_output([args.solver, '--version'], text=True).strip(),
                  'search_seconds': round(sum(r['seconds'] for r in runs), 3)}
        DATA.write_text(json.dumps(record, indent=2) + '\n')
        retained = {p['certificate'] for p in proofs}
        for proof in all_proofs:
            if proof['certificate'] not in retained:
                (ROOT / proof['certificate']).unlink()
    record = json.loads(DATA.read_text())
    assert record['cases'] == cases and record['clauses'] == len(base)
    assert record['cnf_sha256'] == sha(payload)
    proofs = record['proofs']
    reps = record['canonical']['representatives']
    assert len(reps) == 21 and len(proofs) == len(reps) + 1
    for i, proof in enumerate(proofs):
        assert proof['name'] == (f'case{reps[i]:02d}' if i < len(reps) else 'coverage')
        assert proof['input_clauses'] == len(base) + (N if i < len(reps) else len(cases))
        audit_proof(proof)
    assert sum(p['compressed_bytes'] for p in proofs) == record['compressed_bytes']
    row_file = ROOT / 'equational_theories/Spectrum/Equation63/OrderFourteen/RowData.lean'
    row_text = render_row_data(cases, record['canonical'])
    if args.solve or args.write:
        row_file.write_text(row_text)
    else:
        assert row_file.read_text() == row_text, 'Generated row data changed'
    cert_file = row_file.with_name('CanonicalCertificate.lean')
    cert_text = render_certificate(record['canonical'])
    if args.solve or args.write:
        cert_file.write_text(cert_text)
    else:
        assert cert_file.read_text() == cert_text, 'Certificate wrapper changed'
    if args.export_cnf:
        args.export_cnf.write_bytes(payload)
    if args.check_lean_cnf:
        assert args.check_lean_cnf.read_bytes() == payload
    print(f'E63/14: {len(cases)} cases, {record["steps"]:,} checked additions, '
          f'{record["compressed_bytes"]:,} bytes; hashes and CNF checked.')


if __name__ == '__main__':
    main()
