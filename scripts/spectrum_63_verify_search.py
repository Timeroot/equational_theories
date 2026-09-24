#!/usr/bin/env python3
"""Independently check saved DRAT refutations from spectrum_63_exhaustive.py.

Checks the complete case list and regenerates the CNF input before invoking
drat-trim. This validates the finite computation, not its translation to Lean.
"""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

from spectrum_63_exhaustive import (base_cnf, case_cnf, cases, variable,
                                   add_nonidempotent_cycle_filter,
                                   add_positive_fixed_short_cycles,
                                   add_short_cycle_steps)
from spectrum_63_search import partitions


def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def verify_square_involution(certificate, checker, output, seconds=3600,
                             resume=False, artifact_dir=None):
    """Audit the 17 exclusions giving the uniform 3,5,5,5-row consequence.

    The parent permits ANY zero-fixed-point row of this type as 0: its
    minimum fixed count is zero and its minimum commuting count is three,
    both vacuous bounds. The caller must also check the earlier zero-row
    cycle exclusions on which this parent input depends.
    """
    data = json.loads(certificate.read_text())
    assert data['law'] == 63 and data['order'] == 18
    parent = data['parent_case']
    assert parent['cycles'] == [3, 5, 5, 5] and not parent['idempotent']
    assert parent['min_fixed'] and parent['min_commuting']
    assert parent['nonidempotent_cycle_filter']
    for flag in ['idempotent_no_short_cycles', 'fixed_count_consequence',
                 'idempotent_single_cycle', 'zero_three_square_involution']:
        assert not parent.get(flag, False), 'Circular or inapplicable square dependency'
    flags = ['min_fixed', 'min_commuting', 'lex_rows', 'lex_powers',
             'even_columns', 'nonidempotent_cycle_filter',
             'commuting_cycles_mod_three', 'no_even_identity', 'commuting_triangles']
    text = io.StringIO()
    case_cnf(base_cnf(18), 18, parent,
             **{k: parent.get(k, 0 if k == 'lex_rows' else False) for k in flags}).to_fp(text)
    raw = text.getvalue()
    assert hashlib.sha256(raw.encode()).hexdigest() == parent['cnf_sha256']
    entries = data['excluded_diagonal_values']
    assert sorted(c['diagonal_value'] for c in entries) == list(range(1, 18))
    header, body = raw.split('\n', 1)
    parts = header.split()
    parts[-1] = str(int(parts[-1]) + 1)
    checker_hash = sha256(checker)
    previous = {}
    if resume and output.exists():
        old = json.loads(output.read_text())
        if old.get('checker_sha256') == checker_hash:
            previous = {c['diagonal_value']: c for c in old['cases']
                        if c['status'] == 'DRAT_VERIFIED'}
    result = {'order': 18, 'source_certificate': str(certificate),
              'parent_input_regenerated': True, 'all_nonzero_values_covered': True,
              'checker_sha256': checker_hash, 'cases': [], 'status': 'CHECKING'}
    with tempfile.TemporaryDirectory(prefix='e63-square-check-') as directory:
        input_path = Path(directory) / 'input.cnf'
        for c in entries:
            value = c['diagonal_value']
            regenerated = (' '.join(parts) + '\n' + body +
                           f'{variable(18, 1, 1, value)} 0\n').encode()
            assert hashlib.sha256(regenerated).hexdigest() == c['cnf_sha256']
            source, proof = Path(c['cnf']), Path(c['proof'])
            if artifact_dir:
                source = artifact_dir / 'cnf' / source.name
                proof = artifact_dir / 'proof' / proof.name
            assert gzip.decompress(source.read_bytes()) == regenerated
            assert sha256(proof) == c['proof_sha256']
            old = previous.get(value)
            if old and all(old[k] == c[k] for k in ['cnf_sha256', 'proof_sha256']):
                record = old
            else:
                input_path.write_bytes(regenerated)
                started = time.time()
                with subprocess.Popen(['gzip', '-dc', str(proof)], stdout=subprocess.PIPE) as unzip:
                    checked = subprocess.run([str(checker), str(input_path), '-i', '-w'],
                                             stdin=unzip.stdout, stdout=subprocess.PIPE,
                                             stderr=subprocess.STDOUT, timeout=seconds)
                    unzip.stdout.close()
                    assert unzip.wait() == 0, 'Corrupt square-dependency proof'
                assert checked.returncode == 0 and b's VERIFIED' in checked.stdout
                record = {**c, 'status': 'DRAT_VERIFIED', 'input_regenerated': True,
                          'wall_seconds': round(time.time() - started, 3)}
            result['cases'].append(record)
            temp = output.with_name(output.name + f'.{os.getpid()}.tmp')
            temp.write_text(json.dumps(result, indent=2) + '\n')
            temp.replace(output)
    result['status'] = 'ALL_17_DRAT_VERIFIED_NOT_LEAN'
    temp = output.with_name(output.name + f'.{os.getpid()}.tmp')
    temp.write_text(json.dumps(result, indent=2) + '\n')
    temp.replace(output)
    return result


def verify_positive_rows(certificate, checker, output, seconds=3600,
                         resume=False, artifact_dir=None):
    """Check all excluded positive-fixed row types, without a minimum choice."""
    data = json.loads(certificate.read_text())
    assert data['law'] == 63 and data['order'] == 18
    scope = data.get('fixed_point_scope', 'at_least_two')
    assert scope in ['at_least_two', 'exactly_one']
    one_fixed = scope == 'exactly_one'
    expected = [c for c in cases(18) if not c['idempotent'] and
                (c['cycles'].count(1) == 1 if one_fixed else c['cycles'].count(1) >= 2)
                and any(k not in (1, 3, 4) for k in c['cycles'])]
    assert [{k: c[k] for k in ['name', 'idempotent', 'cycles']}
            for c in data['cases']] == expected
    flags = ['min_fixed', 'min_commuting', 'lex_rows', 'lex_powers',
             'even_columns', 'commuting_cycles_mod_three', 'no_even_identity',
             'commuting_triangles']
    base = base_cnf(18)
    checker_hash = sha256(checker)
    previous = {}
    if resume and output.exists():
        old = json.loads(output.read_text())
        if old.get('checker_sha256') == checker_hash:
            previous = {c['name']: c for c in old['cases'] if c['status'] == 'DRAT_VERIFIED'}
    result = {'order': 18, 'source_certificate': str(certificate),
              'fixed_point_scope': scope,
              'complete_excluded_type_list_checked': True,
              'requires_zero_row_exclusions': True,
              'checker_sha256': checker_hash, 'cases': [], 'status': 'CHECKING'}
    for c in data['cases']:
        for flag in ['min_fixed', 'min_commuting', 'idempotent_no_short_cycles',
                     'fixed_count_consequence', 'idempotent_single_cycle',
                     'nonidempotent_cycle_filter', 'zero_three_square_involution',
                     'positive_fixed_short_cycles', 'one_fixed_short_cycles']:
            assert not c.get(flag, False), 'Circular or global row-type restriction'
        assert c.get('uses_square_involution', False) == one_fixed
        assert c.get('uses_positive_row_filter', False) == one_fixed
        cnf = case_cnf(base, 18, c,
                       **{k: c.get(k, 0 if k == 'lex_rows' else False) for k in flags})
        if c.get('zero_row_cycle_filter', False):
            # Apply the already checked zero-row exclusions, with the vacuous
            # commuting bound three, independently of this chosen positive row.
            add_nonidempotent_cycle_filter(cnf, 18, {'cycles': [3, 5, 5, 5]}, one_fixed)
        if one_fixed:
            assert c.get('zero_row_cycle_filter', False)
            add_positive_fixed_short_cycles(cnf, 18)
        text = io.StringIO()
        cnf.to_fp(text)
        assert hashlib.sha256(text.getvalue().encode()).hexdigest() == c['cnf_sha256']
        source, proof = Path(c['cnf']), Path(c['proof'])
        if artifact_dir:
            source = artifact_dir / 'cnf' / source.name
            proof = artifact_dir / 'proof' / proof.name
        assert sha256(source) == c['cnf_sha256']
        assert sha256(proof) == c['proof_sha256']
        old = previous.get(c['name'])
        if old and all(old[k] == c[k] for k in ['cnf_sha256', 'proof_sha256']):
            record = old
        else:
            started = time.time()
            with subprocess.Popen(['gzip', '-dc', str(proof)], stdout=subprocess.PIPE) as unzip:
                checked = subprocess.run([str(checker), str(source), '-i', '-w'],
                                         stdin=unzip.stdout, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, timeout=seconds)
                unzip.stdout.close()
                assert unzip.wait() == 0, 'Corrupt positive-row dependency proof'
            assert checked.returncode == 0 and b's VERIFIED' in checked.stdout
            record = {'name': c['name'], 'cnf_sha256': c['cnf_sha256'],
                      'proof': str(proof), 'proof_sha256': c['proof_sha256'],
                      'status': 'DRAT_VERIFIED', 'input_regenerated': True,
                      'wall_seconds': round(time.time() - started, 3)}
        result['cases'].append(record)
        temp = output.with_name(output.name + f'.{os.getpid()}.tmp')
        temp.write_text(json.dumps(result, indent=2) + '\n')
        temp.replace(output)
    result['status'] = f'ALL_{len(expected)}_DRAT_VERIFIED_NOT_LEAN'
    result['all_inputs_regenerated'] = True
    result['cases'] = [{**c, 'input_regenerated': True} for c in result['cases']]
    temp = output.with_name(output.name + f'.{os.getpid()}.tmp')
    temp.write_text(json.dumps(result, indent=2) + '\n')
    temp.replace(output)
    return result


def verify_idempotent_rows(certificate, checker, output, seconds=3600,
                           resume=False, artifact_dir=None):
    """Check the 103 idempotent-root exclusions conditional on A/B.

    A/B already require some zero-fixed row and short cycles in every
    non-idempotent row. Relabeling an idempotent element as root preserves
    these properties. The auxiliary inputs never use the resulting
    restriction on idempotent rows themselves.
    """
    data = json.loads(certificate.read_text())
    assert data['law'] == 63 and data['order'] == 18
    assert data['scope'] == 'remaining_ab_models'
    expected = [{'name': 'pointidem-' + '-'.join(map(str, [1, *p])),
                 'cycles': [1, *p], 'idempotent': False}
                for p in partitions(17, 1) if any(k not in (1, 3, 4) for k in p)]
    assert len(expected) == 103
    # Here idempotent=False disables GLOBAL idempotence. The prescribed
    # leading one-cycle fixes 0 and makes the chosen root idempotent.
    assert [{k: c[k] for k in ['name', 'cycles', 'idempotent']}
            for c in data['cases']] == expected
    base = base_cnf(18)
    checker_hash = sha256(checker)
    previous = {}
    if resume and output.exists():
        old = json.loads(output.read_text())
        if old.get('checker_sha256') == checker_hash:
            previous = {c['name']: c for c in old['cases'] if c['status'] == 'DRAT_VERIFIED'}
    result = {'order': 18, 'source_certificate': str(certificate),
              'scope': 'remaining_ab_models', 'complete_excluded_type_list_checked': True,
              'requires_nonidempotent_short_rows': True, 'requires_zero_fixed_row': True,
              'checker_sha256': checker_hash, 'cases': [], 'status': 'CHECKING'}
    # Preserve independently checked records while regenerating inputs. Other
    # single-case verifiers may read this shared dependency cache concurrently;
    # each still checks both hashes before reusing a record.
    checked_records = {c['name']: previous[c['name']] for c in data['cases']
                       if c['name'] in previous and
                       all(previous[c['name']][k] == c[k]
                           for k in ['cnf_sha256', 'proof_sha256'])}
    for c in data['cases']:
        for flag in ['min_fixed', 'min_commuting', 'idempotent_no_short_cycles',
                     'fixed_count_consequence', 'idempotent_single_cycle',
                     'nonidempotent_cycle_filter', 'zero_three_square_involution',
                     'positive_fixed_short_cycles', 'one_fixed_short_cycles',
                     'all_row_short_cycles', 'diagonal_fiber_parity']:
            assert not c.get(flag, False), 'Circular or competing global restriction'
        all_nonidem = c.get('all_nonidempotent_short_cycles', False)
        zero_row = c.get('requires_zero_fixed_row', False)
        steps = c.get('short_cycle_steps', False)
        assert bool(c.get('requires_nonidempotent_element', False)) == all_nonidem
        assert not (zero_row or steps) or all_nonidem
        assert all(c.get(k) for k in ['zero_row_cycle_filter', 'uses_square_involution',
                                      'uses_positive_row_filter', 'uses_one_fixed_filter'])
        assert c['lex_rows'] in (2, 17)
        flags = {k: c[k] for k in ['lex_rows', 'lex_powers',
                                  'commuting_cycles_mod_three', 'no_even_identity',
                                  'commuting_triangles']}
        cnf = case_cnf(base, 18, c, **flags)
        add_nonidempotent_cycle_filter(cnf, 18, {'cycles': [3, 5, 5, 5]}, True)
        add_positive_fixed_short_cycles(cnf, 18, include_one=True,
                                         all_nonidempotent=all_nonidem)
        if all_nonidem:
            cnf.append([-variable(18, x, x, x) for x in range(18)])
        if steps:
            add_short_cycle_steps(cnf, 18)
        if zero_row:
            zeros = []
            for x in range(18):
                cnf.nv += 1
                lit = cnf.nv
                zeros.append(lit)
                cnf.extend([[-lit, -variable(18, x, y, y)] for y in range(18)])
            cnf.append(zeros)
        text = io.StringIO()
        cnf.to_fp(text)
        raw = text.getvalue().encode()
        assert hashlib.sha256(raw).hexdigest() == c['cnf_sha256']
        source, proof = Path(c['cnf']), Path(c['proof'])
        if artifact_dir:
            source = artifact_dir / 'cnf' / source.name
            proof = artifact_dir / 'proof' / proof.name
        saved = gzip.decompress(source.read_bytes()) if source.suffix == '.gz' else source.read_bytes()
        assert saved == raw
        assert sha256(proof) == c['proof_sha256']
        old = previous.get(c['name'])
        if old and all(old[k] == c[k] for k in ['cnf_sha256', 'proof_sha256']):
            record = old
        else:
            started = time.time()
            with tempfile.TemporaryDirectory(prefix='e63-idempotent-row-') as tmp:
                source = Path(tmp) / 'input.cnf'
                source.write_bytes(raw)
                with subprocess.Popen(['gzip', '-dc', str(proof)], stdout=subprocess.PIPE) as unzip:
                    try:
                        checked = subprocess.run([str(checker), str(source), '-i', '-w'],
                                                 stdin=unzip.stdout, stdout=subprocess.PIPE,
                                                 stderr=subprocess.STDOUT, timeout=seconds)
                    finally:
                        unzip.stdout.close()
                    assert unzip.wait() == 0, 'Corrupt idempotent-row dependency proof'
            assert checked.returncode == 0 and b's VERIFIED' in checked.stdout
            record = {'name': c['name'], 'cnf_sha256': c['cnf_sha256'],
                      'proof': str(proof), 'proof_sha256': c['proof_sha256'],
                      'status': 'DRAT_VERIFIED', 'input_regenerated': True,
                      'wall_seconds': round(time.time() - started, 3)}
        checked_records[c['name']] = record
        result['cases'] = [checked_records[c['name']] for c in data['cases']
                           if c['name'] in checked_records]
        temp = output.with_name(output.name + f'.{os.getpid()}.tmp')
        temp.write_text(json.dumps(result, indent=2) + '\n')
        temp.replace(output)
    result.update(status='ALL_103_DRAT_VERIFIED_NOT_LEAN', all_inputs_regenerated=True)
    temp = output.with_name(output.name + f'.{os.getpid()}.tmp')
    temp.write_text(json.dumps(result, indent=2) + '\n')
    temp.replace(output)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--checker', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--artifact-dir', type=Path,
                        help='Extracted certificate archive, containing cnf/ and proof/')
    parser.add_argument('--seconds', type=int, default=3600)
    parser.add_argument('--resume', action='store_true', help='Reuse unchanged, previously checked proofs')
    parser.add_argument('--only', nargs='+', help='Check only these named cases, retaining the complete split audit')
    parser.add_argument('--no-core-first', action='store_true',
                        help='Use drat-trim default propagation (-u), instead of core-first propagation')
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    n = report['order']
    expected = cases(n, report.get('minimum_fixed_bound', False))
    assert [{k: c[k] for k in ['name', 'idempotent', 'cycles']} for c in report['cases']] == expected
    base = base_cnf(n)
    case_by_name = {c['name']: c for c in report['cases']}
    if args.only:
        assert set(args.only) <= case_by_name.keys(), 'Unknown requested case'
    dependency_names = [c['name'] for c in expected if c['idempotent'] and
                        any(length in (3, 4) for length in c['cycles'][1:])]
    uses_dependencies = any(c.get('idempotent_no_short_cycles', False) for c in report['cases'])
    single_cycle_cases = [c for c in report['cases'] if c.get('idempotent_single_cycle', False)]
    if single_cycle_cases:
        assert len(single_cycle_cases) == 1
        selected = single_cycle_cases[0]
        assert selected['idempotent'] and selected['cycles'] == [1, n - 1]
        for c in expected:
            if not c['idempotent'] or c['name'] == selected['name']:
                continue
            metadata = case_by_name[c['name']]
            # Every other first-row type must be covered without a competing
            # global selection rule. A commuting bound of one is vacuous.
            assert (not metadata.get('min_commuting', report.get('min_commuting', False))
                    or c['cycles'].count(1) + 3 * c['cycles'].count(3) == 1)
    if uses_dependencies:
        for name in dependency_names:
            c = case_by_name[name]
            assert not c.get('idempotent_no_short_cycles', False), 'Circular cycle exclusion'
            assert not c.get('min_commuting', report.get('min_commuting', False)), (
                'Dependency must exclude the first-row type without a global commuting-count choice')
    proved = {r['name']: r for r in report['attempts'] if r['status'] == 'UNSAT_NOT_LEAN'}
    row_filter_dependencies = {}
    for c in report['cases']:
        if not c.get('nonidempotent_cycle_filter', False):
            continue
        assert n == 18 and not c['idempotent']
        fixed = c['cycles'].count(1)
        survivors = ([[3, 1, 3, 3, 4, 4]] if fixed else
                     [[3, 3, 3, 3, 3, 3], [3, 3, 4, 4, 4], [3, 5, 5, 5]])
        assert c['cycles'] in survivors
        dependencies = []
        for other in report['cases']:
            if (other['idempotent'] or other['cycles'].count(1) != fixed
                    or other['cycles'] in survivors):
                continue
            assert other['name'] in proved, 'Missing row-type refutation'
            assert not other.get('nonidempotent_cycle_filter', False), 'Circular row-type filter'
            assert not other.get('min_commuting', report.get('min_commuting', False)), (
                'Row-type dependency must allow any minimum-fixed-point row as 0')
            dependencies.append(other['name'])
        row_filter_dependencies[c['name']] = dependencies
    square_dependencies = None
    # A single-case check can reuse separately checked dependency traces after
    # regenerating their inputs and checking all hashes. A full check without
    # --resume rechecks every dependency proof as well.
    reuse_dependencies = args.resume or bool(args.only)
    uses_one_fixed = any(c.get('one_fixed_short_cycles', False) for c in report['cases'])
    if uses_one_fixed or any(c.get('zero_three_square_involution', False) for c in report['cases']):
        certificate = Path(report['square_involution_certificate'])
        square_dependencies = verify_square_involution(
            certificate, args.checker, certificate.with_name(certificate.stem + '_proofcheck.json'),
            args.seconds, reuse_dependencies, args.artifact_dir)
    positive_dependencies = None
    if any(c.get('positive_fixed_short_cycles', False) for c in report['cases']):
        certificate = Path(report['positive_rows_certificate'])
        positive_dependencies = verify_positive_rows(
            certificate, args.checker, certificate.with_name(certificate.stem + '_proofcheck.json'),
            args.seconds, reuse_dependencies, args.artifact_dir)
    one_fixed_dependencies = None
    if uses_one_fixed:
        assert positive_dependencies is not None
        certificate = Path(report['one_fixed_rows_certificate'])
        one_fixed_dependencies = verify_positive_rows(
            certificate, args.checker, certificate.with_name(certificate.stem + '_proofcheck.json'),
            args.seconds, reuse_dependencies, args.artifact_dir)
    idempotent_row_dependencies = None
    if any(c.get('all_row_short_cycles', False) for c in report['cases']):
        assert n == 18 and one_fixed_dependencies is not None
        for c in report['cases']:
            if c.get('all_row_short_cycles', False):
                assert c['cycles'] in ([3, 3, 3, 3, 3, 3], [3, 3, 4, 4, 4])
                assert all(c.get(k) for k in ['min_fixed', 'min_commuting',
                                              'all_nonidempotent_short_cycles'])
        certificate = Path(report['idempotent_rows_certificate'])
        idempotent_row_dependencies = verify_idempotent_rows(
            certificate, args.checker, certificate.with_name(certificate.stem + '_proofcheck.json'),
            args.seconds, reuse_dependencies, args.artifact_dir)
    result = {'order': n, 'source_report': str(args.report),
              'evidence': 'DRAT_CHECKED_COMPUTATION_NOT_LEAN',
              'complete_case_list_checked': True, 'min_fixed': report.get('min_fixed', False),
              'minimum_fixed_bound': report.get('minimum_fixed_bound', False),
              'min_commuting': report.get('min_commuting', False),
              'lex_rows': report.get('lex_rows', 0),
              'checker': str(args.checker), 'checker_sha256': sha256(args.checker),
              'core_first_propagation': not args.no_core_first,
              'cases': [], 'status': 'CHECKING'}
    if square_dependencies is not None:
        result['square_involution_dependencies'] = square_dependencies
    if positive_dependencies is not None:
        result['positive_row_dependencies'] = positive_dependencies
    if one_fixed_dependencies is not None:
        result['one_fixed_row_dependencies'] = one_fixed_dependencies
    if idempotent_row_dependencies is not None:
        result['idempotent_row_dependencies'] = idempotent_row_dependencies
    previous = {}
    if args.resume:
        old = json.loads(args.output.read_text())
        assert old['order'] == n and old['checker_sha256'] == result['checker_sha256']
        previous = {c['name']: c for c in old['cases'] if c['status'] == 'DRAT_VERIFIED'}
    # Keep still-applicable records while checking newly finished cases, so an
    # interrupted resume cannot discard proofs later in the traversal order.
    verified = {name: c for name, c in previous.items()
                if name in proved and c['cnf_sha256'] == case_by_name[name]['cnf_sha256']}

    def save():
        result['cases'] = [verified[c['name']] for c in expected if c['name'] in verified]
        temp = args.output.with_name(args.output.name + f'.{os.getpid()}.tmp')
        temp.write_text(json.dumps(result, indent=2) + '\n')
        temp.replace(args.output)

    for case in report['cases']:
        if args.only and case['name'] not in args.only:
            continue
        if case['name'] not in proved:
            continue
        attempt = proved[case['name']]
        source, proof = Path(case['cnf']), Path(attempt['proof'])
        if args.artifact_dir:
            source = args.artifact_dir / 'cnf' / source.name
            proof = args.artifact_dir / 'proof' / proof.name
        assert sha256(source) == case['cnf_sha256']
        old = previous.get(case['name'])
        if old and old['cnf_sha256'] == case['cnf_sha256'] and old['proof_sha256'] == sha256(proof):
            verified[case['name']] = old
            save()
            continue
        verified.pop(case['name'], None)
        text = io.StringIO()
        min_fixed = case.get('min_fixed', report.get('min_fixed', False))
        min_commuting = case.get('min_commuting', report.get('min_commuting', False))
        lex_rows = case.get('lex_rows', report.get('lex_rows', 0))
        lex_powers = case.get('lex_powers', report.get('lex_powers', False))
        even_columns = case.get('even_columns', report.get('even_columns', False))
        single_cycle = case.get('idempotent_single_cycle', False)
        row_filter = case.get('nonidempotent_cycle_filter', False)
        mod_three = case.get('commuting_cycles_mod_three', False)
        no_even_identity = case.get('no_even_identity', False)
        triangles = case.get('commuting_triangles', False)
        square_involution = case.get('zero_three_square_involution', False)
        positive_short = case.get('positive_fixed_short_cycles', False)
        one_fixed_short = case.get('one_fixed_short_cycles', False)
        all_nonidempotent = case.get('all_nonidempotent_short_cycles', False)
        short_steps = case.get('short_cycle_steps', False)
        all_short = case.get('all_row_short_cycles', False)
        diagonal_parity = case.get('diagonal_fiber_parity', False)
        no_short = case.get('idempotent_no_short_cycles', False)
        fixed_count = case.get('fixed_count_consequence', False)
        case_cnf(base, n, case, min_fixed, min_commuting, lex_rows, no_short,
                 fixed_count, lex_powers, even_columns, single_cycle, row_filter,
                 mod_three, no_even_identity, triangles, square_involution,
                 positive_short, one_fixed_short, all_nonidempotent,
                 short_steps, all_short, diagonal_parity).to_fp(text)
        assert hashlib.sha256(text.getvalue().encode()).hexdigest() == case['cnf_sha256']
        started = time.time()
        with subprocess.Popen(['gzip', '-dc', str(proof)], stdout=subprocess.PIPE) as unzip:
            checked = subprocess.run([str(args.checker), str(source), '-i', '-w',
                                      *(['-u'] if args.no_core_first else [])],
                                     stdin=unzip.stdout, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, timeout=args.seconds)
            unzip.stdout.close()
            assert unzip.wait() == 0, 'Corrupt or truncated compressed proof'
        assert checked.returncode == 0 and b's VERIFIED' in checked.stdout, checked.stdout[-4000:]
        log = source.with_suffix('.drat-check.log')
        log.write_bytes(checked.stdout)
        verified[case['name']] = {'name': case['name'], 'cnf_sha256': case['cnf_sha256'],
                                'min_fixed': min_fixed,
                                'min_commuting': min_commuting,
                                'lex_rows': lex_rows,
                                'lex_powers': lex_powers,
                                'even_columns': even_columns,
                                'idempotent_single_cycle': single_cycle,
                                'nonidempotent_cycle_filter': row_filter,
                                'commuting_cycles_mod_three': mod_three,
                                'no_even_identity': no_even_identity,
                                'commuting_triangles': triangles,
                                'zero_three_square_involution': square_involution,
                                'positive_fixed_short_cycles': positive_short,
                                'one_fixed_short_cycles': one_fixed_short,
                                'all_nonidempotent_short_cycles': all_nonidempotent,
                                'short_cycle_steps': short_steps,
                                'all_row_short_cycles': all_short,
                                'diagonal_fiber_parity': diagonal_parity,
                                'idempotent_no_short_cycles': no_short,
                                'fixed_count_consequence': fixed_count,
                                'input_regenerated': True, 'proof': str(proof),
                                'core_first_propagation': not args.no_core_first,
                                'proof_sha256': sha256(proof), 'log': str(log),
                                'wall_seconds': round(time.time() - started, 3),
                                'status': 'DRAT_VERIFIED'}
        save()
        print(case['name'], 'DRAT_VERIFIED', flush=True)
    if uses_dependencies:
        checked = {c['name'] for c in result['cases']}
        result['derived_cycle_exclusions'] = {
            'cycles': [3, 4], 'scope': 'idempotent models only',
            'dependency_cases': dependency_names,
            'all_dependencies_checked': set(dependency_names) <= checked}
    if row_filter_dependencies:
        checked_names = {c['name'] for c in result['cases']}
        result['row_cycle_filter_dependencies'] = {
            name: {'dependency_cases': names, 'all_dependencies_checked': set(names) <= checked_names}
            for name, names in row_filter_dependencies.items()}
    result['status'] = ('ALL_CASES_DRAT_VERIFIED_NOT_LEAN'
                        if len(result['cases']) == len(expected) else 'PARTIAL')
    save()
    print(result['status'], flush=True)


if __name__ == '__main__':
    main()
