#!/usr/bin/env python3
"""Generate and verify all website data locally, then update the committed bundle."""
import argparse
import gzip
import os
import shutil
import subprocess
import sys

from website_data import ROOT, pack


def run(*command, output=None, env=None):
    print('+ ' + ' '.join(map(str, command)), flush=True)
    if output is None:
        subprocess.run(list(map(str, command)), cwd=ROOT, env=env, check=True)
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open('wb') as out:
            subprocess.run(list(map(str, command)), cwd=ROOT, env=env, stdout=out, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true', help='Use an already completed local Lean build')
    args = parser.parse_args()
    for tool in ['lake', 'ruby', 'node']:
        if not shutil.which(tool):
            raise SystemExit(f'Missing {tool}; see docs/research_website.md')
    for module in ['numpy', 'markdown', 'PIL']:
        __import__(module)
    changed = subprocess.check_output(['git', 'diff', '--name-only', 'HEAD', '--', '*.lean',
                                      'data/spectrum', 'data/equations.txt', 'data/duals.json'],
                                     cwd=ROOT, text=True).strip()
    untracked = subprocess.check_output(
        ['git', 'ls-files', '--others', '--exclude-standard', '--', '*.lean',
         'data/spectrum', 'data/equations.txt', 'data/duals.json'], cwd=ROOT, text=True).strip()
    if changed or untracked:
        raise SystemExit('Commit the Lean/evidence changes before generating commit-pinned website data:\n'
                         + '\n'.join(filter(None, [changed, untracked])))
    if not args.skip_build:
        run('lake', 'build', 'equational_theories', 'extract_implications')
    work = ROOT / '.cache/website'
    raw = work / 'raw_data'
    site = ROOT / 'home_page'
    raw.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, OPENBLAS_NUM_THREADS='2',
               WEBSITE_DECLARATION_REQUESTS=str(work / 'declaration-requests.json'),
               WEBSITE_DECLARATIONS=str(work / 'declarations.json'))
    # Each export is sequential so the large Lean environments do not compete for RAM.
    for flavour, flags in [('general', []), ('finite', ['--finite-only'])]:
        for suffix, command in [('', ['--json']),
                                ('_implications_closure', ['--json', '--closure', '--only-implications']),
                                ('_raw_full_entries', ['raw', '--full-entries']),
                                ('_outcomes', ['outcomes'])]:
            run('lake', 'exe', 'extract_implications', *command, *flags,
                output=raw / f'{flavour}{suffix}.json')
        run('lake', 'exe', 'extract_implications', 'unknowns', *flags,
            output=work / f'{flavour}_unknowns.json')
    run('lake', 'env', 'lean', 'scripts/check_spectrum.lean')
    run(sys.executable, 'scripts/website_declarations.py', work / 'declaration-requests.json')
    run('lake', 'env', 'lean', 'scripts/export_website.lean', env=env)
    run(sys.executable, 'scripts/generate_research_site.py',
        '--declarations', work / 'declarations.json',
        '--general-entries', raw / 'general_raw_full_entries.json',
        '--finite-entries', raw / 'finite_raw_full_entries.json', env=env)
    run('lake', 'env', 'lean', 'scripts/check_website_witnesses.lean')
    run('node', 'scripts/test_research_proofs.mjs')
    run('node', 'scripts/test_research_site.mjs')
    run(sys.executable, 'scripts/generate_equation_implication_js.py',
        output=site / 'implications/implications.js')
    for flavour, filename in [('general', 'graph.json'), ('finite', 'finite_graph.json')]:
        run(sys.executable, 'scripts/generate_equation_explorer_graph.py',
            raw / f'{flavour}_outcomes.json', raw / f'{flavour}_raw_full_entries.json',
            output=site / 'implications' / filename)
    run('ruby', 'scripts/generate_graphiti_data.rb', 'data/duals.json',
        raw / 'general_implications_closure.json', work / 'general_unknowns.json',
        raw / 'finite_implications_closure.json', work / 'finite_unknowns.json',
        output=site / 'graphiti/graph.json')
    run('ruby', 'scripts/generate_dashboard_graph_info.rb', raw, output=work / 'graph_info.md')
    run(sys.executable, 'scripts/generate_dashboard.py', work / 'graph_info.md')
    run(sys.executable, 'scripts/outcomes_to_image.py', raw / 'general_outcomes.json',
        '--outfile', site / 'dashboard/outcomes.png')
    (site / 'raw_data').mkdir(exist_ok=True)
    print('Compressing raw-data downloads…', flush=True)
    for path in sorted(raw.glob('*.json')):
        with path.open('rb') as source, (site / 'raw_data' / (path.name + '.gz')).open('wb') as out:
            with gzip.GzipFile(filename='', mode='wb', fileobj=out, mtime=0, compresslevel=9) as zipped:
                shutil.copyfileobj(source, zipped)
        # Keep the downloadable compressed copy; these intermediates total about 1.7 GiB.
        path.unlink()
    commit = subprocess.check_output(['git', 'rev-parse', '--short', 'HEAD'], cwd=ROOT).strip()
    pack(site, overrides={
        'fme/unknowns.json': (work / 'finite_unknowns.json').read_bytes(),
        'fme/index.html': (site / 'fme/index.html').read_bytes().replace(b'UNKNOWN_VERSION', commit),
    })
    print('Ready: commit website_data/site-data.tar.gz and website_data/manifest.json, then push.', flush=True)


if __name__ == '__main__':
    main()
