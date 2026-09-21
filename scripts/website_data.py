#!/usr/bin/env python3
"""Pack or restore the precomputed website assets; uses only Python's standard library."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile

ROOT = Path(__file__).resolve().parent.parent
BUNDLE = ROOT / 'website_data/site-data.tar.gz'
MANIFEST = ROOT / 'website_data/manifest.json'
RELATIONS = [f'{relation}-{flavour}' for relation in
             ['implies', 'termStructural', 'structural', 'termDefinable', 'definable']
             for flavour in ['all', 'fin']]
RAW_NAMES = [f'{flavour}{suffix}.json.gz' for flavour in ['general', 'finite']
             for suffix in ['', '_implications_closure', '_raw_full_entries', '_outcomes']]
ASSETS = sorted([
    *(f'research/data/{name}.json' for name in [*RELATIONS, 'index', 'proofs', 'spectrum']),
    *(f'raw_data/{name}' for name in RAW_NAMES),
    'implications/implications.js', 'implications/graph.json', 'implications/finite_graph.json',
    'graphiti/graph.json', 'dashboard/index.md', 'dashboard/progress_badge.svg',
    'dashboard/outcomes.png', 'fme/unknowns.json', 'fme/index.html',
])


def digest(data):
    return hashlib.sha256(data).hexdigest()


def pack(site, overrides=None):
    overrides = overrides or {}
    index = json.loads((site / 'research/data/index.json').read_text())
    manifest = dict(version=1, source_commit=index['commit'], repository=index['repository'],
                    generated=index['generated'],
                    relations=[{k: relation[k] for k in ['key', 'classes', 'unresolved_equivalence_pairs', 'counts']}
                               for relation in index['relations']], files={})
    BUNDLE.parent.mkdir(parents=True, exist_ok=True)
    temporary = BUNDLE.with_suffix('.tmp')
    with temporary.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=9) as zipped:
            with tarfile.open(fileobj=zipped, mode='w|', format=tarfile.USTAR_FORMAT) as archive:
                for name in ASSETS:
                    data = overrides[name] if name in overrides else (site / name).read_bytes()
                    info = tarfile.TarInfo(name)
                    info.size, info.mode, info.mtime = len(data), 0o644, 0
                    archive.addfile(info, io.BytesIO(data))
                    manifest['files'][name] = dict(bytes=len(data), sha256=digest(data))
    if temporary.stat().st_size >= 100 * 1024**2:
        temporary.unlink()
        raise ValueError('Website bundle exceeds the GitHub regular-file limit.')
    temporary.replace(BUNDLE)
    manifest['archive'] = dict(file=BUNDLE.name, bytes=BUNDLE.stat().st_size,
                               sha256=digest(BUNDLE.read_bytes()))
    MANIFEST.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'Packed {len(ASSETS)} assets: {BUNDLE.stat().st_size / 1024**2:.2f} MiB')


def unpack(destination):
    manifest = json.loads(MANIFEST.read_text())
    if manifest['version'] != 1 or set(manifest['files']) != set(ASSETS):
        raise ValueError('Unsupported or incomplete website data manifest')
    raw = BUNDLE.read_bytes()
    if len(raw) != manifest['archive']['bytes'] or digest(raw) != manifest['archive']['sha256']:
        raise ValueError('Website archive does not match its manifest')
    # Validate every member before writing, including paths and the extracted bytes.
    contents = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
        for member in archive:
            name = member.name
            path = PurePosixPath(name)
            if (not member.isfile() or name not in ASSETS or name in contents
                    or path.is_absolute() or '..' in path.parts):
                raise ValueError(f'Unexpected archive member: {name}')
            data = archive.extractfile(member).read()
            expected = manifest['files'][name]
            if len(data) != expected['bytes'] or digest(data) != expected['sha256']:
                raise ValueError(f'Corrupt website asset: {name}')
            if name.endswith('.json'):
                json.loads(data)
            contents[name] = data
    if set(contents) != set(ASSETS):
        raise ValueError('Website archive is missing required assets')
    for name, data in contents.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    print(f'Restored {len(contents)} assets from source commit {manifest["source_commit"]}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['pack', 'unpack'])
    parser.add_argument('--site', type=Path, default=ROOT / 'home_page')
    args = parser.parse_args()
    (pack if args.command == 'pack' else unpack)(args.site.resolve())


if __name__ == '__main__':
    main()
