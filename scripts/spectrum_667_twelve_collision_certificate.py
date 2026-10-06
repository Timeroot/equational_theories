#!/usr/bin/env python3
"""Prepare the noninjective-square certificates for E667 at order twelve.

Input LRAT traces are trimmed, their input IDs renumbered after removing
tautologies with spectrum_sanitize_lrat.cpp, and packed as compact RUP.
Lean independently defines the CNFs and verifies the resulting certificates.
"""
import argparse
import gzip
import hashlib
import json
import lzma
from pathlib import Path
from spectrum_667_incremental import partitions

ROOT=Path(__file__).resolve().parent.parent
DEST=ROOT/'data/spectrum/667_twelve_collision_rup'
META=ROOT/'data/spectrum/667_order12_collision_refutations.json'
LEAN=ROOT/'equational_theories/Spectrum/Equation667Twelve'


def sha(x):return hashlib.sha256(x).hexdigest()


def unpack(path):
    data=path.read_bytes()
    return lzma.decompress(data) if path.suffix=='.xz' else gzip.decompress(data)


def input_mask(data):
    """Return the optional input mask and the underlying v1 clause stream."""
    value=shift=pos=0
    while True:
        b=data[pos];pos+=1;value|=(b&127)<<shift
        if b<128:break
        shift+=7
        assert shift<70
    if data[pos]!=ord('m'):return None,data
    end=pos+1+value//2
    assert end<=len(data)
    mask=data[pos+1:end]
    assert mask[0]==0 and all(x in (0,1) for x in mask)
    return mask,data[:pos]+data[end:]


def canonical_clauses(path,sanitize):
    result=[]
    for line in path.read_text().splitlines()[1:]:
        clause=set(map(int,line.split()[:-1]))
        if sanitize and any(-v in clause for v in clause):continue
        result.append(sorted(clause))
    return result


def prepare(work):
    specs=[('three',None,work/'square-collision-0'),('four',None,work/'collision-proofs/four')]
    for i,c in enumerate(partitions(12)):
        if c[0]==1 and (c.count(1)>1 or 2 in c):
            specs.append((f'row{i:03d}',i,work/'idempotent-collision-rows'/('-'.join(map(str,c)))))
    assert len(specs)==52
    DEST.mkdir(exist_ok=True,parents=True);rows=[]
    for name,index,stem in specs:
        source=stem.with_suffix('.cnf')
        canonical=canonical_clauses(source,True)
        assert canonical==canonical_clauses(stem.with_suffix('.lean.cnf'),False),name
        data=stem.with_suffix('.sanitized.rup.gz').read_bytes();path=DEST/(name+'.rup.gz')
        path.write_bytes(data)
        rows.append(dict(name=name,index=index,raw_cnf_sha256=sha(source.read_bytes()),
            sanitized_clauses=len(canonical),
            canonical_clause_sha256=sha(json.dumps(canonical,separators=(',',':')).encode()),
            lean_cnf_match=True,compressed_bytes=len(data),compressed_sha256=sha(data),
            compact_sha256=sha(gzip.decompress(data)),certificate=str(path.relative_to(ROOT))))
    META.write_text(json.dumps(dict(law=667,order=12,
        scope='three/four-point square collisions and 50 idempotent-collision row types',
        trust='Lean CompactRup reconstruction followed by LRAT.check_sound; spectrum_native',
        cases=rows),indent=2)+'\n')


def audit():
    rows=json.loads(META.read_text())['cases'];assert len(rows)==52
    for r in rows:
        data=(ROOT/r['certificate']).read_bytes()
        assert len(data)==r['compressed_bytes'] and sha(data)==r['compressed_sha256']
        compact=unpack(ROOT/r['certificate'])
        assert sha(compact)==r['compact_sha256']
        if 'selected_input_clauses' in r:
            mask,_=input_mask(compact)
            assert mask is not None and len(mask)==r['sanitized_clauses']+1
            assert sum(mask)==r['selected_input_clauses']
    return rows


def select_inputs(work):
    """Install input masks and xz compression; preserve every learned clause stream."""
    meta=json.loads(META.read_text())
    prepared=[]
    for r in meta['cases']:
        path=ROOT/r['certificate']
        old=unpack(path)
        compact=gzip.decompress((work/(r['name']+'.masked.rup.gz')).read_bytes())
        mask,plain=input_mask(compact)
        assert mask is not None and plain==input_mask(old)[1],r['name']
        assert len(mask)==r['sanitized_clauses']+1
        dest=path.with_suffix('.xz')
        data=lzma.compress(compact,preset=6)
        prepared.append((path,dest,data))
        r.update(selected_input_clauses=sum(mask),compressed_bytes=len(data),
            certificate=str(dest.relative_to(ROOT)),
            compressed_sha256=sha(data),compact_sha256=sha(compact))
    meta.pop('validation',None)
    meta.pop('integration_validation',None)
    for _,dest,data in prepared:dest.write_bytes(data)
    META.write_text(json.dumps(meta,indent=2)+'\n')
    for old,dest,_ in prepared:
        if old!=dest:old.unlink()


def improve(work):
    """Replace the five expensive rows after matching independently exported Lean CNFs."""
    meta=json.loads(META.read_text())
    for r in meta['cases']:
        i=r['index']
        if i not in (37,38,39,40,41):continue
        mode='min-fibers' if i in (37,39) else 'fibers'
        stem=work/f'row{i:03d}-{mode}'
        source=stem.with_suffix('.cnf')
        canonical=canonical_clauses(source,False)
        assert canonical==canonical_clauses(work/f'row{i:03d}.lean.cnf',False),i
        data=stem.with_suffix('.rup.gz').read_bytes()
        if r['certificate'].endswith('.xz'):
            data=lzma.compress(gzip.decompress(data),preset=6)
        (ROOT/r['certificate']).write_bytes(data)
        r.pop('selected_input_clauses',None)
        r.update(encoding='row-reduction',raw_cnf_sha256=sha(source.read_bytes()),
            sanitized_clauses=len(canonical),
            canonical_clause_sha256=sha(json.dumps(canonical,separators=(',',':')).encode()),
            lean_cnf_match=True,compressed_bytes=len(data),compressed_sha256=sha(data),
            compact_sha256=sha(unpack(ROOT/r['certificate'])))
    # Timings and validation of the old formulas do not describe the replacements.
    meta.pop('validation',None)
    meta.pop('integration_validation',None)
    META.write_text(json.dumps(meta,indent=2)+'\n')


def render(rows):
    core=[r for r in rows if r['index'] is None]
    groups=[[] for _ in range(4)]
    for r in sorted((r for r in rows if r['index'] is not None),key=lambda r:-r['compressed_bytes']):
        min(groups,key=lambda g:sum(x['compressed_bytes'] for x in g)).append(r)
    groups=[[r] for r in core]+[sorted(g,key=lambda r:r['index']) for g in groups]
    (LEAN/'Certificates').mkdir(exist_ok=True)
    for batch,group in enumerate(groups):
        s='''import equational_theories.Spectrum.Equation667Twelve.Collisions
import equational_theories.Spectrum.Equation667Twelve.IdempotentCollision
import equational_theories.Spectrum.Equation667Twelve.RowReduction
import SpectrumCertificateData
import SpectrumCertificateData.Replay

/- Generated by scripts/spectrum_667_twelve_collision_certificate.py.
The actual Lean CNF is used for reconstruction and the verified LRAT check. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
'''
        for r in group:
            formula={'three':'threeFormula','four':'fourFormula'}.get(r['name'],f'natRow {r["index"]}')
            if r.get('encoding')=='row-reduction':formula=f'RowReduction.natFormula {r["index"]}'
            embed='include_binary_xz' if r['certificate'].endswith('.xz') else 'include_binary_gzip'
            s+=f'''
namespace Spectrum.E667.Twelve.Certificates.C_{r['name']}
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction :=
  CompactRup.reconstruct ({embed} "../../../../{r['certificate']}") ({formula})
@[spectrum_native]
theorem checked : check refutation ({formula}) = true := by native_decide
theorem unsat : ({formula}).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E667.Twelve.Certificates.C_{r['name']}
'''
        (LEAN/f'Certificates/Batch{batch:02d}.lean').write_text(s)
    ids=[r['index'] for r in rows if r['index'] is not None]
    s=''.join(f'import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch{b:02d}\n' for b in range(6))
    s+='''
namespace Spectrum.E667.Twelve
theorem rows_refuted : ∀ i ∈ collisionRows,
    ∀ f : Fin 12 → Fin 12 → Fin 12, RightIdentityTwelve.Holds f →
      (∀ y, f 0 y = FixedSquare.Cases.table i y) → False := by
  intro i hi f hf hr
  simp only [collisionRows, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with '''+' | '.join('rfl' for _ in ids)+'\n'
    for r in rows:
        i=r['index']
        if i is None:continue
        if r.get('encoding')=='row-reduction':
            s+=f'  · exact RowReduction.no_fixed_row {i} Certificates.C_row{i:03d}.unsat\n'
            s+='      Certificates.C_three.unsat Certificates.C_four.unsat f hf hr\n'
        else:
            s+=f'  · exact no_fixed_row {i} Certificates.C_row{i:03d}.unsat f hf hr\n'
    s+='''
theorem three_refuted : threeFormula.Unsat := Certificates.C_three.unsat
theorem four_refuted : fourFormula.Unsat := Certificates.C_four.unsat

theorem no_idempotent_collision
    (f : Fin 12 → Fin 12 → Fin 12) (h : RightIdentityTwelve.Holds f)
    (he : f 0 0 = 0) (x : Fin 12) (hx : x ≠ 0) (hs : f x x = 0) : False := by
  obtain ⟨i,hi,g,hg,hr⟩ := normalize_idempotent_collision f h he x hx hs
  exact rows_refuted i hi g hg hr

spectrum_assert rows_refuted complete
spectrum_assert three_refuted complete
spectrum_assert four_refuted complete
spectrum_assert no_idempotent_collision complete
end Spectrum.E667.Twelve
'''
    (LEAN/'Certificates.lean').write_text(s)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prepare',type=Path)
    ap.add_argument('--improve',type=Path)
    ap.add_argument('--select-inputs',type=Path)
    ap.add_argument('--write-lean',action='store_true')
    args=ap.parse_args()
    if args.prepare:prepare(args.prepare)
    if args.improve:improve(args.improve)
    if args.select_inputs:select_inputs(args.select_inputs)
    rows=audit()
    if args.write_lean:render(rows)
    print('Audited 52 collision certificates:',sum(r['compressed_bytes'] for r in rows),'compressed bytes')
