#!/usr/bin/env python3
"""Reconstruct TD(8,50) and TD(8,100) from recorded V(m,t) vectors.

Lean checks short inverse certificates and proves the translation development
and hole filling abstractly. Python and the input vectors are not trusted.
"""
import argparse
import json
from itertools import combinations
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
FILES={50:'td50_v6_7.json',100:'td100_v8_11.json'}

def generate(n):
    data=json.loads((ROOT/'data/spectrum'/FILES[n]).read_text())
    p=data['prime'];t=data['hole'];w=data['primitive'];V=data['vector'];m=len(V)-1
    assert n==p+t and p==m*t+1 and m+2>=8 and t>=7
    roots=[pow(w,m*e,p) for e in range(t)]
    M=[]
    for e in range(t):
        row=[None]+[a*roots[e]%p for a in V]
        for shift in range(m+2):
            moved=row[-shift:]+row[:-shift]
            M.append([('h',e) if a is None else ('g',a) for a in moved])
    M.append([('g',0)]*(m+2))
    for i,j in combinations(range(m+2),2):
        ds=[(r[i][1]-r[j][1])%p for r in M if r[i][0]==r[j][0]=='g']
        assert sorted(ds)==list(range(p))
    assert all(sum(r[i][0]=='h' for r in M)==t for i in range(m+2))
    assert all(sum(a[0]=='h' for a in r)<=1 for r in M)
    invs=[]
    for i in range(8):
        for j in range(8):
            inv=[0]*p
            if i!=j:
                for k,r in enumerate(M):
                    if r[i][0]==r[j][0]=='g':inv[(r[i][1]-r[j][1])%p]=k
            invs+=inv
    vec=lambda xs:'!['+', '.join(map(str,xs))+']'
    replacements={'N':n,'P':p,'H':t,'M':m,'COLS':m+2,'ROWS':len(M),'LAST':len(M)-1,
                  'ROOTS':vec(roots),'VECTOR':vec([0]+V),'INVERSES':'#['+', '.join(map(str,invs))+']'}
    out=(ROOT/'scripts/templates/spectrum_quasi_difference.lean.in').read_text()
    for key,value in replacements.items():out=out.replace('@'+key+'@',str(value))
    return ROOT/f'equational_theories/Spectrum/Equation63/Designs/N{n}.lean',out

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for n in FILES:
        path,text=generate(n)
        if args.check:assert path.read_text()==text,f'Stale generated file: {path}'
        else:path.write_text(text)
