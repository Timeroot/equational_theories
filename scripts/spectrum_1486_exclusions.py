#!/usr/bin/env python3
"""Reproduce E1486 small-order refutations whose Lean checks have passed.

The inherited encoding proves that every multiplication table is represented.
Lean's registered native LRAT checker validates the SAT certificates.
"""
from pathlib import Path
import argparse
import spectrum_small_certificates as certificates
from spectrum_1486_eight import sources as eight_sources

ROOT=Path(__file__).resolve().parents[1]
CHECKED=(5,6,7)

def main():
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
    imports=['import equational_theories.Spectrum.Equation1486.SingletonRow']
    for n in CHECKED:
        out=ROOT/f'equational_theories/Spectrum/Equation1486/Exclusion{n}.lean'
        certificates.NORMALIZED_CASES.add((1486,7))
        text=certificates.certificate(1486,n,180)
        if a.write:out.write_text(text)
        else:assert out.read_text()==text,out
        imports.append(f'import equational_theories.Spectrum.Equation1486.Exclusion{n}')
    for name, text in eight_sources().items():
        out=ROOT/'equational_theories/Spectrum/Equation1486'/name
        if a.write:out.write_text(text)
        else:assert out.read_text()==text,out
    imports.append('import equational_theories.Spectrum.Equation1486.Exclusion8')
    out=ROOT/'equational_theories/Spectrum/Equation1486/Exclusions.lean'
    text='\n'.join(imports)+'\n'
    if a.write:out.write_text(text)
    else:assert out.read_text()==text,out
    print('Checked source reproduction for E1486 exclusions:',(*CHECKED,8))

if __name__=='__main__':main()
