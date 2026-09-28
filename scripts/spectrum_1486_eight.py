#!/usr/bin/env python3
"""Generate the checked two-image E1486 order-eight refutation.

The mathematical normalization is in EightNormalization.lean; this emits only
its finite checker and the proved representation of eight-element tables.
"""
from pathlib import Path
import argparse
import spectrum_small_certificates as c

ROOT = Path(__file__).resolve().parents[1]


def sources():
    enc='\n'.join(['import equational_theories.Spectrum.Basic','import equational_theories.Spectrum.Status','import Lean.Elab.Tactic.BVDecide','import Mathlib.Tactic.FinCases','import Mathlib.Data.Fin.VecNotation','','namespace Spectrum.FiniteTableEncoding',c.encoding(8),'end Spectrum.FiniteTableEncoding',''])
    output = {'Encoding8.lean': enc}
    s=c.raw_certificate(1486,8,120)
    s=s.replace('import equational_theories.Spectrum.FiniteTableEncoding','import equational_theories.Spectrum.Equation1486.Encoding8')
    s=s[:s.index('theorem Spectrum.not_order_1486_8')]
    s=s.replace('E1486N8','E1486N8TwoImages')
    args=' '.join(f'a{i}'for i in range(8)); rows=' '.join(f'(rows M {i})'for i in range(8))
    s=s.replace(f'def test ({args}',f'def test (inside : Bool) ({args}')
    tests=[f'(op {args} 0 (op {args} {z} {z}) = (if inside then 0 else 1) ∨ op {args} 0 (op {args} {z} {z}) = (if inside then 1 else 2))'for z in range(8)]
    s=s.replace(' : Prop :=\n  ',' : Prop :=\n  '+' ∧\n  '.join(tests)+' ∧\n  ',1)
    s=s.replace(f'theorem refute ({args}',f'theorem refute (inside : Bool) ({args}').replace(f'¬ test {args}',f'¬ test inside {args}')
    s=s.replace('  unfold test op clip\n  bv_decide','  cases inside <;> unfold test op clip <;>\n    bv_decide')
    s=s.replace('theorem impossible (M :','theorem impossible (inside : Bool) (M :')
    s=s.replace('(h : @Equation1486 (Fin 8) M) : False := by','(h : @Equation1486 (Fin 8) M)\n    (hi : ∀ z, M.op 0 (M.op z z) = (if inside then 0 else 1) ∨\n      M.op 0 (M.op z z) = (if inside then 1 else 2)) : False := by')
    s=s.replace(f'  apply refute {rows}',f'  apply refute inside {rows}')
    s=s.replace('  refine ⟨','  refine ⟨'+', '.join('?_'for _ in range(8))+', ',1)
    pos=s.index('  · change');proof=''
    for z in range(8):
     proof+=f'''  · change encoded M (bv (0 : Fin 8)) (encoded M (bv ({z} : Fin 8)) (bv ({z} : Fin 8))) = (if inside then 0 else 1) ∨
          encoded M (bv (0 : Fin 8)) (encoded M (bv ({z} : Fin 8)) (bv ({z} : Fin 8))) = (if inside then 1 else 2)
        simp only [he]
        have h0 := hi {z}
        cases inside <;> simpa [FiniteTableEncoding.N8.bv] using h0.elim (fun h => Or.inl (congrArg bv h)) (fun h => Or.inr (congrArg bv h))
    '''
    proof = proof.replace("\n    ", "\n")
    s=s[:pos]+proof+s[pos:]
    output['EightRefutation.lean'] = s
    return output


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--write', action='store_true')
    args = p.parse_args()
    for name, source in sources().items():
        path = ROOT / 'equational_theories/Spectrum/Equation1486' / name
        if args.write:
            path.write_text(source)
        else:
            assert path.read_text() == source, path
    print('Checked E1486 order-eight refutation source reproduction.')


if __name__ == '__main__':
    main()
