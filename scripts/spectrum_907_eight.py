#!/usr/bin/env python3
"""Generate the E907 order-eight normalization and Lean-checked refutations.

The pointed-permutation normalization reuses the E883 algorithm at order 8.
Lean checks all 8! permutations. Every one of the 45 row forms, including
identity, is then refuted by bv_decide with only row injectivity and E907.
No right cancellation is assumed. Default checks generated files; --write
regenerates them. Requires python-sat through spectrum_907_row_search.
"""
import argparse
from pathlib import Path
from spectrum_907_row_search import canonical_rows

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write', action='store_true')
options = parser.parse_args()

def emit(path, text):
    if options.write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    elif not path.exists() or path.read_text() != text:
        raise SystemExit(f'Stale generated file: {path}')

R=Path('equational_theories/Spectrum/Equation907Eight');R.mkdir(exist_ok=True);(R/'Cases').mkdir(exist_ok=True)
NS='Spectrum.E907Eight';mod='equational_theories.Spectrum.Equation907Eight'
args='a b c d e f g h';letters=args.split();bvargs='b c d e f g h'
rows = [row for _, _, row in canonical_rows(8)]
assert len(rows) == 45
header=f'set_option maxHeartbeats 16000000\nset_option maxRecDepth 32768\n\nnamespace {NS}\n'
canon=Path('equational_theories/Spectrum/Equation883Nine/Canonical.lean').read_text()
canon=canon.replace('import equational_theories.Spectrum.Equation883Nine.Normalization','import equational_theories.Spectrum.Equation907').replace('Spectrum.E883Nine','Spectrum.E907Eight').replace('Fin 9','Fin 8').replace('List.range 8','List.range 7').replace('cycles f 9','cycles f 8').replace('List.finRange 9','List.finRange 8')
a=canon.index('def rows :');b=canon.index('\ndef rowTables',a)
canon=canon[:a]+'def rows : List (Fin 8 → Fin 8) := [\n'+',\n'.join('  !['+','.join(map(str,r))+']' for r in rows)+']\n'+canon[b:]
emit(R/'Canonical.lean', canon)
cm=Path('equational_theories/Spectrum/Equation883Nine/CanonicalModels.lean').read_text()
cm=cm[:cm.index('/-- Every nine-element')].replace('Equation883Nine','Equation907Eight').replace('E883Nine','E907Eight').replace('Fin 9','Fin 8').replace('List.finRange 9','List.finRange 8')
cm+='''theorem canonical_model (h : Law907.HasModel 8) :
    ∃ M : Magma (Fin 8), @Equation907 (Fin 8) M ∧
      ∃ g ∈ Canonical.rows, ∀ x, M.op 0 x = g x := by
  obtain ⟨M,hM⟩ := h
  have hE : @Equation907 (Fin 8) M := (@Law907.models_iff _ M).mp hM
  let f : Equiv.Perm (Fin 8) := Equiv.ofBijective (M.op 0)
    ⟨@E907.left_injective _ M _ hE 0, @E907.left_surjective _ M hE 0⟩
  let e := Canonical.relabel f
  obtain ⟨hzero,g,hg,he⟩ := Canonical.covers f
  let N := M.relabel e
  have hzero' : e.symm 0 = 0 := by
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using hzero.symm
  refine ⟨N, ?_, g, hg, ?_⟩
  · apply (@Law907.models_iff _ N).mp
    exact (@Law.satisfies_equiv _ _ _ M N (M.relabelEquiv e) Law907).mp hM
  · intro x
    change e (M.op (e.symm 0) (e.symm x)) = g x
    rw [hzero']
    exact (he (e.symm x)).trans (congrArg g (e.apply_symm_apply x))

end Spectrum.E907Eight
'''
emit(R/'CanonicalModels.lean', cm)
pack=' ++ '.join('bv '+l for l in reversed(letters));vec='!['+','.join(letters)+']'
s=f'import equational_theories.Spectrum.Equation907\n\n{header}\ndef bv (x : Fin 8) : BitVec 3 := BitVec.ofFin x\n'
s+=f'def pack ({args} : Fin 8) : BitVec 24 := {pack}\n\n@[spectrum_native]\ntheorem row_correct ({args} y : Fin 8) :\n    ((pack {args} >>> ((bv y).setWidth 24 * 3)).setWidth 3) = bv ({vec} y) := by\n  fin_cases y\n'
for i,l in enumerate(letters):s+=f'  · change ((({pack}) >>> ({i*3} : BitVec 24)).setWidth 3) = bv {l}\n    bv_decide\n'
selector=''.join(f'if x = {i} then {l} else ' for i,l in enumerate(letters[:-1]))+letters[-1]
s+=f'\ndef op ({args} : BitVec 24) (x y : BitVec 3) : BitVec 3 :=\n  ((({selector}) >>> (y.setWidth 24 * 3)).setWidth 3)\n'
s+='\ndef rows (M : Magma (Fin 8)) (x : Fin 8) : BitVec 24 :=\n  pack '+' '.join(f'(M.op x {i})' for i in range(8))+'\n'
rargs=' '.join(f'(rows M {i})' for i in range(8))
s+=f'def encoded (M : Magma (Fin 8)) := op {rargs}\n'
rs=''.join(f'if bv x = {i} then rows M {i} else ' for i in range(7))+'rows M 7'
vm='!['+','.join(f'M.op x {i}' for i in range(8))+']'
s+=f'''\ntheorem encoded_eq (M : Magma (Fin 8)) (x y : Fin 8) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : ({rs}) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : {vm} y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy]

end {NS}
'''
emit(R/'Table.lean', s)
op=lambda x,y:f'(op {args} {x} {y})'
laws=[f'({x} : BitVec 3) = {op(str(y),op(op(str(y),str(x)),op(str(x),str(y))))}' for x in range(8) for y in range(8)]
latin=[f'{op(str(x),str(y))} ≠ {op(str(x),str(z))}' for x in range(8) for y in range(8) for z in range(y+1,8)]
s=f'import {mod}.Table\n\n{header}\ndef testLaw ({args} : BitVec 24) : Prop :=\n  '+' ∧\n  '.join(laws)+'\n'
s+=f'\ndef testLatin ({args} : BitVec 24) : Prop :=\n  '+' ∧\n  '.join(latin)+f'\n\nend {NS}\n'
emit(R/'Predicates.lean', s)
s=f'import {mod}.Predicates\n\n{header}\ntheorem modelLaw (M : Magma (Fin 8)) (h : @Equation907 (Fin 8) M) :\n    testLaw {rargs} := by\n'
s+='''  have H (x y : Fin 8) : bv x =
      encoded M (bv y) (encoded M (encoded M (bv y) (bv x)) (encoded M (bv x) (bv y))) := by
    simp only [encoded_eq]
    exact congrArg bv (h x y)
'''
s+='  exact ⟨'+', '.join(f'H {x} {y}' for x in range(8) for y in range(8))+'⟩\n'
s+=f'\ntheorem modelLatin (M : Magma (Fin 8)) (h : @Equation907 (Fin 8) M) :\n    testLatin {rargs} := by\n'
s+='''  have hinj : Function.Injective bv := by decide
  have hL (x y z : Fin 8) (hyz : y ≠ z) :
      encoded M (bv x) (bv y) ≠ encoded M (bv x) (bv z) := by
    intro e
    apply hyz
    apply @E907.left_injective _ M _ h x
    apply hinj
    simpa only [encoded_eq] using e
'''
s+='  exact ⟨'+',\n    '.join(f'hL {x} {y} {z} (by decide)' for x in range(8) for y in range(8) for z in range(y+1,8))+f'⟩\n\nend {NS}\n'
emit(R/'Models.lean', s)
for i,row in enumerate(rows):
 val=sum(x<<(j*3) for j,x in enumerate(row))
 s=f'import {mod}.Predicates\n\n{header}\n@[spectrum_native]\ntheorem refuteRow{i:02d} ({bvargs} : BitVec 24)\n    (hl : testLatin {val} {bvargs}) : ¬ testLaw {val} {bvargs} := by\n  unfold testLatin testLaw op at *\n  bv_decide (config := {{ timeout := 120, embeddedConstraintSubst := false }})\nspectrum_assert refuteRow{i:02d} complete\n\nend {NS}\n'
 emit(R/f'Cases/Row{i:02d}.lean', s)

s = f'import {mod}.CanonicalModels\nimport {mod}.Models\n'
s += ''.join(f'import {mod}.Cases.Row{i:02d}\n' for i in range(45))
s += '\n' + header
s += 'def rowBits (r : Fin 8 → Fin 8) : BitVec 24 := pack ' + ' '.join(f'(r {i})' for i in range(8)) + '\n'
s += f'\ntheorem refuteRows (r : Fin 8 → Fin 8) (hr : r ∈ Canonical.rows) ({bvargs} : BitVec 24)\n    (hl : testLatin (rowBits r) {bvargs}) : ¬ testLaw (rowBits r) {bvargs} := by\n'
s += '  simp only [Canonical.rows, List.mem_cons, List.not_mem_nil, or_false] at hr\n'
s += '  rcases hr with ' + ' | '.join(['rfl']*45) + '\n'
s += ''.join(f'  · exact refuteRow{i:02d} {bvargs} hl\n' for i in range(45))
s += """
theorem not_order_907_8 : ¬ Law907.HasModel 8 := by
  intro h
  obtain ⟨M,hM,r,hr,hrow⟩ := canonical_model h
  have hbits : rows M 0 = rowBits r := by
    simp only [rows, rowBits, hrow]
  have hLatin := modelLatin M hM
  have hLaw := modelLaw M hM
  rw [hbits] at hLatin hLaw
  exact refuteRows r hr (rows M 1) (rows M 2) (rows M 3) (rows M 4)
    (rows M 5) (rows M 6) (rows M 7) hLatin hLaw
spectrum_assert not_order_907_8 complete

end Spectrum.E907Eight
"""
emit(R/'Exclusion.lean', s)
emit(R.with_suffix('.lean'), """import equational_theories.Spectrum.Equation907Eight.Exclusion

/-! E907 has no eight-element model. Lean checks all 8! first-row permutations
and the LRAT refutations of all 45 canonical forms, including the identity.
Only left cancellation, a consequence of the law and finiteness, is used. -/
namespace Spectrum

theorem not_order_907_8 : ¬ Law907.HasModel 8 := E907Eight.not_order_907_8
spectrum_assert not_order_907_8 complete

end Spectrum
""")
