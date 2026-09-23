"""Generate exhaustive, checked small-order spectrum exclusions.

Run through spectrum_generate.py --write / --check. CHECKED_CASES contains only
refutations already verified by Lean. Each finite table is packed into bit-vector
rows; row_correct and encoded_eq prove that every magma is represented. The SAT
solver supplies a certificate checked by the registered native LRAT checker.
"""
import itertools
from spectrum_generate import load_equations, variables


CHECKED_CASES = (
    (63, 6),
    (467, 4),
    (467, 6),
    (670, 6),
    (704, 4),
    (704, 6),
    (907, 4),
    (907, 5),
    (907, 6),
    (1076, 4),
    (1076, 6),
    (1076, 7),
    (1110, 6),
    (1279, 4),
    (1279, 6),
    (1286, 4),
    (1286, 6),
    (1313, 4),
    (1313, 6),
    (1483, 5),
    (1483, 6),
    (1489, 4),
    (1516, 4),
    (1516, 6),
)

NORMALIZED_CASES = {(1483, 6)}


def encoding(n):
    w=(n-1).bit_length(); r=n*w
    args=' '.join(f'a{i}' for i in range(n))
    packed=' ++ '.join(f'bv a{i}' for i in reversed(range(n)))
    selection=''.join(f'if x = {i} then a{i} else ' for i in range(n-1))+f'a{n-1}'
    rows=' '.join(f'(rows M {i})' for i in range(n))
    vals=', '.join(f'M.op x {i}' for i in range(n))
    lines=[f'namespace N{n}',
      f'def bv (x : Fin {n}) : BitVec {w} := BitVec.ofFin (x.castLE (by decide : {n} ≤ {2**w}))',
      f'def clip (x : BitVec {w}) : BitVec {w} := '+(f'if x < {n} then x else 0' if n!=2**w else 'x'),
      f'@[simp] theorem clip_bv (x : Fin {n}) : clip (bv x) = bv x := by fin_cases x <;> decide',
      f'def pack ({args} : Fin {n}) : BitVec {r} := {packed}',
      f'@[spectrum_native]\ntheorem row_correct ({args} y : Fin {n}) :',
      f'    ((pack {args} >>> ((bv y).setWidth {r} * {w})).setWidth {w}) =',
      f'      bv (![{", ".join(f"a{i}" for i in range(n))}] y) := by',
      '  fin_cases y']
    for i in range(n):
        lines += [f'  · change ((({packed}) >>> ({w*i} : BitVec {r})).setWidth {w}) = bv a{i}', '    bv_decide']
    lines += [f'def op ({args} : BitVec {r}) (x y : BitVec {w}) : BitVec {w} :=',
      f'  clip ((({selection}) >>> (y.setWidth {r} * {w})).setWidth {w})',
      f'def rows (M : Magma (Fin {n})) (x : Fin {n}) : BitVec {r} :=',
      '  pack '+' '.join(f'(M.op x {i})' for i in range(n)),
      f'def encoded (M : Magma (Fin {n})) := op {rows}',
      f'theorem encoded_eq (M : Magma (Fin {n})) (x y : Fin {n}) :',
      '    encoded M (bv x) (bv y) = bv (M.op x y) := by',
      '  unfold encoded op',
      '  have hx : ('+''.join(f'if bv x = {i} then rows M {i} else ' for i in range(n-1))+f'rows M {n-1}) = rows M x := by',
      '    fin_cases x <;> rfl',
      '  rw [hx, rows, row_correct]',
      f'  have hy : ![{vals}] y = M.op x y := by',
      '    fin_cases y <;> rfl',
      '  rw [hy, clip_bv]',
      f'end N{n}', '']
    return '\n'.join(lines)


def encoding_source():
    return '\n'.join(['import equational_theories.Spectrum.Basic',
      'import equational_theories.Spectrum.Status', 'import Lean.Elab.Tactic.BVDecide',
      'import Mathlib.Tactic.FinCases', 'import Mathlib.Data.Fin.VecNotation', '',
      '/-! Generated finite table encodings. Each encoding represents every magma of the indicated size. -/',
      'namespace Spectrum.FiniteTableEncoding',
      *[encoding(n) for n in sorted({n for _, n in CHECKED_CASES})], 'end Spectrum.FiniteTableEncoding', ''])


def raw_certificate(law,n,timeout=300):
    w=(n-1).bit_length(); r=n*w
    args=' '.join(f'a{i}' for i in range(n))
    lhs,rhs=load_equations()[law-1]
    vs=sorted(variables(lhs)|variables(rhs))
    values=list(itertools.product(range(n),repeat=len(vs)))
    def render(t,a,lift=False):
        if isinstance(t,str):
            return f'(bv ({a[t]} : Fin {n}))' if lift else str(a[t])
        op='encoded M' if lift else 'op '+args
        return f'({op} {render(t[0],a,lift)} {render(t[1],a,lift)})'
    tests=[f'({render(lhs,dict(zip(vs,v)))} : BitVec {w}) = {render(rhs,dict(zip(vs,v)))}' for v in values]
    lines=['import equational_theories.Spectrum.FiniteTableEncoding',
      'import equational_theories.Equations.All', '',
      '/-! Generated exhaustive refutation, verified by Lean\'s registered native LRAT checker. -/',
      'set_option maxHeartbeats 4000000', 'set_option maxRecDepth 16384',
      f'namespace Spectrum.FiniteExclusion.E{law}N{n}',
      f'open FiniteTableEncoding.N{n}',
      f'def test ({args} : BitVec {r}) : Prop :=\n  '+' ∧\n  '.join(tests),
      f'@[spectrum_native]\ntheorem refute ({args} : BitVec {r}) : ¬ test {args} := by',
      '  unfold test op clip',
      f'  bv_decide (config := {{ timeout := {timeout}, embeddedConstraintSubst := false }})',
      'spectrum_assert refute complete',
      f'theorem impossible (M : Magma (Fin {n})) (h : @Equation{law} (Fin {n}) M) : False := by',
      '  have he := encoded_eq M',
      '  apply refute '+' '.join(f'(rows M {i})' for i in range(n)),
      '  unfold test',
      '  refine ⟨'+', '.join('?_' for _ in values)+'⟩']
    for v in values:
        a=dict(zip(vs,v))
        lines += [f'  · change {render(lhs,a,True)} = {render(rhs,a,True)}', '    simp only [he]',
          '    exact congrArg bv (h '+' '.join(map(str,v))+')']
    lines += [f'end Spectrum.FiniteExclusion.E{law}N{n}',
      f'theorem Spectrum.not_order_{law}_{n} : ¬ Law{law}.HasModel {n} := by',
      '  rintro ⟨M, hM⟩',
      f'  exact Spectrum.FiniteExclusion.E{law}N{n}.impossible M ((@Law{law}.models_iff _ M).mp hM)',
      f'spectrum_assert Spectrum.not_order_{law}_{n} complete', '']
    return '\n'.join(lines)

def certificate(law,n,timeout=300):
    s=raw_certificate(law,n,timeout)
    if (law,n) not in NORMALIZED_CASES:
        return s
    args=' '.join(f'a{i}' for i in range(n))
    s=s.replace('import equational_theories.Spectrum.FiniteTableEncoding','import equational_theories.Spectrum.FiniteTableEncoding\nimport equational_theories.Spectrum.SmallModelNormalization')
    s=s.replace(' : Prop :=\n  ',f' : Prop :=\n  (op {args} 0 0 = 0 ∨ op {args} 0 0 = 1) ∧\n  ',1)
    s=s.replace(f'(h : @Equation{law} (Fin {n}) M) : False := by',f'(h : @Equation{law} (Fin {n}) M)\n    (hd : M.op 0 0 = 0 ∨ M.op 0 0 = 1) : False := by')
    s=s.replace('  refine ⟨','  refine ⟨?_, ',1)
    i=s.index('  · change')
    proof=f'''  · change encoded M (bv (0 : Fin {n})) (bv (0 : Fin {n})) = bv (0 : Fin {n}) ∨
      encoded M (bv (0 : Fin {n})) (bv (0 : Fin {n})) = bv (1 : Fin {n})
    simp only [he]
    exact hd.elim (fun h => Or.inl (congrArg bv h)) (fun h => Or.inr (congrArg bv h))
'''
    s=s[:i]+proof+s[i:]
    s=s.replace('  rintro ⟨M, hM⟩',f'  intro h\n  obtain ⟨M, hM, hd⟩ := Spectrum.Symmetry.two_label_model Law{law} h 0 1 (by decide)')
    s=s.replace(f'((@Law{law}.models_iff _ M).mp hM)',f'((@Law{law}.models_iff _ M).mp hM) hd')
    return s


def generate(root, emit):
    """Emit the common encoding, individual certificates, and import module."""
    target = root / "equational_theories/Spectrum"
    emit(target / "FiniteTableEncoding.lean", encoding_source())
    imports = []
    for law, n in CHECKED_CASES:
        name = f"Exclusion{law}_{n}"
        emit(target / "Generated" / (name + ".lean"), certificate(law, n))
        imports.append(f"import equational_theories.Spectrum.Generated.{name}")
    emit(target / "SmallCertificates.lean", "\n".join(imports) + "\n")
