"""Reproduce compiled orbit evaluators and their checked Lean bridges.

Only the exhaustive arithmetic runs in the precompiled DefOrbit library.
Small finite checks identify its tables, while symbolic lemmas identify every
parameter code and connect the boolean result to the original orbit family.
"""
import math
import re
from spectrum_generate import load_equations


def arr(xs):
    return '#[' + ', '.join(map(str, xs)) + ']'


def matrix(xs):
    return arr(arr(row) for row in xs)


def chunk_array_literals(source):
    """Bound elaborator/compiler recursion in unusually large data arrays."""
    def replace(match):
        name, typ, literal = match.groups()
        body = literal[2:-1]
        entries, depth, start = [], 0, 0
        for i, char in enumerate(body):
            if char in '[(':
                depth += 1
            elif char in '])':
                depth -= 1
            elif char == ',' and depth == 0:
                entries.append(body[start:i].strip())
                start = i + 1
        if body[start:].strip():
            entries.append(body[start:].strip())
        if len(entries) <= 256:
            return match.group(0)
        parts = [f'{name}Chunk{i // 128}' for i in range(0, len(entries), 128)]
        declarations = ''.join(
            f'def {part} : {typ} := {arr(entries[i:i + 128])}\n'
            for part, i in zip(parts, range(0, len(entries), 128), strict=True)
        )
        return declarations + (
            f'def {name} : {typ} :=\n'
            f'  ({arr(parts)} : Array ({typ})).foldl (fun acc xs => acc ++ xs) #[]'
        )

    return re.sub(r'^def (\w+Data) : (Array [^\n]+?) := (#\[[^\n]*\])$',
                  replace, source, flags=re.M)


def dimensions(d):
    assert d.get('mixed_indexed_parameters') and d.get('cache_word_images')
    assert d.get('restricted_target_test') and not d.get('pattern_first')
    assert not d.get('shared_four_chart') and not d.get('compact_literals')
    sizes = list(map(len, d['values']))
    assert all(sizes)
    total = math.prod(sizes)
    left = math.isqrt(total)
    while total % left:
        left -= 1
    places = [math.prod(sizes[:i]) for i in range(len(sizes))]
    return sizes, places, left, total // left


def targets(d):
    return sorted({d['candidates'][i]['target'] for i in d['selected_indices']})


def render_native(d, ns):
    sizes, places, _, _ = dimensions(d)
    n, q = d['order'], len(d['probes'])
    images = []
    for word in d['words']:
        perm = list(range(n))
        for i in reversed(word):
            perm = [d['generators'][i][x] for x in perm]
        images.append(perm)
    cells = [[images[w][v] for v in d['values'][o]]
             for row in d['transport'] for o, w in row]
    orbits = [o for row in d['transport'] for o, _ in row]
    s = f'''import DefOrbit

/-! Compiled evaluator reproduced from the finite orbit certificate JSON. -/
namespace DefOrbit.Native{ns}

def cellData : Array (Array (Fin {n})) := {matrix(cells)}
def orbitData : Array Nat := {arr(orbits)}
def placesData : Array Nat := {arr(places)}
def sizesData : Array Nat := {arr(sizes)}
def probeData : Array (Array (Fin {n})) := {matrix(d['probes'])}
def probe (i : Fin {q}) (x : Fin {n}) : Fin {n} :=
  (probeData.getD i.val #[]).getD x.val 0

def op (code : Nat) (x y : Fin {n}) : Fin {n} :=
  let c := x.val * {n} + y.val
  let r := orbitData.getD c 0
  let v := (code / placesData.getD r 0) % sizesData.getD r 0
  (cellData.getD c #[]).getD v 0

abbrev pattern (code : Nat) : Prop := ∀ i : Fin {q}, ¬ ∀ x y : Fin {n},
  probe i (op code x y) = op code (probe i x) (probe i y)
'''
    if d.get('native_large_literals'):
        s = s.replace(f'namespace DefOrbit.Native{ns}',
                      'set_option maxRecDepth 100000\n'
                      'set_option maxHeartbeats 8000000\n'
                      f'namespace DefOrbit.Native{ns}', 1)
    for t in targets(d):
        names = []
        def expression(term):
            if isinstance(term, str):
                if term not in names:
                    names.append(term)
                return '0' if term == names[0] else term
            return f'(op code {expression(term[0])} {expression(term[1])})'
        a, b = load_equations()[t - 1]
        equation = f'{expression(a)} = {expression(b)}'
        if len(names) > 1:
            equation = f"∀ {' '.join(names[1:])} : Fin {n}, {equation}"
        s += f'\nabbrev test{t} (code : Nat) : Prop := {equation}\n'
        s += f'def check{t} (code : Nat) : Bool := decide (test{t} code → ¬ pattern code)\n'
    s += f'\nend DefOrbit.Native{ns}\n'
    return chunk_array_literals(s) if d.get('native_large_literals') else s


def integrate_native(d, ns, s):
    sizes, places, left, right = dimensions(d)
    n, m, q = d['order'], len(sizes), len(d['probes'])
    native = f'DefOrbit.Native{ns}'
    index = f'Fin {left} × Fin {right}'
    code = f'i.2.val + {right} * i.1.val'
    # NativeOrbit already imports the cached-image and finite-product lemmas.
    s = s.replace('import equational_theories.Definability.CachedWordImages\n'
                  'import Mathlib.Algebra.BigOperators.Fin\n',
                  f'import DefOrbit.Generated.Native{ns}\n'
                  'import equational_theories.Definability.NativeOrbit\n')
    bridge = f'''def places : Fin {m} → ℕ := ![{', '.join(map(str, places))}]
private theorem sizes_pos : ∀ j, 0 < sizes j := by native_decide
private theorem places_correct : ∀ j : Fin {m},
    places j = ∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k) := by native_decide
def decodeNative (i : {index}) : Params := fun j =>
  ⟨(({code}) / places j) % sizes j, Nat.mod_lt _ (sizes_pos j)⟩
private theorem decodeNative_eq (i : {index}) : decodeNative i = paramEquiv.symm i := by
  funext j
  apply Fin.ext
  change (({code}) / places j) % sizes j =
    (({code}) / (∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k))) % sizes j
  rw [places_correct]
private theorem native_orbit_correct : ∀ x y : Fin {n},
    {native}.orbitData.getD (x.val * {n} + y.val) 0 = (tr x y).1.val := by native_decide
private theorem native_places_correct : ∀ j : Fin {m},
    {native}.placesData.getD j.val 0 = places j := by native_decide
private theorem native_sizes_correct : ∀ j : Fin {m},
    {native}.sizesData.getD j.val 0 = sizes j := by native_decide
private theorem native_cell_correct : ∀ (x y : Fin {n}) (v : Fin (sizes (tr x y).1)),
    ({native}.cellData.getD (x.val * {n} + y.val) #[]).getD v.val 0 =
      image (tr x y).2 (values (tr x y).1 v) := by native_decide
private theorem native_op_correct (i : {index}) (x y : Fin {n}) :
    {native}.op ({code}) x y = (fam (paramEquiv.symm i)).op x y := by
  rw [← decodeNative_eq]
  unfold {native}.op
  dsimp only
  rw [native_orbit_correct, native_places_correct, native_sizes_correct]
  exact native_cell_correct x y (decodeNative i (tr x y).1)
private theorem native_probe_correct : ∀ i : Fin {q}, ∀ x : Fin {n},
    {native}.probe i x = probePerm i x := by native_decide
private theorem native_pattern_correct (i : {index}) :
    {native}.pattern ({code}) ↔ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by
  unfold {native}.pattern Pattern pattern
  simp only [native_op_correct, native_probe_correct, Magma.IsEndo]
  simp

'''
    first = targets(d)[0]
    s = s.replace(f'private abbrev test{first}', bridge + f'private abbrev test{first}', 1)
    for t in targets(d):
        replacement = f'''private theorem native_test{t}_correct (i : {index}) :
    {native}.test{t} ({code}) ↔ test{t} (paramEquiv.symm i) := by
  unfold {native}.test{t} test{t}
  simp only [native_op_correct]
private theorem native_checked{t} : DefOrbit.allBelow {native}.check{t} {left * right} = true := by
  native_decide
private theorem restricted{t} : ∀ p : Params, test{t} p → ¬ Pattern (fam p) probePerm pattern := by
  have h : ∀ i : {index}, test{t} (paramEquiv.symm i) →
      ¬ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by
    intro i
    have hi : {code} < {left * right} := by omega
    have hc := (DefOrbit.allBelow_spec _ _).mp native_checked{t} _ hi
    have ht := of_decide_eq_true hc
    change {native}.test{t} ({code}) → ¬ {native}.pattern ({code}) at ht
    simpa only [native_test{t}_correct, native_pattern_correct] using ht
  intro p
  simpa only [Equiv.symm_apply_apply] using h (paramEquiv p)
'''
        s, count = re.subn(rf'private theorem restricted{t} :.*?(?=theorem target{t})',
                           lambda _: replacement, s, count=1, flags=re.S)
        assert count == 1
    return s
