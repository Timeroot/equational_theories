"""Compiled counts for cyclic projection/kernel families, with Lean bridges."""
import re
from definability_orbit_native import arr, matrix
from spectrum_generate import load_equations, variables


def laws(d):
    return {e[key]: e[key + '_count'] for e in d['candidates']
            for key in ['source', 'target']}


def render_native(d):
    ns, a, b = d['namespace'], d['base_modulus'], d['kernel_modulus']
    k = len(d['kernel_functions'])
    assert a > 0 and b > 0 and k > 0
    s = f'''import DefOrbit.Counting

/-! Compiled evaluator for a complete cyclic projection/kernel family. -/
namespace DefOrbit.Native{ns}
abbrev Point := Fin {a} × Fin {b}
def gPlaces : Array Nat := {arr(a**i for i in range(a))}
def hPlaces : Array Nat := {arr(k**i for i in range(a))}
def g (code : Nat) (x : Fin {a}) : Fin {a} :=
  ⟨(code / gPlaces.getD x.val 0) % {a}, Nat.mod_lt _ (by decide)⟩
def h (code : Nat) (x : Fin {a}) : Fin {k} :=
  ⟨(code / hPlaces.getD x.val 0) % {k}, Nat.mod_lt _ (by decide)⟩
def valueData : Array (Array (Fin {b})) := {matrix(d['kernel_functions'])}
def value (i : Fin {k}) (x : Fin {b}) : Fin {b} :=
  (valueData.getD i.val #[]).getD x.val 0
def op (gc hc : Nat) (x y : Point) : Point :=
  (x.1 + g gc (y.1 - x.1), x.2 + value (h hc (y.1 - x.1)) (y.2 - x.2))
def points : List Point :=
  (List.finRange {a}).flatMap fun x => (List.finRange {b}).map fun y => (x, y)
'''
    for law in sorted(laws(d)):
        l, r = load_equations()[law-1]
        nv = max('xyzuvw'.index(v) for v in variables(l) | variables(r))
        def expr(t):
            if isinstance(t, str):
                i = 'xyzuvw'.index(t)
                return '(0, 0)' if i == 0 else f'v{i-1}'
            return f'(op gc hc {expr(t[0])} {expr(t[1])})'
        body = f'{expr(l)} = {expr(r)}'
        binders = ' '.join(f'v{i}' for i in range(nv))
        quantifier = f'∀ {binders} : Point, ' if nv else ''
        s += f'\nabbrev test{law} (gc hc : Nat) : Prop := {quantifier}{body}\n'
        boolean = f'decide ({body})'
        for i in reversed(range(nv)):
            boolean = f'points.all (fun v{i} => {boolean})'
        s += f'def good{law} (code : Nat) : Bool :=\n  let gc := code % {a**a}\n  let hc := code / {a**a}\n  {boolean}\n'
    return s + f'\nend DefOrbit.Native{ns}\n'


def integrate(d, s):
    ns, a, b = d['namespace'], d['base_modulus'], d['kernel_modulus']
    k = len(d['kernel_functions']); ng, nh = a**a, k**a
    native = f'DefOrbit.Native{ns}'
    s = f'import DefOrbit.Generated.Native{ns}\nimport equational_theories.Definability.NativeOrbitCounting\n' + s
    bridge = f'''def paramEquiv : Params ≃ (Fin {ng} × Fin {nh}) :=
  Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv
def codeEquiv : Params ≃ Fin {ng * nh} :=
  paramEquiv.trans ((Equiv.prodComm _ _).trans (finProdFinEquiv (m := {nh}) (n := {ng})))
private theorem native_g_correct : ∀ (i : Fin {ng}) (x : A),
    {native}.g i.val x = finFunctionFinEquiv.symm i x := by native_decide
private theorem native_h_correct : ∀ (i : Fin {nh}) (x : A),
    {native}.h i.val x = finFunctionFinEquiv.symm i x := by native_decide
private theorem native_value_correct : ∀ (i : K) (x : B),
    {native}.value i x = values i x := by native_decide
private theorem native_op_correct (i : Fin {ng} × Fin {nh}) (x y : A × B) :
    {native}.op i.1.val i.2.val x y = (model (paramEquiv.symm i)).op x y := by
  simp only [{native}.op, native_g_correct, native_h_correct, native_value_correct]
  rfl
private theorem native_code_mod (i : Fin {ng} × Fin {nh}) :
    (i.1.val + {ng} * i.2.val) % {ng} = i.1.val := by omega
private theorem native_code_div (i : Fin {ng} × Fin {nh}) :
    (i.1.val + {ng} * i.2.val) / {ng} = i.2.val := by omega

'''
    first = min(laws(d));s = s.replace(f'private def law{first}', bridge + f'private def law{first}', 1)
    for law, count in sorted(laws(d).items()):
        replacement = f'''private theorem native_good{law}_correct (code : Nat) :
    {native}.good{law} code = true ↔ {native}.test{law} (code % {ng}) (code / {ng}) := by
  simp [{native}.good{law}, {native}.test{law}, {native}.points, List.all_eq_true, Prod.forall]
private theorem native_test{law}_correct (i : Fin {ng} × Fin {nh}) :
    {native}.test{law} i.1.val i.2.val ↔ ZeroTest (model (paramEquiv.symm i)) law{law} := by
  unfold {native}.test{law} ZeroTest law{law}
  simp only [native_op_correct, FreeMagma.evalInMagma, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi, Fin.cons_zero]
  rfl
private theorem native_count{law} :
    DefOrbit.countBelow {native}.good{law} {ng * nh} = {count} := by native_decide
private theorem count{law} : Fintype.card {{p : Params // ZeroTest (model p) law{law}}} = {count} := by
  rw [DefOrbit.card_eq_countBelow codeEquiv
    (fun p => ZeroTest (model p) law{law}) {native}.good{law}]
  · exact native_count{law}
  · intro p
    change ZeroTest (model p) law{law} ↔
      {native}.good{law} ((paramEquiv p).1.val + {ng} * (paramEquiv p).2.val) = true
    rw [native_good{law}_correct, native_code_mod, native_code_div]
    simpa only [Equiv.symm_apply_apply] using (native_test{law}_correct (paramEquiv p)).symm

'''
        s, count = re.subn(rf'private theorem count{law} :.*?(?=\n\n)', lambda _: replacement.rstrip(), s, count=1, flags=re.S)
        assert count == 1
    return s
