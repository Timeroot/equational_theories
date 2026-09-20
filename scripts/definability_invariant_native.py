"""Compiled evaluation for complete invariant-family model counts."""

import re
from definability_orbit_native import dimensions, integrate_native, render_native, arr
from spectrum_generate import load_equations, variables


def laws(d):
    return {
        e[key]: e[key + "_count"]
        for e in d["candidates"]
        for key in ["source", "target"]
    }


def points(d):
    assert d.get("orbit_representative_test")
    diagonal = sorted({d["transport"][x][x][0] for x in range(d["order"])})
    return [d["representatives"][i][0] for i in diagonal]


def render_native_counts(d):
    ns, n = d["namespace"], d["order"]
    ps = points(d)
    s = render_native(d, ns).split("abbrev pattern")[0]
    s = s.replace("import DefOrbit", "import DefOrbit.Counting")
    from definability_orbit_certificates_check import render as orbit_render

    raw = orbit_render(d, ns).split("theorem source_generators")[0]
    for name, decl in re.findall(
        r"^(def (\w+Data) : Array[^\n]*:= #\[[^\n]*\n)", raw, re.M
    ):
        if not re.search(r"^def " + decl + r" :", s, re.M):
            s += name
    s += f"def pointData : Array (Fin {n}) := {arr(ps)}\n"
    s += f"def point (i : Fin {len(ps)}) : Fin {n} := pointData.getD i.val 0\n"
    for law in sorted(laws(d)):
        a, b = load_equations()[law - 1]
        k = max("xyzuvw".index(v) for v in variables(a) | variables(b))

        def expression(term):
            if isinstance(term, str):
                index = "xyzuvw".index(term)
                return "(point i)" if index == 0 else f"v{index - 1}"
            return f"(op code {expression(term[0])} {expression(term[1])})"

        binders = " ".join(f"v{j}" for j in range(k))
        quantifier = f"∀ {binders} : Fin {n}," if k else ""
        s += f"\nabbrev test{law} (code : Nat) : Prop := ∀ i : Fin {len(ps)}, {quantifier}\n  {expression(a)} = {expression(b)}\n"
        body = f"decide ({expression(a)} = {expression(b)})"
        for j in reversed(range(k)):
            body = f"(List.finRange {n}).all (fun v{j} => {body})"
        body = f"(List.finRange {len(ps)}).all (fun i => {body})"
        s += f"def good{law} (code : Nat) : Bool := {body}\n"
    s += f"\nend DefOrbit.Native{ns}\n"
    if d.get("native_large_literals"):
        from definability_orbit_native import chunk_array_literals

        s = chunk_array_literals(s)
    return s


def integrate_native_counts(d, s):
    from definability_orbit_certificates_check import render as orbit_render

    ns, n = d["namespace"], d["order"]
    native = f"DefOrbit.Native{ns}"
    _, _, left, right = dimensions(d)
    index, code = f"Fin {left} × Fin {right}", f"i.2.val + {right} * i.1.val"
    # Reuse the same checked mixed-radix decoder and operation bridge.
    bridge = integrate_native(d, ns, orbit_render(d, ns))
    bridge = bridge[
        bridge.index("def places :") : bridge.index(
            "private theorem native_probe_correct"
        )
    ]
    bridge = bridge.replace(
        "image (tr x y).2 (values (tr x y).1 v) := by native_decide",
        "wordPerm genPerm (words (tr x y).2) (values (tr x y).1 v) := by native_decide",
    )
    bridge = bridge.replace(
        "exact native_cell_correct x y (decodeNative i (tr x y).1)",
        "exact (native_cell_correct x y (decodeNative i (tr x y).1)).trans (image_correct _ _).symm",
    )
    s = (
        f"import DefOrbit.Generated.Native{ns}\nimport equational_theories.Definability.NativeOrbitCounting\n"
        + s
    )
    s = re.sub(
        r"^(def (\w+Data) : Array[^\n]*:= )#\[[^\n]*",
        lambda m: m[1] + native + "." + m[2],
        s,
        flags=re.M,
    )
    first = min(laws(d))
    bridge += f"""private theorem native_point_correct : ∀ i : Fin {len(points(d))},
    {native}.point i = points i := by native_decide

"""
    s = s.replace(f"private def law{first}", bridge + f"private def law{first}", 1)
    tuple_rules = "Fin.cons_zero"
    finish = "\n  rfl"
    if d.get("simplify_test_tuples"):
        max_arity = max(
            max("xyzuvw".index(v) for v in variables(a) | variables(b)) + 1
            for law in laws(d)
            for a, b in [load_equations()[law - 1]]
        )
        tuple_rules += ", Fin.cons_one"
        helpers = ""
        for size in range(3, max_arity + 1):
            for index_value in range(2, size):
                name = f"native_cons{size}_{index_value}"
                helpers += (
                    f"private theorem {name} {{A : Type}} (a : A) "
                    f"(p : Fin {size - 1} → A) :\n"
                    f"    (Fin.cons a p : Fin {size} → A) {index_value} = "
                    f"p {index_value - 1} := by rfl\n\n"
                )
                tuple_rules += ", " + name
        s = s.replace(f"private def law{first}", helpers + f"private def law{first}", 1)
        finish = ""
    for law, count in sorted(laws(d).items()):
        # Explicit tuple lookup prevents definitional equality from expanding
        # the entire orbit family while comparing a variable assignment.
        replacement = f"""private theorem native_good{law}_correct (code : Nat) :
    {native}.good{law} code = true ↔ {native}.test{law} code := by
  simp [{native}.good{law}, {native}.test{law}, List.all_eq_true]
private theorem native_test{law}_correct (i : {index}) :
    {native}.test{law} ({code}) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law{law} := by
  unfold {native}.test{law} Magma.InvariantFamily.OrbitTest
    Magma.InvariantFamily.PointTest law{law}
  simp only [native_op_correct, native_point_correct, FreeMagma.evalInMagma,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, {tuple_rules}]{finish}
private theorem native_count{law} :
    DefOrbit.countBelow {native}.good{law} {left * right} = {count} := by native_decide
private theorem count{law} : Fintype.card {{p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law{law}}} = {count} := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := {left}) (n := {right})))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law{law}) {native}.good{law}]
  · exact native_count{law}
  · intro p
    have h := (native_test{law}_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good{law}_correct] using h

"""
        s, matches = re.subn(
            rf"private theorem count{law} :.*?(?=\n\n)",
            lambda _: replacement.rstrip(),
            s,
            count=1,
            flags=re.S,
        )
        assert matches == 1
    if d.get("abstract_count_bridges"):
        s = abstract_count_bridges(d, s)
    return s


# Keep concrete tables out of kernel conversion checks: prove both bridges
# with arbitrary operations and orbit charts, then instantiate the proofs.
def abstract_count_bridges(d, s):
    assert d.get(
        "simplify_test_tuples"
    ), "Abstract bridges require explicit tuple simplification"
    ns, n = d["namespace"], d["order"]
    native = "DefOrbit.Native" + ns
    from definability_orbit_native import dimensions

    _, _, left, right = dimensions(d)
    code = f"i.2.val + {right} * i.1.val"
    max_arity = max(
        max("xyzuvw".index(v) for v in variables(a) | variables(b)) + 1
        for law in laws(d)
        for a, b in [load_equations()[law - 1]]
    )
    rules = "Fin.cons_zero, Fin.cons_one" + "".join(
        f", native_cons{size}_{j}"
        for size in range(3, max_arity + 1)
        for j in range(2, size)
    )
    for law in sorted(laws(d)):
        a, b = load_equations()[law - 1]
        k = max("xyzuvw".index(v) for v in variables(a) | variables(b))

        def expr(t):
            if isinstance(t, str):
                i = "xyzuvw".index(t)
                return "(ps i)" if i == 0 else f"v{i-1}"
            return f"(M.op {expr(t[0])} {expr(t[1])})"

        binders = " ".join(f"v{j}" for j in range(k))
        quantifier = f"∀ {binders} : Fin {n}," if k else ""
        proof = f"""private theorem abstract_test{law} (M : Magma (Fin {n})) (ps : Fin {len(points(d))} → Fin {n}) :
    (∀ i : Fin {len(points(d))}, {quantifier} {expr(a)} = {expr(b)}) ↔
      Magma.InvariantFamily.OrbitTest ps M law{law} := by
  simp only [Magma.InvariantFamily.OrbitTest, Magma.InvariantFamily.PointTest, law{law},
    FreeMagma.evalInMagma, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, {rules}]
private theorem native_test{law}_correct (i : Fin {left} × Fin {right}) :
    {native}.test{law} ({code}) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law{law} := by
  have hp : {native}.point = points := funext native_point_correct
  have hm : (⟨{native}.op ({code})⟩ : Magma (Fin {n})) = fam (paramEquiv.symm i) :=
    congrArg Magma.mk (funext fun x => funext fun y => native_op_correct i x y)
  have h := abstract_test{law} (⟨{native}.op ({code})⟩ : Magma (Fin {n})) {native}.point
  apply h.trans
  rw [hp, hm]
"""
        s, m = re.subn(
            rf"private theorem native_test{law}_correct.*?(?=private theorem native_count{law})",
            lambda _: proof,
            s,
            flags=re.S,
        )
        assert m == 1
    op_rep_proof = """private theorem abstract_op_rep {n g k m : Nat}
    (generators : Fin g → Equiv.Perm (Fin n)) (words : Fin k → List (Fin g))
    (rep : Fin m → Fin n × Fin n) (tr : Fin n → Fin n → Fin m × Fin k)
    (sizes : Fin m → Nat) (values : (i : Fin m) → Fin (sizes i) → Fin n)
    (zero : Fin k) (tr_rep : ∀ i, tr (rep i).1 (rep i).2 = (i, zero))
    (words_zero : words zero = []) (p : (i : Fin m) → Fin (sizes i)) (i : Fin m) :
    (family generators words tr sizes values p).op (rep i).1 (rep i).2 = values i (p i) := by
  change wordPerm generators (words (tr (rep i).1 (rep i).2).2)
    (values (tr (rep i).1 (rep i).2).1 (p (tr (rep i).1 (rep i).2).1)) = _
  rw [tr_rep]
  change wordPerm generators (words zero) (values i (p i)) = _
  rw [words_zero]
  rfl

theorem op_rep (p : Params) (i) : (fam p).op (rep i).1 (rep i).2 = values i (p i) := by
  have hf := congrArg (fun M : Magma (Fin ORDER) => M.op (rep i).1 (rep i).2) (fam_eq_family p)
  exact hf.trans (abstract_op_rep genPerm words rep tr sizes values 0 tr_rep words_zero p i)
""".replace(
        "ORDER", str(n)
    )
    s, matches = re.subn(
        r"theorem op_rep .*?(?=\ntheorem family_injective)",
        lambda _: op_rep_proof,
        s,
        flags=re.S,
    )
    assert matches == 1
    return s
