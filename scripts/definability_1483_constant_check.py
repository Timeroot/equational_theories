#!/usr/bin/env python3
"""Replay the saved E1483 constant-row equational proofs into ordinary Lean.

Each rewrite is matched against its cited equality and lifted through one
explicit context by congrArg. Lean checks the resulting certificates without
trusting this generator or the prover. Run --write to refresh the generated
block; the default checks exact reproduction and preserves the hand-written
cardinality corollaries.
"""
import argparse
import re
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def parse(s):
    ts = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[(),]", s)
    i = 0

    def p():
        nonlocal i
        v = ts[i]
        i += 1
        if v != "f":
            return v
        assert ts[i] == "("
        i += 1
        a = p()
        assert ts[i] == ","
        i += 1
        b = p()
        assert ts[i] == ")"
        i += 1
        return (a, b)

    t = p()
    assert i == len(ts), (s, ts[i:])
    return t


def variables(t):
    if isinstance(t, str):
        return {t} if t[0].isupper() else set()
    return variables(t[0]) | variables(t[1])


def match(p, t, env):
    if isinstance(p, str) and p[0].isupper():
        if p in env:
            return env[p] == t
        env[p] = t
        return True
    if isinstance(p, str):
        return p == t
    return not isinstance(t, str) and match(p[0], t[0], env) and match(p[1], t[1], env)


def paths(t):
    yield ()
    if not isinstance(t, str):
        for i in range(2):
            for p in paths(t[i]):
                yield (i,) + p


def sub(t, path):
    for i in path:
        t = t[i]
    return t


def replace(t, path, val):
    if not path:
        return val
    a = list(t)
    a[path[0]] = replace(a[path[0]], path[1:], val)
    return tuple(a)


def render(t, bound):
    if isinstance(t, str):
        return "v_" + t if t in bound else ("zero" if t[0].isupper() else t)
    return f"({render(t[0],bound)} ◇ {render(t[1],bound)})"


def sections(text):
    lines = text.splitlines()
    i = 0
    out = []
    while i < len(lines):
        m = re.match(r"(Axiom|Lemma|Goal) (\d+)(?: \([^)]*\))?: (.*)\.$", lines[i])
        if not m:
            i += 1
            continue
        kind, num, eq = m.groups()
        l, r = eq.split(" = ")
        item = {
            "kind": kind.lower(),
            "num": int(num),
            "lhs": parse(l),
            "rhs": parse(r),
            "steps": [],
        }
        i += 1
        if i < len(lines) and lines[i] == "Proof:":
            i += 1
            item["initial"] = parse(lines[i].strip())
            i += 1
            while i < len(lines) and lines[i].startswith("= {"):
                m = re.match(
                    r"= \{ by (axiom|lemma) (\d+)(?: \([^)]*\))?( R->L)? \}", lines[i]
                )
                assert m, lines[i]
                k, no, rev = m.groups()
                i += 1
                item["steps"].append((k, int(no), bool(rev), parse(lines[i].strip())))
                i += 1
        out.append(item)
    return out


def generate(name, text):
    blocks = sections(text)
    axioms = [b for b in blocks if b["kind"] == "axiom"]
    goal = [b for b in blocks if b["kind"] == "goal"][0]
    extras = []
    if name == "odd":
        extras = ["(hfixed : one ◇ (one ◇ (one ◇ x)) = x)"]
    if name == "idem":
        extras = ["(hidem : x ◇ x = x)", "(hfixed : one ◇ (one ◇ x) = x)"]
    title = {
        "six": "left_six",
        "auto": "left_square_hom",
        "odd": "left_cube_fixed",
        "idem": "idempotent_left_square_fixed",
    }[name]
    params = "(x y : G)" if name == "auto" else "(x : G)"
    out = [
        f"theorem {title} (h : Equation1483 G) (zero one : G)",
        f"    (hzero : ∀ t : G, zero ◇ t = one) {params} " + " ".join(extras) + " :",
        f'    {render(goal["lhs"],set())} = {render(goal["rhs"],set())} := by',
        "  have dual (a b c : G) : ((c ◇ b) ◇ a) ◇ (a ◇ b) = a := by",
        "    calc",
        "      ((c ◇ b) ◇ a) ◇ (a ◇ b) =",
        "          ((c ◇ b) ◇ a) ◇ (a ◇ ((c ◇ b) ◇ (b ◇ (c ◇ b)))) :=",
        "        congrArg (fun t => ((c ◇ b) ◇ a) ◇ (a ◇ t)) (h b c b)",
        "      _ = a := (h a (c ◇ b) (b ◇ (c ◇ b))).symm",
    ]
    known = {}
    for b in blocks:
        key = (b["kind"], b["num"])
        bound = sorted(variables(b["lhs"]) | variables(b["rhs"]))
        b["bound"] = bound
        known[key] = b
        nm = f'{b["kind"]}_{b["num"]}'
        if b["kind"] == "axiom":
            out.append(
                f"  have {nm} "
                + ("(" + " ".join("v_" + v for v in bound) + " : G) " if bound else "")
                + f': {render(b["lhs"],bound)} = {render(b["rhs"],bound)} := by'
            )
            if b["lhs"] == ("zero", "X"):
                proof = "exact hzero v_X"
            elif b["lhs"] == (("X", "Y"), ("Y", ("X", "Z"))):
                proof = "exact (h v_Y v_X v_Z).symm"
            elif b["lhs"] == ((("X", "Y"), "Z"), ("Z", "Y")):
                proof = "exact dual v_Z v_Y v_X"
            elif b["lhs"] == ("x", "x"):
                proof = "exact hidem"
            else:
                proof = "exact hfixed"
            out.append("    " + proof)
            continue
        if b["kind"] == "lemma":
            out.append(
                f"  have {nm} "
                + ("(" + " ".join("v_" + v for v in bound) + " : G) " if bound else "")
                + f': {render(b["lhs"],bound)} = {render(b["rhs"],bound)} := by'
            )
            indent = "    "
        else:
            indent = "  "
        assert b["initial"] == b["lhs"]
        out.append(indent + "calc")
        prev = b["initial"]
        for j, (kind, no, rev, nxt) in enumerate(b["steps"]):
            lemma = known[kind, no]
            l, r = (lemma["rhs"], lemma["lhs"]) if rev else (lemma["lhs"], lemma["rhs"])
            found = None
            for path in paths(prev):
                try:
                    pt, nt = sub(prev, path), sub(nxt, path)
                except (IndexError, TypeError):
                    continue
                env = {}
                if (
                    match(l, pt, env)
                    and match(r, nt, env)
                    and replace(prev, path, nt) == nxt
                ):
                    found = path, env
                    break
            assert found, (name, nm, j, kind, no)
            path, env = found
            app = f"{kind}_{no}" + "".join(
                " " + render(env.get(v, "zero"), bound) for v in lemma["bound"]
            )
            app = "(" + app + ")" + (".symm" if rev else "")
            if path:
                app = f'congrArg (fun hole : G => {render(replace(prev,path,"hole"),bound)}) {app}'
            out.append(
                indent
                + "  "
                + (render(prev, bound) if j == 0 else "_")
                + " = "
                + render(nxt, bound)
                + " := "
                + app
            )
            prev = nxt
        assert prev == b["rhs"]
    out += [
        "",
        f"/-- info: 'CentralConstant.{title}' does not depend on any axioms -/",
        "#guard_msgs in",
        f"#print axioms {title}",
        "",
    ]
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    proofs = json.loads(
        (ROOT / "data/definability_1483_constant_proofs.json").read_text()
    )
    assert set(proofs) == {"six", "auto", "odd", "idem"}
    generated = (
        "\n".join(
            generate(name, proofs[name]) for name in ("six", "auto", "odd", "idem")
        )
        + "\n"
    )
    path = ROOT / "equational_theories/Definability/Central1483Constant.lean"
    text = path.read_text()
    start = "/- BEGIN REPLAYED PROOFS -/\n"
    end = "/- END REPLAYED PROOFS -/\n"
    before, rest = text.split(start, 1)
    current, after = rest.split(end, 1)
    if args.write:
        path.write_text(before + start + generated + end + after)
    else:
        assert current == generated, "generated proof block differs; run --write"
    print(
        "Four equational proofs replayed; generated Lean block matches."
        if not args.write
        else "Generated Lean proof block updated."
    )


if __name__ == "__main__":
    main()
