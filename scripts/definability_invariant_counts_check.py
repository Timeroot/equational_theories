#!/usr/bin/env python3
"""Verify complete invariant families, normalized law counts, and their Lean certificates."""
import argparse
import itertools
import json
from pathlib import Path
import numpy as np
from spectrum_generate import load_equations, variables
from definability_orbit_certificates_check import render as orbit_render
from definability_ring_counts_check import term

ROOT = Path(__file__).resolve().parents[1]
E = load_equations()


def render(d):
    q = d["order"]
    ns = d["namespace"]
    s = (
        orbit_render(d, ns)
        .split("theorem source_generators")[0]
        .replace(
            "import equational_theories.Definability.FiniteSymmetry",
            "import equational_theories.Definability.InvariantFamilyCounting\nimport Mathlib.Data.ZMod.Basic",
        )
        .replace(
            "import equational_theories.Definability.CachedWordImages",
            "import equational_theories.Definability.CachedWordImages\n"
            "import equational_theories.Definability.InvariantFamilyCounting\n"
            "import Mathlib.Data.ZMod.Basic",
        )
    )
    s += f"local instance : AddCommGroup (Fin {q}) := inferInstanceAs (AddCommGroup (ZMod {q}))\n\n"
    s += """theorem same_orbit : ∀ i x y, (tr (genPerm i x) (genPerm i y)).1 = (tr x y).1 := by native_decide
theorem coherent_values : ∀ i x y a,
    genPerm i (wordPerm genPerm (words (tr x y).2) (values (tr x y).1 a)) =
    wordPerm genPerm (words (tr (genPerm i x) (genPerm i y)).2) (values (tr x y).1 a) := by native_decide

theorem family_generators : ∀ p i, (fam p).IsEndo (genPerm i) :=
  Magma.InvariantFamily.family_endos genPerm words tr sizes values same_orbit coherent_values

theorem tr_rep : ∀ i, tr (rep i).1 (rep i).2 = (i, 0) := by native_decide
theorem words_zero : words 0 = [] := by native_decide
theorem values_injective : ∀ i, Function.Injective (values i) := by native_decide

theorem op_rep (p : Params) (i) : (fam p).op (rep i).1 (rep i).2 = values i (p i) := by
  change wordPerm genPerm (words (tr (rep i).1 (rep i).2).2)
    (values (tr (rep i).1 (rep i).2).1 (p (tr (rep i).1 (rep i).2).1)) = _
  rw [tr_rep]
  change wordPerm genPerm (words 0) (values i (p i)) = _
  rw [words_zero]
  rfl

theorem family_injective : Function.Injective (fun p : Params => (fam p).op) := by
  intro p q hpq
  funext i
  apply values_injective i
  rw [← op_rep p i, ← op_rep q i]
  exact congrFun (congrFun hpq (rep i).1) (rep i).2

theorem translation_words : ∀ a x,
    wordPerm genPerm (List.replicate a.val 0) x = a+x := by native_decide

theorem translations (p : Params) (a) : (fam p).IsEndo (fun x => a+x) := by
  have h := word_endo (fam p) genPerm (family_generators p) (List.replicate a.val 0)
  have he : (wordPerm genPerm (List.replicate a.val 0) : _ → _) = (fun x => a+x) :=
    funext (translation_words a)
  rw [he] at h
  exact h

"""
    counts = {
        e[key]: e[key + "_count"]
        for e in d["candidates"]
        for key in ["source", "target"]
    }
    for law in sorted(counts):
        l, r = E[law - 1]
        k = 1 + max("xyzuvw".index(v) for v in variables(l) | variables(r))
        s += f"""private def law{law} : MagmaLaw (Fin {k}) := ⟨{term(l)}, {term(r)}⟩
private theorem count{law} : Fintype.card {{p : Params // Magma.InvariantFamily.ZeroTest (fam p) law{law}}} = {counts[law]} := by native_decide

"""
        if d.get("indexed_parameters"):
            s = s.replace(
                f"= {counts[law]} := by native_decide\n\n",
                f"= {counts[law]} := by\n"
                "  rw [Fintype.card_congr (paramEquiv.subtypeEquivOfSubtype' "
                f"(p := fun p => Magma.InvariantFamily.ZeroTest (fam p) law{law}))]\n"
                "  native_decide\n\n",
            )
    s += f"end Magma.{ns}\n\nopen Magma.{ns} Magma.InvariantFamily\n\n"
    for e in d["candidates"]:
        a, t = e["source"], e["target"]
        k = 1 + max("xyzuvw".index(v) for term0 in E[t - 1] for v in variables(term0))
        name = f"Equation{t}_not_termStructuralFromFin_Equation{a}_invariantFamilyCount"
        s += f"""theorem {name} : ¬ Law{t}.TermStructuralFromFin Law{a} := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => ZeroTest (fam p) law{a}) (fun p => ZeroTest (fam p) law{t})
  · intro p hp φ
    exact (zeroTest_iff_satisfies (fam p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (fam p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat {k} i))
  · rw [count{a}, count{t}]
    decide

#print axioms {name}

"""
    if d.get("orbit_representative_test"):
        assert not d.get("transitive_point_test")
        diagonal_orbits = sorted({d["transport"][x][x][0] for x in range(q)})
        assert all(d["representatives"][i][0] == d["representatives"][i][1] for i in diagonal_orbits)
        points = [d["representatives"][i][0] for i in diagonal_orbits]
        indices = [diagonal_orbits.index(d["transport"][x][x][0]) for x in range(q)]
        s = s.replace(
            "import equational_theories.Definability.InvariantFamilyCounting",
            "import equational_theories.Definability.OrbitInvariantCounting",
        ).replace(
            f"local instance : AddCommGroup (Fin {q}) := inferInstanceAs (AddCommGroup (ZMod {q}))\n\n",
            "",
        )
        start = s.index("theorem translation_words")
        end = s.index("private def law", start)
        s = s[:start] + f"""def points : Fin {len(points)} → Fin {q} := ![{', '.join(map(str, points))}]
def point_index : Fin {q} → Fin {len(points)} := ![{', '.join(map(str, indices))}]

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

""" + s[end:]
        if d.get("compact_point_index"):
            # Consecutive points often share a representative.  A short chain
            # of bounds avoids a long dependent Fin.cons term in kernel checks.
            runs = []
            for i, value in enumerate(indices):
                if not runs or runs[-1][1] != value:
                    runs.append([i + 1, value])
                else:
                    runs[-1][0] = i + 1
            expression = str(runs[-1][1])
            for stop, value in reversed(runs[:-1]):
                expression = f"if x.val < {stop} then {value} else {expression}"
            s = s.replace(
                f"def point_index : Fin {q} → Fin {len(points)} := ![{', '.join(map(str, indices))}]",
                f"def point_index (x : Fin {q}) : Fin {len(points)} := {expression}",
            )
        s = s.replace("ZeroTest (fam p)", "OrbitTest points (fam p)")
        s = s.replace(
            "zeroTest_iff_satisfies (fam p) (translations p) _",
            "orbitTest_iff_satisfies points (fam p) point_index "
            "(fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _",
        )
    elif d.get("full_assignment_test"):
        assert not d.get("transitive_point_test")
        s = s.replace(
            f"local instance : AddCommGroup (Fin {q}) := inferInstanceAs (AddCommGroup (ZMod {q}))\n\n",
            "",
        )
        start = s.index("theorem translation_words")
        end = s.index("private def law", start)
        s = s[:start] + f"""private def fullTest {{k : ℕ}} (M : Magma (Fin {q}))
    (L : MagmaLaw (Fin k)) : Prop :=
  ∀ φ : Fin k → Fin {q}, @FreeMagma.evalInMagma _ _ M φ L.lhs =
    @FreeMagma.evalInMagma _ _ M φ L.rhs

private instance {{k : ℕ}} (M : Magma (Fin {q})) (L : MagmaLaw (Fin k)) :
    Decidable (fullTest M L) := by unfold fullTest; infer_instance

""" + s[end:]
        s = s.replace("Magma.InvariantFamily.ZeroTest (fam p)", "fullTest (fam p)")
        s = s.replace("ZeroTest (fam p)", "fullTest (fam p)")
        s = s.replace(
            "(zeroTest_iff_satisfies (fam p) (translations p) _).mp hp",
            "hp",
        )
        s = s.replace(
            "    apply (zeroTest_iff_satisfies (fam p) (translations p) _).mpr\n",
            "",
        )
    elif d.get("transitive_point_test"):
        s = s.replace(
            "import equational_theories.Definability.InvariantFamilyCounting",
            "import equational_theories.Definability.TransitiveInvariantCounting",
        ).replace(
            f"local instance : AddCommGroup (Fin {q}) := inferInstanceAs (AddCommGroup (ZMod {q}))\n\n",
            "",
        )
        start = s.index("theorem translation_words")
        end = s.index("private def law", start)
        s = (
            s[:start]
            + """theorem point_transitive : ∀ a,
    wordPerm genPerm (words (tr a a).2) 0 = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

"""
            + s[end:]
        )
        s = s.replace("ZeroTest (fam p)", f"PointTest (0 : Fin {q}) (fam p)")
        s = s.replace(
            "zeroTest_iff_satisfies (fam p) (translations p) _",
            "pointTest_iff_satisfies 0 (fam p) "
            "(fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _",
        )
    if d.get("cache_word_images"):
        s = s.replace(
            "theorem family_generators : ∀ p i, (fam p).IsEndo (genPerm i) :=\n"
            "  Magma.InvariantFamily.family_endos",
            "theorem family_generators : ∀ p i, (fam p).IsEndo (genPerm i) := by\n"
            "  intro p\n  rw [fam_eq_family p]\n"
            "  exact Magma.InvariantFamily.family_endos",
        ).replace(
            "  exact Magma.InvariantFamily.family_endos genPerm words tr sizes values same_orbit coherent_values\n",
            "  exact Magma.InvariantFamily.family_endos genPerm words tr sizes values same_orbit coherent_values p\n",
        ).replace(
            "= values i (p i) := by\n  change wordPerm",
            "= values i (p i) := by\n  rw [fam_eq_family p]\n  change wordPerm",
        )
    if d.get("compiled_counts"):
        from definability_invariant_native import integrate_native_counts

        s = integrate_native_counts(d, s)
    inline_axioms = {} if d.get("separate_axiom_guards") else d.get("axioms", {})
    for name, axioms in inline_axioms.items():
        s = s.replace(
            "#print axioms " + name + "\n",
            "/-- info: "
            + axioms
            + " -/\n#guard_msgs (whitespace := lax) in\n#print axioms "
            + name
            + "\n",
        )
    return s


def render_axiom_guards(d):
    """Check imported theorem dependencies without rebuilding a large proof.

    Private names are printed explicitly so their defining module is recorded.
    During initial generation, missing imported messages leave plain print
    commands; a completed certificate must supply every expected message.
    """
    assert d.get("separate_axiom_guards")
    names = d["axioms"]
    assert len(names) == len(d["candidates"])
    s = (
        f"import equational_theories.Definability.Generated.{d['namespace']}\n\n"
        "open Law Law.MagmaLaw Magma.FiniteSymmetry\n"
        f"open Magma.{d['namespace']} Magma.InvariantFamily\n"
        "set_option pp.privateNames true\n\n"
    )
    for name in names:
        expected = d.get("imported_axioms", {}).get(name)
        if expected is not None:
            s += f"/-- info: {expected} -/\n#guard_msgs (whitespace := lax) in\n"
        s += f"#print axioms {name}\n\n"
    return s


def check(d):
    n = d["order"]
    identity = list(range(n))
    gens = d["generators"]
    images = []
    for p, inv in zip(gens, d["generator_inverses"], strict=True):
        assert sorted(p) == sorted(inv) == identity
        assert all(inv[p[x]] == x == p[inv[x]] for x in identity)
    # The shared orbit renderer also emits inverse proofs for these probes,
    # even though counting itself uses only the generators.
    for p, inv in zip(d["probes"], d["probe_inverses"], strict=True):
        assert sorted(p) == sorted(inv) == identity
        assert all(inv[p[x]] == x == p[inv[x]] for x in identity)
    for word in d["words"]:
        p = identity
        for i in reversed(word):
            p = [gens[i][x] for x in p]
        images.append(p)
    for x, y in itertools.product(identity, repeat=2):
        i, w = d["transport"][x][y]
        a, b = d["representatives"][i]
        assert images[w][a] == x and images[w][b] == y
    for i, (a, b) in enumerate(d["representatives"]):
        stabilizers = [images[w] for w in d["stabilizers"][i]]
        assert all(p[a] == a and p[b] == b for p in stabilizers)
        assert {x for x in identity if all(p[x] == x for p in stabilizers)} == set(
            d["values"][i]
        )
        assert d["transport"][a][b] == [i, 0] and images[0] == identity
        assert len(set(d["values"][i])) == len(d["values"][i])
    parameters = np.array(list(itertools.product(*d["values"])), dtype=np.uint16)
    images = np.array(images, dtype=np.uint16)
    transport = np.array(d["transport"])
    orbit, word = transport[:, :, 0], transport[:, :, 1]
    tables = np.empty((len(parameters), n, n), dtype=np.uint16)
    for first in range(0, len(parameters), 1024):
        selected = parameters[first : first + 1024, orbit]
        tables[first : first + len(selected)] = images[word[None], selected]
    assert len(tables) == d["family_count"]
    # A parameter chooses one allowed value independently for each pair orbit.
    # Check the transport formula for every such value at every pair.  This
    # proves equivariance for the whole family without repeating the same
    # comparison once per combination of the other orbit parameters.
    for perm in map(np.array, gens):
        assert np.array_equal(orbit[perm[:, None], perm[None, :]], orbit)
        for x, y in itertools.product(identity, repeat=2):
            values = d["values"][orbit[x, y]]
            assert np.array_equal(
                images[word[perm[x], perm[y]], values],
                perm[images[word[x, y], values]],
            )
    if d.get("orbit_representative_test"):
        assert not d.get("transitive_point_test")
        for x in identity:
            i, w = d["transport"][x][x]
            a, b = d["representatives"][i]
            assert a == b and images[w, a] == x
    elif d.get("full_assignment_test"):
        assert not d.get("transitive_point_test")
    elif d.get("transitive_point_test"):
        for x in identity:
            assert images[d["transport"][x][x][1], 0] == x
    else:
        assert gens[0] == [(x + 1) % n for x in identity]

    def models(law):
        l, r = E[law - 1]
        names = sorted(variables(l) | variables(r))
        rows = (
            list(itertools.product(identity, repeat=len(names)))
            if d.get("full_assignment_test") or d.get("orbit_representative_test")
            else [(0,) + xs for xs in itertools.product(identity, repeat=len(names) - 1)]
        )
        assignments = np.array(rows, dtype=np.uint16).T
        active = np.arange(len(tables))
        for first in range(0, assignments.shape[1], 32):
            if not len(active):
                break
            batch = assignments[:, first : first + 32]
            cache = {v: batch[i][None, :] for i, v in enumerate(names)}
            idx = active[:, None]

            def ev(t):
                if t not in cache:
                    cache[t] = tables[idx, ev(t[0]), ev(t[1])]
                return cache[t]

            active = active[
                np.broadcast_to(ev(l) == ev(r), (len(active), batch.shape[1])).all(
                    axis=1
                )
            ]
        return len(active)

    counts = {
        law: models(law) for e in d["candidates"] for law in [e["source"], e["target"]]
    }
    for e in d["candidates"]:
        for key in ["source", "target"]:
            assert counts[e[key]] == e[key + "_count"]
    print(
        f"{d['namespace']}: independently checked {len(tables)} operations and {len(d['candidates'])} count obstructions.",
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--only", help="check namespaces containing this string")
    args = parser.parse_args()
    for path in sorted((ROOT / "data").glob("definability_invariant_count_*.json")):
        d = json.loads(path.read_text())
        if args.only and args.only not in d["namespace"]:
            continue
        check(d)
        result = render(d)
        output = (
            ROOT
            / "equational_theories/Definability/Generated"
            / f"{d['namespace']}.lean"
        )
        if args.write:
            output.write_text(result)
        else:
            assert output.read_text() == result, f"Regenerate {output} with --write"
        if d.get("separate_axiom_guards"):
            guard_output = output.with_name(d["namespace"] + "Axioms.lean")
            guard_result = render_axiom_guards(d)
            if args.write:
                guard_output.write_text(guard_result)
            else:
                assert set(d.get("imported_axioms", {})) == set(d["axioms"])
                assert guard_output.read_text() == guard_result, (
                    f"Regenerate {guard_output} with --write"
                )
        if d.get("compiled_counts"):
            from definability_invariant_native import render_native_counts

            native_output = (
                ROOT / "defsearch/DefOrbit/Generated"
                / f"Native{d['namespace']}.lean"
            )
            native_result = render_native_counts(d)
            if args.write:
                native_output.parent.mkdir(parents=True, exist_ok=True)
                native_output.write_text(native_result)
            else:
                assert native_output.read_text() == native_result, (
                    f"Regenerate {native_output} with --write"
                )


if __name__ == "__main__":
    main()
