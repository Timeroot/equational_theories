#!/usr/bin/env python3
"""Independently check finite orbit certificates and reproduce their Lean modules."""
import argparse
import itertools
import json
import math
import re
import numpy as np
from definability_counting_upgrades_check import model_indices, preserves
from spectrum_generate import load_equations, variables
from pathlib import Path


def arr(xs):
    return "#[" + ", ".join(map(str, xs)) + "]"


def matrix(xs):
    return arr([arr(row) for row in xs])


def nat_rows(name, rows):
    # Separate declarations bound compiler recursion on the largest certificates.
    return (
        "".join(
            f"def {name}Row{i} : Array ℕ := {arr(row)}\n" for i, row in enumerate(rows)
        )
        + f"def {name} : Array (Array ℕ) := {arr([f'{name}Row{i}' for i in range(len(rows))])}\n"
    )


def _render_raw(d, ns):
    n = d["order"]
    g = len(d["generators"])
    k = len(d["words"])
    m = len(d["representatives"])
    h = len(d["stabilizers"][0])
    q = len(d["probes"])
    library = "CachedWordImages" if d.get("cache_word_images") else "FiniteSymmetry"
    s = f"""import equational_theories.Definability.{library}

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.{ns}

"""
    for key, name, num in [
        ("generators", "gen", g),
        ("generator_inverses", "genInv", g),
        ("probes", "probe", q),
        ("probe_inverses", "probeInv", q),
        ("source", "sourceRow", n),
    ]:
        table = d[key]
        s += f"def {name}Data : Array (Array (Fin {n})) := {matrix(table)}\ndef {name} (i : Fin {num}) (x : Fin {n}) : Fin {n} := ({name}Data.getD i.val #[]).getD x.val 0\n\n"
    for name, num in [("gen", g), ("probe", q)]:
        s += f"theorem {name}_inverse : ∀ i x, {name}Inv i ({name} i x) = x ∧ {name} i ({name}Inv i x) = x := by native_decide\ndef {name}Perm (i : Fin {num}) : Equiv.Perm (Fin {n}) := Magma.permOf ({name} i) ({name}Inv i) ({name}_inverse i)\n\n"
    s += f'def wordsData : Array (List (Fin {g})) := {arr(["["+", ".join(map(str,w))+"]" for w in d["words"]])}\ndef words (i : Fin {k}) : List (Fin {g}) := wordsData.getD i.val []\n'
    s += f'def repData : Array (Fin {n} × Fin {n}) := {arr(["("+", ".join(map(str,r))+")" for r in d["representatives"]])}\ndef rep (i : Fin {m}) := repData.getD i.val (0, 0)\n'
    s += f'def trData : Array (Array (Fin {m} × Fin {k})) := {matrix([["("+", ".join(map(str,r))+")" for r in row] for row in d["transport"]])}\ndef tr (x y : Fin {n}) := (trData.getD x.val #[]).getD y.val (0, 0)\n'
    if d.get("indexed_parameters"):
        radix = len(d["values"][0])
        assert all(len(v) == radix for v in d["values"])
        s = s.replace(
            f"import equational_theories.Definability.{library}\n",
            f"import equational_theories.Definability.{library}\n"
            "import Mathlib.Algebra.BigOperators.Fin\n",
        )
        s += f"abbrev sizes : Fin {m} → ℕ := fun _ => {radix}\n"
    else:
        s += (
            f"def sizes : Fin {m} → ℕ := !["
            + ", ".join(str(len(v)) for v in d["values"])
            + "]\n"
        )
    if d.get("mixed_indexed_parameters"):
        assert not d.get("indexed_parameters")
        s = s.replace(
            f"import equational_theories.Definability.{library}\n",
            f"import equational_theories.Definability.{library}\n"
            "import Mathlib.Algebra.BigOperators.Fin\n",
        )
    s += f'def valuesData : Array (Array (Fin {n})) := {matrix(d["values"])}\ndef values (i : Fin {m}) (j : Fin (sizes i)) : Fin {n} := (valuesData.getD i.val #[]).getD j.val 0\n'
    s += f'def stabilizersData : Array (Array (Fin {k})) := {matrix(d["stabilizers"])}\ndef stabilizers (i : Fin {m}) (j : Fin {h}) : Fin {k} := (stabilizersData.getD i.val #[]).getD j.val 0\n\n'
    s += """theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

"""
    s += f"abbrev Params := (i : Fin {m}) → Fin (sizes i)\n"
    if d.get("indexed_parameters"):
        # Two short finite ranges avoid the recursive forall instance on a
        # single range with millions of elements.
        left, right = (m + 1) // 2, m // 2
        index_type = f"Fin ({radix} ^ {left}) × Fin ({radix} ^ {right})"
        s += (
            f"def paramEquiv : Params ≃ ({index_type}) :=\n"
            "  finFunctionFinEquiv.trans "
            f"(finProdFinEquiv (m := {radix} ^ {left}) (n := {radix} ^ {right})).symm\n"
        )
    if d.get("mixed_indexed_parameters"):
        total = math.prod(map(len, d["values"]))
        left = math.isqrt(total)
        while total % left:
            left -= 1
        right = total // left
        index_type = f"Fin {left} × Fin {right}"
        s += (
            f"def paramEquiv : Params ≃ ({index_type}) :=\n"
            "  finPiFinEquiv.trans ((finCongr (by decide)).trans "
            f"(finProdFinEquiv (m := {left}) (n := {right})).symm)\n"
        )
    if d.get("cache_word_images"):
        s += f"""def imageData : Array (Array (Fin {n})) :=
  wordImageData genPerm words
def image (i : Fin {k}) (x : Fin {n}) : Fin {n} :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin {k}) (x : Fin {n}) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin {n}) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

"""
    else:
        s += f"@[implicit_reducible] def fam (p : Params) : Magma (Fin {n}) := family genPerm words tr sizes values p\n"
    s += f"@[implicit_reducible] def source : Magma (Fin {n}) := ⟨sourceRow⟩\ndef pattern : Fin {q} → Bool := fun _ => false\n\n"
    s += f"""theorem coverage (N : Magma (Fin {n})) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

"""
    if d.get("cache_word_images"):
        s = s.replace(
            ": ∃ p, fam p = N :=\n  classification genPerm words rep tr sizes values stabilizers\n"
            "    transport_correct stabilizers_correct values_complete N hg",
            ": ∃ p, fam p = N := by\n"
            "  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers\n"
            "    transport_correct stabilizers_correct values_complete N hg\n"
            "  exact ⟨p, (fam_eq_family p).trans hp⟩",
        )
    selected = [d["candidates"][i] for i in d["selected_indices"]]
    for t in sorted({e["target"] for e in selected}):
        if d.get("restricted_target_test"):
            # A failed assignment already refutes a universal law. Fixing its
            # first variable is sound here without any transitivity assumption.
            left, right = load_equations()[t - 1]
            names = []

            def expression(term):
                if isinstance(term, str):
                    if term not in names:
                        names.append(term)
                    return "0" if term == names[0] else term
                return f"((fam p).op {expression(term[0])} {expression(term[1])})"

            equation = f"{expression(left)} = {expression(right)}"
            if len(names) > 1:
                equation = f"∀ {' '.join(names[1:])} : Fin {n}, {equation}"
            s += f"private abbrev test{t} (p : Params) : Prop := {equation}\n"
            s += f"private theorem restricted{t} : ∀ p : Params, test{t} p → ¬ Pattern (fam p) probePerm pattern := by"
            if d.get("indexed_parameters") or d.get("mixed_indexed_parameters"):
                s += f"""
  have h : ∀ i : {index_type}, test{t} (paramEquiv.symm i) →
      ¬ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by native_decide
  intro p
  simpa only [Equiv.symm_apply_apply] using h (paramEquiv p)
"""
            else:
                s += " native_decide\n"
            s += f"theorem target{t} : ∀ p : Params, @Equation{t} (Fin {n}) (fam p) → ¬ Pattern (fam p) probePerm pattern := by\n  intro p ht\n  exact restricted{t} p (ht 0)\n\n"
        else:
            s += f"theorem target{t} : ∀ p : Params, @Equation{t} (Fin {n}) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide\n\n"
    s += f"end Magma.{ns}\n\nopen Magma.{ns}\n\n"
    for e in selected:
        a, t = e["source"], e["target"]
        if d.get("one_way"):
            assert not d["probes"] and d["target_counts"][str(t)] == 0
            name = (
                f"Equation{t}_not_definableFromFin_Equation{a}_{ns[0].lower()+ns[1:]}"
            )
            s += f"""theorem {name} : ¬ Law{t}.DefinableFromFin Law{a} := by
  intro h
  have hs := (@Law{a}.models_iff (Fin {n}) source).mpr (by native_decide)
  obtain ⟨N, hN, hf⟩ := h source hs
  have hg : ∀ i, N.IsEndo (genPerm i) := fun i =>
    Magma.IsEndo.of_definable hf (source_generators i)
  obtain ⟨p, rfl⟩ := coverage N hg
  apply target{t} p ((@Law{t}.models_iff (Fin {n}) (fam p)).mp hN)
  intro i
  exact Fin.elim0 i

#print axioms {name}

"""
            continue
        name = f"Equation{t}_not_structuralFromFin_Equation{a}_{ns[0].lower()+ns[1:]}"
        s += f"""theorem {name} : ¬ Law{t}.StructuralFromFin Law{a} := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law{a}.models_iff (Fin {n}) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target{t} p ((@Law{t}.models_iff (Fin {n}) (fam p)).mp hp)

#print axioms {name}

"""
    for name, axioms in d.get("axioms", {}).items():
        s = s.replace(
            "#print axioms " + name + "\n",
            "/-- info: "
            + axioms
            + " -/\n#guard_msgs (whitespace := lax) in\n#print axioms "
            + name
            + "\n",
        )
    if d.get("pattern_first"):
        for e in selected:
            t = e["target"]
            if d.get("restricted_target_test"):
                s = s.replace(
                    f"test{t} p → ¬ Pattern (fam p) probePerm pattern",
                    f"Pattern (fam p) probePerm pattern → ¬ test{t} p",
                ).replace(
                    f"intro p ht\n  exact restricted{t} p (ht 0)",
                    f"intro p hp ht\n  exact restricted{t} p hp (ht 0)",
                )
            s = s.replace(
                f"@Equation{t} (Fin {n}) (fam p) → ¬ Pattern (fam p) probePerm pattern",
                f"Pattern (fam p) probePerm pattern → ¬ @Equation{t} (Fin {n}) (fam p)",
            )
            s = s.replace(
                f"exact target{t} p ((@Law{t}.models_iff (Fin {n}) (fam p)).mp hp)",
                f"intro hpattern\n    exact target{t} p hpattern ((@Law{t}.models_iff (Fin {n}) (fam p)).mp hp)",
            )
    return s


def render_four_chart(d):
    """Share the large chart; encode words as natural numbers before decoding."""
    assert d["order"] == 256 and len(d["generators"]) == 15
    assert len(d["words"]) == 41476 and len(d["representatives"]) == 6
    s = _render_raw(d, "CyclicFourChart").split("theorem source_generators")[0]
    s = re.sub(r"def sourceRowData.*?\n\n", "", s, flags=re.S)
    s = re.sub(r"@\[implicit_reducible\] def source[^\n]*\n", "", s)

    def encode(word):
        code = 0
        for generator in reversed(word):
            code = generator + 1 + 15 * code
        return code

    codes = [encode(word) for word in d["words"]]
    blocks = [codes[i : i + 256] for i in range(0, len(codes), 256)]
    words = (
        """def decodeWord : ℕ → List (Fin 15)
  | 0 => []
  | n + 1 => Fin.ofNat 15 (n % 15) :: decodeWord (n / 15)
termination_by n => n

"""
        + nat_rows("wordCodeBlocks", blocks)
        + "def wordCodes : Array ℕ := wordCodeBlocks.foldl (fun a b => a ++ b) #[]\n"
        + "def wordsData : Array (List (Fin 15)) := wordCodes.map decodeWord\n"
    )
    s = re.sub(r"def wordsData[^\n]*\n", lambda _: words, s)
    transport = (
        nat_rows("trCodes", [[a * 41476 + b for a, b in row] for row in d["transport"]])
        + """
def trData : Array (Array (Fin 6 × Fin 41476)) :=
  trCodes.map (fun row => row.map (fun code => (Fin.ofNat 6 (code / 41476), Fin.ofNat 41476 code)))
"""
    )
    s = re.sub(r"def trData[^\n]*\n", lambda _: transport, s)
    return s + "end Magma.CyclicFourChart\n"


def render(d, ns):
    s = _render_raw(d, ns)
    if d.get("compiled_orbit"):
        from definability_orbit_native import integrate_native

        s = integrate_native(d, ns, s)
    if d.get("compact_literals"):
        n, g, k, m = d["order"], len(d["generators"]), len(d["words"]), len(d["values"])
        codes = []
        for word in d["words"]:
            code = 0
            for generator in reversed(word):
                code = generator + 1 + g * code
            codes.append(code)
        words = f"""def decodeWord : ℕ → List (Fin {g})
  | 0 => []
  | n + 1 => Fin.ofNat {g} (n % {g}) :: decodeWord (n / {g})
termination_by n => n

""" + nat_rows(
            "wordCodeBlocks", [codes[i : i + 256] for i in range(0, len(codes), 256)]
        )
        words += f"def wordCodes : Array ℕ := wordCodeBlocks.foldl (fun a b => a ++ b) #[]\ndef wordsData : Array (List (Fin {g})) := wordCodes.map decodeWord\n"
        s = re.sub(r"def wordsData[^\n]*\n", lambda _: words, s)
        transport = nat_rows(
            "trCodes", [[a * k + b for a, b in row] for row in d["transport"]]
        )
        transport += f"def trData : Array (Array (Fin {m} × Fin {k})) :=\n  trCodes.map (fun row => row.map (fun code => (Fin.ofNat {m} (code / {k}), Fin.ofNat {k} code)))\n"
        s = re.sub(r"def trData[^\n]*\n", lambda _: transport, s)
        source = nat_rows("sourceRowCodes", d["source"])
        source += f"def sourceRowData : Array (Array (Fin {n})) :=\n  sourceRowCodes.map (fun row => row.map (Fin.ofNat {n}))\ndef sourceRow (i x : Fin {n}) : Fin {n} := (sourceRowData.getD i.val #[]).getD x.val 0\n"
        s = re.sub(
            r"def sourceRowData[^\n]*\ndef sourceRow[^\n]*\n", lambda _: source, s
        )
    if not d.get("shared_four_chart"):
        return s
    source = (
        nat_rows("sourceRowCodes", d["source"])
        + """
def sourceRowData : Array (Array (Fin 256)) :=
  sourceRowCodes.map (fun row => row.map (Fin.ofNat 256))
def sourceRow (i x : Fin 256) : Fin 256 := (sourceRowData.getD i.val #[]).getD x.val 0
@[implicit_reducible] def source : Magma (Fin 256) := ⟨sourceRow⟩

"""
    )
    return (
        "import equational_theories.Definability.Generated.CyclicFourChart\n\n"
        "/-! A finite symmetry obstruction using the shared four-coordinate chart. -/\n"
        "open Law Law.MagmaLaw Magma.FiniteSymmetry Magma.CyclicFourChart\n"
        "set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n"
        f"namespace Magma.{ns}\n\n"
        + source
        + "theorem source_generators"
        + s.split("theorem source_generators", 1)[1]
    )


ROOT = Path(__file__).resolve().parents[1]


def render_axiom_checks(data):
    text = "".join(
        f"import equational_theories.Definability.Generated.{name}\n"
        for name in data["modules"]
    )
    text += "\n/-! Explicit axiom checks for the large symmetry certificates. -/\n\n"
    for name in data["theorems"]:
        if name in data.get("axioms", {}):
            text += f"/-- info: {data['axioms'][name]} -/\n#guard_msgs (whitespace := lax) in\n"
        text += f"#print axioms {name}\n\n"
    return text


def check(d):
    n = d["order"]
    identity = list(range(n))
    generators = d["generators"]
    for key, invkey in [
        ("generators", "generator_inverses"),
        ("probes", "probe_inverses"),
    ]:
        for perm, inv in zip(d[key], d[invkey], strict=True):
            assert sorted(perm) == sorted(inv) == identity
            assert all(inv[perm[x]] == x == perm[inv[x]] for x in identity)
    images = []
    for word in d["words"]:
        perm = identity
        for i in reversed(word):
            perm = [generators[i][x] for x in perm]
        images.append(perm)
    for x in identity:
        for y in identity:
            orbit, word = d["transport"][x][y]
            a, b = d["representatives"][orbit]
            assert images[word][a] == x and images[word][b] == y
    for i, (a, b) in enumerate(d["representatives"]):
        stabilizers = [images[j] for j in d["stabilizers"][i]]
        assert all(p[a] == a and p[b] == b for p in stabilizers)
        fixed = {x for x in identity if all(p[x] == x for p in stabilizers)}
        assert fixed == set(d["values"][i])
    transport = np.array(d["transport"], dtype=np.int64)
    image_array = np.array(images, dtype=np.uint16)
    orbits, words = transport[:, :, 0], transport[:, :, 1]
    if d.get("lazy_tables"):
        size = math.prod(map(len, d["values"]))
        parameters = np.empty((size, len(d["values"])), dtype=np.uint16)
        codes = np.arange(size)
        divisor = size
        for i, allowed in enumerate(d["values"]):
            divisor //= len(allowed)
            parameters[:, i] = np.array(allowed)[codes // divisor % len(allowed)]
        del codes

        class Tables:
            """Evaluate the checked orbit chart without storing every table."""

            shape = (size, n, n)

            def __len__(self):
                return size

            def __getitem__(self, key):
                if isinstance(key, tuple):
                    index, x, y = key
                    values = parameters[index, orbits[x, y]]
                    return image_array[words[x, y], values]
                values = parameters[key][..., orbits]
                return image_array[words, values]

        tables = Tables()
    else:
        parameters = np.array(list(itertools.product(*d["values"])), dtype=np.uint16)
        tables = np.empty((len(parameters), n, n), dtype=np.uint16)
        for start in range(0, len(parameters), 1024):
            values = parameters[start : start + 1024, orbits]
            tables[start : start + len(values)] = image_array[words[None], values]
    assert len(tables) == d["family_count"]
    source = np.array(d["source"], dtype=np.uint16)
    if "field_witness" in d:
        field = d["field_witness"]
        p = field["prime"]
        assert n == p and all(p % k for k in range(2, math.isqrt(p) + 1))
        powers = sorted({pow(x, field.get("index", 2), p) for x in range(1, p)})
        f = np.full(n, -1, dtype=np.int64)
        f[0] = 0
        for representative, value in zip(
            field["coset_representatives"], field["values"], strict=True
        ):
            for a in powers:
                x = a * representative % p
                assert f[x] == -1
                f[x] = a * value % p
        assert np.all(f >= 0)
        x, y = np.indices((n, n))
        assert np.array_equal(source, (x + f[(y - x) % p]) % p)
    if "quadratic_field_witness" in d:
        field = d["quadratic_field_witness"]
        p, constant = field["prime"], field["constant"]
        assert n == p * p
        a, b = np.arange(n) % p, np.arange(n) // p
        add = (a[:, None] + a) % p + p * ((b[:, None] + b) % p)
        mul = (a[:, None] * a - constant * b[:, None] * b) % p + p * (
            (a[:, None] * b + b[:, None] * a) % p
        )
        assert all(len(set(row[1:])) == n - 1 for row in mul[1:])
        cubes = sorted({int(mul[mul[x, x], x]) for x in range(1, n)})
        assert len(cubes) * len(field["representatives"]) == n - 1
        f = np.full(n, -1, dtype=np.int64)
        f[0] = 0
        for representative, value in zip(
            field["representatives"], field["values"], strict=True
        ):
            orbit = mul[cubes, representative]
            assert np.all(f[orbit] == -1)
            f[orbit] = mul[cubes, value]
        assert np.all(f >= 0)
        negative = (-a) % p + p * ((-b) % p)
        assert np.array_equal(
            source, add[np.arange(n)[:, None], f[add[negative[:, None], np.arange(n)]]]
        )
    assert preserves(source, map(np.array, generators))
    probes = list(map(np.array, d["probes"]))
    assert all(not preserves(source, [p]) for p in probes)
    equations = load_equations()
    models_for = model_indices
    if d.get("normalize_first_variable"):
        # Check local coherence before using transitivity to normalize valuations.
        for perm in map(np.array, generators):
            shifted = transport[perm[:, None], perm[None, :]]
            assert np.array_equal(shifted[:, :, 0], orbits)
            for i, allowed in enumerate(d["values"]):
                cells = orbits == i
                for value in allowed:
                    assert np.array_equal(
                        perm[image_array[words[cells], value]],
                        image_array[shifted[:, :, 1][cells], value],
                    )
        orbit = {0}
        while True:
            larger = orbit | {perm[x] for perm in generators for x in orbit}
            if larger == orbit:
                break
            orbit = larger
        assert len(orbit) == n

        def normalized_models(equations, tables, law):
            left, right = equations[law - 1]
            names = sorted(variables(left) | variables(right))
            assignments = itertools.product(range(n), repeat=len(names) - 1)
            active = np.arange(len(tables))
            while len(active):
                batch_size = min(32, max(1, 2_000_000 // len(active)))
                batch = list(itertools.islice(assignments, batch_size))
                if not batch:
                    break
                vals = np.array([(0,) + row for row in batch], dtype=np.uint16).T
                cache = {v: vals[i][None, :] for i, v in enumerate(names)}
                indices = active[:, None]

                def ev(term):
                    if term not in cache:
                        cache[term] = tables[indices, ev(term[0]), ev(term[1])]
                    return cache[term]

                good = np.broadcast_to(ev(left) == ev(right), (len(active), len(batch)))
                active = active[good.all(axis=1)]
            return active

        models_for = normalized_models
    if d.get("coordinate_dimension"):
        dimension = d["coordinate_dimension"]
        assert n == 4**dimension
        points = np.array(
            list(itertools.product(range(4), repeat=dimension)), dtype=np.uint16
        )

        def encode(v):
            return sum(
                v[..., j].astype(np.int64) * 4 ** (dimension - 1 - j)
                for j in range(dimension)
            )

        for j in range(dimension):
            for perm in [[1, 2, 3, 0], [1, 0, 2, 3]]:
                out = points.copy()
                out[:, j] = np.array(perm)[out[:, j]]
                p = encode(out)
                assert np.array_equal(tables[:, p[:, None], p[None, :]], p[tables])
                assert preserves(source, [p])

        def canonical_models(equations, tables, law):
            l, r = equations[law - 1]
            names = sorted(variables(l) | variables(r))

            def partitions(v):
                if len(v) == len(names):
                    yield v
                else:
                    for x in range(min(4, max(v, default=-1) + 2)):
                        yield from partitions(v + [x])

            parts = list(partitions([]))
            assignments = itertools.product(parts, repeat=dimension)
            active = np.arange(len(tables))
            while len(active):
                batch = list(itertools.islice(assignments, 32))
                if not batch:
                    break
                vals = encode(np.array(batch, dtype=np.uint16).transpose(0, 2, 1)).T
                cache = {v: vals[i][None, :] for i, v in enumerate(names)}
                idx = active[:, None]

                def ev(t):
                    if t not in cache:
                        cache[t] = tables[idx, ev(t[0]), ev(t[1])]
                    return cache[t]

                active = active[
                    np.broadcast_to(ev(l) == ev(r), (len(active), len(batch))).all(
                        axis=1
                    )
                ]
            return active

        models_for = canonical_models
    for law in {e["source"] for e in d["candidates"]}:
        assert len(models_for(equations, source[None], law)) == 1
    for law in {e["target"] for e in d["candidates"]}:
        models = models_for(equations, tables, law)
        assert len(models) == d["target_counts"][str(law)]
        assert all(any(preserves(tables[i], [p]) for p in probes) for i in models)
    assert {j for _, covered in d["coverage"] for j in covered} == set(
        range(len(d["candidates"]))
    )
    print(
        f"{d['label']}: checked {len(tables)} operations and {len(d['candidates'])} obstructions.",
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--only")
    args = parser.parse_args()
    for path in sorted((ROOT / "data").glob("definability_orbit_*.json")):
        d = json.loads(path.read_text())
        if args.only and args.only != d["label"]:
            continue
        check(d)
        output = (
            ROOT
            / "equational_theories/Definability/Generated"
            / f"{d['namespace']}.lean"
        )
        result = render(d, d["namespace"])
        if args.write:
            output.write_text(result)
        else:
            assert output.read_text() == result, f"Regenerate {output} with --write"
        if d.get("compiled_orbit"):
            from definability_orbit_native import render_native

            native_output = (
                ROOT / "defsearch/DefOrbit/Generated"
                / f"Native{d['namespace']}.lean"
            )
            native_result = render_native(d, d["namespace"])
            if args.write:
                native_output.parent.mkdir(parents=True, exist_ok=True)
                native_output.write_text(native_result)
            else:
                assert native_output.read_text() == native_result, (
                    f"Regenerate {native_output} with --write"
                )
        if d.get("shared_four_chart"):
            chart = output.with_name("CyclicFourChart.lean")
            text = render_four_chart(d)
            if args.write:
                chart.write_text(text)
            else:
                assert chart.read_text() == text, f"Regenerate {chart} with --write"
    axiom_path = ROOT / "data/definability_large_symmetry_axioms.json"
    if axiom_path.exists():
        data = json.loads(axiom_path.read_text())
        text = render_axiom_checks(data)
        output = (
            ROOT / "equational_theories/Definability/Generated/LargeSymmetryAxioms.lean"
        )
        if args.write:
            output.write_text(text)
        else:
            assert output.read_text() == text, f"Regenerate {output} with --write"


if __name__ == "__main__":
    main()
