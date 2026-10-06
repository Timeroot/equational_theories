import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { decode, ProofEngine } from "../home_page/research/shared.js";
import {
  RELATION_KEYS,
  closure,
  entails,
  partitions,
  quotientByDuality,
  mergerGenerators,
  mergeWitness,
} from "../home_page/research/relation-comparison.js";
import { mergeDiagram } from "../home_page/research/merge-diagram.js";
import {
  parseShape,
  contains,
  subset,
  spectrumBoard,
} from "../home_page/research/spectrum-relations.js";

function board(key, groups, edges) {
  const yes = closure(groups.length, edges),
    classOf = [];
  groups.forEach((g, c) => g.forEach((id) => (classOf[id] = c)));
  return {
    key,
    groups,
    classOf,
    classes: groups.length,
    possibleMerges: [],
    matrix: Uint8Array.from(yes.flatMap((r) => [...r])),
    at(s, t) {
      return this.matrix[classOf[s] * groups.length + classOf[t]];
    },
  };
}
const fine = board(
  "implies-all",
  [[1], [2, 3], [4], [5]],
  [
    [0, 2],
    [1, 2],
    [1, 3],
  ],
);
const coarse = board(
  "termStructural-fin",
  [[1], [2, 3, 4], [5]],
  [
    [0, 1],
    [1, 2],
  ],
);
const facts = {
  positive: [{ key: 3, s: [4], t: [3], refs: [0] }],
  includes: Array.from({ length: 10 }, (_, i) =>
    Array.from({ length: 10 }, (_, j) => +(i === j)),
  ),
};

test("the hierarchy includes finite restriction, separate branches, and spectra", () => {
  assert.ok(entails("termStructural-all", "structural-fin"));
  assert.ok(!entails("termStructural-fin", "structural-all"));
  assert.ok(!entails("structural-all", "termDefinable-fin"));
  assert.ok(!entails("termDefinable-all", "structural-fin"));
  assert.ok(entails("definable-all", "spectrum-fin"));
  assert.ok(!entails("spectrum-fin", "definable-fin"));
});
test("the five-law example preserves fine classes and needs just its backedge", () => {
  const rows = partitions(fine, coarse),
    gens = mergerGenerators(fine, coarse, facts);
  assert.deepEqual(rows[1].fine, [1, 2]);
  const w = mergeWitness(rows[1], fine, coarse, gens);
  assert.deepEqual(
    w.base.map((e) => [e.s, e.t]),
    [[2, 4]],
  );
  assert.deepEqual(
    w.added.map((e) => [e.s, e.t]),
    [[4, 3]],
  );
  const graph = mergeDiagram(rows, fine, coarse, (r) =>
    mergeWitness(r, fine, coarse, gens),
  );
  assert.ok(
    graph.edges.some((e) => e.kind === "inherited" && e.s === 1 && e.t === 4),
  );
  assert.ok(
    graph.edges.some((e) => e.kind === "inherited" && e.s === 2 && e.t === 5),
  );
  assert.ok(
    !graph.edges.some((e) => e.kind === "inherited" && e.s === 1 && e.t === 2),
  );
  assert.ok(
    graph.edges.some((e) => e.kind === "coarser" && e.s === 1 && e.t === 2),
  );
});
test("conjectural generators cannot merge proved classes", () => {
  const g = mergerGenerators(fine, coarse, {
    ...facts,
    positive: [{ ...facts.positive[0], conjectural: true }],
  });
  assert.equal(g.size, 0);
});
test("non-refining class partitions are rejected", () => {
  assert.throws(() => partitions(coarse, fine), /refinement/);
});
test("duality quotient counts orbits and retains the actual orientation of an implication", () => {
  const original = board(
    "implies-all",
    [[1], [2], [3], [4], [5]],
    [
      [0, 3],
      [1, 2],
    ],
  );
  original.matrix[2] = 2;
  original.matrix[8] = 2; // 1 ↛ 3 and its dual 2 ↛ 4
  const duals = [null, 2, 1, 4, 3, 5],
    q = quotientByDuality(original, duals);
  assert.equal(q.classes, 3);
  assert.deepEqual(q.groups, [[1, 2], [3, 4], [5]]);
  assert.equal(original.classes, 5);
  assert.equal(original.at(1, 3), 2);
  assert.equal(q.at(1, 3), 1);
  assert.deepEqual(q.proofOptions(1, 3), [
    { s: 1, t: 3, status: 2 },
    { s: 1, t: 4, status: 1 },
  ]);
  assert.strictEqual(quotientByDuality(q, duals), q);
  assert.strictEqual(quotientByDuality(coarse, duals), coarse);
});
test("refuting one orientation cannot refute a quotient arrow", () => {
  const original = board("implies-fin", [[1], [2], [3], [4]], []),
    duals = [null, 2, 1, 4, 3];
  original.matrix[2] = 2;
  original.matrix[7] = 2; // 1 ↛ 3, 2 ↛ 4
  let q = quotientByDuality(original, duals);
  assert.equal(q.at(1, 3), 0);
  assert.ok(q.possibleMerges.length);
  original.matrix[3] = original.matrix[6] = 2; // both target orientations refuted
  q = quotientByDuality(original, duals);
  assert.equal(q.at(1, 3), 2);
  assert.equal(q.possibleMerges.length, 0);
});
test("symbolic inclusions use whole formulas rather than a finite sample", () => {
  assert.ok(
    subset(parseShape("powersTwo"), parseShape("squares ∪ twiceSquares")),
  );
  assert.ok(
    subset(parseShape("squares ∪ twiceSquares"), parseShape("sumTwoSquares")),
  );
  assert.ok(subset(parseShape("squares"), parseShape("residues 4 {0, 1} ∅")));
  assert.ok(!subset(parseShape("squares"), parseShape("powersTwo")));
  assert.ok(
    !subset(
      parseShape("positiveExcept {2}"),
      parseShape("positiveExcept {2, 6}"),
    ),
  );
  assert.ok(
    subset(
      parseShape("positiveExcept {2, 6}"),
      parseShape("positiveExcept {2}"),
    ),
  );
  assert.equal(parseShape("unrecognizedFamily"), null);
  assert.equal(parseShape("(squares ∪ unrecognizedFamily)"), null);
  assert.ok(contains(parseShape("(squares ∪ unrecognizedFamily)", true), 9));
  assert.ok(!contains(parseShape("sumTwoSquares"), 3));
  assert.ok(contains(parseShape("sumTwoSquares"), 5));
});
function record(equation, formula, status = "PROVED") {
  return {
    equation,
    exact_proof_status: status,
    exact_spectrum_formula: formula,
    exact_spectrum_theorem: `exact${equation}`,
  };
}
function dataset(records) {
  return {
    records,
    declarations: Object.fromEntries(
      records.map((r) => [
        r.exact_spectrum_theorem,
        { name: r.exact_spectrum_theorem, status: r.exact_proof_status },
      ]),
    ),
  };
}
test("equal proved spectra merge even when finite FO equivalence is false", () => {
  const fo = board("definable-fin", [[1], [2]], []);
  fo.matrix[1] = fo.matrix[2] = 2;
  const b = spectrumBoard(
    dataset([record(1, "squares"), record(2, "squares")]),
    fo,
  );
  assert.equal(b.classes, 1);
  assert.equal(b.at(1, 2), 1);
});
test("identical guesses and matching lower bounds never prove cospectrality", () => {
  const records = [
    record(1, "squares", "UNKNOWN"),
    record(2, "squares", "UNKNOWN"),
  ];
  for (const r of records)
    Object.assign(r, {
      lower_bound_formula: "squares",
      lower_bound_theorem: "lower",
    });
  const data = dataset(records);
  data.declarations.lower = { name: "lower", status: "PROVED" };
  const b = spectrumBoard(data, board("definable-fin", [[1], [2]], []));
  assert.equal(b.classes, 2);
  assert.equal(b.at(1, 2), 0);
  assert.equal(b.possibleMerges.length, 1);
});
test("a purported exact formula without an audited declaration supplies neither arrows nor labels", () => {
  const data = dataset([record(1, "squares"), record(2, "squares")]);
  data.declarations.exact2.status = "SORRY";
  const b = spectrumBoard(data, board("definable-fin", [[1], [2]], []));
  assert.equal(b.classes, 2);
  assert.equal(b.at(1, 2), 0);
  assert.equal(b.labels[b.classOf[2]], "Spec(E2) ?");
});
test("a separating finite order proves spectral non-inclusion in the correct direction", () => {
  const b = spectrumBoard(
    dataset([record(1, "squares"), record(2, "{1}")]),
    board("definable-fin", [[1], [2]], []),
  );
  assert.equal(b.at(1, 2), 2);
  assert.equal(b.at(2, 1), 1);
  assert.equal(b.explain(1, 2).witness.order, 4);
});
test("a separating order transfers along inclusions in the correct directions", () => {
  const records = [
    record(1, "squares"),
    record(2, null, "UNKNOWN"),
    record(3, null, "UNKNOWN"),
    record(4, "{1}"),
  ];
  const b = spectrumBoard(
    dataset(records),
    board(
      "definable-fin",
      [[1], [2], [3], [4]],
      [
        [0, 1],
        [2, 3],
      ],
    ),
  );
  const p = b.explain(2, 3);
  assert.equal(p.status, 2);
  assert.equal(p.witness.order, 4);
  assert.deepEqual(
    p.left.map((e) => [e.s, e.t]),
    [[1, 2]],
  );
  assert.deepEqual(
    p.right.map((e) => [e.s, e.t]),
    [[3, 4]],
  );
});

const root = new URL("../home_page/research/data/", import.meta.url);
const read = async (name) =>
  JSON.parse(await readFile(new URL(`${name}.json`, root), "utf8"));
const load = async (key) => {
  const b = await read(key);
  b.matrix = decode(b.status, b.classes ** 2);
  b.at = (s, t) => b.matrix[b.classOf[s] * b.classes + b.classOf[t]];
  return b;
};
test("the comparison hierarchy agrees with every published relation inclusion", async () => {
  const proofs = await read("proofs");
  for (let a = 0; a < 10; a++)
    for (let b = 0; b < 10; b++)
      assert.equal(
        entails(RELATION_KEYS[a], RELATION_KEYS[b]),
        !!proofs.includes[a][b],
      );
});
test("every published implication-to-finite-term-structural merger has an irredundant source certificate", async () => {
  const [f, c, p] = await Promise.all([
    load("implies-all"),
    load("termStructural-fin"),
    read("proofs"),
  ]);
  const generators = mergerGenerators(f, c, p),
    rows = partitions(f, c),
    engine = new ProofEngine(p);
  let merges = 0,
    added = 0;
  for (const row of rows)
    if (row.fine.length > 1) {
      merges++;
      const w = mergeWitness(row, f, c, generators),
        local = new Map(w.nodes.map((v, i) => [v, i]));
      for (const e of w.added) {
        added++;
        assert.notEqual(f.at(e.s, e.t), 1);
        assert.equal(c.at(e.s, e.t), 1);
        assert.ok(e.fact.refs.every((r) => p.sources[r].status === "PROVED"));
        assert.ok(engine.path(e.s, e.t, e.key).length);
        const remaining = [...w.base, ...w.added.filter((x) => x !== e)].map(
          (x) => [local.get(x.a), local.get(x.b)],
        );
        assert.equal(
          closure(w.nodes.length, remaining)[local.get(e.a)][local.get(e.b)],
          0,
        );
      }
    }
  assert.ok(merges > 600);
  assert.ok(added > 1000);
});
test("published spectra preserve every finite FO positive and provide replayable evidence", async () => {
  const [fo, data] = await Promise.all([
    load("definable-fin"),
    read("spectrum"),
  ]);
  const s = spectrumBoard(data, fo);
  for (const a of fo.groups)
    for (const b of fo.groups)
      if (fo.at(a[0], b[0]) === 1) assert.equal(s.at(a[0], b[0]), 1);
  assert.ok(s.classes < fo.classes);
  assert.deepEqual(
    s.possibleMerges.map(([a, b]) => [s.groups[a][0], s.groups[b][0]]),
    [[1483, 1485]],
  );
  for (const a of s.groups)
    for (const b of s.groups) {
      const proof = s.explain(a[0], b[0]);
      for (const step of [
        ...(proof.path || []),
        ...(proof.left || []),
        ...(proof.right || []),
      ]) {
        if (step.kind === "fo") assert.equal(fo.at(step.s, step.t), 1);
        else
          for (const name of step.refs)
            assert.equal(data.declarations[name].status, "PROVED");
      }
      for (const name of proof.witness?.refs || [])
        assert.equal(data.declarations[name].status, "PROVED");
    }
  assert.equal(s.at(1483, 168), 2); // order 2 separates them
  assert.equal(s.at(168, 1483), 1);
  assert.notEqual(s.classOf[1483], s.classOf[1485]); // a conjectured equality is not a proof
});
test("published comparisons quotient both implication scopes before computing merger certificates", async () => {
  const [a, f, t, index, proofs] = await Promise.all([
    load("implies-all"),
    load("implies-fin"),
    load("termStructural-fin"),
    read("index"),
    read("proofs"),
  ]);
  const all = quotientByDuality(a, index.duals),
    fin = quotientByDuality(f, index.duals);
  assert.ok(all.classes < a.classes && fin.classes < f.classes);
  for (const b of [all, fin])
    for (const g of b.groups)
      for (const id of g)
        assert.equal(b.classOf[index.duals[id]], b.classOf[id]);
  for (const [fine, coarse] of [
    [all, fin],
    [all, t],
    [fin, t],
  ]) {
    const rows = partitions(fine, coarse),
      generators = mergerGenerators(fine, coarse, proofs);
    for (const row of rows) {
      const w = mergeWitness(row, fine, coarse, generators);
      for (const e of w.base) {
        assert.ok(e.upToDuality);
        assert.ok(fine.proofOptions(e.s, e.t).some((p) => p.status === 1));
      }
      for (const e of w.added) {
        assert.notEqual(fine.at(e.s, e.t), 1);
        assert.equal(coarse.at(e.s, e.t), 1);
      }
    }
  }
  const r = partitions(all, t).find((r) => r.members.includes(63));
  assert.equal(r.fine.length, 5); // The ten implication classes are five dual pairs.
  const graph = mergeDiagram([r], all, t, (row) =>
    mergeWitness(row, all, t, mergerGenerators(all, t, proofs)),
  );
  assert.ok(
    graph.edges
      .filter((e) => e.kind === "inherited")
      .every((e) => e.upToDuality),
  );
});
