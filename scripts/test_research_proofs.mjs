// Small semantic cases for hierarchy/flavour handling in the proof viewer.
import assert from "node:assert/strict";
import { KEYS, ProofEngine, decode } from "../home_page/research/shared.js";
const includes = KEYS.map((_, i) => KEYS.map((_, j) => +(i === j)));
for (let i = 0; i < 10; i += 2) includes[i][i + 1] = 1;
for (const f of [0, 1])
  for (const [a, b] of [
    [0, 2],
    [2, 4],
    [2, 6],
    [4, 8],
    [6, 8],
  ])
    includes[a + f][b + f] = 1;
for (let k = 0; k < 10; k++)
  for (let i = 0; i < 10; i++)
    for (let j = 0; j < 10; j++)
      includes[i][j] ||= includes[i][k] && includes[k][j];
const data = {
  includes,
  positive: [
    { key: 9, s: [1], t: [2], refs: [0] },
    { key: 2, s: [4], t: [5], refs: [1] },
    { key: 0, s: [6], t: [7], refs: [2], conjectural: true },
  ],
  negative: [{ key: 9, s: [1], t: [3], refs: [3] }],
};
const load = async (key) => ({
  at: (s, t) =>
    s === t
      ? 1
      : s === 1 && t === 2 && key === "definable-fin"
        ? 1
        : s === 2 && t === 3
          ? 2
          : s === 6 && t === 7 && key === "implies-all"
            ? 3
            : 0,
});
const e = new ProofEngine(data, load);
// A finite FO-definability obstruction refutes all-magmas term structurality,
// but its auxiliary path must retain its weaker native relation.
const negative = await e.explain(2, 3, "termStructural-all");
assert.equal(negative.native, "definable-fin");
assert.deepEqual(
  negative.left.map((x) => [x.s, x.t]),
  [[1, 2]],
);
assert.throws(() => e.path(1, 2, "termStructural-all"), /Missing source path/);
// All-magmas positive results restrict to finite models, not vice versa.
assert.equal(e.path(4, 5, "termStructural-fin").length, 1);
assert.throws(() => e.path(1, 2, "definable-all"), /Missing source path/);
// Claims do not become proofs or seed another relation's proved classes.
assert.throws(() => e.path(6, 7, "implies-all"), /Missing source path/);
assert.equal(
  (await e.explain(6, 7, "implies-all")).path[0].fact.conjectural,
  true,
);
assert.deepEqual(e.path(2, 2, "termStructural-all"), []);
assert.deepEqual([...decode([0, 2, 1, 1, 4, 2], 5)], [0, 0, 1, 4, 4]);
assert.throws(() => decode([1, 2], 3), /Invalid relation data/);
console.log(
  "Proof semantics passed: finite/all direction, hierarchy, native negative paths, conjectures, and reflexivity.",
);
