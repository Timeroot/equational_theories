// Integration checks against the generated website data, without a browser.
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { KEYS, decode, ProofEngine } from "../home_page/research/shared.js";
const root = new URL("../home_page/research/data/", import.meta.url);
const read = async (file) =>
  JSON.parse(await readFile(new URL(`${file}.json`, root), "utf8"));
const index = await read("index"),
  proofs = await read("proofs"),
  spectrum = await read("spectrum");
assert.equal(index.equations.length, 4694);
const boards = new Map();
for (const key of KEYS) {
  const b = await read(key),
    n = b.groups.length;
  b.matrix = decode(b.status, n * n);
  b.at = (s, t) => b.matrix[b.classOf[s] * n + b.classOf[t]];
  boards.set(key, b);
  assert.equal(b.groups.flat().length, 4694);
  assert.equal(new Set(b.groups.flat()).size, 4694);
  assert.equal(b.possibleMerges.length, b.unresolved_equivalence_pairs);
  for (let a = 0; a < n; a++) {
    assert.equal(b.matrix[a * n + a], 1);
    for (let c = a + 1; c < n; c++)
      assert.ok(
        b.matrix[a * n + c] !== 1 || b.matrix[c * n + a] !== 1,
        "Uncollapsed proved class",
      );
  }
  for (const [a, c] of b.possibleMerges)
    assert.ok(b.matrix[a * n + c] !== 2 && b.matrix[c * n + a] !== 2);
  if (!key.startsWith("implies"))
    assert.ok(
      !b.matrix.some((s) => s === 3 || s === 4),
      "Conjecture leaked into definability",
    );
}
for (const fact of [...proofs.positive, ...proofs.negative]) {
  assert.ok(fact.key >= 0 && fact.key < 10);
  if (fact.conjectural) assert.ok(fact.key < 2);
  else
    for (const ref of fact.refs)
      assert.equal(proofs.sources[ref].status, "PROVED");
}
for (const family of Object.values(proofs.families)) {
  for (const pieces of Object.values(family)) {
    for (const [, ref] of pieces)
      assert.equal(proofs.sources[ref].status, "PROVED");
  }
}
const engine = new ProofEngine(proofs, async (key) => boards.get(key));
function checkPath(path, s, t, key, claims) {
  let at = s;
  for (const step of path) {
    assert.equal(step.s, at);
    assert.ok(step.fact.s.includes(step.s));
    assert.ok(step.fact.t.includes(step.t));
    assert.ok(proofs.includes[step.fact.key][KEYS.indexOf(key)]);
    assert.ok(claims || !step.fact.conjectural);
    at = step.t;
  }
  assert.equal(at, t);
}
let checked = 0;
async function check(s, t, key) {
  const result = await engine.explain(s, t, key),
    b = boards.get(key);
  assert.equal(result.status, b.at(s, t));
  if (result.path) checkPath(result.path, s, t, key, result.status === 3);
  else if (result.status === 2 || result.status === 4) {
    assert.ok(proofs.includes[KEYS.indexOf(key)][result.fact.key]);
    assert.ok(
      result.fact.s.includes(result.a) && result.fact.t.includes(result.b),
    );
    checkPath(result.left, result.a, s, result.native, result.status === 4);
    checkPath(result.right, t, result.b, result.native, result.status === 4);
    assert.ok(result.refs.length);
  }
  checked++;
}
// Fixed difficult cells cover finite/all distinctions and closed negative paths.
for (const key of KEYS)
  for (const [s, t] of [
    [2, 1],
    [1, 2],
    [52, 629],
    [629, 52],
    [433, 854],
    [3342, 3545],
    [3545, 3342],
    [1486, 1485],
    [677, 255],
    [1485, 1483],
  ])
    await check(s, t, key);
let rng = 72391;
const rand = (n) => {
  rng = (Math.imul(rng, 1664525) + 1013904223) >>> 0;
  return rng % n;
};
for (const key of KEYS) {
  const b = boards.get(key),
    reps = b.groups.map((g) => g[0]);
  for (let i = 0; i < 80; i++)
    await check(reps[rand(reps.length)], reps[rand(reps.length)], key);
  // Every nonempty status category must have a reconstructible representative.
  for (const status of [0, 1, 2, 3, 4]) {
    const i = b.matrix.findIndex((x) => x === status);
    if (i >= 0)
      await check(
        reps[Math.floor(i / reps.length)],
        reps[i % reps.length],
        key,
      );
  }
}
for (const src of proofs.sources) {
  assert.ok(!src.file.startsWith("/"), "Source must be repository-relative");
  assert.ok(src.line >= 1);
  assert.ok(src.name);
}
for (const r of spectrum.records) {
  for (const [k, name] of Object.entries(r))
    if (k.endsWith("_theorem") && name)
      assert.ok(spectrum.declarations[name], name);
  if (r.mathematical_status === "EXACT")
    assert.equal(
      spectrum.declarations[r.exact_spectrum_theorem].status,
      r.exact_proof_status,
    );
  else
    for (const kind of ["lower", "upper"])
      assert.equal(
        spectrum.declarations[r[`${kind}_bound_theorem`]].status,
        r[`${kind}_bound_proof_status`],
      );
}
assert.equal(spectrum.records[1484].exact_proof_status, "PROVED");
assert.equal(spectrum.records[1312].cofinite_status, "DISPUTED");
assert.equal(spectrum.records[1479].mathematical_status, "UNKNOWN");
assert.equal(
  spectrum.records[1479].lower_bound_proof_status,
  "PROOF_AVAILABLE",
);
console.log(
  `Verified ten class partitions, ${checked} proof reconstructions, and 4694 spectrum records.`,
);
