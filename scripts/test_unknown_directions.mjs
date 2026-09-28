import assert from "node:assert/strict";
import test from "node:test";
import { readFile } from "node:fs/promises";
import { KEYS, decode } from "../home_page/research/shared.js";
import {
  unknownDirections,
  filterUnknownDirections,
} from "../home_page/research/unknown-directions.js";

const board = {
  groups: [[1, 4], [2], [3]],
  matrix: new Uint8Array([
    1, 0, 2,
    2, 1, 3,
    0, 4, 1,
  ]),
};
const equations = ["x = x", "x = y", "x = y ◇ x", "x ◇ x = x"];

test("unknown directions include separated classes and exclude conjectures", () => {
  assert.deepEqual(unknownDirections(board), [[0, 1], [2, 0]]);
});

test("both unknown directions are retained as separate questions", () => {
  const b = { groups: [[1], [2]], matrix: new Uint8Array([1, 0, 0, 1]) };
  assert.deepEqual(unknownDirections(b), [[0, 1], [1, 0]]);
});

test("equation search finds nonrepresentative members and respects direction", () => {
  const pairs = unknownDirections(board);
  const filtered = (side) => filterUnknownDirections(pairs, board, equations, " E4 ", side);
  assert.deepEqual(filtered("either"), pairs);
  assert.deepEqual(filtered("source"), [[0, 1]]);
  assert.deepEqual(filtered("target"), [[2, 0]]);
  assert.deepEqual(filterUnknownDirections(pairs, board, equations, "44"), []);
});

test("formula search considers every member of a class", () => {
  assert.deepEqual(
    filterUnknownDirections(unknownDirections(board), board, equations, "X ◇ X", "target"),
    [[2, 0]],
  );
});

test("no unknown directions is an empty list, even with conjectural results", () => {
  assert.deepEqual(unknownDirections({ groups: [[1], [2]], matrix: [1, 3, 4, 1] }), []);
});

test("all ten published relation modes expose precisely their unknown class cells", async () => {
  for (const key of KEYS) {
    const b = JSON.parse(await readFile(
      new URL(`../home_page/research/data/${key}.json`, import.meta.url), "utf8",
    ));
    b.matrix = decode(b.status, b.groups.length ** 2);
    const pairs = unknownDirections(b);
    const expected = b.status.reduce((count, entry, i) =>
      i % 2 === 0 && entry === 0 ? count + b.status[i + 1] : count, 0);
    assert.equal(pairs.length, expected, key);
    assert.equal(new Set(pairs.map(([a, c]) => `${a},${c}`)).size, expected, key);
    for (const [a, c] of pairs) {
      assert.notEqual(a, c, key);
      assert.equal(b.matrix[a * b.groups.length + c], 0, key);
    }
  }
});
