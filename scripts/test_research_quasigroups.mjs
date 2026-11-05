import assert from "node:assert/strict";
import {test} from "node:test";
import {readFile} from "node:fs/promises";
import {decode} from "../home_page/research/shared.js";
import {parastropheBoard} from "../home_page/research/parastrophes.js";
import {QUESTIONS, questionById, caseStatus, inventory, readState, stateParams, matchingCases} from "../home_page/research/quasigroup-data.js";

test("bookmark state preserves every filter and handles invalid inputs", () => {
  const state = {scope: "all", question: "singleEquation-right", status: "no", query: "x ◇ y", focus: 477, representatives: true, page: 3};
  assert.deepEqual(readState(stateParams(state)), state);
  const invalid = readState(new URLSearchParams("flavour=bad&question=bad&status=bad&eq=4695&page=-20"));
  assert.equal(invalid.scope, "fin");
  assert.equal(invalid.question, "singleEquation-left");
  assert.equal(invalid.status, "unproved");
  assert.equal(invalid.focus, null);
  assert.equal(invalid.page, 1);
  assert.equal(readState(new URLSearchParams("status=yes&unproved=1")).status, "unproved");
  assert.equal(readState(new URLSearchParams("eq=1e3")).focus, null);
  assert.equal(stateParams({...state, status: "unproved"}).get("unproved"), "1");
  assert.equal(stateParams(state).has("unproved"), false);
});

test("not-applicable sides are excluded from open questions, but not the other side", () => {
  const board = {get: (_eq, _scope, _kind, side) => ({status: side === "right" ? 3 : 0}),
    applicable: (_eq, _scope, side) => side !== "left"};
  assert.equal(caseStatus(board, 1, "fin", questionById("singleEquation-left")), "na");
  assert.equal(caseStatus(board, 1, "fin", questionById("singleEquation-right")), "conjectural");
  assert.equal(caseStatus(board, 1, "fin", questionById("sideQuasigroup-left")), "unknown");
  const index = {equations: ["x = y"]};
  const state = {...readState(new URLSearchParams()), representatives: false};
  assert.equal(matchingCases(board, index, {}, state).length, 0);
  assert.equal(matchingCases(board, index, {}, {...state, question: "singleEquation-right"}).length, 1);
  assert.equal(matchingCases(board, index, {}, {...state, status: "na"}).length, 1);
});

test("representative search matches every equivalent member and respects carrier scope", () => {
  const index = {equations: ["a = a", "b = b", "c = c"]};
  const board = {get: () => ({status: 0}), applicable: () => true};
  const implications = {fin: {groups: [[2, 1], [3]]}, all: {groups: [[1], [2], [3]]}};
  const state = {...readState(new URLSearchParams()), representatives: true, query: "E2"};
  assert.deepEqual(matchingCases(board, index, implications, state), [{eq: 1, members: [2, 1]}]);
  assert.deepEqual(matchingCases(board, index, implications, {...state, scope: "all"}), [{eq: 2, members: [2]}]);
  assert.equal(matchingCases(board, index, implications, {...state, query: "b = b"})[0].eq, 1);
  assert.equal(matchingCases(board, index, implications, {...state, query: "E99"}).length, 0);
});

test("published summary counts and every drill-down agree with proof closure", async () => {
  const root = new URL("../home_page/research/data/", import.meta.url);
  const read = async name => JSON.parse(await readFile(new URL(`${name}.json`, root), "utf8"));
  const [data, index, all, fin] = await Promise.all(["parastrophes", "index", "implies-all", "implies-fin"].map(read));
  const implications = {all, fin};
  for (const b of [all, fin]) {
    const matrix = decode(b.status, b.classes * b.classes);
    b.at = (a, c) => matrix[b.classOf[a] * b.classes + b.classOf[c]];
  }
  const board = parastropheBoard(data, index, implications), totals = inventory(board, index);
  for (const scope of ["all", "fin"]) {
    assert.equal(totals[scope].total, 4694);
    for (const q of QUESTIONS) {
      const c = totals[scope].counts[q.id];
      assert.equal(Object.values(c).reduce((a, b) => a + b, 0), index.equations.length);
      for (const status of ["yes", "no", "unknown", "conjectural", "na", "unproved"]) {
        const state = {scope, question: q.id, status, query: "", representatives: false};
        const cases = matchingCases(board, index, implications, state);
        assert.equal(cases.length, status === "unproved" ? c.unknown + c.conjectural : c[status]);
        const groups = matchingCases(board, index, implications, {...state, representatives: true});
        assert.equal(groups.reduce((n, row) => n + row.members.length, 0), cases.length);
      }
    }
  }
  // When the new research is included, its finite negative must be navigable.
  if (data.records.some(r => r.name.endsWith("left_noSingleEquation680_fin"))) {
    for (const eq of [477, 680]) assert.equal(caseStatus(board, eq, "fin", questionById("singleEquation-left")), "no");
  }
});
