import assert from "node:assert/strict";
import test from "node:test";
import {
  orderList,
  overviewOf,
  remainingOf,
  initialOrders,
} from "../home_page/research/spectrum-view.js";

test("order lists abbreviate consecutive runs without filling gaps", () => {
  assert.equal(orderList([8, 4, 3, 2, 2, 10, 11, 0]), "2–4, 8, 10, 11");
  assert.equal(orderList([]), "");
});

test("a finite gap list keeps reported exclusions separate", () => {
  const o = overviewOf({
    overview: {
      finite: true,
      through: 26,
      open_orders: [10, 12, 14],
      pending_orders: [14],
      excluded_orders: [2, 3],
      included_orders: [1, 4],
    },
  });
  assert.deepEqual(o.open, [10, 12]);
  assert.deepEqual(o.pending, [14]);
  const remaining = remainingOf(o);
  assert.equal(remaining.text, "10, 12");
  assert.match(remaining.scope, /complete list/);
});

test("an initial segment never claims the spectrum is classified", () => {
  const o = overviewOf({
    overview: { finite: false, through: 64, open_orders: [] },
  });
  assert.equal(remainingOf(o).label, "Unresolved through 64");
  assert.match(remainingOf(o).text, /initial segment/);
  assert.match(remainingOf(o).scope, /larger orders may also remain open/);
  o.pending = [11];
  assert.doesNotMatch(remainingOf(o).text, /Only .*await Lean/);
});

test("the strip distinguishes proved absence from reported absence", () => {
  const cells = initialOrders({
    overview: {
      included_orders: [1, 4, 5],
      excluded_orders: [2],
      pending_orders: [3],
      open_orders: [6],
    },
  }, 6);
  assert.deepEqual(cells.map((x) => x.status), [
    "included", "excluded", "pending", "included", "included", "unknown",
  ]);
  assert.match(cells[2].label, /reported; Lean proof pending/);
  assert.match(cells[1].label, /proved in Lean/);
});

test("a proved tail can appear beyond the finite gap-list endpoint", () => {
  const cells = initialOrders({
    overview: {
      finite: true,
      through: 26,
      included_orders: Array.from({ length: 38 }, (_, i) => i + 27),
    },
  });
  assert.equal(cells.length, 64);
  assert.equal(cells[25].status, "unknown");
  assert.equal(cells[26].status, "included");
  assert.equal(cells[63].status, "included");
});

test("construction congruences are not used as exclusions", () => {
  const cells = initialOrders({
    overview: {
      family_labels: ["Sufficiently large orders congruent to 0 or 1 modulo 3"],
      included_orders: [1, 3],
      excluded_orders: [],
    },
  }, 3);
  assert.equal(cells[1].status, "unknown");
});

test("old bundles without overviews have an explicit fallback", () => {
  assert.equal(overviewOf({}), null);
  assert.deepEqual(initialOrders({}), []);
  assert.match(remainingOf(null).text, /bounds below/);
});
