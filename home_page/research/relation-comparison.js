// Pure graph operations shared by the merger views and their semantic tests.
export const RELATION_KEYS = [
  "implies-all",
  "implies-fin",
  "termStructural-all",
  "termStructural-fin",
  "structural-all",
  "structural-fin",
  "termDefinable-all",
  "termDefinable-fin",
  "definable-all",
  "definable-fin",
  "spectrum-fin",
];
export const RELATION_LABELS = [
  "Implication · all magmas",
  "Implication · finite",
  "Term structural · all magmas",
  "Term structural · finite",
  "FO structural · all magmas",
  "FO structural · finite",
  "Term definable · all magmas",
  "Term definable · finite",
  "FO definable · all magmas",
  "FO definable · finite",
  "Spectrum inclusion · finite",
];
const parents = [
  [1, 2],
  [3],
  [3, 4, 6],
  [5, 7],
  [5, 8],
  [9],
  [7, 8],
  [9],
  [9],
  [10],
  [],
];
export function entails(fine, coarse) {
  const target = RELATION_KEYS.indexOf(coarse),
    start = RELATION_KEYS.indexOf(fine);
  if (start < 0 || target < 0) return false;
  const seen = new Set([start]),
    queue = [start];
  for (const i of queue)
    for (const j of parents[i])
      if (!seen.has(j)) {
        seen.add(j);
        queue.push(j);
      }
  return seen.has(target);
}
export function closure(size, edges) {
  const rows = Array.from({ length: size }, (_, i) => {
    const r = new Uint8Array(size);
    r[i] = 1;
    return r;
  });
  for (const [a, b] of edges) rows[a][b] = 1;
  for (let k = 0; k < size; k++)
    for (let i = 0; i < size; i++)
      if (rows[i][k]) for (let j = 0; j < size; j++) rows[i][j] ||= rows[k][j];
  return rows;
}
export function reducedEdges(nodes, yes) {
  return nodes.flatMap((a) =>
    nodes
      .filter(
        (b) =>
          a !== b &&
          yes(a, b) &&
          !nodes.some((m) => m !== a && m !== b && yes(a, m) && yes(m, b)),
      )
      .map((b) => [a, b]),
  );
}
export function partitions(fine, coarse) {
  const rows = coarse.groups.map((members, id) => ({ id, members, fine: [] }));
  fine.groups.forEach((g, id) => {
    const c = coarse.classOf[g[0]];
    if (g.some((e) => coarse.classOf[e] !== c))
      throw Error("These proved partitions do not form a refinement.");
    rows[c].fine.push(id);
  });
  return rows;
}
// Duality acts as an order automorphism on implication classes. The quotient
// arrow [A] → [B] means A → B OR A → dual(B), not necessarily A → B.
// All other relations already identify a law with its dual.
export function quotientByDuality(board, duals) {
  if (!board.key.startsWith("implies-") || board.upToDuality) return board;
  const dualClass = board.groups.map((g) => board.classOf[duals[g[0]]]);
  board.groups.forEach((g, c) => {
    if (
      dualClass[dualClass[c]] !== c ||
      g.some((id) => board.classOf[duals[id]] !== dualClass[c])
    )
      throw Error("Duality does not preserve the implication classes.");
  });
  const parts = [],
    seen = new Set();
  board.groups.forEach((_, c) => {
    if (seen.has(c)) return;
    const orbit = [...new Set([c, dualClass[c]])];
    orbit.forEach((d) => seen.add(d));
    parts.push(orbit);
  });
  const groups = parts.map((orbit) =>
    orbit.flatMap((c) => board.groups[c]).sort((a, b) => a - b),
  );
  const classOf = Array(board.classOf.length).fill(null);
  groups.forEach((g, c) => g.forEach((id) => (classOf[id] = c)));
  const options = (s, t) =>
    [...new Set([t, duals[t]])].map((target) => ({
      s,
      t: target,
      status: board.at(s, target),
    }));
  const size = groups.length,
    matrix = new Uint8Array(size * size),
    possibleMerges = [];
  for (let a = 0; a < size; a++)
    for (let b = 0; b < size; b++) {
      const statuses = options(groups[a][0], groups[b][0]).map((e) => e.status);
      matrix[a * size + b] = statuses.includes(1)
        ? 1
        : statuses.every((s) => s === 2)
          ? 2
          : statuses.includes(3)
            ? 3
            : statuses.every((s) => s === 2 || s === 4)
              ? 4
              : 0;
    }
  for (let a = 0; a < size; a++)
    for (let b = a + 1; b < size; b++)
      if (matrix[a * size + b] !== 2 && matrix[b * size + a] !== 2)
        possibleMerges.push([a, b]);
  return {
    key: board.key,
    label: board.label,
    flavour: board.flavour,
    upToDuality: true,
    original: board,
    parts,
    groups,
    classOf,
    matrix,
    classes: size,
    possibleMerges,
    unresolved_equivalence_pairs: possibleMerges.length,
    labels: parts.map((orbit) =>
      orbit.map((c) => `E${board.groups[c][0]}`).join(" / "),
    ),
    proofOptions: options,
    at(s, t) {
      return matrix[classOf[s] * size + classOf[t]];
    },
  };
}
// Project source-labelled generators once. Retain actual theorem endpoints so
// the UI can distinguish a construction from transfers within the fine classes.
export function mergerGenerators(fine, coarse, proofs) {
  const result = new Map();
  if (coarse.key === "spectrum-fin") return result;
  const k = RELATION_KEYS.indexOf(coarse.key);
  for (const fact of proofs.positive) {
    if (fact.conjectural || !proofs.includes[fact.key][k]) continue;
    const sources = new Map(fact.s.map((s) => [fine.classOf[s], s]));
    const targets = new Map(fact.t.map((t) => [fine.classOf[t], t]));
    for (const [a, s] of sources)
      for (const [b, t] of targets) {
        if (
          a === b ||
          coarse.classOf[s] !== coarse.classOf[t] ||
          fine.at(s, t) === 1
        )
          continue;
        const c = coarse.classOf[s],
          pair = `${a},${b}`;
        if (!result.has(c)) result.set(c, new Map());
        const edges = result.get(c),
          old = edges.get(pair);
        if (
          !old ||
          fact.key < old.fact.key ||
          (fact.key === old.fact.key && fact.refs.length < old.fact.refs.length)
        )
          edges.set(pair, {
            a,
            b,
            s,
            t,
            fact,
            key: RELATION_KEYS[fact.key],
            kind: "added",
          });
      }
  }
  return result;
}
function reachable(nodes, edges, source, target) {
  const next = new Map(nodes.map((n) => [n, []]));
  for (const e of edges) next.get(e.a).push(e.b);
  const seen = new Set([source]),
    queue = [source];
  for (const a of queue)
    for (const b of next.get(a)) {
      if (b === target) return true;
      if (!seen.has(b)) {
        seen.add(b);
        queue.push(b);
      }
    }
  return source === target;
}
export function mergeWitness(row, fine, coarse, generators = new Map()) {
  const nodes = row.fine,
    rep = (c) => fine.groups[c][0];
  // Larger classes get a bounded spanning certificate; details remain available
  // through the explorer. Do not claim a minimum in either algorithm.
  const large = nodes.length > 120;
  if (large) {
    const star = nodes
      .slice(1)
      .flatMap((n) => [
        [nodes[0], n],
        [n, nodes[0]],
      ])
      .map(([a, b]) => {
        const inherited = fine.at(rep(a), rep(b)) === 1;
        return {
          a,
          b,
          s: rep(a),
          t: rep(b),
          key: inherited ? fine.key : coarse.key,
          upToDuality: (inherited ? fine : coarse).upToDuality,
          kind: inherited ? "inherited" : "added",
        };
      });
    return {
      nodes,
      base: star.filter((e) => e.kind === "inherited"),
      added: star.filter((e) => e.kind === "added"),
      large,
    };
  }
  const base = reducedEdges(nodes, (a, b) => fine.at(rep(a), rep(b)) === 1).map(
    ([a, b]) => ({
      a,
      b,
      s: rep(a),
      t: rep(b),
      key: fine.key,
      upToDuality: fine.upToDuality,
      kind: "inherited",
    }),
  );
  let added = [...(generators.get(row.id)?.values() || [])];
  if (!added.length && nodes.length > 1) {
    const root = nodes[0];
    added = nodes
      .slice(1)
      .flatMap((n) => [
        [root, n],
        [n, root],
      ])
      .filter(([a, b]) => fine.at(rep(a), rep(b)) !== 1)
      .map(([a, b]) => ({
        a,
        b,
        s: rep(a),
        t: rep(b),
        key: coarse.key,
        upToDuality: coarse.upToDuality,
        kind: "added",
      }));
  }
  if (!large) {
    // Delete an edge only when another path already proves its direction.
    // The result is inclusion-minimal relative to the inherited arrows.
    for (let i = added.length - 1; i >= 0; i--)
      if (
        reachable(
          nodes,
          [...base, ...added.filter((_, j) => j !== i)],
          added[i].a,
          added[i].b,
        )
      )
        added.splice(i, 1);
    for (const n of nodes)
      if (
        !reachable(nodes, [...base, ...added], nodes[0], n) ||
        !reachable(nodes, [...base, ...added], n, nodes[0])
      )
        throw Error("Incomplete merger certificate.");
  }
  return { nodes, base, added, large };
}
