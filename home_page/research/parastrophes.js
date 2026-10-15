// Questions about fixed division operations. This is independent of the ten
// existential definability boards: only ordinary implication transfers here.
export const FIELDS = [
  ["quasigroup", null, "Always a quasigroup"],
  ["singleEquation", "left", "Left: one equation"],
  ["term", "left", "Left: term per model"],
  ["uniformTerm", "left", "Left: uniform term"],
  ["singleEquation", "right", "Right: one equation"],
  ["term", "right", "Right: term per model"],
  ["uniformTerm", "right", "Right: uniform term"],
];
const keyOf = (eq, scope, kind, side) => `${eq}/${scope}/${kind}/${side || ""}`;
const swap = (side) => side === "left" ? "right" : side === "right" ? "left" : null;
export function dualTree(t, swapInputs = false) {
  if (!t) return null;
  if ("leaf" in t) return {leaf: swapInputs ? 1 - t.leaf : t.leaf};
  return {left: dualTree(t.right, swapInputs), right: dualTree(t.left, swapInputs)};
}
export function termText(t, variables = ["x", "y"]) {
  if ("leaf" in t) return variables[t.leaf] ?? `x${t.leaf}`;
  return `(${termText(t.left, variables)} ◇ ${termText(t.right, variables)})`;
}
export function lawText(law) { return `${termText(law.lhs)} = ${termText(law.rhs)}`; }

const ruleName = (kind, suffix) => ({quasigroup: "quasigroup", singleEquation: "singleEquation",
  term: "termRecovery", uniformTerm: "uniformTermRecovery"}[kind]) + suffix;

export function parastropheBoard(data, index, implications = {}) {
  if (data.version !== 1) throw Error("Unsupported parastrophe data version");
  if (!data.local && data.commit !== index.commit) throw Error("Parastrophe and implication exports come from different commits");
  if (data.rules.some(r => r.status !== "PROVED")) throw Error("Unproved parastrophe transfer rule");
  const cells = new Map(), queue = [], propagated = new Set();
  const ruleRefs = new Map(data.rules.map(r => [r.name.split(".").at(-1), r]));
  const unknown = Object.freeze({status: 0, steps: []});
  const get = (eq, scope, kind, side = null) => cells.get(keyOf(eq, scope, kind, side)) || unknown;
  function put(f) {
    const key = keyOf(f.equation, f.scope, f.kind, f.side), old = cells.get(key);
    if (old) {
      if (old.status <= 2 && f.status <= 2 && old.positive !== f.positive)
        throw Error(`Conflicting proved parastrophe evidence: ${key}`);
      // A proof outranks a conjecture. Otherwise retain the first (direct
      // records precede closure); a generic existence proof must not erase a term.
      if (old.status <= 2 || f.status > 2) return;
    }
    cells.set(key, f); queue.push(f);
  }
  function derive(f, changes, rule, details = {}) {
    if (!ruleRefs.has(rule)) throw Error(`Missing audited parastrophe rule: ${rule}`);
    put({...f, ...changes, steps: [...f.steps, {rule, ...details}]});
  }
  data.records.forEach((r, seed) => {
    if (!Number.isInteger(r.equation) || r.equation < 1 || r.equation > index.equations.length ||
        !["all", "fin"].includes(r.scope) || !["PROVED", "PROOF_AVAILABLE"].includes(r.status) ||
        !FIELDS.some(([k,s]) => k === r.kind && s === r.side))
      throw Error("Invalid parastrophe record");
    put({...r, status: r.status === "PROVED" ? (r.positive ? 1 : 2) : (r.positive ? 3 : 4),
      seed, steps: []});
  });
  for (let i = 0; i < queue.length; i++) {
    const f = queue[i];
    // Claims remain visible but are not used as premises in proved closure.
    if (f.status > 2) continue;
    const {equation: eq, scope, kind, side, positive} = f;
    if ((scope === "all" && positive) || (scope === "fin" && !positive))
      derive(f, {scope: scope === "all" ? "fin" : "all"}, ruleName(kind, "_finite"));
    const dual = index.duals[eq];
    if (!Number.isInteger(dual) || index.duals[dual] !== eq) throw Error("Invalid equation duality");
    derive(f, {equation: dual, side: swap(side),
      targetEquation: f.targetEquation ? index.duals[f.targetEquation] : null,
      targetLaw: f.targetLaw ? {lhs: dualTree(f.targetLaw.lhs), rhs: dualTree(f.targetLaw.rhs)} : null,
      term: dualTree(f.term, true)}, ruleName(kind, "_dual"), {from: eq, to: dual});
    if ((kind === "uniformTerm" && positive) || (kind === "term" && !positive))
      derive(f, {kind: kind === "uniformTerm" ? "term" : "uniformTerm"}, "uniform_implies_term");
    if (scope === "all" && ["term", "uniformTerm"].includes(kind))
      derive(f, {kind: kind === "term" ? "uniformTerm" : "term"}, "termRecovery_iff_uniform_all");
    if (kind === "term" && positive && get(eq, scope, "term", swap(side)).status === 1)
      derive(f, {kind: "quasigroup", side: null, term: null}, "termRecovery_quasigroup",
        {support: [eq, scope, "term", swap(side)]});
    if (kind === "quasigroup" && positive) {
      for (const s of ["left", "right"])
        derive(f, {kind: scope === "all" ? "uniformTerm" : "term", side: s, term: null},
          scope === "all" ? "quasigroup_uniform_all" : "quasigroup_term_fin");
    }
    if (!positive && ((scope === "all" && kind === "uniformTerm") || (scope === "fin" && kind === "term")))
      derive(f, {kind: "quasigroup", side: null, term: null},
        scope === "all" ? "quasigroup_uniform_all" : "quasigroup_term_fin");
    if (kind === "singleEquation" && positive && f.targetEquation)
      derive(f, {equation: f.targetEquation, kind: "quasigroup", side: null,
        targetEquation: null, targetLaw: null, term: null}, "characterizes_quasigroup");

    const board = implications[scope];
    if (!board) continue;
    const group = board.classOf[eq];
    const transferKey = `${scope}/${kind}/${side}/${positive}/${group}`;
    if (propagated.has(transferKey)) continue;
    propagated.add(transferKey);
    for (const members of board.groups) {
      const other = members[0];
      const forward = board.at(other, eq) === 1, backward = board.at(eq, other) === 1;
      if (kind === "singleEquation" ? !(forward && backward) : !(positive ? forward : backward)) continue;
      for (const to of members) {
        if (to === eq) continue;
        derive(f, {equation: to}, kind === "singleEquation" ? "singleEquation_of_equivalent" :
          ruleName(kind, "_of_implies"), {from: eq, to, scope, positive,
            equivalent: kind === "singleEquation"});
      }
    }
  }
  return {get, cells, data, ruleRefs,
    applicable: (eq, scope) => get(eq, scope, "quasigroup").status !== 2,
    unproved: (eq, scope) => FIELDS.some(([k,s]) =>
      (k === "quasigroup" || get(eq, scope, "quasigroup").status !== 2) &&
      ![1,2].includes(get(eq, scope, k, s).status)),
  };
}
