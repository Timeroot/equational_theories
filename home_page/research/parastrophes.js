// Questions about fixed division operations. Ordinary implications transfer
// properties here; Lean's attribute-generated consequences seed the structural
// boards in the other direction (the browser does not infer those arrows).
export const FIELDS = [
  ["quasigroup", null, "Both sides bijective"],
  ["sideQuasigroup", "left", "Left: always bijective"],
  ["singleEquation", "left", "Left: one equation"],
  ["term", "left", "Left: term per model"],
  ["uniformTerm", "left", "Left: uniform term"],
  ["sideQuasigroup", "right", "Right: always bijective"],
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

const ruleName = (kind, suffix) => ({quasigroup: "quasigroup", sideQuasigroup: "sideQuasigroup", singleEquation: "singleEquation",
  term: "termRecovery", uniformTerm: "uniformTermRecovery"}[kind]) + suffix;

export function parastropheBoard(data, index, implications = {}) {
  if (data.version !== 2) throw Error("Unsupported parastrophe data version");
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
      // A later explicit term improves an earlier abstract existence proof.
      // Keep it, including its own provenance, and propagate that improvement.
      if ((old.status <= 2 || f.status > 2) &&
          !(old.status === 1 && f.status === 1 && !old.term && f.term &&
            ["term", "uniformTerm"].includes(f.kind))) return;
    }
    cells.set(key, f); queue.push(f);
  }
  function derive(f, changes, rule, details = {}) {
    if (!ruleRefs.has(rule)) throw Error(`Missing audited parastrophe rule: ${rule}`);
    put({...f, ...changes, steps: [...f.steps, {rule, ...details}]});
  }
  function characterizeSimpleDivision(eq, scope, side) {
    const t = get(eq, scope, "uniformTerm", side);
    if (t.status !== 1) return;
    const a = t.term?.left?.leaf, b = t.term?.right?.leaf;
    if (!((a === 0 && b === 1) || (a === 1 && b === 0))) return;
    derive(t, {kind: "singleEquation", term: null, targetLaw: null,
      targetEquation: a === 0 ? eq : index.duals[eq]},
      a === 0 ? "characterizes_self" : "characterizes_opposite");
  }
  function transferImage(eq, scope, side) {
    const f = get(eq, scope, "singleEquation", side);
    if (f.status !== 1 || !f.targetEquation) return;
    const changes = {equation: f.targetEquation, term: null, targetLaw: null};
    if (get(eq, scope, "sideQuasigroup", side).status === 1) {
      derive(f, {...changes, targetEquation: eq}, "characterizes_symm",
        {support: [eq, scope, "sideQuasigroup", side]});
      const other = get(eq, scope, "sideQuasigroup", swap(side));
      if ([1,2].includes(other.status))
        derive(f, {...changes, kind: "sideQuasigroup", side: swap(side), targetEquation: null,
          status: other.status, positive: other.positive}, "characterizes_otherSide",
          {supports: [[eq, scope, "sideQuasigroup", side], [eq, scope, "sideQuasigroup", swap(side)]]});
    }
    if (get(eq, scope, "quasigroup").status === 1)
      derive(f, {...changes, kind: "quasigroup", side: null, targetEquation: null},
        "characterizes_quasigroup", {support: [eq, scope, "quasigroup", null]});
  }
  function combineSides(eq, scope) {
    const q = get(eq, scope, "quasigroup");
    for (const side of ["left", "right"]) {
      const f = get(eq, scope, "sideQuasigroup", side);
      if (f.status !== 1) continue;
      if (get(eq, scope, "sideQuasigroup", swap(side)).status === 1)
        derive(f, {kind: "quasigroup", side: null, term: null}, "sideQuasigroups_quasigroup",
          {support: [eq, scope, "sideQuasigroup", swap(side)]});
      if (q.status === 2)
        derive(q, {kind: "sideQuasigroup", side: swap(side)}, "sideQuasigroups_quasigroup",
          {support: [eq, scope, "sideQuasigroup", side]});
    }
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
    if (kind === "term" && positive)
      derive(f, {kind: "sideQuasigroup", term: null}, "termRecovery_sideQuasigroup");
    if (kind === "sideQuasigroup") {
      if (positive) {
        derive(f, {kind: scope === "all" ? "uniformTerm" : "term", term: null},
          scope === "all" ? "sideQuasigroup_uniform_all" : "sideQuasigroup_term_fin");
      } else {
        derive(f, {kind: "term", term: null}, "termRecovery_sideQuasigroup");
        derive(f, {kind: "quasigroup", side: null, term: null}, "quasigroup_side");
      }
      combineSides(eq, scope);
      transferImage(eq, scope, side);
      transferImage(eq, scope, swap(side));
    }
    if (kind === "quasigroup") {
      if (positive) for (const s of ["left", "right"])
        derive(f, {kind: "sideQuasigroup", side: s, term: null}, "quasigroup_side");
      combineSides(eq, scope);
      for (const s of ["left", "right"]) transferImage(eq, scope, s);
    }
    if (!positive && ((scope === "all" && kind === "uniformTerm") || (scope === "fin" && kind === "term")))
      derive(f, {kind: "sideQuasigroup", term: null},
        scope === "all" ? "sideQuasigroup_uniform_all" : "sideQuasigroup_term_fin");
    if (kind === "singleEquation" && positive && f.targetEquation) {
      derive(f, {equation: f.targetEquation, kind: "sideQuasigroup",
        targetEquation: null, targetLaw: null, term: null}, "characterizes_sideQuasigroup");
      transferImage(eq, scope, side);
    }
    if (positive && kind === "uniformTerm") characterizeSimpleDivision(eq, scope, side);

    const board = implications[scope];
    if (!board) continue;
    const group = board.classOf[eq];
    const transferKey = `${scope}/${kind}/${side}/${positive}/${group}/${Boolean(f.term)}`;
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
  const bases = imageBasisBoard(data, index, implications, ruleRefs);
  return {get, cells, data, ruleRefs, getBasis: bases.get,
    applicable: (eq, scope, side) => get(eq, scope, "sideQuasigroup", side).status !== 2,
    unproved: (eq, scope) => FIELDS.some(([k,s]) =>
      (["quasigroup", "sideQuasigroup"].includes(k) || get(eq, scope, "sideQuasigroup", s).status !== 2) &&
      ![1,2].includes(get(eq, scope, k, s).status)),
  };
}

// Several equations describe an image without answering the one-equation
// question. Keep this evidence separate from the nine question cells.
function imageBasisBoard(data, index, implications, ruleRefs) {
  const cells = new Map(), queue = [];
  const key = (eq, scope, side) => keyOf(eq, scope, "basis", side);
  function put(f) {
    const k = key(f.equation, f.scope, f.side), old = cells.get(k);
    if (old && old.targetLaws.length <= f.targetLaws.length) return;
    cells.set(k, f); queue.push(f);
  }
  function derive(f, changes, rule, details = {}) {
    if (!ruleRefs.has(rule)) throw Error(`Missing audited parastrophe rule: ${rule}`);
    put({...f, ...changes, steps: [...f.steps, {rule, ...details}]});
  }
  for (const [seed, r] of (data.imageBases || []).entries()) {
    if (!Number.isInteger(r.equation) || r.equation < 1 || r.equation > index.equations.length ||
        !["all", "fin"].includes(r.scope) || !["left", "right"].includes(r.side) ||
        r.status !== "PROVED" || !Array.isArray(r.targetLaws) || r.targetLaws.length < 2)
      throw Error("Invalid image-basis record");
    put({...r, seed, steps: []});
  }
  for (let i = 0; i < queue.length; i++) {
    const f = queue[i], {equation: eq, scope, side} = f;
    if (scope === "all") derive(f, {scope: "fin"}, "imageBasis_finite");
    const dual = index.duals[eq];
    if (!Number.isInteger(dual) || index.duals[dual] !== eq) throw Error("Invalid equation duality");
    derive(f, {equation: dual, side: swap(side),
      targetLaws: f.targetLaws.map(l => ({lhs: dualTree(l.lhs), rhs: dualTree(l.rhs)}))},
      "imageBasis_dual", {from: eq, to: dual});
    const board = implications[scope];
    if (board) for (const group of board.groups) {
      if (board.at(eq, group[0]) !== 1 || board.at(group[0], eq) !== 1) continue;
      for (const to of group) if (to !== eq)
        derive(f, {equation: to}, "imageBasis_of_equivalent", {from: eq, to, scope});
    }
  }
  return {get: (eq, scope, side) => cells.get(key(eq, scope, side))};
}
