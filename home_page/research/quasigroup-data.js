import {FIELDS} from "./parastrophes.js";

const descriptions = {
  quasigroup: "Every model has bijective rows and columns.",
  sideQuasigroup: "Every model has bijective translations on this side, so this division exists.",
  singleEquation: "One magma equation exactly characterizes the division image, among all magmas in this carrier scope. A negative excludes equations of every size, including beyond E4694.",
  term: "In each source model, a parameter-free binary term recovers division. The term may depend on the model.",
  uniformTerm: "One fixed parameter-free binary term recovers division in every source model.",
};
const labels = {
  quasigroup: "Quasigroup",
  sideQuasigroup: "Bijective translations",
  singleEquation: "Image characterized by one equation",
  term: "Division term per model",
  uniformTerm: "Uniform division term",
};
export const QUESTIONS = FIELDS.map(([kind, side]) => ({
  id: side ? `${kind}-${side}` : kind, kind, side,
  label: labels[kind], title: side ? `${side === "left" ? "Left" : "Right"}: ${labels[kind].toLowerCase()}` : labels[kind],
  description: descriptions[kind],
}));
export const FILTERS = [
  ["any", "Any status"], ["yes", "Proved yes"], ["no", "Proved no"],
  ["unproved", "Unproved (unknown or conjectural)"], ["unknown", "Unknown"],
  ["conjectural", "Conjectural"], ["na", "Not applicable"],
];
export const questionById = id => QUESTIONS.find(q => q.id === id) || QUESTIONS[2];

export function caseStatus(board, eq, scope, question) {
  if (!["quasigroup", "sideQuasigroup"].includes(question.kind) && !board.applicable(eq, scope, question.side)) return "na";
  return ["unknown", "yes", "no", "conjectural", "conjectural"][board.get(eq, scope, question.kind, question.side).status];
}

export function inventory(board, index) {
  return Object.fromEntries(["all", "fin"].map(scope => {
    const counts = Object.fromEntries(QUESTIONS.map(q => [q.id, {yes: 0, no: 0, unknown: 0, conjectural: 0, na: 0}]));
    let settled = 0;
    for (let eq = 1; eq <= index.equations.length; eq++) {
      if (!board.unproved(eq, scope)) settled++;
      for (const q of QUESTIONS) counts[q.id][caseStatus(board, eq, scope, q)]++;
    }
    return [scope, {counts, settled, total: index.equations.length}];
  }));
}

export function readState(params, total = 4694) {
  const number = value => /^\d+$/.test(value || "") && +value >= 1 && +value <= total ? +value : null;
  return {
    scope: params.get("flavour") === "all" ? "all" : "fin",
    question: questionById(params.get("question")).id,
    status: params.get("unproved") === "1" ? "unproved" :
      FILTERS.some(([id]) => id === params.get("status")) ? params.get("status") : "unproved",
    query: params.get("q") || "", focus: number(params.get("eq")),
    representatives: params.get("representatives") === "1",
    page: Math.max(1, Math.min(total, Number.parseInt(params.get("page"), 10) || 1)),
  };
}

export function stateParams(state) {
  const p = new URLSearchParams({flavour: state.scope, question: state.question, status: state.status});
  if (state.query) p.set("q", state.query);
  if (state.focus) p.set("eq", state.focus);
  if (state.status === "unproved") p.set("unproved", "1");
  if (state.representatives) p.set("representatives", "1");
  if (state.page > 1) p.set("page", state.page);
  return p;
}

export function matchingCases(board, index, implications, state) {
  const question = questionById(state.question), query = state.query.trim().toLowerCase();
  const id = /^e?\d+$/i.test(query) ? Number(query.replace(/^e/i, "")) : null;
  const groups = state.representatives ? implications[state.scope].groups : index.equations.map((_, i) => [i + 1]);
  return groups.map(members => ({eq: Math.min(...members), members})).filter(({eq, members}) => {
    const status = caseStatus(board, eq, state.scope, question);
    const matches = state.status === "any" || state.status === status ||
      state.status === "unproved" && ["unknown", "conjectural"].includes(status);
    return matches && (!query || (id !== null ? members.includes(id) :
      members.some(n => index.equations[n - 1].toLowerCase().includes(query))));
  }).sort((a, b) => a.eq - b.eq);
}
