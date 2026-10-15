import {badge, eqLink, escapeHTML as esc, href, sourceHTML, proofButton, showDetails} from "./shared.js";
import {FIELDS, termText, lawText} from "./parastrophes.js";

const source = (ref, data) => data.local
  ? `<code>${esc(ref.name)}</code> <small>${esc(ref.file)}:${ref.line} · local source</small>`
  : sourceHTML(ref, data);
const RULE_HELP = {
  uniform_implies_term: "A single uniform term also provides a term for each model (or contraposition).",
  termRecovery_iff_uniform_all: "On arbitrary carriers, the free two-generated model makes term recovery uniform.",
  quasigroup_uniform_all: "A variety consisting of quasigroups has uniform division terms, obtained from its free two-generated model (or contraposition).",
  quasigroup_term_fin: "In each finite quasigroup, inverse translations are powers of translations; the exponent can depend on the size (or contraposition).",
  termRecovery_quasigroup: "Terms for both divisions give bijective rows and columns.",
  characterizes_quasigroup: "Every magma in the parastrophic image is a quasigroup, so its exact characterizing law forces a quasigroup.",
};

export function cellHTML(board, eq, scope, kind, side = null) {
  if (kind !== "quasigroup" && !board.applicable(eq, scope))
    return '<span class="muted" title="This law has a proved non-quasigroup model in this scope; these fields are questions about quasigroup laws.">Not applicable</span>';
  const cell = board.get(eq, scope, kind, side);
  if (!cell.status) return badge(0);
  const target = cell.positive && cell.targetEquation && kind === "singleEquation"
    ? ` <span class="parastrophe-target">E${cell.targetEquation}</span>` : "";
  const term = cell.positive && cell.term && ["term", "uniformTerm"].includes(kind)
    ? `<div class="parastrophe-term"><code>${esc(termText(cell.term))}</code></div>` : "";
  return `<button class="status-link" data-parastrophe="${eq},${scope},${kind},${side || ""}" title="View statement, witness, and Lean evidence">${badge(cell.status)}${target}</button>${term}`;
}

export function overviewHTML(board, eq) {
  return `<section class="panel"><h2>Quasigroup and parastrophe properties</h2><p>These concern the actual left and right division operations. “One equation” means an exact characterization among all magmas, not just a law the new operation satisfies. <a href="${href("parastrophes", {eq})}">Browse the parastrophe catalogue ↗</a></p><div class="table-wrap"><table class="parastrophe-table"><thead><tr><th>Models</th>${FIELDS.map(([, , label]) => `<th>${esc(label)}</th>`).join("")}</tr></thead><tbody>${["all", "fin"].map(scope => `<tr><th>${scope === "all" ? "Finite or infinite" : "Finite only"}</th>${FIELDS.map(([k,s]) => `<td>${cellHTML(board, eq, scope, k, s)}</td>`).join("")}</tr>`).join("")}</tbody></table></div><p class="muted">“Term per model” allows the term to depend on the magma; “uniform term” requires one fixed term for every model. These remain separate from exact characterization. Unknown means no proof or purported proof is recorded.</p></section>`;
}

export function proofHTML(board, eq, scope, kind, side) {
  const cell = board.get(eq, scope, kind, side), data = board.data;
  const label = FIELDS.find(([k,s]) => k === kind && s === side)?.[2] || kind;
  let html = `<p>${eqLink(eq, `implies-${scope}`)} · ${esc(label)} · ${scope === "all" ? "arbitrary carriers" : "finite carriers"}: ${badge(cell.status)}</p>`;
  if (!cell.status) return html + "<p>No purported proof or counterexample is recorded.</p>";
  const record = data.records[cell.seed];
  if (cell.targetLaw && cell.positive && kind === "singleEquation")
    html += `<p>Exact characterizing equation: ${cell.targetEquation ? eqLink(cell.targetEquation, `implies-${scope}`) : "outside the numbered catalogue"}.</p><p><code>${esc(lawText(cell.targetLaw))}</code></p>`;
  if (cell.term && cell.positive && ["term", "uniformTerm"].includes(kind))
    html += `<p>Division term in the original operation: <code>${esc(termText(cell.term))}</code>.</p>`;
  if (kind === "singleEquation" && !cell.positive)
    html += "<p>This refutes the existence of any single magma identity, with any finite number of variables and operations. It is stronger than excluding the numbered catalogue alone.</p>";
  html += `<h3>Source result</h3><p>${source(record, data)}</p>${record.description ? `<p class="proof-description">${esc(record.description)}</p>` : ""}`;
  if (cell.steps.length) {
    html += "<h3>Transfer to this cell</h3><ol>";
    for (const step of cell.steps) {
      let description = RULE_HELP[step.rule];
      if (step.rule.endsWith("_finite")) description = "Restrict a positive theorem to finite models, or use a finite negative to refute the arbitrary-carrier claim.";
      if (step.rule.endsWith("_dual")) description = `Pass from E${step.from} to its dual E${step.to}; swap left/right, take the opposite target law, and mirror and swap inputs in any displayed term.`;
      if (step.rule.endsWith("_of_implies") || step.rule === "singleEquation_of_equivalent") {
        description = `Transfer from E${step.from} to E${step.to} by ${step.equivalent ? "ordinary implication equivalence" : "ordinary implication"}.`;
        const arrows = step.equivalent ? [[step.to,step.from],[step.from,step.to]]
          : step.positive ? [[step.to,step.from]] : [[step.from,step.to]];
        description += " " + arrows.map(([a,b]) => `E${a} → E${b}: ${proofButton(a,b,`implies-${step.scope}`,1)}`).join(" · ");
      }
      const support = step.support ? `<p>Other division premise: ${cellHTML(board, ...step.support)}</p>` : "";
      html += `<li>${description || esc(step.rule)}${support}<p>${source(board.ruleRefs.get(step.rule), data)}</p></li>`;
    }
    html += "</ol>";
  }
  if (data.local) html += '<p class="muted">Local working-tree export. Source links become commit-pinned when the evidence is committed and the deployment bundle is refreshed.</p>';
  return html;
}

export function bindParastropheProofs(board) {
  document.addEventListener("click", event => {
    const button = event.target.closest("[data-parastrophe]");
    if (!button) return;
    const [eq, scope, kind, side] = button.dataset.parastrophe.split(",");
    showDetails("Parastrophe evidence", proofHTML(board, +eq, scope, kind, side || null));
  });
}
