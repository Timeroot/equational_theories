import {badge, eqLink, escapeHTML as esc, href, sourceHTML, proofButton, showDetails} from "./shared.js";
import {FIELDS, termText, lawText} from "./parastrophes.js";

const source = (ref, data) => data.local
  ? `<code>${esc(ref.name)}</code> <small>${esc(ref.file)}:${ref.line} · local source</small>`
  : sourceHTML(ref, data);
const RULE_HELP = {
  characterizes_otherSide: "An exact division correspondence preserves bijectivity, or a counterexample to bijectivity, on the other side. Every source model must have the division used in the correspondence.",
  quasigroup_side: "A quasigroup has bijective translations on each side (or contraposition).",
  sideQuasigroups_quasigroup: "Both one-sided properties together give a quasigroup. Conversely, a non-quasigroup counterexample plus one universally bijective side refutes the other side.",
  termRecovery_sideQuasigroup: "A division term supplies inverse translations on its own side (or contraposition).",
  sideQuasigroup_uniform_all: "On arbitrary carriers, bijectivity on this side gives a uniform division term using the free two-generated model (or contraposition).",
  sideQuasigroup_term_fin: "In each finite model, inverse translations on this side are powers of translations; the term can depend on model size (or contraposition).",
  characterizes_sideQuasigroup: "Every model in this division image has bijective translations on this side. No assertion about the other side is needed.",
  characterizes_symm: "Taking the same division twice recovers multiplication. Because every source model has this division, the exact characterization reverses.",
  characterizes_self: "Division is the original operation, so its image is exactly the source law; only this division is needed.",
  characterizes_opposite: "Division swaps the arguments, so its image is exactly the dual source law.",
  uniform_implies_term: "A single uniform term also provides a term for each model (or contraposition).",
  termRecovery_iff_uniform_all: "On arbitrary carriers, the free two-generated model makes term recovery uniform.",
  quasigroup_uniform_all: "A variety consisting of quasigroups has uniform division terms, obtained from its free two-generated model (or contraposition).",
  quasigroup_term_fin: "In each finite quasigroup, inverse translations are powers of translations; the exponent can depend on the size (or contraposition).",
  termRecovery_quasigroup: "Terms for both divisions give bijective rows and columns.",
  characterizes_quasigroup: "The source law forces both sides bijective, so its exact division image also forces both sides. This uses the additional source premise.",
};

export function compositionHTML(board) {
  const refs = ["division_symm", "division_opposite", "division_otherSide_iff", "right_after_left", "left_after_right"];
  return `<details><summary>How the parastrophes compose</summary><p>Write L for left division, R for right division, and O for the opposite operation. L(L(M)) = M and R(R(M)) = M wherever that division exists. O exchanges the sides: L(O(M)) = O(R(M)). When both sides exist, R(L(M)) = O(R(M)) and L(R(M)) = O(L(M)). A left-only quasigroup stays left-only after left division; the mixed step cannot create the missing side.</p><p>Lean proofs:</p><ul>${refs.map(n=>board.ruleRefs.get(n)).filter(Boolean).map(r=>`<li>${source(r,board.data)}</li>`).join("")}</ul></details>`;
}

export function cellHTML(board, eq, scope, kind, side = null) {
  const basis = kind === "singleEquation" && board.getBasis?.(eq, scope, side);
  const basisLink = basis ? `<div><button class="status-link" data-parastrophe="${eq},${scope},${kind},${side}" title="Exact characterization by several identities, with Lean proof">${basis.targetLaws.length}-equation basis</button></div>` : "";
  if (!["quasigroup", "sideQuasigroup"].includes(kind) && !board.applicable(eq, scope, side))
    return '<span class="muted" title="This law has a counterexample to bijective translations on this side. The other side is assessed independently.">Not applicable</span>' + basisLink;
  const cell = board.get(eq, scope, kind, side);
  if (!cell.status) return badge(0) + basisLink;
  const target = cell.positive && cell.targetEquation && kind === "singleEquation"
    ? ` <span class="parastrophe-target">E${cell.targetEquation}</span>` : "";
  const term = cell.positive && cell.term && ["term", "uniformTerm"].includes(kind)
    ? `<div class="parastrophe-term"><code>${esc(termText(cell.term))}</code></div>` : "";
  return `<button class="status-link" data-parastrophe="${eq},${scope},${kind},${side || ""}" title="View statement, witness, and Lean evidence">${badge(cell.status)}${target}</button>${term}${basisLink}`;
}

export function overviewHTML(board, eq) {
  return `<section class="panel"><h2>Quasigroup and parastrophe properties</h2><p>Left and right bijectivity are independent: a left quasigroup has bijective rows; a right quasigroup has bijective columns. Each division needs only its own side. “One equation” means an exact characterization among all magmas, not just a law the new operation satisfies. <a href="${href("parastrophes", {eq})}">Browse the parastrophe catalogue ↗</a></p><div class="table-wrap"><table class="parastrophe-table"><thead><tr><th>Models</th>${FIELDS.map(([, , label]) => `<th>${esc(label)}</th>`).join("")}</tr></thead><tbody>${["all", "fin"].map(scope => `<tr><th>${scope === "all" ? "Finite or infinite" : "Finite only"}</th>${FIELDS.map(([k,s]) => `<td>${cellHTML(board, eq, scope, k, s)}</td>`).join("")}</tr>`).join("")}</tbody></table></div><p class="muted">“Term per model” allows the term to depend on the magma; “uniform term” requires one fixed term for every model. These remain separate from exact characterization. Unknown means no proof or purported proof is recorded.</p>${consequencesHTML(board.data, eq)}${compositionHTML(board)}</section>`;
}

export function consequencesHTML(data, eq, scope = null, side = null) {
  const all = data.consequences || [], refs = new Map((data.consequenceSources || []).map(r => [r.name,r]));
  const seen = new Set();
  const facts = all.filter(c => {
    if (c.source !== eq && c.target !== eq || scope && c.scope !== scope || side && c.side !== side) return false;
    // A stronger fact already states its finite restriction and FO consequence.
    if (!scope && c.scope === "fin" && all.some(a => a.scope === "all" && a.source === c.source && a.target === c.target && a.side === c.side && a.kind === c.kind)) return false;
    if (c.kind === "structural" && all.some(a => a.kind === "termStructural" && a.scope === c.scope && a.source === c.source && a.target === c.target && a.side === c.side)) return false;
    const pair = c.kind === "fineSpectrum" ? [c.source,c.target].sort((a,b)=>a-b) : [c.source,c.target];
    const key = [c.kind,c.scope,c.side,...pair].join(":");
    if (seen.has(key)) return false;
    seen.add(key); return true;
  });
  if (!facts.length) return "";
  return `<h3>Automatically derived relationships</h3><ul>${facts.map(c => {
    const fine = c.kind === "fineSpectrum", key = `${fine ? "implies" : c.kind}-${c.scope}`;
    const meaning = fine ? "Same fine spectrum: equal numbers of labelled models and of models up to isomorphism" : c.kind === "termStructural" ? "Term-structural" : "FO-structural";
    return `<li>${eqLink(c.source,key)} ${fine ? "↔" : "→"} ${eqLink(c.target,key)} · ${meaning} · ${c.scope === "all" ? "all carriers" : "finite carriers"} · ${esc(c.side)} division. ${badge(1)}${fine ? "" : " " + proofButton(c.source,c.target,key,1)}<details><summary>Lean evidence</summary><ul>${c.refs.map(n => `<li>${source(refs.get(n),data)}</li>`).join("")}</ul><p>Generated theorem: <code>${esc(c.name)}</code></p></details></li>`;
  }).join("")}</ul>`;
}

export function proofHTML(board, eq, scope, kind, side) {
  const cell = board.get(eq, scope, kind, side), data = board.data;
  const label = FIELDS.find(([k,s]) => k === kind && s === side)?.[2] || kind;
  let html = `<p>${eqLink(eq, `implies-${scope}`)} · ${esc(label)} · ${scope === "all" ? "arbitrary carriers" : "finite carriers"}: ${badge(cell.status)}</p>`;
  const basis = kind === "singleEquation" && board.getBasis?.(eq, scope, side);
  if (basis) html += imageBasisHTML(board, basis);
  if (basis && !board.applicable(eq,scope,side))
    html += "<p>This describes the image of the source models that admit this division. Some source models do not admit it.</p>";
  if (!cell.status) return html + (basis
    ? "<p>Whether a single equation suffices remains unproved.</p>"
    : "<p>No purported proof or counterexample is recorded.</p>");
  const record = data.records[cell.seed];
  if (cell.targetLaw && cell.positive && kind === "singleEquation")
    html += `<p>Exact characterizing equation: ${cell.targetEquation ? eqLink(cell.targetEquation, `implies-${scope}`) : "outside the numbered catalogue"}.</p><p><code>${esc(lawText(cell.targetLaw))}</code></p>`;
  if (!cell.targetLaw && cell.targetEquation && cell.positive && kind === "singleEquation")
    html += `<p>Exact characterizing equation: ${eqLink(cell.targetEquation, `implies-${scope}`)}.</p>`;
  if (cell.term && cell.positive && ["term", "uniformTerm"].includes(kind))
    html += `<p>Division term in the original operation: <code>${esc(termText(cell.term))}</code>.</p>`;
  if (kind === "singleEquation" && !cell.positive)
    html += "<p>This refutes the existence of any single magma identity, with any finite number of variables and operations. It is stronger than excluding the numbered catalogue alone.</p>";
  html += `<h3>Source result</h3><p>${source(record, data)}</p>${record.description ? `<p class="proof-description">${esc(record.description)}</p>` : ""}`;
  if (kind === "singleEquation" && cell.positive)
    html += consequencesHTML(data, eq, scope, side);
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
      const support = [...(step.support ? [step.support] : []), ...(step.supports || [])].map(p => `<p>Additional premise: ${cellHTML(board, ...p)}</p>`).join("");
      html += `<li>${description || esc(step.rule)}${support}<p>${source(board.ruleRefs.get(step.rule), data)}</p></li>`;
    }
    html += "</ol>";
  }
  if (data.local) html += '<p class="muted">Local working-tree export. Source links become commit-pinned when the evidence is committed and the deployment bundle is refreshed.</p>';
  return html;
}

function imageBasisHTML(board, basis) {
  const record = board.data.imageBases[basis.seed];
  let html = `<h3>Exact ${basis.targetLaws.length}-equation characterization</h3><p>A magma is in this division image exactly when it satisfies every identity below. This is proved in Lean; it does not by itself settle whether one equation suffices.</p><ol>${basis.targetLaws.map(l => `<li><code>${esc(lawText(l))}</code></li>`).join("")}</ol><p>${source(record, board.data)}</p>`;
  if (record.description) html += `<p>${esc(record.description)}</p>`;
  if (basis.steps.length) html += `<p>Transfer of this basis:</p><ol>${basis.steps.map(step => {
    let text = step.rule === "imageBasis_finite" ? "Restrict to finite carriers."
      : step.rule === "imageBasis_dual" ? `Mirror every identity and swap the division side, from E${step.from} to E${step.to}.`
      : `Transfer through ordinary equivalence: ${eqLink(step.from,`implies-${step.scope}`)} ↔ ${eqLink(step.to,`implies-${step.scope}`)}. ${proofButton(step.from,step.to,`implies-${step.scope}`,1)} ${proofButton(step.to,step.from,`implies-${step.scope}`,1)}`;
    return `<li>${text}<p>${source(board.ruleRefs.get(step.rule),board.data)}</p></li>`;
  }).join("")}</ol>`;
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
