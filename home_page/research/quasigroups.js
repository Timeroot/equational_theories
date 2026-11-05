import {$, shell, escapeHTML as esc, eqLink, href, json, relation, error} from "./shared.js";
import {parastropheBoard} from "./parastrophes.js";
import {cellHTML, consequencesHTML, compositionHTML, bindParastropheProofs} from "./parastrophe-view.js";
import {QUESTIONS, FILTERS, questionById, inventory, readState, stateParams, matchingCases} from "./quasigroup-data.js";

shell("quasigroups", "Quasigroups & division images",
  "Start with the big picture, then explore the laws, constructions, and open questions behind each count.");
const scopeLabel = scope => scope === "all" ? "Arbitrary carriers" : "Finite carriers";
const format = n => n.toLocaleString();

try {
  const [index, data, all, fin] = await Promise.all([
    json("index"), json("parastrophes"), relation("implies-all"), relation("implies-fin"),
  ]);
  const implications = {all, fin}, board = parastropheBoard(data, index, implications);
  const totals = inventory(board, index);
  let state = readState(new URLSearchParams(location.search), index.equations.length);
  bindParastropheProofs(board);
  $("controls").innerHTML = `<div class="tabs"><a id="browse-cases" href="#cases">Browse cases ↓</a><a href="${href("parastrophes")}">Full parastrophe catalogue ↗</a></div>`;
  $("content").innerHTML = `
    <div class="division-overview-stats">${["all", "fin"].map(scope => `<section class="panel"><h2>${scopeLabel(scope)}</h2><p class="division-total"><strong>${format(totals[scope].settled)}</strong> / ${format(totals[scope].total)} laws fully settled</p><p class="muted">For a fully settled law, every applicable property has a Lean proof or refutation.</p></section>`).join("")}</div>
    <section class="panel" aria-labelledby="summary-title"><h2 id="summary-title">The classification at a glance</h2><p>Click a count to browse its laws. These totals count individual equations; left and right are shown separately. “Open” includes unknowns and conjectures.</p><div class="table-wrap division-summary-wrap"><table class="division-summary"><thead><tr><th scope="col">Property</th><th scope="col">Arbitrary carriers<br><small>Finite or infinite</small></th><th scope="col">Finite carriers</th></tr></thead><tbody id="summary-rows"></tbody></table></div><p class="muted">Division questions are not applicable when some source model lacks that division. A failure on one side does not suppress questions about the other.</p></section>
    <details class="panel"><summary>What these questions mean</summary><p>Left division solves <code>x ◇ z = y</code> for z. Right division solves <code>z ◇ y = x</code>. Each needs only its own translations to be bijective. A quasigroup has both.</p><p><strong>One equation</strong> means an exact description of the division image, with a converse. Merely satisfying an equation is not enough. An image may have a proved basis of several equations while the single-equation question remains open.</p><p><strong>Term per model</strong> allows different terms for different magmas. <strong>Uniform term</strong> requires the same term for every model. These questions remain meaningful even when the image cannot be characterized by one equation.</p><p>Proved results and their transfers link to Lean. Conjectural means a purported argument awaits Lean formalization; unknown means no purported proof is recorded.</p>${compositionHTML(board)}</details>
    <section class="panel" id="cases" aria-labelledby="cases-title"><h2 id="cases-title">Explore the cases</h2>
      <form id="case-controls" class="toolbar">
        <label class="grow">Property<select id="case-question">${QUESTIONS.map(q => `<option value="${q.id}">${esc(q.title)}</option>`).join("")}</select></label>
        <label>Models<select id="case-scope"><option value="all">Finite or infinite</option><option value="fin">Finite only</option></select></label>
        <label>Evidence<select id="case-status">${FILTERS.map(([id, label]) => `<option value="${id}">${esc(label)}</option>`).join("")}</select></label>
        <label>Find a law<input id="case-query" type="search" placeholder="E477 or an equation fragment"></label>
        <label class="inline" title="Group only by mutual ordinary implication in the selected carrier scope. Structural equivalence need not preserve these properties."><input id="case-representatives" type="checkbox"> Show only equivalence class representative</label>
        <button type="submit">Apply</button>
      </form>
      <p id="case-description" class="muted"></p><p id="case-count" role="status"></p>
      <div class="table-wrap division-cases-wrap"><table class="division-cases"><thead><tr><th scope="col">Law</th><th scope="col" id="selected-scope"></th><th scope="col" id="other-scope"></th><th scope="col">Explore</th></tr></thead><tbody id="case-rows"></tbody></table></div>
      <div class="pager"><button type="button" class="secondary" id="case-previous">Previous</button><span id="case-page"></span><button type="button" class="secondary" id="case-next">Next</button></div>
    </section><section id="law-details"></section>`;
  $("build-info").textContent = `Data generated ${new Date(data.generated).toLocaleString()}${data.local ? " · local preview" : ` · ${data.repository} @ ${data.commit.slice(0, 8)}`}.`;

  function link(changes, hash = "cases") {
    return `?${stateParams({...state, ...changes})}#${hash}`;
  }
  function countsHTML(scope, q) {
    const c = totals[scope].counts[q.id];
    return `<div class="division-counts">${[["yes", "Yes", c.yes], ["no", "No", c.no], ["unproved", "Open", c.unknown + c.conjectural]].map(([status, label, count]) =>
      `<a class="division-count count-${status}" href="${esc(link({scope, question: q.id, status, query: "", focus: null, page: 1}))}" data-count="${scope},${q.id},${status}" aria-label="${esc(`${q.title}, ${scopeLabel(scope)}, ${label}: ${format(count)} laws`)}" ${state.scope === scope && state.question === q.id && state.status === status ? 'aria-current="true"' : ""}><span>${label}</span><strong>${format(count)}</strong></a>`).join("")}</div>${c.conjectural ? `<small>${format(c.conjectural)} open ${c.conjectural === 1 ? "case has" : "cases have"} a conjectural answer.</small>` : ""}${c.na ? `<a class="division-na" href="${esc(link({scope, question: q.id, status: "na", query: "", focus: null, page: 1}))}" data-count="${scope},${q.id},na">${format(c.na)} not applicable</a>` : ""}`;
  }
  function render() {
    for (const anchor of document.querySelectorAll("header nav a, #controls a")) {
      const url = new URL(anchor.href);
      if (url.origin !== location.origin || !/\/(implications|graphiti|mergers|spectrum|parastrophes|quasigroups)\/$/.test(url.pathname)) continue;
      for (const [flag, enabled] of [["unproved", state.status === "unproved"], ["representatives", state.representatives]])
        enabled ? url.searchParams.set(flag, "1") : url.searchParams.delete(flag);
      anchor.href = url;
    }
    const question = questionById(state.question), other = state.scope === "all" ? "fin" : "all";
    $("summary-rows").innerHTML = QUESTIONS.map(q => `<tr><th scope="row" title="${esc(q.description)}">${q.side ? `<span class="division-side">${q.side === "left" ? "Left division" : "Right division"}</span>` : ""}${esc(q.label)}</th>${["all", "fin"].map(scope => `<td>${countsHTML(scope, q)}</td>`).join("")}</tr>`).join("");
    $("case-question").value = state.question;
    $("case-scope").value = state.scope;
    $("case-status").value = state.status;
    $("case-query").value = state.query;
    $("case-representatives").checked = state.representatives;
    $("case-description").textContent = question.description;
    const matches = matchingCases(board, index, implications, state), pages = Math.max(1, Math.ceil(matches.length / 30));
    state.page = Math.min(state.page, pages);
    $("browse-cases").href = link({});
    const laws = matches.reduce((n, row) => n + row.members.length, 0);
    const noun = state.representatives ? `implication ${matches.length === 1 ? "class" : "classes"} (${format(laws)} ${laws === 1 ? "law" : "laws"})` : matches.length === 1 ? "law" : "laws";
    $("case-count").textContent = `${format(matches.length)} ${noun} ${matches.length === 1 ? "matches" : "match"} · ${question.title} · ${scopeLabel(state.scope).toLowerCase()}.`;
    $("selected-scope").textContent = `${scopeLabel(state.scope)} · selected`;
    $("other-scope").textContent = `${scopeLabel(other)} · comparison`;
    $("case-rows").innerHTML = matches.slice((state.page - 1) * 30, state.page * 30).map(({eq, members}) => `<tr>
      <th scope="row"><a href="${esc(link({focus: eq}, "law-details"))}" data-law="${eq}">E${eq}</a><div class="division-law">${esc(index.equations[eq - 1])}</div>${members.length > 1 ? `<details><summary>${format(members.length)} equivalent laws</summary><div class="pills">${members.map(n => `<a href="${esc(link({focus: n}, "law-details"))}" data-law="${n}">E${n}</a>`).join(" ")}</div></details>` : ""}</th>
      <td data-label="${scopeLabel(state.scope)}">${cellHTML(board, eq, state.scope, question.kind, question.side)}</td>
      <td data-label="${scopeLabel(other)}">${cellHTML(board, eq, other, question.kind, question.side)}</td>
      <td><a href="${esc(link({focus: eq}, "law-details"))}" data-law="${eq}">All properties</a><br>${eqLink(eq, `implies-${state.scope}`, "Equation Explorer ↗")}</td></tr>`).join("") || '<tr><td colspan="4">No matching laws. Try another property, status, or search.</td></tr>';
    $("case-page").textContent = `Page ${state.page} of ${pages}`;
    $("case-previous").disabled = state.page === 1;
    $("case-next").disabled = state.page === pages;
    const eq = state.focus;
    $("law-details").innerHTML = eq ? `<div class="panel"><div class="division-detail-heading"><h2>E${eq}: all properties</h2><a href="${esc(link({focus: null}))}" data-clear-law>Close law details</a></div><p class="equation">${esc(index.equations[eq - 1])}</p><p>${eqLink(eq, `implies-${state.scope}`, "Open in Equation Explorer ↗")} · <a href="${esc(link({focus: index.duals[eq]}, "law-details"))}" data-law="${index.duals[eq]}">Dual: E${index.duals[eq]}</a> · <a href="${href("parastrophes", {eq, flavour: state.scope})}">Full parastrophe catalogue ↗</a></p><div class="table-wrap division-summary-wrap"><table class="division-properties"><thead><tr><th scope="col">Property</th><th scope="col">Arbitrary carriers</th><th scope="col">Finite carriers</th></tr></thead><tbody>${QUESTIONS.map(q => `<tr><th scope="row">${esc(q.title)}</th>${["all", "fin"].map(scope => `<td>${cellHTML(board, eq, scope, q.kind, q.side)}</td>`).join("")}</tr>`).join("")}</tbody></table></div>${consequencesHTML(data, eq)}</div>` : "";
  }
  function navigate(changes, target) {
    state = {...state, ...changes};
    history.pushState(null, "", `${location.pathname}?${stateParams(state)}${target ? `#${target}` : ""}`);
    render();
    if (target) $(target).scrollIntoView({block: "start"});
  }
  $("content").addEventListener("click", event => {
    if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const count = event.target.closest("[data-count]"), law = event.target.closest("[data-law]");
    if (count) {
      event.preventDefault();
      const [scope, question, status] = count.dataset.count.split(",");
      navigate({scope, question, status, query: "", focus: null, page: 1}, "cases");
    } else if (law) {
      event.preventDefault(); navigate({focus: +law.dataset.law}, "law-details");
    } else if (event.target.closest("[data-clear-law]")) {
      event.preventDefault(); navigate({focus: null}, "cases");
    }
  });
  $("case-controls").onsubmit = event => {
    event.preventDefault();
    navigate({question: $("case-question").value, scope: $("case-scope").value, status: $("case-status").value,
      query: $("case-query").value.trim(), representatives: $("case-representatives").checked, focus: null, page: 1}, "cases");
  };
  $("case-previous").onclick = () => navigate({page: state.page - 1}, "cases");
  $("case-next").onclick = () => navigate({page: state.page + 1}, "cases");
  window.addEventListener("popstate", () => {
    state = readState(new URLSearchParams(location.search), index.equations.length); render();
    if (["cases", "law-details"].includes(location.hash.slice(1))) $(location.hash.slice(1)).scrollIntoView();
  });
  render();
  if (["cases", "law-details"].includes(location.hash.slice(1))) $(location.hash.slice(1)).scrollIntoView();
} catch (e) { error(e); }
