import {
  $,
  escapeHTML as esc,
  json,
  relation,
  shell,
  footer,
  error,
  href,
  eqLink,
  proofButton,
  badge,
  sourceHTML,
  showProof,
  showDetails,
  validEquation,
} from "./shared.js";
import {
  RELATION_KEYS,
  RELATION_LABELS,
  entails,
  partitions,
  quotientByDuality,
  mergerGenerators,
  mergeWitness,
} from "./relation-comparison.js";
import { mergeDiagram, bindDiagram } from "./merge-diagram.js";

shell(
  "mergers",
  "How equivalence classes merge",
  "Keep the finer classes visible, and see which additional constructions join them when the relation is weakened.",
);
const p = new URLSearchParams(location.search);
let fineKey = p.get("fine") || "implies-all",
  coarseKey = p.get("coarse") || "termStructural-fin";
const view = p.get("view") === "graph" ? "graph" : "table",
  focus = validEquation(p.get("eq"));
const label = (key) => RELATION_LABELS[RELATION_KEYS.indexOf(key)];
const options = (selected) =>
  RELATION_KEYS.map(
    (key, i) =>
      `<option value="${key}" ${key === selected ? "selected" : ""}>${RELATION_LABELS[i]}</option>`,
  ).join("");
const values = (extra) => ({
  fine: fineKey,
  coarse: coarseKey,
  view,
  ...(focus ? { eq: focus } : {}),
  ...extra,
});
const mergerHref = (values) =>
  href("mergers", {
    ...(p.get("nondual") === "1" ? { nondual: "1" } : {}),
    ...values,
  });
const url = (extra) => mergerHref(values(extra));
function link(row, text, extra = {}) {
  return `<a href="${url({ eq: row.members[0], ...extra })}">${esc(text)}</a>`;
}

try {
  $("controls").innerHTML = `<form id="merger-form" class="panel toolbar">
    <label>Finer classes<select id="fine" name="fine">${options(fineKey)}</select></label>
    <label>Coarser classes<select id="coarse" name="coarse">${options(coarseKey)}</select></label>
    <label>Focus equation<input name="eq" placeholder="e.g. 65 or 3342" value="${focus || ""}" inputmode="numeric"></label>
    <label class="inline" title="Identify dual implication classes before comparing. Counts, diagrams, and merger arguments then use classes up to duality. This already holds for structural, definable, and spectrum relations."><input type="checkbox" id="nondual" name="nondual" value="1" ${p.get("nondual") === "1" ? "checked" : ""}> Identify dual implication classes</label>
    <input type="hidden" name="view" value="${view}"><button>Compare</button></form>
    <p class="comparison-presets">Presets: <a href="${mergerHref({ fine: "implies-all", coarse: "termStructural-fin", view })}">Implication → finite term structural</a> · <a href="${mergerHref({ fine: "termStructural-all", coarse: "structural-fin", view })}">All term structural → finite FO structural</a> · <a href="${mergerHref({ fine: "definable-fin", coarse: "spectrum-fin", view })}">Finite FO definable → spectra</a></p>`;
  const updateChoices = () => {
    $("nondual").disabled = !$("fine").value.startsWith("implies-");
    for (const o of $("coarse").options)
      o.disabled = !entails($("fine").value, o.value);
    if ($("coarse").selectedOptions[0].disabled)
      $("coarse").value = $("fine").value;
  };
  $("fine").onchange = updateChoices;
  updateChoices();
  $("merger-form").onsubmit = (event) => {
    event.preventDefault();
    const form = new FormData(event.currentTarget),
      raw = String(form.get("eq") || "").trim();
    if (raw && !validEquation(raw)) {
      const input = event.currentTarget.elements.eq;
      input.setCustomValidity("Enter an equation number from 1 to 4694.");
      input.reportValidity();
      return;
    }
    const query = new URLSearchParams(location.search);
    for (const [name, value] of form) query.set(name, value);
    if (!form.has("nondual")) query.delete("nondual");
    if (validEquation(raw) !== focus) query.delete("q");
    raw ? query.set("eq", validEquation(raw)) : query.delete("eq");
    location.search = query;
  };
  $("merger-form").oninput = (event) => event.target.setCustomValidity?.("");
  $("nondual").onchange = () => $("merger-form").requestSubmit();
  if (!entails(fineKey, coarseKey))
    throw Error(
      "Choose comparable relations: the finer relation must entail the coarser one. FO structural and term definable are separate branches.",
    );
  const [index, originalFine, originalCoarse, proofs] = await Promise.all([
    json("index"),
    relation(fineKey),
    relation(coarseKey),
    json("proofs"),
  ]);
  footer(index);
  const useDuality = p.get("nondual") === "1" && fineKey.startsWith("implies-");
  const fine = useDuality
    ? quotientByDuality(originalFine, index.duals)
    : originalFine;
  const coarse = useDuality
    ? quotientByDuality(originalCoarse, index.duals)
    : originalCoarse;
  const fineSuffix = fine.upToDuality ? " up to duality" : "",
    coarseSuffix = coarse.upToDuality ? " up to duality" : "";
  const rows = partitions(fine, coarse),
    generators = mergerGenerators(fine, coarse, proofs),
    cache = new Map();
  const witness = (row) => {
    if (!cache.has(row.id))
      cache.set(row.id, mergeWitness(row, fine, coarse, generators));
    return cache.get(row.id);
  };
  const merged = rows.filter((r) => r.fine.length > 1),
    unsettled = new Set(coarse.possibleMerges.flat());
  const sorted = [...rows].sort(
    (a, b) => b.fine.length - a.fine.length || a.members[0] - b.members[0],
  );
  const selected = focus ? rows[coarse.classOf[focus]] : sorted[0];
  $("content").innerHTML =
    `<div class="stats"><div class="stat"><strong>${fine.classes}</strong>finer classes${fineSuffix}</div><div class="stat"><strong>${coarse.classes}</strong>coarser classes${coarseSuffix}</div><div class="stat"><strong>${merged.length}</strong>coarser classes contain a merger</div><div class="stat"><strong>${fine.classes - coarse.classes}</strong>class identifications</div></div>
    <nav class="tabs" aria-label="Class comparison view"><a href="${url({ view: "table" })}" ${view === "table" ? 'aria-current="page"' : ""}>Merger catalogue</a><a href="${url({ view: "graph", eq: selected.members[0] })}" ${view === "graph" ? 'aria-current="page"' : ""}>Nested graph</a><a href="${href("implications", { relation: coarseKey.split("-")[0], flavour: coarseKey.split("-")[1], view: "unknown" })}">Unknown coarser directions</a></nav>
    <p class="panel"><strong>${esc(label(fineKey))}${fineSuffix} → ${esc(label(coarseKey))}${coarseSuffix}.</strong> Each small node is one entire finer class${fineSuffix}. Shaded regions are coarser classes${coarseSuffix}. ${useDuality ? "Dual implication classes are identified first, including inside larger mergers. An implication arrow between these classes may use either orientation of the target law. " : ""}Only proved arrows and the selected duality identifications merge classes; unknown and conjectural arrows never do.${coarseKey === "spectrum-fin" ? " Spectrum regions group laws with proved equal positive finite spectra, even when finite FO equivalence is unproved or false." : ""}</p>
    <div class="merge-legend"><span class="key-inherited">━━ Finer arrow</span><span class="key-added">┄┄ Additional merger witness</span><span class="key-coarser">┄┄ Coarser arrow between regions</span><span class="key-unknown">··· Unknown coarser direction</span></div><div id="comparison-view"></div>`;
  const members = (c) => {
    const links = fine.upToDuality
      ? fine.parts[c]
          .map((part) => eqLink(fine.original.groups[part][0], fineKey))
          .join(" / ")
      : eqLink(fine.groups[c][0], fineKey);
    return `<span class="fine-class-pill">${links} <small>${fine.groups[c].length} law${fine.groups[c].length === 1 ? "" : "s"}</small></span>`;
  };
  const boardFor = (key) => (key === fine.key ? fine : coarse);
  function relationButton(s, t, board, status = board.at(s, t)) {
    return board.upToDuality
      ? `<button class="status-link" data-duality-proof="${s},${t},${board.key}" title="View implication evidence up to duality">${badge(status)}</button>`
      : proofButton(s, t, board.key, status);
  }
  function showQuotientProof(s, t, board) {
    const status = board.at(s, t),
      options = board.proofOptions(s, t);
    const directions =
      status === 1
        ? options.filter((e) => e.status === 1).slice(0, 1)
        : options;
    showDetails(
      `E${s} → E${t} · ${label(board.key)} up to duality`,
      `<p>${badge(status)} · up to duality</p><p>Dual implication classes are identified for this comparison. The arrow means E${s} implies E${t} <em>or its dual</em>. Select the underlying implication below for its Lean sources.</p>
      ${directions.map((e) => `<p><strong>E${e.s} → E${e.t}</strong>${e.t !== t ? ` (E${e.t} is the dual of E${t})` : ""} ${proofButton(e.s, e.t, board.key, e.status)}</p>`).join("")}`,
    );
  }
  document.addEventListener("click", (event) => {
    const button = event.target.closest("[data-duality-proof]");
    if (!button) return;
    const [s, t, key] = button.dataset.dualityProof.split(",");
    showQuotientProof(+s, +t, boardFor(key));
  });
  const edgeButton = (edge) =>
    edge.upToDuality
      ? relationButton(
          edge.s,
          edge.t,
          boardFor(edge.key),
          edge.kind === "unknown" ? 0 : 1,
        )
      : proofButton(edge.s, edge.t, edge.key, edge.kind === "unknown" ? 0 : 1);
  function evidence(edge) {
    const source = edge.fact
      ? `<ul class="sources">${edge.fact.refs.map((r) => `<li>${sourceHTML(proofs.sources[r], index)}</li>`).join("")}</ul>${edge.fact.dual ? '<p class="muted">Apply the cited construction to the dual operation.</p>' : ""}`
      : "";
    const transfers = [];
    const a = fine.groups[edge.a]?.[0],
      b = fine.groups[edge.b]?.[0];
    if (a !== edge.s)
      transfers.push(
        `${eqLink(a, fineKey)} → E${edge.s} ${relationButton(a, edge.s, fine, 1)}`,
      );
    if (b !== edge.t)
      transfers.push(
        `E${edge.t} → ${eqLink(b, fineKey)} ${relationButton(edge.t, b, fine, 1)}`,
      );
    return `<p><strong>E${edge.s} → E${edge.t}</strong> · ${esc(label(edge.key))}${edge.upToDuality ? " up to duality" : ""} ${edgeButton(edge)}</p>
      <p class="muted">In the finer relation${fineSuffix}: ${relationButton(edge.s, edge.t, fine)}</p>${source}
      ${transfers.length ? `<details><summary>Transfers inside the finer classes${fineSuffix}</summary><p>${transfers.join(" · ")}</p></details>` : ""}`;
  }
  function explanation(row) {
    const w = witness(row);
    if (row.fine.length === 1)
      return `<p>This coarser class is already one finer class${fineSuffix}. No additional merger argument is needed.</p>`;
    return `<p><strong>${w.nodes.length} finer classes${fineSuffix} become one.</strong> ${w.base.length} displayed finer arrows and ${w.added.length} added witness arrows suffice.</p>
      <p class="muted">${w.large ? "This large class uses a spanning certificate through one representative; it is not claimed minimal." : "The added arrows are irredundant: removing any one breaks this certificate. Another choice of constructions might use fewer arrows. Added arrows need not all point backward; they may join formerly unrelated classes."}</p>
      <div class="merger-witnesses">${w.added.map((e, i) => `<section><h3>Added arrow ${i + 1}</h3>${evidence(e)}</section>`).join("")}</div>`;
  }
  function draw(target, selectedRows, opts = {}) {
    const model = mergeDiagram(selectedRows, fine, coarse, witness, {
      ...opts,
      focus,
    });
    target.innerHTML = model.svg;
    const fit = bindDiagram(target, model, {
      edge: (e) =>
        e.fact
          ? showDetails(`Merger construction E${e.s} → E${e.t}`, evidence(e))
          : e.upToDuality
            ? showQuotientProof(e.s, e.t, boardFor(e.key))
            : showProof(e.s, e.t, e.key),
      node: (c) => {
        const group = fine.groups[c];
        showDetails(
          `Finer class E${group[0]} · ${label(fineKey)}${fineSuffix}`,
          fine.upToDuality
            ? `<p>${group.length} equations form this finer class up to duality. Its constituent implication classes are:</p>${fine.parts[
                c
              ]
                .map((part) => {
                  const g = fine.original.groups[part];
                  return `<h3>Implication class E${g[0]}</h3><div class="pills">${g.map((id) => eqLink(id, fineKey)).join("")}</div><p>${eqLink(g[0], fineKey, "Inspect this implication class's proofs")}</p>`;
                })
                .join("")}`
            : `<p>${group.length} equations form this finer class.</p><div class="pills">${group.map((id) => eqLink(id, fineKey)).join("")}</div><p><a href="${href("implications", { relation: fineKey.split("-")[0], flavour: fineKey.split("-")[1], eq: group[0] })}">Inspect its equivalence proofs</a></p>`,
        );
      },
    });
    return { model, fit };
  }
  if (view === "table") {
    $("comparison-view").innerHTML =
      `<section class="panel"><h2>Coarser classes and their merger arguments</h2>
      <div class="toolbar"><label class="grow">Find any member or equation formula<input id="search" type="search" value="${focus || ""}" placeholder="E1483 or x ◇ y"></label>
      <label class="inline"><input type="checkbox" id="changed" ${p.get("changed") !== "0" ? "checked" : ""}> Only classes that merge</label>
      <label class="inline"><input type="checkbox" id="unproved-mergers" ${p.get("unproved") === "1" ? "checked" : ""}> View only unproved separations</label></div>
      <p class="muted">The last filter keeps proved coarser classes that could still merge further. Each row lists finer classes, not individual equations.</p>
      <div class="table-wrap merger-table-wrap"><table><thead><tr><th>Coarser class${coarseSuffix}</th><th>Finer classes${fineSuffix} inside it</th><th>Additional merger arguments</th></tr></thead><tbody id="merger-rows"></tbody></table></div>
      <div class="pager"><span id="page-info"></span><button id="previous" class="secondary">Previous</button><button id="next" class="secondary">Next</button></div></section>`;
    let page = 0,
      matching = [];
    const render = () => {
      $("merger-rows").innerHTML =
        matching
          .slice(page * 25, (page + 1) * 25)
          .map((row) => {
            const w = witness(row);
            return `<tr><td>${link(row, coarse.labels?.[row.id] || `E${row.members[0]}`)}<div class="muted">${row.members.length} laws · ${row.fine.length} finer classes${fineSuffix}</div>${link(row, "Nested graph ↗", { view: "graph" })}</td>
          <td><div class="fine-class-list">${row.fine.map(members).join("")}</div></td>
          <td>${
            w.added.length
              ? `<p>${w.added.length} ${w.large ? "spanning" : "irredundant"} added arrows</p>${w.added
                  .slice(0, 4)
                  .map(
                    (e, i) =>
                      `<div class="compact-witness">E${e.s} → E${e.t} <button class="status-link" data-merger-proof="${row.id},${i}" title="Inspect the construction and its Lean sources">${badge(1)}</button></div>`,
                  )
                  .join(
                    "",
                  )}${w.added.length > 4 ? "<small>Remaining arrows in the certificate below.</small>" : ""}`
              : "<p>Already one finer class.</p>"
          }
          <details data-mini="${row.id}"><summary>Diagram, constructions, and Lean sources</summary><div class="mini-content"></div></details></td></tr>`;
          })
          .join("") ||
        '<tr><td colspan="3">No classes match these filters. Clear the search or relax the filters.</td></tr>';
      $("page-info").textContent = matching.length
        ? `${page * 25 + 1}–${Math.min((page + 1) * 25, matching.length)} of ${matching.length} coarser classes`
        : "No matching classes";
      $("previous").disabled = !page;
      $("next").disabled = (page + 1) * 25 >= matching.length;
    };
    const filter = () => {
      page = 0;
      const q = $("search")
        .value.trim()
        .toLowerCase()
        .replace(/^e(?=\d+$)/, "");
      matching = sorted.filter(
        (row) =>
          (!$("changed").checked || row.fine.length > 1) &&
          (!$("unproved-mergers").checked || unsettled.has(row.id)) &&
          (!q ||
            row.members.some((id) =>
              /^\d+$/.test(q)
                ? id === +q
                : index.equations[id - 1].toLowerCase().includes(q),
            )),
      );
      const u = new URL(location);
      q ? u.searchParams.set("q", q) : u.searchParams.delete("q");
      u.searchParams.set("changed", $("changed").checked ? "1" : "0");
      $("unproved-mergers").checked
        ? u.searchParams.set("unproved", "1")
        : u.searchParams.delete("unproved");
      history.replaceState(null, "", u);
      render();
    };
    if (p.has("q")) $("search").value = p.get("q");
    $("search").oninput =
      $("changed").onchange =
      $("unproved-mergers").onchange =
        filter;
    $("previous").onclick = () => {
      page--;
      render();
    };
    $("next").onclick = () => {
      page++;
      render();
    };
    $("merger-rows").onclick = (event) => {
      const button = event.target.closest("[data-merger-proof]");
      if (!button) return;
      const [row, i] = button.dataset.mergerProof.split(",").map(Number),
        edge = witness(rows[row]).added[i];
      showDetails(
        `Merger construction E${edge.s} → E${edge.t}`,
        evidence(edge),
      );
    };
    $("merger-rows").addEventListener(
      "toggle",
      (event) => {
        const detail = event.target;
        if (
          !detail.matches("details[data-mini]") ||
          !detail.open ||
          detail.dataset.loaded
        )
          return;
        detail.dataset.loaded = "1";
        const row = rows[+detail.dataset.mini],
          content = detail.querySelector(".mini-content");
        content.innerHTML = `<div class="merge-canvas mini-merge"></div><div class="mini-note"></div>${explanation(row)}`;
        const { model } = draw(content.querySelector(".merge-canvas"), [row], {
          id: `mini-${row.id}`,
        });
        content.querySelector(".mini-note").textContent = model.omitted
          ? `Diagram omits ${model.omitted} finer nodes; the full certificate is listed below.`
          : "Scroll to zoom, drag to pan, or select an arrow for its proof.";
      },
      true,
    );
    filter();
  } else {
    $("comparison-view").innerHTML =
      `<section class="panel"><h2>Coarser class${coarseSuffix} ${esc(coarse.labels?.[selected.id] || `E${selected.members[0]}`)}</h2>
      <p>${link(selected, "Read this merger in the catalogue", { view: "table" })} · ${eqLink(selected.members[0], coarseKey, "Explore this coarser class")}</p>
      <div class="toolbar"><label class="inline"><input id="context" type="checkbox" ${p.get("context") === "0" ? "" : "checked"}> Include neighbouring coarser classes</label>
      <label>Region limit<select id="region-limit">${[4, 8, 12, 20].map((n) => `<option ${n === +(p.get("limit") || 8) ? "selected" : ""}>${n}</option>`).join("")}</select></label>
      <label class="inline"><input id="inherited" type="checkbox" ${p.get("inherited") === "0" ? "" : "checked"}> Finer arrows</label><label class="inline"><input id="added" type="checkbox" ${p.get("added") === "0" ? "" : "checked"}> Merger witnesses</label>
      <label class="inline"><input id="coarser" type="checkbox" ${p.get("coarser") === "0" ? "" : "checked"}> Coarser region arrows</label><label class="inline"><input id="unknown" type="checkbox" ${p.get("unknown") === "1" ? "checked" : ""}> Unknown directions</label>
      <button id="fit-merge" class="secondary">Fit graph</button><button id="download-merge" class="secondary">Download SVG</button></div>
      <p class="muted">A coarser arrow connects whole regions; finer arrows keep their specific endpoints. Neighbours use cover relations in the full coarser order. Unknown arrows are questions, not merger arguments.</p></section>
      <p id="diagram-note" class="notice" hidden></p><div id="merge-graph" class="merge-canvas"></div><p>Drag to pan; scroll to zoom. Nodes and arrows also respond to Enter or Space.</p>
      <section class="panel" id="merger-certificate"><h2>The merger certificate for this class</h2>${explanation(selected)}</section>
      <details class="panel"><summary>Accessible table of visible arrows</summary><table><thead><tr><th>Kind</th><th>Direction</th><th>Evidence</th></tr></thead><tbody id="visible-arrows"></tbody></table></details>`;
    const graph = () => {
      const rep = (row) => row.members[0],
        f = rep(selected),
        neighbours = rows.filter(
          (row) =>
            row.id !== selected.id &&
            ((coarse.at(f, rep(row)) === 1 &&
              !rows.some(
                (m) =>
                  m.id !== selected.id &&
                  m.id !== row.id &&
                  coarse.at(f, rep(m)) === 1 &&
                  coarse.at(rep(m), rep(row)) === 1,
              )) ||
              (coarse.at(rep(row), f) === 1 &&
                !rows.some(
                  (m) =>
                    m.id !== selected.id &&
                    m.id !== row.id &&
                    coarse.at(rep(row), rep(m)) === 1 &&
                    coarse.at(rep(m), f) === 1,
                )) ||
              ($("unknown").checked &&
                (coarse.at(f, rep(row)) === 0 ||
                  coarse.at(rep(row), f) === 0))),
        );
      const limit = +$("region-limit").value;
      const chosen = [
        selected,
        ...($("context").checked ? neighbours.slice(0, limit - 1) : []),
      ];
      const { model, fit } = draw($("merge-graph"), chosen, {
        id: "full-merge",
        inherited: $("inherited").checked,
        added: $("added").checked,
        coarser: $("coarser").checked,
        unknown: $("unknown").checked,
        nodeLimit: Math.max(12, Math.floor(180 / Math.max(1, chosen.length))),
      });
      $("fit-merge").onclick = fit;
      const notes = [];
      if ($("context").checked && neighbours.length >= limit)
        notes.push(
          `Showing ${limit - 1} of ${neighbours.length} neighbouring regions; raise the region limit for more.`,
        );
      if (model.omitted)
        notes.push(
          `${model.omitted} finer nodes are omitted from this overview. The focused class's full certificate remains below; use the catalogue for every class.`,
        );
      $("diagram-note").hidden = !notes.length;
      $("diagram-note").textContent = notes.join(" ");
      $("visible-arrows").innerHTML = model.edges
        .map(
          (e) =>
            `<tr><td>${esc(e.kind)}${e.upToDuality ? " up to duality" : ""}</td><td>E${e.s} → E${e.t}</td><td>${edgeButton(e)}</td></tr>`,
        )
        .join("");
      $("download-merge").onclick = async () => {
        const svg = $("merge-graph").querySelector("svg");
        const copy = svg.cloneNode(true);
        copy.setAttribute("viewBox", `0 0 ${model.width} ${model.height}`);
        const css = await fetch(new URL("./style.css", import.meta.url)).then(
          (r) => r.text(),
        );
        const style = document.createElementNS(
          "http://www.w3.org/2000/svg",
          "style",
        );
        style.textContent = css;
        copy.prepend(style);
        const object = URL.createObjectURL(
          new Blob([new XMLSerializer().serializeToString(copy)], {
            type: "image/svg+xml",
          }),
        );
        const a = document.createElement("a");
        a.href = object;
        a.download = `mergers-${fineKey}-${coarseKey}.svg`;
        a.click();
        setTimeout(() => URL.revokeObjectURL(object), 1000);
      };
      const u = new URL(location);
      u.searchParams.set("eq", focus || selected.members[0]);
      u.searchParams.set("limit", limit);
      for (const id of ["context", "inherited", "added", "coarser", "unknown"])
        u.searchParams.set(id, $(id).checked ? "1" : "0");
      history.replaceState(null, "", u);
    };
    for (const id of [
      "context",
      "region-limit",
      "inherited",
      "added",
      "coarser",
      "unknown",
    ])
      $(id).onchange = graph;
    graph();
  }
} catch (e) {
  error(e);
}
