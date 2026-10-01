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
    <label class="inline" title="Hide coarser classes containing exactly two finer classes exchanged by duality. Larger mergers remain visible even when some of their classes are dual."><input type="checkbox" id="nondual" name="nondual" value="1" ${p.get("nondual") === "1" ? "checked" : ""}> Hide collapses from duality alone</label>
    <input type="hidden" name="view" value="${view}"><button>Compare</button></form>
    <p class="comparison-presets">Presets: <a href="${mergerHref({ fine: "implies-all", coarse: "termStructural-fin", view })}">Implication → finite term structural</a> · <a href="${mergerHref({ fine: "termStructural-all", coarse: "structural-fin", view })}">All term structural → finite FO structural</a> · <a href="${mergerHref({ fine: "definable-fin", coarse: "spectrum-fin", view })}">Finite FO definable → spectra</a></p>`;
  const updateChoices = () => {
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
    const query = new URLSearchParams(form);
    raw ? query.set("eq", validEquation(raw)) : query.delete("eq");
    location.search = query;
  };
  $("merger-form").oninput = (event) => event.target.setCustomValidity?.("");
  if (!entails(fineKey, coarseKey))
    throw Error(
      "Choose comparable relations: the finer relation must entail the coarser one. FO structural and term definable are separate branches.",
    );
  const [index, fine, coarse, proofs] = await Promise.all([
    json("index"),
    relation(fineKey),
    relation(coarseKey),
    json("proofs"),
  ]);
  footer(index);
  const rows = partitions(fine, coarse),
    generators = mergerGenerators(fine, coarse, proofs),
    cache = new Map();
  // Compare dual classes, not just equation representatives: a representative's
  // dual may be a different member of the other finer class.
  const dualityOnly = new Set(
    rows
      .filter(
        (row) =>
          row.fine.length === 2 &&
          row.fine.every(
            (c, i) =>
              fine.classOf[index.duals[fine.groups[c][0]]] === row.fine[1 - i],
          ),
      )
      .map((row) => row.id),
  );
  const visibleByDuality = (row) =>
    !$("nondual").checked || !dualityOnly.has(row.id);
  function bindDualityFilter(apply) {
    $("nondual").onchange = () => {
      const enabled = $("nondual").checked,
        u = new URL(location);
      enabled ? p.set("nondual", "1") : p.delete("nondual");
      enabled
        ? u.searchParams.set("nondual", "1")
        : u.searchParams.delete("nondual");
      history.replaceState(null, "", u);
      apply();
      for (const link of document.querySelectorAll("a[href]")) {
        const target = new URL(link.href);
        if (
          target.origin !== location.origin ||
          !/\/mergers\/$/.test(target.pathname)
        )
          continue;
        enabled
          ? target.searchParams.set("nondual", "1")
          : target.searchParams.delete("nondual");
        link.href = target.href;
      }
    };
  }
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
    `<div class="stats"><div class="stat"><strong>${fine.classes}</strong>finer classes</div><div class="stat"><strong>${coarse.classes}</strong>coarser classes</div><div class="stat"><strong>${merged.length}</strong>coarser classes contain a merger</div><div class="stat"><strong>${fine.classes - coarse.classes}</strong>class identifications</div></div>
    <nav class="tabs" aria-label="Class comparison view"><a href="${url({ view: "table" })}" ${view === "table" ? 'aria-current="page"' : ""}>Merger catalogue</a><a href="${url({ view: "graph", eq: selected.members[0] })}" ${view === "graph" ? 'aria-current="page"' : ""}>Nested graph</a><a href="${href("implications", { relation: coarseKey.split("-")[0], flavour: coarseKey.split("-")[1], view: "unknown" })}">Unknown coarser directions</a></nav>
    <p class="panel"><strong>${esc(label(fineKey))} → ${esc(label(coarseKey))}.</strong> Each small node is one entire finer equivalence class. Shaded regions are proved coarser classes. Only proved arrows merge classes; unknown and conjectural arrows never do.${coarseKey === "spectrum-fin" ? " Spectrum regions group laws with proved equal positive finite spectra, even when finite FO equivalence is unproved or false." : ""}</p>
    <div class="merge-legend"><span class="key-inherited">━━ Finer arrow</span><span class="key-added">┄┄ Additional merger witness</span><span class="key-coarser">┄┄ Coarser arrow between regions</span><span class="key-unknown">··· Unknown coarser direction</span></div><div id="comparison-view"></div>`;
  const members = (c) =>
    `<span class="fine-class-pill">${eqLink(fine.groups[c][0], fineKey)} <small>${fine.groups[c].length} law${fine.groups[c].length === 1 ? "" : "s"}</small></span>`;
  function evidence(edge) {
    const source = edge.fact
      ? `<ul class="sources">${edge.fact.refs.map((r) => `<li>${sourceHTML(proofs.sources[r], index)}</li>`).join("")}</ul>${edge.fact.dual ? '<p class="muted">Apply the cited construction to the dual operation.</p>' : ""}`
      : "";
    const transfers = [];
    const a = fine.groups[edge.a]?.[0],
      b = fine.groups[edge.b]?.[0];
    if (a !== edge.s)
      transfers.push(
        `${eqLink(a, fineKey)} → E${edge.s} ${proofButton(a, edge.s, fineKey, 1)}`,
      );
    if (b !== edge.t)
      transfers.push(
        `E${edge.t} → ${eqLink(b, fineKey)} ${proofButton(edge.t, b, fineKey, 1)}`,
      );
    return `<p><strong>E${edge.s} → E${edge.t}</strong> · ${esc(label(edge.key))} ${proofButton(edge.s, edge.t, edge.key, 1)}</p>
      <p class="muted">In the finer relation: ${proofButton(edge.s, edge.t, fineKey, fine.at(edge.s, edge.t))}</p>${source}
      ${transfers.length ? `<details><summary>Transfers inside the finer classes</summary><p>${transfers.join(" · ")}</p></details>` : ""}`;
  }
  function explanation(row) {
    const w = witness(row);
    if (row.fine.length === 1)
      return "<p>This coarser class is already one finer class. No additional merger argument is needed.</p>";
    return `<p><strong>${w.nodes.length} finer classes become one.</strong> ${w.base.length} displayed finer arrows and ${w.added.length} added witness arrows suffice.</p>
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
          : showProof(e.s, e.t, e.key),
      node: (c) => {
        const group = fine.groups[c];
        showDetails(
          `Finer class E${group[0]} · ${label(fineKey)}`,
          `<p>${group.length} equations form this finer class.</p><div class="pills">${group.map((id) => eqLink(id, fineKey)).join("")}</div><p><a href="${href("implications", { relation: fineKey.split("-")[0], flavour: fineKey.split("-")[1], eq: group[0] })}">Inspect its equivalence proofs</a></p>`,
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
      <div class="table-wrap merger-table-wrap"><table><thead><tr><th>Coarser class</th><th>Finer classes inside it</th><th>Additional merger arguments</th></tr></thead><tbody id="merger-rows"></tbody></table></div>
      <div class="pager"><span id="page-info"></span><button id="previous" class="secondary">Previous</button><button id="next" class="secondary">Next</button></div></section>`;
    let page = 0,
      matching = [];
    const render = () => {
      $("merger-rows").innerHTML =
        matching
          .slice(page * 25, (page + 1) * 25)
          .map((row) => {
            const w = witness(row);
            return `<tr><td>${link(row, coarse.labels?.[row.id] || `E${row.members[0]}`)}<div class="muted">${row.members.length} laws · ${row.fine.length} finer classes</div>${link(row, "Nested graph ↗", { view: "graph" })}</td>
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
          visibleByDuality(row) &&
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
    bindDualityFilter(filter);
    filter();
  } else {
    $("comparison-view").innerHTML =
      `<section class="panel"><h2>Coarser class ${esc(coarse.labels?.[selected.id] || `E${selected.members[0]}`)}</h2>
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
            visibleByDuality(row) &&
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
      const chosen = visibleByDuality(selected)
        ? [
            selected,
            ...($("context").checked ? neighbours.slice(0, limit - 1) : []),
          ]
        : [];
      const { model, fit } = draw($("merge-graph"), chosen, {
        id: "full-merge",
        inherited: $("inherited").checked,
        added: $("added").checked,
        coarser: $("coarser").checked,
        unknown: $("unknown").checked,
        nodeLimit: Math.max(12, Math.floor(180 / Math.max(1, chosen.length))),
      });
      $("fit-merge").onclick = fit;
      $("fit-merge").disabled = $("download-merge").disabled = !chosen.length;
      $("merge-graph").hidden = $("merger-certificate").hidden = !chosen.length;
      const notes = [];
      if (!chosen.length)
        notes.push(
          "The focused class is hidden because its only merger is between dual finer classes. Uncheck ‘Hide collapses from duality alone’ to inspect it.",
        );
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
            `<tr><td>${esc(e.kind)}</td><td>E${e.s} → E${e.t}</td><td>${proofButton(e.s, e.t, e.key, e.kind === "unknown" ? 0 : 1)}</td></tr>`,
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
    bindDualityFilter(graph);
    graph();
  }
} catch (e) {
  error(e);
}
