import {
  $,
  VIEW_KEYS,
  relationLabel,
  escapeHTML as esc,
  json,
  relation,
  params,
  keyOf,
  href,
  eqLink,
  badge,
  proofButton,
  shell,
  controls,
  footer,
  error,
  validEquation,
  sourceHTML,
  isUnproved,
  unsettledClasses,
  bindUnproved,
  representativesControl,
  bindRepresentatives,
} from "./shared.js";
import {
  unknownDirections,
  filterUnknownDirections,
} from "./unknown-directions.js";
shell(
  "implications",
  "Equation Explorer",
  "Explore implications, definability, structural relations, spectrum inclusion, and their equivalence classes.",
);
const p = params(),
  key = keyOf(p),
  eq = validEquation(p.get("eq")),
  view = ["equation", "classes", "unknown", "open"].includes(p.get("view"))
    ? p.get("view")
    : eq
      ? "equation"
      : "classes";
controls(
  p,
  `${representativesControl(p)}<label>Equation<input id="equation-input" name="eq" placeholder="e.g. 1485" value="${eq || ""}" inputmode="numeric" pattern="[Ee]?[0-9]+"></label><input type="hidden" name="view" value="${view}">`,
);
try {
  const [index, board] = await Promise.all([json("index"), relation(key)]);
  footer(index);
  const common = { relation: p.get("relation"), flavour: p.get("flavour") };
  const unknown = unknownDirections(board);
  const tabs = [
    ["equation", "Equation"],
    ["classes", "Equivalence classes"],
    ["unknown", `Unknown directions (${unknown.length.toLocaleString()})`],
    ["open", "Possible class merges"],
  ]
    .map(
      ([v, n]) =>
        `<a href="${href("implications", { ...common, view: v, ...(eq ? { eq } : {}) })}" ${v === view ? 'aria-current="page"' : ""}>${n}</a>`,
    )
    .join("");
  $("content").innerHTML =
    `<p class="panel"><strong>A → B:</strong> ${esc(board.description)} ${board.flavour === "fin" ? "Here the source magma must be finite." : "Here the source magma may be finite or infinite."}${key.startsWith("implies") || key === "spectrum-fin" ? "" : " The defining term or formula may depend on the source magma."}</p><nav class="tabs" aria-label="Explorer view">${tabs}<a href="${href("graphiti", { ...common, ...(eq ? { eq } : {}) })}">View graph ↗</a><a href="${href("mergers", { fine: "implies-all", coarse: key.startsWith("implies") ? "termStructural-fin" : key, ...(eq ? { eq } : {}) })}">How classes merge ↗</a></nav><div id="view"></div>`;
  let refreshUnproved = () => {};
  if (view === "equation") renderEquation(eq || 2);
  else if (view === "unknown") renderUnknown();
  else if (view === "open") renderOpen();
  else renderClasses();
  bindUnproved(p, () => refreshUnproved());
  bindRepresentatives(p, () => {
    const members = $("class-members");
    if (members)
      members.innerHTML = classMembers(
        board.groups[board.classOf[eq || 2]],
        eq || 2,
      );
    refreshUnproved();
  });

  function equationText(id) {
    return esc(index.equations[id - 1]);
  }
  function classDescription(id) {
    return key === "spectrum-fin"
      ? esc(board.labels[board.classOf[id]])
      : equationText(id);
  }
  function updateParams(values) {
    const url = new URL(location);
    for (const [name, value] of Object.entries(values)) {
      if (value) {
        p.set(name, value);
        url.searchParams.set(name, value);
      } else {
        p.delete(name);
        url.searchParams.delete(name);
      }
    }
    history.replaceState(null, "", url);
  }
  function classMembers(group, against = group[0]) {
    const members = $("representatives").checked ? group.slice(0, 1) : group;
    return `<div class="pills">${members.map((i) => `<a href="${href("implications", { ...common, eq: i, target: against })}">E${i}</a>`).join("")}</div>`;
  }
  function pagination(rows, render, target = "rows", size = 60) {
    let page = 0;
    const show = () => {
      $(target).innerHTML = render(rows.slice(page * size, (page + 1) * size));
      $("page-info").textContent = rows.length
        ? `${page * size + 1}–${Math.min((page + 1) * size, rows.length)} of ${rows.length.toLocaleString()}`
        : "No matches";
      $("previous").disabled = page === 0;
      $("next").disabled = (page + 1) * size >= rows.length;
    };
    $("previous").onclick = () => {
      page--;
      show();
    };
    $("next").onclick = () => {
      page++;
      show();
    };
    show();
  }
  function pager() {
    return '<div class="pager"><span id="page-info"></span><button class="secondary" id="previous">Previous</button><button class="secondary" id="next">Next</button></div>';
  }
  function renderClasses() {
    const unsettled = unsettledClasses(board);
    $("view").innerHTML =
      `<section class="panel"><h2>${board.classes.toLocaleString()} proved equivalence classes</h2><p>Two equations share a class exactly when both directions are proved for this relation.${key === "spectrum-fin" ? " Equal spectra can identify laws beyond finite FO definability. A question mark means the exact spectrum is unknown; identical guesses or initial segments do not merge classes." : ""} ${board.unresolved_equivalence_pairs ? `${board.unresolved_equivalence_pairs.toLocaleString()} pairs of these classes could still merge.` : "Every pair of distinct classes has a proved separation in at least one direction: this classification is complete."}</p><p class="muted">“View only unproved” keeps classes whose separation from another class is not yet proved: they could still merge.</p><label>Find an equation or formula <input id="class-search" type="search" placeholder="1485 or x ◇ y"></label><div class="table-wrap"><table><thead><tr><th>Representative</th><th>${key === "spectrum-fin" ? "Spectrum" : "Equation"}</th><th>Members</th></tr></thead><tbody id="rows"></tbody></table></div>${pager()}</section>`;
    const show = () => {
      const q = $("class-search")
        .value.trim()
        .toLowerCase()
        .replace(/^e(?=\d+$)/, "");
      const groups = board.groups.filter(
        (g, c) =>
          (!$("unproved").checked || unsettled.has(c)) &&
          (!q ||
            (/^\d+$/.test(q)
              ? g.includes(+q)
              : g.some((i) =>
                  index.equations[i - 1].toLowerCase().includes(q),
                ))),
      );
      pagination(groups, (gs) =>
        gs
          .map(
            (g) =>
              `<tr><td>${eqLink(g[0], key)}</td><td><code>${classDescription(g[0])}</code></td><td>${$("representatives").checked ? `${g.length} equation${g.length === 1 ? "" : "s"}` : `<details><summary>${g.length} equation${g.length === 1 ? "" : "s"}</summary>${classMembers(g)}</details>`}</td></tr>`,
          )
          .join(""),
      );
    };
    refreshUnproved = show;
    $("class-search").oninput = show;
    show();
  }
  function renderOpen() {
    $("view").innerHTML =
      `<section class="panel"><h2>Possible class merges</h2><p>${board.unresolved_equivalence_pairs.toLocaleString()} unordered class pairs have no proved negative in either direction. A conjectural result does not settle a class separation. Click either status to inspect its evidence.</p><label>Filter by equation <input id="merge-search" placeholder="e.g. 3342" inputmode="numeric"></label><div class="table-wrap"><table><thead><tr><th>A</th><th>B</th><th>A → B</th><th>B → A</th></tr></thead><tbody id="rows"></tbody></table></div>${pager()}</section>`;
    const show = () => {
      const id = validEquation($("merge-search").value),
        c = id ? board.classOf[id] : null;
      const pairs = board.possibleMerges.filter(
        ([a, b]) => c === null || a === c || b === c,
      );
      pagination(pairs, (ps) =>
        ps
          .map(([a, b]) => {
            const s = board.groups[a][0],
              t = board.groups[b][0];
            return `<tr><td>${eqLink(s, key)}</td><td>${eqLink(t, key)}</td><td>${proofButton(s, t, key, board.at(s, t))}</td><td>${proofButton(t, s, key, board.at(t, s))}</td></tr>`;
          })
          .join(""),
      );
    };
    refreshUnproved = show;
    $("merge-search").oninput = show;
    show();
  }
  function renderUnknown() {
    $("view").innerHTML =
      `<section class="panel"><h2>Unknown directions</h2><p>${unknown.length.toLocaleString()} directed class pairs have no purported proof or disproof in the database for this relation and magma scope. Conjectural results are excluded.</p><p class="muted">Each row uses representatives of two proved equivalence classes. An unknown direction remains here even when the reverse direction is proved false; see “Possible class merges” for the separate question of which classes might coincide. Every row is already unproved, so “View only unproved” adds no filter here.</p><div class="toolbar"><label class="grow">Find equation or formula<input id="unknown-search" type="search" placeholder="e.g. 1485 or x ◇ y" value="${esc(p.get("q") || "")}"></label><label>Match in<select id="unknown-side"><option value="either">Either class</option><option value="source">Source class A</option><option value="target">Target class B</option></select></label></div><p class="count-note">Select a status to inspect its evidence, or an equation to explore that class.</p><div class="table-wrap"><table><thead><tr><th>Source class A</th><th>Target class B</th><th>A → B</th><th>B → A</th></tr></thead><tbody id="rows"></tbody></table></div>${pager()}</section>`;
    $("unknown-side").value = ["source", "target"].includes(p.get("side"))
      ? p.get("side")
      : "either";
    const classCell = (c) => {
      const group = board.groups[c],
        id = group[0];
      return `${eqLink(id, key)} <small class="muted">· ${group.length} equation${group.length === 1 ? "" : "s"}</small><div><code>${classDescription(id)}</code></div>`;
    };
    const show = () => {
      const query = $("unknown-search").value,
        side = $("unknown-side").value;
      updateParams({ q: query || null, side: side === "either" ? null : side });
      const pairs = filterUnknownDirections(
        unknown,
        board,
        index.equations,
        query,
        side,
      );
      pagination(pairs, (ps) =>
        ps.length
          ? ps
              .map(([a, b]) => {
                const s = board.groups[a][0],
                  t = board.groups[b][0];
                return `<tr><td>${classCell(a)}</td><td>${classCell(b)}</td><td>${proofButton(s, t, key, 0)}</td><td>${proofButton(t, s, key, board.at(t, s))}</td></tr>`;
              })
              .join("")
          : `<tr><td colspan="4">${unknown.length ? "No unknown directions match this search." : "No unknown directions remain for this relation and magma scope. Any conjectural results are listed in the equation view."}</td></tr>`,
      );
    };
    refreshUnproved = show;
    $("unknown-search").oninput = show;
    $("unknown-side").onchange = show;
    show();
  }
  function renderEquation(id) {
    const group = board.groups[board.classOf[id]],
      dual = index.duals[id];
    $("view").innerHTML =
      `<section class="panel"><h2>E${id}</h2><p class="equation">${equationText(id)}</p><p class="sources">${sourceHTML(index.equationSources[id], index)}</p><p>Dual: ${eqLink(dual, key)} · <a href="${href("spectrum", { eq: id })}">Finite spectrum</a> · <a href="legacy.html?${id}${key.endsWith("fin") ? "&finite" : ""}">Original implication viewer and commentary</a></p><details open><summary>Proved equivalence class · ${group.length} equation${group.length === 1 ? "" : "s"}</summary><div id="class-members">${classMembers(group, id)}</div><p class="muted">Select a member to inspect both directions of its equivalence.</p></details></section><section class="panel"><h2>Compare two equations</h2><form id="compare-form" class="toolbar"><label>A<input id="compare-a" type="number" min="1" max="4694" value="${id}" required></label><label>B<input id="compare-b" type="number" min="1" max="4694" value="${validEquation(p.get("target")) || group.find((x) => x !== id) || 1}" required></label><button>Compare all relations</button></form><div id="comparison"></div></section><section class="panel"><h2>Relations to E${id}</h2><p><button type="button" class="secondary" id="show-unknown">Show unknown directions</button> · <a href="${href("implications", { ...common, view: "unknown", q: id })}">Browse unknown directions involving this class</a></p><div class="toolbar"><label>Direction<select id="direction"><option value="out">E${id} → B</option><option value="in">A → E${id}</option></select></label><label>Status<select id="status-filter"><option value="all">All results</option><option value="1">Proved yes</option><option value="2">Proved no</option><option value="claims">Conjectural</option><option value="0">Unknown</option></select></label><label>Find equation<input id="row-search" type="search" placeholder="ID or formula"></label></div><p class="count-note" id="row-summary"></p><div class="table-wrap"><table><thead><tr><th>Other equation</th><th>${key === "spectrum-fin" ? "Spectrum" : "Formula"}</th><th>Result</th><th>Class size</th></tr></thead><tbody id="rows"></tbody></table></div>${pager()}</section>`;
    $("compare-form").onsubmit = async (event) => {
      event.preventDefault();
      await compare();
    };
    async function compare() {
      const a = validEquation($("compare-a").value),
        b = validEquation($("compare-b").value);
      if (!a || !b) return;
      const url = new URL(location);
      url.searchParams.set("eq", a);
      url.searchParams.set("target", b);
      history.replaceState(null, "", url);
      $("comparison").innerHTML =
        '<p class="loading">Comparing relations and finite spectra…</p>';
      try {
        const data = await Promise.all(VIEW_KEYS.map(relation));
        const visible = data.filter(
          (d) =>
            !$("unproved").checked ||
            isUnproved(d.at(a, b)) ||
            isUnproved(d.at(b, a)),
        );
        $("comparison").innerHTML =
          `<p>Each arrow means that the right-hand law is obtainable from the left-hand law in the selected sense. ${$("unproved").checked ? "Showing variants with at least one unproved direction." : ""}</p><div class="table-wrap"><table><thead><tr><th>Relation</th><th>Magmas</th><th>E${a} → E${b}</th><th>E${b} → E${a}</th></tr></thead><tbody>${visible.map((d) => `<tr><td>${relationLabel(d.key)}</td><td>${d.flavour === "all" ? "All" : "Finite"}</td><td>${proofButton(a, b, d.key, d.at(a, b))}</td><td>${proofButton(b, a, d.key, d.at(b, a))}</td></tr>`).join("") || '<tr><td colspan="4">All directions have complete Lean proofs.</td></tr>'}</tbody></table></div>`;
      } catch (e) {
        error(e, "comparison");
      }
    }
    $("direction").value = p.get("direction") === "in" ? "in" : "out";
    $("status-filter").value = ["0", "1", "2", "claims"].includes(
      p.get("status"),
    )
      ? p.get("status")
      : "all";
    $("row-search").value = p.get("rowq") || "";
    const show = () => {
      const out = $("direction").value === "out",
        wanted = $("status-filter").value,
        q = $("row-search")
          .value.trim()
          .toLowerCase()
          .replace(/^e(?=\d+$)/, "");
      updateParams({
        status: wanted === "all" ? null : wanted,
        direction: out ? null : "in",
        rowq: $("row-search").value || null,
      });
      const representatives = $("representatives").checked;
      const ids = representatives
        ? board.groups.map((g) => g[0])
        : Array.from({ length: 4694 }, (_, i) => i + 1);
      const counts = [0, 0, 0, 0, 0];
      for (const t of ids) counts[out ? board.at(id, t) : board.at(t, id)]++;
      $("row-summary").innerHTML =
        "All relations before filtering: " +
        counts
          .map((count, i) => `${badge(i)} ${count.toLocaleString()}`)
          .join(" · ");
      const rows = ids.filter((t) => {
        const v = out ? board.at(id, t) : board.at(t, id);
        const members = representatives ? board.groups[board.classOf[t]] : [t];
        const matches =
          !q ||
          members.some((member) =>
            /^\d+$/.test(q)
              ? member === +q
              : index.equations[member - 1].toLowerCase().includes(q),
          );
        return (
          (!$("unproved").checked || isUnproved(v)) &&
          (wanted === "all" ||
            (wanted === "claims" ? v === 3 || v === 4 : v === +wanted)) &&
          matches
        );
      });
      pagination(rows, (rs) =>
        rs
          .map(
            (t) =>
              `<tr><td>${eqLink(t, key)}</td><td><code>${classDescription(t)}</code></td><td>${out ? proofButton(id, t, key, board.at(id, t)) : proofButton(t, id, key, board.at(t, id))}</td><td>${board.groups[board.classOf[t]].length}</td></tr>`,
          )
          .join(""),
      );
    };
    $("show-unknown").onclick = () => {
      $("status-filter").value = "0";
      show();
    };
    for (const field of ["direction", "status-filter"])
      $(field).onchange = show;
    refreshUnproved = () => {
      show();
      if ($("comparison").hasChildNodes()) compare();
    };
    $("row-search").oninput = show;
    show();
    if (p.has("target")) compare();
  }
} catch (e) {
  error(e);
}
