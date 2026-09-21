import {
  $,
  KEYS,
  NAMES,
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
} from "./shared.js";
shell(
  "implications",
  "Equation Explorer",
  "Explore implications, definability, structural relations, and the equivalence classes they determine.",
);
const p = params(),
  key = keyOf(p),
  eq = validEquation(p.get("eq")),
  view = ["equation", "classes", "open"].includes(p.get("view"))
    ? p.get("view")
    : eq
      ? "equation"
      : "classes";
controls(
  p,
  `<label>Equation<input id="equation-input" name="eq" placeholder="e.g. 1485" value="${eq || ""}" inputmode="numeric" pattern="[Ee]?[0-9]+"></label><input type="hidden" name="view" value="${view}">`,
);
try {
  const [index, board] = await Promise.all([json("index"), relation(key)]);
  footer(index);
  const common = { relation: p.get("relation"), flavour: p.get("flavour") };
  const tabs = [
    ["equation", "Equation"],
    ["classes", "Equivalence classes"],
    ["open", "Possible class merges"],
  ]
    .map(
      ([v, n]) =>
        `<a href="${href("implications", { ...common, view: v, ...(eq ? { eq } : {}) })}" ${v === view ? 'aria-current="page"' : ""}>${n}</a>`,
    )
    .join("");
  $("content").innerHTML =
    `<p class="panel"><strong>A → B:</strong> ${esc(board.description)} ${board.flavour === "fin" ? "Here the source magma must be finite." : "Here the source magma may be finite or infinite."}${key.startsWith("implies") ? "" : " The defining term or formula may depend on the source magma."}</p><nav class="tabs" aria-label="Explorer view">${tabs}<a href="${href("graphiti", { ...common, ...(eq ? { eq } : {}) })}">View graph ↗</a></nav><div id="view"></div>`;
  if (view === "equation") renderEquation(eq || 2);
  else if (view === "open") renderOpen();
  else renderClasses();

  function equationText(id) {
    return esc(index.equations[id - 1]);
  }
  function classMembers(group, against = group[0]) {
    return `<div class="pills">${group.map((i) => `<a href="${href("implications", { ...common, eq: i, target: against })}">E${i}</a>`).join("")}</div>`;
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
    $("view").innerHTML =
      `<section class="panel"><h2>${board.classes.toLocaleString()} proved equivalence classes</h2><p>Two equations share a class exactly when both directions are proved for this relation. ${board.unresolved_equivalence_pairs ? `${board.unresolved_equivalence_pairs.toLocaleString()} pairs of these classes could still merge.` : "Every pair of distinct classes has a proved separation in at least one direction: this classification is complete."}</p><label>Find an equation or formula <input id="class-search" type="search" placeholder="1485 or x ◇ y"></label><div class="table-wrap"><table><thead><tr><th>Representative</th><th>Equation</th><th>Members</th></tr></thead><tbody id="rows"></tbody></table></div>${pager()}</section>`;
    const show = () => {
      const q = $("class-search")
        .value.trim()
        .toLowerCase()
        .replace(/^e(?=\d+$)/, "");
      const groups = board.groups.filter(
        (g) =>
          !q ||
          (/^\d+$/.test(q)
            ? g.includes(+q)
            : g.some((i) => index.equations[i - 1].toLowerCase().includes(q))),
      );
      pagination(groups, (gs) =>
        gs
          .map(
            (g) =>
              `<tr><td>${eqLink(g[0], key)}</td><td><code>${equationText(g[0])}</code></td><td><details><summary>${g.length} equation${g.length === 1 ? "" : "s"}</summary>${classMembers(g)}</details></td></tr>`,
          )
          .join(""),
      );
    };
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
    $("merge-search").oninput = show;
    show();
  }
  function renderEquation(id) {
    const group = board.groups[board.classOf[id]],
      dual = index.duals[id];
    $("view").innerHTML =
      `<section class="panel"><h2>E${id}</h2><p class="equation">${equationText(id)}</p><p class="sources">${sourceHTML(index.equationSources[id], index)}</p><p>Dual: ${eqLink(dual, key)} · <a href="${href("spectrum", { eq: id })}">Finite spectrum</a> · <a href="legacy.html?${id}${key.endsWith("fin") ? "&finite" : ""}">Original implication viewer and commentary</a></p><details open><summary>Proved equivalence class · ${group.length} equation${group.length === 1 ? "" : "s"}</summary>${classMembers(group, id)}<p class="muted">Select a member to inspect both directions of its equivalence.</p></details></section><section class="panel"><h2>Compare two equations</h2><form id="compare-form" class="toolbar"><label>A<input id="compare-a" type="number" min="1" max="4694" value="${id}" required></label><label>B<input id="compare-b" type="number" min="1" max="4694" value="${validEquation(p.get("target")) || group.find((x) => x !== id) || 1}" required></label><button>Compare all relations</button></form><div id="comparison"></div></section><section class="panel"><h2>Relations to E${id}</h2><div class="toolbar"><label>Direction<select id="direction"><option value="out">E${id} → B</option><option value="in">A → E${id}</option></select></label><label>Status<select id="status-filter"><option value="all">All results</option><option value="1">Proved yes</option><option value="2">Proved no</option><option value="claims">Conjectural</option><option value="0">Unknown</option></select></label><label>Find equation<input id="row-search" type="search" placeholder="ID or formula"></label><label class="inline"><input type="checkbox" id="collapse" checked> Group equivalent equations</label></div><p class="count-note" id="row-summary"></p><div class="table-wrap"><table><thead><tr><th>Other equation</th><th>Formula</th><th>Result</th><th>Class size</th></tr></thead><tbody id="rows"></tbody></table></div>${pager()}</section>`;
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
        '<p class="loading">Comparing all ten variants…</p>';
      try {
        const data = await Promise.all(KEYS.map(relation));
        $("comparison").innerHTML =
          `<p>Each arrow means that the right-hand law is obtainable from the left-hand law in the selected sense.</p><div class="table-wrap"><table><thead><tr><th>Relation</th><th>Magmas</th><th>E${a} → E${b}</th><th>E${b} → E${a}</th></tr></thead><tbody>${data.map((d, i) => `<tr><td>${NAMES[Math.floor(i / 2)]}</td><td>${d.flavour === "all" ? "All" : "Finite"}</td><td>${proofButton(a, b, KEYS[i], d.at(a, b))}</td><td>${proofButton(b, a, KEYS[i], d.at(b, a))}</td></tr>`).join("")}</tbody></table></div>`;
      } catch (e) {
        error(e, "comparison");
      }
    }
    const show = () => {
      const out = $("direction").value === "out",
        wanted = $("status-filter").value,
        q = $("row-search")
          .value.trim()
          .toLowerCase()
          .replace(/^e(?=\d+$)/, "");
      const ids = $("collapse").checked
        ? board.groups.map((g) => (g.includes(+q) ? +q : g[0]))
        : Array.from({ length: 4694 }, (_, i) => i + 1);
      const counts = [0, 0, 0, 0, 0];
      for (const t of ids) counts[out ? board.at(id, t) : board.at(t, id)]++;
      $("row-summary").innerHTML = counts
        .map((count, i) => `${badge(i)} ${count.toLocaleString()}`)
        .join(" · ");
      const rows = ids.filter((t) => {
        const v = out ? board.at(id, t) : board.at(t, id);
        return (
          (wanted === "all" ||
            (wanted === "claims" ? v === 3 || v === 4 : v === +wanted)) &&
          (!q ||
            (/^\d+$/.test(q)
              ? t === +q
              : index.equations[t - 1].toLowerCase().includes(q)))
        );
      });
      pagination(rows, (rs) =>
        rs
          .map(
            (t) =>
              `<tr><td>${eqLink(t, key)}</td><td><code>${equationText(t)}</code></td><td>${out ? proofButton(id, t, key, board.at(id, t)) : proofButton(t, id, key, board.at(t, id))}</td><td>${board.groups[board.classOf[t]].length}</td></tr>`,
          )
          .join(""),
      );
    };
    for (const field of ["direction", "status-filter", "collapse"])
      $(field).onchange = show;
    $("row-search").oninput = show;
    show();
    if (p.has("target")) compare();
  }
} catch (e) {
  error(e);
}
