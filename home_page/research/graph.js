import {
  $,
  escapeHTML as esc,
  json,
  relation,
  params,
  keyOf,
  href,
  eqLink,
  proofButton,
  shell,
  controls,
  footer,
  error,
  validEquation,
  showProof,
  unsettledClasses,
  bindUnproved,
} from "./shared.js";
shell(
  "graphiti",
  "Graphiti",
  "Graphs of proved equivalence classes, ordered by implication, definability, or structural relations.",
);
const p = params(),
  key = keyOf(p),
  eq = validEquation(p.get("eq"));
controls(
  p,
  `<label>Focus equation<input name="eq" value="${eq || ""}" placeholder="e.g. 3342" inputmode="numeric"></label><label class="grow">Include equations (comma separated)<input name="equations" value="${esc(p.get("equations") || p.get("limit_equations") || "")}" placeholder="e.g. 52, 629, 433, 854, 3342, 3545"></label><label>Class limit<select name="limit">${[30, 60, 120, 300, 5000].map((n) => `<option value="${n}" ${+(p.get("limit") || 60) === n ? "selected" : ""}>${n === 5000 ? "All classes" : n}</option>`).join("")}</select></label>`,
);
bindUnproved(p, () => $("relation-form").requestSubmit());
try {
  const [index, b] = await Promise.all([json("index"), relation(key)]);
  footer(index);
  const reps = b.groups.map((g) => g[0]),
    at = (a, c) => b.matrix[a * reps.length + c];
  let chosen = [...reps.keys()];
  const raw = (p.get("equations") || p.get("limit_equations") || "").trim();
  const ids = raw ? raw.split(/[\s,]+/).map(validEquation) : [];
  if (ids.some((x) => x === null))
    throw Error("Enter equation numbers from 1 to 4694, separated by commas.");
  if (ids.length) chosen = [...new Set(ids.map((i) => b.classOf[i]))];
  const onlyUnproved = p.get("unproved") === "1";
  if (onlyUnproved) {
    const unsettled = unsettledClasses(b);
    chosen = chosen.filter((c) => unsettled.has(c));
  }
  if (eq) {
    const c = b.classOf[eq];
    if (onlyUnproved) {
      const neighbours = new Set(
        b.possibleMerges.filter(([a, d]) => a === c || d === c).flat(),
      );
      chosen = chosen.filter((x) => neighbours.has(x));
    } else
      chosen = chosen.filter(
        (x) => x === c || at(c, x) === 1 || at(x, c) === 1,
      );
    chosen.sort((a, d) => (a === c ? -1 : d === c ? 1 : reps[a] - reps[d]));
  }
  const total = chosen.length,
    limit = Math.min(5000, Math.max(1, Number(p.get("limit")) || 60));
  chosen = chosen.slice(0, limit);
  $("content").innerHTML =
    `<p class="panel"><strong>A → B:</strong> ${esc(b.description)} ${b.flavour === "fin" ? "Finite magmas only." : "All magmas, including infinite ones."}</p><div class="stats"><div class="stat"><strong>${b.classes}</strong>proved classes</div><div class="stat"><strong>${b.unresolved_equivalence_pairs.toLocaleString()}</strong>possible class merges</div><div class="stat"><strong>${chosen.length}</strong>classes in this graph</div></div>${total > limit ? `<p class="notice">Showing ${limit} of ${total} matching classes. Increase the class limit or focus on an equation to see a different part of the graph.</p>` : ""}<p class="muted">“View only unproved” keeps classes that could still merge. With a focus equation, it shows that class and its possible merges. Arrows still represent proved relations.</p>${chosen.length ? "" : '<p role="status">No classes match these filters.</p>'}<p>Each node is a proved equivalence class. Arrows point from source to target; arrows implied by other visible paths are omitted. Click an arrow for its Lean sources, or a node for its members. Drag to pan; scroll to zoom. An absent arrow may be refuted, conjectural, or unknown; compare the pair in the Equation Explorer.</p><div class="tabs"><button id="fit" class="secondary">Fit graph</button><button id="download-svg" class="secondary">Download SVG</button><button id="download-dot" class="secondary">Download DOT</button><a href="${href("implications", { relation: p.get("relation"), flavour: p.get("flavour"), view: "open" })}">Browse possible class merges</a><a href="legacy.html?${new URLSearchParams({ finite: String(b.flavour === "fin"), limit_equations: raw })}">Original implication graph controls</a></div><div id="graph" role="region" aria-label="Graph of proved relations"></div><section class="panel" id="selection"><h2>Class members and evidence</h2><p>Select a node to inspect its class, or an arrow to see why that relation holds.</p></section><details class="panel"><summary>Accessible table of the visible graph</summary><div class="table-wrap"><table><thead><tr><th>Class</th><th>Members</th><th>Outgoing arrows</th></tr></thead><tbody id="graph-table"></tbody></table></div></details>`;
  // A Hasse diagram of the induced suborder. Reachability remains available in
  // the explorer, and clicking a reduced edge still reconstructs its full proof.
  const edges = [];
  for (const a of chosen)
    for (const c of chosen)
      if (a !== c && at(a, c) === 1) {
        if (
          !chosen.some(
            (m) => m !== a && m !== c && at(a, m) === 1 && at(m, c) === 1,
          )
        )
          edges.push([a, c]);
      }
  const incoming = new Map(chosen.map((c) => [c, 0])),
    next = new Map(chosen.map((c) => [c, []])),
    levels = new Map(chosen.map((c) => [c, 0]));
  for (const [a, c] of edges) {
    incoming.set(c, incoming.get(c) + 1);
    next.get(a).push(c);
  }
  const queue = chosen.filter((c) => !incoming.get(c));
  for (let i = 0; i < queue.length; i++)
    for (const c of next.get(queue[i])) {
      levels.set(c, Math.max(levels.get(c), levels.get(queue[i]) + 1));
      incoming.set(c, incoming.get(c) - 1);
      if (!incoming.get(c)) queue.push(c);
    }
  const layers = [];
  for (const c of chosen) (layers[levels.get(c)] ??= []).push(c);
  const width = Math.max(600, ...layers.map((l) => l.length * 165)),
    height = Math.max(260, layers.length * 115 + 50),
    positions = new Map();
  layers.forEach((layer, l) =>
    layer.forEach((c, i) =>
      positions.set(c, {
        x: (width - layer.length * 165) / 2 + i * 165 + 82,
        y: l * 115 + 55,
      }),
    ),
  );
  const nodeHTML = (c) => {
    const { x, y } = positions.get(c),
      g = b.groups[c];
    return `<g class="graph-node ${eq && g.includes(eq) ? "selected" : ""}" data-class="${c}" tabindex="0" role="button" aria-label="Class of E${reps[c]}, ${g.length} equations"><title>${esc(
      g
        .slice(0, 20)
        .map((i) => "E" + i)
        .join(", "),
    )}${g.length > 20 ? ", …" : ""}</title><rect x="${x - 68}" y="${y - 25}" width="136" height="50" rx="7"/><text x="${x}" y="${y - 3}" text-anchor="middle">E${reps[c]}</text><text x="${x}" y="${y + 15}" text-anchor="middle">${g.length} equation${g.length === 1 ? "" : "s"}</text></g>`;
  };
  $("graph").innerHTML =
    `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" aria-label="${esc(b.label)} graph"><defs><marker id="arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0,0 L8,4 L0,8" fill="#78949c"/></marker></defs><g>${edges
      .map(([a, c]) => {
        const s = positions.get(a),
          t = positions.get(c);
        const curve = `M${s.x},${s.y + 25} C${s.x},${(s.y + t.y) / 2} ${t.x},${(s.y + t.y) / 2} ${t.x},${t.y - 27}`;
        return `<g class="graph-connection" data-edge="${reps[a]},${reps[c]}" tabindex="0" role="button" aria-label="Proof of E${reps[a]} to E${reps[c]}"><title>E${reps[a]} → E${reps[c]}: click for proof</title><path class="graph-edge" d="${curve}" marker-end="url(#arrow)"/><path class="graph-hit" d="${curve}"/><circle cx="${(s.x + t.x) / 2}" cy="${(s.y + t.y) / 2}" r="8" fill="transparent" pointer-events="all"/></g>`;
      })
      .join("")}${chosen.map(nodeHTML).join("")}</g></svg>`;
  const svg = $("graph").querySelector("svg");
  let box = [0, 0, width, height],
    drag = null;
  const update = () => svg.setAttribute("viewBox", box.join(" "));
  $("fit").onclick = () => {
    box = [0, 0, width, height];
    update();
  };
  svg.onwheel = (event) => {
    event.preventDefault();
    const rect = svg.getBoundingClientRect(),
      factor = event.deltaY > 0 ? 1.13 : 1 / 1.13;
    const fx = (event.clientX - rect.left) / rect.width,
      fy = (event.clientY - rect.top) / rect.height;
    box = [
      box[0] + box[2] * fx * (1 - factor),
      box[1] + box[3] * fy * (1 - factor),
      box[2] * factor,
      box[3] * factor,
    ];
    update();
  };
  svg.onpointerdown = (e) => {
    if (e.target.closest("[data-class],[data-edge]")) return;
    drag = [e.clientX, e.clientY, ...box];
    svg.setPointerCapture(e.pointerId);
  };
  svg.onpointermove = (e) => {
    if (!drag) return;
    const r = svg.getBoundingClientRect(),
      scale = Math.max(drag[4] / r.width, drag[5] / r.height);
    box = [
      drag[2] - (e.clientX - drag[0]) * scale,
      drag[3] - (e.clientY - drag[1]) * scale,
      drag[4],
      drag[5],
    ];
    update();
  };
  svg.onpointerup = () => (drag = null);
  svg.onpointercancel = () => (drag = null);
  const select = (c) => {
    const g = b.groups[c],
      r = g[0];
    $("selection").innerHTML =
      `<h2>Class of E${r} · ${g.length} equations</h2><p class="equation">${esc(index.equations[r - 1])}</p><div class="pills">${g.map((i) => eqLink(i, key)).join("")}</div><details><summary>Evidence for equivalence to E${r}</summary><div class="table-wrap"><table><thead><tr><th>Member</th><th>E${r} → member</th><th>Member → E${r}</th></tr></thead><tbody>${g.map((i) => `<tr><td>${eqLink(i, key)}</td><td>${proofButton(r, i, key, 1)}</td><td>${proofButton(i, r, key, 1)}</td></tr>`).join("")}</tbody></table></div></details><p><a href="${href("implications", { eq: r, relation: p.get("relation"), flavour: p.get("flavour") })}">Explore all relations for this class</a></p>`;
    svg
      .querySelectorAll("[data-class]")
      .forEach((n) => n.classList.toggle("selected", +n.dataset.class === c));
  };
  svg.onclick = (e) => {
    const n = e.target.closest("[data-class]"),
      edge = e.target.closest("[data-edge]");
    if (n) select(+n.dataset.class);
    if (edge) {
      const [a, c] = edge.dataset.edge.split(",").map(Number);
      showProof(a, c, key);
    }
  };
  svg.onkeydown = (e) => {
    if (e.key === "Enter" || e.key === " ") {
      const n = e.target.closest("[data-class]");
      if (n) {
        e.preventDefault();
        select(+n.dataset.class);
      }
      const edge = e.target.closest("[data-edge]");
      if (edge) {
        e.preventDefault();
        const [a, c] = edge.dataset.edge.split(",").map(Number);
        showProof(a, c, key);
      }
    }
  };
  $("graph-table").innerHTML = chosen
    .map(
      (c) =>
        `<tr><td>${eqLink(reps[c], key)}</td><td>${b.groups[c].length}</td><td>${
          next
            .get(c)
            .map(
              (d) =>
                `${eqLink(reps[d], key)} ${proofButton(reps[c], reps[d], key, 1)}`,
            )
            .join(" · ") || "None in this graph"
        }</td></tr>`,
    )
    .join("");
  function download(name, content, type) {
    const url = URL.createObjectURL(new Blob([content], { type }));
    const a = document.createElement("a");
    a.href = url;
    a.download = name;
    a.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }
  $("download-svg").onclick = () => {
    const copy = svg.cloneNode(true);
    copy.setAttribute("viewBox", `0 0 ${width} ${height}`);
    copy.insertAdjacentHTML(
      "afterbegin",
      "<style>.graph-edge{stroke:#78949c;stroke-width:1.5;fill:none}.graph-hit{stroke:transparent;stroke-width:12;fill:none}.graph-node rect{fill:#f2f9f8;stroke:#75a6a6}.graph-node text{font:13px sans-serif;fill:#173044}</style>",
    );
    download(
      `${key}.svg`,
      new XMLSerializer().serializeToString(copy),
      "image/svg+xml",
    );
  };
  $("download-dot").onclick = () =>
    download(
      `${key}.dot`,
      `digraph {\n${chosen.map((c) => `${reps[c]} [label="E${reps[c]} (${b.groups[c].length} equations)"];`).join("\n")}\n${edges.map(([a, c]) => `${reps[a]} -> ${reps[c]};`).join("\n")}\n}`,
      "text/vnd.graphviz",
    );
  if (eq && chosen.includes(b.classOf[eq])) select(b.classOf[eq]);
} catch (e) {
  error(e);
}
