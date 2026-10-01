import { reducedEdges } from "./relation-comparison.js";
import { escapeHTML as esc } from "./shared.js";

function levels(nodes, edges) {
  const degree = new Map(nodes.map((n) => [n, 0])),
    next = new Map(nodes.map((n) => [n, []])),
    rank = new Map(nodes.map((n) => [n, 0]));
  for (const [a, b] of edges) {
    degree.set(b, degree.get(b) + 1);
    next.get(a).push(b);
  }
  const queue = nodes.filter((n) => !degree.get(n));
  for (const a of queue)
    for (const b of next.get(a)) {
      rank.set(b, Math.max(rank.get(b), rank.get(a) + 1));
      degree.set(b, degree.get(b) - 1);
      if (!degree.get(b)) queue.push(b);
    }
  return rank;
}
export function mergeDiagram(rows, fine, coarse, witness, options = {}) {
  const id = options.id || "merge",
    rep = (c) => fine.groups[c][0],
    coarseRep = (c) => coarse.groups[c][0];
  const outer = reducedEdges(
    rows.map((r) => r.id),
    (a, b) => coarse.at(coarseRep(a), coarseRep(b)) === 1,
  );
  const rank = levels(
      rows.map((r) => r.id),
      outer,
    ),
    positions = new Map(),
    boxes = new Map(),
    layers = [];
  let omitted = 0;
  for (const row of rows) {
    const ns = [...row.fine];
    if (options.focus)
      ns.sort(
        (a, b) =>
          (fine.groups[b].includes(options.focus) ? 1 : 0) -
          (fine.groups[a].includes(options.focus) ? 1 : 0),
      );
    const shown = ns.slice(0, options.nodeLimit || 60);
    omitted += ns.length - shown.length;
    const base = reducedEdges(shown, (a, b) => fine.at(rep(a), rep(b)) === 1),
      innerRank = levels(shown, base),
      innerLayers = [];
    for (const n of shown) (innerLayers[innerRank.get(n)] ||= []).push(n);
    const box = {
      row,
      shown,
      base,
      innerLayers,
      width: Math.max(290, ...innerLayers.map((l) => l.length * 180 + 64)),
      height: Math.max(215, innerLayers.length * 120 + 95),
    };
    boxes.set(row.id, box);
    (layers[rank.get(row.id)] ||= []).push(box);
  }
  const width = Math.max(
    640,
    ...layers.map((l) => l.reduce((n, b) => n + b.width + 42, 0) + 20),
  );
  let y = 30;
  for (const layer of layers) {
    let x = (width - layer.reduce((n, b) => n + b.width + 42, 0) + 42) / 2;
    for (const box of layer) {
      Object.assign(box, { x, y });
      box.innerLayers.forEach((ns, level) =>
        ns.forEach((n, i) =>
          positions.set(n, {
            x: x + box.width / 2 + (i - (ns.length - 1) / 2) * 180,
            y: y + 112 + level * 120,
            box: box.row.id,
          }),
        ),
      );
      x += box.width + 42;
    }
    y += Math.max(...layer.map((b) => b.height)) + 95;
  }
  const height = Math.max(240, y - 50),
    shown = [...positions.keys()],
    shownSet = new Set(shown);
  const base =
    options.inherited === false
      ? []
      : reducedEdges(shown, (a, b) => fine.at(rep(a), rep(b)) === 1).map(
          ([a, b]) => ({
            a,
            b,
            s: rep(a),
            t: rep(b),
            key: fine.key,
            upToDuality: fine.upToDuality,
            kind: "inherited",
          }),
        );
  const added =
    options.added === false
      ? []
      : rows
          .flatMap((row) => witness(row).added)
          .filter((e) => shownSet.has(e.a) && shownSet.has(e.b));
  const coarseEdges =
    options.coarser === false
      ? []
      : outer.map(([a, b]) => ({
          a,
          b,
          s: coarseRep(a),
          t: coarseRep(b),
          key: coarse.key,
          upToDuality: coarse.upToDuality,
          kind: "coarser",
        }));
  let unknown = [];
  if (options.unknown) {
    for (const row of rows)
      for (const other of rows)
        if (
          row.id !== other.id &&
          coarse.at(coarseRep(row.id), coarseRep(other.id)) === 0
        )
          unknown.push({
            a: row.id,
            b: other.id,
            s: coarseRep(row.id),
            t: coarseRep(other.id),
            key: coarse.key,
            upToDuality: coarse.upToDuality,
            kind: "unknown",
          });
  }
  const edges = [...base, ...coarseEdges, ...added, ...unknown];
  const connection = (e, i) => {
    const region = ["coarser", "unknown"].includes(e.kind);
    const a = region ? boxes.get(e.a) : positions.get(e.a),
      b = region ? boxes.get(e.b) : positions.get(e.b);
    let d;
    if (region && a.y === b.y) {
      const right = a.x < b.x,
        side = right ? 1 : -1,
        ax = a.x + (right ? a.width : 0),
        bx = b.x + (right ? 0 : b.width),
        ay = a.y + a.height / 2 + side * 28,
        by = b.y + b.height / 2 + side * 28;
      d = `M${ax},${ay} C${(ax + bx) / 2},${ay + side * 25} ${(ax + bx) / 2},${by + side * 25} ${bx - side * 3},${by}`;
    } else if (region && a.y > b.y) {
      const ax = a.x + a.width / 2,
        bx = b.x + b.width / 2,
        ay = a.y,
        by = b.y + b.height;
      d = `M${ax},${ay} C${ax},${(ay + by) / 2} ${bx},${(ay + by) / 2} ${bx},${by + 3}`;
    } else if (region) {
      const ax = a.x + a.width / 2,
        bx = b.x + b.width / 2,
        ay = a.y + a.height,
        by = b.y;
      d = `M${ax},${ay} C${ax},${(ay + by) / 2} ${bx},${(ay + by) / 2} ${bx},${by - 3}`;
    } else if (a.y === b.y) {
      // Reciprocal arrows use opposite sides of the row. They enter the top or
      // bottom of a node instead of curling past the boundary of its region.
      const side = a.x < b.x ? 1 : -1,
        bend = a.y + side * (58 + Math.min(18, Math.abs(a.x - b.x) / 20));
      d = `M${a.x},${a.y + side * 23} C${a.x},${bend} ${b.x},${bend} ${b.x},${b.y + side * 27}`;
    } else if (e.kind === "added" || a.y > b.y) {
      const down = a.y < b.y ? 1 : -1,
        side = e.a < e.b ? 1 : -1,
        middle = (a.y + b.y) / 2;
      d = `M${a.x + side * 48},${a.y + down * 23} C${a.x + side * 106},${middle} ${b.x + side * 106},${middle} ${b.x + side * 48},${b.y - down * 27}`;
    } else
      d = `M${a.x},${a.y + 23} C${a.x},${(a.y + b.y) / 2} ${b.x},${(a.y + b.y) / 2} ${b.x},${b.y - 26}`;
    const label = `${e.kind === "unknown" ? "Unknown" : e.kind === "inherited" ? "Finer" : e.kind === "added" ? "Merger witness" : "Coarser region"} arrow E${e.s} → E${e.t}${e.upToDuality ? " (up to duality)" : ""}`;
    return `<g class="merge-edge ${e.kind}" data-diagram-edge="${i}" tabindex="0" role="button" aria-label="${esc(label)}"><title>${esc(label)}. Select for evidence.</title><path d="${d}" marker-end="url(#${id}-${e.kind})"/><path class="graph-hit" d="${d}"/></g>`;
  };
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" role="group" aria-label="Finer classes inside coarser equivalence classes"><defs>${["inherited", "added", "coarser", "unknown"].map((kind) => `<marker id="${id}-${kind}" class="arrow-${kind}" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0,0 L8,4 L0,8"/></marker>`).join("")}</defs>
    ${[...boxes.values()].map((b) => `<g class="merge-region ${b.row.fine.length > 1 ? "merged" : ""}"><rect x="${b.x}" y="${b.y}" width="${b.width}" height="${b.height}" rx="18"/><text x="${b.x + 15}" y="${b.y + 25}">${esc(coarse.labels?.[b.row.id] || `E${b.row.members[0]}`)} · ${b.row.fine.length} finer class${b.row.fine.length === 1 ? "" : "es"}</text></g>`).join("")}
    ${edges.map(connection).join("")}
    ${shown
      .map((c) => {
        const p = positions.get(c),
          group = fine.groups[c];
        return `<g class="graph-node" data-diagram-node="${c}" tabindex="0" role="button" aria-label="Finer class${fine.upToDuality ? " up to duality" : ""} E${group[0]}, ${group.length} equations"><title>${group
          .slice(0, 20)
          .map((n) => "E" + n)
          .join(
            ", ",
          )}${group.length > 20 ? ", …" : ""}</title><rect x="${p.x - 64}" y="${p.y - 22}" width="128" height="44" rx="7"/><text x="${p.x}" y="${p.y - 3}" text-anchor="middle">${esc(fine.labels?.[c] || `E${group[0]}`)}</text><text x="${p.x}" y="${p.y + 14}" text-anchor="middle">${group.length} law${group.length === 1 ? "" : "s"}</text></g>`;
      })
      .join("")}</svg>`;
  return { svg, width, height, edges, omitted };
}
export function bindDiagram(element, model, { edge, node }) {
  const svg = element.querySelector("svg");
  let box = [0, 0, model.width, model.height],
    drag;
  const update = () => svg.setAttribute("viewBox", box.join(" "));
  const click = (event) => {
    const e = event.target.closest("[data-diagram-edge]"),
      n = event.target.closest("[data-diagram-node]");
    if (e) edge(model.edges[+e.dataset.diagramEdge]);
    if (n) node(+n.dataset.diagramNode);
  };
  svg.onclick = click;
  svg.onkeydown = (event) => {
    if (
      ["Enter", " "].includes(event.key) &&
      event.target.closest("[data-diagram-edge],[data-diagram-node]")
    ) {
      event.preventDefault();
      click(event);
    }
  };
  svg.onwheel = (event) => {
    event.preventDefault();
    const r = svg.getBoundingClientRect(),
      f = event.deltaY > 0 ? 1.12 : 1 / 1.12;
    box = [
      box[0] + ((box[2] * (event.clientX - r.left)) / r.width) * (1 - f),
      box[1] + ((box[3] * (event.clientY - r.top)) / r.height) * (1 - f),
      box[2] * f,
      box[3] * f,
    ];
    update();
  };
  svg.onpointerdown = (event) => {
    if (event.target.closest("[data-diagram-edge],[data-diagram-node]")) return;
    drag = [event.clientX, event.clientY, ...box];
    svg.setPointerCapture(event.pointerId);
  };
  svg.onpointermove = (event) => {
    if (!drag) return;
    const r = svg.getBoundingClientRect(),
      scale = Math.max(drag[4] / r.width, drag[5] / r.height);
    box = [
      drag[2] - (event.clientX - drag[0]) * scale,
      drag[3] - (event.clientY - drag[1]) * scale,
      drag[4],
      drag[5],
    ];
    update();
  };
  svg.onpointerup = svg.onpointercancel = () => {
    drag = null;
  };
  return () => {
    box = [0, 0, model.width, model.height];
    update();
  };
}
