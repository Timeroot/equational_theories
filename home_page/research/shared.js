export const KEYS = [
  "implies-all",
  "implies-fin",
  "termStructural-all",
  "termStructural-fin",
  "structural-all",
  "structural-fin",
  "termDefinable-all",
  "termDefinable-fin",
  "definable-all",
  "definable-fin",
];
export const NAMES = [
  "Implication",
  "Term structural",
  "FO structural",
  "Term definable",
  "FO definable",
];
export const STATUSES = [
  "Unknown",
  "Proved yes",
  "Proved no",
  "Conjectural yes",
  "Conjectural no",
];
export const isUnproved = (status) =>
  status === 0 || status === 3 || status === 4;
export const unsettledClasses = (board) => new Set(board.possibleMerges.flat());
export function unprovedControl(p) {
  return `<label class="inline"><input type="checkbox" id="unproved" name="unproved" value="1" ${p.get("unproved") === "1" ? "checked" : ""}> View only unproved</label>`;
}
export function bindUnproved(p, apply) {
  $("unproved").onchange = () => {
    const enabled = $("unproved").checked;
    enabled ? p.set("unproved", "1") : p.delete("unproved");
    const url = new URL(location);
    enabled
      ? url.searchParams.set("unproved", "1")
      : url.searchParams.delete("unproved");
    history.replaceState(null, "", url);
    // Preserve the filter when moving between the research views.
    for (const link of document.querySelectorAll("a[href]")) {
      const target = new URL(link.href);
      if (
        target.origin !== location.origin ||
        !/\/(implications|graphiti|spectrum)\/$/.test(target.pathname)
      )
        continue;
      enabled
        ? target.searchParams.set("unproved", "1")
        : target.searchParams.delete("unproved");
      link.href = target.href;
    }
    apply();
  };
}
export const escapeHTML = (s) =>
  String(s ?? "").replace(
    /[&<>"']/g,
    (c) =>
      ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[
        c
      ],
  );
export const $ = (id) => document.getElementById(id);
const pending = new Map();
export async function json(file) {
  if (!pending.has(file))
    pending.set(
      file,
      fetch(new URL(`data/${file}.json`, import.meta.url))
        .then((r) => {
          if (!r.ok)
            throw Error(
              `Could not load ${file}.json (${r.status}). The published website data is missing.`,
            );
          return r.json();
        })
        .catch((e) => {
          pending.delete(file);
          throw e;
        }),
    );
  return pending.get(file);
}
export function decode(encoded, size) {
  const out = new Uint8Array(size);
  let at = 0;
  for (let i = 0; i < encoded.length; i += 2) {
    out.fill(encoded[i], at, at + encoded[i + 1]);
    at += encoded[i + 1];
  }
  if (at !== size) throw Error("Invalid relation data length");
  return out;
}
const boards = new Map();
export async function relation(key) {
  if (!KEYS.includes(key)) throw Error("Unknown relation");
  if (!boards.has(key))
    boards.set(
      key,
      json(key).then((data) => {
        data.matrix = decode(data.status, data.groups.length ** 2);
        data.at = (s, t) =>
          data.matrix[data.classOf[s] * data.groups.length + data.classOf[t]];
        return data;
      }),
    );
  return boards.get(key);
}
export function params() {
  const p = new URLSearchParams(location.search);
  const legacy = location.search.match(/^\?(\d+)(?:&|$)/);
  if (legacy && !p.has("eq")) p.set("eq", legacy[1]);
  if (
    p.has("finite") &&
    !["false", "0"].includes(p.get("finite")) &&
    !p.has("flavour")
  )
    p.set("flavour", "fin");
  if (!["all", "fin"].includes(p.get("flavour"))) p.set("flavour", "all");
  if (!KEYS.includes(`${p.get("relation")}-${p.get("flavour")}`))
    p.set("relation", "implies");
  return p;
}
export const keyOf = (p) => `${p.get("relation")}-${p.get("flavour")}`;
export function href(page, values = {}) {
  const query = new URLSearchParams(values);
  if (
    !query.has("unproved") &&
    typeof location !== "undefined" &&
    new URLSearchParams(location.search).get("unproved") === "1"
  )
    query.set("unproved", "1");
  return `../${page}/?${query}`;
}
export function eqLink(id, key, label = `E${id}`) {
  const [rel, flavour] = key.split("-");
  return `<a href="${href("implications", { eq: id, relation: rel, flavour })}">${escapeHTML(label)}</a>`;
}
export function badge(status) {
  return `<span class="badge s${status}">${STATUSES[status]}</span>`;
}
export function evidence(status) {
  const label =
    status === "PROVED"
      ? "Proved in Lean"
      : status === "PROOF_AVAILABLE"
        ? "Conjectural · proof awaiting Lean"
        : status === "NOTE_GAP"
          ? "Conjectural · argument has a gap"
          : "Unknown";
  const cls =
    status === "PROVED"
      ? "proved"
      : ["PROOF_AVAILABLE", "NOTE_GAP"].includes(status)
        ? "conjectural"
        : "unknown";
  return `<span class="badge ${cls}">${label}</span>`;
}
export function proofButton(s, t, key, status) {
  return `<button class="status-link" data-proof="${s},${t},${key}" title="View evidence for E${s} → E${t}">${badge(status)}</button>`;
}
export function shell(page, title, description) {
  document.title = `${title} · Equational Theories`;
  document.body.innerHTML = `<header><nav aria-label="Main navigation"><a class="brand" href="../">Equational Theories</a>${[
    ["implications", "Equation Explorer"],
    ["graphiti", "Graphiti"],
    ["spectrum", "Spectra"],
  ]
    .map(
      ([p, n]) =>
        `<a href="${href(p)}" ${p === page ? 'aria-current="page"' : ""}>${n}</a>`,
    )
    .join(
      "",
    )}<a href="https://teorth.github.io/equational_theories/docs/">Original Lean docs</a></nav></header><main><div class="eyebrow">Equations · definitions · models</div><h1>${title}</h1><p class="muted">${description}</p><div id="controls"></div><div class="legend" aria-label="Evidence legend"><span>${badge(1)} / ${badge(2)} Lean proofs and their logical consequences</span><span>${evidence("PROOF_AVAILABLE")} A claimed argument without a completed Lean proof</span><span>${badge(0)} No purported proof in the database</span></div><div id="content" aria-live="polite"><p class="loading">Loading checked data…</p></div><footer id="build-info"></footer></main><dialog id="proof-dialog" aria-labelledby="proof-title"><button class="secondary close" id="close-proof">Close</button><h2 id="proof-title">Evidence</h2><div id="proof-body"></div></dialog>`;
  $("close-proof").onclick = () => $("proof-dialog").close();
  document.addEventListener("click", (event) => {
    const button = event.target.closest("[data-proof]");
    if (button) {
      const [s, t, key] = button.dataset.proof.split(",");
      showProof(+s, +t, key);
    }
  });
}
export function controls(p, extra = "") {
  $("controls").innerHTML =
    `<form id="relation-form" class="panel toolbar"><label>Relation<select name="relation" id="relation">${NAMES.map((n, i) => `<option value="${KEYS[2 * i].split("-")[0]}" ${p.get("relation") === KEYS[2 * i].split("-")[0] ? "selected" : ""}>${n}</option>`).join("")}</select></label><label>Magmas<select name="flavour" id="flavour"><option value="all" ${p.get("flavour") === "all" ? "selected" : ""}>All, including infinite</option><option value="fin" ${p.get("flavour") === "fin" ? "selected" : ""}>Finite only</option></select></label>${extra}${unprovedControl(p)}<button type="submit">Explore</button></form>`;
  $("relation-form").oninput = (event) => event.target.setCustomValidity?.("");
  $("relation-form").onsubmit = (event) => {
    event.preventDefault();
    const form = new FormData(event.currentTarget);
    const entered = String(form.get("eq") || "").trim();
    const field = event.currentTarget.elements.namedItem("eq");
    if (entered && !validEquation(entered)) {
      field.setCustomValidity("Enter an equation number from 1 to 4694.");
      field.reportValidity();
      return;
    }
    if (
      form.has("view") &&
      entered !== String(validEquation(p.get("eq")) || "")
    ) {
      form.set("view", entered ? "equation" : "classes");
    }
    for (const [k, v] of form) v ? p.set(k, v) : p.delete(k);
    if (!form.has("unproved")) p.delete("unproved");
    // The positional ?2 is read for compatibility but need not survive rewriting.
    for (const k of [...p.keys()]) if (/^\d+$/.test(k)) p.delete(k);
    location.search = p.toString();
  };
}
export function footer(index) {
  $("build-info").innerHTML =
    `Data generated ${escapeHTML(new Date(index.generated).toLocaleString())}. Source: <a href="https://github.com/${escapeHTML(index.repository)}/tree/${index.commit}">${escapeHTML(index.repository)} @ ${index.commit.slice(0, 8)}</a>. “Proved” includes closure of Lean results; open class pairs may still merge. <a href="../research/about.html">Definitions, evidence, and data</a>.`;
}
export function sourceHTML(ref, index) {
  return `<a href="https://github.com/${escapeHTML(index.repository)}/blob/${index.commit}/${escapeHTML(ref.file)}#L${ref.line}"><code>${escapeHTML(ref.name)}</code></a> <small>${escapeHTML(ref.file)}:${ref.line}</small>`;
}
export function error(e, target = "content") {
  $(target).innerHTML =
    `<p role="alert" class="error">${escapeHTML(e.message)}</p>`;
}
export function validEquation(s) {
  const n = Number(String(s).replace(/^E/i, ""));
  return Number.isInteger(n) && n >= 1 && n <= 4694 ? n : null;
}

// Reconstruct paths from source-labelled generators, not from unlabelled closure
// edges. A positive path may use stronger relations; negative paths are proved
// in the native relation of the counterexample before contraposition is applied.
export class ProofEngine {
  constructor(data, load = relation) {
    this.data = data;
    this.load = load;
    this.adj = new Map();
  }
  adjacency(key, claims = false) {
    const k = KEYS.indexOf(key),
      cacheKey = `${key}:${claims}`;
    if (!this.adj.has(cacheKey)) {
      const rows = Array.from({ length: 4695 }, () => []);
      for (const fact of this.data.positive) {
        if (!this.data.includes[fact.key][k] || (fact.conjectural && !claims))
          continue;
        for (const s of fact.s) rows[s].push(fact);
      }
      this.adj.set(cacheKey, rows);
    }
    return this.adj.get(cacheKey);
  }
  path(s, t, key, claims = false) {
    if (s === t) return [];
    const adj = this.adjacency(key, claims),
      previous = new Map([[s, null]]),
      queue = [s];
    for (let i = 0; i < queue.length; i++) {
      const a = queue[i];
      for (const fact of adj[a])
        for (const b of fact.t) {
          if (previous.has(b)) continue;
          previous.set(b, { s: a, t: b, fact });
          if (b === t) {
            const path = [];
            let at = t;
            while (at !== s) {
              const step = previous.get(at);
              path.push(step);
              at = step.s;
            }
            return path.reverse();
          }
          queue.push(b);
        }
    }
    throw Error(`Missing source path for E${s} → E${t} (${key}).`);
  }
  async explain(s, t, key) {
    const board = await this.load(key),
      status = board.at(s, t);
    if (status === 0) return { status };
    if (status === 1 || status === 3)
      return { status, path: this.path(s, t, key, status === 3) };
    const k = KEYS.indexOf(key),
      claims = status === 4;
    for (const fact of this.data.negative) {
      if (!this.data.includes[k][fact.key] || (fact.conjectural && !claims))
        continue;
      const native = KEYS[fact.key];
      // Direct membership avoids loading another matrix for most counterexamples.
      let a = fact.s.includes(s) ? s : null,
        b = fact.t.includes(t) ? t : null;
      if (a === null || b === null) {
        const data = await this.load(native),
          yes = (v) => v === 1 || (claims && v === 3);
        if (a === null) a = fact.s.find((x) => yes(data.at(x, s)));
        if (a === undefined) continue;
        if (b === null) b = fact.t.find((x) => yes(data.at(t, x)));
        if (b === undefined) continue;
      }
      const refs = [...fact.refs];
      if (fact.family) {
        const family = this.data.families[fact.family];
        refs.push(
          family.s.find(([ids]) => ids.includes(a))[1],
          family.t.find(([ids]) => ids.includes(b))[1],
        );
      }
      return {
        status,
        fact,
        refs,
        a,
        b,
        native,
        left: this.path(a, s, native, claims),
        right: this.path(t, b, native, claims),
      };
    }
    throw Error(
      `No counterexample provenance found for E${s} → E${t} (${key}).`,
    );
  }
}
let engine;
let proofRequest = 0;
export async function showProof(s, t, key) {
  const request = ++proofRequest;
  $("proof-title").textContent =
    `E${s} → E${t} · ${NAMES[Math.floor(KEYS.indexOf(key) / 2)]} · ${key.endsWith("-fin") ? "finite" : "all magmas"}`;
  $("proof-body").innerHTML =
    '<p class="loading">Tracing source declarations…</p>';
  if (!$("proof-dialog").open) $("proof-dialog").showModal();
  try {
    const [data, index] = await Promise.all([json("proofs"), json("index")]);
    engine ??= new ProofEngine(data);
    const proof = await engine.explain(s, t, key);
    if (request !== proofRequest) return;
    const sources = (refs) =>
      `<ul class="sources">${[...new Set(refs)].map((r) => `<li>${sourceHTML(data.sources[r], index)}</li>`).join("")}</ul>`;
    const pathHTML = (path) =>
      path
        .map(
          (step) =>
            `<div class="proof-step"><strong>E${step.s} → E${step.t}</strong> · ${NAMES[Math.floor(step.fact.key / 2)]}, ${KEYS[step.fact.key].endsWith("fin") ? "finite" : "all magmas"} ${step.fact.conjectural ? evidence("PROOF_AVAILABLE") : ""}${step.fact.dual ? "<p>Mirror the source theorem and both laws using the dual operation.</p>" : ""}${sources(step.fact.refs)}</div>`,
        )
        .join("");
    let html = `<p>${badge(proof.status)}</p>`;
    if (proof.status === 0)
      html +=
        "<p>No proof or counterexample is recorded for this relation. This is an open cell, not a claimed result.</p>";
    else if (proof.path)
      html += proof.path.length
        ? `<p>The following source results compose in this relation:</p>${pathHTML(proof.path)}`
        : "<p>Reflexivity: the operation defines itself.</p>";
    else {
      html += `<p>The source certificate ${proof.fact.conjectural ? "claims" : "proves"} <strong>E${proof.a} ↛ E${proof.b}</strong> for ${NAMES[Math.floor(KEYS.indexOf(proof.native) / 2)]}, ${proof.native.endsWith("fin") ? "finite magmas" : "all magmas"}.</p>${sources(proof.refs)}`;
      if (proof.fact.family)
        html += `<p>Family <code>${escapeHTML(proof.fact.family)}</code>: the source model satisfies E${proof.a}; every permitted target operation refutes E${proof.b}. The links give the obstruction lemma and both certificates.</p>`;
      if (proof.fact.dual)
        html +=
          "<p>This certificate is transported along the dual operation.</p>";
      if (proof.left.length || proof.right.length)
        html += `<p>If the requested arrow existed, these paths would compose with it to contradict the certificate:</p>${pathHTML(proof.left)}<p><strong>E${s} → E${t}</strong> (the hypothetical arrow)</p>${pathHTML(proof.right)}`;
      if (proof.native !== key)
        html +=
          "<p>The requested relation entails the certificate’s relation (with restriction to finite magmas if needed), so its refutation also refutes the requested arrow.</p>";
    }
    if (proof.status !== 0)
      html += `<details><summary>Lean rules for composition and the relation hierarchy</summary><p>Closure uses transitivity, contraposition, and the hierarchy implication → term structural → FO structural / term definable → FO definable. Results for all magmas restrict to finite magmas; refutations travel in the reverse direction. Finite counterexample certificates refute both flavours.</p>${sources(data.rules)}</details>`;
    $("proof-body").innerHTML = html;
  } catch (e) {
    if (request === proofRequest) error(e, "proof-body");
  }
}
