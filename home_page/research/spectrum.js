import {
  $,
  escapeHTML as esc,
  json,
  params,
  href,
  eqLink,
  evidence,
  shell,
  footer,
  sourceHTML,
  error,
  validEquation,
} from "./shared.js";
shell(
  "spectrum",
  "Finite spectra",
  "The spectrum of an equation is the set of positive sizes of its finite, nonempty models. Exact formulas and partial bounds carry separate evidence labels.",
);
const p = params(),
  eq = validEquation(p.get("eq"));
try {
  const [index, data] = await Promise.all([json("index"), json("spectrum")]);
  footer(index);
  $("controls").innerHTML =
    `<form class="panel toolbar" id="spectrum-form"><label>Equation<input name="eq" value="${eq || ""}" placeholder="e.g. 1485" inputmode="numeric"></label><button>View spectrum</button><a href="./" class="button secondary">All spectra</a></form>`;
  $("spectrum-form").onsubmit = (e) => {
    e.preventDefault();
    const id = validEquation(new FormData(e.currentTarget).get("eq"));
    if (!id) {
      error(Error("Enter an equation number from 1 to 4694."));
      return;
    }
    location.search = new URLSearchParams({ eq: id });
  };
  function source(name) {
    const d = data.declarations[name];
    return d
      ? `<p class="sources">${sourceHTML(d, index)}</p>${pending(d)}`
      : "";
  }
  function pending(d) {
    if (!d.pending?.length) return "";
    return `<details><summary>Pending argument and source</summary><ul class="sources">${d.pending.map((x) => `<li><strong>${esc(x.name)}</strong><p>${esc(x.source)}</p><p>Missing: ${esc(x.missing)}</p></li>`).join("")}</ul></details>`;
  }
  function formula(f) {
    return `<div class="formula"><code>${esc(f)}</code></div>`;
  }
  function claim(title, f, name, status) {
    return `<section class="panel"><h2>${title}</h2><p>${evidence(status)}</p>${formula(f)}${source(name)}</section>`;
  }
  if (eq) detail(data.records[eq - 1]);
  else catalogue();
  function detail(r) {
    $("content").innerHTML =
      `<section class="panel"><h2>E${r.equation}</h2><p class="equation">${esc(index.equations[r.equation - 1])}</p><p class="sources">${sourceHTML(index.equationSources[r.equation], index)}</p><p>${eqLink(r.equation, "implies-all", "Explore implications and definability")} · <a href="${href("graphiti", { eq: r.equation, relation: "termStructural", flavour: "fin" })}">Term structural graph</a>${r.pdf_representative && r.pdf_representative !== r.equation ? ` · <a href="?eq=${r.pdf_representative}">Spectrum representative E${r.pdf_representative}</a>` : ""}</p></section>`;
    if (r.mathematical_status === "EXACT")
      $("content").innerHTML += claim(
        "Exact spectrum",
        r.exact_spectrum_formula,
        r.exact_spectrum_theorem,
        r.exact_proof_status,
      );
    else {
      $("content").innerHTML +=
        `<section class="panel"><h2>Exact spectrum</h2><p>${evidence("UNKNOWN")} No exact spectrum has a purported proof in the catalogue.</p>${r.conjectured_spectrum_formula ? `<p>Candidate formula (a guess, without a purported proof):</p>${formula(r.conjectured_spectrum_formula)}` : ""}</section><div class="split">${claim("Lower bound · included orders", r.lower_bound_formula, r.lower_bound_theorem, r.lower_bound_proof_status)}${claim("Upper bound · permitted orders", r.upper_bound_formula, r.upper_bound_theorem, r.upper_bound_proof_status)}</div>`;
      $("content").innerHTML +=
        `<section class="panel"><h2>Cofiniteness</h2><p>A cofinite spectrum contains every sufficiently large positive integer.</p>${r.cofinite_status === "KNOWN" ? `<p>${evidence(r.cofinite_proof_status)}</p>${source(r.cofinite_theorem)}` : `<p>${evidence("UNKNOWN")} ${r.cofinite_status === "DISPUTED" ? "The source makes conflicting claims; no cofiniteness theorem is asserted." : "Cofiniteness is not settled in the catalogue."}</p>`}</section>`;
    }
    const coverage = data.declarations[r.full_or_exclusion_theorem];
    $("content").innerHTML +=
      `<section class="panel"><h2>Additional certificates</h2><p>${evidence(coverage.status)} ${r.full_spectrum ? "Models exist at every positive order." : coverage.name.includes("not_two") ? "No model has order 2." : "No model has order 3."}</p>${source(r.full_or_exclusion_theorem)}${r.representative_equality_theorem ? `<details><summary>Transfer to the spectrum representative</summary>${source(r.representative_equality_theorem)}</details>` : ""}${r.witnesses?.length ? `<details open><summary>Individual model certificates</summary><p>These are selected orders with individual declarations, not the full spectrum or all consequences of the bounds.</p><div class="table-wrap"><table><thead><tr><th>Order</th><th>Evidence</th><th>Lean declaration</th></tr></thead><tbody>${r.witnesses.map((w) => `<tr><td>${w.order}</td><td>${evidence(data.declarations[w.theorem].status)}</td><td>${source(w.theorem)}</td></tr>`).join("")}</tbody></table></div></details>` : ""}</section>`;
    if (r.pdf_notes)
      $("content").innerHTML +=
        `<section class="panel"><h2>Catalogue notes</h2><p>${esc(r.pdf_notes)}</p></section>`;
    $("content").innerHTML += glossary();
  }
  function catalogue() {
    const counts = { PROVED: 0, CONJECTURAL: 0, UNKNOWN: 0 };
    for (const r of data.records)
      counts[
        r.exact_proof_status === "PROVED"
          ? "PROVED"
          : r.mathematical_status === "EXACT"
            ? "CONJECTURAL"
            : "UNKNOWN"
      ]++;
    $("content").innerHTML =
      `<div class="stats"><div class="stat"><strong>${counts.PROVED}</strong>exact spectra proved in Lean</div><div class="stat"><strong>${counts.CONJECTURAL}</strong>exact claims awaiting proof</div><div class="stat"><strong>${counts.UNKNOWN}</strong>exact spectra unknown</div></div><section class="panel"><h2>Spectrum catalogue</h2><div class="toolbar"><label class="grow">Search<input id="search" type="search" placeholder="Equation number, formula, or notes"></label><label>Exact spectrum status<select id="filter"><option value="all">All</option><option value="PROVED">Proved in Lean</option><option value="CONJECTURAL">Conjectural</option><option value="UNKNOWN">Unknown</option></select></label><label class="inline"><input id="nonfull" type="checkbox"> Only spectra that are not full</label></div><div class="table-wrap"><table><thead><tr><th>Equation</th><th>Exact formula / candidate</th><th>Evidence for exactness</th><th>Partial bounds</th></tr></thead><tbody id="spectrum-rows"></tbody></table></div><div class="pager"><span id="page-info"></span><button class="secondary" id="previous">Previous</button><button class="secondary" id="next">Next</button></div></section>${glossary()}`;
    let page = 0,
      rows = [];
    const render = () => {
      $("spectrum-rows").innerHTML = rows
        .slice(page * 60, (page + 1) * 60)
        .map(
          (r) =>
            `<tr><td><a href="?eq=${r.equation}">E${r.equation}</a></td><td><code>${esc(r.exact_spectrum_formula || r.conjectured_spectrum_formula || "No exact formula proposed")}</code>${r.conjectured_spectrum_formula ? "<small> · candidate only</small>" : ""}</td><td>${evidence(r.exact_proof_status)}</td><td>${r.mathematical_status === "UNKNOWN" ? `Lower: ${evidence(r.lower_bound_proof_status)}<br>Upper: ${evidence(r.upper_bound_proof_status)}` : "—"}</td></tr>`,
        )
        .join("");
      $("page-info").textContent = rows.length
        ? `${page * 60 + 1}–${Math.min((page + 1) * 60, rows.length)} of ${rows.length}`
        : "No matches";
      $("previous").disabled = page === 0;
      $("next").disabled = (page + 1) * 60 >= rows.length;
    };
    const filter = () => {
      page = 0;
      const q = $("search")
          .value.trim()
          .toLowerCase()
          .replace(/^e(?=\d+$)/, ""),
        v = $("filter").value;
      rows = data.records.filter((r) => {
        const status =
          r.exact_proof_status === "PROVED"
            ? "PROVED"
            : r.mathematical_status === "EXACT"
              ? "CONJECTURAL"
              : "UNKNOWN";
        return (
          (v === "all" || v === status) &&
          (!$("nonfull").checked || !r.full_spectrum) &&
          (!q ||
            (/^\d+$/.test(q)
              ? r.equation === +q
              : JSON.stringify(r).toLowerCase().includes(q)))
        );
      });
      render();
    };
    $("search").oninput = filter;
    $("filter").onchange = filter;
    $("nonfull").onchange = filter;
    $("previous").onclick = () => {
      page--;
      render();
    };
    $("next").onclick = () => {
      page++;
      render();
    };
    filter();
  }
  function glossary() {
    return `<details class="panel"><summary>Reading the formulas and evidence</summary><p><code>{n : ℕ | 0 &lt; n}</code> means every positive order. <code>positiveExcept {…}</code> excludes the listed positive orders. <code>squares</code> means positive perfect squares, <code>twiceSquares</code> twice a positive square, and <code>shiftedSquares</code> means k² + 2 for k ≥ 3, and <code>∪</code> is union. Source declarations define the other named sets.</p><p>“Conjectural” means the catalogue records a purported argument or reported computation that has not been completed in Lean. A note gap is flagged separately because its missing step is mathematical. “Unknown” includes proposed formulas without purported proofs. A partial bound's status never upgrades the exact spectrum.</p><p>Lean provenance is checked transitively, so a theorem depending on a pending declaration remains conjectural. Selected native computation certificates use Lean's native-computation trust boundary.</p></details>`;
  }
} catch (e) {
  error(e);
}
