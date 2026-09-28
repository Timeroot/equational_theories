import {
  $,
  escapeHTML as esc,
  json,
  relation,
  params,
  href,
  eqLink,
  evidence,
  shell,
  footer,
  sourceHTML,
  error,
  validEquation,
  unprovedControl,
  bindUnproved,
  representativesControl,
  bindRepresentatives,
  SPECTRUM_REPRESENTATIVE_HELP,
} from "./shared.js";
import {
  orderList,
  overviewOf,
  remainingOf,
  initialOrders,
  ORDER_STATES,
} from "./spectrum-view.js";
shell(
  "spectrum",
  "Finite spectra",
  "The spectrum of an equation is the set of positive sizes of its finite, nonempty models. Exact formulas and partial bounds carry separate evidence labels.",
);
const p = params(),
  eq = validEquation(p.get("eq"));
try {
  const [index, data, finiteFO] = await Promise.all([
    json("index"),
    json("spectrum"),
    relation("definable-fin"),
  ]);
  footer(index);
  function spectrumLink(values = {}) {
    const filters = Object.fromEntries(
      ["nonfull", "nonsingleton"]
        .filter((name) => p.get(name) === "1")
        .map((name) => [name, "1"]),
    );
    return href("spectrum", { ...filters, ...values });
  }
  $("controls").innerHTML =
    `<form class="panel toolbar" id="spectrum-form"><label>Equation<input name="eq" value="${eq || ""}" placeholder="e.g. 1485" inputmode="numeric"></label><button>View spectrum</button><a id="all-spectra" href="${spectrumLink()}" class="button secondary">All spectra</a></form>`;
  $("spectrum-form").onsubmit = (e) => {
    e.preventDefault();
    const id = validEquation(new FormData(e.currentTarget).get("eq"));
    if (!id) {
      error(Error("Enter an equation number from 1 to 4694."));
      return;
    }
    location.href = spectrumLink({ eq: id });
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
  function constructions(r) {
    const o = overviewOf(r);
    if (!o)
      return `<p><strong>Lower bound:</strong> ${evidence(r.lower_bound_proof_status)}</p>${formula(r.lower_bound_formula)}<p><strong>Upper bound:</strong> ${evidence(r.upper_bound_proof_status)}</p>${formula(r.upper_bound_formula)}`;
    return `<p>${esc(o.includedSummary)}</p><p><strong>No models:</strong> ${o.excluded.length ? esc(orderList(o.excluded)) + "." : "No orders excluded by the current Lean results."}</p>`;
  }
  function questions(r, compact = false) {
    const o = overviewOf(r),
      remaining = remainingOf(o);
    const fold = compact && o && remaining.text.length > 180;
    const shown = fold ? `${orderList(o.open.slice(0, 12))}, …` : remaining.text;
    return `<p><strong>${esc(remaining.label)}:</strong> <span class="spectrum-orders">${esc(shown)}</span></p>${fold ? `<details><summary>Show all ${o.open.length} unresolved orders${o.finite ? "" : ` through ${o.through}`}</summary><p class="spectrum-orders">${esc(remaining.text)}</p></details>` : ""}${remaining.scope ? `<p class="muted spectrum-scope">${esc(remaining.scope)}</p>` : ""}${o?.pending.length ? `<p class="spectrum-pending"><strong>Reported nonexistence, awaiting Lean:</strong> ${esc(orderList(o.pending))}.</p>` : ""}${o?.note ? `<p class="spectrum-note">${esc(o.note)}</p>` : ""}`;
  }
  function constructionSources(r) {
    return `${source(r.lower_bound_theorem)}${source("Law.MagmaLaw.HasModel.mul")}${r.tail_theorem ? source(r.tail_theorem) : ""}`;
  }
  function exclusionSources(r) {
    return (r.exclusions || [])
      .map(
        (x) =>
          `<div class="spectrum-exclusion"><strong>Order ${esc(x.order)}</strong> ${evidence(x.status)}${source(x.theorem)}</div>`,
      )
      .join("");
  }
  function proofDetails(r, compact = false) {
    const exclusions = exclusionSources(r);
    return `<details class="${compact ? "spectrum-row-proofs" : "panel"}"><summary>Formulas and proof links</summary><div class="spectrum-bound"><h3>${r.lower_bound_proof_status === "PROVED" ? "Proved constructions and their products" : "Construction bound and product rule"}</h3><p>${evidence(r.lower_bound_proof_status)}</p>${formula(r.lower_bound_formula)}${constructionSources(r)}</div><div class="spectrum-bound"><h3>Upper bound</h3><p>${evidence(r.upper_bound_proof_status)}${r.upper_bound_proof_status !== "PROVED" ? " This upper bound is not fully proved in Lean." : ""}</p>${formula(r.upper_bound_formula)}${source(r.upper_bound_theorem)}${exclusions ? `<details><summary>Evidence for each excluded order</summary>${exclusions}</details>` : ""}</div>${r.conjectured_spectrum_formula ? `<div class="spectrum-bound"><h3>Proposed exact formula</h3><p>${evidence("UNKNOWN")} A guess without a purported proof.</p>${formula(r.conjectured_spectrum_formula)}</div>` : ""}${!compact ? `<div class="spectrum-bound"><h3>Cofiniteness</h3><p>A cofinite spectrum contains every sufficiently large positive integer.</p>${r.cofinite_status === "KNOWN" ? `<p>${evidence(r.cofinite_proof_status)}${r.cofinite_cutoff ? ` Every order at least ${esc(r.cofinite_cutoff)} is included.` : ""}</p>${source(r.cofinite_theorem)}` : `<p>${evidence("UNKNOWN")} ${r.cofinite_status === "DISPUTED" ? "The source makes conflicting claims; no cofiniteness theorem is asserted." : "Cofiniteness is not settled in the catalogue."}</p>`}</div>` : ""}</details>`;
  }
  function orderStrip(r) {
    const cells = initialOrders(r);
    if (!cells.length) return "";
    return `<section class="panel"><h2>Orders 1–64</h2><p class="muted">Included orders use the proved constructions and their products. Reported exclusions are shown separately from Lean proofs.</p><ul class="order-strip" aria-label="Model existence at orders 1 through 64">${cells.map((x) => `<li class="order-${x.status}" title="Order ${x.order}: ${esc(x.label)}"><span aria-hidden="true">${x.symbol}</span> ${x.order}<span class="sr-only">: ${esc(x.label)}</span></li>`).join("")}</ul><div class="legend spectrum-legend">${Object.entries(ORDER_STATES).map(([status, x]) => `<span><span class="order-key order-${status}" aria-hidden="true">${x.symbol}</span> ${esc(x.label)}</span>`).join("")}</div></section>`;
  }
  function detail(r) {
    const isOpen = r.mathematical_status !== "EXACT";
    $("content").innerHTML =
      `<section class="panel"><h2>E${r.equation}</h2><p class="equation">${esc(index.equations[r.equation - 1])}</p><details><summary>Law source and related views</summary><p class="sources">${sourceHTML(index.equationSources[r.equation], index)}</p><p>${eqLink(r.equation, "implies-all", "Explore implications and definability")} · <a href="${href("graphiti", { eq: r.equation, relation: "termStructural", flavour: "fin" })}">Term structural graph</a>${r.pdf_representative && r.pdf_representative !== r.equation ? ` · <a href="${spectrumLink({ eq: r.pdf_representative })}">Catalogue proof representative E${r.pdf_representative}</a>` : ""}</p></details></section>`;
    if (!isOpen)
      $("content").innerHTML += claim(
        "Exact spectrum",
        r.exact_spectrum_formula,
        r.exact_spectrum_theorem,
        r.exact_proof_status,
      );
    else
      $("content").innerHTML +=
        `<section class="panel spectrum-overview"><h2>Spectrum overview</h2><div class="spectrum-overview-columns"><div><h3>Proved constructions &amp; exclusions</h3>${constructions(r)}</div><div><h3>Remaining questions</h3>${questions(r)}</div></div></section>${orderStrip(r)}${proofDetails(r)}`;
    const coverage = data.declarations[r.full_or_exclusion_theorem],
      certificates = `${coverage ? `<p>${evidence(coverage.status)} ${r.full_spectrum ? "Models exist at every positive order." : coverage.name.includes("not_two") ? "No model has order 2." : "No model has order 3."}</p>${source(r.full_or_exclusion_theorem)}` : ""}${r.representative_equality_theorem ? `<details><summary>Transfer to the catalogue proof representative</summary>${source(r.representative_equality_theorem)}</details>` : ""}${r.witnesses?.length ? `<details><summary>Individual model certificates</summary><p>These are selected orders with individual declarations. The proved constructions and their products supply further orders.</p><div class="table-wrap"><table><thead><tr><th>Order</th><th>Evidence</th><th>Lean declaration</th></tr></thead><tbody>${r.witnesses.map((w) => `<tr><td>${w.order}</td><td>${evidence(data.declarations[w.theorem]?.status)}</td><td>${source(w.theorem)}</td></tr>`).join("")}</tbody></table></div></details>` : ""}`;
    $("content").innerHTML += isOpen
      ? `<details class="panel"><summary>Individual witnesses and additional certificates</summary>${certificates}</details>`
      : `<section class="panel"><h2>Additional certificates</h2>${certificates}</section>`;
    if (r.pdf_notes)
      $("content").innerHTML +=
        `<details class="panel"><summary>Catalogue notes</summary><p>${esc(r.pdf_notes)}</p></details>`;
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
      `<div class="stats"><div class="stat"><strong>${counts.PROVED}</strong>exact spectra proved in Lean</div><div class="stat"><strong>${counts.CONJECTURAL}</strong>exact claims awaiting proof</div><div class="stat"><strong>${counts.UNKNOWN}</strong>exact spectra unknown</div></div><section class="panel"><h2>Spectrum catalogue</h2><p><a id="open-spectra" href="${spectrumLink({ unproved: "1", representatives: "1" })}">Open spectra: one representative per equivalence class</a></p><div class="toolbar"><label class="grow">Search<input id="search" type="search" placeholder="Equation number, formula, or notes"></label><label>Exact spectrum status<select id="filter"><option value="all">All</option><option value="PROVED">Proved in Lean</option><option value="CONJECTURAL">Conjectural</option><option value="UNKNOWN">Unknown</option></select></label>${unprovedControl(p)}${representativesControl(p, SPECTRUM_REPRESENTATIVE_HELP)}<label class="inline"><input id="nonfull" type="checkbox" ${p.get("nonfull") === "1" ? "checked" : ""}> Hide full spectrum</label><label class="inline"><input id="nonsingleton" type="checkbox" ${p.get("nonsingleton") === "1" ? "checked" : ""}> Hide {1} spectrum</label></div><p class="muted">The representative filter uses proved finite FO-definability equivalence, with the smallest equation number representing each class. “View only unproved” includes unknown and conjectural exact spectra, even when some bounds or individual models are proved in Lean.</p><div class="table-wrap spectrum-table-wrap"><table class="spectrum-table"><thead><tr><th>Law</th><th>Proved constructions &amp; exclusions</th><th>Remaining questions</th></tr></thead><tbody id="spectrum-rows"></tbody></table></div><div class="pager"><span id="page-info"></span><button class="secondary" id="previous">Previous</button><button class="secondary" id="next">Next</button></div></section>${glossary()}`;
    let page = 0,
      rows = [];
    const render = () => {
      $("spectrum-rows").innerHTML = rows
        .slice(page * 60, (page + 1) * 60)
        .map((r) => {
          const law = `<a ${$("representatives").checked ? `title="${esc(SPECTRUM_REPRESENTATIVE_HELP)}"` : ""} href="${spectrumLink({ eq: r.equation })}">E${r.equation}</a>`;
          if (r.mathematical_status === "UNKNOWN")
            return `<tr class="spectrum-open-row"><td data-label="Law">${law}</td><td data-label="Proved constructions & exclusions">${constructions(r)}${proofDetails(r, true)}</td><td data-label="Remaining questions">${questions(r, true)}</td></tr>`;
          return `<tr><td data-label="Law">${law}</td><td data-label="Proved constructions & exclusions"><code>${esc(r.exact_spectrum_formula)}</code> ${evidence(r.exact_proof_status)}</td><td data-label="Remaining questions">${r.exact_proof_status === "PROVED" ? "None." : "The exact claim awaits a complete Lean proof."}</td></tr>`;
        })
        .join("");
      $("page-info").textContent = rows.length
        ? `${page * 60 + 1}–${Math.min((page + 1) * 60, rows.length)} of ${rows.length}`
        : "No matches";
      $("previous").disabled = page === 0;
      $("next").disabled = (page + 1) * 60 >= rows.length;
    };
    const filter = () => {
      $("all-spectra").href = spectrumLink();
      $("open-spectra").href = spectrumLink({ unproved: "1", representatives: "1" });
      page = 0;
      const q = $("search")
          .value.trim()
          .toLowerCase()
          .replace(/^e(?=\d+$)/, ""),
        v = $("filter").value;
      const representatives = $("representatives").checked;
      rows = data.records.filter((r) => {
        const group = finiteFO.groups[finiteFO.classOf[r.equation]];
        if (representatives && r.equation !== group[0]) return false;
        const matches =
          !q ||
          (representatives ? group : [r.equation]).some((id) =>
            /^\d+$/.test(q)
              ? id === +q
              : JSON.stringify(data.records[id - 1])
                  .toLowerCase()
                  .includes(q),
          );
        const status =
          r.exact_proof_status === "PROVED"
            ? "PROVED"
            : r.mathematical_status === "EXACT"
              ? "CONJECTURAL"
              : "UNKNOWN";
        return (
          (v === "all" || v === status) &&
          (!$("unproved").checked || r.exact_proof_status !== "PROVED") &&
          (!$("nonfull").checked || !r.full_spectrum) &&
          (!$("nonsingleton").checked || r.exact_spectrum !== "SINGLETON") &&
          matches
        );
      });
      render();
    };
    $("search").oninput = filter;
    $("filter").onchange = filter;
    for (const name of ["nonfull", "nonsingleton"])
      $(name).onchange = () => {
        const url = new URL(location);
        if ($(name).checked) {
          p.set(name, "1");
          url.searchParams.set(name, "1");
        } else {
          p.delete(name);
          url.searchParams.delete(name);
        }
        history.replaceState(null, "", url);
        filter();
      };
    bindUnproved(p, filter);
    bindRepresentatives(p, filter);
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
    return `<details class="panel"><summary>Reading the formulas and evidence</summary><p><code>{n : ℕ | 0 &lt; n}</code> means every positive order. <code>positiveExcept {…}</code> excludes the listed positive orders. <code>squares</code> means positive perfect squares, <code>twiceSquares</code> twice a positive square, and <code>shiftedSquares</code> means k² + 2 for k ≥ 3, and <code>∪</code> is union. Source declarations define the other named sets.</p><p>“Conjectural” means the catalogue records a purported argument or reported computation that has not been completed in Lean. A note gap is flagged separately because its missing step is mathematical. “Unknown” includes proposed formulas without purported proofs. A partial bound's status never upgrades the exact spectrum.</p><p>The representative filter groups equations by finite FO-definability equivalence: each law is FO-definable from the other on finite magmas. A common spectrum alone does not put two laws in the same class.</p><p>Lean provenance is checked transitively, so a theorem depending on a pending declaration remains conjectural. Selected native computation certificates use Lean's native-computation trust boundary.</p></details>`;
  }
} catch (e) {
  error(e);
}
