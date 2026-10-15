import {$, shell, params, validEquation, escapeHTML as esc, eqLink, json, relation, error} from "./shared.js";
import {FIELDS, parastropheBoard} from "./parastrophes.js";
import {cellHTML, overviewHTML, bindParastropheProofs} from "./parastrophe-view.js";

shell("parastrophes", "Quasigroups and parastrophes",
  "Which laws force a quasigroup, which identities exactly characterize their divisions, and how those divisions can be recovered by terms.");
const p = params();
$("controls").innerHTML = `<form id="parastrophe-controls" class="toolbar"><label>Models<select id="scope"><option value="all">Finite or infinite</option><option value="fin">Finite only</option></select></label><label>Find equation<input id="search" type="search" placeholder="e.g. 543 or x ◇ y" value="${esc(p.get("eq") || p.get("q") || "")}"></label><label>Quasigroup status<select id="quasigroup-filter"><option value="any">Any status</option><option value="yes">Proved yes</option><option value="no">Proved no</option><option value="unknown">Unproved</option></select></label><label class="inline"><input id="only-unproved" type="checkbox" ${p.get("unproved") === "1" ? "checked" : ""}> View only unproved</label><label class="inline" title="Use ordinary implication equivalence in the selected carrier scope; structural equivalence need not preserve these properties."><input id="only-representatives" type="checkbox" ${p.get("representatives") === "1" ? "checked" : ""}> Only implication-class representatives</label><button>Apply</button></form>`;
$("scope").value = p.get("flavour") === "fin" ? "fin" : "all";
$("quasigroup-filter").value = ["yes", "no", "unknown"].includes(p.get("quasigroup")) ? p.get("quasigroup") : "any";
try {
  const [index, data, all, fin] = await Promise.all([json("index"), json("parastrophes"), relation("implies-all"), relation("implies-fin")]);
  const board = parastropheBoard(data, index, {all, fin});
  bindParastropheProofs(board);
  $("content").innerHTML = `<details class="panel"><summary>What the fields mean</summary><p>A quasigroup has bijective left and right translations. Left division solves x ◇ z = y; right division solves z ◇ y = x. Multiplication, the two divisions, and their opposites give the six parastrophes.</p><p>“One equation” asks for exactly the image model class, among all magmas in the selected scope. A negative excludes every single identity, not merely E1–E4694. A positive includes its characterizing equation and the converse proof.</p><p>“Term per model” asks whether every source model admits a parameter-free binary term for that division. “Uniform term” requires one term for all models. These questions do not depend on whether a single equation characterizes the division image. Division is always first-order definable when it exists.</p><p>For a law forcing quasigroups on arbitrary carriers, the free two-generated model gives uniform terms for both divisions. On finite carriers, inverse translations are powers of translations, giving a term in each model; this alone gives no uniform term. Both statements are proved in Lean and linked from the resulting cells.</p><p>Only ordinary implication transfers these properties; existential structural or definability equivalence need not preserve them. Duality swaps the division sides and also takes the opposite target law. When a law has a proved non-quasigroup model, its remaining cells read “Not applicable”.</p></details><div id="focused"></div><section class="panel"><p id="row-count"></p><div class="table-wrap"><table class="parastrophe-table"><thead><tr><th>Equation</th>${FIELDS.map(([, ,label]) => `<th>${esc(label)}</th>`).join("")}</tr></thead><tbody id="parastrophe-rows"></tbody></table></div><div class="pager"><button class="secondary" id="previous">Previous</button><span id="page-count"></span><button class="secondary" id="next">Next</button></div></section>`;
  $("build-info").textContent = `Parastrophe data generated ${new Date(data.generated).toLocaleString()}${data.local ? " from local, uncommitted sources; refresh after committing to publish source links." : ` · ${data.repository} @ ${data.commit.slice(0,8)}.`}`;
  let page = 0;
  function show() {
    const scope = $("scope").value, query = $("search").value.trim(), id = validEquation(query),
      q = query.toLowerCase(), filter = $("quasigroup-filter").value, unproved = $("only-unproved").checked;
    const representatives = $("only-representatives").checked, implication = scope === "all" ? all : fin;
    const ids = representatives ? implication.groups.map(g => g[0]) : index.equations.map((_,i) => i+1);
    const rows = ids.filter(eq => {
      const status = board.get(eq,scope,"quasigroup").status;
      const members = representatives ? implication.groups[implication.classOf[eq]] : [eq];
      return (!query || (id ? members.includes(id) : members.some(i => index.equations[i-1].toLowerCase().includes(q)))) &&
        (filter === "any" || (filter === "yes" ? status === 1 : filter === "no" ? status === 2 : ![1,2].includes(status))) &&
        (!unproved || board.unproved(eq,scope));
    });
    const pages = Math.max(1,Math.ceil(rows.length/40)); page = Math.min(page,pages-1);
    $("focused").innerHTML = id ? overviewHTML(board,id) : "";
    $("row-count").textContent = `${rows.length.toLocaleString()} ${representatives ? "implication classes" : "laws"} match · ${scope === "all" ? "finite or infinite models" : "finite models only"}. Select a status for its witness and Lean sources.`;
    $("parastrophe-rows").innerHTML = rows.slice(page*40,(page+1)*40).map(eq =>
      `<tr><th>${eqLink(eq,`implies-${scope}`)}<div><small>${esc(index.equations[eq-1])}</small></div></th>${FIELDS.map(([k,s]) => `<td>${cellHTML(board,eq,scope,k,s)}</td>`).join("")}</tr>`).join("");
    $("page-count").textContent = `Page ${page+1} of ${pages}`;
    $("previous").disabled = page === 0; $("next").disabled = page+1 >= pages;
  }
  $("parastrophe-controls").onsubmit = event => {
    event.preventDefault(); page = 0;
    const url = new URL(location);
    for (const key of ["eq","q","flavour","quasigroup","unproved","representatives"]) url.searchParams.delete(key);
    const query = $("search").value.trim();
    if (query) url.searchParams.set(validEquation(query) ? "eq" : "q",query);
    url.searchParams.set("flavour",$("scope").value);
    if ($("quasigroup-filter").value !== "any") url.searchParams.set("quasigroup",$("quasigroup-filter").value);
    if ($("only-unproved").checked) url.searchParams.set("unproved","1");
    if ($("only-representatives").checked) url.searchParams.set("representatives","1");
    history.replaceState(null,"",url); show();
  };
  $("previous").onclick = () => {page--;show();}; $("next").onclick = () => {page++;show();};
  show();
} catch (e) { error(e); }
