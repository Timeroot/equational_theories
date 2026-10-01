import {
  escapeHTML as esc,
  badge,
  sourceHTML,
  proofButton,
  href,
} from "./shared.js";

export function spectrumProofHTML(proof, data, index) {
  const sources = (refs) =>
    `<ul class="sources">${[...new Set(refs)]
      .map((name) => `<li>${sourceHTML(data.declarations[name], index)}</li>`)
      .join("")}</ul>`;
  const path = (steps) =>
    steps
      .map(
        (e) =>
          `<div class="proof-step"><strong>Spec(E${e.s}) ⊆ Spec(E${e.t})</strong>${
            e.kind === "fo"
              ? `<p>Finite FO definability preserves the underlying cardinality. ${proofButton(e.s, e.t, "definable-fin", 1)} <small>Inspect the defining-relation proof.</small></p>`
              : `<p>${esc(e.message)}</p><p><code>${esc(e.formulas[0])} ⊆ ${esc(e.formulas[1])}</code></p>${sources(e.refs)}`
          }</div>`,
      )
      .join("");
  let html = `<p>${badge(proof.status)}</p>`;
  if (proof.status === 0)
    return (
      html +
      "<p>No spectral inclusion or separating order has been established by the loaded evidence. Matching known orders or bounds does not establish equality.</p>"
    );
  if (proof.path)
    html += proof.path.length
      ? path(proof.path)
      : "<p>Reflexivity: a spectrum is contained in itself.</p>";
  else {
    const w = proof.witness;
    html += `<p><strong>Separating order: ${w.order}.</strong> E${w.s} has a model of this size, while E${w.t} does not.</p>${sources(w.refs)}
      <p><a href="${href("spectrum", { eq: w.s })}">Source spectrum</a> · <a href="${href("spectrum", { eq: w.t })}">Target spectrum</a></p>`;
    if (proof.left.length || proof.right.length)
      html += `<p>These inclusions transfer the separating order to the requested pair:</p>${path(proof.left)}${path(proof.right)}`;
  }
  return (
    html +
    '<p class="muted">Spectrum comparisons are logical consequences of the linked Lean results. Set inclusions and separating-order calculations are computed by the viewer; there may be no separate Lean declaration for this particular comparison. Unformalized bounds and guessed formulas are not used to prove these arrows.</p>'
  );
}
