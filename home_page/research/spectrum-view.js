// Presentation helpers keep proved, reported, and unresolved orders separate.
const orders = (values = []) =>
  [...new Set(values.filter((n) => Number.isInteger(n) && n > 0))].sort(
    (a, b) => a - b,
  );

export function orderList(values = []) {
  const ns = orders(values),
    parts = [];
  for (let i = 0; i < ns.length; i++) {
    let j = i;
    while (j + 1 < ns.length && ns[j + 1] === ns[j] + 1) j++;
    if (j - i >= 2) parts.push(`${ns[i]}–${ns[j]}`);
    else parts.push(...ns.slice(i, j + 1).map(String));
    i = j;
  }
  return parts.join(", ");
}

export function cofinitenessOf(record) {
  const candidate = record.reported_tail;
  const reported = candidate && Number.isSafeInteger(candidate.cutoff) && candidate.cutoff > 0 &&
    ["PROVED_UNFORMALIZED", "PROOF_AVAILABLE", "NOTE_GAP"].includes(candidate.status) ? candidate : null;
  const status = record.cofinite_status === "KNOWN"
    ? record.cofinite_proof_status || "UNKNOWN"
    : "UNKNOWN";
  if (status === "PROVED") {
    const cutoff = record.cofinite_cutoff;
    return {
      status,
      reported,
      description: Number.isSafeInteger(cutoff) && cutoff > 0
        ? `Models exist at every order ≥ ${cutoff}.`
        : reported ? "Every sufficiently large order has a model."
        : "Every sufficiently large order has a model. No numerical cutoff has been extracted.",
    };
  }
  return {
    status,
    reported,
    description: ["PROOF_AVAILABLE", "NOTE_GAP"].includes(status)
      ? "Existence at every sufficiently large order is claimed, but the Lean proof is incomplete."
      : record.cofinite_status === "DISPUTED"
        ? "The source makes conflicting cofiniteness claims; no theorem is asserted."
        : "It is unknown whether every sufficiently large order has a model.",
  };
}

export function overviewOf(record) {
  const o = record.overview;
  if (!o) return null;
  const excluded = orders(o.excluded_orders),
    included = orders(o.included_orders),
    pending = orders(o.pending_orders).filter((n) => !excluded.includes(n));
  return {
    includedSummary: o.included_summary || "See the proved constructions below.",
    note: o.note || "",
    finite: o.finite === true,
    cofinite: cofinitenessOf(record).status === "PROVED",
    through: o.through ?? 64,
    included,
    excluded,
    pending,
    open: orders(o.open_orders).filter(
      (n) => !excluded.includes(n) && !pending.includes(n),
    ),
  };
}

export function remainingOf(overview) {
  if (!overview)
    return {
      label: "Open problem",
      text: "Determine the orders not covered by the bounds below.",
      scope: "",
    };
  const { open, finite, cofinite, through, pending } = overview;
  return {
    label: finite ? "Existence unresolved" : `Existence unresolved through ${through}`,
    text: open.length
      ? orderList(open)
      : pending.length && finite
        ? "Only the reported exclusions below await Lean verification."
        : finite
          ? "All positive orders are classified."
          : "No gaps in this initial segment.",
    scope: finite
      ? "This is the complete list of unresolved existence questions."
      : cofinite
        ? `Only finitely many orders remain unresolved. This list only covers orders through ${through}.`
        : "This is only an initial segment; larger orders may also remain open.",
  };
}

export const ORDER_STATES = {
  included: { symbol: "✓", label: "Model proved in Lean" },
  excluded: { symbol: "×", label: "Nonexistence proved in Lean" },
  pending: { symbol: "◇", label: "Nonexistence reported; Lean proof pending" },
  unknown: { symbol: "?", label: "Existence unresolved" },
};

export function initialOrders(record, limit = 64) {
  const overview = overviewOf(record);
  if (!overview) return [];
  const included = new Set(overview.included),
    excluded = new Set(overview.excluded),
    pending = new Set(overview.pending);
  return Array.from({ length: limit }, (_, i) => {
    const order = i + 1;
    const status = excluded.has(order)
      ? "excluded"
      : included.has(order)
        ? "included"
        : pending.has(order)
          ? "pending"
          : "unknown";
    return { order, status, ...ORDER_STATES[status] };
  });
}
