import { closure } from "./relation-comparison.js";

const numbers = (text) => (text.match(/\d+/g) || []).map(Number);
function unwrap(text) {
  let s = text.trim();
  while (s.startsWith("(") && s.endsWith(")")) {
    let depth = 0,
      whole = true;
    for (let i = 0; i < s.length - 1; i++) {
      if (s[i] === "(") depth++;
      if (s[i] === ")") depth--;
      if (!depth) {
        whole = false;
        break;
      }
    }
    if (!whole) break;
    s = s.slice(1, -1).trim();
  }
  return s;
}
// A deliberately small symbolic language. An unsupported expression stays
// unknown; a finite sample is never used to prove an infinite inclusion.
export function parseShape(text, partial = false) {
  if (!text) return null;
  const s = unwrap(text);
  let depth = 0,
    start = 0;
  const parts = [];
  for (let i = 0; i < s.length; i++) {
    if ("({".includes(s[i])) depth++;
    if (")}".includes(s[i])) depth--;
    if (!depth && s[i] === "∪") {
      parts.push(s.slice(start, i));
      start = i + 1;
    }
  }
  if (parts.length) {
    parts.push(s.slice(start));
    const terms = parts.map((x) => parseShape(x, partial));
    if (!partial && terms.some((x) => !x)) return null;
    const good = terms.filter(Boolean);
    return good.length ? { type: "union", terms: good } : null;
  }
  if (s === "{n : ℕ | 0 < n}" || s === "POSITIVE")
    return { type: "cofinite", excluded: [] };
  if (s === "SINGLETON") return { type: "finite", values: [1] };
  if (/^\{[\d,\s]+\}(\s*:\s*Set ℕ)?$/.test(s))
    return { type: "finite", values: numbers(s) };
  if (/^positiveExcept\s+(\{[\d,\s]*\}|∅)$/.test(s))
    return { type: "cofinite", excluded: numbers(s) };
  const residue = s.match(
    /^residues\s+(\d+)\s+(\{[\d,\s]*\}|∅)\s+(\{[\d,\s]*\}|∅)$/,
  );
  if (residue)
    return {
      type: "residues",
      modulus: +residue[1],
      allowed: numbers(residue[2]),
      excluded: numbers(residue[3]),
    };
  const tail = s.match(/^Set.Ici\s+(\d+)$/);
  if (tail) return { type: "tail", cutoff: +tail[1] };
  if (
    [
      "squares",
      "twiceSquares",
      "cubes",
      "fourthPowers",
      "sumTwoSquares",
      "oddSumTwoSquares",
      "powersTwo",
    ].includes(s)
  )
    return { type: s };
  return null;
}
export function contains(shape, n) {
  if (!shape || !Number.isSafeInteger(n) || n <= 0) return false;
  const square = (x) => Number.isInteger(Math.sqrt(x));
  switch (shape.type) {
    case "finite":
      return shape.values.includes(n);
    case "cofinite":
      return !shape.excluded.includes(n);
    case "residues":
      return (
        shape.allowed.includes(n % shape.modulus) && !shape.excluded.includes(n)
      );
    case "tail":
      return n >= shape.cutoff;
    case "union":
      return shape.terms.some((s) => contains(s, n));
    case "squares":
      return square(n);
    case "twiceSquares":
      return n % 2 === 0 && square(n / 2);
    case "cubes":
      return Math.round(Math.cbrt(n)) ** 3 === n;
    case "fourthPowers":
      return square(n) && square(Math.sqrt(n));
    case "powersTwo":
      return 2 ** Math.round(Math.log2(n)) === n;
    case "oddSumTwoSquares":
      if (!(n % 2)) return false; // falls through
    case "sumTwoSquares":
      for (let a = 0; a * a <= n; a++) if (square(n - a * a)) return true;
      return false;
    default:
      return false;
  }
}
function residueImage(s, m) {
  if (s.type === "union") {
    const images = s.terms.map((t) => residueImage(t, m));
    return images.some((x) => !x) ? null : [...new Set(images.flat())];
  }
  if (s.type === "finite") return s.values.map((n) => n % m);
  if (s.type === "residues")
    return Array.from({ length: m * s.modulus }, (_, n) => n)
      .filter((n) => s.allowed.includes(n % s.modulus))
      .map((n) => n % m);
  if (["cofinite", "tail"].includes(s.type))
    return Array.from({ length: m }, (_, n) => n);
  if (s.type === "powersTwo") {
    const seen = new Set();
    let n = 1 % m;
    while (!seen.has(n)) {
      seen.add(n);
      n = (2 * n) % m;
    }
    return [...seen];
  }
  if (["sumTwoSquares", "oddSumTwoSquares"].includes(s.type)) {
    const out = new Set();
    for (let a = 0; a < m; a++)
      for (let b = 0; b < m; b++)
        out.add(
          s.type === "sumTwoSquares"
            ? (a * a + b * b) % m
            : ((2 * a) ** 2 + (2 * b + 1) ** 2) % m,
        );
    return [...out];
  }
  const powers = {
    squares: [1, 2],
    twiceSquares: [2, 2],
    cubes: [1, 3],
    fourthPowers: [1, 4],
  };
  if (powers[s.type]) {
    const [k, e] = powers[s.type];
    return Array.from({ length: m }, (_, n) => (k * n ** e) % m);
  }
  return null;
}
export function subset(a, b) {
  if (!a || !b) return false;
  if (JSON.stringify(a) === JSON.stringify(b)) return true;
  if (a.type === "union") return a.terms.every((t) => subset(t, b));
  if (a.type === "finite") return a.values.every((n) => contains(b, n));
  if (b.type === "union") {
    if (b.terms.some((t) => subset(a, t))) return true;
    // 2^(2k) is a square; 2^(2k+1) is twice a square.
    return (
      a.type === "powersTwo" &&
      b.terms.some((t) => t.type === "squares") &&
      b.terms.some((t) => t.type === "twiceSquares")
    );
  }
  if (b.type === "cofinite") return b.excluded.every((n) => !contains(a, n));
  if (b.type === "residues") {
    const residues = residueImage(a, b.modulus);
    return (
      !!residues &&
      residues.every((n) => b.allowed.includes(n)) &&
      b.excluded.every((n) => !contains(a, n))
    );
  }
  if (b.type === "sumTwoSquares")
    return [
      "squares",
      "twiceSquares",
      "fourthPowers",
      "powersTwo",
      "oddSumTwoSquares",
    ].includes(a.type);
  if (b.type === "squares") return a.type === "fourthPowers";
  return false;
}
export function shorthand(record) {
  if (record.exact_proof_status !== "PROVED")
    return `Spec(E${record.equation}) ?`;
  const names = {
    "{n : ℕ | 0 < n}": "ℕ₊",
    "{1}": "{1}",
    squares: "n²",
    powersTwo: "2ⁿ",
    sumTwoSquares: "a² + b² > 0",
    "squares ∪ twiceSquares": "n² or 2n²",
  };
  const f = record.exact_spectrum_formula;
  if (names[f]) return names[f];
  const shape = parseShape(f);
  if (shape?.type === "cofinite") return `ℕ₊ ∖ {${shape.excluded.join(",")}}`;
  if (shape?.type === "residues")
    return `${shape.allowed.join(",")} mod ${shape.modulus}${shape.excluded.length ? ` ∖ {${shape.excluded.join(",")}}` : ""}`;
  return f || `Spec(E${record.equation}) ?`;
}

export function spectrumBoard(data, finiteFO) {
  const n = finiteFO.groups.length,
    records = data.records;
  const declared = (name) =>
    name && data.declarations[name]?.status === "PROVED";
  const descriptors = finiteFO.groups.map((group) =>
    group.map((id) => {
      const r = records[id - 1],
        exact =
          r.exact_proof_status === "PROVED" &&
          declared(r.exact_spectrum_theorem);
      const d = {
        r,
        upper: exact
          ? parseShape(r.exact_spectrum_formula)
          : declared(r.upper_bound_theorem)
            ? parseShape(r.upper_bound_formula)
            : null,
        lower: exact
          ? parseShape(r.exact_spectrum_formula)
          : declared(r.lower_bound_theorem)
            ? parseShape(r.lower_bound_formula, true)
            : null,
        upperFormula: exact ? r.exact_spectrum_formula : r.upper_bound_formula,
        lowerFormula: exact ? r.exact_spectrum_formula : r.lower_bound_formula,
        upperRef: exact ? r.exact_spectrum_theorem : r.upper_bound_theorem,
        lowerRef: exact ? r.exact_spectrum_theorem : r.lower_bound_theorem,
      };
      d.upperBounds = d.upper
        ? [{ shape: d.upper, formula: d.upperFormula, refs: [d.upperRef] }]
        : [];
      // A pending stronger bound must not hide individually proved exclusions.
      // Spectra contain only positive orders, so these give a cofinite upper bound.
      const exclusions = (r.exclusions || []).filter((x) => declared(x.theorem));
      if (exclusions.length) {
        const cofinite = d.upper?.type === "cofinite";
        const orders = [...new Set([
          ...(cofinite ? d.upper.excluded : []),
          ...exclusions.map((x) => x.order),
        ])].sort((a, b) => a - b);
        d.upperBounds.push({
          shape: { type: "cofinite", excluded: orders },
          formula: `positiveExcept {${orders.join(", ")}}`,
          refs: [...new Set([
            ...(cofinite ? [d.upperRef] : []),
            ...exclusions.map((x) => x.theorem),
          ])],
        });
      }
      return d;
    }),
  );
  // Equivalent FO laws often repeat exactly the same spectrum evidence.
  const summaries = descriptors.map((ds) => [
    ...new Map(
      ds.map((d) => [
        JSON.stringify([d.upper, d.lower, d.r.exclusions, d.r.cofinite_cutoff]),
        d,
      ]),
    ).values(),
  ]);
  const edges = [],
    add = (e) => edges.push(e);
  for (let a = 0; a < n; a++)
    for (let b = 0; b < n; b++)
      if (a !== b) {
        const s = finiteFO.groups[a][0],
          t = finiteFO.groups[b][0];
        if (finiteFO.at(s, t) === 1)
          add({ a, b, s, t, kind: "fo", key: "definable-fin" });
        else {
          outer: for (const x of summaries[a])
            for (const y of summaries[b])
              for (const upper of x.upperBounds)
                if (subset(upper.shape, y.lower)) {
                  add({
                    a,
                    b,
                    s: x.r.equation,
                    t: y.r.equation,
                    kind: "bounds",
                    refs: [...upper.refs, y.lowerRef],
                    message:
                      "The source upper bound is contained in the target lower bound.",
                    formulas: [upper.formula, y.lowerFormula],
                  });
                  break outer;
                }
        }
      }
  const yes = closure(
    n,
    edges.map((e) => [e.a, e.b]),
  );
  function included(d, order) {
    if (contains(d.lower, order)) return { refs: [d.lowerRef] };
    const r = d.r;
    if (
      r.cofinite_cutoff &&
      order >= r.cofinite_cutoff &&
      declared(r.tail_theorem)
    )
      return { refs: [r.tail_theorem] };
    const w = r.witnesses?.find(
      (w) => w.order === order && declared(w.theorem),
    );
    if (w) return { refs: [w.theorem] };
    return null;
  }
  function excluded(d, order) {
    if (d.upper && !contains(d.upper, order)) return { refs: [d.upperRef] };
    const x = d.r.exclusions?.find(
      (x) => x.order === order && declared(x.theorem),
    );
    return x ? { refs: [x.theorem] } : null;
  }
  const negatives = [];
  // Finite search finds witnesses of NON-inclusion only. Failure finds no fact.
  const membership = summaries.map((ds) =>
    Array.from({ length: 257 }, (_, order) => {
      let pos, neg;
      if (order)
        for (const d of ds) {
          const p = !pos && included(d, order),
            n = !neg && excluded(d, order);
          if (p) pos = { ...p, equation: d.r.equation };
          if (n) neg = { ...n, equation: d.r.equation };
        }
      return { pos, neg };
    }),
  );
  for (let a = 0; a < n; a++)
    for (let b = 0; b < n; b++) {
      const order = membership[a].findIndex(
        (m, order) => m.pos && membership[b][order].neg,
      );
      if (order > 0)
        negatives.push({
          a,
          b,
          order,
          s: membership[a][order].pos.equation,
          t: membership[b][order].neg.equation,
          refs: [
            ...membership[a][order].pos.refs,
            ...membership[b][order].neg.refs,
          ],
        });
    }
  const no = Array.from({ length: n }, () => Array(n).fill(null));
  for (const witness of negatives)
    for (let a = 0; a < n; a++)
      if (yes[witness.a][a])
        for (let b = 0; b < n; b++) if (yes[b][witness.b]) no[a][b] ||= witness;
  for (let a = 0; a < n; a++)
    for (let b = 0; b < n; b++)
      if (yes[a][b] && no[a][b])
        throw Error(
          `Conflicting spectral evidence at E${finiteFO.groups[a][0]} → E${finiteFO.groups[b][0]}.`,
        );
  const groups = [],
    origins = [],
    seen = new Set(),
    classOf = Array(records.length + 1).fill(null);
  for (let a = 0; a < n; a++)
    if (!seen.has(a)) {
      const origin = [];
      for (let b = a; b < n; b++)
        if (yes[a][b] && yes[b][a]) {
          seen.add(b);
          origin.push(b);
        }
      const group = origin
        .flatMap((b) => finiteFO.groups[b])
        .sort((x, y) => x - y);
      origins.push(origin);
      groups.push(group);
    }
  const order = groups
    .map((_, i) => i)
    .sort((a, b) => groups[a][0] - groups[b][0]);
  const sorted = order.map((i) => groups[i]),
    base = order.map((i) => origins[i][0]);
  sorted.forEach((g, c) => g.forEach((id) => (classOf[id] = c)));
  const size = sorted.length,
    matrix = new Uint8Array(size * size),
    possibleMerges = [];
  for (let a = 0; a < size; a++)
    for (let b = 0; b < size; b++)
      matrix[a * size + b] = yes[base[a]][base[b]]
        ? 1
        : no[base[a]][base[b]]
          ? 2
          : 0;
  for (let a = 0; a < size; a++)
    for (let b = a + 1; b < size; b++)
      if (matrix[a * size + b] !== 2 && matrix[b * size + a] !== 2)
        possibleMerges.push([a, b]);
  const adj = Array.from({ length: n }, () => []);
  edges.forEach((e) => adj[e.a].push(e));
  function path(s, t) {
    const a = finiteFO.classOf[s],
      b = finiteFO.classOf[t];
    if (a === b)
      return s === t ? [] : [{ s, t, kind: "fo", key: "definable-fin" }];
    const prev = new Map([[a, null]]),
      queue = [a];
    for (const c of queue)
      for (const e of adj[c])
        if (!prev.has(e.b)) {
          prev.set(e.b, e);
          queue.push(e.b);
        }
    if (!prev.has(b)) throw Error("Missing spectral inclusion path.");
    const steps = [];
    let c = b;
    while (c !== a) {
      const e = prev.get(c);
      steps.push(e);
      c = e.a;
    }
    steps.reverse();
    const out = [];
    let last = s;
    for (const e of steps) {
      if (last !== e.s)
        out.push({ s: last, t: e.s, kind: "fo", key: "definable-fin" });
      out.push(e);
      last = e.t;
    }
    if (last !== t) out.push({ s: last, t, kind: "fo", key: "definable-fin" });
    return out;
  }
  return {
    key: "spectrum-fin",
    label: "Spectrum inclusion",
    flavour: "fin",
    classes: size,
    description:
      "Every positive finite order admitting an A-model also admits a B-model: Spec(A) ⊆ Spec(B).",
    groups: sorted,
    classOf,
    matrix,
    possibleMerges,
    unresolved_equivalence_pairs: possibleMerges.length,
    labels: sorted.map((g) => {
      const r = g
        .map((id) => records[id - 1])
        .find(
          (r) =>
            r.exact_proof_status === "PROVED" &&
            declared(r.exact_spectrum_theorem),
        );
      return r ? shorthand(r) : `Spec(E${g[0]}) ?`;
    }),
    at(s, t) {
      return matrix[classOf[s] * size + classOf[t]];
    },
    explain(s, t) {
      const status = this.at(s, t);
      if (status === 1) return { status, path: path(s, t) };
      if (status === 0) return { status };
      const witness = no[finiteFO.classOf[s]][finiteFO.classOf[t]];
      return {
        status,
        witness,
        left: path(witness.s, s),
        right: path(t, witness.t),
      };
    },
  };
}
