"""Conservative presentation summaries for the 17 open spectrum families.

Only PROVED lower bounds, individually proved examples/exclusions, and proved
tails determine the displayed orders. Multiplication uses HasModel.mul. The
small parser accepts the catalogue's set-expression grammar, never Python or
Lean code. Unsupported syntax is an export error rather than a guessed bound.
"""

from math import isqrt
from functools import cache
from pathlib import Path
import json
import re

from spectrum_note import ALIASES


NOTES = {
    63: "Constructive designs and finite witnesses reduce the question to finitely many orders. "
        "The cited construction at order 90 has an invalid intermediate model; this does not "
        "prove nonexistence at 90.",
    467: "Odd sums of two squares come from the Gaussian construction. Idempotent E63 "
         "constructions provide cubes and an explicit cofinite bound; the remaining small "
         "orders require further constructions or exclusions.",
    667: "Loops, finite-field designs, and idempotent E63 models give a proved cofinite bound. "
         "The remaining finite list is not resolved by the existing field constructions.",
    670: "Cofiniteness is proved in Lean, including idempotent models at every sufficiently "
         "large order. Seeds 9, 11, and 16 give design period 2, and both parity classes "
         "are filled. No numerical cutoff has been extracted.",
    677: "Cofiniteness is proved in Lean, including design existence and the group "
         "fillings that cover every residue. A checked computer-assisted construction "
         "now gives every order ≥ 42,239,519; the finite certificates for that numerical "
         "bound await Lean verification. Fourth powers and models at 6487, 6493, and "
         "6499 have symbolic Lean proofs.",
    704: "Left division in idempotent E63 models gives cubes and an explicit cofinite bound. "
         "Finite-field witnesses and products fill further small orders.",
    883: "Loops, finite-field designs, and idempotent E63 transfer give a proved cofinite "
         "bound. Order 9 is excluded in Lean; the same spectrum bounds apply to E1323, "
         "E1526, and their duals.",
    907: "Every sufficiently large odd order has an idempotent model, proved in Lean "
         "using constructive designs with block sizes 3 and 23. No numerical cutoff "
         "has been extracted. Order 8 is excluded in Lean by first-row normalization "
         "and checked refutations. Commutative and group-affine models are proved to "
         "have odd order in Lean; arbitrary even-order models remain unresolved.",
    1076: "Explicit finite-field seeds and transversal-design gluing give an idempotent "
          "model at every order ≥ 107773, proved in Lean. Only finitely many smaller "
          "orders remain to classify; this proof does not use Wilson's theorem.",
    1083: "Cofiniteness is proved in Lean, including design existence for blocks "
          "{7,9,16}. The explicit bound above is proved by checked construction "
          "certificates that await Lean verification. Squares, 119(30t+2)²−6, and "
          "1008·1009^(t+1)+11 are proved for t ≥ 0; orders 50 and 113 are also proved.",
    1110: "The Fibonacci companion construction gives every square order in Lean. "
          "Idempotent E63 left division also gives cubes and an explicit cofinite bound.",
    1279: "The opposite of left division in idempotent E63 models gives cubes and an "
          "explicit cofinite bound. Further finite-field witnesses supply smaller orders.",
    1286: "Cofiniteness is proved in Lean using the design-existence theorem "
          "shared with E1083. The explicit bound above is proved by checked "
          "construction certificates that await Lean verification. Fourth powers, "
          "119(30t+2)⁴−6, 224(30t+1)⁴−6, and 1008·1009^(t+1)+11 are proved "
          "for t ≥ 0; the 32-point binary matrix seed and order 113 are also proved.",
    1313: "The same explicit construction as E1076 gives idempotent models at every "
          "order ≥ 107773 in Lean. This resolves the source's conflicting cofiniteness "
          "claims; the remaining questions concern smaller orders.",
    1483: "Every square and twice a square is included. A model at any other order would "
          "separate this spectrum from E1485. Nontrivial idempotent models are impossible, "
          "so they cannot supply the missing orders.",
    1486: "Graph covers, splitting, and matching witnesses provide the useful general "
          "constructions. Nontrivial idempotent models are impossible; the remaining "
          "small orders need different witnesses or exclusions.",
    1516: "Idempotent E63 models give cubes and an explicit cofinite bound. New "
          "homogeneous models at orders 31 and 41, with their design extensions, "
          "supply further small orders in Lean.",
}

FAMILY_LABELS = {
    "squares": "Squares", "twiceSquares": "Twice a square", "cubes": "Cubes",
    "fourthPowers": "Fourth powers", "oddSumTwoSquares": "Odd sums of two squares",
    "sumTwoSquares": "Sums of two squares", "shiftedSquares": "Squares plus 2 (base at least 3)",
    "powersTwo": "Powers of two",
    "quarticTailSeeds": "Finite design constructions",
    "designPairOrders": "1008·1009^(t+1)+11 (t ≥ 0)",
    "commonPointSquareOrders": "119(30t+2)²−6 (t ≥ 0)",
    "commonPointFourthOrders": "119(30t+2)⁴−6 (t ≥ 0)",
    "binaryPointFourthOrders": "224(30t+1)⁴−6 (t ≥ 0)",
}
TOKEN = re.compile(r"Set\.Ici|[0-9]+|[A-Za-z][A-Za-z0-9]*|[∪∅ℕ(){},:]")


class FormulaParser:
    def __init__(self, text):
        self.tokens = []
        self.pos = 0
        offset = 0
        while offset < len(text):
            if text[offset].isspace():
                offset += 1
                continue
            match = TOKEN.match(text, offset)
            if not match:
                raise ValueError(f"Unsupported spectrum formula near {text[offset:offset+24]!r}")
            self.tokens.append(match.group())
            offset = match.end()

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or expected is not None and token != expected:
            raise ValueError(f"Expected {expected or 'formula token'}, found {token!r}")
        self.pos += 1
        return token

    def number(self):
        token = self.take()
        if not token.isdecimal():
            raise ValueError(f"Expected a natural number, found {token!r}")
        return int(token)

    def finite_set(self):
        if self.peek() == "∅":
            self.take()
            return frozenset()
        self.take("{")
        values = []
        if self.peek() != "}":
            values.append(self.number())
            while self.peek() == ",":
                self.take()
                values.append(self.number())
        self.take("}")
        return frozenset(values)

    def atom(self):
        token = self.peek()
        if token == "(":
            self.take()
            value = self.expression()
            self.take(")")
            return value
        if token in ("{", "∅"):
            return ("finite", self.finite_set())
        if token == "Set.Ici":
            self.take()
            cutoff = self.number()
            if cutoff == 0:
                raise ValueError("A positive spectrum tail must start above zero")
            return ("tail", cutoff)
        if token == "positiveExcept":
            self.take()
            return ("positiveExcept", self.finite_set())
        if token == "residues":
            self.take()
            modulus = self.number()
            if modulus == 0:
                raise ValueError("Residue modulus must be positive")
            return ("residues", modulus, self.finite_set(), self.finite_set())
        if token in FAMILY_LABELS:
            return (self.take(),)
        raise ValueError(f"Unsupported spectrum formula atom {token!r}")

    def expression(self):
        children = [self.atom()]
        while self.peek() == "∪":
            self.take()
            children.append(self.atom())
        if self.peek() == ":":
            self.take()
            self.take("Set")
            self.take("ℕ")
        return children[0] if len(children) == 1 else ("union", *children)

    def parse(self):
        value = self.expression()
        if self.peek() is not None:
            raise ValueError(f"Unexpected trailing spectrum token {self.peek()!r}")
        return value


def parse_formula(text):
    return FormulaParser(text).parse()


def _powers(limit, exponent, factor=1, shift=0, start=1):
    result = set()
    k = start
    while factor*k**exponent+shift <= limit:
        result.add(factor*k**exponent+shift)
        k += 1
    return result


@cache
def quartic_seed_orders():
    certificate = Path(__file__).resolve().parent.parent / "data/spectrum/quartic_tail_certificate.json"
    return frozenset(int(n) for n in json.loads(certificate.read_text())["models"] if int(n) > 0)


def formula_orders(node, limit):
    kind = node[0]
    if kind == "union":
        return set().union(*(formula_orders(child, limit) for child in node[1:]))
    if kind == "finite":
        return {n for n in node[1] if 0 < n <= limit}
    if kind == "tail":
        return set(range(node[1], limit+1))
    if kind == "quarticTailSeeds":
        return {n for n in quartic_seed_orders() if n <= limit}
    if kind == "designPairOrders":
        values, power = set(), 1009
        while 1008*power+11 <= limit:
            values.add(1008*power+11)
            power *= 1009
        return values
    if kind in ("commonPointSquareOrders", "commonPointFourthOrders", "binaryPointFourthOrders"):
        degree = 2 if kind == "commonPointSquareOrders" else 4
        coefficient = 224 if kind == "binaryPointFourthOrders" else 119
        values, base = set(), 1 if kind == "binaryPointFourthOrders" else 2
        while coefficient*base**degree-6 <= limit:
            values.add(coefficient*base**degree-6)
            base += 30
        return values
    if kind == "positiveExcept":
        return set(range(1, limit+1)) - node[1]
    if kind == "residues":
        return {n for n in range(1, limit+1) if n % node[1] in node[2] and n not in node[3]}
    if kind in ("squares", "cubes", "fourthPowers"):
        return _powers(limit, {"squares": 2, "cubes": 3, "fourthPowers": 4}[kind])
    if kind == "twiceSquares":
        return _powers(limit, 2, factor=2)
    if kind == "shiftedSquares":
        return _powers(limit, 2, shift=2, start=3)
    if kind == "powersTwo":
        return {1 << k for k in range(limit.bit_length()) if 1 << k <= limit}
    if kind in ("sumTwoSquares", "oddSumTwoSquares"):
        values = {a*a+b*b for a in range(isqrt(limit)+1) for b in range(isqrt(limit)+1)
                  if 0 < a*a+b*b <= limit}
        return values if kind == "sumTwoSquares" else {n for n in values if n % 2}
    raise ValueError(f"Unsupported spectrum family {kind!r}")


def _cutoff(node):
    if node[0] == "tail":
        return node[1]
    if node[0] == "positiveExcept":
        return max(node[1], default=0)+1
    if node[0] == "union":
        cutoffs = [value for child in node[1:] if (value := _cutoff(child)) is not None]
        return min(cutoffs, default=None)
    if node[0] == "residues" and set(range(node[1])).issubset(node[2]):
        return max(node[3], default=0)+1
    return None


def _labels(node):
    if node[0] == "union":
        return [label for child in node[1:] for label in _labels(child)]
    if node[0] == "finite":
        return ["Finite witnesses"] if any(n > 1 for n in node[1]) else []
    if node[0] in ("positiveExcept", "tail"):
        return []  # The explicit tail is added after combining all proved inputs.
    if node[0] == "residues":
        allowed = ", ".join(map(str, sorted(node[2]))) or "none"
        label = f"Residues {allowed} modulo {node[1]}"
        if node[3]:
            label += "; excluding " + ", ".join(map(str, sorted(node[3])))
        return [label]
    return [FAMILY_LABELS[node[0]]]


def _positive_order(value):
    if type(value) is not int or value <= 0:
        raise ValueError(f"Expected a positive model order, found {value!r}")
    return value


def overview(record):
    """Return the UI schema for an UNKNOWN spectrum; never upgrade paper evidence."""
    if record.get("mathematical_status", "UNKNOWN") != "UNKNOWN":
        raise ValueError("Spectrum overview requires an UNKNOWN exact spectrum")
    base = record.get("pdf_representative", record.get("equation"))
    seen = set()
    while base in ALIASES:
        if base in seen:
            raise ValueError("Spectrum alias cycle")
        seen.add(base)
        base = ALIASES[base]
    if base not in NOTES:
        raise ValueError(f"No open-spectrum overview note for E{base}")

    formula = record.get("lower_bound_formula")
    parsed = parse_formula(formula) if formula else None
    proved = parsed if record.get("lower_bound_proof_status") == "PROVED" else None
    cutoff = _cutoff(proved) if proved else None
    explicit_cutoff = record.get("cofinite_cutoff")
    if explicit_cutoff is not None:
        _positive_order(explicit_cutoff)
        if record.get("cofinite_proof_status") == "PROVED":
            cutoff = min(cutoff, explicit_cutoff) if cutoff is not None else explicit_cutoff
    through = cutoff-1 if cutoff is not None else 64
    limit = max(64, through)
    included = formula_orders(proved, limit) if proved else set()
    included.add(1)  # Every magma equation has its one-element model.
    examples = set()
    for example in record.get("included_examples", []):
        if isinstance(example, dict):
            if example.get("status") != "PROVED":
                continue
            example = example["order"]
        examples.add(_positive_order(example))
    included.update(n for n in examples if n <= limit)
    if cutoff is not None:
        included.update(range(cutoff, limit+1))

    # Proper factors are smaller: one ascending pass gives the entire product closure.
    for n in range(2, limit+1):
        if n not in included and any(n % d == 0 and d in included and n//d in included
                                     for d in range(2, isqrt(n)+1)):
            included.add(n)

    excluded, pending = set(), set()
    for entry in record.get("exclusions", []):
        n = _positive_order(entry["order"])
        if entry.get("status") == "PROVED":
            excluded.add(n)
        elif entry.get("status") in ("PROOF_AVAILABLE", "NOTE_GAP"):
            pending.add(n)
    pending.difference_update(excluded)
    contradictions = {n for n in excluded | pending
                      if n in included or cutoff is not None and n >= cutoff or n in examples}
    if contradictions:
        raise ValueError(f"Inconsistent spectrum evidence at orders {sorted(contradictions)}")

    labels = _labels(proved) if proved else []
    if any(n > 1 for n in examples):
        labels.append("Finite witnesses")
    if cutoff is not None:
        labels.append(f"All orders ≥ {cutoff}")
    labels = list(dict.fromkeys(labels))
    labels.append("Products of proved model orders")
    if cutoff is not None:
        count = sum(n < cutoff for n in included)
        summary = f"Models exist at every order ≥ {cutoff} and at {count} smaller orders."
    else:
        families = [label for label in labels if label not in
                    ("Finite witnesses", "Products of proved model orders")]
        prefix = "; ".join(families) + "; examples and products" if families else "Proved examples and products"
        summary = f"{prefix}. {sum(n <= 64 for n in included)} proved model orders through 64."
    return {
        "included_summary": summary,
        "note": NOTES[base],
        "open_orders": [n for n in range(1, through+1)
                        if n not in included and n not in excluded and n not in pending],
        "through": through,
        "finite": cutoff is not None,
        "pending_orders": sorted(pending),
        "included_orders": sorted(n for n in included if n <= 64),
        "excluded_orders": sorted(excluded),
        "family_labels": labels,
    }
