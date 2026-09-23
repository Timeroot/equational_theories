"""Emit kernel-checked idempotent E1489 seeds for the transversal construction."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def certificate_files():
    seeds = json.loads((ROOT / "data/spectrum/1489_idempotent_seeds.json").read_text())
    expected = [n for n in range(1, 35) if n not in (2, 4)]
    if sorted(map(int, seeds)) != expected:
        raise ValueError("E1489 seeds must cover precisely 1 <= n < 35, except 2 and 4")
    lines = [
        "import equational_theories.Spectrum.Idempotent1489",
        "import Mathlib.Data.Fin.VecNotation", "",
        "/-! Generated finite seeds. Every table is checked by ordinary kernel reduction. -/",
        "set_option maxRecDepth 16384", "set_option maxHeartbeats 4000000", "",
        "namespace Spectrum.Idempotent1489.Seeds", "",
    ]
    for n in expected:
        table = seeds[str(n)]
        if len(table) != n * n or any(not 0 <= x < n for x in table):
            raise ValueError(f"Invalid table of order {n}")
        op = lambda x, y: table[n * x + y]
        if not all(op(x, x) == x and all(op(op(y, x), op(y, op(x, y))) == x
                                        for y in range(n)) for x in range(n)):
            raise ValueError(f"Invalid idempotent E1489 model of order {n}")
        rows = ["![" + ", ".join(map(str, table[n*i:n*(i+1)])) + "]" for i in range(n)]
        lines += [
            f"def op{n} (x y : Fin {n}) : Fin {n} :=",
            "  ![" + ",\n    ".join(rows) + "] x y", "",
            f"def model{n} : Idempotent1489 (Fin {n}) where",
            f"  op := op{n}", "  idem := by decide", "  law := by decide", "",
        ]
    lines += [
        "theorem exists_small {n : ℕ} (hn : n < 35) (h2 : n ≠ 2) (h4 : n ≠ 4) :",
        "    Nonempty (Idempotent1489 (Fin n)) := by",
        "  interval_cases n",
        "  · exact ⟨⟨fun x => Fin.elim0 x, fun x => Fin.elim0 x, fun x => Fin.elim0 x⟩⟩",
    ]
    for n in range(1, 35):
        lines.append(f"  · exact (h{n} rfl).elim" if n in (2, 4) else f"  · exact ⟨model{n}⟩")
    lines += ["", "spectrum_assert exists_small complete", "",
              "end Spectrum.Idempotent1489.Seeds", ""]
    return {ROOT / "equational_theories/Spectrum/Generated/Idempotent1489Seeds.lean": "\n".join(lines)}


if __name__ == "__main__":
    for path, source in certificate_files().items():
        path.write_text(source)
