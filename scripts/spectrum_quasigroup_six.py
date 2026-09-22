"""Generate exhaustive six-element certificates for the completed quasigroup spectra.

Every assignment to six 18-bit rows encodes an operation. Clipping maps each
3-bit entry to Fin 6; `encoded_eq` proves that every actual magma is covered.
The SAT solver supplies only a certificate checked by Lean's native LRAT checker.
Run through `spectrum_generate.py --write` or `--check`.
"""
import itertools
from spectrum_generate import load_equations, variables

HEADER = '''import equational_theories.Spectrum.MendelsohnSix

/-! Exhaustive six-element exclusions. Each bit-vector refutation is checked
by Lean's LRAT checker, and the encoding covers every six-element magma. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace Spectrum.QuasigroupSix
open MendelsohnSix

def op (a b c d e f : BitVec 18) (x y : BitVec 3) : BitVec 3 :=
  clip (((if x = 0 then a else if x = 1 then b else if x = 2 then c
    else if x = 3 then d else if x = 4 then e else f) >>>
    (y.setWidth 18 * 3)).setWidth 3)

def rows (M : Magma (Fin 6)) (x : Fin 6) : BitVec 18 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5)
def encoded (M : Magma (Fin 6)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)

theorem encoded_eq (M : Magma (Fin 6)) (x y : Fin 6) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1
      else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3
      else if bv x = 4 then rows M 4 else rows M 5) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4, M.op x 5] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]
'''


def render(term, assignment, lift=False):
    if isinstance(term, str):
        value = assignment[term]
        return f"(bv ({value} : Fin 6))" if lift else str(value)
    operation = "encoded M" if lift else "op a b c d e f"
    return f"({operation} {render(term[0], assignment, lift)} {render(term[1], assignment, lift)})"


def certificate():
    lines = [HEADER]
    equations = load_equations()
    for law in (115, 481, 873):
        lhs, rhs = equations[law - 1]
        names = sorted(variables(lhs) | variables(rhs))
        values = list(itertools.product(range(6), repeat=len(names)))
        tests = []
        for value in values:
            assignment = dict(zip(names, value))
            tests.append(f"({render(lhs, assignment)} : BitVec 3) = {render(rhs, assignment)}")
        rows = " ".join(f"(rows M {i})" for i in range(6))
        goals = ", ".join("?_ " for _ in values)
        lines += [
            f"def test{law} (a b c d e f : BitVec 18) : Prop :=\n  " + " ∧\n  ".join(tests),
            "",
            f"@[spectrum_native]\ntheorem refute{law} (a b c d e f : BitVec 18) : "
            f"¬ test{law} a b c d e f := by\n  unfold test{law} op clip\n"
            "  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })",
            f"spectrum_assert refute{law} complete",
            "",
            f"theorem impossible{law} (M : Magma (Fin 6)) (h : @Equation{law} (Fin 6) M) : False := by\n"
            f"  have he := encoded_eq M\n  apply refute{law} {rows}\n"
            f"  unfold test{law}\n  refine ⟨{goals}⟩",
        ]
        for value in values:
            assignment = dict(zip(names, value))
            arguments = " ".join(map(str, value))
            lines += [
                f"  · change {render(lhs, assignment, True)} = {render(rhs, assignment, True)}",
                "    simp only [he]",
                f"    exact congrArg bv (h {arguments})",
            ]
        lines.append("")
    lines += ["end Spectrum.QuasigroupSix", ""]
    return "\n".join(lines)
