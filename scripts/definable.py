"""Closure of the definability relations, computed from what the Lean development proves.

`equational_theories/Definability/` states individual facts; almost none of the grid is written
down explicitly, because the grid has 4694 * 4694 cells. What is written down are the generators:
the implication graph, the dual symmetry, a few hundred positive definitions and a few thousand
refutation certificates. Everything else follows by closure, and this script does the closing.

## The relations

There are five, defined in `Definability/Basic.lean`, and each comes in two flavours depending on
whether the magmas quantified over are arbitrary or finite. Write `t <= s` for "`t` is R-definable
from `s`". The entailments between them, all proved in `Basic.lean`, are

    implies  ==>  termStructural  ==>  structural      ==>  definable
                                  ==>  termDefinable   ==>  definable

    R over all magmas  ==>  R over finite magmas

the last because a definition that works for every magma in particular works for every finite one.
`A ==> B` means `A` holds of a pair whenever `B` does not fail to, i.e. the relation `A` is
contained in the relation `B`. So positive facts travel forwards along these arrows and negative
facts travel backwards: refuting the finite variant refutes the general one, and refuting
definability refutes all four of the others.

## The closure

Positives close under transitivity (`TermDefinable.trans` and friends, and the four `Preorder`
instances at the foot of `Basic.lean`) and along the arrows above.

Negatives close by contraposition of exactly the same two facts. If `t` is not definable from `s`,
`t` is definable from `u` and `v` is definable from `s`, then `u` is not definable from `v` --
otherwise `t <= u <= v <= s` would compose. This is the step the older version of this script did
not do at all, and it is worth tens of thousands of cells: a single refutation certificate is
never about one pair, it is about a rectangle.

## What seeds it

  * implications, and non-implications, read off the `@[equational_result]` theorems in the Lean
    sources, each of which says by its use of `Finite` whether it is about all magmas or only
    finite ones.
  * duals, from `data/duals.json`: `Simple.lean`'s `TermStructural_dual`.
  * every concrete `Law<n>.RFrom Law<m>` and `¬ Law<n>.RFrom Law<m>` in `Definability/`,
    together with the `Law<n>.RFromFin Law<m>` forms of `Definability/FiniteFlavour.lean`, which
    seed the finite column directly -- that is the only way a *positive* fact reaches it, since a
    definition that exists on every finite model but not on every model has no other statement, together
    with the four universal rows and one universal column stated there for a quantified law.
  * the symmetry-certificate rectangles of `Definability/Certs/`, which pair each family's
    `Satisfies` lists (its sources) against its `FamilyRefutes` lists (its targets).

A refutation is a finite-magma refutation exactly when its witness magma is finite, and the
witness carrier is visible in the proof: every certificate goes through `Law<n>.models_iff` at an
explicit carrier. `Fin k` and `ZMod k` are finite; `ZZ`, the Gaussian integers and the orders in
number fields used by `Definability/LinearOrders*.lean` are not. A proof whose carrier cannot be
classified is reported and treated as an all-magmas refutation only, which is the sound direction.

Usage: python3 scripts/definable.py   (from the repository root)
"""
import json
import pathlib
import re
import string

import numpy as np

N_EQ = 4694
# Matrices are (N_EQ+1) x (N_EQ+1) and 1-indexed, so that row and column indices are equation
# numbers and there is no off-by-one to get wrong. Row 0 and column 0 are never used.
SIZE = N_EQ + 1
# mat[s, t] is "equation t is R-definable from equation s", the same orientation as an implication
# s => t. Rows are sources, columns are targets.

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / 'equational_theories' / 'Definability'

RELATIONS = ['implies', 'termStructural', 'structural', 'termDefinable', 'definable']
FLAVOURS = ['all', 'fin']
# (A, B) with A contained in B: positives flow A -> B, negatives flow B -> A.
ARROWS = [(('implies', f), ('termStructural', f)) for f in FLAVOURS] + \
         [(('termStructural', f), ('structural', f)) for f in FLAVOURS] + \
         [(('termStructural', f), ('termDefinable', f)) for f in FLAVOURS] + \
         [(('structural', f), ('definable', f)) for f in FLAVOURS] + \
         [(('termDefinable', f), ('definable', f)) for f in FLAVOURS] + \
         [((r, 'all'), (r, 'fin')) for r in RELATIONS]
KEYS = [(r, f) for r in RELATIONS for f in FLAVOURS]


def toposort(keys, arrows):
    """keys ordered so that every arrow points forwards"""
    incoming = {k: {a for a, b in arrows if b == k} for k in keys}
    done, order = set(), []
    while len(order) < len(keys):
        ready = [k for k in keys if k not in done and incoming[k] <= done]
        if not ready:
            raise RuntimeError('the entailment graph has a cycle')
        order += sorted(ready)
        done |= set(ready)
    return order


ORDER = toposort(KEYS, ARROWS)


# ---------------------------------------------------------------------------------------------
# Reading the facts
# ---------------------------------------------------------------------------------------------

def eq_number(name):
    """-> the equation number, or None for a sporadic equation outside the 4694"""
    n = int(name)
    return n if 1 <= n <= N_EQ else None


def load_duals():
    """-> the involution swapping each law with its mirror image, as a permutation of 0..N_EQ"""
    with open(ROOT / 'data' / 'duals.json') as f:
        pairs = json.load(f)
    sigma = np.arange(SIZE)
    for eq, dual in pairs:
        sigma[eq], sigma[dual] = dual, eq
    return pairs, sigma


RESULT_ATTR = re.compile(r'@\[equational_result\]')
# `Facts G [satisfied] [refuted]`, the form the generated counterexample files use
RESULT_FACTS = re.compile(r'\bFacts\s+\S+\s*\[([^\]]*)\]\s*\[([^\]]*)\]', re.S)
# `theorem Equation<a>_implies_Equation<b> (G : Type*) [Magma G] (h : Equation<a> G) : Equation<b> G`
RESULT_IMPL = re.compile(r'\(\s*h\s*:\s*Equation(\d+)\s+(\w+)\s*\)\s*:\s*Equation(\d+)\s+\2\s*$')
# `theorem Equation1_true (G : Type*) [Magma G] : Equation1 G` -- only unconditional if the
# signature binds no equation as a hypothesis
RESULT_UNCOND = re.compile(r':\s*Equation(\d+)\s+\w+\s*$')
RESULT_HYP = re.compile(r'\(\s*\w+\s*:\s*Equation\d+')
# `∃ (G : Type) (_ : Magma G), Equation<a> G ∧ ¬ Equation<b> G`, one conjunct per equation
RESULT_CONJUNCT = re.compile(r'(¬\s*)?Equation(\d+)\s+\w+\b')
RESULT_FINITE = re.compile(r'\bFinite\s+\w+')
# `EquationalResult.lean` documents the attribute and `LiftingMagmaFamiliesCounterexamples.lean`
# is a generator that prints it inside a string literal; neither states a result.
RESULT_SKIP = {'EquationalResult.lean', 'LiftingMagmaFamiliesCounterexamples.lean'}


def load_implications():
    """-> (implies, not_implies), each keyed by flavour.

    Every edge of the implication graph is a theorem tagged `@[equational_result]`, and there are
    three shapes of them:

      implication    `(h : Equation<a> G) : Equation<b> G`;
      facts          a magma exhibited together with equations it satisfies and refutes, written
                     either as `Facts G [satisfied] [refuted]` or as a chain of conjuncts
                     `Equation<a> G ∧ ¬ Equation<b> G`, so every satisfied/refuted pair is a
                     non-implication;
      unconditional  an equation, such as `Equation1`, that every magma satisfies.

    Each is about arbitrary magmas unless it binds `Finite G`, in which case an implication is
    only known for finite magmas and a counterexample magma is itself finite. So a `Finite`
    implication seeds the finite relation only, while a `Finite` counterexample refutes the
    finite implication and closure carries that back to the general one.

    A `conjecture` declaration is an axiom, not a proof, and is skipped.

    This reads the Lean sources rather than the `full_entries.json` export or the edge list in
    `data/`, both of which are checked-in snapshots from November 2024 and predate several
    hundred resolutions; the export is regenerated by `lake exe extract_implications`, which
    needs the whole project built.
    """
    yes = {f: np.eye(SIZE, dtype=bool) for f in FLAVOURS}
    no = {f: np.zeros((SIZE, SIZE), dtype=bool) for f in FLAVOURS}
    counts = {'implication': 0, 'facts': 0, 'unconditional': 0, 'conjecture': 0}
    unparsed = []

    def refute(flavour, satisfied, refuted):
        sat = [s for s in map(eq_number, satisfied) if s is not None]
        ref = [t for t in map(eq_number, refuted) if t is not None]
        if sat and ref:
            no[flavour][np.ix_(sat, ref)] = True

    for path in sorted((ROOT / 'equational_theories').rglob('*.lean')):
        if path.name in RESULT_SKIP:
            continue
        text = path.read_text()
        if '@[equational_result]' not in text:
            continue
        for chunk in RESULT_ATTR.split(text)[1:]:
            # the statement is everything up to the proof
            cut = chunk.find(':=')
            statement = ' '.join((chunk[:cut] if cut >= 0 else chunk[:400]).split())
            if statement.startswith('conjecture'):
                counts['conjecture'] += 1
                continue
            flavour = 'fin' if RESULT_FINITE.search(statement) else 'all'
            if (m := RESULT_FACTS.search(statement)):
                counts['facts'] += 1
                refute(flavour, m.group(1).split(','), m.group(2).split(','))
            elif (m := RESULT_IMPL.search(statement)):
                counts['implication'] += 1
                s, t = eq_number(m.group(1)), eq_number(m.group(3))
                if s is not None and t is not None:
                    yes[flavour][s, t] = True
            elif '∃' in statement and '∧' in statement:
                counts['facts'] += 1
                body = statement[statement.index('∃'):]
                conjuncts = RESULT_CONJUNCT.findall(body[body.index(',') + 1:])
                refute(flavour, [n for neg, n in conjuncts if not neg],
                       [n for neg, n in conjuncts if neg])
            elif not RESULT_HYP.search(statement) and (m := RESULT_UNCOND.search(statement)):
                counts['unconditional'] += 1
                # every magma satisfies it, so every equation implies it
                if (t := eq_number(m.group(1))) is not None:
                    yes['all'][1:, t] = True
            else:
                unparsed.append(f'{path.name}: {statement[:70]}')
    print(f'equational results: {counts["implication"]:,} implications, {counts["facts"]:,} '
          f'magmas, {counts["unconditional"]} unconditional, '
          f'{counts["conjecture"]} conjectures skipped')
    if unparsed:
        print(f'  {len(unparsed)} statements not understood: {unparsed[:4]}')
    # Reading a law right to left turns every model into a model of the mirror law, so both
    # implications and counterexamples transport along the duality involution. The project's own
    # closure does this too; it is not derivable from transitivity, since a law does not in
    # general imply its dual.
    _, sigma = load_duals()
    mirror = np.ix_(sigma, sigma)
    for flavour in FLAVOURS:
        yes[flavour] |= yes[flavour][mirror]
        no[flavour] |= no[flavour][mirror]
    return yes, no


BLOCK_COMMENT = re.compile(r'/-.*?-/', re.S)
LINE_COMMENT = re.compile(r'--.*')
# `theorem`, `lemma` and `example` at the left margin start a new declaration; `private` and
# `@[...]` may precede them.
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*'
                  r'(?:theorem|lemma|example)\b', re.M)

REL_NAMES = {'Definable': 'definable', 'TermDefinable': 'termDefinable',
             'Structural': 'structural', 'TermStructural': 'termStructural'}
# The `Fin` suffix is the finite flavour of the relation, defined in `Definability/
# FiniteFlavour.lean`: `Law73.TermDefinableFromFin Law63` quantifies over finite carriers only.
FACT = re.compile(r'(¬\s*)?Law(\d+)\.(TermDefinable|Definable|TermStructural|Structural)From'
                  r'(Fin)?\s+Law(\d+)')
# `theorem foo (L : NatMagmaLaw) : Law4.TermDefinableFrom L` is a whole row at once, and dually a
# whole column. Only the unconditional form counts: Law43 and Law46 quantify over an implicit `L`
# but carry hypotheses on it, and those are written `{L : NatMagmaLaw}`.
ROW = re.compile(r'\(L : NatMagmaLaw\)\s*:\s*Law(\d+)\.'
                 r'(TermDefinable|Definable|TermStructural|Structural)From L\b')
COL = re.compile(r'\(L : NatMagmaLaw\)\s*:\s*L\.'
                 r'(TermDefinable|Definable|TermStructural|Structural)From Law(\d+)')
SATISFIES = re.compile(r'theorem\s+\w+?_satisfies_\w+\s*:\s*Satisfies\s*\(?Magma\.(\w+)[^\[]*'
                       r'\[([^\]]*)\]', re.S)
REFUTES = re.compile(r'FamilyRefutes\s+Magma\.(\w+)\s*\[([^\]]*)\]', re.S)
CARRIERS = [
    re.compile(r'@Law\d+\.models_iff\s+(\([^)]*\)|\S+)'),   # every certificate goes through this
    re.compile(r'\(G := (\([^)]*\)|[^)]+)\)'),              # ... except a handful of hand proofs
    re.compile(r':\s*Magma (\([^)]*\)|\S+)'),
]
# helper lemmas whose own signature pins the witness to a finite carrier
FINITE_LEMMAS = ('not_definableFrom_of_no_fin_model',)
# A `Satisfies`/`FamilyRefutes` pair normally refutes `DefinableFrom`, since the family is closed
# under the symmetry the source model exhibits and definability transports that symmetry forward.
# `Magma.fin2Rigid` is the other kind: its members have *no* symmetry, so the forward transport is
# vacuous and the rectangle it closes is a refutation of `StructuralFrom` instead -- structurality
# also demands definability backwards, which forces `Aut(M') = Aut(M)`. See
# `Definability/Structural.lean`.
def _classtags(n):
    """`A … Z`, then `AA …`: the exact-`End` class names `genend4.py` emits, in that order"""
    L = string.ascii_uppercase
    return [L[i] if i < 26 else L[i // 26 - 1] + L[i % 26] for i in range(n)]


STRUCTURAL_FAMILIES = {'fin2Rigid': 'structural', 'cyclic3Exact': 'structural',
                       'reflective3Exact': 'structural', 'cyclic4Exact': 'structural',
                       'rigid3': 'structural'} | {
    f'exact{t}': 'structural' for t in ('C3', 'V4', 'K4', 'S3', 'D4', 'A4',
                                        'C45', 'V45', 'C55', 'C65', 'S35', 'D45', 'D55', 'D65',
                                        'A45', 'F205', 'S45', 'A55', 'S55',
                                        'D56', 'A46', 'D66', 'C3S36', 'F206', 'S4a6', 'S4b6',
                                        'C2A46', 'C2A4b6', 'S3sq6', 'S3wr6', 'S56',
                                        'PSL7', 'F427', 'F217', 'D147', 'F207', 'S4a7',
                                        'S4b7', 'G247', 'S3wr7')} | {
    # `Magma.end3<X>` is the exact-*endomorphism* device of `Definability/ExactEnd3.lean`: mutual
    # term-definability preserves `End` and not just `Aut`, so these rectangles refute
    # `TermStructuralFrom` rather than `StructuralFrom`.
    f'end3{t}': 'termStructural' for t in string.ascii_uppercase[:24]} | {
    # `Magma.end4<X>` is the same device on `Fin 4`, where the operations cannot be enumerated:
    # `End(M) = E` pins the unit group too, so each class sits inside an invariant family that
    # `Definability/ExactAut4.lean` already knows how to classify. See `Definability/ExactEnd4`.
    f'end4{t}': 'termStructural' for t in string.ascii_uppercase[:14]} | {
    # `Magma.end5<X>`: the same device again on `Fin 5`.  An unregistered family falls through to
    # `'definable'` below, which turns eighteen honest `termStructural` rectangles into eighteen
    # false `definable` ones -- the symptom is `close()` reporting that `Equation1` both is and is
    # not definable from itself.
    f'end5{t}': 'termStructural' for t in string.ascii_uppercase[:18]} | {
    # `Magma.end6<X>`: and again on `Fin 6`, where `endwide.py` also feeds the device the groups
    # whose invariant family is far too big for an exact-`Aut` rectangle -- a class of two members
    # costs the same whichever family it was carved out of.
    f'end6{t}': 'termStructural' for t in _classtags(40)}


def carrier_is_finite(carrier):
    """-> True (finite), False (infinite), or None (cannot tell)"""
    c = carrier.strip()
    while c.startswith('(') and c.endswith(')'):
        c = c[1:-1].strip()
    if re.fullmatch(r'Fin\s+\S+', c) or re.fullmatch(r'ZMod\s+[1-9]\d*', c):
        return True
    # ZZ, the Gaussian integers, and `Golden.R`, `Plastic.R`, ... : orders in number fields, all
    # of them infinite. See Definability/LinearInt.lean, LinearGaussian.lean, LinearOrders*.lean.
    if c in ('ℤ', 'ℚ', 'ℝ', 'ℂ', 'ℤ[i]') or re.fullmatch(r'[A-Z]\w*\.R', c):
        return False
    return None


def witness_carriers(decl):
    return [m for pattern in CARRIERS for m in pattern.findall(decl)]


def parse_lean():
    """-> (positives, negatives, rows, cols, families), reading Definability/ declaration by
    declaration so that each refutation can be matched with the carrier of its witness."""
    positives, negatives = [], []
    rows, cols = [], []
    satisfies, refutes = {}, {}
    unknown_carriers, uncarried, mixed = set(), [], []
    for path in sorted(LEAN.rglob('*.lean')):
        text = LINE_COMMENT.sub('', BLOCK_COMMENT.sub('', path.read_text()))
        for tgt, rel in ROW.findall(text):
            rows.append((int(tgt), REL_NAMES[rel]))
        for rel, src in COL.findall(text):
            cols.append((int(src), REL_NAMES[rel]))
        for fam, body in SATISFIES.findall(text):
            satisfies.setdefault(fam, set()).update(
                int(x) for x in body.replace('\n', ' ').split(','))
        for fam, body in REFUTES.findall(text):
            refutes.setdefault(fam, set()).update(
                int(x) for x in body.replace('\n', ' ').split(','))
        # split into declarations so a `¬` fact can be attributed to the carrier it was proved on
        cuts = [m.start() for m in DECL.finditer(text)] + [len(text)]
        for start, stop in zip(cuts, cuts[1:]):
            decl = text[start:stop]
            found = FACT.findall(decl)
            if not found:
                continue
            seen = witness_carriers(decl)
            carriers = {carrier_is_finite(c) for c in seen}
            if any(lemma in decl for lemma in FINITE_LEMMAS):
                carriers.add(True)
            unknown_carriers |= {c for c in seen if carrier_is_finite(c) is None}
            # the witness is finite only if every carrier the proof mentions is
            finite = bool(carriers) and carriers == {True}
            if any(neg for neg, *_ in found):
                name = re.search(r'(?:theorem|lemma)\s+(\S+)', decl)
                name = f'{path.name}:{name.group(1) if name else "?"}'
                if not carriers:
                    uncarried.append(name)
                elif len(carriers) > 1:
                    mixed.append(name)
            for neg, tgt, rel, fin, src in found:
                fact = (int(src), int(tgt), REL_NAMES[rel])
                if neg:
                    # a refutation is finite-flavour if its witness is finite, or if it is stated
                    # against the finite relation outright
                    negatives.append(fact + (finite or bool(fin),))
                else:
                    # a positive says nothing about carriers, so only the relation it is stated
                    # against can make it finite-flavour
                    positives.append(fact + (bool(fin),))
    families = {f: (sorted(satisfies[f]), sorted(refutes[f]))
                for f in sorted(set(satisfies) & set(refutes))}
    # Anything reported here is counted as an all-magmas refutation only, which is the sound
    # direction: it loses the finite-magma corollary rather than inventing one.
    if unknown_carriers:
        print(f'  carriers not classified: {sorted(unknown_carriers)}')
    if uncarried:
        print(f'  {len(uncarried)} refutations name no carrier: {uncarried[:4]}')
    if mixed:
        print(f'  {len(mixed)} refutations mention both finite and infinite carriers: '
              f'{mixed[:4]}')
    return positives, negatives, rows, cols, families


# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

def transitive_closure(mat):
    """repeated squaring; `mat` must be reflexive"""
    while True:
        bigger = (mat.astype(np.float32) @ mat.astype(np.float32)) > 0
        if bigger.sum() == mat.sum():
            return mat
        mat = bigger


def compose_negatives(pos, neg):
    """`t` is not definable from `s`, `t` from `u`, `v` from `s`  ==>  `u` is not from `v`.

    In matrix form that is pos.T @ neg @ pos.T; one application saturates, since `pos` is already
    reflexive and transitively closed."""
    p = pos.astype(np.float32)
    return ((p.T @ (neg.astype(np.float32) @ p.T)) > 0)


def close(pos, neg):
    """saturate all ten preorders together, in place"""
    for key in ORDER:
        for a, b in ARROWS:
            if b == key:
                pos[key] |= pos[a]
        pos[key] = transitive_closure(pos[key])
    for key in reversed(ORDER):
        for a, b in ARROWS:
            if a == key:
                neg[key] |= neg[b]
        neg[key] = compose_negatives(pos[key], neg[key])
        clash = pos[key] & neg[key]
        if clash.any():
            s, t = (int(x) for x in np.transpose(np.nonzero(clash))[0])
            raise RuntimeError(f'{key} says Equation{t} both is and is not definable '
                               f'from Equation{s}')
    return pos, neg


def equivalence_classes(pos):
    """-> (representative of each class, class of each equation)"""
    same = pos & pos.T
    cls = np.zeros(SIZE, dtype=int)
    reps, seen = [], np.zeros(SIZE, dtype=bool)
    seen[0] = True
    for i in range(1, SIZE):
        if seen[i]:
            continue
        cls[same[i]] = len(reps)
        reps.append(i)
        seen |= same[i]
    return np.array(reps), cls


# ---------------------------------------------------------------------------------------------

def main():
    pos = {k: np.eye(SIZE, dtype=bool) for k in KEYS}
    neg = {k: np.zeros((SIZE, SIZE), dtype=bool) for k in KEYS}

    implies, not_implies = load_implications()
    for flavour in FLAVOURS:
        pos['implies', flavour] |= implies[flavour]
        neg['implies', flavour] |= not_implies[flavour]

    duals, _ = load_duals()
    for eq, dual in duals:
        pos['termStructural', 'all'][eq, dual] = True
        pos['termStructural', 'all'][dual, eq] = True
    print(f'duals: {len(duals)} pairs, term-structural both ways')

    positives, negatives, rows, cols, families = parse_lean()
    for src, tgt, rel, finite in positives:
        pos[rel, 'fin' if finite else 'all'][src, tgt] = True
    for tgt, rel in rows:
        pos[rel, 'all'][1:, tgt] = True
    for src, rel in cols:
        pos[rel, 'all'][src, 1:] = True
    for src, tgt, rel, finite in negatives:
        neg[rel, 'fin' if finite else 'all'][src, tgt] = True
    print(f'Definability/: {len(positives)} positive and {len(negatives)} negative facts, '
          f'{len(rows)} universal rows, {len(cols)} universal columns')
    print(f'  {sum(1 for f in negatives if f[3])} of the refutations have a finite witness')

    # Every symmetry certificate refutes first-order definability, and every family in
    # Definability/Certs/ lives on a `Fin k`, so these are finite-magma refutations too.
    for fam, (sources, targets) in families.items():
        rel = STRUCTURAL_FAMILIES.get(fam, 'definable')
        neg[rel, 'fin'][np.ix_(sources, targets)] = True
        print(f'  family {fam:12s} {len(sources):5,} sources x {len(targets):5,} targets '
              f'= {len(sources) * len(targets):11,} pairs  ({rel})')

    close(pos, neg)

    total = N_EQ * N_EQ - N_EQ
    print(f'\n{"relation":22s} {"classes":>8s} {"positive":>12s} {"negative":>12s} '
          f'{"open":>10s}  {"reduced open":>13s}')
    for key in KEYS:
        p, n = pos[key], neg[key]
        reps, cls = equivalence_classes(p)
        k = len(reps)
        grid = np.ix_(reps, reps)
        decided_r = (p | n)[grid].sum() - k
        open_r = k * k - k - decided_r
        name = f'{key[0]} ({key[1]})'
        print(f'{name:22s} {k:8,} {int(p.sum()) - SIZE:12,} {int(n.sum()):12,} '
              f'{total - int((p | n).sum()) + SIZE:10,}  {open_r:13,}')
    print(f'\nfull grid {total:,} ordered pairs; the reduced grid is one row and column per '
          f'definability-equivalence class')


if __name__ == '__main__':
    main()
