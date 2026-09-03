# Definability board: structural coverage, 30 Aug – 3 Sep 2026

A status report on `equational_theories/Definability/`, covering the 54 commits from
`b90f771` (Sun 30 Aug, 02:16) through `e07c90e` (Thu 3 Sep, 19:47). It has three parts:

1. what the numbers did, and which devices moved them;
2. the parastrophic term-structural witnesses, all 31 of them, in full;
3. how those witnesses line up — and fail to line up — with the `commentary/` files.

There is a fourth part nobody enjoys writing, on two integrity failures found during the week
and what they cost.

---

## 0. What is being measured

`Law_t.StructuralFrom Law_s` says: every magma `M ⊨ L_s` has a companion operation `□` on the
same carrier with `Aut (G, □) = Aut M` and `(G, □) ⊨ L_t`. `StructuralFromFin` restricts to
finite carriers. `TermStructuralFrom` is the strong form: the companion is given by a fixed
binary term `w(x, y)` in `◇`, and `◇` is recovered from `□` by a fixed binary term `v`, so the
two operations generate each other in the clone. Every `TermStructural` fact is a `Structural`
fact; the converse is open in general.

Coverage is reported two ways, and the difference matters.

* **Raw cells** — ordered pairs `(s, t)` of equation numbers, out of `4694 × 4693`.
* **Reduced cells** — first quotient by the positive relation's equivalence classes (716 for
  `fin`, 739 for `all`), then count open ordered pairs of *classes*. This is the honest measure
  of how much is left to decide: closing a cell whose class has 300 members moves the raw count
  by 300 and the reduced count by 1.

Both are computed by `scripts/definable.py`, which parses the Lean **sources** — theorem
statements, `@[equational_result]` attributes, certificate-family registrations, row and column
facts — and then takes the transitive closure. Nothing is read from a pickle or a prover log.
Reproduce with:

```
python3 scripts/definable.py            # or defwork/openlist.py <relation> <flavour>
```

---

## 1. The arc

| checkpoint | | structural/fin | structural/all | termStructural/fin |
|---|---|---|---|---|
| `95ce5d2` | Sat 29 Aug (baseline) | **68,698** (86.6%) | **70,096** (87.1%) | 19,986 (96.1%) |
| `66fccec` | Sun 30 Aug 22:35 | 65,294 (87.2%) | 66,692 (87.8%) | — |
| `d625329` | Mon 31 Aug 23:49 | 64,577 (87.4%) | 65,957 (87.9%) | — |
| `2b2cefd` | Tue 1 Sep 22:15 | 64,093 (87.5%) | 65,442 (88.0%) | — |
| `1460577` | Wed 2 Sep 21:20 | 58,887 (88.5%) | 63,114 (88.4%) | — |
| `f95be99` | Thu 3 Sep 10:51 | 58,560 (88.6%) | 63,065 (88.4%) | — |
| `cdbff7c` | Thu 3 Sep 15:58 | 58,661 (+101) | 63,166 (+101) | — |
| `3ebbba3` | Thu 3 Sep 16:24 | 58,703 (+42) | 63,166 | — |
| `e07c90e` | Thu 3 Sep 19:47 (HEAD) | **58,560** (88.6%) | **63,065** (88.4%) | **19,141** (96.3%) |

Net over the window:

| relation | reduced open | raw open | settled |
|---|---|---|---|
| `structural/fin` | 68,698 → 58,560 (**−10,138**) | 517,373 → 439,498 (−77,875) | 86.6% → 88.6% |
| `structural/all` | 70,096 → 63,065 (**−7,031**) | 519,091 → 459,924 (−59,167) | 87.1% → 88.4% |
| `termStructural/fin` | 19,986 → 19,141 (−845) | 191,939 → 180,863 (−11,076) | 96.1% → 96.3% |
| `termStructural/all` | 20,818 → 19,966 (−852) | 193,867 → 182,965 (−10,902) | 96.2% → 96.3% |

`Definability/` now holds **4,152 modules** and about **9,091** named cell theorems
(4,765 `StructuralFrom`, 979 `StructuralFromFin`, 1,567 `not_termDefinableFrom`,
1,148 `not_definableFrom`, 212 `termStructuralFrom`, 204 `termStructuralFromFin`, and the rest),
plus the certificate families, which carry their weight through `FamilyRefutes`/`Satisfies` pairs
rather than through named cells.

**A warning about commit messages.** Individual commits advertise cell counts far larger than the
net movement above — "20,768 cells", "1,896 cells", "161 reuse cells". Those numbers are honest
about what the device proved, but devices overlap heavily and the transitive closure had already
implied much of it. The table is the truth about the board; the commit messages are the truth
about the devices. Do not add them up.

### Sun 30 Aug — column-constant hubs (6 commits, −3,404 reduced fin)

The largest single day. The **column-constant device** picks a target law `t` whose companion can
be taken of the form `x □ y = c(y)`: the operation ignores its left argument, so the target
collapses to a unary condition and the automorphism obligation collapses to "every `σ ∈ Aut M`
commutes with `c`". Three generations landed 735, then 864, then 909 targets; a fourth commit
stopped inferring the naming of `T` and named it by hand, which is what let the read-back work at
all. The day closed with the **square-column family** (hub 4351) and its per-source facts.

### Mon 31 Aug — square rows, first-order division, diagonal repair (10 commits, −717)

Hub 4341 (square rows) and hub 4268 (row-image-constant) joined 4351 and 4374. `216dd0e` proved
first-order division over *all* magmas rather than only finite ones — the standing preference is
`all` over `fin` whenever it is reachable, and here it was. `d625329` introduced the **diagonal
replacement** family: companions of the shape

```
x □ y = if x = y then d x else x ◇ y
```

whose whole obligation is packaged as `AutBox.DiagFix Law_s`, one lemma per source, reusable
across every target.

### Tue 1 Sep — exact-Aut sweeps begin (8 commits, −484)

Generations three through five of the column-constant device, then the first **exact-Aut**
rectangles: for a finite group `H`, find every magma on `Fin n` with `Aut M = H` exactly, and read
off a whole rectangle of cells at once. The Fin 6 small-group half, then Fin 7. `2b2cefd` is a
bug fix — the `srch7R` small-group band was registered only up to 339.

### Wed 2 Sep — the big exact-Aut day, and the word device (12 commits, −5,206)

`04fcbd0` alone claims 20,768 cells from Fin 9 and Fin 10 exact-automorphism classes. Fin 11 and
Fin 12 followed, then `9a0c07a` replaced the CP-SAT search with straight enumeration of the family
(CP-SAT was undercounting past Fin 8). `2373fb8`/`f245ff9`/`76dca22` are the Equation 3 lane —
idempotent realizability, which is 16.5% of the board on its own. `4d37981` introduced the **word
companion device**: `x □ y = W(x, y)` for a fixed word `W`, splitting each cell into a
target-free rigidity obligation `haut` (every bijection respecting `W` respects `◇`) and a
σ-free satisfaction obligation `hsat`.

### Thu 3 Sep — guarded companions, cell replay, and cleanup (18 commits, −327 net)

The **guarded companion** generalises the diagonal one:

```
x □ y = if x = y then D x y else (if P = Q then A else B)
```

with obligation `AutBox.GuardFix P Q A B L'`. Eleven sources, then eight more; 41, then 96, then
161 reuse cells.

`f95be99` is the methodological result of the day. `grind` closes only about a third of the reuse
cells the provers settle — 64 of 180 for the diagonal companion. Pointing `vchain.leanproof` at
the *target* half of the cell, rather than only at the automorphism obligation, lands all 116 that
were stuck, none of them needing a refined step. A Vampire derivation becomes one `have` per
superposition; the negated target goes in as a **ground axiom** so no Skolemisation is needed, and
every axiom is written as a disjunction because an implication costs an `ennf transformation` step
whose parenthesised body the chain parser cannot split.

The rest of Thursday is the cleanup described in §4.

---

## 2. Parastrophic term-structural witnesses

`equational_theories/Definability/Parastrophic.lean` (2,156 lines) proves **31 directed cells**
across **28 unordered pairs** and **10 source laws**. It was committed as `97daa64` on Wed 26 Aug
— *before* this window — so it contributes **nothing** to the deltas in §1. It is reported here in
full because it is the only lane on the board that produces `TermStructural` facts by hand rather
than by search, and because it is the lane the `commentary/` files have opinions about.

### What a parastrophic witness is

`Law_t.TermStructuralFrom Law_s` needs a *pair* of binary terms:

* `w(x, y)` with `s ⊢ t[◇ := w]` — the companion satisfies the target;
* `v(x, y)` with `s ⊢ v[□ := w] = x ◇ y` — the source operation is recovered from the companion.

The second is what makes it structural rather than merely definable: `w` and `v` exhibit `◇` and
`□` as mutually term-definable, so they have the same automorphism group for free. In this file
`w` is always a *parastrophe* — a division operation of the source — and `v` is the inversion
that undoes it. The `v` half is proved once per `(source, w)` as a private `inv<src>_<hash>` lemma
and reused by every target that term reaches; it does not mention the target at all.

Lemmas named `...FromFin` need a finite carrier. The reason is `rot_of_finite`: they turn the
source law into a rotation of itself, which requires a one-sided inverse to be two-sided, which is
automatic exactly when a surjective self-map is injective.

### The twelve defining terms

| `inv` lemma | source | `w`, i.e. `x □ y :=` | used by |
|---|---|---|---|
| `inv65_73f9f1faf` | 65 | `x ◇ ((y ◇ (x ◇ y)) ◇ y)` | 359, 614, 817, 1426, 1491, 3862, 4065 |
| `inv66_1c4da5b9` | 66 | `x ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ x))` | 53 |
| `inv66_dfe2c1ca` | 66 | `(y ◇ y) ◇ x` | 2494 |
| `inv476_18005b30f` | 476 | `y ◇ (x ◇ (x ◇ y))` | 503 |
| `inv503_52c8d385f` | 503 | `(x ◇ y) ◇ (x ◇ (x ◇ y))` | 476, 3862 |
| `inv510_23d3c07e` | 510 | `x ◇ ((x ◇ y) ◇ (x ◇ y))` | 439 |
| `inv546_6e2757bf` | 546 | `x ◇ (x ◇ (x ◇ y))` | 556 |
| `inv556_4b460107` | 556 | `x ◇ ((x ◇ y) ◇ x)` | 546 |
| `inv714_fe56b280` | 714 | `y ◇ (y ◇ (x ◇ y))` | 8, 3103, 3253, 3319, 3862, 3915 |
| `inv714_4b460107` | 714 | `x ◇ ((x ◇ y) ◇ x)` | 23, 464, 1629, 1832, 3456, 3522, 4065, 4118 |
| `inv960_dd43a143` | 960 | `(x ◇ x) ◇ (y ◇ y)` | 653 |
| `inv1491_f3ffbbdd` | 1491 | `y ◇ (x ◇ y)` | 65 |

Two of these are literally the same term with different source hypotheses: `inv556_4b460107` and
`inv714_4b460107` are both `x ◇ ((x ◇ y) ◇ x)` (the shared hash is not a coincidence — the term is
content-addressed). Source 714 is the only one that needed two genuinely different divisions, and
they split its fourteen targets almost evenly.

### The 31 cells

| source | targets | flavour |
|---|---|---|
| 65 | 359, 614, 817, 1426, 1491, 3862, 4065 | `Fin` (7) |
| 66 | 53, 2494 | all magmas (2) |
| 476 | 503 | `Fin` (1) |
| 503 | 476, 3862 | `Fin` (2) |
| 510 | 439 | all magmas (1) |
| 546 | 556 | all magmas (1) |
| 556 | 546 | all magmas (1) |
| 714 | 8, 23, 464, 1629, 1832, 3103, 3253, 3319, 3456, 3522, 3862, 3915, 4065, 4118 | all magmas (14) |
| 960 | 653 | all magmas (1) |
| 1491 | 65 | all magmas (1) |

Ten cells need finiteness; twenty-one hold over all magmas. Three pairs are proved in both
directions and are therefore genuine term-structural *equivalences*: **(65, 1491)**,
**(476, 503)**, **(546, 556)**. Note the asymmetry in the first of those — `1491 → 65` holds over
all magmas but `65 → 1491` needs a finite carrier, because the division witnessing `65 → 1491` is
only surjective a priori.

Two targets are hit from two different sources: 3862 from both 503 and 714, and 4065 from both 65
and 714.

---

## 3. Cross-reference with `commentary/`

Of 771 `commentary/Equation<n>.md` files, **57** mention "parastroph". Extracting the equation
numbers named in those sentences gives **63 unordered pairs** the human commentary asserts to be
parastrophically related. Against the 28 unordered pairs `Parastrophic.lean` proves:

### 3.1 Both agree — 7 pairs

| pair | where | what the commentary says |
|---|---|---|
| (53, 66) | `Equation53.md`, `Equation66.md` | 53 holds iff left division `x ◇ (x : y) = y` satisfies 66 — "parastrophically equivalent in left quasigroups" |
| (65, 1491) | `Equation1491.md` | "in a quasigroup this law is equivalent to the Asterix law 65" |
| (439, 510) | `Equation439.md`, `Equation510.md` | left division of 510 satisfies 439; converse in left quasigroups |
| (464, 714) | `Equation714.md` | left division of 714 satisfies 464; converse when left multiplications are bijective |
| (476, 503) | `Equation476.md`, `Equation503.md` | left division of 476 satisfies 503 (credited to a Zulip thread on Austin pairs) |
| (546, 556) | `Equation546.md`, `Equation556.md` | a magma satisfying 556 is a quasigroup and its left division satisfies 546, and conversely |
| (653, 960) | `Equation960.md` | "the laws 960 and 653 are parastrophically equivalent for (left-)quasigroups" |

These are the cases where a human wrote down the parastrophe and the Lean now carries a term
witness for it in at least one direction.

One of them matches down to the term. `Equation714.md` gives the division explicitly as
`x : y = x ◇ ((x ◇ y) ◇ x)`, and `inv714_4b460107` — the witness that proves `714 → 464` in
Lean — is that term character for character. Whoever wrote the commentary and whatever found the
witness converged on the same parastrophe.

**A likely typo in `Equation714.md`.** That same sentence concludes "Thus, laws 714 and 474 are
parastrophically equivalent for (left-)quasigroups", after two sentences that are entirely about
464. The board has (474, 714) as `neg` in both directions in every flavour, while (464, 714) is
proved; `474` is almost certainly a slip for `464`.

### 3.2 Proved but unremarked — 21 pairs

Nothing in `commentary/` mentions these, and they are all genuine `TermStructuralFrom` theorems:

```
(8, 714)    (23, 714)   (65, 359)   (65, 614)   (65, 817)   (65, 1426)  (65, 3862)
(65, 4065)  (66, 2494)  (503, 3862) (714, 1629) (714, 1832) (714, 3103) (714, 3253)
(714, 3319) (714, 3456) (714, 3522) (714, 3862) (714, 3915) (714, 4065) (714, 4118)
```

Two observations.

* **Source 714 is the story.** Fourteen of the twenty-one are 714's, and none of them appear in
  the commentary. A single law with two useful divisions reaches fourteen targets over all
  magmas, which is a better yield than anything the commentary predicted.
* **(66, 2494) is a bookkeeping artifact, and a sharpenable claim.** `Equation66.md` does discuss
  2494 — "this law also implies that the right division operation … satisfies law 2494 …, but this
  is not an equivalence" — in a sentence that does not itself contain the word "parastroph", so the
  extraction in §3.6 does not pick it up. The content agrees with what is proved: the Lean theorem
  is `Equation2494_termStructuralFrom_Equation66_parastrophic`, one direction only, via
  `w = (y ◇ y) ◇ x`. Worth recording that the *one* direction is term-structural, which is strictly
  more than the implication the commentary claims.

### 3.3 Asserted but unproved — 56 pairs

The commentary claims parastrophy for 56 pairs with no witness in `Parastrophic.lean`. Most of
them are **already settled on the board by other means**, and a large fraction are settled
*negatively*:

| board status of the pair | count |
|---|---|
| at least one direction still open somewhere | **27** |
| fully settled, both directions `pos` on `termStructural/all` | 4 |
| fully settled, one direction `pos`, the other `neg` | 10 |
| fully settled, both directions `neg` | 15 |

The negatives are not contradictions. Commentary parastrophy claims are almost always
**conditional** — "in a quasigroup", "if right multiplications are bijective", "for
(left-)quasigroups". The board relation quantifies over *all* models of the source law, including
the non-quasigroup ones, so a conditional parastrophe is simply a different statement.
`commentary/Equation65.md` asserting 65 ⟺ 4443 in right quasigroups sits perfectly happily
alongside the board's `neg` for (65, 4443) in every flavour.

There is a sharper pattern inside the negatives, though, and it is the most useful thing in this
section.

### 3.4 The finiteness gap — 11 pairs worth attacking

Eleven commentary-predicted pairs are **proved on `termStructural/fin` and open on
`termStructural/all`**:

```
(124, 1648)  (206, 1648)  (417, 477)  (417, 1492)  (427, 504)  (427, 910)
(429, 473)   (437, 467)   (452, 481)  (452, 1496)  (632, 879)
```

This is exactly the shape the commentary's own hedging predicts. The parastrophe needs a division
operation, the division needs a multiplication to be bijective, and bijectivity is free on a
finite carrier and not otherwise. Each of these is a concrete open cell where the finite proof
already exists and the question is whether bijectivity can be got from the law itself.

### 3.5 All 35 open cells the commentary predicts

Directed cells, still open, where a commentary file asserts the underlying parastrophy:

**`termStructural/all` (28)**

```
125 ← 63     3548 ← 63     1648 ← 124    3343 ← 124    4130 ← 124
3548 ← 125   3954 ← 125    1648 ← 206    3343 ← 206    3548 ← 222
3548 ← 271   124 ← 1648    206 ← 1648    3343 ← 1648   4130 ← 1648
50 ← 56      117 ← 167     414 ← 440     437 ← 467     429 ← 473
417 ← 477    452 ← 481     427 ← 504     4541 ← 543    632 ← 879
427 ← 910    417 ← 1492    452 ← 1496
```

**`termStructural/fin` (3)** — `50 ← 56`, `117 ← 167`, `414 ← 440`

**`structural/fin` (4)** — `50 ← 56`, `117 ← 167`, `3 ← 332`, `414 ← 440`

The four laws `50 ← 56`, `117 ← 167`, `414 ← 440` and `3 ← 332` are open in *every* flavour and
have no positive in either direction: the commentary asserts the parastrophy, and the board knows
nothing at all. Those are the four cheapest things on this list to try, and `117 ← 167` comes with
its own recipe — `commentary/Equation117.md` gives the division explicitly as
`x : y = (y ◇ x) ◇ y`.

### 3.6 A caveat on the extraction

The 63 predicted pairs come from a regex over sentences containing "parastroph", pulling equation
numbers out of `[law N](…/implications/?N)` links and out of enumerations like
"laws 124, 3343, 384 (and their duals 206, 4130, and 335)". Enumerations of that kind generate the
full clique, so a handful of the 63 — the (124, 1648)-style pairs — are pairs the prose implies
rather than states. The seven matches and the eleven finiteness-gap pairs were checked by reading
the sentences.

---

## 4. Two integrity failures

Both were found this week, both are fixed, and both had the same root cause: **`definable.py`
reads Lean sources, so a module that nothing imports scores cells that no build ever checked.**
`lake build equational_theories.Definability` elaborates only the transitive import closure of
`Definability.lean`. Forgetting an import line is silent in both directions — the build stays
green and the board still goes up.

### 4.1 The `Wrd_*` modules — 56 declarations, 41 broken proofs

Four word-device modules sat in the tree for a day, unimported, carrying 56 board declarations of
which 41 did not elaborate. Repairing them meant applying the cell-replay technique to both halves
of the word device (`defwork/wreplay.py`): the `haut` rigidity obligation and the equational cell.
**60 of 61 obligations replayed**, 60 of those with zero refined steps.

The last one is worth recording because the diagnosis was wrong for two long passes.
`Wrd_1448`'s `haut` reported "stuck", which is the signature of a compound unifier the replay
cannot reconstruct, and 34 cells were written off. The actual cause: `vchain.render` ends with
`return names.get(t[1], 'x')`, so any variable a superposition leaves unconstrained is emitted as
the bare identifier `x`. Every device predating the word companion happens to map some constant to
a Lean variable named `x`, so the fallback had never been visible; the word device binds `a` and
`b`, and the generated step referred to an unbound `x`. Adding `have x : G := a` — the
instantiation is arbitrary, since the premises are universally quantified — makes the obligation
replay clean with **zero** refinements. All 34 cells are back.

*Lesson: when the refinement loop says "stuck", print the generated `have` before believing it.*

### 4.2 The scratch sweep — 101 reduced cells deleted by accident

`cdbff7c` deleted 68 unreachable modules. The screen behind it looked for
`theorem`/`instance` declarations naming one of the four definability relations, and **that misses
how a certificate family scores**. A family needs two files that mention no relation by name: a
`Satisfies` file listing the equations its exhibited members satisfy (the sources) and a
`FamilyRefutes` file listing the equations no member satisfies (the targets). Neither counts
alone. Forty-two `Certs/Srch{12R400,9R70[0-3]}` modules were classified inert and deleted, and
`structural/fin` and `structural/all` each went **up by 101 reduced cells**.

`e07c90e` restores them and — this time — imports them, so the build checks them: 42 `Certs`
modules, `AutShape` with the four `Shp_shp9h6s2k3*` modules behind it (four `DefinableFrom`
negatives from the mixed-arity coordinate frame, worth 1 further reduced cell), and five
`Prn_prn8h8b_L*` pruned-search refutations. 7,020 jobs, no sorries, no new axioms.

**Two of the restored files were false and are not coming back.** `Prn_prn8h8c_L3345` and
`Prn_prn8h8c_L3548` claim `Magma.searchT … = true` where `native_decide` evaluates the search to
`false` — the `prn8h8c` family *does* contain a model of 3345 and of 3548. They had never been
built, so nothing had ever checked them. They scored no cells (the board was 58,560 with and
without them), and the `Prn_prn8h8d` files with the same two targets are the correct ones and were
already imported. This is precisely the failure mode the import-closure hole allows: a false
certificate, in the tree, invisible.

### 4.3 The guard

`defwork/openlist.py` now recomputes the import closure of `Definability.lean` over the whole
tree and refuses to write a board while any unreachable module declares anything that moves it.
The pattern was widened after §4.2 from the four relation names to

```
StructuralFrom | DefinableFrom | TermDefinableFrom | TermStructural
  | FamilyRefutes | Satisfies | Magma.search[TY]
```

It currently reports zero orphans. Reachability must be computed over the whole tree, not over
`Definability/*.lean` — `Certs/` is a subdirectory, and scanning the flat directory alone reports
102 orphans where there are 72.

---

## 5. Where things stand

* `structural/fin` is **88.6% settled** by reduced cells, `structural/all` **88.4%**,
  `termStructural` **96.3%** in both flavours.
* Every module that moves the board is in the import closure of `Definability.lean`, and the
  closure builds clean at 7,020 jobs with no sorries.
* The parastrophic lane has 31 cells from 12 hand-built division terms across 10 sources, and it
  has been idle since 26 Aug.
* The commentary predicts **35 open cells** (§3.5), of which **11** (§3.4) already have a finite
  proof and need only the bijectivity argument to go through over all magmas. That is the
  best-signposted work left in this lane.
