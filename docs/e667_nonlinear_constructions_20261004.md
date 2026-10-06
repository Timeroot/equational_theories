# E667 from automorphisms, binary block data, and nonabelian groups

Research date: 2026-10-04. This continues the
[structural notes](e667_structure_20261004.md). There are two new general Lean
proofs from the first pass, now joined by the formalizations listed in the
[proof index](e667_formalization_20261004.md). These include the complete
three-class binary-extension classification, arbitrary independent block
gluing and its completeness, the nonabelian directed-triangle construction,
and the affine obstruction. The restricted search exclusions remain external
CP-SAT results, not Lean proofs.

These constructions explain noncommutative, non-idempotent, and nonmedial
models. They do **not** change the unrestricted spectrum: all 17 previously
open orders, including 12 and 15, remain open.

## 1. An involutive output twist preserves E667

Let `(Q,*)` satisfy E667, and let `J` be an involutive automorphism. Define

```
x ∘ y = J(x*y).
```

Then `∘` also satisfies E667. Expand its defining expression and push the
automorphism through the products. Since `J²=id`, the expression becomes

```
J(y) * (x * ((x*x) * J(y))) = x,
```

which is the original law at `(x,J(y))`. No finiteness is required. The
construction is its own inverse; `J` remains an automorphism of the new
operation. Commutativity is preserved and reflected because `J` is
injective. Mediality is also preserved and reflected: both outer twists in
`(x∘y)∘(z∘w)` cancel to give `(x*y)*(z*w)`.

In particular, start with an **idempotent E63** operation `p`. It already
satisfies E667. The twisted operation has square map exactly `J`, so:

* its idempotents are exactly the fixed points of `J`;
* a fixed-point-free involution gives an idempotent-free E667 model;
* a noncommutative or nonmedial starting operation retains that property.

Conversely, if an E667 model's square map `D` is an involutive automorphism,
then `p(x,y)=D(x*y)` is idempotent and satisfies E63. Thus this is an exact
description of that subclass, not merely a sufficient construction.

The public Lean declarations in `Equation667AutomorphismTwist.lean` are
`AutomorphismTwist.law`, `of_idempotent_e63`, `untwist`, `commutative_iff`,
and `medial_iff`. Their proofs use only ordinary Lean axioms.

For example, the previously classified idempotent-free eight-point model

```
x*y=(1+t)x+ty+1  over F₂[t]/(t³+t+1)
```

comes from the idempotent affine E63 model `(1+t)x+ty` by the involutive
automorphism `J(x)=x+1`. More generally, on any idempotent E63 algebra P,
swapping the factors of P×P is an involutive automorphism. Its output twist
has exactly the diagonal pairs as idempotents. This gives examples without
requiring an automorphism of P itself.

The constant-diagonal construction from semisymmetric loops is another
instance: such a loop already satisfies E667, and its involutive
automorphisms fix the identity, so the twist still has constant square.

## 2. A complete explicit family on F₅ × F₂

For an arbitrary function `v : F₅ → F₂`, define

```
(i,a) * (j,b) = (3(i+j), a+b+v(i)+v(2j-i)).
```

The first coordinate is computed modulo five and the second modulo two.
There is no linearity assumption on `v`. This is always an E667 magma.
Its square map is simply

```
D(i,a)=(i,0).
```

Consequently it has exactly five idempotents, its square map is a retraction,
and its five square fibers form a congruence with two-element classes.

Here is the full coefficient argument. Let `p(i,j)=3(i+j)` and
`C(i,j)=v(i)+v(2j-i)`. For an idempotent E63 base, the operation
`(i,a)*(j,b)=(p(i,j),a+b+C(i,j))`, with `C(i,i)=0`, satisfies E667 exactly
when

```
C(i,j)+C(i,p(i,j))+C(j,p(i,p(i,j)))=0.
```

In F₅, `2p(i,j)-i=j` and `2p(i,p(i,j))-j=2j-i`. The three terms are
therefore

```
v(i)+v(2j-i),   v(i)+v(j),   v(j)+v(2j-i),
```

and cancel in pairs. This proof, including the symbolic law for arbitrary
`v`, is formalized in `Equation667BinaryFive.lean`. The public statements
are `BinaryFive.law`, `square`, `square_retraction`, and `idempotent_iff`.
No multiplication-table search or exhaustive enumeration of functions is
used by these proofs.

If `v` is nonconstant, then `C` is nonzero: fix `i`, and `2j-i` ranges over
the whole field as `j` varies. A nonzero value of `C(i,j)` says the product
of idempotents `(i,0),(j,0)` is not idempotent. Thus squaring fails to be a
homomorphism. It follows that the magma is **noncommutative** (commutative
E667 magmas have homomorphic squaring) and **nonmedial** (the medial law
always makes squaring a homomorphism). In particular it cannot be affine over any abelian group, even after an
arbitrary relabelling: `AffineStructure.medial` proves that the E667 law
itself forces every affine abelian-group operation to be medial, and
`no_affine_representation` makes this obstruction independent of coordinates.

This reconstructs the earlier saved ten-point counterexample, rather than
merely supplying an unrelated example. Use

```
v=[0,1,1,0,0]
```

and send the lexicographically listed pairs `(0,0),(0,1),...,(4,1)` to its
old labels

```
[0,9,1,8,4,7,5,2,3,6].
```

The checker verifies that this relabelling reproduces every saved table
entry. The model's previously mysterious failures of square-homomorphism
and closure of idempotents now follow directly from the formula.

### All binary extensions of this five-point quotient

There is also a small complete classification of this extension class.
Every Latin two-point block is `a+b+C(i,j)`. The square in its i-th fiber
is `(i,C(i,i))`; label that unique idempotent by zero. This uses up the
fiber relabelling freedom and makes all `C(i,i)=0`.

Substitute the five-point table into the displayed cocycle equation. The
25 scalar variables, with the five zero-diagonal conditions, have constraint
rank 21 over F₂, hence a four-dimensional solution space. The script
`spectrum_667_nonlinear_constructions.py` reproduces this exact elementary
linear-algebra calculation. The explicit functions `v`, modulo adding a
constant, already give 16 distinct solutions (the first row recovers `v`
modulo a constant). Thus they give **all** normalized binary extensions.
This completeness statement is now formalized in
`Equation667BinaryFiveCompleteness.lean` by short linear combinations of the
cocycle equations; no external linear-algebra result is trusted. The generator
`scripts/spectrum_667_binary_classification.py` reproduces those ordinary Lean
proofs.

Every isomorphism preserves the square fibers and their unique idempotents,
so it is determined by its permutation on the quotient. That permutation
must be an automorphism of the five-point mean operation. These are exactly
`i ↦ ai+b`, with `a≠0`: the images of two distinct points determine the
whole five-point table. Functions `v` are therefore identified under affine
permutation of the five arguments and under complementation. There are
exactly **three isomorphism classes** in this extension class:

| Representative v | Description | Automorphism group order |
|---|---|---:|
| constant | the product of the five-point mean algebra with C₂ | 20 |
| one nonzero entry | noncommutative, nonmedial | 4 |
| two nonzero entries | noncommutative, nonmedial; includes the saved counterexample | 2 |

The affine group is two-transitive, so it is transitive on one-point and
two-point supports; complementation reduces every support to size at most
two. This also shows these three classes are distinct. The three-class classification is now proved in
`Equation667BinaryFiveClassification.lean`, including for an arbitrary
10-element carrier equipped with a surjective homomorphism to the five-point
mean algebra. Distinctness is proved under **arbitrary** magma isomorphisms:
the three representatives have respectively 100, 36, and 68 commuting ordered
pairs. The automorphism-group orders in the table above are also proved in
`Equation667BinaryFiveAutomorphisms.lean`. Every automorphism is determined
by its action on the five idempotents, reducing the count to permutations
of five points.
This is not a classification of all ten-point E667 magmas.

## 3. Independent binary choices on every five-point block

Take any commutative idempotent E667 algebra P, equivalently a five-point
design algebra from the preceding note. Choose F₅ coordinates and an
arbitrary binary function `v_B` on **each** five-point block B. On P×F₂,
use the construction of section 2 whenever the two base points are in B.
Within a single fiber use `(i,a)*(i,b)=(i,a+b)`.

This is well-defined: two different blocks intersect in at most one base
point, and their doubled algebras agree on its two-element fiber. Every
E667 instance involving two different base points stays inside that block's
ten-element algebra. An instance from one fiber stays in its C₂ algebra.
Thus the result satisfies E667, with `D(i,a)=(i,0)` and exactly |P|
idempotents. The base projection is a homomorphism even when D is not.

This is gluing along shared **two-element submagmas**, rather than relying
on global idempotency of the constructed model. Each block contributes four
independent binary parameters: with b blocks there are `2^(4b)` distinct
operations on the fixed labelled carrier after the fibers are normalized.
This count is of labelled operations, not isomorphism classes. Any nonconstant
block choice makes the result noncommutative and nonmedial. In particular,
noncommutativity can be introduced on just one ten-element block while the
other blocks retain commutative multiplication.

**Proved in Lean:** `Equation667BinaryDesign.lean` supplies the construction,
square map, idempotent count, and the noncommutativity/nonmediality obstruction.
`Equation667BinaryDesignClassification.lean` proves more: these are **all**
normalized binary extensions of the design algebra. Setting `v_B(0)=0` gives
unique parameters, and `normalized_count` proves the exact count `2^(4b)`.
There is just one commutative normalized extension: all block functions zero.
The design itself may be nonmedial, even in that zero-data case.
`Equation667BinaryDesignCount.lean` also proves the count before normalization:
with n points and b blocks there are exactly `2^(n+4b)` binary cocycles,
including the independent choice of origin in each fiber.

An explicit instance uses the nonabelian group `C₇ ⋊ C₃`, with coordinates
`(a,b)` and multiplication

```
(a,b)(c,d)=(a+2^b c mod 7, b+d mod 3).
```

Encode `(a,b)` by `a+7b`. Its left translates of

```
B=[0,1,3,20,13]
```

form a 2-(21,5,1) design. Give this base block the F₅ labels `[0,1,3,4,2]`
and develop its mean operation by left translation. The resulting
21-element algebra is commutative and idempotent but nonmedial. Its profile
is saved in the data; the checker verifies all 21 blocks, all 210 unordered
pairs, and the resulting operation.

Now make the binary choice `[1,0,0,0,0]` on B and zero choices on the other
20 blocks. This gives a checked **42-element noncommutative, nonmedial E667
model with exactly 21 idempotents**, described by the profile and one small
block modification. It is a structural example, not a new positive spectrum
order; 42 was already known.

The 21-point group/profile model and the existence of a nonlinear 42-point
double cover are now proved in `Equation667Frobenius21.lean`. Its group
axioms use symbolic arithmetic plus the nine cases of the C₃ action.
The E667 proof uses only 21 profile checks. The double-cover proof uses the
general design theorem and retains this specific 21-point algebra as quotient;
it does not rely on evaluating all 42² instances of the E667 law. The exact
counts for this quotient are now formalized too: `2^84` normalized binary
extensions and `2^105` before choosing the origins of the fibers.

## 4. Nonabelian multiplication inside a directed-triangle construction

Nonabelian groups also enter through Latin squares and Mendelsohn systems.
Here is an explicit construction using S₃.

Take three disjoint copies `G₀,G₁,G₂` of S₃ and a common point ∞. For every
`a,b∈G`, put in the directed triangles

```
(a₀, b₁, (ab)₂),       (b₁, a₀, (ba)₂),
```

where a directed triangle `(x,y,z)` means `x·y=z`, `y·z=x`, `z·x=y`.
Every ordered pair from different copies occurs exactly once: completing
either sort of triangle just uses left or right division in G. The two
orientations use multiplication and opposite multiplication respectively.
For noncommuting a,b, `a₀·b₁` and `b₁·a₀` are different, exposing the
nonabelian multiplication directly.

Each set `G_i ∪ {∞}` has seven points. Fill it with the affine Mendelsohn
operation `x·y=5x+3y mod 7`, using the common point as zero. The three
fillings agree at ∞ and cover exactly the remaining ordered pairs. We now
have an idempotent semisymmetric quasigroup on **19 points**.

Adjoin a new identity e, change every old square to e, and retain products
of distinct old points. This is a semisymmetric loop on **20 points**:
`y·(x·y)=x`, every square is e, and e is a two-sided identity. Therefore

```
y·(x·((x·x)·y)) = y·(x·y) = x,
```

so it satisfies E667. It is noncommutative, has exactly one idempotent, and
is nonmedial: a medial loop is commutative, by substituting its identity
into the medial law.

The group is encoded between the colored copies; it is not a group
submagma of the resulting E667 operation. More generally the cross-copy
step can use any two Latin squares of the same order, while suitable
Mendelsohn fillings handle pairs within each copy and the shared point.
This provides substantial freedom beyond affine models. The two-independent-
Latin-square generalization is now formalized in
`Equation667LatinTriangles.lean`; neither Latin square needs to be
associative or idempotent. Both input squares can be recovered from the
labelled result. The 20-point
example and all its original-law instances are independently checked by
the accompanying script; the general construction is now formalized in
`Equation667GroupMendelsohn.lean`. It works for any group G with a Mendelsohn
filling on G plus one point. The cross-copy proof uses group cancellation;
it does not enumerate group elements. The S₃ instance has 20 points by a
cardinality calculation, and its noncommutativity follows from two
noncommuting transpositions. Lean chooses an arbitrary labelling for the
seven-point affine filling, so no claim is made that its raw labels equal
the JSON table's labels.

## 5. Why the most direct nonabelian affine ansatz fails

There is a clean obstruction to simply replacing an abelian group by a
nonabelian one. Suppose a group G is given automorphisms α,β and an element
c, and define

```
x*y=α(x)β(y)c.
```

If this satisfies E667, G must be abelian. This needs no finiteness.
Indeed substitute x=1 in E667. Expanding the automorphisms gives

```
α(y) K β³(y) L = 1,
K=β²(α(c)),    L=β²(c)β(c)c.
```

Putting y=1 gives `L=K⁻¹`, hence

```
α(y)=K β³(y)⁻¹ K⁻¹.
```

The left side is an automorphism. The right side is an anti-automorphism.
Their equality forces all elements to commute. Thus arbitrary noncommuting
automorphism coefficients do not enlarge this affine family. This argument
does not cover arbitrary permutation isotopes of a nonabelian group, nor
the directed-triangle construction above.

This obstruction is proved in Lean as
`GroupConstructions.affine_forces_commutative`.

## 6. Regular group actions reduce the table to one profile

A different group-based ansatz is substantially more general. Let G act
regularly by automorphisms on the carrier. After identifying the carrier
with G, every such operation is uniquely

```
x*y = x h(x⁻¹y)
```

for a function `h:G→G`. It is Latin exactly when both `h(t)` and
`t⁻¹h(t)` are permutations. Put `d=h(1)`. Its square map is `D(x)=xd`,
so such a model is either globally idempotent (`d=1`) or idempotent-free.
Substitution shows that E667 is precisely the |G|-equation profile condition

```
h(t⁻¹ h(d h(d⁻¹t))) = t⁻¹.
```

This works over nonabelian groups too. It turns a multiplication-table
search into a search over one permutation and its associated complete
mapping. `scripts/spectrum_667_regular.py` implements this formulation;
every returned model is checked independently using the original E667 law.
The representation, square formula, exact E667 profile criterion, and the
necessary permutation conditions are now proved in
`Equation667GroupConstructions.lean`. Formalizing the criterion does not
formalize the negative CP-SAT search outcomes.

The 27 bounded probes in `667_regular_action_searches.json` give:

* **All five groups of order 12** were exhausted: C₁₂, C₆×C₂, the dihedral
  group of order 12, A₄, and the dicyclic group of order 12. No profile exists.
* **C₁₅**, the only group of order 15, was exhausted. No profile exists.
  Thus regular automorphism-group constructions cannot supply either missing
  order. This does not exclude arbitrary or even all transitive models.
* The idempotent-free profile classes over C₉, C₃², C₁₁, C₁₃, D₈, Q₈,
  `C₇⋊C₃`, `C₅⋊C₄`, Q₈×C₂, D₁₆, and C₄² were exhausted.
* Idempotent profiles over `C₅⋊C₄` and C₅×C₂² were exhausted. This leaves
  the broader order-20 idempotent question unresolved.
* Idempotent-free searches over the Heisenberg group of order 27 and C₃³,
  and unrestricted searches over S₄ and Q₈×C₃, timed out at 30 seconds.
* Positive controls recovered the familiar five- and eight-point
  idempotent-free affine models and the seven-point idempotent affine model.
  The nonabelian regular action at order 21 yielded the nonmedial five-design
  algebra used in section 3.

These are external solver outcomes for explicitly restricted classes.
They are not formal exclusions of E667 orders. Exact groups, limits,
statuses, profiles, tables, solver version, and source hash are saved.
All runs from this batch have finished.

## Reproduction and next directions

```
python3 scripts/spectrum_667_nonlinear_constructions.py
python3 scripts/spectrum_667_regular.py A4 --seconds 15
python3 scripts/spectrum_667_regular.py C15 --seconds 30
python3 scripts/spectrum_667_regular.py F21 --diagonal idempotent --seconds 60
lake build equational_theories.Spectrum
```

The useful new directions are extension theory with explicitly controlled
square fibers, local modifications of design blocks, and automorphism twists
of nonmedial idempotent algebras. The negative regular-action results explain
why imposing translation symmetry at 12 and 15 is too restrictive. The
binary family also separates two notions that should remain distinct:
square fibers can form a congruence even though squaring is not itself a
homomorphism.
