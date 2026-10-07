# The unrestricted E63 term-structural family

Date: 2026-10-06.

E63, E73, E118, E125, and E1692 are equivalent for finite term-structural
interpretation. Their five unrestricted classes still have ten possible
equivalence pairs. This pass does **not** resolve any of those ten pairs. It does settle several
other definability questions, including all remaining outgoing term-structural
cells for E125 (both finite and unrestricted).

The known unrestricted arrows include E125 → E63 → E118 and
E125 → E1692 → E73. **All five laws have Mal'tsev terms on arbitrary
carriers.** They also have permuting congruences, congruences determined by
any one class, and equinumerous congruence classes. The initially proposed
Mal'tsev obstruction therefore cannot separate this family.

The initial structural proofs are in
[E63Family.lean](../equational_theories/Definability/E63Family.lean),
[E63Malcev.lean](../equational_theories/Definability/E63Malcev.lean), and
[E125Homogeneous.lean](../equational_theories/Definability/E125Homogeneous.lean),
with transitive axiom checks and no `sorry` or native decision procedure.

## Newly settled definability cells

The arrows below name the source first. All are complete Lean proofs, with
transitive checks excluding `sorryAx` and native decision procedures.

| Source → target | Result | Main proof |
|---|---|---|
| E118 → E3 | FO-structural, arbitrary carriers | `Equation3_structuralFrom_Equation118_diagonalCycle` |
| E1289 → E3 | FO-structural, arbitrary carriers | `Equation3_structuralFrom_Equation1289_diagonalCycle` |
| E464 → E1289 | Term-structural, arbitrary carriers | `Equation1289_termStructuralFrom_Equation464_iteratedDivision` |
| E125 → E3954 (and E3548 by duality) | FO-structural, arbitrary carriers | `Equation3954_structuralFrom_Equation125_rightDivision` |
| E125 → E3548 (and E3954 by duality) | **Not** term-structural on arbitrary carriers | `Equation3548_not_termStructuralFrom_Equation125_convex` |
| E125 → E3659 | **Not** term-structural, already on seven elements | `Equation3659_not_termStructuralFromFin_Equation125_translation` |

The corresponding files are
[DiagonalCycle.lean](../equational_theories/Definability/DiagonalCycle.lean),
[IteratedDivisionRecovery.lean](../equational_theories/Definability/IteratedDivisionRecovery.lean),
[E125DivisionFO.lean](../equational_theories/Definability/E125DivisionFO.lean),
[E125ConvexSeparation.lean](../equational_theories/Definability/E125ConvexSeparation.lean), and
[E125TranslationSeparation.lean](../equational_theories/Definability/E125TranslationSeparation.lean).

Closure adds **14 unrestricted term-structural positives, 210 unrestricted
FO-structural positives, 34 unrestricted term-structural negatives, and 14
finite term-structural negatives**. E63 inherits the new FO-structural arrow to
E3 through E118; E464 inherits one through E1289. There are no newly merged
term-structural classes. E464 → E1289 changes one previously two-way-open
class pair to a pair with one proved direction.

For E125 → E3548, one-way term-definability remains proved, as does finite
term-structural definability. The new negative concerns recovering the source
operation by a term on arbitrary carriers. FO formulas can recover it.
Consequently E125 has **no unknown outgoing term-structural cells** in either
variant, although incoming arrows and other modes remain open.

More precisely, among the 4,694 catalogue laws, the unrestricted row has
35 positive and 4,659 negative entries. The finite row has 37 positive and
4,657 negative entries. **E3548 and E3954 are the only targets for which
the two rows differ.** Thus the finite-versus-infinite distinction for
term-structural constructions starting from E125 is now completely classified.

The [machine-readable pass report](../data/definability_e63_family_pass.json)
records the six direct generators, closure gains, and source fingerprint.
The full `Definability` build passed (17,208 jobs), including transitive
axiom guards on the new results. The subsequent audit rebuilt all ten
relation boards from Lean declarations, checked their closure against the
full-matrix reference, and verified every reported gain. The remaining
equivalence-pair inventory was regenerated from the same source snapshot.

### Recovering an erased diagonal by a finite cycle

Let `R_a(x)=x*a` be injective and suppose `R_a^k(a)=a`, with a fixed `k>0`.
Replace the diagonal by `a □ a=a`, preserving every off-diagonal entry.
The original square `a*a` is the unique `z` satisfying

```
(R□_a)^(k-1)(z)=a,     and     ∀u≠a, u □ a ≠ z.
```

It is the missing value at the beginning of the broken column cycle.
The bounded path condition excludes points outside the column's image;
whole-column surjectivity is unnecessary. Lean proves this for every `k`.
E118 supplies an injective column and a three-cycle; E1289 supplies a
four-cycle. In both cases the cycle follows from just two instances of the
source equation.

### The E464 inverse term

For a source satisfying `y*L_x^k(y)=x`, set `x □ y=L_x^k(y)`. Writing
`B_y(x)=x □ y`, we have `L_y B_y=id`, so `L_y^k B_y^k=id` and
`L_y^k B_y^(k-1)=L_y`. The first identity proves the companion law; the
second recovers the original operation. For E464, `k=3` and explicitly

```
x □ y = x*(x*(x*y)),
x*y   = x □ ((y □ x) □ x).
```

This upgrades an existing one-way term interpretation, using only
one-sided cancellation. It does not use finiteness.

### Why E3548 permits FO recovery but prevents term recovery

The E125 right division is `d(x,y)=y*(y*x)`. Its graph is the atomic
formula `z*y=x`; the same formula in `d` recovers the original operation.
The E125 rotation proves that `d` satisfies E3954, and duality gives E3548.

For the negative, choose a real `a` with `1<a<2` and `a(1-a)^2=1`, whose
existence follows by the intermediate value theorem. The operation
`x*y=a*x+(1-a)*y` satisfies E125. Every binary term is again affine, with
coefficient sum one. If `x □ y=b*x+(1-b)*y` satisfies E3548, then
`b=(1-b)(b²+1-b)`. Since `b²+1-b>0`, necessarily `0≤b≤1`. Hence `□`
and every term formed from it preserve `[0,1]`. The source sends `(1,0)`
to `a>1`, so no recovery term exists. This is a short ordered-field
argument, with no search certificate.

### The seven-element E3659 obstruction

On `ZMod 7`, let `x*y=4x+4y+1`. This satisfies E125 and commutes with
all translations. Every interpreting term inherits those translations,
so the square of the interpreted operation has the form `x↦c+x`.
E3659 says this square is idempotent, forcing `c=0`. Thus the interpreted
operation and all its terms are idempotent. They cannot recover the
source, for which `0*0=1`. The small source law is checked by ordinary
kernel `decide`; the obstruction to **all** interpreting terms is proved
symbolically.

## Left and right division behave differently

For E125, all six parastrophes (the operation, its opposite, both divisions,
and their opposites) are FO interdefinable. The term-recovery picture is
asymmetric. Left division is `x \ y=(x*y)*x`, and from the operation
`x □ y=(x*y)*x` one recovers `x*y=y □ (y □ x)` immediately by E125.
The operation and its opposite, and left division and its opposite, thus
admit term recovery on arbitrary carriers. The existing positive wrappers
are in [PositiveStructural.lean](../equational_theories/Definability/PositiveStructural.lean).

Right division is `x/y=y*(y*x)`. It and its opposite permit FO recovery,
but **no recovery term exists even for the particular real model above**,
by the interval obstruction. On finite carriers they permit term recovery too, using a finite
translation period. This is a complete distinction between these natural
constructions, although it does not classify every possible companion.

## What finiteness buys

Write `L_y(x) = y*x`, `R_y(x) = x*y`, and `P_y(x) = x*(x*y)`.
Composition is read from right to left.

| Law | Translation identity | Consequence without finiteness |
|---|---|---|
| E63 | `L_y P_y = id` | `L_y` is surjective; `P_y` is injective |
| E1692 | `P_y L_y = id` | `L_y` is injective; `P_y` is surjective |
| E73 | `L_y² R_y = id` | `L_y` is surjective; `R_y` is injective |
| E118 | `L_y R_y² = id` | `L_y` is surjective; `R_y` is injective |
| E125 | `L_y R_y L_y = id` | Both translations are bijective |

For E125, the sandwich identity makes `L_y` both injective and surjective.
Consequently `R_y = L_y⁻²`. In particular E125 implies E73 with the same
operation on arbitrary carriers.

Three exact conditional converses are now proved in Lean:

* In an E63 magma, E1692 holds if and only if every left translation is
  injective (`equation1692_iff_left_injective`).
* In an E73 magma, E125 holds if and only if every left translation is
  injective (`equation125_iff_left_injective`).
* In an E118 magma, E222, the dual of E125, holds if and only if every right
  translation is surjective (`equation222_iff_right_surjective`).

These are statements about the original operation. A failure of one condition
does **not** rule out a different operation given by some interpreting term.
That remaining quantifier is the hard part of a term-structural separation.

## Affine models cannot exploit the missing inverse

Let `x*y = A(x) + B(y) + c` on any abelian group. Neither finiteness nor
commutation of the additive endomorphisms `A,B` is assumed. All five laws
force **commuting, invertible** `A,B`, and therefore bijective translations.
This is formalized by `Affine.commuting_units` and
`Affine.translations_bijective`.

Expanding the law at `(x,0)`, `(0,y)`, and `(0,0)` separates its linear
coefficients from its constant. In the possibly noncommutative endomorphism
ring the resulting identities are:

| Law | Coefficient of `x` | Coefficient of `y` |
|---|---|---|
| E63 | `BA + B²A = 1` | `A + B³ = 0` |
| E73 | `B²A = 1` | `A + BA + B³ = 0` |
| E118 | `BA² = 1` | `A + BAB + B² = 0` |
| E125 | `BAB = 1` | `A + BA² + B² = 0` |
| E1692 | `(A+BA)B = 1` | `(A+BA)A + B² = 0` |

For E63, substitute `A = -B³`: then `B⁵+B⁴+1 = 0`, giving an explicit
inverse for `B`. For E73, multiplying the second identity by `B` gives
`BA = -1-B⁴`, and then `A = 1+B⁴-B³`; commutation follows, as does the
inverse `B⁻¹ = -1-B⁴`. For E118, multiply the second identity by `A²`
on the right to get `A³+BA+B = 0`; one more multiplication gives
`BA = -A⁴-1`, hence `B = A⁴-A³+1`. For E125, `BAB=1` supplies a left
and a right inverse of `B`; their equality forces commutation. Finally,
for E1692 put `D=A+BA`. The pair `(B²,D)` satisfies the E73 coefficient
identities, so `D` is invertible. Since `DB=1`, we obtain `BD=1` and
`A=-B³`.

Thus moving to infinite-dimensional modules or to noncommuting matrices
does not produce the one-sided inverse behavior needed here. This conclusion
concerns affine operations over **abelian** groups; it does not classify
operations on nonabelian groups or general nonlinear constructions.

## Mal'tsev terms: the weaker laws have them too

E125 has term divisions

```
y \ z = (y*z)*y
x / y = y*(y*x).
```

They give the Mal'tsev term

```
p(x,y,z) = (x / (y\y)) * (y\z),
p(x,y,y) = x,    p(y,y,z) = z.
```

Both identities are proved in Lean (`malcev125_left`, `malcev125_right`).
However, the weaker laws need only *one-sided* divisions to obtain a
Mal'tsev term. Suppose binary terms `d,r` satisfy

```
x * d(x,y) = y,       r(x*y,y) = x.
```

Put `e(x)=d(x,x)` and

```
p(x,y,z) = r(z * d(y,x), e(x)).
```

Then `p(x,y,y)=r(x,e(x))=r(x*e(x),e(x))=x`, while
`p(y,y,z)=r(z*e(y),e(y))=z`. No reverse division identity is used.

For E73 take `d(x,y)=x*(y*x)` and `r(x,y)=y*(y*x)`. For E118 take
`d(x,y)=(y*x)*x` and `r(x,y)=y*(x*y)`. This gives explicit nine-operation
Mal'tsev terms:

```
E73:  s * (s * (z * (y * (x*y)))),   s = x*(x*x).
E118: s * ((z * ((x*y)*y)) * s),     s = (x*x)*x.
```

For E63, substitute `x □ y = x*(x*y)` into the E118 term. For E1692,
substitute `x □ y = y*(y*x)` into the E73 term. Lean checks both
companion laws and all eight Mal'tsev identities. Vampire's proofs that
reflexive compatible relations are symmetric suggested this construction;
the final Lean proofs use the short general argument above, not ATP replay.

## Further shared structure

All of the following now have Lean proofs, including the transfers to
E63 and E1692 through their explicit companion operations:

* Every reflexive relation preserved by multiplication is an equivalence
  relation (`family_compatible_equivalence`). The Mal'tsev term directly
  supplies symmetry and transitivity.
* Congruences permute (`SplitPresentation.congruences_permute`). If
  `x α y β z`, the intermediate point `p(x,y,z)` gives `x β p(x,y,z) α z`.
* Inclusion of a single pair of congruence classes implies inclusion of
  the congruences (`congruence_le_of_class_le`). To compare `x α y`,
  multiply both on the right by `c=d(x,a)`, placing `x*c=a` in the
  designated class. Transfer class membership and apply `r(-,c)` to
  recover `x β y`. In particular, one class determines a congruence.
* All classes of any congruence are equinumerous
  (`family_classes_equinumerous`). The map `x ↦ x*d(a,b)` embeds the
  class of `a` into the class of `b`, with left inverse `r(-,d(a,b))`.
  Reverse the roles of `a,b` and apply Schröder–Bernstein. This works
  for infinite carriers too.

Consequently neither asymmetric compatible relations, nonpermuting
congruences, nor unequal congruence-class sizes can supply the desired
separation. These are stronger conclusions than merely finding individual
Mal'tsev terms.

## A stronger necessary property of E125 interpretations

E125 supplies a *term-defined bijection with a term-defined inverse*
carrying any specified point `a` to any specified point `b`. Set
`c=d(a,b)`. The maps are

```
T(x) = x*c,       U(x) = c*(c*x).
```

They satisfy `T(a)=b`, `U(T(x))=x`, and `T(U(x))=x`. The last identity
uses the extra E125 rotation and is formalized in `transport_retract_125`;
`transport_bijective_125` packages the result.

The split-division construction for the weaker laws directly provides
`T(a)=b` and `U∘T=id`. Schröder–Bernstein provides set-theoretic
bijections of congruence classes, but does not provide inverse terms.
Finding an infinite source in which no mutually inverse unary polynomial
terms carry some `a` to some `b` would refute even one-way term
definability into E125: an E125 interpretation would supply those terms.
Parameters `a,b` are allowed in this obstruction. A failure of the
particular displayed transport is insufficient; other terms must also
be ruled out. This remains a research target, not a separation theorem.

## Reduction for the existing free-group models

The E73 greedy model is invariant under right multiplication in its
underlying free group. Any term interpretation has the same invariance.
An operation with that invariance has the form

```
x*y = f(y*x⁻¹)*x.
```

Its E125 law is equivalent to the single-variable functional identity

```
f(f((f(x))⁻¹) * f(x)) = x.
```

`Homogeneous.equation125_iff` proves this equivalence. E125 also forces
both `f` and `x ↦ f(x)*x⁻¹` to be bijective, and `f(f(f(1)))=1`.
For any operation of this form, every unary term is left multiplication
by its value at `1`, and hence bijective (`unary_term_bijective`).
This gives a concrete setting for stronger unary-term invariants; it
does not assert that every solution `f` is term-definable in the source.

A bounded SAT investigation tested whether `f(1)` can fail to commute
with `f(f(1))`. It ruled out that combination on D8, Q8, A4, D12, D16,
D20, S4, D28, D32, the groups C7⋊C3 and C5⋊C4, and the Heisenberg
group over F3. These are **finite ATP checks, not Lean theorems**. Two larger
semidirect-product searches reached their conflict budgets. The homogeneous
commutation conjecture is now **refuted in Lean** by the Heisenberg group
over F₇ below. The earlier bounded searches simply did not reach that group. The stronger claim that all E125 models with bijective
unary terms have commuting square and cube maps is false: the 49-element
construction below is a Lean-verified counterexample. A separate rigidity
theorem about the E73 source is also formalized below.

The [probe results](../data/e125_homogeneous_probe.json) retain solver status
and conflict budgets. The bounded search can be repeated with
`python3 scripts/e125_homogeneous_probe.py --groups D8 Q8 A4 --conflicts 2000000 --output results.json`.

## A rejected shortcut, with a small witness

E125 does not force its square and cube maps to commute, or either map to
be an endomorphism. Mace4 found the following nine-element E125 table in a
bounded search; an independent Python check verified all 81 law instances.
This table is research evidence, not an additional Lean catalogue entry.

```
1 2 0 5 7 6 3 8 4
2 0 1 6 8 3 5 4 7
0 1 3 4 2 5 6 7 8
5 6 4 2 3 7 8 0 1
7 8 2 3 4 0 1 5 6
6 3 5 7 0 8 4 1 2
3 5 6 8 1 4 7 2 0
8 4 7 0 5 1 2 6 3
4 7 8 1 6 2 0 3 5
```

With zero-based labels, let `s(x)=x*x` and `t(x)=x*(x*x)`. Then
`t(s(0))=2` but `s(t(0))=3`. Also `s(0*1)=3` but `s(0)*s(1)=2`,
and `t(0*0)=2` but `t(0)*t(0)=3`. The table is commutative, so right
cubing fails these same tests. ATP timeouts from the preceding probes
were not interpreted as negative mathematical results.


## Unary endomorphism rigidity in the E73 free-group source

[FreeGroupUnaryRecovery.lean](../equational_theories/Definability/FreeGroupUnaryRecovery.lean)
proves that the seeded E73 model has no nonidentity endomorphism given by a
unary term. Every unary term is left multiplication by a group element `c`.
If that translation preserves multiplication, evaluating it on the first
two seed values forces `c` to commute with two distinct free generators.
Their common centralizer is trivial. The group lemma uses reduced-word
heads, rather than a classification of centralizers.

This restriction survives **FO interdefinability**: right group translations
remain automorphisms of any FO companion; its unary terms are consequently
left translations and bijective. A unary term endomorphism of the companion
is therefore an automorphism, and FO recovery makes it an automorphism of
the source as well. It must be the identity. The statement and its concrete
E73 instantiation are proved in Lean.

This is not yet a separation inside the five-law family. In particular,
E125 does not generally make its square or cube map an endomorphism. The
nine-element table above even has bijective squaring, so that additional
hypothesis does not repair the false square-endomorphism claim. The 49-element construction below refutes two stronger proposed identities
even under bijectivity of **every** unary term.

## Why the same diagonal-erasure method stalls for E73

[E73DiagonalAmbiguity.lean](../equational_theories/Definability/E73DiagonalAmbiguity.lean)
constructs two infinite E73 operations that agree at every off-diagonal
entry and disagree at **every** diagonal entry. Their erased operations
are identical, so no single restoration map from erased tables can work
on all E73 models. This is a complete Lean construction.

Use distinct free generators `a,c,b,d,e,u,v` and the ten-pair seed

```
f(1)=a, f(a)=c, f(c)=1, f(b)=d, f(d)=1,
f(c⁻¹)=e, f(e)=c⁻¹,
f(a⁻¹)=u, f(ua)=v, f(v)=a.
```

The existing E73 extension theorem supplies a total `f`. Its functional
identity forces `f` to have no fixed point and forces
`f(f(x)x⁻¹)≠1`: a violation of either property would contradict one of
the displayed seed values. Hence replacing only `f(1)=a` by `f(1)=b`
preserves the identity; the new diagonal follows the second three-cycle
`1,b,d,1`. In `x*y=f(yx⁻¹)x`, this changes precisely the diagonal.

This rules out a **uniform diagonal-erasure restoration**. It does not
refute E73 → E3 FO-structurally: that definition permits another companion
and permits the recovery formula to depend on the source model.

## A symbolic 49-element counterexample to stronger unary invariants

[E125UnaryCountermodel.lean](../equational_theories/Definability/E125UnaryCountermodel.lean)
works on `F₇ × F₇`. Let `q(x,y)=4x+4y+1` and put

```
(x,a) * (y,b) = (q(x,y), 4a+4b+κ(x,y)),
κ(0,2)=κ(2,0)=5,   κ(2,2)=1,
κ(x,y)=0 otherwise.
```

E125 reduces to the linear cocycle condition

```
2κ(y,x) + 4κ(q(y,x),y) + κ(y,q(q(y,x),y)) = 0.
```

A nullspace search over `F₇` found this sparse solution. Lean checks its
49 base instances by ordinary `decide`, then proves the full law by symbolic
linear algebra in the second coordinate. No 49-by-49 multiplication table
or search certificate is stored.

Induction on terms gives the exact unary form `(x,a) ↦ (x+c,a+d(x))`;
therefore **all unary terms are bijective**, with explicit triangular
inverses. Nevertheless, if `S(z)=z*z` and `C(z)=z*(z*z)`, then
`S(C(1,0)) ≠ C(S(1,0))`. Also `S²` fails to preserve the product of
`(0,0)` and `(1,0)`. These are complete Lean counterexamples, not failed
ATP attempts. In particular, bijectivity of unary terms does not repair
these proposed E125 endomorphism or commutation invariants. This 49-element construction is not homogeneous under a regular group action
on its carrier. A related, smaller-degree cocycle does produce a homogeneous
counterexample, as follows.

## A homogeneous counterexample on the 343-element Heisenberg group

[E125Heisenberg.lean](../equational_theories/Definability/E125Heisenberg.lean)
refutes commutation even with a regular group of automorphisms. Work over `F₇`
and give triples the Heisenberg group multiplication

```
(c,d,e) · (r,s,t) = (c+r, d+s, e+t+dr).
```

Put

```
u(c) = 4c+c²+6c³+6c⁴+5c⁵,
v(c) = 5c²+3c⁴+c⁶,
f(c,d,e) = (4c+1, 4d+v(c), 4e+u(c)).
```

Then `f(f((f(x))⁻¹)·f(x))=x`. The first coordinate is immediate modulo
seven; the other two reduce to seven scalar checks each, with arbitrary
`d,e` handled symbolically. Thus `x*y=f(y·x⁻¹)·x` is a complete Lean E125
model. Every unary term is a bijection, and every right group translation
is an automorphism. However `f(1)=(1,0,0)` and `f(f(1))=(5,2,1)` do not
commute: their products have third coordinates `1` and `3`.

The search found this by writing a cocycle as
`κ(x,y)=u(y-x)+x·v(y-x)` and solving its linear equations. Triangular
permutations `(x,a)↦(x+c,a+dx+e)` form precisely this Heisenberg group;
pointwise multiplication induces the displayed construction. The checked
Lean proof uses the group formula directly and stores no large table.
This eliminates the general homogeneous commutation obstruction. It does
not decide whether a suitable E125 companion can be term-defined in the
specific infinite E73 source.

The two cocycle searches and independent finite checks are reproducible with
`python3 scripts/e125_cocycle_probe.py`; their small output is saved in
[data/e125_cocycle_probe.json](../data/e125_cocycle_probe.json).

### Homogenizing a finite model whose unary terms are permutations

There is a general construction behind these examples, formalized in
[UnaryHomogenization.lean](../equational_theories/Definability/UnaryHomogenization.lean).
Let `A` be any finite magma in which every unary term operation is a
permutation. Its unary term operations form a group `H` under composition:
substitution gives closure, the variable gives the identity, and finiteness
expresses the inverse of any permutation as a positive composition power.
Define an operation on `H` pointwise, by `(p*q)(a)=p(a)*q(a)`. It belongs
to `H` because joining two unary terms gives another unary term. Every
equational law of `A` holds pointwise in this new magma. Right composition
by any `h∈H` is an automorphism, since

```
((p∘h)*(q∘h))(a) = (p*q)(h(a)).
```

Thus this is a homogeneous model of every law of `A`, with the regular
right action of `H`. Lean proves the group construction, law preservation
(`satisfies`), equivariance, and the evaluation homomorphisms. Evaluation at a
point has image equal to the one-generated subalgebra at that point.
Homogeneous models are therefore not confined to affine constructions on
abelian groups.

For the 49-element example above, `H` is exactly the full triangular group

```
(x,a) ↦ (x+c,a+d(x)),       c∈F₇, d:F₇→F₇,
```

of order `7⁸=5,764,801` (the wreath product `C₇ ≀ C₇`). Here is a short
way to establish the order without enumerating that many permutations.
This specific group-order calculation is a pen-and-paper argument with an
independent seven-coordinate check in the probe script, not a Lean theorem.
Write `δ₂(x)=1` for `x=2` and zero otherwise. Squaring and cubing have
coordinates `S=(1,δ₂)` and `C=(5,4δ₂)`. The element `C∘S⁻⁵` has zero
base shift and fibre vector `(3,0,0,6,6,6,6)`. Conjugating by `S` cyclically
shifts this vector. Its coordinate sum is `6≠0` in `F₇`, so its cyclic
shifts span all seven fibre coordinates: in
`F₇[X]/(X⁷-1)=F₇[X]/((X-1)⁷)`, an element is a unit exactly when its
value at `1` is nonzero. We therefore obtain every fibre translation,
and `S` supplies the base shift. Conversely, the triangular form of all
unary terms was proved in Lean above. This identifies the entire unary
term group using only seven coordinates.

The induced E125 operation on this group is also explicit:
`(c,d)*(e,f)=(4c+4e+1, x↦4d(x)+4f(x)+κ(x+c,x+e))`.
No large multiplication table is needed. The smaller 343-element homogeneous
counterexample remains the Lean witness; this larger construction explains
the available algebraic flexibility and does not settle a new class arrow.

## Short E8 companions: three exact obstructions, one remaining candidate

[E73ShortCompanions.lean](../equational_theories/Definability/E73ShortCompanions.lean)
proves that each of the following terms defines an E8 operation in every E73
magma, writing `L_x(z)=x*z`:

| Companion `x □ y` | Recovery status for this specific construction |
|---|---|
| `L_x³(y*(x*y))` | No recovery term on an eight-element E125 source: the companion is right projection |
| `L_x³(y*(y*x))` | No recovery term on a five-element E125 source: the companion is right projection |
| `y*((L_x³(y))*x)` | Undetermined on E73; agrees with left division and recovers the operation on E125 |
| `(L_x³(y))*(y*x)` | No recovery term on that five-element source: the companion is left projection |

The five-element source is `x*y=4x+2y` on `F₅`. The eight-element source
has `x*y=A(x)+(I-A)(y)` on `F₂³`, where
`A(x₀,x₁,x₂)=(x₂,x₀+x₂,x₁)` satisfies `A³+A+I=0`.
Lean checks both small source laws and the projection identities. The
obstruction to every recovery term follows from preservation of dependence
on at most one argument; no bounded term search is assumed in these negatives.

For the third companion, E125 simplifies it to `(y*x)*y`; its square as a
right translation recovers the original multiplication:
`(x □ y) □ y = x*y`. Both statements are proved in Lean. Its usual two-product recovery already
fails at the diagonal in a Lean-verified infinite E73 model. The seven-pair
free-group seed is

```
f(1)=a, f(a)=b, f(b)=1,
f(b⁻¹)=c, f(c)=b⁻¹, f(c⁻¹)=d, f(dcb)=e.
```

Here `a,b,c,d,e` are distinct free generators. The original square at `1`
is `a`, whereas the proposed recovered square is `e`. The existing extension
theorem supplies a total model from this finite seed. A bounded test in the
infinite E73 extension found no recovery term through eight leaves;
that is research evidence, not a proof that no recovery term exists.
The unrestricted E73 → E8 class arrow remains open.
