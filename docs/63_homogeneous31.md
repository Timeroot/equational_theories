# New idempotent E63 seeds at orders 31 and 41

28 September 2026. An idempotent E63 model of order **31** is now proved in
Lean. Its field-design consequence supplies an idempotent model of order
**255**, the missing `7·32+31` construction noted in the previous spectrum
report. Both proofs are in
[`Spectrum/Equation63/Homogeneous31.lean`](../equational_theories/Spectrum/Equation63/Homogeneous31.lean).

Work in F31. Set `p(0,y)=5y`, and for `x≠0` set

    p(x,y) = x h(y/x),

where the values of h, indexed from 0 through 30, are

    30, 1, 28, 29, 13, 6, 26, 3, 20, 4, 8, 23, 16, 9, 15, 19,
    17, 12, 27, 14, 10, 11, 18, 21, 2, 0, 5, 22, 24, 7, 25.

The operation satisfies `p(y,p(x,p(x,y)))=x` and `p(x,x)=x`. The Lean
representation stores this profile and the 31 multiplicative inverses. The
kernel checks all 961 law instances and all 31 diagonal entries by ordinary
`decide +kernel`; no solver refutation or native computation axiom is involved.
`Spectrum.E63.idem31` has only `propext` in its axiom audit.

For order 255, use the existing TD(8,32) from F32, fill seven groups with the
idempotent order 32 model, and truncate the last group to the new order 31
model. The transversal blocks have sizes seven or eight, whose idempotent
fillings were already proved. `Spectrum.E63.idem255` has only the standard
three Lean axioms.

The model was found while investigating finite FO transfers into E1516.
For a homogeneous operation, E1516 reduces to a constraint problem for h and
its inverse permutation. Setting `h(1)=1` makes the operation idempotent, so
E1516 becomes E63. The strengthened inverse-permutation encoding found this
model in about 27 seconds. Existence rests on the complete Lean check,
independently of the search.

The same search found an idempotent model at **41** in about 36 seconds.
It is formalized as `Spectrum.E63.idem41` in
[`Homogeneous41.lean`](../equational_theories/Spectrum/Equation63/Homogeneous41.lean),
again with only `propext`. Here `p(0,y)=18y` over F41 and the profile is

    31,1,29,14,37,24,11,5,15,3,18,21,39,8,9,13,4,36,40,12,30,
    6,2,10,7,23,33,38,26,22,35,16,27,28,17,20,34,0,32,19,25.

This directly supplies the previously missing order 41 E1516 model discussed
in the finite FO-transfer investigation.

The saved profile is in
[`data/spectrum/63_idempotent31.json`](../data/spectrum/63_idempotent31.json).
`python3 scripts/fo_1516_homogeneous29.py` checks both models independently on
their full tables. The idempotent closure generator now uses the proved
constructions `idem31`, `idem41`, and `idem255`; the latter is a design construction,
not a separate stored table witness. The existing nonidempotent E63 exception
list and its pending exclusions are unchanged.

The regenerated finite-field closure supplies 33 additional idempotent orders
below 1480:

    31,41,205,234,236,238,240,242,244,248,255,290,298,304,310,314,
    321,327,332,374,384,402,412,423,451,489,510,527,654,710,779,899,1039.

The established tail still starts at 1228. Transfer and products give E667 new
orders 255, 321, 327, 489, 510, 654 and the E883 family new
orders 255, 321, 327, 423, 489, 510, 654. Thus E667 has29 genuinely open cases left,
and E883 has 36. With the order 41 seed included, 510 also has an idempotent
construction. The idempotent possible-exception list below 1480 shrinks from
173 to 140 entries.
