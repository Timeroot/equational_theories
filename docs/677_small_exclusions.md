# E677 has no models of orders three or four

The external refutations recorded in the September 2026 survey are now
formalized in Lean:

* `Spectrum.not_order_677_3 : ¬ Law677.HasModel 3`;
* `Spectrum.not_order_677_4 : ¬ Law677.HasModel 4`.

Both are in `equational_theories/Spectrum/Equation677/Small.lean`. They
exhaust all multiplication tables at the indicated orders, without
assuming cancellation, commutativity, or idempotence. The three-element
encoding uses 18 bits and checks all nine instances of E677; the
four-element encoding uses 32 bits and checks all sixteen instances.
The conversion from an arbitrary magma to its table encoding is proved
in Lean.

The saved `Three.lrat` and `Four.lrat` files are approximately 22 KiB and
99 KiB. Ordinary builds replay them with `bv_check`; they do not run a
model search. Each final theorem has an exact axiom guard allowing the
three standard axioms and its single compiled LRAT-checker axiom. Both
also pass `spectrum_assert ... complete`. These are audited native proofs;
the external solver's original UNSAT answer is not assumed.

Certificate hashes and declaration names are recorded in
`data/spectrum/677_small_exclusions.json`. The exact spectrum of E677
remains open; these results add only the exclusions at three and four.
