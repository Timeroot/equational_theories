# Explicit idempotent E63 tail

The construction below gives an idempotent E63 magma at every order **n ≥ 1480**.
The additional finite-field designs in `Spectrum/Equation63/FieldTail.lean`
now improve this to **n ≥ 1228**; see the
[finite-field supplement](667_883_spectrum_progress.md#finite-field-designs-improve-the-cutoff-to-1228).
Both bounds are constructive and independent of Wilson's asymptotic existence
theorem. Neither bound is claimed optimal. The original arithmetic certificate
described below is retained unchanged.

## Ingredients

The operation satisfies `y * (x * (x * y)) = x` and `x * x = x`.
The available constructions are:

* Affine models on `Z/nZ` whenever `b³ − b + 1 = 0` modulo `n`.
* A model at every cube `n³`, obtained from the companion matrix
  `B(x₀,x₁,x₂) = (−x₂,x₀+x₂,x₁)` using `x*y = x−Bx+By`.
* The concrete idempotent models of orders 8 and 32. The latter is obtained
  from Bennett's partial C3 quasigroup of type `2⁴`, inflated by the
  four-element C3 quasigroup and filled with four idempotent eight-element
  quasigroups; taking left division gives E63.
* Products of idempotent models.
* Singular products of order `k(q−1)+1`, with idempotent factors at `k` and
  `q`, and an ordinary E63 model at `q−1`. The diagonal is calculated in a
  copy of the idempotent `q`-point factor. The ordinary factors used here
  are all below 1608 and covered by the previously proved E63 finite basis.
* Seven-group gluing of order `7q+r`, for `r≤q`, using idempotent group
  fillings of orders `q,r` and idempotent block fillings of orders 7 and 8.
  The transversal designs used are the cyclic construction when
  `gcd(q,60)=1`, and the existing finite designs at `q=25,27,36`.

## Finite part

The deterministic generator `scripts/spectrum_63_idempotent_bounds.py`
constructs 1888 orders below 2086 from these ingredients. Every order in
`[1480,2086)` occurs. There are 198 smaller orders not reached by this
construction; these are possible exceptions, not nonexistence claims.

For each `2086≤n<12176`, choose

`q = ceil(n/8) + d`, `r = n−7q`,

where `0≤d≤30` is supplied by a packed arithmetic certificate. Direct
checking gives `gcd(q,60)=1`, `0≤r≤q`, and both `q` and `r` belong to the
already constructed orders below 2086. In fact the selected ingredients
are at most 1523. Thus seven-group gluing covers the rest of the finite
interval `[1480,12176)`.

The generator supplies individual Lean applications of the proved
construction lemmas. The arithmetic certificate is checked using
`decide +kernel` in batches of at most 256 cases to limit memory use;
no search result or Python computation is trusted. Reproduce and check
the generated files without rewriting them with:

```sh
python3 scripts/spectrum_63_idempotent_bounds.py --check
python3 scripts/spectrum_63_idempotent_seeds.py --check-lean equational_theories/Spectrum/Equation63/IdempotentSeeds.lean
```

## Induction

Every six consecutive integers contain one coprime to 60, as a check of
the 60 residue classes shows. Suppose `n≥12176=8(1480+42)`. Choose

`q = ceil(n/8)+d`, with `0≤d≤5` and `gcd(q,60)=1`, and put `r=n−7q`.

Then `1480≤q<n`, `1480≤r<n`, and `r≤q`. Strong induction supplies the two
idempotent group fillings, and seven-group gluing supplies order `n`.
Together with the finite part, this proves the stated tail.

Lean interfaces are `Spectrum.E63.idempotent_all_large` and
`Spectrum.E63.idempotent_model_of_not_exception` in
`Spectrum/Equation63/IdempotentTail.lean`. The latter also includes the
proved small orders, using the explicit possible-exception list
`Spectrum.E63.IdempotentFiniteBasis.exceptions`.
