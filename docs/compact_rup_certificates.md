# Compact RUP certificates

The order-sixteen E467 exclusion saves compact certificates in
`data/spectrum/467_sixteen_rup/`. They are gzip-compressed data, not executable
code. The accompanying JSON records the encoding, canonical case, compressed
and expanded SHA-256 hashes, source LRAT hash, and relevant sizes.

## Trust and checking

An external SAT solver produces an LRAT refutation. Lean's LRAT trimmer/checker
checks that refutation before `scripts/spectrum_compact_rup.cpp` packs it.
The packer accepts RUP additions only and rejects RAT additions. Ordinary Lean
builds do not need the solver or the packer.

At build time, `Spectrum.CertificateData.CompactRup.reconstruct` reads the
compact data and the actual Lean-defined CNF. It uses watched-literal unit
propagation to reconstruct a conventional `Array IntAction`. Each learned
clause is checked under its negated literals. The reconstruction retains a
dependency slice of the propagation trail as its LRAT hint list. Permanent
root assignments are cached, and their supporting clauses are retained even
if the original trace deleted them. An earlier root contradiction can finish
the reconstructed proof early.

This reconstruction is a pure Lean program, **not a trusted proof checker**.
The proof is subsequently passed to `Std.Tactic.BVDecide.LRAT.check`, and
`check_sound` proves unsatisfiability. Thus the reconstruction algorithm does
not need its own correctness theorem to establish the exclusion. The final
checks have the same explicit `spectrum_native` policy as the original saved
LRAT certificates, and every exposed theorem has a completeness audit.

The `SpectrumCertificateData` library imports and precompiles the reconstruction
module. This matters: interpreting that loop during each proof check is much
slower. The program also releases its old state before a fallible propagation
call; otherwise Lean's reference counting forces repeated copies of the
entire clause database.

## Version 1 format

All integers use unsigned base-128 variable-length encoding, low groups first.
The first integer is twice the first learned-clause ID, as in binary LRAT.
That ID must be one more than the number of input clauses. Subsequent addition
IDs are consecutive and implicit.

Each record starts with ASCII `a` (addition) or `d` (deletion):

- An addition stores a backward distance into a 256-entry clause history, or
  zero for no base clause. A nonzero distance is followed by a keep-mask for
  the base clause, whose length is at most 63. Added literal codes follow in
  sorted order, encoded as `current − previous + 1`, starting from zero and
  ending with zero. The resulting clause is sorted before it enters the
  history. Literal codes are the binary LRAT codes `2*v` for positive `v`
  and `2*v+1` for negative `v`, with one-based variables.
- A deletion stores sorted clause IDs, encoded with the same positive-delta
  convention and a zero terminator. These IDs are ordinary IDs, not doubled
  binary LRAT integers. The packer omits requests for clause IDs that do not
  yet exist: these requests do nothing in the source trace. The stream audit
  checks this bound before Lean reconstruction.

No propagation hints are stored. The empty learned clause ends the proof.
The format deliberately has no facilities for executing code or bypassing
the final LRAT check.

### Optional input-clause mask

The E667 collision certificates use an extension to this format. Immediately
after the initial integer, an optional ASCII `m` introduces one byte per
original clause ID (including unused ID zero). A zero byte tells reconstruction
to omit that input clause from its watch lists; a positive byte selects it.
Clause IDs remain unchanged, and the addition/deletion stream then follows as
above. Old streams without this header remain supported.

`scripts/spectrum_compact_rup.cpp --input-mask OUTPUT` selects the input clauses
referenced by the trimmed LRAT proof. This reduces propagation work during hint
reconstruction. The final verified LRAT checker still receives the entire
original CNF, so the selection is untrusted data and cannot weaken the check.
The E667 files use xz compression; `include_binary_xz` embeds their expanded
bytes, just as `include_binary_gzip` does for older files. Builds require the
corresponding decompressor. Measurements and reproduction details are in
[the E667 order-twelve note](e667_order12_square_map_20261005.md).

## Reproduction

```sh
python3 scripts/spectrum_467_sixteen_data.py
python3 scripts/spectrum_467_sixteen_certificate.py --write-lean --audit
python3 scripts/spectrum_467_sixteen_certificate.py --audit-lean-cnf
lake build equational_theories.Definability.Equation467Spectrum
```

`--audit` checks file hashes and regenerates the exact solver input for each
case. `--audit-lean-cnf` independently exports every selected formula from Lean
and compares those hashes. The final build checks the actual refutations.
`--generate --solver PATH` prepares new certificates where saved successes
are absent; it requires a C++ compiler and CaDiCaL with LRAT output support.

The E467 package shrank from 1,734,568,959 to 162,367,842 compressed bytes.
The largest file is 8,704,434 bytes. The 112 checks share 19 modules, balanced
by certificate size to avoid making several large checks one serial build
job. Reconstructing omitted hints adds computation to a cold build; the size
reduction is not a claim that every individual proof check becomes faster.
The chosen batch assignment is saved in metadata so that replacing one
certificate does not rearrange and invalidate every batch's build cache.
