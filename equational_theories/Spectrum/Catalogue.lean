import equational_theories.Spectrum.Generated.NoteBounds

/-!
# Spectrum catalogue: coverage, evidence, and proof organization

All E1–E4694 are covered. An exact formula stated in the note is NOT necessarily
a completed proof here. Each theorem is followed by a `spectrum_assert` that
checks its actual transitive dependencies (not a generator's claim):

* `complete`: no sorry or undocumented axioms. Standard Lean axioms are allowed;
  native_decide/bv_decide axioms require an explicitly tagged owner theorem.
* `proofAvailable`: a mathematical argument, cited theorem, or reported finite
  ATP/model result exists, but its proof is not integrated here. This does
  NOT mean a replayable ATP certificate is currently available in this repo.
* `noteGap`: at least one essential step is elided/unclear in the note and has
  not been reconstructed. This is not a claim that the spectrum is open.
* `openProblems`: exact spectra still UNKNOWN after the recorded supplements.
  These have bounds, never an exact theorem (not even one using sorry).
* `sourceConflicts`: contradictory source claims, not silently promoted to proofs.

To see the exact missing steps and source sections for any declaration:
`#spectrum_status Spectrum.Catalogue.exact_546`

Proof layers:
1. Basic/Definability/Linear/Constructions/Exact/Transfer: reusable mathematics.
2. Generated.Linear*, Modular, Two, NoteWitnesses: checked positive witnesses.
3. Generated.SmallOrder: native enumeration only at an exclusion basis;
   NegativeTransfer: proved implication/duality/definability routes to that basis.
   SmallExclusions: checked BV exclusions for E474 at size 4 and E1286 at size 5;
   Squaring/Symmetry/BitTables: complete relabeling and magma-to-BV bridges.
4. NotePending and Generated.NoteObligations: the ONLY sorry boundaries, each
   annotated with evidence, source, and the precise missing formalization.
5. Note/Generated.NoteBounds: assemble formulas; this file transfers them to all laws.

Data is deliberately not a proof oracle: data/spectrum/witnesses.json and
bv_cases.json are INPUT (candidate tables and SAT-core selections rechecked
in Lean); catalogue.json is GENERATED OUTPUT. The integrated BV proofs and
their total compilation timings are documented in docs/spectrum_bv.md.
There is no separate JSON list of obligations: their provenance lives in Lean.
See docs/spectrum_status.md and scripts/check_spectrum.lean for the full audit.
-/

open Law Law.MagmaLaw
namespace Spectrum.Catalogue

theorem exact_1 : Law1.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1
spectrum_assert exact_1 complete

theorem exact_2 : Law2.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2
spectrum_assert exact_2 complete

theorem exact_3 : Law3.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3
spectrum_assert exact_3 complete

theorem exact_4 : Law4.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4
spectrum_assert exact_4 complete

theorem exact_5 : Law5.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_5
spectrum_assert exact_5 complete

theorem exact_6 : Law6.spectrum = ({1}) :=
  ImplicationTransfer.singleton_6
spectrum_assert exact_6 complete

theorem exact_7 : Law7.spectrum = ({1}) :=
  ImplicationTransfer.singleton_7
spectrum_assert exact_7 complete

theorem exact_8 : Law8.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_8
spectrum_assert exact_8 complete

theorem exact_9 : Law9.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_9
spectrum_assert exact_9 complete

theorem exact_10 : Law10.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_10
spectrum_assert exact_10 complete

theorem exact_11 : Law11.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_11
spectrum_assert exact_11 complete

theorem exact_12 : Law12.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_12
spectrum_assert exact_12 complete

theorem exact_13 : Law13.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_13
spectrum_assert exact_13 complete

theorem exact_14 : Law14.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_14
spectrum_assert exact_14 complete

theorem exact_15 : Law15.spectrum = ({1}) :=
  ImplicationTransfer.singleton_15
spectrum_assert exact_15 complete

theorem exact_16 : Law16.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_16
spectrum_assert exact_16 complete

theorem exact_17 : Law17.spectrum = ({1}) :=
  ImplicationTransfer.singleton_17
spectrum_assert exact_17 complete

theorem exact_18 : Law18.spectrum = ({1}) :=
  ImplicationTransfer.singleton_18
spectrum_assert exact_18 complete

theorem exact_19 : Law19.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_19
spectrum_assert exact_19 complete

theorem exact_20 : Law20.spectrum = ({1}) :=
  ImplicationTransfer.singleton_20
spectrum_assert exact_20 complete

theorem exact_21 : Law21.spectrum = ({1}) :=
  ImplicationTransfer.singleton_21
spectrum_assert exact_21 complete

theorem exact_22 : Law22.spectrum = ({1}) :=
  ImplicationTransfer.singleton_22
spectrum_assert exact_22 complete

theorem exact_23 : Law23.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_23
spectrum_assert exact_23 complete

theorem exact_24 : Law24.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_24
spectrum_assert exact_24 complete

theorem exact_25 : Law25.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_25
spectrum_assert exact_25 complete

theorem exact_26 : Law26.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_26
spectrum_assert exact_26 complete

theorem exact_27 : Law27.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_27
spectrum_assert exact_27 complete

theorem exact_28 : Law28.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_28
spectrum_assert exact_28 complete

theorem exact_29 : Law29.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_29
spectrum_assert exact_29 complete

theorem exact_30 : Law30.spectrum = ({1}) :=
  ImplicationTransfer.singleton_30
spectrum_assert exact_30 complete

theorem exact_31 : Law31.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_31
spectrum_assert exact_31 complete

theorem exact_32 : Law32.spectrum = ({1}) :=
  ImplicationTransfer.singleton_32
spectrum_assert exact_32 complete

theorem exact_33 : Law33.spectrum = ({1}) :=
  ImplicationTransfer.singleton_33
spectrum_assert exact_33 complete

theorem exact_34 : Law34.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_34
spectrum_assert exact_34 complete

theorem exact_35 : Law35.spectrum = ({1}) :=
  ImplicationTransfer.singleton_35
spectrum_assert exact_35 complete

theorem exact_36 : Law36.spectrum = ({1}) :=
  ImplicationTransfer.singleton_36
spectrum_assert exact_36 complete

theorem exact_37 : Law37.spectrum = ({1}) :=
  ImplicationTransfer.singleton_37
spectrum_assert exact_37 complete

theorem exact_38 : Law38.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_38
spectrum_assert exact_38 complete

theorem exact_39 : Law39.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_39
spectrum_assert exact_39 complete

theorem exact_40 : Law40.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_40
spectrum_assert exact_40 complete

theorem exact_41 : Law41.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_41
spectrum_assert exact_41 complete

theorem exact_42 : Law42.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_42
spectrum_assert exact_42 complete

theorem exact_43 : Law43.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_43
spectrum_assert exact_43 complete

theorem exact_44 : Law44.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_44
spectrum_assert exact_44 complete

theorem exact_45 : Law45.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_45
spectrum_assert exact_45 complete

theorem exact_46 : Law46.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_46
spectrum_assert exact_46 complete

theorem exact_47 : Law47.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_47
spectrum_assert exact_47 complete

theorem exact_48 : Law48.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_48
spectrum_assert exact_48 complete

theorem exact_49 : Law49.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_49
spectrum_assert exact_49 complete

theorem exact_50 : Law50.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_50
spectrum_assert exact_50 complete

theorem exact_51 : Law51.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_51
spectrum_assert exact_51 complete

theorem exact_52 : Law52.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_52
spectrum_assert exact_52 complete

theorem exact_53 : Law53.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_53
spectrum_assert exact_53 complete

theorem exact_54 : Law54.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_54
spectrum_assert exact_54 complete

theorem exact_55 : Law55.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_55
spectrum_assert exact_55 complete

theorem exact_56 : Law56.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_56
spectrum_assert exact_56 complete

theorem exact_57 : Law57.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_57
spectrum_assert exact_57 complete

theorem exact_58 : Law58.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_58
spectrum_assert exact_58 complete

theorem exact_59 : Law59.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_59
spectrum_assert exact_59 complete

theorem exact_60 : Law60.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_60
spectrum_assert exact_60 complete

theorem exact_61 : Law61.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_61
spectrum_assert exact_61 complete

theorem exact_62 : Law62.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_62
spectrum_assert exact_62 complete

-- UNKNOWN exact spectrum (PDF representative E63).
theorem lower_63 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law63.spectrum := by
  rw [ImplicationTransfer.spectrum_63_eq_63]
  exact Note.lower_63
spectrum_assert lower_63 complete

theorem upper_63 : Law63.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_63_eq_63]
  exact Note.upper_63
spectrum_assert upper_63 proofAvailable

theorem cofinite_63 : CofiniteSpectrum Law63 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_63_eq_63]
  exact Note.cofinite_63
spectrum_assert cofinite_63 proofAvailable

theorem exact_64 : Law64.spectrum = ({1}) :=
  ImplicationTransfer.singleton_64
spectrum_assert exact_64 complete

theorem exact_65 : Law65.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_65
spectrum_assert exact_65 complete

theorem exact_66 : Law66.spectrum = (residues 3 {0, 1} {6}) :=
  ImplicationTransfer.spectrum_66_eq_66 |>.trans Note.exact_66
spectrum_assert exact_66 complete

theorem exact_67 : Law67.spectrum = ({1}) :=
  ImplicationTransfer.singleton_67
spectrum_assert exact_67 complete

theorem exact_68 : Law68.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_68
spectrum_assert exact_68 complete

theorem exact_69 : Law69.spectrum = ({1}) :=
  ImplicationTransfer.singleton_69
spectrum_assert exact_69 complete

theorem exact_70 : Law70.spectrum = ({1}) :=
  ImplicationTransfer.singleton_70
spectrum_assert exact_70 complete

theorem exact_71 : Law71.spectrum = ({1}) :=
  ImplicationTransfer.singleton_71
spectrum_assert exact_71 complete

theorem exact_72 : Law72.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_72
spectrum_assert exact_72 complete

-- UNKNOWN exact spectrum (PDF representative E73).
theorem lower_73 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law73.spectrum := by
  rw [ImplicationTransfer.spectrum_73_eq_73]
  exact Note.lower_73
spectrum_assert lower_73 complete

theorem upper_73 : Law73.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_73_eq_73]
  exact Note.upper_73
spectrum_assert upper_73 proofAvailable

theorem cofinite_73 : CofiniteSpectrum Law73 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_73_eq_73]
  exact Note.cofinite_73
spectrum_assert cofinite_73 proofAvailable

theorem exact_74 : Law74.spectrum = ({1}) :=
  ImplicationTransfer.singleton_74
spectrum_assert exact_74 complete

theorem exact_75 : Law75.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_75
spectrum_assert exact_75 complete

theorem exact_76 : Law76.spectrum = ({1}) :=
  ImplicationTransfer.singleton_76
spectrum_assert exact_76 complete

theorem exact_77 : Law77.spectrum = ({1}) :=
  ImplicationTransfer.singleton_77
spectrum_assert exact_77 complete

theorem exact_78 : Law78.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_78
spectrum_assert exact_78 complete

theorem exact_79 : Law79.spectrum = ({1}) :=
  ImplicationTransfer.singleton_79
spectrum_assert exact_79 complete

theorem exact_80 : Law80.spectrum = ({1}) :=
  ImplicationTransfer.singleton_80
spectrum_assert exact_80 complete

theorem exact_81 : Law81.spectrum = ({1}) :=
  ImplicationTransfer.singleton_81
spectrum_assert exact_81 complete

theorem exact_82 : Law82.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_82
spectrum_assert exact_82 complete

theorem exact_83 : Law83.spectrum = ({1}) :=
  ImplicationTransfer.singleton_83
spectrum_assert exact_83 complete

theorem exact_84 : Law84.spectrum = ({1}) :=
  ImplicationTransfer.singleton_84
spectrum_assert exact_84 complete

theorem exact_85 : Law85.spectrum = ({1}) :=
  ImplicationTransfer.singleton_85
spectrum_assert exact_85 complete

theorem exact_86 : Law86.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_86
spectrum_assert exact_86 complete

theorem exact_87 : Law87.spectrum = ({1}) :=
  ImplicationTransfer.singleton_87
spectrum_assert exact_87 complete

theorem exact_88 : Law88.spectrum = ({1}) :=
  ImplicationTransfer.singleton_88
spectrum_assert exact_88 complete

theorem exact_89 : Law89.spectrum = ({1}) :=
  ImplicationTransfer.singleton_89
spectrum_assert exact_89 complete

theorem exact_90 : Law90.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_90
spectrum_assert exact_90 complete

theorem exact_91 : Law91.spectrum = ({1}) :=
  ImplicationTransfer.singleton_91
spectrum_assert exact_91 complete

theorem exact_92 : Law92.spectrum = ({1}) :=
  ImplicationTransfer.singleton_92
spectrum_assert exact_92 complete

theorem exact_93 : Law93.spectrum = ({1}) :=
  ImplicationTransfer.singleton_93
spectrum_assert exact_93 complete

theorem exact_94 : Law94.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_94
spectrum_assert exact_94 complete

theorem exact_95 : Law95.spectrum = ({1}) :=
  ImplicationTransfer.singleton_95
spectrum_assert exact_95 complete

theorem exact_96 : Law96.spectrum = ({1}) :=
  ImplicationTransfer.singleton_96
spectrum_assert exact_96 complete

theorem exact_97 : Law97.spectrum = ({1}) :=
  ImplicationTransfer.singleton_97
spectrum_assert exact_97 complete

theorem exact_98 : Law98.spectrum = ({1}) :=
  ImplicationTransfer.singleton_98
spectrum_assert exact_98 complete

theorem exact_99 : Law99.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_99
spectrum_assert exact_99 complete

theorem exact_100 : Law100.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_100
spectrum_assert exact_100 complete

theorem exact_101 : Law101.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_101
spectrum_assert exact_101 complete

theorem exact_102 : Law102.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_102
spectrum_assert exact_102 complete

theorem exact_103 : Law103.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_103
spectrum_assert exact_103 complete

theorem exact_104 : Law104.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_104
spectrum_assert exact_104 complete

theorem exact_105 : Law105.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_105
spectrum_assert exact_105 complete

theorem exact_106 : Law106.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_106
spectrum_assert exact_106 complete

theorem exact_107 : Law107.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_107
spectrum_assert exact_107 complete

theorem exact_108 : Law108.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_108
spectrum_assert exact_108 complete

theorem exact_109 : Law109.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_109
spectrum_assert exact_109 complete

theorem exact_110 : Law110.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_110
spectrum_assert exact_110 complete

theorem exact_111 : Law111.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_111
spectrum_assert exact_111 complete

theorem exact_112 : Law112.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_112
spectrum_assert exact_112 complete

theorem exact_113 : Law113.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_113
spectrum_assert exact_113 complete

theorem exact_114 : Law114.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_114
spectrum_assert exact_114 complete

-- UNKNOWN exact spectrum (PDF representative E115).
theorem lower_115 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law115.spectrum := by
  rw [ImplicationTransfer.spectrum_115_eq_115]
  exact Note.lower_115
spectrum_assert lower_115 proofAvailable

theorem upper_115 : Law115.spectrum ⊆ (positiveExcept {2, 6}) := by
  rw [ImplicationTransfer.spectrum_115_eq_115]
  exact Note.upper_115
spectrum_assert upper_115 proofAvailable

theorem exact_116 : Law116.spectrum = ({1}) :=
  ImplicationTransfer.singleton_116
spectrum_assert exact_116 complete

theorem exact_117 : Law117.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_117
spectrum_assert exact_117 complete

-- UNKNOWN exact spectrum (PDF representative E118).
theorem lower_118 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law118.spectrum := by
  rw [ImplicationTransfer.spectrum_118_eq_118]
  exact Note.lower_118
spectrum_assert lower_118 complete

theorem upper_118 : Law118.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_118_eq_118]
  exact Note.upper_118
spectrum_assert upper_118 proofAvailable

theorem cofinite_118 : CofiniteSpectrum Law118 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_118_eq_118]
  exact Note.cofinite_118
spectrum_assert cofinite_118 proofAvailable

theorem exact_119 : Law119.spectrum = ({1}) :=
  ImplicationTransfer.singleton_119
spectrum_assert exact_119 complete

theorem exact_120 : Law120.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_120
spectrum_assert exact_120 complete

theorem exact_121 : Law121.spectrum = ({1}) :=
  ImplicationTransfer.singleton_121
spectrum_assert exact_121 complete

theorem exact_122 : Law122.spectrum = ({1}) :=
  ImplicationTransfer.singleton_122
spectrum_assert exact_122 complete

theorem exact_123 : Law123.spectrum = ({1}) :=
  ImplicationTransfer.singleton_123
spectrum_assert exact_123 complete

theorem exact_124 : Law124.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_124
spectrum_assert exact_124 complete

-- UNKNOWN exact spectrum (PDF representative E125).
theorem lower_125 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law125.spectrum := by
  rw [ImplicationTransfer.spectrum_125_eq_125]
  exact Note.lower_125
spectrum_assert lower_125 complete

theorem upper_125 : Law125.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_125_eq_125]
  exact Note.upper_125
spectrum_assert upper_125 proofAvailable

theorem cofinite_125 : CofiniteSpectrum Law125 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_125_eq_125]
  exact Note.cofinite_125
spectrum_assert cofinite_125 proofAvailable

theorem exact_126 : Law126.spectrum = ({1}) :=
  ImplicationTransfer.singleton_126
spectrum_assert exact_126 complete

theorem exact_127 : Law127.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_127
spectrum_assert exact_127 complete

theorem exact_128 : Law128.spectrum = ({1}) :=
  ImplicationTransfer.singleton_128
spectrum_assert exact_128 complete

theorem exact_129 : Law129.spectrum = ({1}) :=
  ImplicationTransfer.singleton_129
spectrum_assert exact_129 complete

theorem exact_130 : Law130.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_130
spectrum_assert exact_130 complete

theorem exact_131 : Law131.spectrum = ({1}) :=
  ImplicationTransfer.singleton_131
spectrum_assert exact_131 complete

theorem exact_132 : Law132.spectrum = ({1}) :=
  ImplicationTransfer.singleton_132
spectrum_assert exact_132 complete

theorem exact_133 : Law133.spectrum = ({1}) :=
  ImplicationTransfer.singleton_133
spectrum_assert exact_133 complete

theorem exact_134 : Law134.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_134
spectrum_assert exact_134 complete

theorem exact_135 : Law135.spectrum = ({1}) :=
  ImplicationTransfer.singleton_135
spectrum_assert exact_135 complete

theorem exact_136 : Law136.spectrum = ({1}) :=
  ImplicationTransfer.singleton_136
spectrum_assert exact_136 complete

theorem exact_137 : Law137.spectrum = ({1}) :=
  ImplicationTransfer.singleton_137
spectrum_assert exact_137 complete

theorem exact_138 : Law138.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_138
spectrum_assert exact_138 complete

theorem exact_139 : Law139.spectrum = ({1}) :=
  ImplicationTransfer.singleton_139
spectrum_assert exact_139 complete

theorem exact_140 : Law140.spectrum = ({1}) :=
  ImplicationTransfer.singleton_140
spectrum_assert exact_140 complete

theorem exact_141 : Law141.spectrum = ({1}) :=
  ImplicationTransfer.singleton_141
spectrum_assert exact_141 complete

theorem exact_142 : Law142.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_142
spectrum_assert exact_142 complete

theorem exact_143 : Law143.spectrum = ({1}) :=
  ImplicationTransfer.singleton_143
spectrum_assert exact_143 complete

theorem exact_144 : Law144.spectrum = ({1}) :=
  ImplicationTransfer.singleton_144
spectrum_assert exact_144 complete

theorem exact_145 : Law145.spectrum = ({1}) :=
  ImplicationTransfer.singleton_145
spectrum_assert exact_145 complete

theorem exact_146 : Law146.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_146
spectrum_assert exact_146 complete

theorem exact_147 : Law147.spectrum = ({1}) :=
  ImplicationTransfer.singleton_147
spectrum_assert exact_147 complete

theorem exact_148 : Law148.spectrum = ({1}) :=
  ImplicationTransfer.singleton_148
spectrum_assert exact_148 complete

theorem exact_149 : Law149.spectrum = ({1}) :=
  ImplicationTransfer.singleton_149
spectrum_assert exact_149 complete

theorem exact_150 : Law150.spectrum = ({1}) :=
  ImplicationTransfer.singleton_150
spectrum_assert exact_150 complete

theorem exact_151 : Law151.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_151
spectrum_assert exact_151 complete

theorem exact_152 : Law152.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_152
spectrum_assert exact_152 complete

theorem exact_153 : Law153.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_153
spectrum_assert exact_153 complete

theorem exact_154 : Law154.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_154
spectrum_assert exact_154 complete

theorem exact_155 : Law155.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_155
spectrum_assert exact_155 complete

theorem exact_156 : Law156.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_156
spectrum_assert exact_156 complete

theorem exact_157 : Law157.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_157
spectrum_assert exact_157 complete

theorem exact_158 : Law158.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_158
spectrum_assert exact_158 complete

theorem exact_159 : Law159.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_159
spectrum_assert exact_159 complete

theorem exact_160 : Law160.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_160
spectrum_assert exact_160 complete

theorem exact_161 : Law161.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_161
spectrum_assert exact_161 complete

theorem exact_162 : Law162.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_162
spectrum_assert exact_162 complete

theorem exact_163 : Law163.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_163
spectrum_assert exact_163 complete

theorem exact_164 : Law164.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_164
spectrum_assert exact_164 complete

theorem exact_165 : Law165.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_165
spectrum_assert exact_165 complete

theorem exact_166 : Law166.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_166
spectrum_assert exact_166 complete

theorem exact_167 : Law167.spectrum = (residues 4 {0, 1} ∅) :=
  ImplicationTransfer.spectrum_167_eq_167 |>.trans Note.exact_167
spectrum_assert exact_167 proofAvailable

theorem exact_168 : Law168.spectrum = (squares) :=
  ImplicationTransfer.spectrum_168_eq_168 |>.trans Note.exact_168
spectrum_assert exact_168 complete

theorem exact_169 : Law169.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_169
spectrum_assert exact_169 complete

theorem exact_170 : Law170.spectrum = (residues 3 {0, 1} {6}) :=
  ImplicationTransfer.spectrum_170_eq_66 |>.trans Note.exact_66
spectrum_assert exact_170 complete

theorem exact_171 : Law171.spectrum = ({1}) :=
  ImplicationTransfer.singleton_171
spectrum_assert exact_171 complete

theorem exact_172 : Law172.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_172
spectrum_assert exact_172 complete

theorem exact_173 : Law173.spectrum = ({1}) :=
  ImplicationTransfer.singleton_173
spectrum_assert exact_173 complete

theorem exact_174 : Law174.spectrum = ({1}) :=
  ImplicationTransfer.singleton_174
spectrum_assert exact_174 complete

theorem exact_175 : Law175.spectrum = ({1}) :=
  ImplicationTransfer.singleton_175
spectrum_assert exact_175 complete

theorem exact_176 : Law176.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_176
spectrum_assert exact_176 complete

theorem exact_177 : Law177.spectrum = (residues 3 {0, 1} {6}) :=
  ImplicationTransfer.spectrum_177_eq_66 |>.trans Note.exact_66
spectrum_assert exact_177 complete

theorem exact_178 : Law178.spectrum = ({1}) :=
  ImplicationTransfer.singleton_178
spectrum_assert exact_178 complete

theorem exact_179 : Law179.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_179
spectrum_assert exact_179 complete

theorem exact_180 : Law180.spectrum = ({1}) :=
  ImplicationTransfer.singleton_180
spectrum_assert exact_180 complete

theorem exact_181 : Law181.spectrum = ({1}) :=
  ImplicationTransfer.singleton_181
spectrum_assert exact_181 complete

theorem exact_182 : Law182.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_182
spectrum_assert exact_182 complete

theorem exact_183 : Law183.spectrum = ({1}) :=
  ImplicationTransfer.singleton_183
spectrum_assert exact_183 complete

theorem exact_184 : Law184.spectrum = ({1}) :=
  ImplicationTransfer.singleton_184
spectrum_assert exact_184 complete

theorem exact_185 : Law185.spectrum = ({1}) :=
  ImplicationTransfer.singleton_185
spectrum_assert exact_185 complete

theorem exact_186 : Law186.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_186
spectrum_assert exact_186 complete

theorem exact_187 : Law187.spectrum = ({1}) :=
  ImplicationTransfer.singleton_187
spectrum_assert exact_187 complete

theorem exact_188 : Law188.spectrum = ({1}) :=
  ImplicationTransfer.singleton_188
spectrum_assert exact_188 complete

theorem exact_189 : Law189.spectrum = ({1}) :=
  ImplicationTransfer.singleton_189
spectrum_assert exact_189 complete

theorem exact_190 : Law190.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_190
spectrum_assert exact_190 complete

theorem exact_191 : Law191.spectrum = ({1}) :=
  ImplicationTransfer.singleton_191
spectrum_assert exact_191 complete

theorem exact_192 : Law192.spectrum = ({1}) :=
  ImplicationTransfer.singleton_192
spectrum_assert exact_192 complete

theorem exact_193 : Law193.spectrum = ({1}) :=
  ImplicationTransfer.singleton_193
spectrum_assert exact_193 complete

theorem exact_194 : Law194.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_194
spectrum_assert exact_194 complete

theorem exact_195 : Law195.spectrum = ({1}) :=
  ImplicationTransfer.singleton_195
spectrum_assert exact_195 complete

theorem exact_196 : Law196.spectrum = ({1}) :=
  ImplicationTransfer.singleton_196
spectrum_assert exact_196 complete

theorem exact_197 : Law197.spectrum = ({1}) :=
  ImplicationTransfer.singleton_197
spectrum_assert exact_197 complete

theorem exact_198 : Law198.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_198
spectrum_assert exact_198 complete

theorem exact_199 : Law199.spectrum = ({1}) :=
  ImplicationTransfer.singleton_199
spectrum_assert exact_199 complete

theorem exact_200 : Law200.spectrum = ({1}) :=
  ImplicationTransfer.singleton_200
spectrum_assert exact_200 complete

theorem exact_201 : Law201.spectrum = ({1}) :=
  ImplicationTransfer.singleton_201
spectrum_assert exact_201 complete

theorem exact_202 : Law202.spectrum = ({1}) :=
  ImplicationTransfer.singleton_202
spectrum_assert exact_202 complete

theorem exact_203 : Law203.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_203
spectrum_assert exact_203 complete

theorem exact_204 : Law204.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_204
spectrum_assert exact_204 complete

theorem exact_205 : Law205.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_205
spectrum_assert exact_205 complete

theorem exact_206 : Law206.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_206
spectrum_assert exact_206 complete

theorem exact_207 : Law207.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_207
spectrum_assert exact_207 complete

theorem exact_208 : Law208.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_208
spectrum_assert exact_208 complete

theorem exact_209 : Law209.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_209
spectrum_assert exact_209 complete

theorem exact_210 : Law210.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_210
spectrum_assert exact_210 complete

theorem exact_211 : Law211.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_211
spectrum_assert exact_211 complete

theorem exact_212 : Law212.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_212
spectrum_assert exact_212 complete

theorem exact_213 : Law213.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_213
spectrum_assert exact_213 complete

theorem exact_214 : Law214.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_214
spectrum_assert exact_214 complete

theorem exact_215 : Law215.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_215
spectrum_assert exact_215 complete

theorem exact_216 : Law216.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_216
spectrum_assert exact_216 complete

theorem exact_217 : Law217.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_217
spectrum_assert exact_217 complete

theorem exact_218 : Law218.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_218
spectrum_assert exact_218 complete

-- UNKNOWN exact spectrum (PDF representative E115).
theorem lower_219 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law219.spectrum := by
  rw [ImplicationTransfer.spectrum_219_eq_115]
  exact Note.lower_115
spectrum_assert lower_219 proofAvailable

theorem upper_219 : Law219.spectrum ⊆ (positiveExcept {2, 6}) := by
  rw [ImplicationTransfer.spectrum_219_eq_115]
  exact Note.upper_115
spectrum_assert upper_219 proofAvailable

theorem exact_220 : Law220.spectrum = ({1}) :=
  ImplicationTransfer.singleton_220
spectrum_assert exact_220 complete

theorem exact_221 : Law221.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_221
spectrum_assert exact_221 complete

-- UNKNOWN exact spectrum (PDF representative E125).
theorem lower_222 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law222.spectrum := by
  rw [ImplicationTransfer.spectrum_222_eq_125]
  exact Note.lower_125
spectrum_assert lower_222 complete

theorem upper_222 : Law222.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_222_eq_125]
  exact Note.upper_125
spectrum_assert upper_222 proofAvailable

theorem cofinite_222 : CofiniteSpectrum Law222 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_222_eq_125]
  exact Note.cofinite_125
spectrum_assert cofinite_222 proofAvailable

theorem exact_223 : Law223.spectrum = ({1}) :=
  ImplicationTransfer.singleton_223
spectrum_assert exact_223 complete

theorem exact_224 : Law224.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_224
spectrum_assert exact_224 complete

theorem exact_225 : Law225.spectrum = ({1}) :=
  ImplicationTransfer.singleton_225
spectrum_assert exact_225 complete

theorem exact_226 : Law226.spectrum = ({1}) :=
  ImplicationTransfer.singleton_226
spectrum_assert exact_226 complete

theorem exact_227 : Law227.spectrum = ({1}) :=
  ImplicationTransfer.singleton_227
spectrum_assert exact_227 complete

theorem exact_228 : Law228.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_228
spectrum_assert exact_228 complete

-- UNKNOWN exact spectrum (PDF representative E118).
theorem lower_229 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law229.spectrum := by
  rw [ImplicationTransfer.spectrum_229_eq_118]
  exact Note.lower_118
spectrum_assert lower_229 complete

theorem upper_229 : Law229.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_229_eq_118]
  exact Note.upper_118
spectrum_assert upper_229 proofAvailable

theorem cofinite_229 : CofiniteSpectrum Law229 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_229_eq_118]
  exact Note.cofinite_118
spectrum_assert cofinite_229 proofAvailable

theorem exact_230 : Law230.spectrum = ({1}) :=
  ImplicationTransfer.singleton_230
spectrum_assert exact_230 complete

theorem exact_231 : Law231.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_231
spectrum_assert exact_231 complete

theorem exact_232 : Law232.spectrum = ({1}) :=
  ImplicationTransfer.singleton_232
spectrum_assert exact_232 complete

theorem exact_233 : Law233.spectrum = ({1}) :=
  ImplicationTransfer.singleton_233
spectrum_assert exact_233 complete

theorem exact_234 : Law234.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_234
spectrum_assert exact_234 complete

theorem exact_235 : Law235.spectrum = ({1}) :=
  ImplicationTransfer.singleton_235
spectrum_assert exact_235 complete

theorem exact_236 : Law236.spectrum = ({1}) :=
  ImplicationTransfer.singleton_236
spectrum_assert exact_236 complete

theorem exact_237 : Law237.spectrum = ({1}) :=
  ImplicationTransfer.singleton_237
spectrum_assert exact_237 complete

theorem exact_238 : Law238.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_238
spectrum_assert exact_238 complete

theorem exact_239 : Law239.spectrum = ({1}) :=
  ImplicationTransfer.singleton_239
spectrum_assert exact_239 complete

theorem exact_240 : Law240.spectrum = ({1}) :=
  ImplicationTransfer.singleton_240
spectrum_assert exact_240 complete

theorem exact_241 : Law241.spectrum = ({1}) :=
  ImplicationTransfer.singleton_241
spectrum_assert exact_241 complete

theorem exact_242 : Law242.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_242
spectrum_assert exact_242 complete

theorem exact_243 : Law243.spectrum = ({1}) :=
  ImplicationTransfer.singleton_243
spectrum_assert exact_243 complete

theorem exact_244 : Law244.spectrum = ({1}) :=
  ImplicationTransfer.singleton_244
spectrum_assert exact_244 complete

theorem exact_245 : Law245.spectrum = ({1}) :=
  ImplicationTransfer.singleton_245
spectrum_assert exact_245 complete

theorem exact_246 : Law246.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_246
spectrum_assert exact_246 complete

theorem exact_247 : Law247.spectrum = ({1}) :=
  ImplicationTransfer.singleton_247
spectrum_assert exact_247 complete

theorem exact_248 : Law248.spectrum = ({1}) :=
  ImplicationTransfer.singleton_248
spectrum_assert exact_248 complete

theorem exact_249 : Law249.spectrum = ({1}) :=
  ImplicationTransfer.singleton_249
spectrum_assert exact_249 complete

theorem exact_250 : Law250.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_250
spectrum_assert exact_250 complete

theorem exact_251 : Law251.spectrum = ({1}) :=
  ImplicationTransfer.singleton_251
spectrum_assert exact_251 complete

theorem exact_252 : Law252.spectrum = ({1}) :=
  ImplicationTransfer.singleton_252
spectrum_assert exact_252 complete

theorem exact_253 : Law253.spectrum = ({1}) :=
  ImplicationTransfer.singleton_253
spectrum_assert exact_253 complete

theorem exact_254 : Law254.spectrum = ({1}) :=
  ImplicationTransfer.singleton_254
spectrum_assert exact_254 complete

theorem exact_255 : Law255.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_255
spectrum_assert exact_255 complete

theorem exact_256 : Law256.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_256
spectrum_assert exact_256 complete

theorem exact_257 : Law257.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_257
spectrum_assert exact_257 complete

theorem exact_258 : Law258.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_258
spectrum_assert exact_258 complete

theorem exact_259 : Law259.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_259
spectrum_assert exact_259 complete

theorem exact_260 : Law260.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_260
spectrum_assert exact_260 complete

theorem exact_261 : Law261.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_261
spectrum_assert exact_261 complete

theorem exact_262 : Law262.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_262
spectrum_assert exact_262 complete

theorem exact_263 : Law263.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_263
spectrum_assert exact_263 complete

theorem exact_264 : Law264.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_264
spectrum_assert exact_264 complete

theorem exact_265 : Law265.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_265
spectrum_assert exact_265 complete

theorem exact_266 : Law266.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_266
spectrum_assert exact_266 complete

theorem exact_267 : Law267.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_267
spectrum_assert exact_267 complete

theorem exact_268 : Law268.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_268
spectrum_assert exact_268 complete

theorem exact_269 : Law269.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_269
spectrum_assert exact_269 complete

theorem exact_270 : Law270.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_270
spectrum_assert exact_270 complete

-- UNKNOWN exact spectrum (PDF representative E63).
theorem lower_271 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law271.spectrum := by
  rw [ImplicationTransfer.spectrum_271_eq_63]
  exact Note.lower_63
spectrum_assert lower_271 complete

theorem upper_271 : Law271.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_271_eq_63]
  exact Note.upper_63
spectrum_assert upper_271 proofAvailable

theorem cofinite_271 : CofiniteSpectrum Law271 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_271_eq_63]
  exact Note.cofinite_63
spectrum_assert cofinite_271 proofAvailable

theorem exact_272 : Law272.spectrum = ({1}) :=
  ImplicationTransfer.singleton_272
spectrum_assert exact_272 complete

theorem exact_273 : Law273.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_273
spectrum_assert exact_273 complete

-- UNKNOWN exact spectrum (PDF representative E73).
theorem lower_274 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law274.spectrum := by
  rw [ImplicationTransfer.spectrum_274_eq_73]
  exact Note.lower_73
spectrum_assert lower_274 complete

theorem upper_274 : Law274.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_274_eq_73]
  exact Note.upper_73
spectrum_assert upper_274 proofAvailable

theorem cofinite_274 : CofiniteSpectrum Law274 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_274_eq_73]
  exact Note.cofinite_73
spectrum_assert cofinite_274 proofAvailable

theorem exact_275 : Law275.spectrum = ({1}) :=
  ImplicationTransfer.singleton_275
spectrum_assert exact_275 complete

theorem exact_276 : Law276.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_276
spectrum_assert exact_276 complete

theorem exact_277 : Law277.spectrum = ({1}) :=
  ImplicationTransfer.singleton_277
spectrum_assert exact_277 complete

theorem exact_278 : Law278.spectrum = ({1}) :=
  ImplicationTransfer.singleton_278
spectrum_assert exact_278 complete

theorem exact_279 : Law279.spectrum = ({1}) :=
  ImplicationTransfer.singleton_279
spectrum_assert exact_279 complete

theorem exact_280 : Law280.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_280
spectrum_assert exact_280 complete

theorem exact_281 : Law281.spectrum = (residues 3 {0, 1} {6}) :=
  ImplicationTransfer.spectrum_281_eq_66 |>.trans Note.exact_66
spectrum_assert exact_281 complete

theorem exact_282 : Law282.spectrum = ({1}) :=
  ImplicationTransfer.singleton_282
spectrum_assert exact_282 complete

theorem exact_283 : Law283.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_283
spectrum_assert exact_283 complete

theorem exact_284 : Law284.spectrum = ({1}) :=
  ImplicationTransfer.singleton_284
spectrum_assert exact_284 complete

theorem exact_285 : Law285.spectrum = ({1}) :=
  ImplicationTransfer.singleton_285
spectrum_assert exact_285 complete

theorem exact_286 : Law286.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_286
spectrum_assert exact_286 complete

theorem exact_287 : Law287.spectrum = ({1}) :=
  ImplicationTransfer.singleton_287
spectrum_assert exact_287 complete

theorem exact_288 : Law288.spectrum = ({1}) :=
  ImplicationTransfer.singleton_288
spectrum_assert exact_288 complete

theorem exact_289 : Law289.spectrum = ({1}) :=
  ImplicationTransfer.singleton_289
spectrum_assert exact_289 complete

theorem exact_290 : Law290.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_290
spectrum_assert exact_290 complete

theorem exact_291 : Law291.spectrum = ({1}) :=
  ImplicationTransfer.singleton_291
spectrum_assert exact_291 complete

theorem exact_292 : Law292.spectrum = ({1}) :=
  ImplicationTransfer.singleton_292
spectrum_assert exact_292 complete

theorem exact_293 : Law293.spectrum = ({1}) :=
  ImplicationTransfer.singleton_293
spectrum_assert exact_293 complete

theorem exact_294 : Law294.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_294
spectrum_assert exact_294 complete

theorem exact_295 : Law295.spectrum = ({1}) :=
  ImplicationTransfer.singleton_295
spectrum_assert exact_295 complete

theorem exact_296 : Law296.spectrum = ({1}) :=
  ImplicationTransfer.singleton_296
spectrum_assert exact_296 complete

theorem exact_297 : Law297.spectrum = ({1}) :=
  ImplicationTransfer.singleton_297
spectrum_assert exact_297 complete

theorem exact_298 : Law298.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_298
spectrum_assert exact_298 complete

theorem exact_299 : Law299.spectrum = ({1}) :=
  ImplicationTransfer.singleton_299
spectrum_assert exact_299 complete

theorem exact_300 : Law300.spectrum = ({1}) :=
  ImplicationTransfer.singleton_300
spectrum_assert exact_300 complete

theorem exact_301 : Law301.spectrum = ({1}) :=
  ImplicationTransfer.singleton_301
spectrum_assert exact_301 complete

theorem exact_302 : Law302.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_302
spectrum_assert exact_302 complete

theorem exact_303 : Law303.spectrum = ({1}) :=
  ImplicationTransfer.singleton_303
spectrum_assert exact_303 complete

theorem exact_304 : Law304.spectrum = ({1}) :=
  ImplicationTransfer.singleton_304
spectrum_assert exact_304 complete

theorem exact_305 : Law305.spectrum = ({1}) :=
  ImplicationTransfer.singleton_305
spectrum_assert exact_305 complete

theorem exact_306 : Law306.spectrum = ({1}) :=
  ImplicationTransfer.singleton_306
spectrum_assert exact_306 complete

theorem exact_307 : Law307.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_307
spectrum_assert exact_307 complete

theorem exact_308 : Law308.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_308
spectrum_assert exact_308 complete

theorem exact_309 : Law309.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_309
spectrum_assert exact_309 complete

theorem exact_310 : Law310.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_310
spectrum_assert exact_310 complete

theorem exact_311 : Law311.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_311
spectrum_assert exact_311 complete

theorem exact_312 : Law312.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_312
spectrum_assert exact_312 complete

theorem exact_313 : Law313.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_313
spectrum_assert exact_313 complete

theorem exact_314 : Law314.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_314
spectrum_assert exact_314 complete

theorem exact_315 : Law315.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_315
spectrum_assert exact_315 complete

theorem exact_316 : Law316.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_316
spectrum_assert exact_316 complete

theorem exact_317 : Law317.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_317
spectrum_assert exact_317 complete

theorem exact_318 : Law318.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_318
spectrum_assert exact_318 complete

theorem exact_319 : Law319.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_319
spectrum_assert exact_319 complete

theorem exact_320 : Law320.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_320
spectrum_assert exact_320 complete

theorem exact_321 : Law321.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_321
spectrum_assert exact_321 complete

theorem exact_322 : Law322.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_322
spectrum_assert exact_322 complete

theorem exact_323 : Law323.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_323
spectrum_assert exact_323 complete

theorem exact_324 : Law324.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_324
spectrum_assert exact_324 complete

theorem exact_325 : Law325.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_325
spectrum_assert exact_325 complete

theorem exact_326 : Law326.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_326
spectrum_assert exact_326 complete

theorem exact_327 : Law327.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_327
spectrum_assert exact_327 complete

theorem exact_328 : Law328.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_328
spectrum_assert exact_328 complete

theorem exact_329 : Law329.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_329
spectrum_assert exact_329 complete

theorem exact_330 : Law330.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_330
spectrum_assert exact_330 complete

theorem exact_331 : Law331.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_331
spectrum_assert exact_331 complete

theorem exact_332 : Law332.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_332
spectrum_assert exact_332 complete

theorem exact_333 : Law333.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_333
spectrum_assert exact_333 complete

theorem exact_334 : Law334.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_334
spectrum_assert exact_334 complete

theorem exact_335 : Law335.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_335
spectrum_assert exact_335 complete

theorem exact_336 : Law336.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_336
spectrum_assert exact_336 complete

theorem exact_337 : Law337.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_337
spectrum_assert exact_337 complete

theorem exact_338 : Law338.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_338
spectrum_assert exact_338 complete

theorem exact_339 : Law339.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_339
spectrum_assert exact_339 complete

theorem exact_340 : Law340.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_340
spectrum_assert exact_340 complete

theorem exact_341 : Law341.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_341
spectrum_assert exact_341 complete

theorem exact_342 : Law342.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_342
spectrum_assert exact_342 complete

theorem exact_343 : Law343.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_343
spectrum_assert exact_343 complete

theorem exact_344 : Law344.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_344
spectrum_assert exact_344 complete

theorem exact_345 : Law345.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_345
spectrum_assert exact_345 complete

theorem exact_346 : Law346.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_346
spectrum_assert exact_346 complete

theorem exact_347 : Law347.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_347
spectrum_assert exact_347 complete

theorem exact_348 : Law348.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_348
spectrum_assert exact_348 complete

theorem exact_349 : Law349.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_349
spectrum_assert exact_349 complete

theorem exact_350 : Law350.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_350
spectrum_assert exact_350 complete

theorem exact_351 : Law351.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_351
spectrum_assert exact_351 complete

theorem exact_352 : Law352.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_352
spectrum_assert exact_352 complete

theorem exact_353 : Law353.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_353
spectrum_assert exact_353 complete

theorem exact_354 : Law354.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_354
spectrum_assert exact_354 complete

theorem exact_355 : Law355.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_355
spectrum_assert exact_355 complete

theorem exact_356 : Law356.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_356
spectrum_assert exact_356 complete

theorem exact_357 : Law357.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_357
spectrum_assert exact_357 complete

theorem exact_358 : Law358.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_358
spectrum_assert exact_358 complete

theorem exact_359 : Law359.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_359
spectrum_assert exact_359 complete

theorem exact_360 : Law360.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_360
spectrum_assert exact_360 complete

theorem exact_361 : Law361.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_361
spectrum_assert exact_361 complete

theorem exact_362 : Law362.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_362
spectrum_assert exact_362 complete

theorem exact_363 : Law363.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_363
spectrum_assert exact_363 complete

theorem exact_364 : Law364.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_364
spectrum_assert exact_364 complete

theorem exact_365 : Law365.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_365
spectrum_assert exact_365 complete

theorem exact_366 : Law366.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_366
spectrum_assert exact_366 complete

theorem exact_367 : Law367.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_367
spectrum_assert exact_367 complete

theorem exact_368 : Law368.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_368
spectrum_assert exact_368 complete

theorem exact_369 : Law369.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_369
spectrum_assert exact_369 complete

theorem exact_370 : Law370.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_370
spectrum_assert exact_370 complete

theorem exact_371 : Law371.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_371
spectrum_assert exact_371 complete

theorem exact_372 : Law372.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_372
spectrum_assert exact_372 complete

theorem exact_373 : Law373.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_373
spectrum_assert exact_373 complete

theorem exact_374 : Law374.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_374
spectrum_assert exact_374 complete

theorem exact_375 : Law375.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_375
spectrum_assert exact_375 complete

theorem exact_376 : Law376.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_376
spectrum_assert exact_376 complete

theorem exact_377 : Law377.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_377
spectrum_assert exact_377 complete

theorem exact_378 : Law378.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_378
spectrum_assert exact_378 complete

theorem exact_379 : Law379.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_379
spectrum_assert exact_379 complete

theorem exact_380 : Law380.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_380
spectrum_assert exact_380 complete

theorem exact_381 : Law381.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_381
spectrum_assert exact_381 complete

theorem exact_382 : Law382.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_382
spectrum_assert exact_382 complete

theorem exact_383 : Law383.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_383
spectrum_assert exact_383 complete

theorem exact_384 : Law384.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_384
spectrum_assert exact_384 complete

theorem exact_385 : Law385.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_385
spectrum_assert exact_385 complete

theorem exact_386 : Law386.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_386
spectrum_assert exact_386 complete

theorem exact_387 : Law387.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_387
spectrum_assert exact_387 complete

theorem exact_388 : Law388.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_388
spectrum_assert exact_388 complete

theorem exact_389 : Law389.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_389
spectrum_assert exact_389 complete

theorem exact_390 : Law390.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_390
spectrum_assert exact_390 complete

theorem exact_391 : Law391.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_391
spectrum_assert exact_391 complete

theorem exact_392 : Law392.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_392
spectrum_assert exact_392 complete

theorem exact_393 : Law393.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_393
spectrum_assert exact_393 complete

theorem exact_394 : Law394.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_394
spectrum_assert exact_394 complete

theorem exact_395 : Law395.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_395
spectrum_assert exact_395 complete

theorem exact_396 : Law396.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_396
spectrum_assert exact_396 complete

theorem exact_397 : Law397.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_397
spectrum_assert exact_397 complete

theorem exact_398 : Law398.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_398
spectrum_assert exact_398 complete

theorem exact_399 : Law399.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_399
spectrum_assert exact_399 complete

theorem exact_400 : Law400.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_400
spectrum_assert exact_400 complete

theorem exact_401 : Law401.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_401
spectrum_assert exact_401 complete

theorem exact_402 : Law402.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_402
spectrum_assert exact_402 complete

theorem exact_403 : Law403.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_403
spectrum_assert exact_403 complete

theorem exact_404 : Law404.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_404
spectrum_assert exact_404 complete

theorem exact_405 : Law405.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_405
spectrum_assert exact_405 complete

theorem exact_406 : Law406.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_406
spectrum_assert exact_406 complete

theorem exact_407 : Law407.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_407
spectrum_assert exact_407 complete

theorem exact_408 : Law408.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_408
spectrum_assert exact_408 complete

theorem exact_409 : Law409.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_409
spectrum_assert exact_409 complete

theorem exact_410 : Law410.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_410
spectrum_assert exact_410 complete

theorem exact_411 : Law411.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_411
spectrum_assert exact_411 complete

theorem exact_412 : Law412.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_412
spectrum_assert exact_412 complete

theorem exact_413 : Law413.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_413
spectrum_assert exact_413 complete

theorem exact_414 : Law414.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_414
spectrum_assert exact_414 complete

theorem exact_415 : Law415.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_415
spectrum_assert exact_415 complete

theorem exact_416 : Law416.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_416
spectrum_assert exact_416 complete

theorem exact_417 : Law417.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_417
spectrum_assert exact_417 complete

theorem exact_418 : Law418.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_418
spectrum_assert exact_418 complete

theorem exact_419 : Law419.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_419
spectrum_assert exact_419 complete

theorem exact_420 : Law420.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_420
spectrum_assert exact_420 complete

theorem exact_421 : Law421.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_421
spectrum_assert exact_421 complete

theorem exact_422 : Law422.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_422
spectrum_assert exact_422 complete

theorem exact_423 : Law423.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_423
spectrum_assert exact_423 complete

theorem exact_424 : Law424.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_424
spectrum_assert exact_424 complete

theorem exact_425 : Law425.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_425
spectrum_assert exact_425 complete

theorem exact_426 : Law426.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_426
spectrum_assert exact_426 complete

theorem exact_427 : Law427.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_427
spectrum_assert exact_427 complete

theorem exact_428 : Law428.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_428
spectrum_assert exact_428 complete

theorem exact_429 : Law429.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_429
spectrum_assert exact_429 complete

theorem exact_430 : Law430.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_430
spectrum_assert exact_430 complete

theorem exact_431 : Law431.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_431
spectrum_assert exact_431 complete

theorem exact_432 : Law432.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_432
spectrum_assert exact_432 complete

theorem exact_433 : Law433.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_433
spectrum_assert exact_433 complete

theorem exact_434 : Law434.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_434
spectrum_assert exact_434 complete

theorem exact_435 : Law435.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_435
spectrum_assert exact_435 complete

theorem exact_436 : Law436.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_436
spectrum_assert exact_436 complete

theorem exact_437 : Law437.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_437
spectrum_assert exact_437 complete

theorem exact_438 : Law438.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_438
spectrum_assert exact_438 complete

theorem exact_439 : Law439.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_439
spectrum_assert exact_439 complete

theorem exact_440 : Law440.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_440
spectrum_assert exact_440 complete

theorem exact_441 : Law441.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_441
spectrum_assert exact_441 complete

theorem exact_442 : Law442.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_442
spectrum_assert exact_442 complete

theorem exact_443 : Law443.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_443
spectrum_assert exact_443 complete

theorem exact_444 : Law444.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_444
spectrum_assert exact_444 complete

theorem exact_445 : Law445.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_445
spectrum_assert exact_445 complete

theorem exact_446 : Law446.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_446
spectrum_assert exact_446 complete

theorem exact_447 : Law447.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_447
spectrum_assert exact_447 complete

theorem exact_448 : Law448.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_448
spectrum_assert exact_448 complete

theorem exact_449 : Law449.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_449
spectrum_assert exact_449 complete

theorem exact_450 : Law450.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_450
spectrum_assert exact_450 complete

theorem exact_451 : Law451.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_451
spectrum_assert exact_451 complete

theorem exact_452 : Law452.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_452
spectrum_assert exact_452 complete

theorem exact_453 : Law453.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_453
spectrum_assert exact_453 complete

theorem exact_454 : Law454.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_454
spectrum_assert exact_454 complete

theorem exact_455 : Law455.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_455
spectrum_assert exact_455 complete

theorem exact_456 : Law456.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_456
spectrum_assert exact_456 complete

theorem exact_457 : Law457.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_457
spectrum_assert exact_457 complete

theorem exact_458 : Law458.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_458
spectrum_assert exact_458 complete

theorem exact_459 : Law459.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_459
spectrum_assert exact_459 complete

theorem exact_460 : Law460.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_460
spectrum_assert exact_460 complete

theorem exact_461 : Law461.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_461
spectrum_assert exact_461 complete

theorem exact_462 : Law462.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_462
spectrum_assert exact_462 complete

theorem exact_463 : Law463.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_463
spectrum_assert exact_463 complete

theorem exact_464 : Law464.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_464
spectrum_assert exact_464 complete

theorem exact_465 : Law465.spectrum = ({1}) :=
  ImplicationTransfer.singleton_465
spectrum_assert exact_465 complete

theorem exact_466 : Law466.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_466
spectrum_assert exact_466 complete

-- UNKNOWN exact spectrum (PDF representative E467).
theorem lower_467 : (({1, 5, 7, 8} : Set ℕ) ∪ (oddSumTwoSquares)) ⊆ Law467.spectrum := by
  rw [ImplicationTransfer.spectrum_467_eq_467]
  exact Note.lower_467
spectrum_assert lower_467 proofAvailable

theorem upper_467 : Law467.spectrum ⊆ (positiveExcept {2, 3, 4, 6}) := by
  rw [ImplicationTransfer.spectrum_467_eq_467]
  exact Note.upper_467
spectrum_assert upper_467 proofAvailable

theorem cofinite_467 : CofiniteSpectrum Law467 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_467_eq_467]
  exact Note.cofinite_467
spectrum_assert cofinite_467 proofAvailable

theorem exact_468 : Law468.spectrum = ({1}) :=
  ImplicationTransfer.singleton_468
spectrum_assert exact_468 complete

theorem exact_469 : Law469.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_469
spectrum_assert exact_469 complete

theorem exact_470 : Law470.spectrum = ({1}) :=
  ImplicationTransfer.singleton_470
spectrum_assert exact_470 complete

theorem exact_471 : Law471.spectrum = ({1}) :=
  ImplicationTransfer.singleton_471
spectrum_assert exact_471 complete

theorem exact_472 : Law472.spectrum = ({1}) :=
  ImplicationTransfer.singleton_472
spectrum_assert exact_472 complete

theorem exact_473 : Law473.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_473
spectrum_assert exact_473 complete

theorem exact_474 : Law474.spectrum = (positiveExcept {2, 4}) :=
  ImplicationTransfer.spectrum_474_eq_474 |>.trans Note.exact_474
spectrum_assert exact_474 complete

theorem exact_475 : Law475.spectrum = ({1}) :=
  ImplicationTransfer.singleton_475
spectrum_assert exact_475 complete

theorem exact_476 : Law476.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_476
spectrum_assert exact_476 complete

theorem exact_477 : Law477.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_477
spectrum_assert exact_477 complete

theorem exact_478 : Law478.spectrum = ({1}) :=
  ImplicationTransfer.singleton_478
spectrum_assert exact_478 complete

theorem exact_479 : Law479.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_479
spectrum_assert exact_479 complete

theorem exact_480 : Law480.spectrum = ({1}) :=
  ImplicationTransfer.singleton_480
spectrum_assert exact_480 complete

-- UNKNOWN exact spectrum (PDF representative E481).
theorem lower_481 : (({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law481.spectrum := by
  rw [ImplicationTransfer.spectrum_481_eq_481]
  exact Note.lower_481
spectrum_assert lower_481 proofAvailable

theorem upper_481 : Law481.spectrum ⊆ (positiveExcept {3, 6}) := by
  rw [ImplicationTransfer.spectrum_481_eq_481]
  exact Note.upper_481
spectrum_assert upper_481 proofAvailable

theorem exact_482 : Law482.spectrum = ({1}) :=
  ImplicationTransfer.singleton_482
spectrum_assert exact_482 complete

theorem exact_483 : Law483.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_483
spectrum_assert exact_483 complete

theorem exact_484 : Law484.spectrum = ({1}) :=
  ImplicationTransfer.singleton_484
spectrum_assert exact_484 complete

theorem exact_485 : Law485.spectrum = ({1}) :=
  ImplicationTransfer.singleton_485
spectrum_assert exact_485 complete

theorem exact_486 : Law486.spectrum = ({1}) :=
  ImplicationTransfer.singleton_486
spectrum_assert exact_486 complete

theorem exact_487 : Law487.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_487
spectrum_assert exact_487 complete

theorem exact_488 : Law488.spectrum = ({1}) :=
  ImplicationTransfer.singleton_488
spectrum_assert exact_488 complete

theorem exact_489 : Law489.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_489
spectrum_assert exact_489 complete

theorem exact_490 : Law490.spectrum = ({1}) :=
  ImplicationTransfer.singleton_490
spectrum_assert exact_490 complete

theorem exact_491 : Law491.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_491
spectrum_assert exact_491 complete

theorem exact_492 : Law492.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_492
spectrum_assert exact_492 complete

theorem exact_493 : Law493.spectrum = ({1}) :=
  ImplicationTransfer.singleton_493
spectrum_assert exact_493 complete

theorem exact_494 : Law494.spectrum = ({1}) :=
  ImplicationTransfer.singleton_494
spectrum_assert exact_494 complete

theorem exact_495 : Law495.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_495
spectrum_assert exact_495 complete

theorem exact_496 : Law496.spectrum = ({1}) :=
  ImplicationTransfer.singleton_496
spectrum_assert exact_496 complete

theorem exact_497 : Law497.spectrum = ({1}) :=
  ImplicationTransfer.singleton_497
spectrum_assert exact_497 complete

theorem exact_498 : Law498.spectrum = ({1}) :=
  ImplicationTransfer.singleton_498
spectrum_assert exact_498 complete

theorem exact_499 : Law499.spectrum = ({1}) :=
  ImplicationTransfer.singleton_499
spectrum_assert exact_499 complete

theorem exact_500 : Law500.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_500
spectrum_assert exact_500 complete

-- UNKNOWN exact spectrum (PDF representative E501).
theorem lower_501 : (({1, 4, 5, 8, 9} : Set ℕ)) ⊆ Law501.spectrum := by
  rw [ImplicationTransfer.spectrum_501_eq_501]
  exact Note.lower_501
spectrum_assert lower_501 complete

theorem upper_501 : Law501.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_501_eq_501]
  exact Note.upper_501
spectrum_assert upper_501 complete

theorem exact_502 : Law502.spectrum = ({1}) :=
  ImplicationTransfer.singleton_502
spectrum_assert exact_502 complete

theorem exact_503 : Law503.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_503
spectrum_assert exact_503 complete

theorem exact_504 : Law504.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_504
spectrum_assert exact_504 complete

theorem exact_505 : Law505.spectrum = ({1}) :=
  ImplicationTransfer.singleton_505
spectrum_assert exact_505 complete

theorem exact_506 : Law506.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_506
spectrum_assert exact_506 complete

theorem exact_507 : Law507.spectrum = ({1}) :=
  ImplicationTransfer.singleton_507
spectrum_assert exact_507 complete

theorem exact_508 : Law508.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_508
spectrum_assert exact_508 complete

theorem exact_509 : Law509.spectrum = ({1}) :=
  ImplicationTransfer.singleton_509
spectrum_assert exact_509 complete

theorem exact_510 : Law510.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_510
spectrum_assert exact_510 complete

theorem exact_511 : Law511.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_511
spectrum_assert exact_511 complete

theorem exact_512 : Law512.spectrum = ({1}) :=
  ImplicationTransfer.singleton_512
spectrum_assert exact_512 complete

theorem exact_513 : Law513.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_513
spectrum_assert exact_513 complete

theorem exact_514 : Law514.spectrum = ({1}) :=
  ImplicationTransfer.singleton_514
spectrum_assert exact_514 complete

theorem exact_515 : Law515.spectrum = ({1}) :=
  ImplicationTransfer.singleton_515
spectrum_assert exact_515 complete

theorem exact_516 : Law516.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_516
spectrum_assert exact_516 complete

theorem exact_517 : Law517.spectrum = ({1}) :=
  ImplicationTransfer.singleton_517
spectrum_assert exact_517 complete

theorem exact_518 : Law518.spectrum = ({1}) :=
  ImplicationTransfer.singleton_518
spectrum_assert exact_518 complete

theorem exact_519 : Law519.spectrum = ({1}) :=
  ImplicationTransfer.singleton_519
spectrum_assert exact_519 complete

theorem exact_520 : Law520.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_520
spectrum_assert exact_520 complete

theorem exact_521 : Law521.spectrum = ({1}) :=
  ImplicationTransfer.singleton_521
spectrum_assert exact_521 complete

theorem exact_522 : Law522.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_522
spectrum_assert exact_522 complete

theorem exact_523 : Law523.spectrum = ({1}) :=
  ImplicationTransfer.singleton_523
spectrum_assert exact_523 complete

theorem exact_524 : Law524.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_524
spectrum_assert exact_524 complete

theorem exact_525 : Law525.spectrum = ({1}) :=
  ImplicationTransfer.singleton_525
spectrum_assert exact_525 complete

theorem exact_526 : Law526.spectrum = ({1}) :=
  ImplicationTransfer.singleton_526
spectrum_assert exact_526 complete

theorem exact_527 : Law527.spectrum = ({1}) :=
  ImplicationTransfer.singleton_527
spectrum_assert exact_527 complete

theorem exact_528 : Law528.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_528
spectrum_assert exact_528 complete

theorem exact_529 : Law529.spectrum = ({1}) :=
  ImplicationTransfer.singleton_529
spectrum_assert exact_529 complete

theorem exact_530 : Law530.spectrum = ({1}) :=
  ImplicationTransfer.singleton_530
spectrum_assert exact_530 complete

theorem exact_531 : Law531.spectrum = ({1}) :=
  ImplicationTransfer.singleton_531
spectrum_assert exact_531 complete

theorem exact_532 : Law532.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_532
spectrum_assert exact_532 complete

theorem exact_533 : Law533.spectrum = ({1}) :=
  ImplicationTransfer.singleton_533
spectrum_assert exact_533 complete

theorem exact_534 : Law534.spectrum = ({1}) :=
  ImplicationTransfer.singleton_534
spectrum_assert exact_534 complete

theorem exact_535 : Law535.spectrum = ({1}) :=
  ImplicationTransfer.singleton_535
spectrum_assert exact_535 complete

theorem exact_536 : Law536.spectrum = ({1}) :=
  ImplicationTransfer.singleton_536
spectrum_assert exact_536 complete

theorem exact_537 : Law537.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_537
spectrum_assert exact_537 complete

theorem exact_538 : Law538.spectrum = ({1}) :=
  ImplicationTransfer.singleton_538
spectrum_assert exact_538 complete

theorem exact_539 : Law539.spectrum = ({1}) :=
  ImplicationTransfer.singleton_539
spectrum_assert exact_539 complete

theorem exact_540 : Law540.spectrum = ({1}) :=
  ImplicationTransfer.singleton_540
spectrum_assert exact_540 complete

theorem exact_541 : Law541.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_541
spectrum_assert exact_541 complete

theorem exact_542 : Law542.spectrum = ({1}) :=
  ImplicationTransfer.singleton_542
spectrum_assert exact_542 complete

theorem exact_543 : Law543.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_543
spectrum_assert exact_543 complete

theorem exact_544 : Law544.spectrum = ({1}) :=
  ImplicationTransfer.singleton_544
spectrum_assert exact_544 complete

theorem exact_545 : Law545.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_545
spectrum_assert exact_545 complete

theorem exact_546 : Law546.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_546_eq_546 |>.trans Note.exact_546
spectrum_assert exact_546 complete

theorem exact_547 : Law547.spectrum = ({1}) :=
  ImplicationTransfer.singleton_547
spectrum_assert exact_547 complete

theorem exact_548 : Law548.spectrum = ({1}) :=
  ImplicationTransfer.singleton_548
spectrum_assert exact_548 complete

theorem exact_549 : Law549.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_549
spectrum_assert exact_549 complete

theorem exact_550 : Law550.spectrum = ({1}) :=
  ImplicationTransfer.singleton_550
spectrum_assert exact_550 complete

theorem exact_551 : Law551.spectrum = ({1}) :=
  ImplicationTransfer.singleton_551
spectrum_assert exact_551 complete

theorem exact_552 : Law552.spectrum = ({1}) :=
  ImplicationTransfer.singleton_552
spectrum_assert exact_552 complete

theorem exact_553 : Law553.spectrum = ({1}) :=
  ImplicationTransfer.singleton_553
spectrum_assert exact_553 complete

theorem exact_554 : Law554.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_554
spectrum_assert exact_554 complete

theorem exact_555 : Law555.spectrum = ({1}) :=
  ImplicationTransfer.singleton_555
spectrum_assert exact_555 complete

theorem exact_556 : Law556.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_556_eq_556 |>.trans Note.exact_556
spectrum_assert exact_556 complete

theorem exact_557 : Law557.spectrum = ({1}) :=
  ImplicationTransfer.singleton_557
spectrum_assert exact_557 complete

theorem exact_558 : Law558.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_558
spectrum_assert exact_558 complete

theorem exact_559 : Law559.spectrum = ({1}) :=
  ImplicationTransfer.singleton_559
spectrum_assert exact_559 complete

theorem exact_560 : Law560.spectrum = ({1}) :=
  ImplicationTransfer.singleton_560
spectrum_assert exact_560 complete

theorem exact_561 : Law561.spectrum = ({1}) :=
  ImplicationTransfer.singleton_561
spectrum_assert exact_561 complete

theorem exact_562 : Law562.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_562
spectrum_assert exact_562 complete

theorem exact_563 : Law563.spectrum = ({1}) :=
  ImplicationTransfer.singleton_563
spectrum_assert exact_563 complete

theorem exact_564 : Law564.spectrum = ({1}) :=
  ImplicationTransfer.singleton_564
spectrum_assert exact_564 complete

theorem exact_565 : Law565.spectrum = ({1}) :=
  ImplicationTransfer.singleton_565
spectrum_assert exact_565 complete

theorem exact_566 : Law566.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_566
spectrum_assert exact_566 complete

theorem exact_567 : Law567.spectrum = ({1}) :=
  ImplicationTransfer.singleton_567
spectrum_assert exact_567 complete

theorem exact_568 : Law568.spectrum = ({1}) :=
  ImplicationTransfer.singleton_568
spectrum_assert exact_568 complete

theorem exact_569 : Law569.spectrum = ({1}) :=
  ImplicationTransfer.singleton_569
spectrum_assert exact_569 complete

theorem exact_570 : Law570.spectrum = ({1}) :=
  ImplicationTransfer.singleton_570
spectrum_assert exact_570 complete

theorem exact_571 : Law571.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_571
spectrum_assert exact_571 complete

theorem exact_572 : Law572.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_572
spectrum_assert exact_572 complete

theorem exact_573 : Law573.spectrum = ({1}) :=
  ImplicationTransfer.singleton_573
spectrum_assert exact_573 complete

theorem exact_574 : Law574.spectrum = ({1}) :=
  ImplicationTransfer.singleton_574
spectrum_assert exact_574 complete

theorem exact_575 : Law575.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_575
spectrum_assert exact_575 complete

theorem exact_576 : Law576.spectrum = ({1}) :=
  ImplicationTransfer.singleton_576
spectrum_assert exact_576 complete

theorem exact_577 : Law577.spectrum = ({1}) :=
  ImplicationTransfer.singleton_577
spectrum_assert exact_577 complete

theorem exact_578 : Law578.spectrum = ({1}) :=
  ImplicationTransfer.singleton_578
spectrum_assert exact_578 complete

theorem exact_579 : Law579.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_579
spectrum_assert exact_579 complete

theorem exact_580 : Law580.spectrum = ({1}) :=
  ImplicationTransfer.singleton_580
spectrum_assert exact_580 complete

theorem exact_581 : Law581.spectrum = ({1}) :=
  ImplicationTransfer.singleton_581
spectrum_assert exact_581 complete

theorem exact_582 : Law582.spectrum = ({1}) :=
  ImplicationTransfer.singleton_582
spectrum_assert exact_582 complete

theorem exact_583 : Law583.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_583
spectrum_assert exact_583 complete

theorem exact_584 : Law584.spectrum = ({1}) :=
  ImplicationTransfer.singleton_584
spectrum_assert exact_584 complete

theorem exact_585 : Law585.spectrum = ({1}) :=
  ImplicationTransfer.singleton_585
spectrum_assert exact_585 complete

theorem exact_586 : Law586.spectrum = ({1}) :=
  ImplicationTransfer.singleton_586
spectrum_assert exact_586 complete

theorem exact_587 : Law587.spectrum = ({1}) :=
  ImplicationTransfer.singleton_587
spectrum_assert exact_587 complete

theorem exact_588 : Law588.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_588
spectrum_assert exact_588 complete

theorem exact_589 : Law589.spectrum = ({1}) :=
  ImplicationTransfer.singleton_589
spectrum_assert exact_589 complete

theorem exact_590 : Law590.spectrum = ({1}) :=
  ImplicationTransfer.singleton_590
spectrum_assert exact_590 complete

theorem exact_591 : Law591.spectrum = ({1}) :=
  ImplicationTransfer.singleton_591
spectrum_assert exact_591 complete

theorem exact_592 : Law592.spectrum = ({1}) :=
  ImplicationTransfer.singleton_592
spectrum_assert exact_592 complete

theorem exact_593 : Law593.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_593
spectrum_assert exact_593 complete

theorem exact_594 : Law594.spectrum = ({1}) :=
  ImplicationTransfer.singleton_594
spectrum_assert exact_594 complete

theorem exact_595 : Law595.spectrum = ({1}) :=
  ImplicationTransfer.singleton_595
spectrum_assert exact_595 complete

theorem exact_596 : Law596.spectrum = ({1}) :=
  ImplicationTransfer.singleton_596
spectrum_assert exact_596 complete

theorem exact_597 : Law597.spectrum = ({1}) :=
  ImplicationTransfer.singleton_597
spectrum_assert exact_597 complete

theorem exact_598 : Law598.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_598
spectrum_assert exact_598 complete

theorem exact_599 : Law599.spectrum = ({1}) :=
  ImplicationTransfer.singleton_599
spectrum_assert exact_599 complete

theorem exact_600 : Law600.spectrum = ({1}) :=
  ImplicationTransfer.singleton_600
spectrum_assert exact_600 complete

theorem exact_601 : Law601.spectrum = ({1}) :=
  ImplicationTransfer.singleton_601
spectrum_assert exact_601 complete

theorem exact_602 : Law602.spectrum = ({1}) :=
  ImplicationTransfer.singleton_602
spectrum_assert exact_602 complete

theorem exact_603 : Law603.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_603
spectrum_assert exact_603 complete

theorem exact_604 : Law604.spectrum = ({1}) :=
  ImplicationTransfer.singleton_604
spectrum_assert exact_604 complete

theorem exact_605 : Law605.spectrum = ({1}) :=
  ImplicationTransfer.singleton_605
spectrum_assert exact_605 complete

theorem exact_606 : Law606.spectrum = ({1}) :=
  ImplicationTransfer.singleton_606
spectrum_assert exact_606 complete

theorem exact_607 : Law607.spectrum = ({1}) :=
  ImplicationTransfer.singleton_607
spectrum_assert exact_607 complete

theorem exact_608 : Law608.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_608
spectrum_assert exact_608 complete

theorem exact_609 : Law609.spectrum = ({1}) :=
  ImplicationTransfer.singleton_609
spectrum_assert exact_609 complete

theorem exact_610 : Law610.spectrum = ({1}) :=
  ImplicationTransfer.singleton_610
spectrum_assert exact_610 complete

theorem exact_611 : Law611.spectrum = ({1}) :=
  ImplicationTransfer.singleton_611
spectrum_assert exact_611 complete

theorem exact_612 : Law612.spectrum = ({1}) :=
  ImplicationTransfer.singleton_612
spectrum_assert exact_612 complete

theorem exact_613 : Law613.spectrum = ({1}) :=
  ImplicationTransfer.singleton_613
spectrum_assert exact_613 complete

theorem exact_614 : Law614.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_614
spectrum_assert exact_614 complete

theorem exact_615 : Law615.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_615
spectrum_assert exact_615 complete

theorem exact_616 : Law616.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_616
spectrum_assert exact_616 complete

theorem exact_617 : Law617.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_617
spectrum_assert exact_617 complete

theorem exact_618 : Law618.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_618
spectrum_assert exact_618 complete

theorem exact_619 : Law619.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_619
spectrum_assert exact_619 complete

theorem exact_620 : Law620.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_620
spectrum_assert exact_620 complete

theorem exact_621 : Law621.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_621
spectrum_assert exact_621 complete

theorem exact_622 : Law622.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_622
spectrum_assert exact_622 complete

theorem exact_623 : Law623.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_623
spectrum_assert exact_623 complete

theorem exact_624 : Law624.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_624
spectrum_assert exact_624 complete

theorem exact_625 : Law625.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_625
spectrum_assert exact_625 complete

theorem exact_626 : Law626.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_626
spectrum_assert exact_626 complete

theorem exact_627 : Law627.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_627
spectrum_assert exact_627 complete

theorem exact_628 : Law628.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_628
spectrum_assert exact_628 complete

theorem exact_629 : Law629.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_629
spectrum_assert exact_629 complete

theorem exact_630 : Law630.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_630
spectrum_assert exact_630 complete

theorem exact_631 : Law631.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_631
spectrum_assert exact_631 complete

theorem exact_632 : Law632.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_632
spectrum_assert exact_632 complete

theorem exact_633 : Law633.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_633
spectrum_assert exact_633 complete

theorem exact_634 : Law634.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_634
spectrum_assert exact_634 complete

theorem exact_635 : Law635.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_635
spectrum_assert exact_635 complete

theorem exact_636 : Law636.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_636
spectrum_assert exact_636 complete

theorem exact_637 : Law637.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_637
spectrum_assert exact_637 complete

theorem exact_638 : Law638.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_638
spectrum_assert exact_638 complete

theorem exact_639 : Law639.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_639
spectrum_assert exact_639 complete

theorem exact_640 : Law640.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_640
spectrum_assert exact_640 complete

theorem exact_641 : Law641.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_641
spectrum_assert exact_641 complete

theorem exact_642 : Law642.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_642
spectrum_assert exact_642 complete

theorem exact_643 : Law643.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_643
spectrum_assert exact_643 complete

theorem exact_644 : Law644.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_644
spectrum_assert exact_644 complete

theorem exact_645 : Law645.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_645
spectrum_assert exact_645 complete

theorem exact_646 : Law646.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_646
spectrum_assert exact_646 complete

theorem exact_647 : Law647.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_647
spectrum_assert exact_647 complete

theorem exact_648 : Law648.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_648
spectrum_assert exact_648 complete

theorem exact_649 : Law649.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_649
spectrum_assert exact_649 complete

theorem exact_650 : Law650.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_650
spectrum_assert exact_650 complete

theorem exact_651 : Law651.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_651
spectrum_assert exact_651 complete

theorem exact_652 : Law652.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_652
spectrum_assert exact_652 complete

theorem exact_653 : Law653.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_653
spectrum_assert exact_653 complete

theorem exact_654 : Law654.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_654
spectrum_assert exact_654 complete

theorem exact_655 : Law655.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_655
spectrum_assert exact_655 complete

theorem exact_656 : Law656.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_656
spectrum_assert exact_656 complete

theorem exact_657 : Law657.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_657
spectrum_assert exact_657 complete

theorem exact_658 : Law658.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_658
spectrum_assert exact_658 complete

theorem exact_659 : Law659.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_659
spectrum_assert exact_659 complete

theorem exact_660 : Law660.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_660
spectrum_assert exact_660 complete

theorem exact_661 : Law661.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_661
spectrum_assert exact_661 complete

theorem exact_662 : Law662.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_662
spectrum_assert exact_662 complete

theorem exact_663 : Law663.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_663
spectrum_assert exact_663 complete

theorem exact_664 : Law664.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_664
spectrum_assert exact_664 complete

theorem exact_665 : Law665.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_665
spectrum_assert exact_665 complete

theorem exact_666 : Law666.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_666
spectrum_assert exact_666 complete

-- UNKNOWN exact spectrum (PDF representative E667).
theorem lower_667 : (({1, 7, 9} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law667.spectrum := by
  rw [ImplicationTransfer.spectrum_667_eq_667]
  exact Note.lower_667
spectrum_assert lower_667 proofAvailable

theorem upper_667 : Law667.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_667_eq_667]
  exact Note.upper_667
spectrum_assert upper_667 complete

theorem exact_668 : Law668.spectrum = ({1}) :=
  ImplicationTransfer.singleton_668
spectrum_assert exact_668 complete

theorem exact_669 : Law669.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_669
spectrum_assert exact_669 complete

-- UNKNOWN exact spectrum (PDF representative E670).
theorem lower_670 : (({1, 4, 5} : Set ℕ)) ⊆ Law670.spectrum := by
  rw [ImplicationTransfer.spectrum_670_eq_670]
  exact Note.lower_670
spectrum_assert lower_670 complete

theorem upper_670 : Law670.spectrum ⊆ (positiveExcept {2, 3, 6, 7}) := by
  rw [ImplicationTransfer.spectrum_670_eq_670]
  exact Note.upper_670
spectrum_assert upper_670 proofAvailable

theorem cofinite_670 : CofiniteSpectrum Law670 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_670_eq_670]
  exact Note.cofinite_670
spectrum_assert cofinite_670 noteGap

theorem exact_671 : Law671.spectrum = ({1}) :=
  ImplicationTransfer.singleton_671
spectrum_assert exact_671 complete

theorem exact_672 : Law672.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_672
spectrum_assert exact_672 complete

theorem exact_673 : Law673.spectrum = ({1}) :=
  ImplicationTransfer.singleton_673
spectrum_assert exact_673 complete

theorem exact_674 : Law674.spectrum = ({1}) :=
  ImplicationTransfer.singleton_674
spectrum_assert exact_674 complete

theorem exact_675 : Law675.spectrum = ({1}) :=
  ImplicationTransfer.singleton_675
spectrum_assert exact_675 complete

theorem exact_676 : Law676.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_676
spectrum_assert exact_676 complete

-- UNKNOWN exact spectrum (PDF representative E677).
theorem lower_677 : (({1, 5, 7, 9, 11, 13, 16} : Set ℕ)) ⊆ Law677.spectrum := by
  rw [ImplicationTransfer.spectrum_677_eq_677]
  exact Note.lower_677
spectrum_assert lower_677 complete

theorem upper_677 : Law677.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_677_eq_677]
  exact Note.upper_677
spectrum_assert upper_677 complete

theorem cofinite_677 : CofiniteSpectrum Law677 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_677_eq_677]
  exact Note.cofinite_677
spectrum_assert cofinite_677 noteGap

theorem exact_678 : Law678.spectrum = ({1}) :=
  ImplicationTransfer.singleton_678
spectrum_assert exact_678 complete

theorem exact_679 : Law679.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_679
spectrum_assert exact_679 complete

theorem exact_680 : Law680.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_680
spectrum_assert exact_680 complete

theorem exact_681 : Law681.spectrum = ({1}) :=
  ImplicationTransfer.singleton_681
spectrum_assert exact_681 complete

theorem exact_682 : Law682.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_682
spectrum_assert exact_682 complete

theorem exact_683 : Law683.spectrum = ({1}) :=
  ImplicationTransfer.singleton_683
spectrum_assert exact_683 complete

theorem exact_684 : Law684.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_684
spectrum_assert exact_684 complete

theorem exact_685 : Law685.spectrum = ({1}) :=
  ImplicationTransfer.singleton_685
spectrum_assert exact_685 complete

theorem exact_686 : Law686.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_686
spectrum_assert exact_686 complete

theorem exact_687 : Law687.spectrum = ({1}) :=
  ImplicationTransfer.singleton_687
spectrum_assert exact_687 complete

theorem exact_688 : Law688.spectrum = ({1}) :=
  ImplicationTransfer.singleton_688
spectrum_assert exact_688 complete

theorem exact_689 : Law689.spectrum = ({1}) :=
  ImplicationTransfer.singleton_689
spectrum_assert exact_689 complete

theorem exact_690 : Law690.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_690
spectrum_assert exact_690 complete

theorem exact_691 : Law691.spectrum = ({1}) :=
  ImplicationTransfer.singleton_691
spectrum_assert exact_691 complete

theorem exact_692 : Law692.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_692
spectrum_assert exact_692 complete

theorem exact_693 : Law693.spectrum = ({1}) :=
  ImplicationTransfer.singleton_693
spectrum_assert exact_693 complete

theorem exact_694 : Law694.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_694
spectrum_assert exact_694 complete

theorem exact_695 : Law695.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_695_eq_695 |>.trans Note.exact_695
spectrum_assert exact_695 complete

theorem exact_696 : Law696.spectrum = ({1}) :=
  ImplicationTransfer.singleton_696
spectrum_assert exact_696 complete

theorem exact_697 : Law697.spectrum = ({1}) :=
  ImplicationTransfer.singleton_697
spectrum_assert exact_697 complete

theorem exact_698 : Law698.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_698
spectrum_assert exact_698 complete

theorem exact_699 : Law699.spectrum = ({1}) :=
  ImplicationTransfer.singleton_699
spectrum_assert exact_699 complete

theorem exact_700 : Law700.spectrum = ({1}) :=
  ImplicationTransfer.singleton_700
spectrum_assert exact_700 complete

theorem exact_701 : Law701.spectrum = ({1}) :=
  ImplicationTransfer.singleton_701
spectrum_assert exact_701 complete

theorem exact_702 : Law702.spectrum = ({1}) :=
  ImplicationTransfer.singleton_702
spectrum_assert exact_702 complete

theorem exact_703 : Law703.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_703
spectrum_assert exact_703 complete

-- UNKNOWN exact spectrum (PDF representative E704).
theorem lower_704 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law704.spectrum := by
  rw [ImplicationTransfer.spectrum_704_eq_704]
  exact Note.lower_704
spectrum_assert lower_704 complete

theorem upper_704 : Law704.spectrum ⊆ (positiveExcept {2, 3, 4, 6, 9}) := by
  rw [ImplicationTransfer.spectrum_704_eq_704]
  exact Note.upper_704
spectrum_assert upper_704 proofAvailable

theorem cofinite_704 : CofiniteSpectrum Law704 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_704_eq_704]
  exact Note.cofinite_704
spectrum_assert cofinite_704 proofAvailable

theorem exact_705 : Law705.spectrum = ({1}) :=
  ImplicationTransfer.singleton_705
spectrum_assert exact_705 complete

theorem exact_706 : Law706.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_706
spectrum_assert exact_706 complete

theorem exact_707 : Law707.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_707
spectrum_assert exact_707 complete

theorem exact_708 : Law708.spectrum = ({1}) :=
  ImplicationTransfer.singleton_708
spectrum_assert exact_708 complete

theorem exact_709 : Law709.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_709
spectrum_assert exact_709 complete

theorem exact_710 : Law710.spectrum = ({1}) :=
  ImplicationTransfer.singleton_710
spectrum_assert exact_710 complete

theorem exact_711 : Law711.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_711
spectrum_assert exact_711 complete

theorem exact_712 : Law712.spectrum = ({1}) :=
  ImplicationTransfer.singleton_712
spectrum_assert exact_712 complete

theorem exact_713 : Law713.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_713
spectrum_assert exact_713 complete

theorem exact_714 : Law714.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_714
spectrum_assert exact_714 complete

theorem exact_715 : Law715.spectrum = ({1}) :=
  ImplicationTransfer.singleton_715
spectrum_assert exact_715 complete

theorem exact_716 : Law716.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_716
spectrum_assert exact_716 complete

theorem exact_717 : Law717.spectrum = ({1}) :=
  ImplicationTransfer.singleton_717
spectrum_assert exact_717 complete

theorem exact_718 : Law718.spectrum = ({1}) :=
  ImplicationTransfer.singleton_718
spectrum_assert exact_718 complete

theorem exact_719 : Law719.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_719
spectrum_assert exact_719 complete

theorem exact_720 : Law720.spectrum = ({1}) :=
  ImplicationTransfer.singleton_720
spectrum_assert exact_720 complete

theorem exact_721 : Law721.spectrum = ({1}) :=
  ImplicationTransfer.singleton_721
spectrum_assert exact_721 complete

theorem exact_722 : Law722.spectrum = ({1}) :=
  ImplicationTransfer.singleton_722
spectrum_assert exact_722 complete

theorem exact_723 : Law723.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_723
spectrum_assert exact_723 complete

theorem exact_724 : Law724.spectrum = ({1}) :=
  ImplicationTransfer.singleton_724
spectrum_assert exact_724 complete

theorem exact_725 : Law725.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_725
spectrum_assert exact_725 complete

theorem exact_726 : Law726.spectrum = ({1}) :=
  ImplicationTransfer.singleton_726
spectrum_assert exact_726 complete

theorem exact_727 : Law727.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_727
spectrum_assert exact_727 complete

theorem exact_728 : Law728.spectrum = ({1}) :=
  ImplicationTransfer.singleton_728
spectrum_assert exact_728 complete

theorem exact_729 : Law729.spectrum = ({1}) :=
  ImplicationTransfer.singleton_729
spectrum_assert exact_729 complete

theorem exact_730 : Law730.spectrum = ({1}) :=
  ImplicationTransfer.singleton_730
spectrum_assert exact_730 complete

theorem exact_731 : Law731.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_731
spectrum_assert exact_731 complete

theorem exact_732 : Law732.spectrum = ({1}) :=
  ImplicationTransfer.singleton_732
spectrum_assert exact_732 complete

theorem exact_733 : Law733.spectrum = ({1}) :=
  ImplicationTransfer.singleton_733
spectrum_assert exact_733 complete

theorem exact_734 : Law734.spectrum = ({1}) :=
  ImplicationTransfer.singleton_734
spectrum_assert exact_734 complete

theorem exact_735 : Law735.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_735
spectrum_assert exact_735 complete

theorem exact_736 : Law736.spectrum = ({1}) :=
  ImplicationTransfer.singleton_736
spectrum_assert exact_736 complete

theorem exact_737 : Law737.spectrum = ({1}) :=
  ImplicationTransfer.singleton_737
spectrum_assert exact_737 complete

theorem exact_738 : Law738.spectrum = ({1}) :=
  ImplicationTransfer.singleton_738
spectrum_assert exact_738 complete

theorem exact_739 : Law739.spectrum = ({1}) :=
  ImplicationTransfer.singleton_739
spectrum_assert exact_739 complete

theorem exact_740 : Law740.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_740
spectrum_assert exact_740 complete

theorem exact_741 : Law741.spectrum = ({1}) :=
  ImplicationTransfer.singleton_741
spectrum_assert exact_741 complete

theorem exact_742 : Law742.spectrum = ({1}) :=
  ImplicationTransfer.singleton_742
spectrum_assert exact_742 complete

theorem exact_743 : Law743.spectrum = ({1}) :=
  ImplicationTransfer.singleton_743
spectrum_assert exact_743 complete

theorem exact_744 : Law744.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_744
spectrum_assert exact_744 complete

theorem exact_745 : Law745.spectrum = ({1}) :=
  ImplicationTransfer.singleton_745
spectrum_assert exact_745 complete

theorem exact_746 : Law746.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_746
spectrum_assert exact_746 complete

theorem exact_747 : Law747.spectrum = ({1}) :=
  ImplicationTransfer.singleton_747
spectrum_assert exact_747 complete

theorem exact_748 : Law748.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_748
spectrum_assert exact_748 complete

theorem exact_749 : Law749.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_749_eq_556 |>.trans Note.exact_556
spectrum_assert exact_749 complete

theorem exact_750 : Law750.spectrum = ({1}) :=
  ImplicationTransfer.singleton_750
spectrum_assert exact_750 complete

theorem exact_751 : Law751.spectrum = ({1}) :=
  ImplicationTransfer.singleton_751
spectrum_assert exact_751 complete

theorem exact_752 : Law752.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_752
spectrum_assert exact_752 complete

theorem exact_753 : Law753.spectrum = ({1}) :=
  ImplicationTransfer.singleton_753
spectrum_assert exact_753 complete

theorem exact_754 : Law754.spectrum = ({1}) :=
  ImplicationTransfer.singleton_754
spectrum_assert exact_754 complete

theorem exact_755 : Law755.spectrum = ({1}) :=
  ImplicationTransfer.singleton_755
spectrum_assert exact_755 complete

theorem exact_756 : Law756.spectrum = ({1}) :=
  ImplicationTransfer.singleton_756
spectrum_assert exact_756 complete

theorem exact_757 : Law757.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_757
spectrum_assert exact_757 complete

theorem exact_758 : Law758.spectrum = ({1}) :=
  ImplicationTransfer.singleton_758
spectrum_assert exact_758 complete

theorem exact_759 : Law759.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_759
spectrum_assert exact_759 complete

theorem exact_760 : Law760.spectrum = ({1}) :=
  ImplicationTransfer.singleton_760
spectrum_assert exact_760 complete

theorem exact_761 : Law761.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_761
spectrum_assert exact_761 complete

theorem exact_762 : Law762.spectrum = ({1}) :=
  ImplicationTransfer.singleton_762
spectrum_assert exact_762 complete

theorem exact_763 : Law763.spectrum = ({1}) :=
  ImplicationTransfer.singleton_763
spectrum_assert exact_763 complete

theorem exact_764 : Law764.spectrum = ({1}) :=
  ImplicationTransfer.singleton_764
spectrum_assert exact_764 complete

theorem exact_765 : Law765.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_765
spectrum_assert exact_765 complete

theorem exact_766 : Law766.spectrum = ({1}) :=
  ImplicationTransfer.singleton_766
spectrum_assert exact_766 complete

theorem exact_767 : Law767.spectrum = ({1}) :=
  ImplicationTransfer.singleton_767
spectrum_assert exact_767 complete

theorem exact_768 : Law768.spectrum = ({1}) :=
  ImplicationTransfer.singleton_768
spectrum_assert exact_768 complete

theorem exact_769 : Law769.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_769
spectrum_assert exact_769 complete

theorem exact_770 : Law770.spectrum = ({1}) :=
  ImplicationTransfer.singleton_770
spectrum_assert exact_770 complete

theorem exact_771 : Law771.spectrum = ({1}) :=
  ImplicationTransfer.singleton_771
spectrum_assert exact_771 complete

theorem exact_772 : Law772.spectrum = ({1}) :=
  ImplicationTransfer.singleton_772
spectrum_assert exact_772 complete

theorem exact_773 : Law773.spectrum = ({1}) :=
  ImplicationTransfer.singleton_773
spectrum_assert exact_773 complete

theorem exact_774 : Law774.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_774
spectrum_assert exact_774 complete

theorem exact_775 : Law775.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_775_eq_556 |>.trans Note.exact_556
spectrum_assert exact_775 complete

theorem exact_776 : Law776.spectrum = ({1}) :=
  ImplicationTransfer.singleton_776
spectrum_assert exact_776 complete

theorem exact_777 : Law777.spectrum = ({1}) :=
  ImplicationTransfer.singleton_777
spectrum_assert exact_777 complete

theorem exact_778 : Law778.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_778
spectrum_assert exact_778 complete

theorem exact_779 : Law779.spectrum = ({1}) :=
  ImplicationTransfer.singleton_779
spectrum_assert exact_779 complete

theorem exact_780 : Law780.spectrum = ({1}) :=
  ImplicationTransfer.singleton_780
spectrum_assert exact_780 complete

theorem exact_781 : Law781.spectrum = ({1}) :=
  ImplicationTransfer.singleton_781
spectrum_assert exact_781 complete

theorem exact_782 : Law782.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_782
spectrum_assert exact_782 complete

theorem exact_783 : Law783.spectrum = ({1}) :=
  ImplicationTransfer.singleton_783
spectrum_assert exact_783 complete

theorem exact_784 : Law784.spectrum = ({1}) :=
  ImplicationTransfer.singleton_784
spectrum_assert exact_784 complete

theorem exact_785 : Law785.spectrum = ({1}) :=
  ImplicationTransfer.singleton_785
spectrum_assert exact_785 complete

theorem exact_786 : Law786.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_786
spectrum_assert exact_786 complete

theorem exact_787 : Law787.spectrum = ({1}) :=
  ImplicationTransfer.singleton_787
spectrum_assert exact_787 complete

theorem exact_788 : Law788.spectrum = ({1}) :=
  ImplicationTransfer.singleton_788
spectrum_assert exact_788 complete

theorem exact_789 : Law789.spectrum = ({1}) :=
  ImplicationTransfer.singleton_789
spectrum_assert exact_789 complete

theorem exact_790 : Law790.spectrum = ({1}) :=
  ImplicationTransfer.singleton_790
spectrum_assert exact_790 complete

theorem exact_791 : Law791.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_791
spectrum_assert exact_791 complete

theorem exact_792 : Law792.spectrum = ({1}) :=
  ImplicationTransfer.singleton_792
spectrum_assert exact_792 complete

theorem exact_793 : Law793.spectrum = ({1}) :=
  ImplicationTransfer.singleton_793
spectrum_assert exact_793 complete

theorem exact_794 : Law794.spectrum = ({1}) :=
  ImplicationTransfer.singleton_794
spectrum_assert exact_794 complete

theorem exact_795 : Law795.spectrum = ({1}) :=
  ImplicationTransfer.singleton_795
spectrum_assert exact_795 complete

theorem exact_796 : Law796.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_796
spectrum_assert exact_796 complete

theorem exact_797 : Law797.spectrum = ({1}) :=
  ImplicationTransfer.singleton_797
spectrum_assert exact_797 complete

theorem exact_798 : Law798.spectrum = ({1}) :=
  ImplicationTransfer.singleton_798
spectrum_assert exact_798 complete

theorem exact_799 : Law799.spectrum = ({1}) :=
  ImplicationTransfer.singleton_799
spectrum_assert exact_799 complete

theorem exact_800 : Law800.spectrum = ({1}) :=
  ImplicationTransfer.singleton_800
spectrum_assert exact_800 complete

theorem exact_801 : Law801.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_801
spectrum_assert exact_801 complete

theorem exact_802 : Law802.spectrum = ({1}) :=
  ImplicationTransfer.singleton_802
spectrum_assert exact_802 complete

theorem exact_803 : Law803.spectrum = ({1}) :=
  ImplicationTransfer.singleton_803
spectrum_assert exact_803 complete

theorem exact_804 : Law804.spectrum = ({1}) :=
  ImplicationTransfer.singleton_804
spectrum_assert exact_804 complete

theorem exact_805 : Law805.spectrum = ({1}) :=
  ImplicationTransfer.singleton_805
spectrum_assert exact_805 complete

theorem exact_806 : Law806.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_806
spectrum_assert exact_806 complete

theorem exact_807 : Law807.spectrum = ({1}) :=
  ImplicationTransfer.singleton_807
spectrum_assert exact_807 complete

theorem exact_808 : Law808.spectrum = ({1}) :=
  ImplicationTransfer.singleton_808
spectrum_assert exact_808 complete

theorem exact_809 : Law809.spectrum = ({1}) :=
  ImplicationTransfer.singleton_809
spectrum_assert exact_809 complete

theorem exact_810 : Law810.spectrum = ({1}) :=
  ImplicationTransfer.singleton_810
spectrum_assert exact_810 complete

theorem exact_811 : Law811.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_811
spectrum_assert exact_811 complete

theorem exact_812 : Law812.spectrum = ({1}) :=
  ImplicationTransfer.singleton_812
spectrum_assert exact_812 complete

theorem exact_813 : Law813.spectrum = ({1}) :=
  ImplicationTransfer.singleton_813
spectrum_assert exact_813 complete

theorem exact_814 : Law814.spectrum = ({1}) :=
  ImplicationTransfer.singleton_814
spectrum_assert exact_814 complete

theorem exact_815 : Law815.spectrum = ({1}) :=
  ImplicationTransfer.singleton_815
spectrum_assert exact_815 complete

theorem exact_816 : Law816.spectrum = ({1}) :=
  ImplicationTransfer.singleton_816
spectrum_assert exact_816 complete

theorem exact_817 : Law817.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_817
spectrum_assert exact_817 complete

theorem exact_818 : Law818.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_818
spectrum_assert exact_818 complete

theorem exact_819 : Law819.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_819
spectrum_assert exact_819 complete

theorem exact_820 : Law820.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_820
spectrum_assert exact_820 complete

theorem exact_821 : Law821.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_821
spectrum_assert exact_821 complete

theorem exact_822 : Law822.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_822
spectrum_assert exact_822 complete

theorem exact_823 : Law823.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_823
spectrum_assert exact_823 complete

theorem exact_824 : Law824.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_824
spectrum_assert exact_824 complete

theorem exact_825 : Law825.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_825
spectrum_assert exact_825 complete

theorem exact_826 : Law826.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_826
spectrum_assert exact_826 complete

theorem exact_827 : Law827.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_827
spectrum_assert exact_827 complete

theorem exact_828 : Law828.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_828
spectrum_assert exact_828 complete

theorem exact_829 : Law829.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_829
spectrum_assert exact_829 complete

theorem exact_830 : Law830.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_830
spectrum_assert exact_830 complete

theorem exact_831 : Law831.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_831
spectrum_assert exact_831 complete

theorem exact_832 : Law832.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_832
spectrum_assert exact_832 complete

theorem exact_833 : Law833.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_833
spectrum_assert exact_833 complete

theorem exact_834 : Law834.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_834
spectrum_assert exact_834 complete

theorem exact_835 : Law835.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_835
spectrum_assert exact_835 complete

theorem exact_836 : Law836.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_836
spectrum_assert exact_836 complete

theorem exact_837 : Law837.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_837
spectrum_assert exact_837 complete

theorem exact_838 : Law838.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_838
spectrum_assert exact_838 complete

theorem exact_839 : Law839.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_839
spectrum_assert exact_839 complete

theorem exact_840 : Law840.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_840
spectrum_assert exact_840 complete

theorem exact_841 : Law841.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_841
spectrum_assert exact_841 complete

theorem exact_842 : Law842.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_842
spectrum_assert exact_842 complete

theorem exact_843 : Law843.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_843
spectrum_assert exact_843 complete

theorem exact_844 : Law844.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_844
spectrum_assert exact_844 complete

theorem exact_845 : Law845.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_845
spectrum_assert exact_845 complete

theorem exact_846 : Law846.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_846
spectrum_assert exact_846 complete

theorem exact_847 : Law847.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_847
spectrum_assert exact_847 complete

theorem exact_848 : Law848.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_848
spectrum_assert exact_848 complete

theorem exact_849 : Law849.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_849
spectrum_assert exact_849 complete

theorem exact_850 : Law850.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_850
spectrum_assert exact_850 complete

theorem exact_851 : Law851.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_851
spectrum_assert exact_851 complete

theorem exact_852 : Law852.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_852
spectrum_assert exact_852 complete

theorem exact_853 : Law853.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_853
spectrum_assert exact_853 complete

theorem exact_854 : Law854.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_854
spectrum_assert exact_854 complete

theorem exact_855 : Law855.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_855
spectrum_assert exact_855 complete

theorem exact_856 : Law856.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_856
spectrum_assert exact_856 complete

theorem exact_857 : Law857.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_857
spectrum_assert exact_857 complete

theorem exact_858 : Law858.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_858
spectrum_assert exact_858 complete

theorem exact_859 : Law859.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_859
spectrum_assert exact_859 complete

theorem exact_860 : Law860.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_860
spectrum_assert exact_860 complete

theorem exact_861 : Law861.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_861
spectrum_assert exact_861 complete

theorem exact_862 : Law862.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_862
spectrum_assert exact_862 complete

theorem exact_863 : Law863.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_863
spectrum_assert exact_863 complete

theorem exact_864 : Law864.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_864
spectrum_assert exact_864 complete

theorem exact_865 : Law865.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_865
spectrum_assert exact_865 complete

theorem exact_866 : Law866.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_866
spectrum_assert exact_866 complete

theorem exact_867 : Law867.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_867
spectrum_assert exact_867 complete

theorem exact_868 : Law868.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_868
spectrum_assert exact_868 complete

theorem exact_869 : Law869.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_869
spectrum_assert exact_869 complete

theorem exact_870 : Law870.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_870
spectrum_assert exact_870 complete

theorem exact_871 : Law871.spectrum = ({1}) :=
  ImplicationTransfer.singleton_871
spectrum_assert exact_871 complete

theorem exact_872 : Law872.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_872
spectrum_assert exact_872 complete

-- UNKNOWN exact spectrum (PDF representative E873).
theorem lower_873 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law873.spectrum := by
  rw [ImplicationTransfer.spectrum_873_eq_873]
  exact Note.lower_873
spectrum_assert lower_873 proofAvailable

theorem upper_873 : Law873.spectrum ⊆ (positiveExcept {2, 6}) := by
  rw [ImplicationTransfer.spectrum_873_eq_873]
  exact Note.upper_873
spectrum_assert upper_873 proofAvailable

theorem exact_874 : Law874.spectrum = ({1}) :=
  ImplicationTransfer.singleton_874
spectrum_assert exact_874 complete

theorem exact_875 : Law875.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_875
spectrum_assert exact_875 complete

theorem exact_876 : Law876.spectrum = ({1}) :=
  ImplicationTransfer.singleton_876
spectrum_assert exact_876 complete

theorem exact_877 : Law877.spectrum = ({1}) :=
  ImplicationTransfer.singleton_877
spectrum_assert exact_877 complete

theorem exact_878 : Law878.spectrum = ({1}) :=
  ImplicationTransfer.singleton_878
spectrum_assert exact_878 complete

theorem exact_879 : Law879.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_879
spectrum_assert exact_879 complete

-- UNKNOWN exact spectrum (PDF representative E880).
theorem lower_880 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law880.spectrum := by
  rw [ImplicationTransfer.spectrum_880_eq_880]
  exact Note.lower_880
spectrum_assert lower_880 proofAvailable

theorem upper_880 : Law880.spectrum ⊆ (positiveExcept {2, 6}) := by
  rw [ImplicationTransfer.spectrum_880_eq_880]
  exact Note.upper_880
spectrum_assert upper_880 proofAvailable

theorem exact_881 : Law881.spectrum = ({1}) :=
  ImplicationTransfer.singleton_881
spectrum_assert exact_881 complete

theorem exact_882 : Law882.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_882
spectrum_assert exact_882 complete

-- UNKNOWN exact spectrum (PDF representative E883).
theorem lower_883 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law883.spectrum := by
  rw [ImplicationTransfer.spectrum_883_eq_883]
  exact Note.lower_883
spectrum_assert lower_883 proofAvailable

theorem upper_883 : Law883.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_883_eq_883]
  exact Note.upper_883
spectrum_assert upper_883 complete

theorem cofinite_883 : CofiniteSpectrum Law883 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_883_eq_883]
  exact Note.cofinite_883
spectrum_assert cofinite_883 proofAvailable

theorem exact_884 : Law884.spectrum = ({1}) :=
  ImplicationTransfer.singleton_884
spectrum_assert exact_884 complete

theorem exact_885 : Law885.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_885
spectrum_assert exact_885 complete

theorem exact_886 : Law886.spectrum = ({1}) :=
  ImplicationTransfer.singleton_886
spectrum_assert exact_886 complete

theorem exact_887 : Law887.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_887_eq_887 |>.trans Note.exact_887
spectrum_assert exact_887 complete

theorem exact_888 : Law888.spectrum = ({1}) :=
  ImplicationTransfer.singleton_888
spectrum_assert exact_888 complete

theorem exact_889 : Law889.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_889
spectrum_assert exact_889 complete

theorem exact_890 : Law890.spectrum = ({1}) :=
  ImplicationTransfer.singleton_890
spectrum_assert exact_890 complete

theorem exact_891 : Law891.spectrum = ({1}) :=
  ImplicationTransfer.singleton_891
spectrum_assert exact_891 complete

theorem exact_892 : Law892.spectrum = ({1}) :=
  ImplicationTransfer.singleton_892
spectrum_assert exact_892 complete

theorem exact_893 : Law893.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_893
spectrum_assert exact_893 complete

theorem exact_894 : Law894.spectrum = ({1}) :=
  ImplicationTransfer.singleton_894
spectrum_assert exact_894 complete

theorem exact_895 : Law895.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_895_eq_895 |>.trans Note.exact_895
spectrum_assert exact_895 proofAvailable

theorem exact_896 : Law896.spectrum = ({1}) :=
  ImplicationTransfer.singleton_896
spectrum_assert exact_896 complete

theorem exact_897 : Law897.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_897
spectrum_assert exact_897 complete

theorem exact_898 : Law898.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_898_eq_898 |>.trans Note.exact_898
spectrum_assert exact_898 noteGap

theorem exact_899 : Law899.spectrum = ({1}) :=
  ImplicationTransfer.singleton_899
spectrum_assert exact_899 complete

theorem exact_900 : Law900.spectrum = ({1}) :=
  ImplicationTransfer.singleton_900
spectrum_assert exact_900 complete

theorem exact_901 : Law901.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_901
spectrum_assert exact_901 complete

theorem exact_902 : Law902.spectrum = ({1}) :=
  ImplicationTransfer.singleton_902
spectrum_assert exact_902 complete

theorem exact_903 : Law903.spectrum = ({1}) :=
  ImplicationTransfer.singleton_903
spectrum_assert exact_903 complete

theorem exact_904 : Law904.spectrum = ({1}) :=
  ImplicationTransfer.singleton_904
spectrum_assert exact_904 complete

theorem exact_905 : Law905.spectrum = ({1}) :=
  ImplicationTransfer.singleton_905
spectrum_assert exact_905 complete

theorem exact_906 : Law906.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_906
spectrum_assert exact_906 complete

-- UNKNOWN exact spectrum (PDF representative E907).
theorem lower_907 : (({1, 3, 7, 9, 13} : Set ℕ)) ⊆ Law907.spectrum := by
  rw [ImplicationTransfer.spectrum_907_eq_907]
  exact Note.lower_907
spectrum_assert lower_907 complete

theorem upper_907 : Law907.spectrum ⊆ (positiveExcept {2, 4, 5, 6}) := by
  rw [ImplicationTransfer.spectrum_907_eq_907]
  exact Note.upper_907
spectrum_assert upper_907 proofAvailable

theorem exact_908 : Law908.spectrum = ({1}) :=
  ImplicationTransfer.singleton_908
spectrum_assert exact_908 complete

theorem exact_909 : Law909.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_909
spectrum_assert exact_909 complete

theorem exact_910 : Law910.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_910
spectrum_assert exact_910 complete

theorem exact_911 : Law911.spectrum = ({1}) :=
  ImplicationTransfer.singleton_911
spectrum_assert exact_911 complete

theorem exact_912 : Law912.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_912
spectrum_assert exact_912 complete

theorem exact_913 : Law913.spectrum = ({1}) :=
  ImplicationTransfer.singleton_913
spectrum_assert exact_913 complete

theorem exact_914 : Law914.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_914
spectrum_assert exact_914 complete

theorem exact_915 : Law915.spectrum = ({1}) :=
  ImplicationTransfer.singleton_915
spectrum_assert exact_915 complete

theorem exact_916 : Law916.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_916
spectrum_assert exact_916 complete

theorem exact_917 : Law917.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_917
spectrum_assert exact_917 complete

theorem exact_918 : Law918.spectrum = ({1}) :=
  ImplicationTransfer.singleton_918
spectrum_assert exact_918 complete

theorem exact_919 : Law919.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_919
spectrum_assert exact_919 complete

theorem exact_920 : Law920.spectrum = ({1}) :=
  ImplicationTransfer.singleton_920
spectrum_assert exact_920 complete

theorem exact_921 : Law921.spectrum = ({1}) :=
  ImplicationTransfer.singleton_921
spectrum_assert exact_921 complete

theorem exact_922 : Law922.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_922
spectrum_assert exact_922 complete

theorem exact_923 : Law923.spectrum = ({1}) :=
  ImplicationTransfer.singleton_923
spectrum_assert exact_923 complete

theorem exact_924 : Law924.spectrum = ({1}) :=
  ImplicationTransfer.singleton_924
spectrum_assert exact_924 complete

theorem exact_925 : Law925.spectrum = ({1}) :=
  ImplicationTransfer.singleton_925
spectrum_assert exact_925 complete

theorem exact_926 : Law926.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_926
spectrum_assert exact_926 complete

theorem exact_927 : Law927.spectrum = ({1}) :=
  ImplicationTransfer.singleton_927
spectrum_assert exact_927 complete

theorem exact_928 : Law928.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_928
spectrum_assert exact_928 complete

theorem exact_929 : Law929.spectrum = ({1}) :=
  ImplicationTransfer.singleton_929
spectrum_assert exact_929 complete

theorem exact_930 : Law930.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_930
spectrum_assert exact_930 complete

theorem exact_931 : Law931.spectrum = ({1}) :=
  ImplicationTransfer.singleton_931
spectrum_assert exact_931 complete

theorem exact_932 : Law932.spectrum = ({1}) :=
  ImplicationTransfer.singleton_932
spectrum_assert exact_932 complete

theorem exact_933 : Law933.spectrum = ({1}) :=
  ImplicationTransfer.singleton_933
spectrum_assert exact_933 complete

theorem exact_934 : Law934.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_934
spectrum_assert exact_934 complete

theorem exact_935 : Law935.spectrum = ({1}) :=
  ImplicationTransfer.singleton_935
spectrum_assert exact_935 complete

theorem exact_936 : Law936.spectrum = ({1}) :=
  ImplicationTransfer.singleton_936
spectrum_assert exact_936 complete

theorem exact_937 : Law937.spectrum = ({1}) :=
  ImplicationTransfer.singleton_937
spectrum_assert exact_937 complete

theorem exact_938 : Law938.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_938
spectrum_assert exact_938 complete

theorem exact_939 : Law939.spectrum = ({1}) :=
  ImplicationTransfer.singleton_939
spectrum_assert exact_939 complete

theorem exact_940 : Law940.spectrum = ({1}) :=
  ImplicationTransfer.singleton_940
spectrum_assert exact_940 complete

theorem exact_941 : Law941.spectrum = ({1}) :=
  ImplicationTransfer.singleton_941
spectrum_assert exact_941 complete

theorem exact_942 : Law942.spectrum = ({1}) :=
  ImplicationTransfer.singleton_942
spectrum_assert exact_942 complete

theorem exact_943 : Law943.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_943
spectrum_assert exact_943 complete

theorem exact_944 : Law944.spectrum = ({1}) :=
  ImplicationTransfer.singleton_944
spectrum_assert exact_944 complete

theorem exact_945 : Law945.spectrum = ({1}) :=
  ImplicationTransfer.singleton_945
spectrum_assert exact_945 complete

theorem exact_946 : Law946.spectrum = ({1}) :=
  ImplicationTransfer.singleton_946
spectrum_assert exact_946 complete

theorem exact_947 : Law947.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_947
spectrum_assert exact_947 complete

theorem exact_948 : Law948.spectrum = ({1}) :=
  ImplicationTransfer.singleton_948
spectrum_assert exact_948 complete

theorem exact_949 : Law949.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_949_eq_546 |>.trans Note.exact_546
spectrum_assert exact_949 complete

theorem exact_950 : Law950.spectrum = ({1}) :=
  ImplicationTransfer.singleton_950
spectrum_assert exact_950 complete

theorem exact_951 : Law951.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_951
spectrum_assert exact_951 complete

theorem exact_952 : Law952.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_952
spectrum_assert exact_952 complete

theorem exact_953 : Law953.spectrum = ({1}) :=
  ImplicationTransfer.singleton_953
spectrum_assert exact_953 complete

theorem exact_954 : Law954.spectrum = ({1}) :=
  ImplicationTransfer.singleton_954
spectrum_assert exact_954 complete

theorem exact_955 : Law955.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_955
spectrum_assert exact_955 complete

theorem exact_956 : Law956.spectrum = ({1}) :=
  ImplicationTransfer.singleton_956
spectrum_assert exact_956 complete

theorem exact_957 : Law957.spectrum = ({1}) :=
  ImplicationTransfer.singleton_957
spectrum_assert exact_957 complete

theorem exact_958 : Law958.spectrum = ({1}) :=
  ImplicationTransfer.singleton_958
spectrum_assert exact_958 complete

theorem exact_959 : Law959.spectrum = ({1}) :=
  ImplicationTransfer.singleton_959
spectrum_assert exact_959 complete

theorem exact_960 : Law960.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_960
spectrum_assert exact_960 complete

theorem exact_961 : Law961.spectrum = ({1}) :=
  ImplicationTransfer.singleton_961
spectrum_assert exact_961 complete

theorem exact_962 : Law962.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_962_eq_546 |>.trans Note.exact_546
spectrum_assert exact_962 complete

theorem exact_963 : Law963.spectrum = ({1}) :=
  ImplicationTransfer.singleton_963
spectrum_assert exact_963 complete

theorem exact_964 : Law964.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_964
spectrum_assert exact_964 complete

theorem exact_965 : Law965.spectrum = ({1}) :=
  ImplicationTransfer.singleton_965
spectrum_assert exact_965 complete

theorem exact_966 : Law966.spectrum = ({1}) :=
  ImplicationTransfer.singleton_966
spectrum_assert exact_966 complete

theorem exact_967 : Law967.spectrum = ({1}) :=
  ImplicationTransfer.singleton_967
spectrum_assert exact_967 complete

theorem exact_968 : Law968.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_968
spectrum_assert exact_968 complete

theorem exact_969 : Law969.spectrum = ({1}) :=
  ImplicationTransfer.singleton_969
spectrum_assert exact_969 complete

theorem exact_970 : Law970.spectrum = ({1}) :=
  ImplicationTransfer.singleton_970
spectrum_assert exact_970 complete

theorem exact_971 : Law971.spectrum = ({1}) :=
  ImplicationTransfer.singleton_971
spectrum_assert exact_971 complete

theorem exact_972 : Law972.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_972
spectrum_assert exact_972 complete

theorem exact_973 : Law973.spectrum = ({1}) :=
  ImplicationTransfer.singleton_973
spectrum_assert exact_973 complete

theorem exact_974 : Law974.spectrum = ({1}) :=
  ImplicationTransfer.singleton_974
spectrum_assert exact_974 complete

theorem exact_975 : Law975.spectrum = ({1}) :=
  ImplicationTransfer.singleton_975
spectrum_assert exact_975 complete

theorem exact_976 : Law976.spectrum = ({1}) :=
  ImplicationTransfer.singleton_976
spectrum_assert exact_976 complete

theorem exact_977 : Law977.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_977
spectrum_assert exact_977 complete

theorem exact_978 : Law978.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_978
spectrum_assert exact_978 complete

theorem exact_979 : Law979.spectrum = ({1}) :=
  ImplicationTransfer.singleton_979
spectrum_assert exact_979 complete

theorem exact_980 : Law980.spectrum = ({1}) :=
  ImplicationTransfer.singleton_980
spectrum_assert exact_980 complete

theorem exact_981 : Law981.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_981
spectrum_assert exact_981 complete

theorem exact_982 : Law982.spectrum = ({1}) :=
  ImplicationTransfer.singleton_982
spectrum_assert exact_982 complete

theorem exact_983 : Law983.spectrum = ({1}) :=
  ImplicationTransfer.singleton_983
spectrum_assert exact_983 complete

theorem exact_984 : Law984.spectrum = ({1}) :=
  ImplicationTransfer.singleton_984
spectrum_assert exact_984 complete

theorem exact_985 : Law985.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_985
spectrum_assert exact_985 complete

theorem exact_986 : Law986.spectrum = ({1}) :=
  ImplicationTransfer.singleton_986
spectrum_assert exact_986 complete

theorem exact_987 : Law987.spectrum = ({1}) :=
  ImplicationTransfer.singleton_987
spectrum_assert exact_987 complete

theorem exact_988 : Law988.spectrum = ({1}) :=
  ImplicationTransfer.singleton_988
spectrum_assert exact_988 complete

theorem exact_989 : Law989.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_989
spectrum_assert exact_989 complete

theorem exact_990 : Law990.spectrum = ({1}) :=
  ImplicationTransfer.singleton_990
spectrum_assert exact_990 complete

theorem exact_991 : Law991.spectrum = ({1}) :=
  ImplicationTransfer.singleton_991
spectrum_assert exact_991 complete

theorem exact_992 : Law992.spectrum = ({1}) :=
  ImplicationTransfer.singleton_992
spectrum_assert exact_992 complete

theorem exact_993 : Law993.spectrum = ({1}) :=
  ImplicationTransfer.singleton_993
spectrum_assert exact_993 complete

theorem exact_994 : Law994.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_994
spectrum_assert exact_994 complete

theorem exact_995 : Law995.spectrum = ({1}) :=
  ImplicationTransfer.singleton_995
spectrum_assert exact_995 complete

theorem exact_996 : Law996.spectrum = ({1}) :=
  ImplicationTransfer.singleton_996
spectrum_assert exact_996 complete

theorem exact_997 : Law997.spectrum = ({1}) :=
  ImplicationTransfer.singleton_997
spectrum_assert exact_997 complete

theorem exact_998 : Law998.spectrum = ({1}) :=
  ImplicationTransfer.singleton_998
spectrum_assert exact_998 complete

theorem exact_999 : Law999.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_999
spectrum_assert exact_999 complete

theorem exact_1000 : Law1000.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1000
spectrum_assert exact_1000 complete

theorem exact_1001 : Law1001.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1001
spectrum_assert exact_1001 complete

theorem exact_1002 : Law1002.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1002
spectrum_assert exact_1002 complete

theorem exact_1003 : Law1003.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1003
spectrum_assert exact_1003 complete

theorem exact_1004 : Law1004.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1004
spectrum_assert exact_1004 complete

theorem exact_1005 : Law1005.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1005
spectrum_assert exact_1005 complete

theorem exact_1006 : Law1006.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1006
spectrum_assert exact_1006 complete

theorem exact_1007 : Law1007.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1007
spectrum_assert exact_1007 complete

theorem exact_1008 : Law1008.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1008
spectrum_assert exact_1008 complete

theorem exact_1009 : Law1009.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1009
spectrum_assert exact_1009 complete

theorem exact_1010 : Law1010.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1010
spectrum_assert exact_1010 complete

theorem exact_1011 : Law1011.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1011
spectrum_assert exact_1011 complete

theorem exact_1012 : Law1012.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1012
spectrum_assert exact_1012 complete

theorem exact_1013 : Law1013.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1013
spectrum_assert exact_1013 complete

theorem exact_1014 : Law1014.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1014
spectrum_assert exact_1014 complete

theorem exact_1015 : Law1015.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1015
spectrum_assert exact_1015 complete

theorem exact_1016 : Law1016.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1016
spectrum_assert exact_1016 complete

theorem exact_1017 : Law1017.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1017
spectrum_assert exact_1017 complete

theorem exact_1018 : Law1018.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1018
spectrum_assert exact_1018 complete

theorem exact_1019 : Law1019.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1019
spectrum_assert exact_1019 complete

theorem exact_1020 : Law1020.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1020
spectrum_assert exact_1020 complete

theorem exact_1021 : Law1021.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1021
spectrum_assert exact_1021 complete

theorem exact_1022 : Law1022.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1022
spectrum_assert exact_1022 complete

theorem exact_1023 : Law1023.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1023
spectrum_assert exact_1023 complete

theorem exact_1024 : Law1024.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1024
spectrum_assert exact_1024 complete

theorem exact_1025 : Law1025.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1025
spectrum_assert exact_1025 complete

theorem exact_1026 : Law1026.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1026
spectrum_assert exact_1026 complete

theorem exact_1027 : Law1027.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1027
spectrum_assert exact_1027 complete

theorem exact_1028 : Law1028.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1028
spectrum_assert exact_1028 complete

theorem exact_1029 : Law1029.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1029
spectrum_assert exact_1029 complete

theorem exact_1030 : Law1030.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1030
spectrum_assert exact_1030 complete

theorem exact_1031 : Law1031.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1031
spectrum_assert exact_1031 complete

theorem exact_1032 : Law1032.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1032
spectrum_assert exact_1032 complete

theorem exact_1033 : Law1033.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1033
spectrum_assert exact_1033 complete

theorem exact_1034 : Law1034.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1034
spectrum_assert exact_1034 complete

theorem exact_1035 : Law1035.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1035
spectrum_assert exact_1035 complete

theorem exact_1036 : Law1036.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1036
spectrum_assert exact_1036 complete

theorem exact_1037 : Law1037.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1037
spectrum_assert exact_1037 complete

theorem exact_1038 : Law1038.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1038
spectrum_assert exact_1038 complete

theorem exact_1039 : Law1039.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1039
spectrum_assert exact_1039 complete

theorem exact_1040 : Law1040.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1040
spectrum_assert exact_1040 complete

theorem exact_1041 : Law1041.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1041
spectrum_assert exact_1041 complete

theorem exact_1042 : Law1042.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1042
spectrum_assert exact_1042 complete

theorem exact_1043 : Law1043.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1043
spectrum_assert exact_1043 complete

theorem exact_1044 : Law1044.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1044
spectrum_assert exact_1044 complete

theorem exact_1045 : Law1045.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1045
spectrum_assert exact_1045 complete

theorem exact_1046 : Law1046.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1046
spectrum_assert exact_1046 complete

theorem exact_1047 : Law1047.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1047
spectrum_assert exact_1047 complete

theorem exact_1048 : Law1048.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1048
spectrum_assert exact_1048 complete

theorem exact_1049 : Law1049.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1049
spectrum_assert exact_1049 complete

theorem exact_1050 : Law1050.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1050
spectrum_assert exact_1050 complete

theorem exact_1051 : Law1051.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1051
spectrum_assert exact_1051 complete

theorem exact_1052 : Law1052.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1052
spectrum_assert exact_1052 complete

theorem exact_1053 : Law1053.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1053
spectrum_assert exact_1053 complete

theorem exact_1054 : Law1054.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1054
spectrum_assert exact_1054 complete

theorem exact_1055 : Law1055.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1055
spectrum_assert exact_1055 complete

theorem exact_1056 : Law1056.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1056
spectrum_assert exact_1056 complete

theorem exact_1057 : Law1057.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1057
spectrum_assert exact_1057 complete

theorem exact_1058 : Law1058.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1058
spectrum_assert exact_1058 complete

theorem exact_1059 : Law1059.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1059
spectrum_assert exact_1059 complete

theorem exact_1060 : Law1060.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1060
spectrum_assert exact_1060 complete

theorem exact_1061 : Law1061.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1061
spectrum_assert exact_1061 complete

theorem exact_1062 : Law1062.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1062
spectrum_assert exact_1062 complete

theorem exact_1063 : Law1063.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1063
spectrum_assert exact_1063 complete

theorem exact_1064 : Law1064.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1064
spectrum_assert exact_1064 complete

theorem exact_1065 : Law1065.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1065
spectrum_assert exact_1065 complete

theorem exact_1066 : Law1066.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1066
spectrum_assert exact_1066 complete

theorem exact_1067 : Law1067.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1067
spectrum_assert exact_1067 complete

theorem exact_1068 : Law1068.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1068
spectrum_assert exact_1068 complete

theorem exact_1069 : Law1069.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1069
spectrum_assert exact_1069 complete

theorem exact_1070 : Law1070.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1070
spectrum_assert exact_1070 complete

theorem exact_1071 : Law1071.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1071
spectrum_assert exact_1071 complete

theorem exact_1072 : Law1072.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1072
spectrum_assert exact_1072 complete

theorem exact_1073 : Law1073.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1073
spectrum_assert exact_1073 complete

theorem exact_1074 : Law1074.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1074
spectrum_assert exact_1074 complete

theorem exact_1075 : Law1075.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1075
spectrum_assert exact_1075 complete

-- UNKNOWN exact spectrum (PDF representative E1076).
theorem lower_1076 : (({1, 5} : Set ℕ)) ⊆ Law1076.spectrum := by
  rw [ImplicationTransfer.spectrum_1076_eq_1076]
  exact Note.lower_1076
spectrum_assert lower_1076 complete

theorem upper_1076 : Law1076.spectrum ⊆ (positiveExcept {2, 3, 4, 6, 7}) := by
  rw [ImplicationTransfer.spectrum_1076_eq_1076]
  exact Note.upper_1076
spectrum_assert upper_1076 proofAvailable

theorem cofinite_1076 : CofiniteSpectrum Law1076 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1076_eq_1076]
  exact Note.cofinite_1076
spectrum_assert cofinite_1076 noteGap

theorem exact_1077 : Law1077.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1077
spectrum_assert exact_1077 complete

theorem exact_1078 : Law1078.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1078
spectrum_assert exact_1078 complete

theorem exact_1079 : Law1079.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1079
spectrum_assert exact_1079 complete

theorem exact_1080 : Law1080.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1080
spectrum_assert exact_1080 complete

theorem exact_1081 : Law1081.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1081
spectrum_assert exact_1081 complete

theorem exact_1082 : Law1082.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1082
spectrum_assert exact_1082 complete

-- UNKNOWN exact spectrum (PDF representative E1083).
theorem lower_1083 : (({1, 3, 4, 7, 8, 9} : Set ℕ)) ⊆ Law1083.spectrum := by
  rw [ImplicationTransfer.spectrum_1083_eq_1083]
  exact Note.lower_1083
spectrum_assert lower_1083 complete

theorem upper_1083 : Law1083.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_1083_eq_1083]
  exact Note.upper_1083
spectrum_assert upper_1083 complete

theorem exact_1084 : Law1084.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1084
spectrum_assert exact_1084 complete

theorem exact_1085 : Law1085.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1085
spectrum_assert exact_1085 complete

theorem exact_1086 : Law1086.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1086
spectrum_assert exact_1086 complete

theorem exact_1087 : Law1087.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1087
spectrum_assert exact_1087 complete

theorem exact_1088 : Law1088.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1088
spectrum_assert exact_1088 complete

theorem exact_1089 : Law1089.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1089
spectrum_assert exact_1089 complete

theorem exact_1090 : Law1090.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1090
spectrum_assert exact_1090 complete

theorem exact_1091 : Law1091.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1091
spectrum_assert exact_1091 complete

theorem exact_1092 : Law1092.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1092
spectrum_assert exact_1092 complete

theorem exact_1093 : Law1093.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1093
spectrum_assert exact_1093 complete

theorem exact_1094 : Law1094.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1094
spectrum_assert exact_1094 complete

theorem exact_1095 : Law1095.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1095
spectrum_assert exact_1095 complete

theorem exact_1096 : Law1096.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1096
spectrum_assert exact_1096 complete

theorem exact_1097 : Law1097.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1097
spectrum_assert exact_1097 complete

theorem exact_1098 : Law1098.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1098_eq_546 |>.trans Note.exact_546
spectrum_assert exact_1098 complete

theorem exact_1099 : Law1099.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1099
spectrum_assert exact_1099 complete

theorem exact_1100 : Law1100.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1100
spectrum_assert exact_1100 complete

theorem exact_1101 : Law1101.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1101
spectrum_assert exact_1101 complete

theorem exact_1102 : Law1102.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1102
spectrum_assert exact_1102 complete

theorem exact_1103 : Law1103.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1103
spectrum_assert exact_1103 complete

theorem exact_1104 : Law1104.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1104
spectrum_assert exact_1104 complete

theorem exact_1105 : Law1105.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1105
spectrum_assert exact_1105 complete

theorem exact_1106 : Law1106.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1106
spectrum_assert exact_1106 complete

theorem exact_1107 : Law1107.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1107
spectrum_assert exact_1107 complete

theorem exact_1108 : Law1108.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1108
spectrum_assert exact_1108 complete

theorem exact_1109 : Law1109.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1109
spectrum_assert exact_1109 complete

-- UNKNOWN exact spectrum (PDF representative E1110).
theorem lower_1110 : (({1, 4, 5, 7, 8, 9} : Set ℕ)) ⊆ Law1110.spectrum := by
  rw [ImplicationTransfer.spectrum_1110_eq_1110]
  exact Note.lower_1110
spectrum_assert lower_1110 complete

theorem upper_1110 : Law1110.spectrum ⊆ (positiveExcept {2, 3, 6}) := by
  rw [ImplicationTransfer.spectrum_1110_eq_1110]
  exact Note.upper_1110
spectrum_assert upper_1110 proofAvailable

theorem cofinite_1110 : CofiniteSpectrum Law1110 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1110_eq_1110]
  exact Note.cofinite_1110
spectrum_assert cofinite_1110 proofAvailable

theorem exact_1111 : Law1111.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1111
spectrum_assert exact_1111 complete

theorem exact_1112 : Law1112.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1112
spectrum_assert exact_1112 complete

theorem exact_1113 : Law1113.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1113
spectrum_assert exact_1113 complete

theorem exact_1114 : Law1114.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1114
spectrum_assert exact_1114 complete

theorem exact_1115 : Law1115.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1115
spectrum_assert exact_1115 complete

theorem exact_1116 : Law1116.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1116
spectrum_assert exact_1116 complete

theorem exact_1117 : Law1117.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1117
spectrum_assert exact_1117 complete

theorem exact_1118 : Law1118.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1118
spectrum_assert exact_1118 complete

theorem exact_1119 : Law1119.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1119
spectrum_assert exact_1119 complete

theorem exact_1120 : Law1120.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1120
spectrum_assert exact_1120 complete

theorem exact_1121 : Law1121.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1121
spectrum_assert exact_1121 complete

theorem exact_1122 : Law1122.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1122
spectrum_assert exact_1122 complete

theorem exact_1123 : Law1123.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1123
spectrum_assert exact_1123 complete

theorem exact_1124 : Law1124.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1124
spectrum_assert exact_1124 complete

theorem exact_1125 : Law1125.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1125
spectrum_assert exact_1125 complete

theorem exact_1126 : Law1126.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1126
spectrum_assert exact_1126 complete

theorem exact_1127 : Law1127.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1127
spectrum_assert exact_1127 complete

theorem exact_1128 : Law1128.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1128
spectrum_assert exact_1128 complete

theorem exact_1129 : Law1129.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1129
spectrum_assert exact_1129 complete

theorem exact_1130 : Law1130.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1130
spectrum_assert exact_1130 complete

theorem exact_1131 : Law1131.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1131_eq_556 |>.trans Note.exact_556
spectrum_assert exact_1131 complete

theorem exact_1132 : Law1132.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1132
spectrum_assert exact_1132 complete

theorem exact_1133 : Law1133.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1133
spectrum_assert exact_1133 complete

theorem exact_1134 : Law1134.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1134
spectrum_assert exact_1134 complete

theorem exact_1135 : Law1135.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1135
spectrum_assert exact_1135 complete

theorem exact_1136 : Law1136.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1136
spectrum_assert exact_1136 complete

theorem exact_1137 : Law1137.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1137
spectrum_assert exact_1137 complete

theorem exact_1138 : Law1138.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1138
spectrum_assert exact_1138 complete

theorem exact_1139 : Law1139.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1139
spectrum_assert exact_1139 complete

theorem exact_1140 : Law1140.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1140
spectrum_assert exact_1140 complete

theorem exact_1141 : Law1141.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1141
spectrum_assert exact_1141 complete

theorem exact_1142 : Law1142.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1142
spectrum_assert exact_1142 complete

theorem exact_1143 : Law1143.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1143
spectrum_assert exact_1143 complete

theorem exact_1144 : Law1144.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1144
spectrum_assert exact_1144 complete

theorem exact_1145 : Law1145.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1145
spectrum_assert exact_1145 complete

theorem exact_1146 : Law1146.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1146
spectrum_assert exact_1146 complete

theorem exact_1147 : Law1147.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1147
spectrum_assert exact_1147 complete

theorem exact_1148 : Law1148.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1148
spectrum_assert exact_1148 complete

theorem exact_1149 : Law1149.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1149
spectrum_assert exact_1149 complete

theorem exact_1150 : Law1150.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1150
spectrum_assert exact_1150 complete

theorem exact_1151 : Law1151.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1151
spectrum_assert exact_1151 complete

theorem exact_1152 : Law1152.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1152
spectrum_assert exact_1152 complete

theorem exact_1153 : Law1153.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1153
spectrum_assert exact_1153 complete

theorem exact_1154 : Law1154.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1154
spectrum_assert exact_1154 complete

theorem exact_1155 : Law1155.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1155
spectrum_assert exact_1155 complete

theorem exact_1156 : Law1156.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1156
spectrum_assert exact_1156 complete

theorem exact_1157 : Law1157.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1157
spectrum_assert exact_1157 complete

theorem exact_1158 : Law1158.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1158
spectrum_assert exact_1158 complete

theorem exact_1159 : Law1159.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1159
spectrum_assert exact_1159 complete

theorem exact_1160 : Law1160.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1160
spectrum_assert exact_1160 complete

theorem exact_1161 : Law1161.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1161
spectrum_assert exact_1161 complete

theorem exact_1162 : Law1162.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1162
spectrum_assert exact_1162 complete

theorem exact_1163 : Law1163.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1163
spectrum_assert exact_1163 complete

theorem exact_1164 : Law1164.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1164
spectrum_assert exact_1164 complete

theorem exact_1165 : Law1165.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1165
spectrum_assert exact_1165 complete

theorem exact_1166 : Law1166.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1166
spectrum_assert exact_1166 complete

theorem exact_1167 : Law1167.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1167
spectrum_assert exact_1167 complete

theorem exact_1168 : Law1168.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1168
spectrum_assert exact_1168 complete

theorem exact_1169 : Law1169.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1169
spectrum_assert exact_1169 complete

theorem exact_1170 : Law1170.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1170
spectrum_assert exact_1170 complete

theorem exact_1171 : Law1171.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1171
spectrum_assert exact_1171 complete

theorem exact_1172 : Law1172.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1172
spectrum_assert exact_1172 complete

theorem exact_1173 : Law1173.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1173
spectrum_assert exact_1173 complete

theorem exact_1174 : Law1174.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1174
spectrum_assert exact_1174 complete

theorem exact_1175 : Law1175.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1175
spectrum_assert exact_1175 complete

theorem exact_1176 : Law1176.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1176
spectrum_assert exact_1176 complete

theorem exact_1177 : Law1177.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1177
spectrum_assert exact_1177 complete

theorem exact_1178 : Law1178.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1178
spectrum_assert exact_1178 complete

theorem exact_1179 : Law1179.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1179
spectrum_assert exact_1179 complete

theorem exact_1180 : Law1180.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1180
spectrum_assert exact_1180 complete

theorem exact_1181 : Law1181.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1181
spectrum_assert exact_1181 complete

theorem exact_1182 : Law1182.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1182
spectrum_assert exact_1182 complete

theorem exact_1183 : Law1183.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1183
spectrum_assert exact_1183 complete

theorem exact_1184 : Law1184.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1184
spectrum_assert exact_1184 complete

theorem exact_1185 : Law1185.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1185
spectrum_assert exact_1185 complete

theorem exact_1186 : Law1186.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1186
spectrum_assert exact_1186 complete

theorem exact_1187 : Law1187.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1187
spectrum_assert exact_1187 complete

theorem exact_1188 : Law1188.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1188
spectrum_assert exact_1188 complete

theorem exact_1189 : Law1189.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1189
spectrum_assert exact_1189 complete

theorem exact_1190 : Law1190.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1190
spectrum_assert exact_1190 complete

theorem exact_1191 : Law1191.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1191
spectrum_assert exact_1191 complete

theorem exact_1192 : Law1192.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1192
spectrum_assert exact_1192 complete

theorem exact_1193 : Law1193.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1193
spectrum_assert exact_1193 complete

theorem exact_1194 : Law1194.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1194
spectrum_assert exact_1194 complete

theorem exact_1195 : Law1195.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1195
spectrum_assert exact_1195 complete

theorem exact_1196 : Law1196.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1196
spectrum_assert exact_1196 complete

theorem exact_1197 : Law1197.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1197
spectrum_assert exact_1197 complete

theorem exact_1198 : Law1198.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1198
spectrum_assert exact_1198 complete

theorem exact_1199 : Law1199.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1199
spectrum_assert exact_1199 complete

theorem exact_1200 : Law1200.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1200
spectrum_assert exact_1200 complete

theorem exact_1201 : Law1201.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1201
spectrum_assert exact_1201 complete

theorem exact_1202 : Law1202.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1202
spectrum_assert exact_1202 complete

theorem exact_1203 : Law1203.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1203
spectrum_assert exact_1203 complete

theorem exact_1204 : Law1204.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1204
spectrum_assert exact_1204 complete

theorem exact_1205 : Law1205.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1205
spectrum_assert exact_1205 complete

theorem exact_1206 : Law1206.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1206
spectrum_assert exact_1206 complete

theorem exact_1207 : Law1207.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1207
spectrum_assert exact_1207 complete

theorem exact_1208 : Law1208.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1208
spectrum_assert exact_1208 complete

theorem exact_1209 : Law1209.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1209
spectrum_assert exact_1209 complete

theorem exact_1210 : Law1210.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1210
spectrum_assert exact_1210 complete

theorem exact_1211 : Law1211.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1211
spectrum_assert exact_1211 complete

theorem exact_1212 : Law1212.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1212
spectrum_assert exact_1212 complete

theorem exact_1213 : Law1213.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1213
spectrum_assert exact_1213 complete

theorem exact_1214 : Law1214.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1214
spectrum_assert exact_1214 complete

theorem exact_1215 : Law1215.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1215
spectrum_assert exact_1215 complete

theorem exact_1216 : Law1216.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1216
spectrum_assert exact_1216 complete

theorem exact_1217 : Law1217.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1217
spectrum_assert exact_1217 complete

theorem exact_1218 : Law1218.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1218
spectrum_assert exact_1218 complete

theorem exact_1219 : Law1219.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1219
spectrum_assert exact_1219 complete

theorem exact_1220 : Law1220.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1220
spectrum_assert exact_1220 complete

theorem exact_1221 : Law1221.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1221
spectrum_assert exact_1221 complete

theorem exact_1222 : Law1222.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1222
spectrum_assert exact_1222 complete

theorem exact_1223 : Law1223.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1223
spectrum_assert exact_1223 complete

theorem exact_1224 : Law1224.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1224
spectrum_assert exact_1224 complete

theorem exact_1225 : Law1225.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1225
spectrum_assert exact_1225 complete

theorem exact_1226 : Law1226.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1226
spectrum_assert exact_1226 complete

theorem exact_1227 : Law1227.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1227
spectrum_assert exact_1227 complete

theorem exact_1228 : Law1228.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1228
spectrum_assert exact_1228 complete

theorem exact_1229 : Law1229.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1229
spectrum_assert exact_1229 complete

theorem exact_1230 : Law1230.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1230
spectrum_assert exact_1230 complete

theorem exact_1231 : Law1231.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1231
spectrum_assert exact_1231 complete

theorem exact_1232 : Law1232.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1232
spectrum_assert exact_1232 complete

theorem exact_1233 : Law1233.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1233
spectrum_assert exact_1233 complete

theorem exact_1234 : Law1234.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1234
spectrum_assert exact_1234 complete

theorem exact_1235 : Law1235.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1235
spectrum_assert exact_1235 complete

theorem exact_1236 : Law1236.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1236
spectrum_assert exact_1236 complete

theorem exact_1237 : Law1237.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1237
spectrum_assert exact_1237 complete

theorem exact_1238 : Law1238.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1238
spectrum_assert exact_1238 complete

theorem exact_1239 : Law1239.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1239
spectrum_assert exact_1239 complete

theorem exact_1240 : Law1240.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1240
spectrum_assert exact_1240 complete

theorem exact_1241 : Law1241.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1241
spectrum_assert exact_1241 complete

theorem exact_1242 : Law1242.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1242
spectrum_assert exact_1242 complete

theorem exact_1243 : Law1243.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1243
spectrum_assert exact_1243 complete

theorem exact_1244 : Law1244.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1244
spectrum_assert exact_1244 complete

theorem exact_1245 : Law1245.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1245
spectrum_assert exact_1245 complete

theorem exact_1246 : Law1246.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1246
spectrum_assert exact_1246 complete

theorem exact_1247 : Law1247.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1247
spectrum_assert exact_1247 complete

theorem exact_1248 : Law1248.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1248
spectrum_assert exact_1248 complete

theorem exact_1249 : Law1249.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1249
spectrum_assert exact_1249 complete

theorem exact_1250 : Law1250.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1250
spectrum_assert exact_1250 complete

theorem exact_1251 : Law1251.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1251
spectrum_assert exact_1251 complete

theorem exact_1252 : Law1252.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1252
spectrum_assert exact_1252 complete

theorem exact_1253 : Law1253.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1253
spectrum_assert exact_1253 complete

theorem exact_1254 : Law1254.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1254
spectrum_assert exact_1254 complete

theorem exact_1255 : Law1255.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1255
spectrum_assert exact_1255 complete

theorem exact_1256 : Law1256.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1256
spectrum_assert exact_1256 complete

theorem exact_1257 : Law1257.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1257
spectrum_assert exact_1257 complete

theorem exact_1258 : Law1258.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1258
spectrum_assert exact_1258 complete

theorem exact_1259 : Law1259.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1259
spectrum_assert exact_1259 complete

theorem exact_1260 : Law1260.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1260
spectrum_assert exact_1260 complete

theorem exact_1261 : Law1261.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1261
spectrum_assert exact_1261 complete

theorem exact_1262 : Law1262.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1262
spectrum_assert exact_1262 complete

theorem exact_1263 : Law1263.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1263
spectrum_assert exact_1263 complete

theorem exact_1264 : Law1264.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1264
spectrum_assert exact_1264 complete

theorem exact_1265 : Law1265.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1265
spectrum_assert exact_1265 complete

theorem exact_1266 : Law1266.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1266
spectrum_assert exact_1266 complete

theorem exact_1267 : Law1267.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1267
spectrum_assert exact_1267 complete

theorem exact_1268 : Law1268.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1268
spectrum_assert exact_1268 complete

theorem exact_1269 : Law1269.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1269
spectrum_assert exact_1269 complete

theorem exact_1270 : Law1270.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1270
spectrum_assert exact_1270 complete

theorem exact_1271 : Law1271.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1271
spectrum_assert exact_1271 complete

theorem exact_1272 : Law1272.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1272
spectrum_assert exact_1272 complete

theorem exact_1273 : Law1273.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1273
spectrum_assert exact_1273 complete

theorem exact_1274 : Law1274.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1274
spectrum_assert exact_1274 complete

theorem exact_1275 : Law1275.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1275
spectrum_assert exact_1275 complete

theorem exact_1276 : Law1276.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1276
spectrum_assert exact_1276 complete

theorem exact_1277 : Law1277.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1277
spectrum_assert exact_1277 complete

theorem exact_1278 : Law1278.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1278
spectrum_assert exact_1278 complete

-- UNKNOWN exact spectrum (PDF representative E1279).
theorem lower_1279 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law1279.spectrum := by
  rw [ImplicationTransfer.spectrum_1279_eq_1279]
  exact Note.lower_1279
spectrum_assert lower_1279 complete

theorem upper_1279 : Law1279.spectrum ⊆ (positiveExcept {2, 3, 4, 6, 9}) := by
  rw [ImplicationTransfer.spectrum_1279_eq_1279]
  exact Note.upper_1279
spectrum_assert upper_1279 proofAvailable

theorem cofinite_1279 : CofiniteSpectrum Law1279 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1279_eq_1279]
  exact Note.cofinite_1279
spectrum_assert cofinite_1279 proofAvailable

theorem exact_1280 : Law1280.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1280
spectrum_assert exact_1280 complete

theorem exact_1281 : Law1281.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1281
spectrum_assert exact_1281 complete

theorem exact_1282 : Law1282.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1282
spectrum_assert exact_1282 complete

theorem exact_1283 : Law1283.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1283
spectrum_assert exact_1283 complete

theorem exact_1284 : Law1284.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1284
spectrum_assert exact_1284 complete

theorem exact_1285 : Law1285.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1285
spectrum_assert exact_1285 complete

-- UNKNOWN exact spectrum (PDF representative E1286).
theorem lower_1286 : (({1, 7} : Set ℕ)) ⊆ Law1286.spectrum := by
  rw [ImplicationTransfer.spectrum_1286_eq_1286]
  exact Note.lower_1286
spectrum_assert lower_1286 complete

theorem upper_1286 : Law1286.spectrum ⊆ (positiveExcept {2, 3, 4, 5, 6}) := by
  rw [ImplicationTransfer.spectrum_1286_eq_1286]
  exact Note.upper_1286
spectrum_assert upper_1286 proofAvailable

theorem exact_1287 : Law1287.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1287
spectrum_assert exact_1287 complete

theorem exact_1288 : Law1288.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1288
spectrum_assert exact_1288 complete

theorem exact_1289 : Law1289.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1289
spectrum_assert exact_1289 complete

theorem exact_1290 : Law1290.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1290
spectrum_assert exact_1290 complete

theorem exact_1291 : Law1291.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1291
spectrum_assert exact_1291 complete

theorem exact_1292 : Law1292.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1292
spectrum_assert exact_1292 complete

theorem exact_1293 : Law1293.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1293
spectrum_assert exact_1293 complete

theorem exact_1294 : Law1294.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1294
spectrum_assert exact_1294 complete

theorem exact_1295 : Law1295.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1295
spectrum_assert exact_1295 complete

theorem exact_1296 : Law1296.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1296
spectrum_assert exact_1296 complete

theorem exact_1297 : Law1297.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1297
spectrum_assert exact_1297 complete

theorem exact_1298 : Law1298.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1298
spectrum_assert exact_1298 complete

theorem exact_1299 : Law1299.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1299
spectrum_assert exact_1299 complete

theorem exact_1300 : Law1300.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1300
spectrum_assert exact_1300 complete

theorem exact_1301 : Law1301.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1301_eq_556 |>.trans Note.exact_556
spectrum_assert exact_1301 complete

theorem exact_1302 : Law1302.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1302
spectrum_assert exact_1302 complete

theorem exact_1303 : Law1303.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1303
spectrum_assert exact_1303 complete

theorem exact_1304 : Law1304.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1304
spectrum_assert exact_1304 complete

theorem exact_1305 : Law1305.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1305
spectrum_assert exact_1305 complete

theorem exact_1306 : Law1306.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1306
spectrum_assert exact_1306 complete

theorem exact_1307 : Law1307.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1307
spectrum_assert exact_1307 complete

theorem exact_1308 : Law1308.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1308
spectrum_assert exact_1308 complete

theorem exact_1309 : Law1309.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1309
spectrum_assert exact_1309 complete

theorem exact_1310 : Law1310.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1310
spectrum_assert exact_1310 complete

theorem exact_1311 : Law1311.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1311
spectrum_assert exact_1311 complete

theorem exact_1312 : Law1312.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1312
spectrum_assert exact_1312 complete

-- UNKNOWN exact spectrum (PDF representative E1313).
theorem lower_1313 : (({1, 5, 7} : Set ℕ)) ⊆ Law1313.spectrum := by
  rw [ImplicationTransfer.spectrum_1313_eq_1313]
  exact Note.lower_1313
spectrum_assert lower_1313 complete

theorem upper_1313 : Law1313.spectrum ⊆ (positiveExcept {2, 3, 4, 6}) := by
  rw [ImplicationTransfer.spectrum_1313_eq_1313]
  exact Note.upper_1313
spectrum_assert upper_1313 proofAvailable

theorem exact_1314 : Law1314.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1314
spectrum_assert exact_1314 complete

theorem exact_1315 : Law1315.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1315
spectrum_assert exact_1315 complete

theorem exact_1316 : Law1316.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1316
spectrum_assert exact_1316 complete

theorem exact_1317 : Law1317.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1317
spectrum_assert exact_1317 complete

theorem exact_1318 : Law1318.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1318
spectrum_assert exact_1318 complete

theorem exact_1319 : Law1319.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1319
spectrum_assert exact_1319 complete

theorem exact_1320 : Law1320.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1320
spectrum_assert exact_1320 complete

theorem exact_1321 : Law1321.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1321
spectrum_assert exact_1321 complete

theorem exact_1322 : Law1322.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1322
spectrum_assert exact_1322 complete

-- UNKNOWN exact spectrum (PDF representative E1323).
theorem lower_1323 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law1323.spectrum := by
  rw [ImplicationTransfer.spectrum_1323_eq_1323]
  exact Note.lower_1323
spectrum_assert lower_1323 proofAvailable

theorem upper_1323 : Law1323.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_1323_eq_1323]
  exact Note.upper_1323
spectrum_assert upper_1323 complete

theorem cofinite_1323 : CofiniteSpectrum Law1323 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1323_eq_1323]
  exact Note.cofinite_1323
spectrum_assert cofinite_1323 proofAvailable

theorem exact_1324 : Law1324.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1324
spectrum_assert exact_1324 complete

theorem exact_1325 : Law1325.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1325
spectrum_assert exact_1325 complete

theorem exact_1326 : Law1326.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1326
spectrum_assert exact_1326 complete

theorem exact_1327 : Law1327.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1327
spectrum_assert exact_1327 complete

theorem exact_1328 : Law1328.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1328
spectrum_assert exact_1328 complete

theorem exact_1329 : Law1329.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1329
spectrum_assert exact_1329 complete

theorem exact_1330 : Law1330.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1330
spectrum_assert exact_1330 complete

theorem exact_1331 : Law1331.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1331
spectrum_assert exact_1331 complete

theorem exact_1332 : Law1332.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1332
spectrum_assert exact_1332 complete

theorem exact_1333 : Law1333.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1333
spectrum_assert exact_1333 complete

theorem exact_1334 : Law1334.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_1334_eq_895 |>.trans Note.exact_895
spectrum_assert exact_1334 proofAvailable

theorem exact_1335 : Law1335.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1335
spectrum_assert exact_1335 complete

theorem exact_1336 : Law1336.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1336
spectrum_assert exact_1336 complete

theorem exact_1337 : Law1337.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1337
spectrum_assert exact_1337 complete

theorem exact_1338 : Law1338.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1338
spectrum_assert exact_1338 complete

theorem exact_1339 : Law1339.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1339
spectrum_assert exact_1339 complete

theorem exact_1340 : Law1340.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1340
spectrum_assert exact_1340 complete

theorem exact_1341 : Law1341.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1341
spectrum_assert exact_1341 complete

theorem exact_1342 : Law1342.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1342
spectrum_assert exact_1342 complete

theorem exact_1343 : Law1343.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1343
spectrum_assert exact_1343 complete

theorem exact_1344 : Law1344.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1344
spectrum_assert exact_1344 complete

theorem exact_1345 : Law1345.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1345
spectrum_assert exact_1345 complete

theorem exact_1346 : Law1346.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1346
spectrum_assert exact_1346 complete

theorem exact_1347 : Law1347.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1347
spectrum_assert exact_1347 complete

theorem exact_1348 : Law1348.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1348
spectrum_assert exact_1348 complete

theorem exact_1349 : Law1349.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1349
spectrum_assert exact_1349 complete

theorem exact_1350 : Law1350.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1350
spectrum_assert exact_1350 complete

theorem exact_1351 : Law1351.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1351
spectrum_assert exact_1351 complete

theorem exact_1352 : Law1352.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1352
spectrum_assert exact_1352 complete

theorem exact_1353 : Law1353.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1353
spectrum_assert exact_1353 complete

theorem exact_1354 : Law1354.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1354
spectrum_assert exact_1354 complete

theorem exact_1355 : Law1355.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1355_eq_556 |>.trans Note.exact_556
spectrum_assert exact_1355 complete

theorem exact_1356 : Law1356.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1356
spectrum_assert exact_1356 complete

theorem exact_1357 : Law1357.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1357
spectrum_assert exact_1357 complete

theorem exact_1358 : Law1358.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1358
spectrum_assert exact_1358 complete

theorem exact_1359 : Law1359.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1359
spectrum_assert exact_1359 complete

theorem exact_1360 : Law1360.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1360
spectrum_assert exact_1360 complete

theorem exact_1361 : Law1361.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1361
spectrum_assert exact_1361 complete

theorem exact_1362 : Law1362.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1362
spectrum_assert exact_1362 complete

theorem exact_1363 : Law1363.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1363
spectrum_assert exact_1363 complete

theorem exact_1364 : Law1364.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1364
spectrum_assert exact_1364 complete

theorem exact_1365 : Law1365.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1365
spectrum_assert exact_1365 complete

theorem exact_1366 : Law1366.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1366
spectrum_assert exact_1366 complete

theorem exact_1367 : Law1367.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1367
spectrum_assert exact_1367 complete

theorem exact_1368 : Law1368.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_1368_eq_898 |>.trans Note.exact_898
spectrum_assert exact_1368 noteGap

theorem exact_1369 : Law1369.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1369
spectrum_assert exact_1369 complete

theorem exact_1370 : Law1370.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1370
spectrum_assert exact_1370 complete

theorem exact_1371 : Law1371.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1371
spectrum_assert exact_1371 complete

theorem exact_1372 : Law1372.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1372
spectrum_assert exact_1372 complete

theorem exact_1373 : Law1373.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1373
spectrum_assert exact_1373 complete

theorem exact_1374 : Law1374.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1374
spectrum_assert exact_1374 complete

theorem exact_1375 : Law1375.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1375
spectrum_assert exact_1375 complete

theorem exact_1376 : Law1376.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1376
spectrum_assert exact_1376 complete

theorem exact_1377 : Law1377.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1377
spectrum_assert exact_1377 complete

theorem exact_1378 : Law1378.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1378
spectrum_assert exact_1378 complete

theorem exact_1379 : Law1379.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1379
spectrum_assert exact_1379 complete

theorem exact_1380 : Law1380.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1380
spectrum_assert exact_1380 complete

theorem exact_1381 : Law1381.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1381
spectrum_assert exact_1381 complete

theorem exact_1382 : Law1382.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1382
spectrum_assert exact_1382 complete

theorem exact_1383 : Law1383.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1383
spectrum_assert exact_1383 complete

theorem exact_1384 : Law1384.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_1384_eq_887 |>.trans Note.exact_887
spectrum_assert exact_1384 complete

theorem exact_1385 : Law1385.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1385
spectrum_assert exact_1385 complete

theorem exact_1386 : Law1386.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1386
spectrum_assert exact_1386 complete

theorem exact_1387 : Law1387.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1387
spectrum_assert exact_1387 complete

theorem exact_1388 : Law1388.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1388
spectrum_assert exact_1388 complete

theorem exact_1389 : Law1389.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1389
spectrum_assert exact_1389 complete

theorem exact_1390 : Law1390.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1390
spectrum_assert exact_1390 complete

theorem exact_1391 : Law1391.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1391
spectrum_assert exact_1391 complete

theorem exact_1392 : Law1392.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1392
spectrum_assert exact_1392 complete

theorem exact_1393 : Law1393.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1393
spectrum_assert exact_1393 complete

theorem exact_1394 : Law1394.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1394
spectrum_assert exact_1394 complete

theorem exact_1395 : Law1395.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1395
spectrum_assert exact_1395 complete

theorem exact_1396 : Law1396.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1396
spectrum_assert exact_1396 complete

theorem exact_1397 : Law1397.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1397
spectrum_assert exact_1397 complete

theorem exact_1398 : Law1398.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1398
spectrum_assert exact_1398 complete

theorem exact_1399 : Law1399.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1399
spectrum_assert exact_1399 complete

theorem exact_1400 : Law1400.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1400
spectrum_assert exact_1400 complete

theorem exact_1401 : Law1401.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1401
spectrum_assert exact_1401 complete

theorem exact_1402 : Law1402.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1402
spectrum_assert exact_1402 complete

theorem exact_1403 : Law1403.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1403
spectrum_assert exact_1403 complete

theorem exact_1404 : Law1404.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1404
spectrum_assert exact_1404 complete

theorem exact_1405 : Law1405.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1405
spectrum_assert exact_1405 complete

theorem exact_1406 : Law1406.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1406
spectrum_assert exact_1406 complete

theorem exact_1407 : Law1407.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1407
spectrum_assert exact_1407 complete

theorem exact_1408 : Law1408.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1408
spectrum_assert exact_1408 complete

theorem exact_1409 : Law1409.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1409
spectrum_assert exact_1409 complete

theorem exact_1410 : Law1410.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1410
spectrum_assert exact_1410 complete

theorem exact_1411 : Law1411.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1411
spectrum_assert exact_1411 complete

theorem exact_1412 : Law1412.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1412
spectrum_assert exact_1412 complete

theorem exact_1413 : Law1413.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1413
spectrum_assert exact_1413 complete

theorem exact_1414 : Law1414.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1414
spectrum_assert exact_1414 complete

theorem exact_1415 : Law1415.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1415
spectrum_assert exact_1415 complete

theorem exact_1416 : Law1416.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1416
spectrum_assert exact_1416 complete

theorem exact_1417 : Law1417.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1417
spectrum_assert exact_1417 complete

theorem exact_1418 : Law1418.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1418
spectrum_assert exact_1418 complete

theorem exact_1419 : Law1419.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1419
spectrum_assert exact_1419 complete

theorem exact_1420 : Law1420.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1420
spectrum_assert exact_1420 complete

theorem exact_1421 : Law1421.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1421
spectrum_assert exact_1421 complete

theorem exact_1422 : Law1422.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1422
spectrum_assert exact_1422 complete

theorem exact_1423 : Law1423.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1423
spectrum_assert exact_1423 complete

theorem exact_1424 : Law1424.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1424
spectrum_assert exact_1424 complete

theorem exact_1425 : Law1425.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1425
spectrum_assert exact_1425 complete

theorem exact_1426 : Law1426.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1426
spectrum_assert exact_1426 complete

theorem exact_1427 : Law1427.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1427
spectrum_assert exact_1427 complete

theorem exact_1428 : Law1428.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1428
spectrum_assert exact_1428 complete

theorem exact_1429 : Law1429.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1429
spectrum_assert exact_1429 complete

theorem exact_1430 : Law1430.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1430
spectrum_assert exact_1430 complete

theorem exact_1431 : Law1431.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1431
spectrum_assert exact_1431 complete

theorem exact_1432 : Law1432.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1432
spectrum_assert exact_1432 complete

theorem exact_1433 : Law1433.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1433
spectrum_assert exact_1433 complete

theorem exact_1434 : Law1434.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1434
spectrum_assert exact_1434 complete

theorem exact_1435 : Law1435.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1435
spectrum_assert exact_1435 complete

theorem exact_1436 : Law1436.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1436
spectrum_assert exact_1436 complete

theorem exact_1437 : Law1437.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1437
spectrum_assert exact_1437 complete

theorem exact_1438 : Law1438.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1438
spectrum_assert exact_1438 complete

theorem exact_1439 : Law1439.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1439
spectrum_assert exact_1439 complete

theorem exact_1440 : Law1440.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1440
spectrum_assert exact_1440 complete

theorem exact_1441 : Law1441.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1441
spectrum_assert exact_1441 complete

theorem exact_1442 : Law1442.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1442
spectrum_assert exact_1442 complete

theorem exact_1443 : Law1443.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1443
spectrum_assert exact_1443 complete

theorem exact_1444 : Law1444.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1444
spectrum_assert exact_1444 complete

theorem exact_1445 : Law1445.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1445
spectrum_assert exact_1445 complete

theorem exact_1446 : Law1446.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1446
spectrum_assert exact_1446 complete

theorem exact_1447 : Law1447.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1447
spectrum_assert exact_1447 complete

theorem exact_1448 : Law1448.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1448
spectrum_assert exact_1448 complete

theorem exact_1449 : Law1449.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1449
spectrum_assert exact_1449 complete

theorem exact_1450 : Law1450.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1450
spectrum_assert exact_1450 complete

theorem exact_1451 : Law1451.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1451
spectrum_assert exact_1451 complete

theorem exact_1452 : Law1452.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1452
spectrum_assert exact_1452 complete

theorem exact_1453 : Law1453.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1453
spectrum_assert exact_1453 complete

theorem exact_1454 : Law1454.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1454
spectrum_assert exact_1454 complete

theorem exact_1455 : Law1455.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1455
spectrum_assert exact_1455 complete

theorem exact_1456 : Law1456.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1456
spectrum_assert exact_1456 complete

theorem exact_1457 : Law1457.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1457
spectrum_assert exact_1457 complete

theorem exact_1458 : Law1458.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1458
spectrum_assert exact_1458 complete

theorem exact_1459 : Law1459.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1459
spectrum_assert exact_1459 complete

theorem exact_1460 : Law1460.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1460
spectrum_assert exact_1460 complete

theorem exact_1461 : Law1461.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1461
spectrum_assert exact_1461 complete

theorem exact_1462 : Law1462.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1462
spectrum_assert exact_1462 complete

theorem exact_1463 : Law1463.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1463
spectrum_assert exact_1463 complete

theorem exact_1464 : Law1464.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1464
spectrum_assert exact_1464 complete

theorem exact_1465 : Law1465.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1465
spectrum_assert exact_1465 complete

theorem exact_1466 : Law1466.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1466
spectrum_assert exact_1466 complete

theorem exact_1467 : Law1467.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1467
spectrum_assert exact_1467 complete

theorem exact_1468 : Law1468.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1468
spectrum_assert exact_1468 complete

theorem exact_1469 : Law1469.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1469
spectrum_assert exact_1469 complete

theorem exact_1470 : Law1470.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1470
spectrum_assert exact_1470 complete

theorem exact_1471 : Law1471.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1471
spectrum_assert exact_1471 complete

theorem exact_1472 : Law1472.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1472
spectrum_assert exact_1472 complete

theorem exact_1473 : Law1473.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1473
spectrum_assert exact_1473 complete

theorem exact_1474 : Law1474.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1474
spectrum_assert exact_1474 complete

theorem exact_1475 : Law1475.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1475
spectrum_assert exact_1475 complete

theorem exact_1476 : Law1476.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1476
spectrum_assert exact_1476 complete

theorem exact_1477 : Law1477.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1477
spectrum_assert exact_1477 complete

theorem exact_1478 : Law1478.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1478
spectrum_assert exact_1478 complete

theorem exact_1479 : Law1479.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1479
spectrum_assert exact_1479 complete

-- UNKNOWN exact spectrum (PDF representative E1480).
theorem lower_1480 : (({1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Set ℕ) ∪ (squares)) ⊆ Law1480.spectrum := by
  rw [ImplicationTransfer.spectrum_1480_eq_1480]
  exact Note.lower_1480
spectrum_assert lower_1480 proofAvailable

theorem upper_1480 : Law1480.spectrum ⊆ (positiveExcept {2, 3}) := by
  rw [ImplicationTransfer.spectrum_1480_eq_1480]
  exact Note.upper_1480
spectrum_assert upper_1480 complete

theorem exact_1481 : Law1481.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1481
spectrum_assert exact_1481 complete

theorem exact_1482 : Law1482.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1482
spectrum_assert exact_1482 complete

-- UNKNOWN exact spectrum (PDF representative E1483).
theorem lower_1483 : (({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares)) ⊆ Law1483.spectrum := by
  rw [ImplicationTransfer.spectrum_1483_eq_1483]
  exact Note.lower_1483
spectrum_assert lower_1483 complete

theorem upper_1483 : Law1483.spectrum ⊆ (positiveExcept {3, 5, 6, 7}) := by
  rw [ImplicationTransfer.spectrum_1483_eq_1483]
  exact Note.upper_1483
spectrum_assert upper_1483 proofAvailable

theorem exact_1484 : Law1484.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1484
spectrum_assert exact_1484 complete

theorem exact_1485 : Law1485.spectrum = (squares ∪ twiceSquares) :=
  ImplicationTransfer.spectrum_1485_eq_1485 |>.trans Note.exact_1485
spectrum_assert exact_1485 complete

-- UNKNOWN exact spectrum (PDF representative E1486).
theorem lower_1486 : (({1, 11, 13, 21} : Set ℕ) ∪ (squares ∪ shiftedSquares)) ⊆ Law1486.spectrum := by
  rw [ImplicationTransfer.spectrum_1486_eq_1486]
  exact Note.lower_1486
spectrum_assert lower_1486 proofAvailable

theorem upper_1486 : Law1486.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_1486_eq_1486]
  exact Note.upper_1486
spectrum_assert upper_1486 complete

theorem exact_1487 : Law1487.spectrum = (squares) :=
  ImplicationTransfer.spectrum_1487_eq_168 |>.trans Note.exact_168
spectrum_assert exact_1487 complete

theorem exact_1488 : Law1488.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1488
spectrum_assert exact_1488 complete

-- UNKNOWN exact spectrum (PDF representative E1489).
theorem lower_1489 : (({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ)) ⊆ Law1489.spectrum := by
  rw [ImplicationTransfer.spectrum_1489_eq_1489]
  exact Note.lower_1489
spectrum_assert lower_1489 proofAvailable

theorem upper_1489 : Law1489.spectrum ⊆ (positiveExcept {2, 4}) := by
  rw [ImplicationTransfer.spectrum_1489_eq_1489]
  exact Note.upper_1489
spectrum_assert upper_1489 proofAvailable

theorem cofinite_1489 : CofiniteSpectrum Law1489 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1489_eq_1489]
  exact Note.cofinite_1489
spectrum_assert cofinite_1489 noteGap

theorem exact_1490 : Law1490.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1490
spectrum_assert exact_1490 complete

theorem exact_1491 : Law1491.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1491
spectrum_assert exact_1491 complete

theorem exact_1492 : Law1492.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1492
spectrum_assert exact_1492 complete

theorem exact_1493 : Law1493.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1493
spectrum_assert exact_1493 complete

theorem exact_1494 : Law1494.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1494
spectrum_assert exact_1494 complete

theorem exact_1495 : Law1495.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1495
spectrum_assert exact_1495 complete

-- UNKNOWN exact spectrum (PDF representative E1496).
theorem lower_1496 : (({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law1496.spectrum := by
  rw [ImplicationTransfer.spectrum_1496_eq_1496]
  exact Note.lower_1496
spectrum_assert lower_1496 proofAvailable

theorem upper_1496 : Law1496.spectrum ⊆ (positiveExcept {3, 6}) := by
  rw [ImplicationTransfer.spectrum_1496_eq_1496]
  exact Note.upper_1496
spectrum_assert upper_1496 proofAvailable

theorem exact_1497 : Law1497.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1497
spectrum_assert exact_1497 complete

theorem exact_1498 : Law1498.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1498
spectrum_assert exact_1498 complete

theorem exact_1499 : Law1499.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1499
spectrum_assert exact_1499 complete

theorem exact_1500 : Law1500.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1500
spectrum_assert exact_1500 complete

theorem exact_1501 : Law1501.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1501
spectrum_assert exact_1501 complete

theorem exact_1502 : Law1502.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1502
spectrum_assert exact_1502 complete

theorem exact_1503 : Law1503.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1503
spectrum_assert exact_1503 complete

theorem exact_1504 : Law1504.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1504
spectrum_assert exact_1504 complete

theorem exact_1505 : Law1505.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1505
spectrum_assert exact_1505 complete

theorem exact_1506 : Law1506.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1506
spectrum_assert exact_1506 complete

theorem exact_1507 : Law1507.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1507
spectrum_assert exact_1507 complete

theorem exact_1508 : Law1508.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1508
spectrum_assert exact_1508 complete

theorem exact_1509 : Law1509.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1509
spectrum_assert exact_1509 complete

theorem exact_1510 : Law1510.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1510
spectrum_assert exact_1510 complete

theorem exact_1511 : Law1511.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1511
spectrum_assert exact_1511 complete

theorem exact_1512 : Law1512.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1512
spectrum_assert exact_1512 complete

theorem exact_1513 : Law1513.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1513
spectrum_assert exact_1513 complete

theorem exact_1514 : Law1514.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1514
spectrum_assert exact_1514 complete

theorem exact_1515 : Law1515.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1515
spectrum_assert exact_1515 complete

-- UNKNOWN exact spectrum (PDF representative E1516).
theorem lower_1516 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law1516.spectrum := by
  rw [ImplicationTransfer.spectrum_1516_eq_1516]
  exact Note.lower_1516
spectrum_assert lower_1516 complete

theorem upper_1516 : Law1516.spectrum ⊆ (positiveExcept {2, 3, 4, 6}) := by
  rw [ImplicationTransfer.spectrum_1516_eq_1516]
  exact Note.upper_1516
spectrum_assert upper_1516 proofAvailable

theorem cofinite_1516 : CofiniteSpectrum Law1516 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1516_eq_1516]
  exact Note.cofinite_1516
spectrum_assert cofinite_1516 proofAvailable

theorem exact_1517 : Law1517.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1517
spectrum_assert exact_1517 complete

theorem exact_1518 : Law1518.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1518
spectrum_assert exact_1518 complete

theorem exact_1519 : Law1519.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1519
spectrum_assert exact_1519 complete

theorem exact_1520 : Law1520.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1520
spectrum_assert exact_1520 complete

theorem exact_1521 : Law1521.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1521
spectrum_assert exact_1521 complete

theorem exact_1522 : Law1522.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1522
spectrum_assert exact_1522 complete

theorem exact_1523 : Law1523.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1523
spectrum_assert exact_1523 complete

theorem exact_1524 : Law1524.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1524
spectrum_assert exact_1524 complete

theorem exact_1525 : Law1525.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1525
spectrum_assert exact_1525 complete

-- UNKNOWN exact spectrum (PDF representative E1526).
theorem lower_1526 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law1526.spectrum := by
  rw [ImplicationTransfer.spectrum_1526_eq_1526]
  exact Note.lower_1526
spectrum_assert lower_1526 proofAvailable

theorem upper_1526 : Law1526.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_1526_eq_1526]
  exact Note.upper_1526
spectrum_assert upper_1526 complete

theorem cofinite_1526 : CofiniteSpectrum Law1526 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1526_eq_1526]
  exact Note.cofinite_1526
spectrum_assert cofinite_1526 proofAvailable

theorem exact_1527 : Law1527.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1527
spectrum_assert exact_1527 complete

theorem exact_1528 : Law1528.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1528
spectrum_assert exact_1528 complete

theorem exact_1529 : Law1529.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1529
spectrum_assert exact_1529 complete

theorem exact_1530 : Law1530.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1530
spectrum_assert exact_1530 complete

theorem exact_1531 : Law1531.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1531
spectrum_assert exact_1531 complete

theorem exact_1532 : Law1532.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1532
spectrum_assert exact_1532 complete

theorem exact_1533 : Law1533.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1533
spectrum_assert exact_1533 complete

theorem exact_1534 : Law1534.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1534
spectrum_assert exact_1534 complete

theorem exact_1535 : Law1535.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1535
spectrum_assert exact_1535 complete

theorem exact_1536 : Law1536.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1536
spectrum_assert exact_1536 complete

theorem exact_1537 : Law1537.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_1537_eq_887 |>.trans Note.exact_887
spectrum_assert exact_1537 complete

theorem exact_1538 : Law1538.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1538
spectrum_assert exact_1538 complete

theorem exact_1539 : Law1539.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1539
spectrum_assert exact_1539 complete

theorem exact_1540 : Law1540.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1540
spectrum_assert exact_1540 complete

theorem exact_1541 : Law1541.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1541
spectrum_assert exact_1541 complete

theorem exact_1542 : Law1542.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1542
spectrum_assert exact_1542 complete

theorem exact_1543 : Law1543.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1543
spectrum_assert exact_1543 complete

theorem exact_1544 : Law1544.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1544
spectrum_assert exact_1544 complete

theorem exact_1545 : Law1545.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1545
spectrum_assert exact_1545 complete

theorem exact_1546 : Law1546.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1546
spectrum_assert exact_1546 complete

theorem exact_1547 : Law1547.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1547
spectrum_assert exact_1547 complete

theorem exact_1548 : Law1548.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1548
spectrum_assert exact_1548 complete

theorem exact_1549 : Law1549.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1549
spectrum_assert exact_1549 complete

theorem exact_1550 : Law1550.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1550
spectrum_assert exact_1550 complete

theorem exact_1551 : Law1551.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1551
spectrum_assert exact_1551 complete

theorem exact_1552 : Law1552.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1552
spectrum_assert exact_1552 complete

theorem exact_1553 : Law1553.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1553
spectrum_assert exact_1553 complete

theorem exact_1554 : Law1554.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1554
spectrum_assert exact_1554 complete

theorem exact_1555 : Law1555.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1555
spectrum_assert exact_1555 complete

theorem exact_1556 : Law1556.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1556
spectrum_assert exact_1556 complete

theorem exact_1557 : Law1557.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1557
spectrum_assert exact_1557 complete

theorem exact_1558 : Law1558.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1558
spectrum_assert exact_1558 complete

theorem exact_1559 : Law1559.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1559
spectrum_assert exact_1559 complete

theorem exact_1560 : Law1560.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1560
spectrum_assert exact_1560 complete

theorem exact_1561 : Law1561.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1561
spectrum_assert exact_1561 complete

theorem exact_1562 : Law1562.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1562
spectrum_assert exact_1562 complete

theorem exact_1563 : Law1563.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1563
spectrum_assert exact_1563 complete

theorem exact_1564 : Law1564.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1564
spectrum_assert exact_1564 complete

theorem exact_1565 : Law1565.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1565
spectrum_assert exact_1565 complete

theorem exact_1566 : Law1566.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1566
spectrum_assert exact_1566 complete

theorem exact_1567 : Law1567.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1567
spectrum_assert exact_1567 complete

theorem exact_1568 : Law1568.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1568
spectrum_assert exact_1568 complete

theorem exact_1569 : Law1569.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1569
spectrum_assert exact_1569 complete

theorem exact_1570 : Law1570.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1570
spectrum_assert exact_1570 complete

theorem exact_1571 : Law1571.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_1571_eq_895 |>.trans Note.exact_895
spectrum_assert exact_1571 proofAvailable

theorem exact_1572 : Law1572.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1572
spectrum_assert exact_1572 complete

theorem exact_1573 : Law1573.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1573
spectrum_assert exact_1573 complete

theorem exact_1574 : Law1574.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1574
spectrum_assert exact_1574 complete

theorem exact_1575 : Law1575.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1575
spectrum_assert exact_1575 complete

theorem exact_1576 : Law1576.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1576
spectrum_assert exact_1576 complete

theorem exact_1577 : Law1577.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1577
spectrum_assert exact_1577 complete

theorem exact_1578 : Law1578.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1578
spectrum_assert exact_1578 complete

theorem exact_1579 : Law1579.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1579
spectrum_assert exact_1579 complete

theorem exact_1580 : Law1580.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1580
spectrum_assert exact_1580 complete

theorem exact_1581 : Law1581.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1581
spectrum_assert exact_1581 complete

theorem exact_1582 : Law1582.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1582
spectrum_assert exact_1582 complete

theorem exact_1583 : Law1583.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1583
spectrum_assert exact_1583 complete

theorem exact_1584 : Law1584.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1584
spectrum_assert exact_1584 complete

theorem exact_1585 : Law1585.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1585
spectrum_assert exact_1585 complete

theorem exact_1586 : Law1586.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1586
spectrum_assert exact_1586 complete

theorem exact_1587 : Law1587.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_1587_eq_898 |>.trans Note.exact_898
spectrum_assert exact_1587 noteGap

theorem exact_1588 : Law1588.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1588
spectrum_assert exact_1588 complete

theorem exact_1589 : Law1589.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1589
spectrum_assert exact_1589 complete

theorem exact_1590 : Law1590.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1590
spectrum_assert exact_1590 complete

theorem exact_1591 : Law1591.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1591
spectrum_assert exact_1591 complete

theorem exact_1592 : Law1592.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1592
spectrum_assert exact_1592 complete

theorem exact_1593 : Law1593.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1593
spectrum_assert exact_1593 complete

theorem exact_1594 : Law1594.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1594
spectrum_assert exact_1594 complete

theorem exact_1595 : Law1595.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1595
spectrum_assert exact_1595 complete

theorem exact_1596 : Law1596.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1596
spectrum_assert exact_1596 complete

theorem exact_1597 : Law1597.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1597
spectrum_assert exact_1597 complete

theorem exact_1598 : Law1598.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1598
spectrum_assert exact_1598 complete

theorem exact_1599 : Law1599.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1599
spectrum_assert exact_1599 complete

theorem exact_1600 : Law1600.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1600
spectrum_assert exact_1600 complete

theorem exact_1601 : Law1601.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1601
spectrum_assert exact_1601 complete

theorem exact_1602 : Law1602.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1602
spectrum_assert exact_1602 complete

theorem exact_1603 : Law1603.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1603
spectrum_assert exact_1603 complete

theorem exact_1604 : Law1604.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1604
spectrum_assert exact_1604 complete

theorem exact_1605 : Law1605.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1605
spectrum_assert exact_1605 complete

theorem exact_1606 : Law1606.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1606
spectrum_assert exact_1606 complete

theorem exact_1607 : Law1607.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1607
spectrum_assert exact_1607 complete

theorem exact_1608 : Law1608.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1608
spectrum_assert exact_1608 complete

theorem exact_1609 : Law1609.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1609
spectrum_assert exact_1609 complete

theorem exact_1610 : Law1610.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1610
spectrum_assert exact_1610 complete

theorem exact_1611 : Law1611.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1611
spectrum_assert exact_1611 complete

theorem exact_1612 : Law1612.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1612
spectrum_assert exact_1612 complete

theorem exact_1613 : Law1613.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1613
spectrum_assert exact_1613 complete

theorem exact_1614 : Law1614.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1614
spectrum_assert exact_1614 complete

theorem exact_1615 : Law1615.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1615
spectrum_assert exact_1615 complete

theorem exact_1616 : Law1616.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1616
spectrum_assert exact_1616 complete

theorem exact_1617 : Law1617.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1617
spectrum_assert exact_1617 complete

theorem exact_1618 : Law1618.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1618
spectrum_assert exact_1618 complete

theorem exact_1619 : Law1619.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1619
spectrum_assert exact_1619 complete

theorem exact_1620 : Law1620.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1620
spectrum_assert exact_1620 complete

theorem exact_1621 : Law1621.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1621
spectrum_assert exact_1621 complete

theorem exact_1622 : Law1622.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1622
spectrum_assert exact_1622 complete

theorem exact_1623 : Law1623.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1623
spectrum_assert exact_1623 complete

theorem exact_1624 : Law1624.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1624
spectrum_assert exact_1624 complete

theorem exact_1625 : Law1625.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1625
spectrum_assert exact_1625 complete

theorem exact_1626 : Law1626.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1626
spectrum_assert exact_1626 complete

theorem exact_1627 : Law1627.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1627
spectrum_assert exact_1627 complete

theorem exact_1628 : Law1628.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1628
spectrum_assert exact_1628 complete

theorem exact_1629 : Law1629.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1629
spectrum_assert exact_1629 complete

theorem exact_1630 : Law1630.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1630
spectrum_assert exact_1630 complete

theorem exact_1631 : Law1631.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1631
spectrum_assert exact_1631 complete

theorem exact_1632 : Law1632.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1632
spectrum_assert exact_1632 complete

theorem exact_1633 : Law1633.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1633
spectrum_assert exact_1633 complete

theorem exact_1634 : Law1634.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1634
spectrum_assert exact_1634 complete

theorem exact_1635 : Law1635.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1635
spectrum_assert exact_1635 complete

theorem exact_1636 : Law1636.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1636
spectrum_assert exact_1636 complete

theorem exact_1637 : Law1637.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1637
spectrum_assert exact_1637 complete

theorem exact_1638 : Law1638.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1638
spectrum_assert exact_1638 complete

theorem exact_1639 : Law1639.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1639
spectrum_assert exact_1639 complete

theorem exact_1640 : Law1640.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1640
spectrum_assert exact_1640 complete

theorem exact_1641 : Law1641.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1641
spectrum_assert exact_1641 complete

theorem exact_1642 : Law1642.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1642
spectrum_assert exact_1642 complete

theorem exact_1643 : Law1643.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1643
spectrum_assert exact_1643 complete

theorem exact_1644 : Law1644.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1644
spectrum_assert exact_1644 complete

theorem exact_1645 : Law1645.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1645
spectrum_assert exact_1645 complete

theorem exact_1646 : Law1646.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1646
spectrum_assert exact_1646 complete

theorem exact_1647 : Law1647.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1647
spectrum_assert exact_1647 complete

theorem exact_1648 : Law1648.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1648
spectrum_assert exact_1648 complete

theorem exact_1649 : Law1649.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1649
spectrum_assert exact_1649 complete

theorem exact_1650 : Law1650.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1650
spectrum_assert exact_1650 complete

theorem exact_1651 : Law1651.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1651
spectrum_assert exact_1651 complete

theorem exact_1652 : Law1652.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1652
spectrum_assert exact_1652 complete

theorem exact_1653 : Law1653.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1653
spectrum_assert exact_1653 complete

theorem exact_1654 : Law1654.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1654
spectrum_assert exact_1654 complete

theorem exact_1655 : Law1655.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1655
spectrum_assert exact_1655 complete

theorem exact_1656 : Law1656.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1656
spectrum_assert exact_1656 complete

theorem exact_1657 : Law1657.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1657
spectrum_assert exact_1657 complete

theorem exact_1658 : Law1658.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1658
spectrum_assert exact_1658 complete

theorem exact_1659 : Law1659.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1659
spectrum_assert exact_1659 complete

theorem exact_1660 : Law1660.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1660
spectrum_assert exact_1660 complete

theorem exact_1661 : Law1661.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1661
spectrum_assert exact_1661 complete

theorem exact_1662 : Law1662.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1662
spectrum_assert exact_1662 complete

theorem exact_1663 : Law1663.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1663
spectrum_assert exact_1663 complete

theorem exact_1664 : Law1664.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1664
spectrum_assert exact_1664 complete

theorem exact_1665 : Law1665.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1665
spectrum_assert exact_1665 complete

theorem exact_1666 : Law1666.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1666
spectrum_assert exact_1666 complete

theorem exact_1667 : Law1667.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1667
spectrum_assert exact_1667 complete

theorem exact_1668 : Law1668.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1668
spectrum_assert exact_1668 complete

theorem exact_1669 : Law1669.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1669
spectrum_assert exact_1669 complete

theorem exact_1670 : Law1670.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1670
spectrum_assert exact_1670 complete

theorem exact_1671 : Law1671.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1671
spectrum_assert exact_1671 complete

theorem exact_1672 : Law1672.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1672
spectrum_assert exact_1672 complete

theorem exact_1673 : Law1673.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1673
spectrum_assert exact_1673 complete

theorem exact_1674 : Law1674.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1674
spectrum_assert exact_1674 complete

theorem exact_1675 : Law1675.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1675
spectrum_assert exact_1675 complete

theorem exact_1676 : Law1676.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1676
spectrum_assert exact_1676 complete

theorem exact_1677 : Law1677.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1677
spectrum_assert exact_1677 complete

theorem exact_1678 : Law1678.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1678
spectrum_assert exact_1678 complete

theorem exact_1679 : Law1679.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1679
spectrum_assert exact_1679 complete

theorem exact_1680 : Law1680.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1680
spectrum_assert exact_1680 complete

theorem exact_1681 : Law1681.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1681
spectrum_assert exact_1681 complete

theorem exact_1682 : Law1682.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1682
spectrum_assert exact_1682 complete

theorem exact_1683 : Law1683.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1683
spectrum_assert exact_1683 complete

theorem exact_1684 : Law1684.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1684
spectrum_assert exact_1684 complete

theorem exact_1685 : Law1685.spectrum = (positiveExcept {2}) :=
  ImplicationTransfer.spectrum_1685_eq_1685 |>.trans Note.exact_1685
spectrum_assert exact_1685 complete

theorem exact_1686 : Law1686.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1686
spectrum_assert exact_1686 complete

theorem exact_1687 : Law1687.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1687
spectrum_assert exact_1687 complete

theorem exact_1688 : Law1688.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1688
spectrum_assert exact_1688 complete

theorem exact_1689 : Law1689.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1689
spectrum_assert exact_1689 complete

theorem exact_1690 : Law1690.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1690
spectrum_assert exact_1690 complete

theorem exact_1691 : Law1691.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1691
spectrum_assert exact_1691 complete

-- UNKNOWN exact spectrum (PDF representative E1692).
theorem lower_1692 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law1692.spectrum := by
  rw [ImplicationTransfer.spectrum_1692_eq_1692]
  exact Note.lower_1692
spectrum_assert lower_1692 complete

theorem upper_1692 : Law1692.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_1692_eq_1692]
  exact Note.upper_1692
spectrum_assert upper_1692 proofAvailable

theorem cofinite_1692 : CofiniteSpectrum Law1692 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1692_eq_1692]
  exact Note.cofinite_1692
spectrum_assert cofinite_1692 proofAvailable

theorem exact_1693 : Law1693.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1693
spectrum_assert exact_1693 complete

theorem exact_1694 : Law1694.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1694
spectrum_assert exact_1694 complete

theorem exact_1695 : Law1695.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1695
spectrum_assert exact_1695 complete

theorem exact_1696 : Law1696.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1696
spectrum_assert exact_1696 complete

theorem exact_1697 : Law1697.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1697
spectrum_assert exact_1697 complete

theorem exact_1698 : Law1698.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1698
spectrum_assert exact_1698 complete

theorem exact_1699 : Law1699.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1699
spectrum_assert exact_1699 complete

theorem exact_1700 : Law1700.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1700
spectrum_assert exact_1700 complete

theorem exact_1701 : Law1701.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1701
spectrum_assert exact_1701 complete

theorem exact_1702 : Law1702.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1702
spectrum_assert exact_1702 complete

theorem exact_1703 : Law1703.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1703
spectrum_assert exact_1703 complete

theorem exact_1704 : Law1704.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1704
spectrum_assert exact_1704 complete

theorem exact_1705 : Law1705.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1705
spectrum_assert exact_1705 complete

theorem exact_1706 : Law1706.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1706
spectrum_assert exact_1706 complete

theorem exact_1707 : Law1707.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1707
spectrum_assert exact_1707 complete

theorem exact_1708 : Law1708.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1708
spectrum_assert exact_1708 complete

theorem exact_1709 : Law1709.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1709
spectrum_assert exact_1709 complete

theorem exact_1710 : Law1710.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_1710_eq_695 |>.trans Note.exact_695
spectrum_assert exact_1710 complete

theorem exact_1711 : Law1711.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1711
spectrum_assert exact_1711 complete

theorem exact_1712 : Law1712.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1712
spectrum_assert exact_1712 complete

theorem exact_1713 : Law1713.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1713
spectrum_assert exact_1713 complete

theorem exact_1714 : Law1714.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1714
spectrum_assert exact_1714 complete

theorem exact_1715 : Law1715.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1715
spectrum_assert exact_1715 complete

theorem exact_1716 : Law1716.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1716
spectrum_assert exact_1716 complete

theorem exact_1717 : Law1717.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1717
spectrum_assert exact_1717 complete

theorem exact_1718 : Law1718.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1718
spectrum_assert exact_1718 complete

-- UNKNOWN exact spectrum (PDF representative E1719).
theorem lower_1719 : (({1, 5, 6, 8} : Set ℕ) ∪ (residues 3 {0, 1} ∅)) ⊆ Law1719.spectrum := by
  rw [ImplicationTransfer.spectrum_1719_eq_1719]
  exact Note.lower_1719
spectrum_assert lower_1719 proofAvailable

theorem upper_1719 : Law1719.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_1719_eq_1719]
  exact Note.upper_1719
spectrum_assert upper_1719 complete

theorem exact_1720 : Law1720.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1720
spectrum_assert exact_1720 complete

theorem exact_1721 : Law1721.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1721
spectrum_assert exact_1721 complete

theorem exact_1722 : Law1722.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1722
spectrum_assert exact_1722 complete

theorem exact_1723 : Law1723.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1723
spectrum_assert exact_1723 complete

theorem exact_1724 : Law1724.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1724
spectrum_assert exact_1724 complete

theorem exact_1725 : Law1725.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1725
spectrum_assert exact_1725 complete

theorem exact_1726 : Law1726.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1726
spectrum_assert exact_1726 complete

theorem exact_1727 : Law1727.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1727
spectrum_assert exact_1727 complete

theorem exact_1728 : Law1728.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1728
spectrum_assert exact_1728 complete

theorem exact_1729 : Law1729.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1729
spectrum_assert exact_1729 complete

theorem exact_1730 : Law1730.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1730
spectrum_assert exact_1730 complete

theorem exact_1731 : Law1731.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1731
spectrum_assert exact_1731 complete

theorem exact_1732 : Law1732.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1732
spectrum_assert exact_1732 complete

theorem exact_1733 : Law1733.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1733
spectrum_assert exact_1733 complete

theorem exact_1734 : Law1734.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1734
spectrum_assert exact_1734 complete

theorem exact_1735 : Law1735.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1735
spectrum_assert exact_1735 complete

theorem exact_1736 : Law1736.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1736
spectrum_assert exact_1736 complete

theorem exact_1737 : Law1737.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1737
spectrum_assert exact_1737 complete

theorem exact_1738 : Law1738.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1738
spectrum_assert exact_1738 complete

theorem exact_1739 : Law1739.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1739
spectrum_assert exact_1739 complete

theorem exact_1740 : Law1740.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1740
spectrum_assert exact_1740 complete

theorem exact_1741 : Law1741.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1741
spectrum_assert exact_1741 complete

theorem exact_1742 : Law1742.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1742
spectrum_assert exact_1742 complete

theorem exact_1743 : Law1743.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1743
spectrum_assert exact_1743 complete

theorem exact_1744 : Law1744.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1744
spectrum_assert exact_1744 complete

theorem exact_1745 : Law1745.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1745
spectrum_assert exact_1745 complete

theorem exact_1746 : Law1746.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1746
spectrum_assert exact_1746 complete

theorem exact_1747 : Law1747.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1747
spectrum_assert exact_1747 complete

theorem exact_1748 : Law1748.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1748
spectrum_assert exact_1748 complete

theorem exact_1749 : Law1749.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1749
spectrum_assert exact_1749 complete

theorem exact_1750 : Law1750.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1750
spectrum_assert exact_1750 complete

theorem exact_1751 : Law1751.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1751
spectrum_assert exact_1751 complete

theorem exact_1752 : Law1752.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1752
spectrum_assert exact_1752 complete

theorem exact_1753 : Law1753.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1753
spectrum_assert exact_1753 complete

theorem exact_1754 : Law1754.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1754
spectrum_assert exact_1754 complete

theorem exact_1755 : Law1755.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1755
spectrum_assert exact_1755 complete

theorem exact_1756 : Law1756.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1756
spectrum_assert exact_1756 complete

theorem exact_1757 : Law1757.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1757
spectrum_assert exact_1757 complete

theorem exact_1758 : Law1758.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1758
spectrum_assert exact_1758 complete

theorem exact_1759 : Law1759.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1759
spectrum_assert exact_1759 complete

theorem exact_1760 : Law1760.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1760
spectrum_assert exact_1760 complete

theorem exact_1761 : Law1761.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1761
spectrum_assert exact_1761 complete

theorem exact_1762 : Law1762.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1762
spectrum_assert exact_1762 complete

theorem exact_1763 : Law1763.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1763
spectrum_assert exact_1763 complete

theorem exact_1764 : Law1764.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1764_eq_546 |>.trans Note.exact_546
spectrum_assert exact_1764 complete

theorem exact_1765 : Law1765.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1765
spectrum_assert exact_1765 complete

theorem exact_1766 : Law1766.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1766
spectrum_assert exact_1766 complete

theorem exact_1767 : Law1767.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1767
spectrum_assert exact_1767 complete

theorem exact_1768 : Law1768.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1768
spectrum_assert exact_1768 complete

theorem exact_1769 : Law1769.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1769
spectrum_assert exact_1769 complete

theorem exact_1770 : Law1770.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1770
spectrum_assert exact_1770 complete

theorem exact_1771 : Law1771.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1771
spectrum_assert exact_1771 complete

theorem exact_1772 : Law1772.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1772
spectrum_assert exact_1772 complete

theorem exact_1773 : Law1773.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1773
spectrum_assert exact_1773 complete

theorem exact_1774 : Law1774.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1774
spectrum_assert exact_1774 complete

theorem exact_1775 : Law1775.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1775
spectrum_assert exact_1775 complete

theorem exact_1776 : Law1776.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1776
spectrum_assert exact_1776 complete

theorem exact_1777 : Law1777.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1777
spectrum_assert exact_1777 complete

theorem exact_1778 : Law1778.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1778
spectrum_assert exact_1778 complete

theorem exact_1779 : Law1779.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1779
spectrum_assert exact_1779 complete

theorem exact_1780 : Law1780.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1780
spectrum_assert exact_1780 complete

theorem exact_1781 : Law1781.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1781
spectrum_assert exact_1781 complete

theorem exact_1782 : Law1782.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1782
spectrum_assert exact_1782 complete

theorem exact_1783 : Law1783.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1783
spectrum_assert exact_1783 complete

theorem exact_1784 : Law1784.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1784
spectrum_assert exact_1784 complete

theorem exact_1785 : Law1785.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1785
spectrum_assert exact_1785 complete

theorem exact_1786 : Law1786.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1786
spectrum_assert exact_1786 complete

theorem exact_1787 : Law1787.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1787
spectrum_assert exact_1787 complete

theorem exact_1788 : Law1788.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1788
spectrum_assert exact_1788 complete

theorem exact_1789 : Law1789.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1789
spectrum_assert exact_1789 complete

theorem exact_1790 : Law1790.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1790_eq_546 |>.trans Note.exact_546
spectrum_assert exact_1790 complete

theorem exact_1791 : Law1791.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1791
spectrum_assert exact_1791 complete

theorem exact_1792 : Law1792.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1792
spectrum_assert exact_1792 complete

theorem exact_1793 : Law1793.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1793
spectrum_assert exact_1793 complete

theorem exact_1794 : Law1794.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1794
spectrum_assert exact_1794 complete

theorem exact_1795 : Law1795.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1795
spectrum_assert exact_1795 complete

theorem exact_1796 : Law1796.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1796
spectrum_assert exact_1796 complete

theorem exact_1797 : Law1797.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1797
spectrum_assert exact_1797 complete

theorem exact_1798 : Law1798.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1798
spectrum_assert exact_1798 complete

theorem exact_1799 : Law1799.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1799
spectrum_assert exact_1799 complete

theorem exact_1800 : Law1800.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1800
spectrum_assert exact_1800 complete

theorem exact_1801 : Law1801.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1801
spectrum_assert exact_1801 complete

theorem exact_1802 : Law1802.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1802
spectrum_assert exact_1802 complete

theorem exact_1803 : Law1803.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1803
spectrum_assert exact_1803 complete

theorem exact_1804 : Law1804.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1804
spectrum_assert exact_1804 complete

theorem exact_1805 : Law1805.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1805
spectrum_assert exact_1805 complete

theorem exact_1806 : Law1806.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1806
spectrum_assert exact_1806 complete

theorem exact_1807 : Law1807.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1807
spectrum_assert exact_1807 complete

theorem exact_1808 : Law1808.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1808
spectrum_assert exact_1808 complete

theorem exact_1809 : Law1809.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1809
spectrum_assert exact_1809 complete

theorem exact_1810 : Law1810.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1810
spectrum_assert exact_1810 complete

theorem exact_1811 : Law1811.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1811
spectrum_assert exact_1811 complete

theorem exact_1812 : Law1812.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1812
spectrum_assert exact_1812 complete

theorem exact_1813 : Law1813.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1813
spectrum_assert exact_1813 complete

theorem exact_1814 : Law1814.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1814
spectrum_assert exact_1814 complete

theorem exact_1815 : Law1815.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1815
spectrum_assert exact_1815 complete

theorem exact_1816 : Law1816.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1816
spectrum_assert exact_1816 complete

theorem exact_1817 : Law1817.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1817
spectrum_assert exact_1817 complete

theorem exact_1818 : Law1818.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1818
spectrum_assert exact_1818 complete

theorem exact_1819 : Law1819.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1819
spectrum_assert exact_1819 complete

theorem exact_1820 : Law1820.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1820
spectrum_assert exact_1820 complete

theorem exact_1821 : Law1821.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1821
spectrum_assert exact_1821 complete

theorem exact_1822 : Law1822.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1822
spectrum_assert exact_1822 complete

theorem exact_1823 : Law1823.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1823
spectrum_assert exact_1823 complete

theorem exact_1824 : Law1824.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1824
spectrum_assert exact_1824 complete

theorem exact_1825 : Law1825.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1825
spectrum_assert exact_1825 complete

theorem exact_1826 : Law1826.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1826
spectrum_assert exact_1826 complete

theorem exact_1827 : Law1827.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1827
spectrum_assert exact_1827 complete

theorem exact_1828 : Law1828.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1828
spectrum_assert exact_1828 complete

theorem exact_1829 : Law1829.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1829
spectrum_assert exact_1829 complete

theorem exact_1830 : Law1830.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1830
spectrum_assert exact_1830 complete

theorem exact_1831 : Law1831.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1831
spectrum_assert exact_1831 complete

theorem exact_1832 : Law1832.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1832
spectrum_assert exact_1832 complete

theorem exact_1833 : Law1833.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1833
spectrum_assert exact_1833 complete

theorem exact_1834 : Law1834.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1834
spectrum_assert exact_1834 complete

theorem exact_1835 : Law1835.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1835
spectrum_assert exact_1835 complete

theorem exact_1836 : Law1836.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1836
spectrum_assert exact_1836 complete

theorem exact_1837 : Law1837.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1837
spectrum_assert exact_1837 complete

theorem exact_1838 : Law1838.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1838
spectrum_assert exact_1838 complete

theorem exact_1839 : Law1839.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1839
spectrum_assert exact_1839 complete

theorem exact_1840 : Law1840.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1840
spectrum_assert exact_1840 complete

theorem exact_1841 : Law1841.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1841
spectrum_assert exact_1841 complete

theorem exact_1842 : Law1842.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1842
spectrum_assert exact_1842 complete

theorem exact_1843 : Law1843.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1843
spectrum_assert exact_1843 complete

theorem exact_1844 : Law1844.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1844
spectrum_assert exact_1844 complete

theorem exact_1845 : Law1845.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1845
spectrum_assert exact_1845 complete

theorem exact_1846 : Law1846.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1846
spectrum_assert exact_1846 complete

theorem exact_1847 : Law1847.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1847
spectrum_assert exact_1847 complete

theorem exact_1848 : Law1848.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1848
spectrum_assert exact_1848 complete

theorem exact_1849 : Law1849.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1849
spectrum_assert exact_1849 complete

theorem exact_1850 : Law1850.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1850
spectrum_assert exact_1850 complete

theorem exact_1851 : Law1851.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1851
spectrum_assert exact_1851 complete

theorem exact_1852 : Law1852.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1852
spectrum_assert exact_1852 complete

theorem exact_1853 : Law1853.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1853
spectrum_assert exact_1853 complete

theorem exact_1854 : Law1854.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1854
spectrum_assert exact_1854 complete

theorem exact_1855 : Law1855.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1855
spectrum_assert exact_1855 complete

theorem exact_1856 : Law1856.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1856
spectrum_assert exact_1856 complete

theorem exact_1857 : Law1857.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1857
spectrum_assert exact_1857 complete

theorem exact_1858 : Law1858.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1858
spectrum_assert exact_1858 complete

theorem exact_1859 : Law1859.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1859
spectrum_assert exact_1859 complete

theorem exact_1860 : Law1860.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1860
spectrum_assert exact_1860 complete

theorem exact_1861 : Law1861.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1861
spectrum_assert exact_1861 complete

theorem exact_1862 : Law1862.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1862
spectrum_assert exact_1862 complete

theorem exact_1863 : Law1863.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1863
spectrum_assert exact_1863 complete

theorem exact_1864 : Law1864.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1864
spectrum_assert exact_1864 complete

theorem exact_1865 : Law1865.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1865
spectrum_assert exact_1865 complete

theorem exact_1866 : Law1866.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1866
spectrum_assert exact_1866 complete

theorem exact_1867 : Law1867.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1867
spectrum_assert exact_1867 complete

theorem exact_1868 : Law1868.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1868
spectrum_assert exact_1868 complete

theorem exact_1869 : Law1869.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1869
spectrum_assert exact_1869 complete

theorem exact_1870 : Law1870.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1870
spectrum_assert exact_1870 complete

theorem exact_1871 : Law1871.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1871
spectrum_assert exact_1871 complete

theorem exact_1872 : Law1872.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1872
spectrum_assert exact_1872 complete

theorem exact_1873 : Law1873.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1873
spectrum_assert exact_1873 complete

theorem exact_1874 : Law1874.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1874
spectrum_assert exact_1874 complete

theorem exact_1875 : Law1875.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1875
spectrum_assert exact_1875 complete

theorem exact_1876 : Law1876.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1876
spectrum_assert exact_1876 complete

theorem exact_1877 : Law1877.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1877
spectrum_assert exact_1877 complete

theorem exact_1878 : Law1878.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1878
spectrum_assert exact_1878 complete

theorem exact_1879 : Law1879.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1879
spectrum_assert exact_1879 complete

theorem exact_1880 : Law1880.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1880
spectrum_assert exact_1880 complete

theorem exact_1881 : Law1881.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1881
spectrum_assert exact_1881 complete

theorem exact_1882 : Law1882.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1882
spectrum_assert exact_1882 complete

theorem exact_1883 : Law1883.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1883
spectrum_assert exact_1883 complete

theorem exact_1884 : Law1884.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1884
spectrum_assert exact_1884 complete

theorem exact_1885 : Law1885.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1885
spectrum_assert exact_1885 complete

theorem exact_1886 : Law1886.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1886
spectrum_assert exact_1886 complete

theorem exact_1887 : Law1887.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1887
spectrum_assert exact_1887 complete

-- UNKNOWN exact spectrum (PDF representative E1719).
theorem lower_1888 : (({1, 5, 6, 8} : Set ℕ) ∪ (residues 3 {0, 1} ∅)) ⊆ Law1888.spectrum := by
  rw [ImplicationTransfer.spectrum_1888_eq_1719]
  exact Note.lower_1719
spectrum_assert lower_1888 proofAvailable

theorem upper_1888 : Law1888.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_1888_eq_1719]
  exact Note.upper_1719
spectrum_assert upper_1888 complete

theorem exact_1889 : Law1889.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1889
spectrum_assert exact_1889 complete

theorem exact_1890 : Law1890.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1890
spectrum_assert exact_1890 complete

theorem exact_1891 : Law1891.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1891
spectrum_assert exact_1891 complete

theorem exact_1892 : Law1892.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1892
spectrum_assert exact_1892 complete

theorem exact_1893 : Law1893.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1893
spectrum_assert exact_1893 complete

theorem exact_1894 : Law1894.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1894
spectrum_assert exact_1894 complete

-- UNKNOWN exact spectrum (PDF representative E1692).
theorem lower_1895 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law1895.spectrum := by
  rw [ImplicationTransfer.spectrum_1895_eq_1692]
  exact Note.lower_1692
spectrum_assert lower_1895 complete

theorem upper_1895 : Law1895.spectrum ⊆ (positiveExcept {2, 6, 10}) := by
  rw [ImplicationTransfer.spectrum_1895_eq_1692]
  exact Note.upper_1692
spectrum_assert upper_1895 proofAvailable

theorem cofinite_1895 : CofiniteSpectrum Law1895 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_1895_eq_1692]
  exact Note.cofinite_1692
spectrum_assert cofinite_1895 proofAvailable

theorem exact_1896 : Law1896.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1896
spectrum_assert exact_1896 complete

theorem exact_1897 : Law1897.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1897
spectrum_assert exact_1897 complete

theorem exact_1898 : Law1898.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1898
spectrum_assert exact_1898 complete

theorem exact_1899 : Law1899.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1899
spectrum_assert exact_1899 complete

theorem exact_1900 : Law1900.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1900
spectrum_assert exact_1900 complete

theorem exact_1901 : Law1901.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1901
spectrum_assert exact_1901 complete

theorem exact_1902 : Law1902.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1902
spectrum_assert exact_1902 complete

theorem exact_1903 : Law1903.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1903
spectrum_assert exact_1903 complete

theorem exact_1904 : Law1904.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1904
spectrum_assert exact_1904 complete

theorem exact_1905 : Law1905.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1905
spectrum_assert exact_1905 complete

theorem exact_1906 : Law1906.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1906
spectrum_assert exact_1906 complete

theorem exact_1907 : Law1907.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1907
spectrum_assert exact_1907 complete

theorem exact_1908 : Law1908.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1908
spectrum_assert exact_1908 complete

theorem exact_1909 : Law1909.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1909
spectrum_assert exact_1909 complete

theorem exact_1910 : Law1910.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1910
spectrum_assert exact_1910 complete

theorem exact_1911 : Law1911.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1911
spectrum_assert exact_1911 complete

theorem exact_1912 : Law1912.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1912
spectrum_assert exact_1912 complete

theorem exact_1913 : Law1913.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1913_eq_546 |>.trans Note.exact_546
spectrum_assert exact_1913 complete

theorem exact_1914 : Law1914.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1914
spectrum_assert exact_1914 complete

theorem exact_1915 : Law1915.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1915
spectrum_assert exact_1915 complete

theorem exact_1916 : Law1916.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1916
spectrum_assert exact_1916 complete

theorem exact_1917 : Law1917.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1917
spectrum_assert exact_1917 complete

theorem exact_1918 : Law1918.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1918
spectrum_assert exact_1918 complete

theorem exact_1919 : Law1919.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1919
spectrum_assert exact_1919 complete

theorem exact_1920 : Law1920.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1920
spectrum_assert exact_1920 complete

theorem exact_1921 : Law1921.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1921
spectrum_assert exact_1921 complete

theorem exact_1922 : Law1922.spectrum = (positiveExcept {2}) :=
  ImplicationTransfer.spectrum_1922_eq_1685 |>.trans Note.exact_1685
spectrum_assert exact_1922 complete

theorem exact_1923 : Law1923.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1923
spectrum_assert exact_1923 complete

theorem exact_1924 : Law1924.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1924
spectrum_assert exact_1924 complete

theorem exact_1925 : Law1925.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1925
spectrum_assert exact_1925 complete

theorem exact_1926 : Law1926.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1926
spectrum_assert exact_1926 complete

theorem exact_1927 : Law1927.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1927
spectrum_assert exact_1927 complete

theorem exact_1928 : Law1928.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1928
spectrum_assert exact_1928 complete

theorem exact_1929 : Law1929.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1929
spectrum_assert exact_1929 complete

theorem exact_1930 : Law1930.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1930
spectrum_assert exact_1930 complete

theorem exact_1931 : Law1931.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1931
spectrum_assert exact_1931 complete

theorem exact_1932 : Law1932.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1932
spectrum_assert exact_1932 complete

theorem exact_1933 : Law1933.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1933
spectrum_assert exact_1933 complete

theorem exact_1934 : Law1934.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1934
spectrum_assert exact_1934 complete

theorem exact_1935 : Law1935.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1935
spectrum_assert exact_1935 complete

theorem exact_1936 : Law1936.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1936
spectrum_assert exact_1936 complete

theorem exact_1937 : Law1937.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1937
spectrum_assert exact_1937 complete

theorem exact_1938 : Law1938.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1938
spectrum_assert exact_1938 complete

theorem exact_1939 : Law1939.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1939
spectrum_assert exact_1939 complete

theorem exact_1940 : Law1940.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1940
spectrum_assert exact_1940 complete

theorem exact_1941 : Law1941.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1941
spectrum_assert exact_1941 complete

theorem exact_1942 : Law1942.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1942
spectrum_assert exact_1942 complete

theorem exact_1943 : Law1943.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1943
spectrum_assert exact_1943 complete

theorem exact_1944 : Law1944.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1944
spectrum_assert exact_1944 complete

theorem exact_1945 : Law1945.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1945
spectrum_assert exact_1945 complete

theorem exact_1946 : Law1946.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1946
spectrum_assert exact_1946 complete

theorem exact_1947 : Law1947.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1947
spectrum_assert exact_1947 complete

theorem exact_1948 : Law1948.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1948
spectrum_assert exact_1948 complete

theorem exact_1949 : Law1949.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1949
spectrum_assert exact_1949 complete

theorem exact_1950 : Law1950.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1950
spectrum_assert exact_1950 complete

theorem exact_1951 : Law1951.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1951
spectrum_assert exact_1951 complete

theorem exact_1952 : Law1952.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1952
spectrum_assert exact_1952 complete

theorem exact_1953 : Law1953.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1953
spectrum_assert exact_1953 complete

theorem exact_1954 : Law1954.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1954
spectrum_assert exact_1954 complete

theorem exact_1955 : Law1955.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1955
spectrum_assert exact_1955 complete

theorem exact_1956 : Law1956.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1956
spectrum_assert exact_1956 complete

theorem exact_1957 : Law1957.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1957
spectrum_assert exact_1957 complete

theorem exact_1958 : Law1958.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1958
spectrum_assert exact_1958 complete

theorem exact_1959 : Law1959.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1959
spectrum_assert exact_1959 complete

theorem exact_1960 : Law1960.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1960
spectrum_assert exact_1960 complete

theorem exact_1961 : Law1961.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1961
spectrum_assert exact_1961 complete

theorem exact_1962 : Law1962.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1962
spectrum_assert exact_1962 complete

theorem exact_1963 : Law1963.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1963
spectrum_assert exact_1963 complete

theorem exact_1964 : Law1964.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1964
spectrum_assert exact_1964 complete

theorem exact_1965 : Law1965.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1965
spectrum_assert exact_1965 complete

theorem exact_1966 : Law1966.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1966
spectrum_assert exact_1966 complete

theorem exact_1967 : Law1967.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_1967_eq_546 |>.trans Note.exact_546
spectrum_assert exact_1967 complete

theorem exact_1968 : Law1968.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1968
spectrum_assert exact_1968 complete

theorem exact_1969 : Law1969.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1969
spectrum_assert exact_1969 complete

theorem exact_1970 : Law1970.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1970
spectrum_assert exact_1970 complete

theorem exact_1971 : Law1971.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1971
spectrum_assert exact_1971 complete

theorem exact_1972 : Law1972.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1972
spectrum_assert exact_1972 complete

theorem exact_1973 : Law1973.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1973
spectrum_assert exact_1973 complete

theorem exact_1974 : Law1974.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1974
spectrum_assert exact_1974 complete

theorem exact_1975 : Law1975.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1975
spectrum_assert exact_1975 complete

theorem exact_1976 : Law1976.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1976
spectrum_assert exact_1976 complete

theorem exact_1977 : Law1977.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1977
spectrum_assert exact_1977 complete

theorem exact_1978 : Law1978.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1978
spectrum_assert exact_1978 complete

theorem exact_1979 : Law1979.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1979
spectrum_assert exact_1979 complete

theorem exact_1980 : Law1980.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1980
spectrum_assert exact_1980 complete

theorem exact_1981 : Law1981.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1981
spectrum_assert exact_1981 complete

theorem exact_1982 : Law1982.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1982
spectrum_assert exact_1982 complete

theorem exact_1983 : Law1983.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1983
spectrum_assert exact_1983 complete

theorem exact_1984 : Law1984.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1984
spectrum_assert exact_1984 complete

theorem exact_1985 : Law1985.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1985
spectrum_assert exact_1985 complete

theorem exact_1986 : Law1986.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1986
spectrum_assert exact_1986 complete

theorem exact_1987 : Law1987.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1987
spectrum_assert exact_1987 complete

theorem exact_1988 : Law1988.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1988
spectrum_assert exact_1988 complete

theorem exact_1989 : Law1989.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1989
spectrum_assert exact_1989 complete

theorem exact_1990 : Law1990.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1990
spectrum_assert exact_1990 complete

theorem exact_1991 : Law1991.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1991
spectrum_assert exact_1991 complete

theorem exact_1992 : Law1992.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1992
spectrum_assert exact_1992 complete

theorem exact_1993 : Law1993.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_1993_eq_695 |>.trans Note.exact_695
spectrum_assert exact_1993 complete

theorem exact_1994 : Law1994.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1994
spectrum_assert exact_1994 complete

theorem exact_1995 : Law1995.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1995
spectrum_assert exact_1995 complete

theorem exact_1996 : Law1996.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_1996
spectrum_assert exact_1996 complete

theorem exact_1997 : Law1997.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1997
spectrum_assert exact_1997 complete

theorem exact_1998 : Law1998.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1998
spectrum_assert exact_1998 complete

theorem exact_1999 : Law1999.spectrum = ({1}) :=
  ImplicationTransfer.singleton_1999
spectrum_assert exact_1999 complete

theorem exact_2000 : Law2000.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2000
spectrum_assert exact_2000 complete

theorem exact_2001 : Law2001.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2001
spectrum_assert exact_2001 complete

theorem exact_2002 : Law2002.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2002
spectrum_assert exact_2002 complete

theorem exact_2003 : Law2003.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2003
spectrum_assert exact_2003 complete

theorem exact_2004 : Law2004.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2004
spectrum_assert exact_2004 complete

theorem exact_2005 : Law2005.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2005
spectrum_assert exact_2005 complete

theorem exact_2006 : Law2006.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2006
spectrum_assert exact_2006 complete

theorem exact_2007 : Law2007.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2007
spectrum_assert exact_2007 complete

theorem exact_2008 : Law2008.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2008
spectrum_assert exact_2008 complete

theorem exact_2009 : Law2009.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2009
spectrum_assert exact_2009 complete

theorem exact_2010 : Law2010.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2010
spectrum_assert exact_2010 complete

theorem exact_2011 : Law2011.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2011
spectrum_assert exact_2011 complete

theorem exact_2012 : Law2012.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2012
spectrum_assert exact_2012 complete

theorem exact_2013 : Law2013.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2013
spectrum_assert exact_2013 complete

theorem exact_2014 : Law2014.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2014
spectrum_assert exact_2014 complete

theorem exact_2015 : Law2015.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2015
spectrum_assert exact_2015 complete

theorem exact_2016 : Law2016.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2016
spectrum_assert exact_2016 complete

theorem exact_2017 : Law2017.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2017
spectrum_assert exact_2017 complete

theorem exact_2018 : Law2018.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2018
spectrum_assert exact_2018 complete

theorem exact_2019 : Law2019.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2019
spectrum_assert exact_2019 complete

theorem exact_2020 : Law2020.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2020
spectrum_assert exact_2020 complete

theorem exact_2021 : Law2021.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2021
spectrum_assert exact_2021 complete

theorem exact_2022 : Law2022.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2022
spectrum_assert exact_2022 complete

theorem exact_2023 : Law2023.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2023
spectrum_assert exact_2023 complete

theorem exact_2024 : Law2024.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2024
spectrum_assert exact_2024 complete

theorem exact_2025 : Law2025.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2025
spectrum_assert exact_2025 complete

theorem exact_2026 : Law2026.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2026
spectrum_assert exact_2026 complete

theorem exact_2027 : Law2027.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2027
spectrum_assert exact_2027 complete

theorem exact_2028 : Law2028.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2028
spectrum_assert exact_2028 complete

theorem exact_2029 : Law2029.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2029
spectrum_assert exact_2029 complete

theorem exact_2030 : Law2030.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2030
spectrum_assert exact_2030 complete

theorem exact_2031 : Law2031.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2031
spectrum_assert exact_2031 complete

theorem exact_2032 : Law2032.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2032
spectrum_assert exact_2032 complete

theorem exact_2033 : Law2033.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2033
spectrum_assert exact_2033 complete

theorem exact_2034 : Law2034.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2034
spectrum_assert exact_2034 complete

theorem exact_2035 : Law2035.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2035
spectrum_assert exact_2035 complete

theorem exact_2036 : Law2036.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2036
spectrum_assert exact_2036 complete

theorem exact_2037 : Law2037.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2037
spectrum_assert exact_2037 complete

theorem exact_2038 : Law2038.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2038
spectrum_assert exact_2038 complete

theorem exact_2039 : Law2039.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2039
spectrum_assert exact_2039 complete

theorem exact_2040 : Law2040.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2040
spectrum_assert exact_2040 complete

theorem exact_2041 : Law2041.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2041
spectrum_assert exact_2041 complete

theorem exact_2042 : Law2042.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2042
spectrum_assert exact_2042 complete

theorem exact_2043 : Law2043.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2043
spectrum_assert exact_2043 complete

theorem exact_2044 : Law2044.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2044
spectrum_assert exact_2044 complete

theorem exact_2045 : Law2045.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2045
spectrum_assert exact_2045 complete

theorem exact_2046 : Law2046.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2046
spectrum_assert exact_2046 complete

theorem exact_2047 : Law2047.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2047
spectrum_assert exact_2047 complete

theorem exact_2048 : Law2048.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2048
spectrum_assert exact_2048 complete

theorem exact_2049 : Law2049.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2049
spectrum_assert exact_2049 complete

theorem exact_2050 : Law2050.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2050
spectrum_assert exact_2050 complete

theorem exact_2051 : Law2051.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2051
spectrum_assert exact_2051 complete

theorem exact_2052 : Law2052.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2052
spectrum_assert exact_2052 complete

theorem exact_2053 : Law2053.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2053
spectrum_assert exact_2053 complete

theorem exact_2054 : Law2054.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2054
spectrum_assert exact_2054 complete

theorem exact_2055 : Law2055.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2055
spectrum_assert exact_2055 complete

theorem exact_2056 : Law2056.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2056
spectrum_assert exact_2056 complete

theorem exact_2057 : Law2057.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2057
spectrum_assert exact_2057 complete

theorem exact_2058 : Law2058.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2058
spectrum_assert exact_2058 complete

theorem exact_2059 : Law2059.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2059
spectrum_assert exact_2059 complete

theorem exact_2060 : Law2060.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2060
spectrum_assert exact_2060 complete

theorem exact_2061 : Law2061.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2061
spectrum_assert exact_2061 complete

theorem exact_2062 : Law2062.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2062
spectrum_assert exact_2062 complete

theorem exact_2063 : Law2063.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2063
spectrum_assert exact_2063 complete

theorem exact_2064 : Law2064.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2064
spectrum_assert exact_2064 complete

theorem exact_2065 : Law2065.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2065
spectrum_assert exact_2065 complete

theorem exact_2066 : Law2066.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2066
spectrum_assert exact_2066 complete

theorem exact_2067 : Law2067.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2067
spectrum_assert exact_2067 complete

theorem exact_2068 : Law2068.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2068
spectrum_assert exact_2068 complete

theorem exact_2069 : Law2069.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2069
spectrum_assert exact_2069 complete

theorem exact_2070 : Law2070.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2070
spectrum_assert exact_2070 complete

theorem exact_2071 : Law2071.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2071
spectrum_assert exact_2071 complete

theorem exact_2072 : Law2072.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2072
spectrum_assert exact_2072 complete

theorem exact_2073 : Law2073.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2073
spectrum_assert exact_2073 complete

theorem exact_2074 : Law2074.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2074
spectrum_assert exact_2074 complete

theorem exact_2075 : Law2075.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2075
spectrum_assert exact_2075 complete

theorem exact_2076 : Law2076.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2076
spectrum_assert exact_2076 complete

theorem exact_2077 : Law2077.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2077
spectrum_assert exact_2077 complete

theorem exact_2078 : Law2078.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2078
spectrum_assert exact_2078 complete

theorem exact_2079 : Law2079.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2079
spectrum_assert exact_2079 complete

theorem exact_2080 : Law2080.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2080
spectrum_assert exact_2080 complete

theorem exact_2081 : Law2081.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2081
spectrum_assert exact_2081 complete

theorem exact_2082 : Law2082.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2082
spectrum_assert exact_2082 complete

theorem exact_2083 : Law2083.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2083
spectrum_assert exact_2083 complete

theorem exact_2084 : Law2084.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2084
spectrum_assert exact_2084 complete

theorem exact_2085 : Law2085.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2085
spectrum_assert exact_2085 complete

theorem exact_2086 : Law2086.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2086
spectrum_assert exact_2086 complete

theorem exact_2087 : Law2087.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2087
spectrum_assert exact_2087 complete

theorem exact_2088 : Law2088.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2088
spectrum_assert exact_2088 complete

-- UNKNOWN exact spectrum (PDF representative E1480).
theorem lower_2089 : (({1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Set ℕ) ∪ (squares)) ⊆ Law2089.spectrum := by
  rw [ImplicationTransfer.spectrum_2089_eq_1480]
  exact Note.lower_1480
spectrum_assert lower_2089 proofAvailable

theorem upper_2089 : Law2089.spectrum ⊆ (positiveExcept {2, 3}) := by
  rw [ImplicationTransfer.spectrum_2089_eq_1480]
  exact Note.upper_1480
spectrum_assert upper_2089 complete

theorem exact_2090 : Law2090.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2090
spectrum_assert exact_2090 complete

-- UNKNOWN exact spectrum (PDF representative E1516).
theorem lower_2091 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law2091.spectrum := by
  rw [ImplicationTransfer.spectrum_2091_eq_1516]
  exact Note.lower_1516
spectrum_assert lower_2091 complete

theorem upper_2091 : Law2091.spectrum ⊆ (positiveExcept {2, 3, 4, 6}) := by
  rw [ImplicationTransfer.spectrum_2091_eq_1516]
  exact Note.upper_1516
spectrum_assert upper_2091 proofAvailable

theorem cofinite_2091 : CofiniteSpectrum Law2091 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2091_eq_1516]
  exact Note.cofinite_1516
spectrum_assert cofinite_2091 proofAvailable

theorem exact_2092 : Law2092.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2092
spectrum_assert exact_2092 complete

theorem exact_2093 : Law2093.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2093
spectrum_assert exact_2093 complete

theorem exact_2094 : Law2094.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2094
spectrum_assert exact_2094 complete

theorem exact_2095 : Law2095.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2095
spectrum_assert exact_2095 complete

theorem exact_2096 : Law2096.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2096
spectrum_assert exact_2096 complete

theorem exact_2097 : Law2097.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2097
spectrum_assert exact_2097 complete

-- UNKNOWN exact spectrum (PDF representative E1489).
theorem lower_2098 : (({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ)) ⊆ Law2098.spectrum := by
  rw [ImplicationTransfer.spectrum_2098_eq_1489]
  exact Note.lower_1489
spectrum_assert lower_2098 proofAvailable

theorem upper_2098 : Law2098.spectrum ⊆ (positiveExcept {2, 4}) := by
  rw [ImplicationTransfer.spectrum_2098_eq_1489]
  exact Note.upper_1489
spectrum_assert upper_2098 proofAvailable

theorem cofinite_2098 : CofiniteSpectrum Law2098 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2098_eq_1489]
  exact Note.cofinite_1489
spectrum_assert cofinite_2098 noteGap

theorem exact_2099 : Law2099.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2099
spectrum_assert exact_2099 complete

theorem exact_2100 : Law2100.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2100
spectrum_assert exact_2100 complete

-- UNKNOWN exact spectrum (PDF representative E1526).
theorem lower_2101 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law2101.spectrum := by
  rw [ImplicationTransfer.spectrum_2101_eq_1526]
  exact Note.lower_1526
spectrum_assert lower_2101 proofAvailable

theorem upper_2101 : Law2101.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_2101_eq_1526]
  exact Note.upper_1526
spectrum_assert upper_2101 complete

theorem cofinite_2101 : CofiniteSpectrum Law2101 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2101_eq_1526]
  exact Note.cofinite_1526
spectrum_assert cofinite_2101 proofAvailable

theorem exact_2102 : Law2102.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2102
spectrum_assert exact_2102 complete

theorem exact_2103 : Law2103.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2103
spectrum_assert exact_2103 complete

theorem exact_2104 : Law2104.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2104
spectrum_assert exact_2104 complete

theorem exact_2105 : Law2105.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_2105_eq_887 |>.trans Note.exact_887
spectrum_assert exact_2105 complete

theorem exact_2106 : Law2106.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2106
spectrum_assert exact_2106 complete

theorem exact_2107 : Law2107.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2107
spectrum_assert exact_2107 complete

theorem exact_2108 : Law2108.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2108
spectrum_assert exact_2108 complete

theorem exact_2109 : Law2109.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2109
spectrum_assert exact_2109 complete

theorem exact_2110 : Law2110.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2110
spectrum_assert exact_2110 complete

theorem exact_2111 : Law2111.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2111
spectrum_assert exact_2111 complete

theorem exact_2112 : Law2112.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2112
spectrum_assert exact_2112 complete

theorem exact_2113 : Law2113.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_2113_eq_895 |>.trans Note.exact_895
spectrum_assert exact_2113 proofAvailable

theorem exact_2114 : Law2114.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2114
spectrum_assert exact_2114 complete

theorem exact_2115 : Law2115.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2115
spectrum_assert exact_2115 complete

theorem exact_2116 : Law2116.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_2116_eq_898 |>.trans Note.exact_898
spectrum_assert exact_2116 noteGap

theorem exact_2117 : Law2117.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2117
spectrum_assert exact_2117 complete

theorem exact_2118 : Law2118.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2118
spectrum_assert exact_2118 complete

theorem exact_2119 : Law2119.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2119
spectrum_assert exact_2119 complete

theorem exact_2120 : Law2120.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2120
spectrum_assert exact_2120 complete

theorem exact_2121 : Law2121.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2121
spectrum_assert exact_2121 complete

theorem exact_2122 : Law2122.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2122
spectrum_assert exact_2122 complete

theorem exact_2123 : Law2123.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2123
spectrum_assert exact_2123 complete

theorem exact_2124 : Law2124.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2124
spectrum_assert exact_2124 complete

theorem exact_2125 : Law2125.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2125
spectrum_assert exact_2125 complete

-- UNKNOWN exact spectrum (PDF representative E1486).
theorem lower_2126 : (({1, 11, 13, 21} : Set ℕ) ∪ (squares ∪ shiftedSquares)) ⊆ Law2126.spectrum := by
  rw [ImplicationTransfer.spectrum_2126_eq_1486]
  exact Note.lower_1486
spectrum_assert lower_2126 proofAvailable

theorem upper_2126 : Law2126.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_2126_eq_1486]
  exact Note.upper_1486
spectrum_assert upper_2126 complete

theorem exact_2127 : Law2127.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2127
spectrum_assert exact_2127 complete

theorem exact_2128 : Law2128.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2128
spectrum_assert exact_2128 complete

theorem exact_2129 : Law2129.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2129
spectrum_assert exact_2129 complete

theorem exact_2130 : Law2130.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2130
spectrum_assert exact_2130 complete

theorem exact_2131 : Law2131.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2131
spectrum_assert exact_2131 complete

theorem exact_2132 : Law2132.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2132
spectrum_assert exact_2132 complete

theorem exact_2133 : Law2133.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2133
spectrum_assert exact_2133 complete

theorem exact_2134 : Law2134.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2134
spectrum_assert exact_2134 complete

theorem exact_2135 : Law2135.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2135
spectrum_assert exact_2135 complete

theorem exact_2136 : Law2136.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2136
spectrum_assert exact_2136 complete

theorem exact_2137 : Law2137.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2137
spectrum_assert exact_2137 complete

theorem exact_2138 : Law2138.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2138
spectrum_assert exact_2138 complete

theorem exact_2139 : Law2139.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2139
spectrum_assert exact_2139 complete

theorem exact_2140 : Law2140.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2140
spectrum_assert exact_2140 complete

theorem exact_2141 : Law2141.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2141
spectrum_assert exact_2141 complete

theorem exact_2142 : Law2142.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2142
spectrum_assert exact_2142 complete

theorem exact_2143 : Law2143.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2143
spectrum_assert exact_2143 complete

theorem exact_2144 : Law2144.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2144
spectrum_assert exact_2144 complete

theorem exact_2145 : Law2145.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2145
spectrum_assert exact_2145 complete

-- UNKNOWN exact spectrum (PDF representative E1496).
theorem lower_2146 : (({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law2146.spectrum := by
  rw [ImplicationTransfer.spectrum_2146_eq_1496]
  exact Note.lower_1496
spectrum_assert lower_2146 proofAvailable

theorem upper_2146 : Law2146.spectrum ⊆ (positiveExcept {3, 6}) := by
  rw [ImplicationTransfer.spectrum_2146_eq_1496]
  exact Note.upper_1496
spectrum_assert upper_2146 proofAvailable

theorem exact_2147 : Law2147.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2147
spectrum_assert exact_2147 complete

theorem exact_2148 : Law2148.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2148
spectrum_assert exact_2148 complete

theorem exact_2149 : Law2149.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2149
spectrum_assert exact_2149 complete

theorem exact_2150 : Law2150.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2150
spectrum_assert exact_2150 complete

theorem exact_2151 : Law2151.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2151
spectrum_assert exact_2151 complete

theorem exact_2152 : Law2152.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2152
spectrum_assert exact_2152 complete

theorem exact_2153 : Law2153.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2153
spectrum_assert exact_2153 complete

theorem exact_2154 : Law2154.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2154
spectrum_assert exact_2154 complete

theorem exact_2155 : Law2155.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2155
spectrum_assert exact_2155 complete

theorem exact_2156 : Law2156.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2156
spectrum_assert exact_2156 complete

theorem exact_2157 : Law2157.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2157
spectrum_assert exact_2157 complete

theorem exact_2158 : Law2158.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2158
spectrum_assert exact_2158 complete

theorem exact_2159 : Law2159.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2159
spectrum_assert exact_2159 complete

theorem exact_2160 : Law2160.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2160
spectrum_assert exact_2160 complete

theorem exact_2161 : Law2161.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2161
spectrum_assert exact_2161 complete

theorem exact_2162 : Law2162.spectrum = (squares ∪ twiceSquares) :=
  ImplicationTransfer.spectrum_2162_eq_1485 |>.trans Note.exact_1485
spectrum_assert exact_2162 complete

-- UNKNOWN exact spectrum (PDF representative E1483).
theorem lower_2163 : (({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares)) ⊆ Law2163.spectrum := by
  rw [ImplicationTransfer.spectrum_2163_eq_1483]
  exact Note.lower_1483
spectrum_assert lower_2163 complete

theorem upper_2163 : Law2163.spectrum ⊆ (positiveExcept {3, 5, 6, 7}) := by
  rw [ImplicationTransfer.spectrum_2163_eq_1483]
  exact Note.upper_1483
spectrum_assert upper_2163 proofAvailable

theorem exact_2164 : Law2164.spectrum = (squares) :=
  ImplicationTransfer.spectrum_2164_eq_168 |>.trans Note.exact_168
spectrum_assert exact_2164 complete

theorem exact_2165 : Law2165.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2165
spectrum_assert exact_2165 complete

theorem exact_2166 : Law2166.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2166
spectrum_assert exact_2166 complete

theorem exact_2167 : Law2167.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2167
spectrum_assert exact_2167 complete

theorem exact_2168 : Law2168.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2168
spectrum_assert exact_2168 complete

theorem exact_2169 : Law2169.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2169
spectrum_assert exact_2169 complete

theorem exact_2170 : Law2170.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2170
spectrum_assert exact_2170 complete

theorem exact_2171 : Law2171.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2171
spectrum_assert exact_2171 complete

theorem exact_2172 : Law2172.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2172
spectrum_assert exact_2172 complete

theorem exact_2173 : Law2173.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2173
spectrum_assert exact_2173 complete

theorem exact_2174 : Law2174.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2174
spectrum_assert exact_2174 complete

theorem exact_2175 : Law2175.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2175
spectrum_assert exact_2175 complete

theorem exact_2176 : Law2176.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2176
spectrum_assert exact_2176 complete

theorem exact_2177 : Law2177.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2177
spectrum_assert exact_2177 complete

theorem exact_2178 : Law2178.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2178
spectrum_assert exact_2178 complete

theorem exact_2179 : Law2179.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2179
spectrum_assert exact_2179 complete

theorem exact_2180 : Law2180.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2180
spectrum_assert exact_2180 complete

theorem exact_2181 : Law2181.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2181
spectrum_assert exact_2181 complete

theorem exact_2182 : Law2182.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2182
spectrum_assert exact_2182 complete

theorem exact_2183 : Law2183.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2183
spectrum_assert exact_2183 complete

theorem exact_2184 : Law2184.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2184
spectrum_assert exact_2184 complete

theorem exact_2185 : Law2185.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2185
spectrum_assert exact_2185 complete

theorem exact_2186 : Law2186.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2186
spectrum_assert exact_2186 complete

theorem exact_2187 : Law2187.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2187
spectrum_assert exact_2187 complete

theorem exact_2188 : Law2188.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2188
spectrum_assert exact_2188 complete

theorem exact_2189 : Law2189.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2189
spectrum_assert exact_2189 complete

theorem exact_2190 : Law2190.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2190
spectrum_assert exact_2190 complete

theorem exact_2191 : Law2191.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2191
spectrum_assert exact_2191 complete

theorem exact_2192 : Law2192.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2192
spectrum_assert exact_2192 complete

theorem exact_2193 : Law2193.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2193
spectrum_assert exact_2193 complete

theorem exact_2194 : Law2194.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2194
spectrum_assert exact_2194 complete

theorem exact_2195 : Law2195.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2195
spectrum_assert exact_2195 complete

theorem exact_2196 : Law2196.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2196
spectrum_assert exact_2196 complete

theorem exact_2197 : Law2197.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2197
spectrum_assert exact_2197 complete

theorem exact_2198 : Law2198.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2198
spectrum_assert exact_2198 complete

theorem exact_2199 : Law2199.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2199
spectrum_assert exact_2199 complete

theorem exact_2200 : Law2200.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2200
spectrum_assert exact_2200 complete

theorem exact_2201 : Law2201.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2201
spectrum_assert exact_2201 complete

theorem exact_2202 : Law2202.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2202
spectrum_assert exact_2202 complete

theorem exact_2203 : Law2203.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2203
spectrum_assert exact_2203 complete

theorem exact_2204 : Law2204.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2204
spectrum_assert exact_2204 complete

theorem exact_2205 : Law2205.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2205
spectrum_assert exact_2205 complete

theorem exact_2206 : Law2206.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2206
spectrum_assert exact_2206 complete

theorem exact_2207 : Law2207.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2207
spectrum_assert exact_2207 complete

theorem exact_2208 : Law2208.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2208
spectrum_assert exact_2208 complete

theorem exact_2209 : Law2209.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2209
spectrum_assert exact_2209 complete

theorem exact_2210 : Law2210.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2210
spectrum_assert exact_2210 complete

theorem exact_2211 : Law2211.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2211
spectrum_assert exact_2211 complete

theorem exact_2212 : Law2212.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2212
spectrum_assert exact_2212 complete

theorem exact_2213 : Law2213.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2213
spectrum_assert exact_2213 complete

theorem exact_2214 : Law2214.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2214
spectrum_assert exact_2214 complete

theorem exact_2215 : Law2215.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2215
spectrum_assert exact_2215 complete

theorem exact_2216 : Law2216.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2216
spectrum_assert exact_2216 complete

theorem exact_2217 : Law2217.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2217
spectrum_assert exact_2217 complete

theorem exact_2218 : Law2218.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2218
spectrum_assert exact_2218 complete

theorem exact_2219 : Law2219.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2219
spectrum_assert exact_2219 complete

theorem exact_2220 : Law2220.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2220
spectrum_assert exact_2220 complete

theorem exact_2221 : Law2221.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2221
spectrum_assert exact_2221 complete

theorem exact_2222 : Law2222.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2222
spectrum_assert exact_2222 complete

theorem exact_2223 : Law2223.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2223
spectrum_assert exact_2223 complete

theorem exact_2224 : Law2224.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2224
spectrum_assert exact_2224 complete

theorem exact_2225 : Law2225.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2225
spectrum_assert exact_2225 complete

theorem exact_2226 : Law2226.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2226
spectrum_assert exact_2226 complete

theorem exact_2227 : Law2227.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2227
spectrum_assert exact_2227 complete

theorem exact_2228 : Law2228.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2228
spectrum_assert exact_2228 complete

theorem exact_2229 : Law2229.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2229
spectrum_assert exact_2229 complete

theorem exact_2230 : Law2230.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2230
spectrum_assert exact_2230 complete

theorem exact_2231 : Law2231.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2231
spectrum_assert exact_2231 complete

theorem exact_2232 : Law2232.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2232
spectrum_assert exact_2232 complete

theorem exact_2233 : Law2233.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2233
spectrum_assert exact_2233 complete

theorem exact_2234 : Law2234.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2234
spectrum_assert exact_2234 complete

theorem exact_2235 : Law2235.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2235
spectrum_assert exact_2235 complete

theorem exact_2236 : Law2236.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2236
spectrum_assert exact_2236 complete

theorem exact_2237 : Law2237.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2237
spectrum_assert exact_2237 complete

theorem exact_2238 : Law2238.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2238
spectrum_assert exact_2238 complete

theorem exact_2239 : Law2239.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2239
spectrum_assert exact_2239 complete

theorem exact_2240 : Law2240.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2240
spectrum_assert exact_2240 complete

theorem exact_2241 : Law2241.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2241
spectrum_assert exact_2241 complete

theorem exact_2242 : Law2242.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2242
spectrum_assert exact_2242 complete

theorem exact_2243 : Law2243.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2243
spectrum_assert exact_2243 complete

theorem exact_2244 : Law2244.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2244
spectrum_assert exact_2244 complete

theorem exact_2245 : Law2245.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2245
spectrum_assert exact_2245 complete

theorem exact_2246 : Law2246.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2246
spectrum_assert exact_2246 complete

theorem exact_2247 : Law2247.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2247
spectrum_assert exact_2247 complete

theorem exact_2248 : Law2248.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2248
spectrum_assert exact_2248 complete

theorem exact_2249 : Law2249.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2249
spectrum_assert exact_2249 complete

theorem exact_2250 : Law2250.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2250
spectrum_assert exact_2250 complete

theorem exact_2251 : Law2251.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2251
spectrum_assert exact_2251 complete

theorem exact_2252 : Law2252.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2252
spectrum_assert exact_2252 complete

theorem exact_2253 : Law2253.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2253
spectrum_assert exact_2253 complete

theorem exact_2254 : Law2254.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2254
spectrum_assert exact_2254 complete

theorem exact_2255 : Law2255.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2255
spectrum_assert exact_2255 complete

theorem exact_2256 : Law2256.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2256
spectrum_assert exact_2256 complete

theorem exact_2257 : Law2257.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2257
spectrum_assert exact_2257 complete

theorem exact_2258 : Law2258.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2258
spectrum_assert exact_2258 complete

theorem exact_2259 : Law2259.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2259
spectrum_assert exact_2259 complete

theorem exact_2260 : Law2260.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2260
spectrum_assert exact_2260 complete

theorem exact_2261 : Law2261.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2261
spectrum_assert exact_2261 complete

theorem exact_2262 : Law2262.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2262
spectrum_assert exact_2262 complete

theorem exact_2263 : Law2263.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2263
spectrum_assert exact_2263 complete

theorem exact_2264 : Law2264.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2264
spectrum_assert exact_2264 complete

theorem exact_2265 : Law2265.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2265
spectrum_assert exact_2265 complete

theorem exact_2266 : Law2266.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2266
spectrum_assert exact_2266 complete

theorem exact_2267 : Law2267.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2267
spectrum_assert exact_2267 complete

theorem exact_2268 : Law2268.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2268
spectrum_assert exact_2268 complete

theorem exact_2269 : Law2269.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2269
spectrum_assert exact_2269 complete

theorem exact_2270 : Law2270.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2270
spectrum_assert exact_2270 complete

theorem exact_2271 : Law2271.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2271
spectrum_assert exact_2271 complete

theorem exact_2272 : Law2272.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2272
spectrum_assert exact_2272 complete

theorem exact_2273 : Law2273.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2273
spectrum_assert exact_2273 complete

theorem exact_2274 : Law2274.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2274
spectrum_assert exact_2274 complete

theorem exact_2275 : Law2275.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2275
spectrum_assert exact_2275 complete

theorem exact_2276 : Law2276.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2276
spectrum_assert exact_2276 complete

theorem exact_2277 : Law2277.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2277
spectrum_assert exact_2277 complete

theorem exact_2278 : Law2278.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2278
spectrum_assert exact_2278 complete

theorem exact_2279 : Law2279.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2279
spectrum_assert exact_2279 complete

theorem exact_2280 : Law2280.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2280
spectrum_assert exact_2280 complete

theorem exact_2281 : Law2281.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2281
spectrum_assert exact_2281 complete

theorem exact_2282 : Law2282.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2282
spectrum_assert exact_2282 complete

theorem exact_2283 : Law2283.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2283
spectrum_assert exact_2283 complete

theorem exact_2284 : Law2284.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2284
spectrum_assert exact_2284 complete

theorem exact_2285 : Law2285.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2285
spectrum_assert exact_2285 complete

theorem exact_2286 : Law2286.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2286
spectrum_assert exact_2286 complete

theorem exact_2287 : Law2287.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2287
spectrum_assert exact_2287 complete

theorem exact_2288 : Law2288.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2288
spectrum_assert exact_2288 complete

theorem exact_2289 : Law2289.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2289
spectrum_assert exact_2289 complete

theorem exact_2290 : Law2290.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2290
spectrum_assert exact_2290 complete

theorem exact_2291 : Law2291.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2291
spectrum_assert exact_2291 complete

theorem exact_2292 : Law2292.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2292
spectrum_assert exact_2292 complete

theorem exact_2293 : Law2293.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2293
spectrum_assert exact_2293 complete

-- UNKNOWN exact spectrum (PDF representative E1313).
theorem lower_2294 : (({1, 5, 7} : Set ℕ)) ⊆ Law2294.spectrum := by
  rw [ImplicationTransfer.spectrum_2294_eq_1313]
  exact Note.lower_1313
spectrum_assert lower_2294 complete

theorem upper_2294 : Law2294.spectrum ⊆ (positiveExcept {2, 3, 4, 6}) := by
  rw [ImplicationTransfer.spectrum_2294_eq_1313]
  exact Note.upper_1313
spectrum_assert upper_2294 proofAvailable

theorem exact_2295 : Law2295.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2295
spectrum_assert exact_2295 complete

theorem exact_2296 : Law2296.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2296
spectrum_assert exact_2296 complete

theorem exact_2297 : Law2297.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2297
spectrum_assert exact_2297 complete

theorem exact_2298 : Law2298.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2298
spectrum_assert exact_2298 complete

theorem exact_2299 : Law2299.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2299
spectrum_assert exact_2299 complete

theorem exact_2300 : Law2300.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2300
spectrum_assert exact_2300 complete

-- UNKNOWN exact spectrum (PDF representative E1286).
theorem lower_2301 : (({1, 7} : Set ℕ)) ⊆ Law2301.spectrum := by
  rw [ImplicationTransfer.spectrum_2301_eq_1286]
  exact Note.lower_1286
spectrum_assert lower_2301 complete

theorem upper_2301 : Law2301.spectrum ⊆ (positiveExcept {2, 3, 4, 5, 6}) := by
  rw [ImplicationTransfer.spectrum_2301_eq_1286]
  exact Note.upper_1286
spectrum_assert upper_2301 proofAvailable

theorem exact_2302 : Law2302.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2302
spectrum_assert exact_2302 complete

theorem exact_2303 : Law2303.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2303
spectrum_assert exact_2303 complete

-- UNKNOWN exact spectrum (PDF representative E1323).
theorem lower_2304 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law2304.spectrum := by
  rw [ImplicationTransfer.spectrum_2304_eq_1323]
  exact Note.lower_1323
spectrum_assert lower_2304 proofAvailable

theorem upper_2304 : Law2304.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_2304_eq_1323]
  exact Note.upper_1323
spectrum_assert upper_2304 complete

theorem cofinite_2304 : CofiniteSpectrum Law2304 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2304_eq_1323]
  exact Note.cofinite_1323
spectrum_assert cofinite_2304 proofAvailable

theorem exact_2305 : Law2305.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2305
spectrum_assert exact_2305 complete

theorem exact_2306 : Law2306.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2306
spectrum_assert exact_2306 complete

theorem exact_2307 : Law2307.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2307
spectrum_assert exact_2307 complete

theorem exact_2308 : Law2308.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_2308_eq_895 |>.trans Note.exact_895
spectrum_assert exact_2308 proofAvailable

theorem exact_2309 : Law2309.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2309
spectrum_assert exact_2309 complete

theorem exact_2310 : Law2310.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2310
spectrum_assert exact_2310 complete

theorem exact_2311 : Law2311.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2311
spectrum_assert exact_2311 complete

theorem exact_2312 : Law2312.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2312
spectrum_assert exact_2312 complete

theorem exact_2313 : Law2313.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2313
spectrum_assert exact_2313 complete

theorem exact_2314 : Law2314.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2314
spectrum_assert exact_2314 complete

theorem exact_2315 : Law2315.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2315
spectrum_assert exact_2315 complete

theorem exact_2316 : Law2316.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_2316_eq_898 |>.trans Note.exact_898
spectrum_assert exact_2316 noteGap

theorem exact_2317 : Law2317.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2317
spectrum_assert exact_2317 complete

theorem exact_2318 : Law2318.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2318
spectrum_assert exact_2318 complete

theorem exact_2319 : Law2319.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_2319_eq_887 |>.trans Note.exact_887
spectrum_assert exact_2319 complete

theorem exact_2320 : Law2320.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2320
spectrum_assert exact_2320 complete

theorem exact_2321 : Law2321.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2321
spectrum_assert exact_2321 complete

theorem exact_2322 : Law2322.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2322
spectrum_assert exact_2322 complete

theorem exact_2323 : Law2323.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2323
spectrum_assert exact_2323 complete

theorem exact_2324 : Law2324.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2324
spectrum_assert exact_2324 complete

theorem exact_2325 : Law2325.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2325
spectrum_assert exact_2325 complete

theorem exact_2326 : Law2326.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2326
spectrum_assert exact_2326 complete

theorem exact_2327 : Law2327.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2327
spectrum_assert exact_2327 complete

-- UNKNOWN exact spectrum (PDF representative E1279).
theorem lower_2328 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law2328.spectrum := by
  rw [ImplicationTransfer.spectrum_2328_eq_1279]
  exact Note.lower_1279
spectrum_assert lower_2328 complete

theorem upper_2328 : Law2328.spectrum ⊆ (positiveExcept {2, 3, 4, 6, 9}) := by
  rw [ImplicationTransfer.spectrum_2328_eq_1279]
  exact Note.upper_1279
spectrum_assert upper_2328 proofAvailable

theorem cofinite_2328 : CofiniteSpectrum Law2328 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2328_eq_1279]
  exact Note.cofinite_1279
spectrum_assert cofinite_2328 proofAvailable

theorem exact_2329 : Law2329.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2329
spectrum_assert exact_2329 complete

theorem exact_2330 : Law2330.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2330
spectrum_assert exact_2330 complete

theorem exact_2331 : Law2331.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2331
spectrum_assert exact_2331 complete

theorem exact_2332 : Law2332.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2332
spectrum_assert exact_2332 complete

theorem exact_2333 : Law2333.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2333
spectrum_assert exact_2333 complete

theorem exact_2334 : Law2334.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2334
spectrum_assert exact_2334 complete

theorem exact_2335 : Law2335.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2335
spectrum_assert exact_2335 complete

theorem exact_2336 : Law2336.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2336
spectrum_assert exact_2336 complete

theorem exact_2337 : Law2337.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2337
spectrum_assert exact_2337 complete

theorem exact_2338 : Law2338.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2338
spectrum_assert exact_2338 complete

theorem exact_2339 : Law2339.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2339
spectrum_assert exact_2339 complete

theorem exact_2340 : Law2340.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2340
spectrum_assert exact_2340 complete

theorem exact_2341 : Law2341.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2341
spectrum_assert exact_2341 complete

theorem exact_2342 : Law2342.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2342
spectrum_assert exact_2342 complete

theorem exact_2343 : Law2343.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2343
spectrum_assert exact_2343 complete

theorem exact_2344 : Law2344.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2344
spectrum_assert exact_2344 complete

theorem exact_2345 : Law2345.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2345
spectrum_assert exact_2345 complete

theorem exact_2346 : Law2346.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2346
spectrum_assert exact_2346 complete

theorem exact_2347 : Law2347.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2347
spectrum_assert exact_2347 complete

theorem exact_2348 : Law2348.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2348
spectrum_assert exact_2348 complete

theorem exact_2349 : Law2349.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2349
spectrum_assert exact_2349 complete

theorem exact_2350 : Law2350.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2350
spectrum_assert exact_2350 complete

theorem exact_2351 : Law2351.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2351
spectrum_assert exact_2351 complete

theorem exact_2352 : Law2352.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2352
spectrum_assert exact_2352 complete

theorem exact_2353 : Law2353.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2353
spectrum_assert exact_2353 complete

theorem exact_2354 : Law2354.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2354
spectrum_assert exact_2354 complete

theorem exact_2355 : Law2355.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2355
spectrum_assert exact_2355 complete

theorem exact_2356 : Law2356.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2356
spectrum_assert exact_2356 complete

theorem exact_2357 : Law2357.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2357
spectrum_assert exact_2357 complete

theorem exact_2358 : Law2358.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2358
spectrum_assert exact_2358 complete

theorem exact_2359 : Law2359.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2359
spectrum_assert exact_2359 complete

theorem exact_2360 : Law2360.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2360
spectrum_assert exact_2360 complete

theorem exact_2361 : Law2361.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2361
spectrum_assert exact_2361 complete

theorem exact_2362 : Law2362.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2362
spectrum_assert exact_2362 complete

theorem exact_2363 : Law2363.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2363
spectrum_assert exact_2363 complete

theorem exact_2364 : Law2364.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2364
spectrum_assert exact_2364 complete

theorem exact_2365 : Law2365.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2365
spectrum_assert exact_2365 complete

theorem exact_2366 : Law2366.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2366
spectrum_assert exact_2366 complete

theorem exact_2367 : Law2367.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2367
spectrum_assert exact_2367 complete

theorem exact_2368 : Law2368.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2368
spectrum_assert exact_2368 complete

theorem exact_2369 : Law2369.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2369
spectrum_assert exact_2369 complete

theorem exact_2370 : Law2370.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2370_eq_556 |>.trans Note.exact_556
spectrum_assert exact_2370 complete

theorem exact_2371 : Law2371.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2371
spectrum_assert exact_2371 complete

theorem exact_2372 : Law2372.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2372
spectrum_assert exact_2372 complete

theorem exact_2373 : Law2373.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2373
spectrum_assert exact_2373 complete

theorem exact_2374 : Law2374.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2374
spectrum_assert exact_2374 complete

theorem exact_2375 : Law2375.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2375
spectrum_assert exact_2375 complete

theorem exact_2376 : Law2376.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2376
spectrum_assert exact_2376 complete

theorem exact_2377 : Law2377.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2377
spectrum_assert exact_2377 complete

theorem exact_2378 : Law2378.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2378
spectrum_assert exact_2378 complete

theorem exact_2379 : Law2379.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2379
spectrum_assert exact_2379 complete

theorem exact_2380 : Law2380.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2380
spectrum_assert exact_2380 complete

theorem exact_2381 : Law2381.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2381
spectrum_assert exact_2381 complete

theorem exact_2382 : Law2382.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2382
spectrum_assert exact_2382 complete

theorem exact_2383 : Law2383.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2383_eq_556 |>.trans Note.exact_556
spectrum_assert exact_2383 complete

theorem exact_2384 : Law2384.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2384
spectrum_assert exact_2384 complete

theorem exact_2385 : Law2385.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2385
spectrum_assert exact_2385 complete

theorem exact_2386 : Law2386.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2386
spectrum_assert exact_2386 complete

theorem exact_2387 : Law2387.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2387
spectrum_assert exact_2387 complete

theorem exact_2388 : Law2388.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2388
spectrum_assert exact_2388 complete

theorem exact_2389 : Law2389.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2389
spectrum_assert exact_2389 complete

theorem exact_2390 : Law2390.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2390
spectrum_assert exact_2390 complete

theorem exact_2391 : Law2391.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2391
spectrum_assert exact_2391 complete

theorem exact_2392 : Law2392.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2392
spectrum_assert exact_2392 complete

theorem exact_2393 : Law2393.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2393
spectrum_assert exact_2393 complete

theorem exact_2394 : Law2394.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2394
spectrum_assert exact_2394 complete

theorem exact_2395 : Law2395.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2395
spectrum_assert exact_2395 complete

theorem exact_2396 : Law2396.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2396
spectrum_assert exact_2396 complete

theorem exact_2397 : Law2397.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2397
spectrum_assert exact_2397 complete

theorem exact_2398 : Law2398.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2398
spectrum_assert exact_2398 complete

theorem exact_2399 : Law2399.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2399
spectrum_assert exact_2399 complete

theorem exact_2400 : Law2400.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2400
spectrum_assert exact_2400 complete

theorem exact_2401 : Law2401.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2401
spectrum_assert exact_2401 complete

theorem exact_2402 : Law2402.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2402
spectrum_assert exact_2402 complete

theorem exact_2403 : Law2403.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2403
spectrum_assert exact_2403 complete

theorem exact_2404 : Law2404.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2404
spectrum_assert exact_2404 complete

theorem exact_2405 : Law2405.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2405
spectrum_assert exact_2405 complete

theorem exact_2406 : Law2406.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2406
spectrum_assert exact_2406 complete

theorem exact_2407 : Law2407.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2407
spectrum_assert exact_2407 complete

theorem exact_2408 : Law2408.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2408
spectrum_assert exact_2408 complete

theorem exact_2409 : Law2409.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2409
spectrum_assert exact_2409 complete

theorem exact_2410 : Law2410.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2410
spectrum_assert exact_2410 complete

theorem exact_2411 : Law2411.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2411
spectrum_assert exact_2411 complete

theorem exact_2412 : Law2412.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2412
spectrum_assert exact_2412 complete

theorem exact_2413 : Law2413.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2413
spectrum_assert exact_2413 complete

theorem exact_2414 : Law2414.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2414
spectrum_assert exact_2414 complete

theorem exact_2415 : Law2415.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2415
spectrum_assert exact_2415 complete

theorem exact_2416 : Law2416.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2416
spectrum_assert exact_2416 complete

theorem exact_2417 : Law2417.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2417
spectrum_assert exact_2417 complete

theorem exact_2418 : Law2418.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2418
spectrum_assert exact_2418 complete

theorem exact_2419 : Law2419.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2419
spectrum_assert exact_2419 complete

theorem exact_2420 : Law2420.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2420
spectrum_assert exact_2420 complete

theorem exact_2421 : Law2421.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2421
spectrum_assert exact_2421 complete

theorem exact_2422 : Law2422.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2422
spectrum_assert exact_2422 complete

theorem exact_2423 : Law2423.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2423
spectrum_assert exact_2423 complete

theorem exact_2424 : Law2424.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2424
spectrum_assert exact_2424 complete

theorem exact_2425 : Law2425.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2425
spectrum_assert exact_2425 complete

theorem exact_2426 : Law2426.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2426
spectrum_assert exact_2426 complete

theorem exact_2427 : Law2427.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2427
spectrum_assert exact_2427 complete

theorem exact_2428 : Law2428.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2428
spectrum_assert exact_2428 complete

theorem exact_2429 : Law2429.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2429
spectrum_assert exact_2429 complete

theorem exact_2430 : Law2430.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2430
spectrum_assert exact_2430 complete

theorem exact_2431 : Law2431.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2431
spectrum_assert exact_2431 complete

theorem exact_2432 : Law2432.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2432
spectrum_assert exact_2432 complete

theorem exact_2433 : Law2433.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2433
spectrum_assert exact_2433 complete

theorem exact_2434 : Law2434.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2434
spectrum_assert exact_2434 complete

theorem exact_2435 : Law2435.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2435
spectrum_assert exact_2435 complete

theorem exact_2436 : Law2436.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2436
spectrum_assert exact_2436 complete

theorem exact_2437 : Law2437.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2437
spectrum_assert exact_2437 complete

theorem exact_2438 : Law2438.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2438
spectrum_assert exact_2438 complete

theorem exact_2439 : Law2439.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2439
spectrum_assert exact_2439 complete

theorem exact_2440 : Law2440.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2440
spectrum_assert exact_2440 complete

theorem exact_2441 : Law2441.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2441
spectrum_assert exact_2441 complete

theorem exact_2442 : Law2442.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2442
spectrum_assert exact_2442 complete

theorem exact_2443 : Law2443.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2443
spectrum_assert exact_2443 complete

theorem exact_2444 : Law2444.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2444
spectrum_assert exact_2444 complete

theorem exact_2445 : Law2445.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2445
spectrum_assert exact_2445 complete

theorem exact_2446 : Law2446.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2446
spectrum_assert exact_2446 complete

theorem exact_2447 : Law2447.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2447
spectrum_assert exact_2447 complete

theorem exact_2448 : Law2448.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2448
spectrum_assert exact_2448 complete

theorem exact_2449 : Law2449.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2449
spectrum_assert exact_2449 complete

theorem exact_2450 : Law2450.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2450
spectrum_assert exact_2450 complete

theorem exact_2451 : Law2451.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2451
spectrum_assert exact_2451 complete

theorem exact_2452 : Law2452.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2452
spectrum_assert exact_2452 complete

theorem exact_2453 : Law2453.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2453
spectrum_assert exact_2453 complete

theorem exact_2454 : Law2454.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2454
spectrum_assert exact_2454 complete

theorem exact_2455 : Law2455.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2455
spectrum_assert exact_2455 complete

theorem exact_2456 : Law2456.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2456
spectrum_assert exact_2456 complete

theorem exact_2457 : Law2457.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2457
spectrum_assert exact_2457 complete

theorem exact_2458 : Law2458.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2458
spectrum_assert exact_2458 complete

theorem exact_2459 : Law2459.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2459
spectrum_assert exact_2459 complete

theorem exact_2460 : Law2460.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2460
spectrum_assert exact_2460 complete

theorem exact_2461 : Law2461.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2461
spectrum_assert exact_2461 complete

theorem exact_2462 : Law2462.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2462
spectrum_assert exact_2462 complete

theorem exact_2463 : Law2463.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2463
spectrum_assert exact_2463 complete

theorem exact_2464 : Law2464.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2464
spectrum_assert exact_2464 complete

theorem exact_2465 : Law2465.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2465
spectrum_assert exact_2465 complete

theorem exact_2466 : Law2466.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2466
spectrum_assert exact_2466 complete

theorem exact_2467 : Law2467.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2467
spectrum_assert exact_2467 complete

theorem exact_2468 : Law2468.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2468
spectrum_assert exact_2468 complete

theorem exact_2469 : Law2469.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2469
spectrum_assert exact_2469 complete

theorem exact_2470 : Law2470.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2470
spectrum_assert exact_2470 complete

theorem exact_2471 : Law2471.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2471
spectrum_assert exact_2471 complete

theorem exact_2472 : Law2472.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2472
spectrum_assert exact_2472 complete

theorem exact_2473 : Law2473.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2473
spectrum_assert exact_2473 complete

theorem exact_2474 : Law2474.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2474
spectrum_assert exact_2474 complete

theorem exact_2475 : Law2475.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2475
spectrum_assert exact_2475 complete

theorem exact_2476 : Law2476.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2476
spectrum_assert exact_2476 complete

theorem exact_2477 : Law2477.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2477
spectrum_assert exact_2477 complete

theorem exact_2478 : Law2478.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2478
spectrum_assert exact_2478 complete

theorem exact_2479 : Law2479.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2479
spectrum_assert exact_2479 complete

theorem exact_2480 : Law2480.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2480
spectrum_assert exact_2480 complete

theorem exact_2481 : Law2481.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2481
spectrum_assert exact_2481 complete

theorem exact_2482 : Law2482.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2482
spectrum_assert exact_2482 complete

theorem exact_2483 : Law2483.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2483
spectrum_assert exact_2483 complete

theorem exact_2484 : Law2484.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2484
spectrum_assert exact_2484 complete

theorem exact_2485 : Law2485.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2485
spectrum_assert exact_2485 complete

theorem exact_2486 : Law2486.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2486
spectrum_assert exact_2486 complete

theorem exact_2487 : Law2487.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2487
spectrum_assert exact_2487 complete

theorem exact_2488 : Law2488.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2488
spectrum_assert exact_2488 complete

theorem exact_2489 : Law2489.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2489
spectrum_assert exact_2489 complete

theorem exact_2490 : Law2490.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2490
spectrum_assert exact_2490 complete

theorem exact_2491 : Law2491.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2491
spectrum_assert exact_2491 complete

theorem exact_2492 : Law2492.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2492
spectrum_assert exact_2492 complete

theorem exact_2493 : Law2493.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2493
spectrum_assert exact_2493 complete

theorem exact_2494 : Law2494.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2494
spectrum_assert exact_2494 complete

theorem exact_2495 : Law2495.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2495
spectrum_assert exact_2495 complete

theorem exact_2496 : Law2496.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2496
spectrum_assert exact_2496 complete

-- UNKNOWN exact spectrum (PDF representative E1110).
theorem lower_2497 : (({1, 4, 5, 7, 8, 9} : Set ℕ)) ⊆ Law2497.spectrum := by
  rw [ImplicationTransfer.spectrum_2497_eq_1110]
  exact Note.lower_1110
spectrum_assert lower_2497 complete

theorem upper_2497 : Law2497.spectrum ⊆ (positiveExcept {2, 3, 6}) := by
  rw [ImplicationTransfer.spectrum_2497_eq_1110]
  exact Note.upper_1110
spectrum_assert upper_2497 proofAvailable

theorem cofinite_2497 : CofiniteSpectrum Law2497 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2497_eq_1110]
  exact Note.cofinite_1110
spectrum_assert cofinite_2497 proofAvailable

theorem exact_2498 : Law2498.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2498
spectrum_assert exact_2498 complete

theorem exact_2499 : Law2499.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2499
spectrum_assert exact_2499 complete

theorem exact_2500 : Law2500.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2500
spectrum_assert exact_2500 complete

theorem exact_2501 : Law2501.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2501
spectrum_assert exact_2501 complete

theorem exact_2502 : Law2502.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2502
spectrum_assert exact_2502 complete

theorem exact_2503 : Law2503.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2503
spectrum_assert exact_2503 complete

-- UNKNOWN exact spectrum (PDF representative E1083).
theorem lower_2504 : (({1, 3, 4, 7, 8, 9} : Set ℕ)) ⊆ Law2504.spectrum := by
  rw [ImplicationTransfer.spectrum_2504_eq_1083]
  exact Note.lower_1083
spectrum_assert lower_2504 complete

theorem upper_2504 : Law2504.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_2504_eq_1083]
  exact Note.upper_1083
spectrum_assert upper_2504 complete

theorem exact_2505 : Law2505.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2505
spectrum_assert exact_2505 complete

theorem exact_2506 : Law2506.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2506
spectrum_assert exact_2506 complete

theorem exact_2507 : Law2507.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2507
spectrum_assert exact_2507 complete

theorem exact_2508 : Law2508.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2508
spectrum_assert exact_2508 complete

theorem exact_2509 : Law2509.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2509
spectrum_assert exact_2509 complete

theorem exact_2510 : Law2510.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2510
spectrum_assert exact_2510 complete

theorem exact_2511 : Law2511.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2511_eq_556 |>.trans Note.exact_556
spectrum_assert exact_2511 complete

theorem exact_2512 : Law2512.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2512
spectrum_assert exact_2512 complete

theorem exact_2513 : Law2513.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2513
spectrum_assert exact_2513 complete

theorem exact_2514 : Law2514.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2514
spectrum_assert exact_2514 complete

theorem exact_2515 : Law2515.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2515
spectrum_assert exact_2515 complete

theorem exact_2516 : Law2516.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2516
spectrum_assert exact_2516 complete

theorem exact_2517 : Law2517.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2517
spectrum_assert exact_2517 complete

theorem exact_2518 : Law2518.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2518
spectrum_assert exact_2518 complete

theorem exact_2519 : Law2519.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2519
spectrum_assert exact_2519 complete

theorem exact_2520 : Law2520.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2520
spectrum_assert exact_2520 complete

theorem exact_2521 : Law2521.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2521
spectrum_assert exact_2521 complete

theorem exact_2522 : Law2522.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2522
spectrum_assert exact_2522 complete

theorem exact_2523 : Law2523.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2523
spectrum_assert exact_2523 complete

theorem exact_2524 : Law2524.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2524
spectrum_assert exact_2524 complete

theorem exact_2525 : Law2525.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2525
spectrum_assert exact_2525 complete

theorem exact_2526 : Law2526.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2526
spectrum_assert exact_2526 complete

theorem exact_2527 : Law2527.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2527
spectrum_assert exact_2527 complete

theorem exact_2528 : Law2528.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2528
spectrum_assert exact_2528 complete

theorem exact_2529 : Law2529.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2529
spectrum_assert exact_2529 complete

theorem exact_2530 : Law2530.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2530
spectrum_assert exact_2530 complete

-- UNKNOWN exact spectrum (PDF representative E1076).
theorem lower_2531 : (({1, 5} : Set ℕ)) ⊆ Law2531.spectrum := by
  rw [ImplicationTransfer.spectrum_2531_eq_1076]
  exact Note.lower_1076
spectrum_assert lower_2531 complete

theorem upper_2531 : Law2531.spectrum ⊆ (positiveExcept {2, 3, 4, 6, 7}) := by
  rw [ImplicationTransfer.spectrum_2531_eq_1076]
  exact Note.upper_1076
spectrum_assert upper_2531 proofAvailable

theorem cofinite_2531 : CofiniteSpectrum Law2531 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2531_eq_1076]
  exact Note.cofinite_1076
spectrum_assert cofinite_2531 noteGap

theorem exact_2532 : Law2532.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2532
spectrum_assert exact_2532 complete

theorem exact_2533 : Law2533.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2533
spectrum_assert exact_2533 complete

theorem exact_2534 : Law2534.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2534
spectrum_assert exact_2534 complete

theorem exact_2535 : Law2535.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2535
spectrum_assert exact_2535 complete

theorem exact_2536 : Law2536.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2536
spectrum_assert exact_2536 complete

theorem exact_2537 : Law2537.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2537
spectrum_assert exact_2537 complete

theorem exact_2538 : Law2538.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2538
spectrum_assert exact_2538 complete

theorem exact_2539 : Law2539.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2539
spectrum_assert exact_2539 complete

theorem exact_2540 : Law2540.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2540
spectrum_assert exact_2540 complete

theorem exact_2541 : Law2541.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2541
spectrum_assert exact_2541 complete

theorem exact_2542 : Law2542.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2542
spectrum_assert exact_2542 complete

theorem exact_2543 : Law2543.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2543
spectrum_assert exact_2543 complete

theorem exact_2544 : Law2544.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2544
spectrum_assert exact_2544 complete

theorem exact_2545 : Law2545.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2545
spectrum_assert exact_2545 complete

theorem exact_2546 : Law2546.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2546
spectrum_assert exact_2546 complete

theorem exact_2547 : Law2547.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2547
spectrum_assert exact_2547 complete

theorem exact_2548 : Law2548.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2548
spectrum_assert exact_2548 complete

theorem exact_2549 : Law2549.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2549
spectrum_assert exact_2549 complete

theorem exact_2550 : Law2550.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2550
spectrum_assert exact_2550 complete

theorem exact_2551 : Law2551.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2551
spectrum_assert exact_2551 complete

theorem exact_2552 : Law2552.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2552
spectrum_assert exact_2552 complete

theorem exact_2553 : Law2553.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2553
spectrum_assert exact_2553 complete

theorem exact_2554 : Law2554.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2554
spectrum_assert exact_2554 complete

theorem exact_2555 : Law2555.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2555
spectrum_assert exact_2555 complete

theorem exact_2556 : Law2556.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2556
spectrum_assert exact_2556 complete

theorem exact_2557 : Law2557.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2557
spectrum_assert exact_2557 complete

theorem exact_2558 : Law2558.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2558
spectrum_assert exact_2558 complete

theorem exact_2559 : Law2559.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2559
spectrum_assert exact_2559 complete

theorem exact_2560 : Law2560.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2560
spectrum_assert exact_2560 complete

theorem exact_2561 : Law2561.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2561
spectrum_assert exact_2561 complete

theorem exact_2562 : Law2562.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2562
spectrum_assert exact_2562 complete

theorem exact_2563 : Law2563.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2563
spectrum_assert exact_2563 complete

theorem exact_2564 : Law2564.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2564
spectrum_assert exact_2564 complete

theorem exact_2565 : Law2565.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2565
spectrum_assert exact_2565 complete

theorem exact_2566 : Law2566.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2566
spectrum_assert exact_2566 complete

theorem exact_2567 : Law2567.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2567
spectrum_assert exact_2567 complete

theorem exact_2568 : Law2568.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2568
spectrum_assert exact_2568 complete

theorem exact_2569 : Law2569.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2569
spectrum_assert exact_2569 complete

theorem exact_2570 : Law2570.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2570
spectrum_assert exact_2570 complete

theorem exact_2571 : Law2571.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2571
spectrum_assert exact_2571 complete

theorem exact_2572 : Law2572.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2572
spectrum_assert exact_2572 complete

theorem exact_2573 : Law2573.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2573
spectrum_assert exact_2573 complete

theorem exact_2574 : Law2574.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2574
spectrum_assert exact_2574 complete

theorem exact_2575 : Law2575.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2575
spectrum_assert exact_2575 complete

theorem exact_2576 : Law2576.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2576
spectrum_assert exact_2576 complete

theorem exact_2577 : Law2577.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2577
spectrum_assert exact_2577 complete

theorem exact_2578 : Law2578.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2578
spectrum_assert exact_2578 complete

theorem exact_2579 : Law2579.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2579
spectrum_assert exact_2579 complete

theorem exact_2580 : Law2580.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2580
spectrum_assert exact_2580 complete

theorem exact_2581 : Law2581.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2581
spectrum_assert exact_2581 complete

theorem exact_2582 : Law2582.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2582
spectrum_assert exact_2582 complete

theorem exact_2583 : Law2583.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2583
spectrum_assert exact_2583 complete

theorem exact_2584 : Law2584.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2584
spectrum_assert exact_2584 complete

theorem exact_2585 : Law2585.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2585
spectrum_assert exact_2585 complete

theorem exact_2586 : Law2586.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2586_eq_546 |>.trans Note.exact_546
spectrum_assert exact_2586 complete

theorem exact_2587 : Law2587.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2587
spectrum_assert exact_2587 complete

theorem exact_2588 : Law2588.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2588
spectrum_assert exact_2588 complete

theorem exact_2589 : Law2589.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2589
spectrum_assert exact_2589 complete

theorem exact_2590 : Law2590.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2590
spectrum_assert exact_2590 complete

theorem exact_2591 : Law2591.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2591
spectrum_assert exact_2591 complete

theorem exact_2592 : Law2592.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2592
spectrum_assert exact_2592 complete

theorem exact_2593 : Law2593.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2593
spectrum_assert exact_2593 complete

theorem exact_2594 : Law2594.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2594
spectrum_assert exact_2594 complete

theorem exact_2595 : Law2595.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2595
spectrum_assert exact_2595 complete

theorem exact_2596 : Law2596.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2596
spectrum_assert exact_2596 complete

theorem exact_2597 : Law2597.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2597
spectrum_assert exact_2597 complete

theorem exact_2598 : Law2598.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2598
spectrum_assert exact_2598 complete

theorem exact_2599 : Law2599.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2599
spectrum_assert exact_2599 complete

theorem exact_2600 : Law2600.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2600
spectrum_assert exact_2600 complete

theorem exact_2601 : Law2601.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2601
spectrum_assert exact_2601 complete

theorem exact_2602 : Law2602.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2602
spectrum_assert exact_2602 complete

theorem exact_2603 : Law2603.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2603
spectrum_assert exact_2603 complete

theorem exact_2604 : Law2604.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2604
spectrum_assert exact_2604 complete

theorem exact_2605 : Law2605.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2605
spectrum_assert exact_2605 complete

theorem exact_2606 : Law2606.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2606
spectrum_assert exact_2606 complete

theorem exact_2607 : Law2607.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2607
spectrum_assert exact_2607 complete

theorem exact_2608 : Law2608.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2608
spectrum_assert exact_2608 complete

theorem exact_2609 : Law2609.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2609
spectrum_assert exact_2609 complete

theorem exact_2610 : Law2610.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2610
spectrum_assert exact_2610 complete

theorem exact_2611 : Law2611.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2611
spectrum_assert exact_2611 complete

theorem exact_2612 : Law2612.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2612
spectrum_assert exact_2612 complete

theorem exact_2613 : Law2613.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2613
spectrum_assert exact_2613 complete

theorem exact_2614 : Law2614.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2614
spectrum_assert exact_2614 complete

theorem exact_2615 : Law2615.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2615
spectrum_assert exact_2615 complete

theorem exact_2616 : Law2616.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2616
spectrum_assert exact_2616 complete

theorem exact_2617 : Law2617.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2617
spectrum_assert exact_2617 complete

theorem exact_2618 : Law2618.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2618
spectrum_assert exact_2618 complete

theorem exact_2619 : Law2619.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2619
spectrum_assert exact_2619 complete

theorem exact_2620 : Law2620.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2620
spectrum_assert exact_2620 complete

theorem exact_2621 : Law2621.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2621
spectrum_assert exact_2621 complete

theorem exact_2622 : Law2622.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2622
spectrum_assert exact_2622 complete

theorem exact_2623 : Law2623.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2623
spectrum_assert exact_2623 complete

theorem exact_2624 : Law2624.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2624
spectrum_assert exact_2624 complete

theorem exact_2625 : Law2625.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2625
spectrum_assert exact_2625 complete

theorem exact_2626 : Law2626.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2626
spectrum_assert exact_2626 complete

theorem exact_2627 : Law2627.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2627
spectrum_assert exact_2627 complete

theorem exact_2628 : Law2628.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2628
spectrum_assert exact_2628 complete

theorem exact_2629 : Law2629.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2629
spectrum_assert exact_2629 complete

theorem exact_2630 : Law2630.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2630
spectrum_assert exact_2630 complete

theorem exact_2631 : Law2631.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2631
spectrum_assert exact_2631 complete

theorem exact_2632 : Law2632.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2632
spectrum_assert exact_2632 complete

theorem exact_2633 : Law2633.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2633
spectrum_assert exact_2633 complete

theorem exact_2634 : Law2634.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2634
spectrum_assert exact_2634 complete

theorem exact_2635 : Law2635.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2635
spectrum_assert exact_2635 complete

theorem exact_2636 : Law2636.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2636
spectrum_assert exact_2636 complete

theorem exact_2637 : Law2637.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2637
spectrum_assert exact_2637 complete

theorem exact_2638 : Law2638.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2638
spectrum_assert exact_2638 complete

theorem exact_2639 : Law2639.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2639
spectrum_assert exact_2639 complete

theorem exact_2640 : Law2640.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2640
spectrum_assert exact_2640 complete

theorem exact_2641 : Law2641.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2641
spectrum_assert exact_2641 complete

theorem exact_2642 : Law2642.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2642
spectrum_assert exact_2642 complete

theorem exact_2643 : Law2643.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2643
spectrum_assert exact_2643 complete

theorem exact_2644 : Law2644.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2644
spectrum_assert exact_2644 complete

theorem exact_2645 : Law2645.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2645
spectrum_assert exact_2645 complete

theorem exact_2646 : Law2646.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2646
spectrum_assert exact_2646 complete

theorem exact_2647 : Law2647.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2647
spectrum_assert exact_2647 complete

theorem exact_2648 : Law2648.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2648
spectrum_assert exact_2648 complete

theorem exact_2649 : Law2649.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2649
spectrum_assert exact_2649 complete

theorem exact_2650 : Law2650.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2650
spectrum_assert exact_2650 complete

theorem exact_2651 : Law2651.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2651
spectrum_assert exact_2651 complete

theorem exact_2652 : Law2652.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2652
spectrum_assert exact_2652 complete

theorem exact_2653 : Law2653.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2653
spectrum_assert exact_2653 complete

theorem exact_2654 : Law2654.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2654
spectrum_assert exact_2654 complete

theorem exact_2655 : Law2655.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2655
spectrum_assert exact_2655 complete

theorem exact_2656 : Law2656.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2656
spectrum_assert exact_2656 complete

theorem exact_2657 : Law2657.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2657
spectrum_assert exact_2657 complete

theorem exact_2658 : Law2658.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2658
spectrum_assert exact_2658 complete

theorem exact_2659 : Law2659.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2659
spectrum_assert exact_2659 complete

theorem exact_2660 : Law2660.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2660
spectrum_assert exact_2660 complete

theorem exact_2661 : Law2661.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2661
spectrum_assert exact_2661 complete

theorem exact_2662 : Law2662.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2662
spectrum_assert exact_2662 complete

theorem exact_2663 : Law2663.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2663
spectrum_assert exact_2663 complete

theorem exact_2664 : Law2664.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2664
spectrum_assert exact_2664 complete

theorem exact_2665 : Law2665.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2665
spectrum_assert exact_2665 complete

theorem exact_2666 : Law2666.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2666
spectrum_assert exact_2666 complete

theorem exact_2667 : Law2667.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2667
spectrum_assert exact_2667 complete

theorem exact_2668 : Law2668.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2668
spectrum_assert exact_2668 complete

theorem exact_2669 : Law2669.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2669
spectrum_assert exact_2669 complete

theorem exact_2670 : Law2670.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2670
spectrum_assert exact_2670 complete

theorem exact_2671 : Law2671.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2671
spectrum_assert exact_2671 complete

theorem exact_2672 : Law2672.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2672
spectrum_assert exact_2672 complete

theorem exact_2673 : Law2673.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2673
spectrum_assert exact_2673 complete

theorem exact_2674 : Law2674.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2674
spectrum_assert exact_2674 complete

theorem exact_2675 : Law2675.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2675
spectrum_assert exact_2675 complete

theorem exact_2676 : Law2676.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2676
spectrum_assert exact_2676 complete

theorem exact_2677 : Law2677.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2677
spectrum_assert exact_2677 complete

theorem exact_2678 : Law2678.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2678
spectrum_assert exact_2678 complete

theorem exact_2679 : Law2679.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2679
spectrum_assert exact_2679 complete

theorem exact_2680 : Law2680.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2680
spectrum_assert exact_2680 complete

theorem exact_2681 : Law2681.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2681
spectrum_assert exact_2681 complete

theorem exact_2682 : Law2682.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2682
spectrum_assert exact_2682 complete

theorem exact_2683 : Law2683.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2683
spectrum_assert exact_2683 complete

theorem exact_2684 : Law2684.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2684
spectrum_assert exact_2684 complete

theorem exact_2685 : Law2685.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2685
spectrum_assert exact_2685 complete

theorem exact_2686 : Law2686.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2686
spectrum_assert exact_2686 complete

theorem exact_2687 : Law2687.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2687
spectrum_assert exact_2687 complete

theorem exact_2688 : Law2688.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2688
spectrum_assert exact_2688 complete

theorem exact_2689 : Law2689.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2689
spectrum_assert exact_2689 complete

theorem exact_2690 : Law2690.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2690
spectrum_assert exact_2690 complete

theorem exact_2691 : Law2691.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2691
spectrum_assert exact_2691 complete

theorem exact_2692 : Law2692.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2692
spectrum_assert exact_2692 complete

theorem exact_2693 : Law2693.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2693
spectrum_assert exact_2693 complete

theorem exact_2694 : Law2694.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2694
spectrum_assert exact_2694 complete

theorem exact_2695 : Law2695.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2695
spectrum_assert exact_2695 complete

theorem exact_2696 : Law2696.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2696
spectrum_assert exact_2696 complete

theorem exact_2697 : Law2697.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2697
spectrum_assert exact_2697 complete

theorem exact_2698 : Law2698.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2698
spectrum_assert exact_2698 complete

theorem exact_2699 : Law2699.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2699
spectrum_assert exact_2699 complete

-- UNKNOWN exact spectrum (PDF representative E907).
theorem lower_2700 : (({1, 3, 7, 9, 13} : Set ℕ)) ⊆ Law2700.spectrum := by
  rw [ImplicationTransfer.spectrum_2700_eq_907]
  exact Note.lower_907
spectrum_assert lower_2700 complete

theorem upper_2700 : Law2700.spectrum ⊆ (positiveExcept {2, 4, 5, 6}) := by
  rw [ImplicationTransfer.spectrum_2700_eq_907]
  exact Note.upper_907
spectrum_assert upper_2700 proofAvailable

theorem exact_2701 : Law2701.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2701
spectrum_assert exact_2701 complete

theorem exact_2702 : Law2702.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2702
spectrum_assert exact_2702 complete

theorem exact_2703 : Law2703.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2703
spectrum_assert exact_2703 complete

theorem exact_2704 : Law2704.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2704
spectrum_assert exact_2704 complete

theorem exact_2705 : Law2705.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2705
spectrum_assert exact_2705 complete

theorem exact_2706 : Law2706.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2706
spectrum_assert exact_2706 complete

-- UNKNOWN exact spectrum (PDF representative E880).
theorem lower_2707 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law2707.spectrum := by
  rw [ImplicationTransfer.spectrum_2707_eq_880]
  exact Note.lower_880
spectrum_assert lower_2707 proofAvailable

theorem upper_2707 : Law2707.spectrum ⊆ (positiveExcept {2, 6}) := by
  rw [ImplicationTransfer.spectrum_2707_eq_880]
  exact Note.upper_880
spectrum_assert upper_2707 proofAvailable

theorem exact_2708 : Law2708.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2708
spectrum_assert exact_2708 complete

theorem exact_2709 : Law2709.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2709
spectrum_assert exact_2709 complete

theorem exact_2710 : Law2710.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2710
spectrum_assert exact_2710 complete

theorem exact_2711 : Law2711.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2711
spectrum_assert exact_2711 complete

theorem exact_2712 : Law2712.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2712
spectrum_assert exact_2712 complete

theorem exact_2713 : Law2713.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2713
spectrum_assert exact_2713 complete

theorem exact_2714 : Law2714.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2714
spectrum_assert exact_2714 complete

theorem exact_2715 : Law2715.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2715
spectrum_assert exact_2715 complete

theorem exact_2716 : Law2716.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2716
spectrum_assert exact_2716 complete

theorem exact_2717 : Law2717.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2717
spectrum_assert exact_2717 complete

theorem exact_2718 : Law2718.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2718
spectrum_assert exact_2718 complete

theorem exact_2719 : Law2719.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2719
spectrum_assert exact_2719 complete

theorem exact_2720 : Law2720.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2720
spectrum_assert exact_2720 complete

theorem exact_2721 : Law2721.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2721
spectrum_assert exact_2721 complete

theorem exact_2722 : Law2722.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2722_eq_546 |>.trans Note.exact_546
spectrum_assert exact_2722 complete

theorem exact_2723 : Law2723.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2723
spectrum_assert exact_2723 complete

theorem exact_2724 : Law2724.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2724
spectrum_assert exact_2724 complete

theorem exact_2725 : Law2725.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2725
spectrum_assert exact_2725 complete

theorem exact_2726 : Law2726.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2726
spectrum_assert exact_2726 complete

theorem exact_2727 : Law2727.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2727
spectrum_assert exact_2727 complete

theorem exact_2728 : Law2728.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2728
spectrum_assert exact_2728 complete

theorem exact_2729 : Law2729.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2729
spectrum_assert exact_2729 complete

theorem exact_2730 : Law2730.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2730
spectrum_assert exact_2730 complete

theorem exact_2731 : Law2731.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2731
spectrum_assert exact_2731 complete

theorem exact_2732 : Law2732.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2732
spectrum_assert exact_2732 complete

theorem exact_2733 : Law2733.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2733
spectrum_assert exact_2733 complete

-- UNKNOWN exact spectrum (PDF representative E873).
theorem lower_2734 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law2734.spectrum := by
  rw [ImplicationTransfer.spectrum_2734_eq_873]
  exact Note.lower_873
spectrum_assert lower_2734 proofAvailable

theorem upper_2734 : Law2734.spectrum ⊆ (positiveExcept {2, 6}) := by
  rw [ImplicationTransfer.spectrum_2734_eq_873]
  exact Note.upper_873
spectrum_assert upper_2734 proofAvailable

theorem exact_2735 : Law2735.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2735
spectrum_assert exact_2735 complete

theorem exact_2736 : Law2736.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2736
spectrum_assert exact_2736 complete

theorem exact_2737 : Law2737.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2737
spectrum_assert exact_2737 complete

theorem exact_2738 : Law2738.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2738
spectrum_assert exact_2738 complete

theorem exact_2739 : Law2739.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2739
spectrum_assert exact_2739 complete

theorem exact_2740 : Law2740.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2740
spectrum_assert exact_2740 complete

theorem exact_2741 : Law2741.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2741
spectrum_assert exact_2741 complete

theorem exact_2742 : Law2742.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2742
spectrum_assert exact_2742 complete

theorem exact_2743 : Law2743.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2743
spectrum_assert exact_2743 complete

-- UNKNOWN exact spectrum (PDF representative E883).
theorem lower_2744 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law2744.spectrum := by
  rw [ImplicationTransfer.spectrum_2744_eq_883]
  exact Note.lower_883
spectrum_assert lower_2744 proofAvailable

theorem upper_2744 : Law2744.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_2744_eq_883]
  exact Note.upper_883
spectrum_assert upper_2744 complete

theorem cofinite_2744 : CofiniteSpectrum Law2744 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2744_eq_883]
  exact Note.cofinite_883
spectrum_assert cofinite_2744 proofAvailable

theorem exact_2745 : Law2745.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2745
spectrum_assert exact_2745 complete

theorem exact_2746 : Law2746.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2746
spectrum_assert exact_2746 complete

theorem exact_2747 : Law2747.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2747
spectrum_assert exact_2747 complete

theorem exact_2748 : Law2748.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2748
spectrum_assert exact_2748 complete

theorem exact_2749 : Law2749.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2749
spectrum_assert exact_2749 complete

theorem exact_2750 : Law2750.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2750
spectrum_assert exact_2750 complete

theorem exact_2751 : Law2751.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2751
spectrum_assert exact_2751 complete

theorem exact_2752 : Law2752.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2752
spectrum_assert exact_2752 complete

theorem exact_2753 : Law2753.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2753
spectrum_assert exact_2753 complete

theorem exact_2754 : Law2754.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2754
spectrum_assert exact_2754 complete

theorem exact_2755 : Law2755.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_2755_eq_887 |>.trans Note.exact_887
spectrum_assert exact_2755 complete

theorem exact_2756 : Law2756.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2756
spectrum_assert exact_2756 complete

theorem exact_2757 : Law2757.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2757
spectrum_assert exact_2757 complete

theorem exact_2758 : Law2758.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2758
spectrum_assert exact_2758 complete

theorem exact_2759 : Law2759.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2759
spectrum_assert exact_2759 complete

theorem exact_2760 : Law2760.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2760
spectrum_assert exact_2760 complete

theorem exact_2761 : Law2761.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2761
spectrum_assert exact_2761 complete

theorem exact_2762 : Law2762.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2762
spectrum_assert exact_2762 complete

theorem exact_2763 : Law2763.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2763
spectrum_assert exact_2763 complete

theorem exact_2764 : Law2764.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2764
spectrum_assert exact_2764 complete

theorem exact_2765 : Law2765.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2765
spectrum_assert exact_2765 complete

theorem exact_2766 : Law2766.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2766
spectrum_assert exact_2766 complete

theorem exact_2767 : Law2767.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2767
spectrum_assert exact_2767 complete

theorem exact_2768 : Law2768.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2768
spectrum_assert exact_2768 complete

theorem exact_2769 : Law2769.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2769
spectrum_assert exact_2769 complete

theorem exact_2770 : Law2770.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2770
spectrum_assert exact_2770 complete

theorem exact_2771 : Law2771.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2771
spectrum_assert exact_2771 complete

theorem exact_2772 : Law2772.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2772
spectrum_assert exact_2772 complete

theorem exact_2773 : Law2773.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2773
spectrum_assert exact_2773 complete

theorem exact_2774 : Law2774.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2774
spectrum_assert exact_2774 complete

theorem exact_2775 : Law2775.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2775
spectrum_assert exact_2775 complete

theorem exact_2776 : Law2776.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2776_eq_546 |>.trans Note.exact_546
spectrum_assert exact_2776 complete

theorem exact_2777 : Law2777.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2777
spectrum_assert exact_2777 complete

theorem exact_2778 : Law2778.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2778
spectrum_assert exact_2778 complete

theorem exact_2779 : Law2779.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2779
spectrum_assert exact_2779 complete

theorem exact_2780 : Law2780.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2780
spectrum_assert exact_2780 complete

theorem exact_2781 : Law2781.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2781
spectrum_assert exact_2781 complete

theorem exact_2782 : Law2782.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2782
spectrum_assert exact_2782 complete

theorem exact_2783 : Law2783.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2783
spectrum_assert exact_2783 complete

theorem exact_2784 : Law2784.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2784
spectrum_assert exact_2784 complete

theorem exact_2785 : Law2785.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2785
spectrum_assert exact_2785 complete

theorem exact_2786 : Law2786.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2786
spectrum_assert exact_2786 complete

theorem exact_2787 : Law2787.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2787
spectrum_assert exact_2787 complete

theorem exact_2788 : Law2788.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2788
spectrum_assert exact_2788 complete

theorem exact_2789 : Law2789.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_2789_eq_895 |>.trans Note.exact_895
spectrum_assert exact_2789 proofAvailable

theorem exact_2790 : Law2790.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2790
spectrum_assert exact_2790 complete

theorem exact_2791 : Law2791.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2791
spectrum_assert exact_2791 complete

theorem exact_2792 : Law2792.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2792
spectrum_assert exact_2792 complete

theorem exact_2793 : Law2793.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2793
spectrum_assert exact_2793 complete

theorem exact_2794 : Law2794.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2794
spectrum_assert exact_2794 complete

theorem exact_2795 : Law2795.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2795
spectrum_assert exact_2795 complete

theorem exact_2796 : Law2796.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2796
spectrum_assert exact_2796 complete

theorem exact_2797 : Law2797.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2797
spectrum_assert exact_2797 complete

theorem exact_2798 : Law2798.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2798
spectrum_assert exact_2798 complete

theorem exact_2799 : Law2799.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2799
spectrum_assert exact_2799 complete

theorem exact_2800 : Law2800.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2800
spectrum_assert exact_2800 complete

theorem exact_2801 : Law2801.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2801
spectrum_assert exact_2801 complete

theorem exact_2802 : Law2802.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2802
spectrum_assert exact_2802 complete

theorem exact_2803 : Law2803.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2803
spectrum_assert exact_2803 complete

theorem exact_2804 : Law2804.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2804
spectrum_assert exact_2804 complete

theorem exact_2805 : Law2805.spectrum = (powersTwo) :=
  ImplicationTransfer.spectrum_2805_eq_898 |>.trans Note.exact_898
spectrum_assert exact_2805 noteGap

theorem exact_2806 : Law2806.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2806
spectrum_assert exact_2806 complete

theorem exact_2807 : Law2807.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2807
spectrum_assert exact_2807 complete

theorem exact_2808 : Law2808.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2808
spectrum_assert exact_2808 complete

theorem exact_2809 : Law2809.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2809
spectrum_assert exact_2809 complete

theorem exact_2810 : Law2810.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2810
spectrum_assert exact_2810 complete

theorem exact_2811 : Law2811.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2811
spectrum_assert exact_2811 complete

theorem exact_2812 : Law2812.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2812
spectrum_assert exact_2812 complete

theorem exact_2813 : Law2813.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2813
spectrum_assert exact_2813 complete

theorem exact_2814 : Law2814.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2814
spectrum_assert exact_2814 complete

theorem exact_2815 : Law2815.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2815
spectrum_assert exact_2815 complete

theorem exact_2816 : Law2816.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2816
spectrum_assert exact_2816 complete

theorem exact_2817 : Law2817.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2817
spectrum_assert exact_2817 complete

theorem exact_2818 : Law2818.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2818
spectrum_assert exact_2818 complete

theorem exact_2819 : Law2819.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2819
spectrum_assert exact_2819 complete

theorem exact_2820 : Law2820.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2820
spectrum_assert exact_2820 complete

theorem exact_2821 : Law2821.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2821
spectrum_assert exact_2821 complete

theorem exact_2822 : Law2822.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2822
spectrum_assert exact_2822 complete

theorem exact_2823 : Law2823.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2823
spectrum_assert exact_2823 complete

theorem exact_2824 : Law2824.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2824
spectrum_assert exact_2824 complete

theorem exact_2825 : Law2825.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2825
spectrum_assert exact_2825 complete

theorem exact_2826 : Law2826.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2826
spectrum_assert exact_2826 complete

theorem exact_2827 : Law2827.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2827
spectrum_assert exact_2827 complete

theorem exact_2828 : Law2828.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2828
spectrum_assert exact_2828 complete

theorem exact_2829 : Law2829.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2829
spectrum_assert exact_2829 complete

theorem exact_2830 : Law2830.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2830
spectrum_assert exact_2830 complete

theorem exact_2831 : Law2831.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2831
spectrum_assert exact_2831 complete

theorem exact_2832 : Law2832.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2832
spectrum_assert exact_2832 complete

theorem exact_2833 : Law2833.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2833
spectrum_assert exact_2833 complete

theorem exact_2834 : Law2834.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2834
spectrum_assert exact_2834 complete

theorem exact_2835 : Law2835.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2835
spectrum_assert exact_2835 complete

theorem exact_2836 : Law2836.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2836
spectrum_assert exact_2836 complete

theorem exact_2837 : Law2837.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2837
spectrum_assert exact_2837 complete

theorem exact_2838 : Law2838.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2838
spectrum_assert exact_2838 complete

theorem exact_2839 : Law2839.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2839
spectrum_assert exact_2839 complete

theorem exact_2840 : Law2840.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2840
spectrum_assert exact_2840 complete

theorem exact_2841 : Law2841.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2841
spectrum_assert exact_2841 complete

theorem exact_2842 : Law2842.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2842
spectrum_assert exact_2842 complete

theorem exact_2843 : Law2843.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2843
spectrum_assert exact_2843 complete

theorem exact_2844 : Law2844.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2844
spectrum_assert exact_2844 complete

theorem exact_2845 : Law2845.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2845
spectrum_assert exact_2845 complete

theorem exact_2846 : Law2846.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2846
spectrum_assert exact_2846 complete

theorem exact_2847 : Law2847.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2847
spectrum_assert exact_2847 complete

theorem exact_2848 : Law2848.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2848
spectrum_assert exact_2848 complete

theorem exact_2849 : Law2849.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2849
spectrum_assert exact_2849 complete

theorem exact_2850 : Law2850.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2850
spectrum_assert exact_2850 complete

theorem exact_2851 : Law2851.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2851
spectrum_assert exact_2851 complete

theorem exact_2852 : Law2852.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2852
spectrum_assert exact_2852 complete

theorem exact_2853 : Law2853.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2853
spectrum_assert exact_2853 complete

theorem exact_2854 : Law2854.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2854
spectrum_assert exact_2854 complete

theorem exact_2855 : Law2855.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2855
spectrum_assert exact_2855 complete

theorem exact_2856 : Law2856.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2856
spectrum_assert exact_2856 complete

theorem exact_2857 : Law2857.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2857
spectrum_assert exact_2857 complete

theorem exact_2858 : Law2858.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2858
spectrum_assert exact_2858 complete

theorem exact_2859 : Law2859.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2859
spectrum_assert exact_2859 complete

theorem exact_2860 : Law2860.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2860
spectrum_assert exact_2860 complete

theorem exact_2861 : Law2861.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2861
spectrum_assert exact_2861 complete

theorem exact_2862 : Law2862.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2862
spectrum_assert exact_2862 complete

theorem exact_2863 : Law2863.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2863
spectrum_assert exact_2863 complete

theorem exact_2864 : Law2864.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2864
spectrum_assert exact_2864 complete

theorem exact_2865 : Law2865.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2865
spectrum_assert exact_2865 complete

theorem exact_2866 : Law2866.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2866
spectrum_assert exact_2866 complete

theorem exact_2867 : Law2867.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2867
spectrum_assert exact_2867 complete

theorem exact_2868 : Law2868.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2868
spectrum_assert exact_2868 complete

theorem exact_2869 : Law2869.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2869
spectrum_assert exact_2869 complete

theorem exact_2870 : Law2870.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2870
spectrum_assert exact_2870 complete

theorem exact_2871 : Law2871.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2871
spectrum_assert exact_2871 complete

theorem exact_2872 : Law2872.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2872
spectrum_assert exact_2872 complete

theorem exact_2873 : Law2873.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2873
spectrum_assert exact_2873 complete

theorem exact_2874 : Law2874.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2874
spectrum_assert exact_2874 complete

theorem exact_2875 : Law2875.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2875
spectrum_assert exact_2875 complete

theorem exact_2876 : Law2876.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2876
spectrum_assert exact_2876 complete

theorem exact_2877 : Law2877.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2877
spectrum_assert exact_2877 complete

theorem exact_2878 : Law2878.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2878
spectrum_assert exact_2878 complete

theorem exact_2879 : Law2879.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2879
spectrum_assert exact_2879 complete

theorem exact_2880 : Law2880.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2880
spectrum_assert exact_2880 complete

theorem exact_2881 : Law2881.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2881
spectrum_assert exact_2881 complete

theorem exact_2882 : Law2882.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2882
spectrum_assert exact_2882 complete

theorem exact_2883 : Law2883.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2883
spectrum_assert exact_2883 complete

theorem exact_2884 : Law2884.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2884
spectrum_assert exact_2884 complete

theorem exact_2885 : Law2885.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2885
spectrum_assert exact_2885 complete

theorem exact_2886 : Law2886.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2886
spectrum_assert exact_2886 complete

theorem exact_2887 : Law2887.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2887
spectrum_assert exact_2887 complete

theorem exact_2888 : Law2888.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2888
spectrum_assert exact_2888 complete

theorem exact_2889 : Law2889.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2889
spectrum_assert exact_2889 complete

theorem exact_2890 : Law2890.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2890
spectrum_assert exact_2890 complete

theorem exact_2891 : Law2891.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2891
spectrum_assert exact_2891 complete

theorem exact_2892 : Law2892.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2892
spectrum_assert exact_2892 complete

theorem exact_2893 : Law2893.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2893
spectrum_assert exact_2893 complete

theorem exact_2894 : Law2894.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2894
spectrum_assert exact_2894 complete

theorem exact_2895 : Law2895.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2895
spectrum_assert exact_2895 complete

theorem exact_2896 : Law2896.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2896
spectrum_assert exact_2896 complete

theorem exact_2897 : Law2897.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2897
spectrum_assert exact_2897 complete

theorem exact_2898 : Law2898.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2898
spectrum_assert exact_2898 complete

theorem exact_2899 : Law2899.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2899
spectrum_assert exact_2899 complete

-- UNKNOWN exact spectrum (PDF representative E667).
theorem lower_2900 : (({1, 7, 9} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law2900.spectrum := by
  rw [ImplicationTransfer.spectrum_2900_eq_667]
  exact Note.lower_667
spectrum_assert lower_2900 proofAvailable

theorem upper_2900 : Law2900.spectrum ⊆ (positiveExcept {3}) := by
  rw [ImplicationTransfer.spectrum_2900_eq_667]
  exact Note.upper_667
spectrum_assert upper_2900 complete

theorem exact_2901 : Law2901.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2901
spectrum_assert exact_2901 complete

theorem exact_2902 : Law2902.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2902
spectrum_assert exact_2902 complete

-- UNKNOWN exact spectrum (PDF representative E704).
theorem lower_2903 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law2903.spectrum := by
  rw [ImplicationTransfer.spectrum_2903_eq_704]
  exact Note.lower_704
spectrum_assert lower_2903 complete

theorem upper_2903 : Law2903.spectrum ⊆ (positiveExcept {2, 3, 4, 6, 9}) := by
  rw [ImplicationTransfer.spectrum_2903_eq_704]
  exact Note.upper_704
spectrum_assert upper_2903 proofAvailable

theorem cofinite_2903 : CofiniteSpectrum Law2903 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2903_eq_704]
  exact Note.cofinite_704
spectrum_assert cofinite_2903 proofAvailable

theorem exact_2904 : Law2904.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2904
spectrum_assert exact_2904 complete

theorem exact_2905 : Law2905.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2905
spectrum_assert exact_2905 complete

theorem exact_2906 : Law2906.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2906
spectrum_assert exact_2906 complete

theorem exact_2907 : Law2907.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2907
spectrum_assert exact_2907 complete

theorem exact_2908 : Law2908.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2908
spectrum_assert exact_2908 complete

theorem exact_2909 : Law2909.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2909
spectrum_assert exact_2909 complete

-- UNKNOWN exact spectrum (PDF representative E677).
theorem lower_2910 : (({1, 5, 7, 9, 11, 13, 16} : Set ℕ)) ⊆ Law2910.spectrum := by
  rw [ImplicationTransfer.spectrum_2910_eq_677]
  exact Note.lower_677
spectrum_assert lower_2910 complete

theorem upper_2910 : Law2910.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_2910_eq_677]
  exact Note.upper_677
spectrum_assert upper_2910 complete

theorem cofinite_2910 : CofiniteSpectrum Law2910 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2910_eq_677]
  exact Note.cofinite_677
spectrum_assert cofinite_2910 noteGap

theorem exact_2911 : Law2911.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2911
spectrum_assert exact_2911 complete

theorem exact_2912 : Law2912.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2912
spectrum_assert exact_2912 complete

theorem exact_2913 : Law2913.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2913
spectrum_assert exact_2913 complete

theorem exact_2914 : Law2914.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2914
spectrum_assert exact_2914 complete

theorem exact_2915 : Law2915.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2915
spectrum_assert exact_2915 complete

theorem exact_2916 : Law2916.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2916
spectrum_assert exact_2916 complete

theorem exact_2917 : Law2917.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2917
spectrum_assert exact_2917 complete

theorem exact_2918 : Law2918.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2918
spectrum_assert exact_2918 complete

theorem exact_2919 : Law2919.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2919
spectrum_assert exact_2919 complete

theorem exact_2920 : Law2920.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2920
spectrum_assert exact_2920 complete

theorem exact_2921 : Law2921.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2921
spectrum_assert exact_2921 complete

theorem exact_2922 : Law2922.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2922
spectrum_assert exact_2922 complete

theorem exact_2923 : Law2923.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2923
spectrum_assert exact_2923 complete

theorem exact_2924 : Law2924.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2924
spectrum_assert exact_2924 complete

theorem exact_2925 : Law2925.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2925
spectrum_assert exact_2925 complete

theorem exact_2926 : Law2926.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2926
spectrum_assert exact_2926 complete

theorem exact_2927 : Law2927.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2927
spectrum_assert exact_2927 complete

theorem exact_2928 : Law2928.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2928_eq_556 |>.trans Note.exact_556
spectrum_assert exact_2928 complete

theorem exact_2929 : Law2929.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2929
spectrum_assert exact_2929 complete

theorem exact_2930 : Law2930.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2930
spectrum_assert exact_2930 complete

theorem exact_2931 : Law2931.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2931
spectrum_assert exact_2931 complete

theorem exact_2932 : Law2932.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2932
spectrum_assert exact_2932 complete

theorem exact_2933 : Law2933.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2933
spectrum_assert exact_2933 complete

theorem exact_2934 : Law2934.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2934
spectrum_assert exact_2934 complete

theorem exact_2935 : Law2935.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2935
spectrum_assert exact_2935 complete

theorem exact_2936 : Law2936.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2936
spectrum_assert exact_2936 complete

-- UNKNOWN exact spectrum (PDF representative E670).
theorem lower_2937 : (({1, 4, 5} : Set ℕ)) ⊆ Law2937.spectrum := by
  rw [ImplicationTransfer.spectrum_2937_eq_670]
  exact Note.lower_670
spectrum_assert lower_2937 complete

theorem upper_2937 : Law2937.spectrum ⊆ (positiveExcept {2, 3, 6, 7}) := by
  rw [ImplicationTransfer.spectrum_2937_eq_670]
  exact Note.upper_670
spectrum_assert upper_2937 proofAvailable

theorem cofinite_2937 : CofiniteSpectrum Law2937 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_2937_eq_670]
  exact Note.cofinite_670
spectrum_assert cofinite_2937 noteGap

theorem exact_2938 : Law2938.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2938
spectrum_assert exact_2938 complete

theorem exact_2939 : Law2939.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2939
spectrum_assert exact_2939 complete

theorem exact_2940 : Law2940.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2940
spectrum_assert exact_2940 complete

theorem exact_2941 : Law2941.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2941
spectrum_assert exact_2941 complete

theorem exact_2942 : Law2942.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2942
spectrum_assert exact_2942 complete

theorem exact_2943 : Law2943.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2943
spectrum_assert exact_2943 complete

theorem exact_2944 : Law2944.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2944
spectrum_assert exact_2944 complete

theorem exact_2945 : Law2945.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2945
spectrum_assert exact_2945 complete

theorem exact_2946 : Law2946.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2946
spectrum_assert exact_2946 complete

theorem exact_2947 : Law2947.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2947
spectrum_assert exact_2947 complete

theorem exact_2948 : Law2948.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2948
spectrum_assert exact_2948 complete

theorem exact_2949 : Law2949.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2949
spectrum_assert exact_2949 complete

theorem exact_2950 : Law2950.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2950
spectrum_assert exact_2950 complete

theorem exact_2951 : Law2951.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2951
spectrum_assert exact_2951 complete

theorem exact_2952 : Law2952.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2952
spectrum_assert exact_2952 complete

theorem exact_2953 : Law2953.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2953
spectrum_assert exact_2953 complete

theorem exact_2954 : Law2954.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2954
spectrum_assert exact_2954 complete

theorem exact_2955 : Law2955.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2955
spectrum_assert exact_2955 complete

theorem exact_2956 : Law2956.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2956
spectrum_assert exact_2956 complete

theorem exact_2957 : Law2957.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2957
spectrum_assert exact_2957 complete

theorem exact_2958 : Law2958.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2958
spectrum_assert exact_2958 complete

theorem exact_2959 : Law2959.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2959
spectrum_assert exact_2959 complete

theorem exact_2960 : Law2960.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2960
spectrum_assert exact_2960 complete

theorem exact_2961 : Law2961.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2961
spectrum_assert exact_2961 complete

theorem exact_2962 : Law2962.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2962
spectrum_assert exact_2962 complete

theorem exact_2963 : Law2963.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2963
spectrum_assert exact_2963 complete

theorem exact_2964 : Law2964.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2964
spectrum_assert exact_2964 complete

theorem exact_2965 : Law2965.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2965
spectrum_assert exact_2965 complete

theorem exact_2966 : Law2966.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2966
spectrum_assert exact_2966 complete

theorem exact_2967 : Law2967.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2967
spectrum_assert exact_2967 complete

theorem exact_2968 : Law2968.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2968
spectrum_assert exact_2968 complete

theorem exact_2969 : Law2969.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2969
spectrum_assert exact_2969 complete

theorem exact_2970 : Law2970.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2970
spectrum_assert exact_2970 complete

theorem exact_2971 : Law2971.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2971
spectrum_assert exact_2971 complete

theorem exact_2972 : Law2972.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2972
spectrum_assert exact_2972 complete

theorem exact_2973 : Law2973.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2973
spectrum_assert exact_2973 complete

theorem exact_2974 : Law2974.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2974
spectrum_assert exact_2974 complete

theorem exact_2975 : Law2975.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2975
spectrum_assert exact_2975 complete

theorem exact_2976 : Law2976.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2976
spectrum_assert exact_2976 complete

theorem exact_2977 : Law2977.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2977
spectrum_assert exact_2977 complete

theorem exact_2978 : Law2978.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2978
spectrum_assert exact_2978 complete

theorem exact_2979 : Law2979.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2979
spectrum_assert exact_2979 complete

theorem exact_2980 : Law2980.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2980
spectrum_assert exact_2980 complete

theorem exact_2981 : Law2981.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2981
spectrum_assert exact_2981 complete

theorem exact_2982 : Law2982.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_2982_eq_556 |>.trans Note.exact_556
spectrum_assert exact_2982 complete

theorem exact_2983 : Law2983.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2983
spectrum_assert exact_2983 complete

theorem exact_2984 : Law2984.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2984
spectrum_assert exact_2984 complete

theorem exact_2985 : Law2985.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2985
spectrum_assert exact_2985 complete

theorem exact_2986 : Law2986.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2986
spectrum_assert exact_2986 complete

theorem exact_2987 : Law2987.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2987
spectrum_assert exact_2987 complete

theorem exact_2988 : Law2988.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2988
spectrum_assert exact_2988 complete

theorem exact_2989 : Law2989.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2989
spectrum_assert exact_2989 complete

theorem exact_2990 : Law2990.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2990
spectrum_assert exact_2990 complete

theorem exact_2991 : Law2991.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2991
spectrum_assert exact_2991 complete

theorem exact_2992 : Law2992.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2992
spectrum_assert exact_2992 complete

theorem exact_2993 : Law2993.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2993
spectrum_assert exact_2993 complete

theorem exact_2994 : Law2994.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2994
spectrum_assert exact_2994 complete

theorem exact_2995 : Law2995.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2995
spectrum_assert exact_2995 complete

theorem exact_2996 : Law2996.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2996
spectrum_assert exact_2996 complete

theorem exact_2997 : Law2997.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2997
spectrum_assert exact_2997 complete

theorem exact_2998 : Law2998.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_2998
spectrum_assert exact_2998 complete

theorem exact_2999 : Law2999.spectrum = ({1}) :=
  ImplicationTransfer.singleton_2999
spectrum_assert exact_2999 complete

theorem exact_3000 : Law3000.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3000
spectrum_assert exact_3000 complete

theorem exact_3001 : Law3001.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3001
spectrum_assert exact_3001 complete

theorem exact_3002 : Law3002.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3002
spectrum_assert exact_3002 complete

theorem exact_3003 : Law3003.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3003
spectrum_assert exact_3003 complete

theorem exact_3004 : Law3004.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3004
spectrum_assert exact_3004 complete

theorem exact_3005 : Law3005.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3005
spectrum_assert exact_3005 complete

theorem exact_3006 : Law3006.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3006
spectrum_assert exact_3006 complete

theorem exact_3007 : Law3007.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3007
spectrum_assert exact_3007 complete

theorem exact_3008 : Law3008.spectrum = (residues 3 {1, 2} {7}) :=
  ImplicationTransfer.spectrum_3008_eq_695 |>.trans Note.exact_695
spectrum_assert exact_3008 complete

theorem exact_3009 : Law3009.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3009
spectrum_assert exact_3009 complete

theorem exact_3010 : Law3010.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3010
spectrum_assert exact_3010 complete

theorem exact_3011 : Law3011.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3011
spectrum_assert exact_3011 complete

theorem exact_3012 : Law3012.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3012
spectrum_assert exact_3012 complete

theorem exact_3013 : Law3013.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3013
spectrum_assert exact_3013 complete

theorem exact_3014 : Law3014.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3014
spectrum_assert exact_3014 complete

theorem exact_3015 : Law3015.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3015
spectrum_assert exact_3015 complete

theorem exact_3016 : Law3016.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3016
spectrum_assert exact_3016 complete

theorem exact_3017 : Law3017.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3017
spectrum_assert exact_3017 complete

theorem exact_3018 : Law3018.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3018
spectrum_assert exact_3018 complete

theorem exact_3019 : Law3019.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3019
spectrum_assert exact_3019 complete

theorem exact_3020 : Law3020.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3020
spectrum_assert exact_3020 complete

theorem exact_3021 : Law3021.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3021
spectrum_assert exact_3021 complete

theorem exact_3022 : Law3022.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3022
spectrum_assert exact_3022 complete

theorem exact_3023 : Law3023.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3023
spectrum_assert exact_3023 complete

theorem exact_3024 : Law3024.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3024
spectrum_assert exact_3024 complete

theorem exact_3025 : Law3025.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3025
spectrum_assert exact_3025 complete

theorem exact_3026 : Law3026.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3026
spectrum_assert exact_3026 complete

theorem exact_3027 : Law3027.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3027
spectrum_assert exact_3027 complete

theorem exact_3028 : Law3028.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3028
spectrum_assert exact_3028 complete

theorem exact_3029 : Law3029.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3029
spectrum_assert exact_3029 complete

theorem exact_3030 : Law3030.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3030
spectrum_assert exact_3030 complete

theorem exact_3031 : Law3031.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3031
spectrum_assert exact_3031 complete

theorem exact_3032 : Law3032.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3032
spectrum_assert exact_3032 complete

theorem exact_3033 : Law3033.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3033
spectrum_assert exact_3033 complete

theorem exact_3034 : Law3034.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3034
spectrum_assert exact_3034 complete

theorem exact_3035 : Law3035.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3035
spectrum_assert exact_3035 complete

theorem exact_3036 : Law3036.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3036
spectrum_assert exact_3036 complete

theorem exact_3037 : Law3037.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3037
spectrum_assert exact_3037 complete

theorem exact_3038 : Law3038.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3038
spectrum_assert exact_3038 complete

theorem exact_3039 : Law3039.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3039
spectrum_assert exact_3039 complete

theorem exact_3040 : Law3040.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3040
spectrum_assert exact_3040 complete

theorem exact_3041 : Law3041.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3041
spectrum_assert exact_3041 complete

theorem exact_3042 : Law3042.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3042
spectrum_assert exact_3042 complete

theorem exact_3043 : Law3043.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3043
spectrum_assert exact_3043 complete

theorem exact_3044 : Law3044.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3044
spectrum_assert exact_3044 complete

theorem exact_3045 : Law3045.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3045
spectrum_assert exact_3045 complete

theorem exact_3046 : Law3046.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3046
spectrum_assert exact_3046 complete

theorem exact_3047 : Law3047.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3047
spectrum_assert exact_3047 complete

theorem exact_3048 : Law3048.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3048
spectrum_assert exact_3048 complete

theorem exact_3049 : Law3049.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3049
spectrum_assert exact_3049 complete

theorem exact_3050 : Law3050.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3050
spectrum_assert exact_3050 complete

theorem exact_3051 : Law3051.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3051
spectrum_assert exact_3051 complete

theorem exact_3052 : Law3052.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3052
spectrum_assert exact_3052 complete

theorem exact_3053 : Law3053.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3053
spectrum_assert exact_3053 complete

theorem exact_3054 : Law3054.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3054
spectrum_assert exact_3054 complete

theorem exact_3055 : Law3055.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3055
spectrum_assert exact_3055 complete

theorem exact_3056 : Law3056.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3056
spectrum_assert exact_3056 complete

theorem exact_3057 : Law3057.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3057
spectrum_assert exact_3057 complete

theorem exact_3058 : Law3058.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3058
spectrum_assert exact_3058 complete

theorem exact_3059 : Law3059.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3059
spectrum_assert exact_3059 complete

theorem exact_3060 : Law3060.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3060
spectrum_assert exact_3060 complete

theorem exact_3061 : Law3061.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3061
spectrum_assert exact_3061 complete

theorem exact_3062 : Law3062.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3062
spectrum_assert exact_3062 complete

theorem exact_3063 : Law3063.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3063
spectrum_assert exact_3063 complete

theorem exact_3064 : Law3064.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3064
spectrum_assert exact_3064 complete

theorem exact_3065 : Law3065.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3065
spectrum_assert exact_3065 complete

theorem exact_3066 : Law3066.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3066
spectrum_assert exact_3066 complete

theorem exact_3067 : Law3067.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3067
spectrum_assert exact_3067 complete

theorem exact_3068 : Law3068.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3068
spectrum_assert exact_3068 complete

theorem exact_3069 : Law3069.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3069
spectrum_assert exact_3069 complete

theorem exact_3070 : Law3070.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3070
spectrum_assert exact_3070 complete

theorem exact_3071 : Law3071.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3071
spectrum_assert exact_3071 complete

theorem exact_3072 : Law3072.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3072
spectrum_assert exact_3072 complete

theorem exact_3073 : Law3073.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3073
spectrum_assert exact_3073 complete

theorem exact_3074 : Law3074.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3074
spectrum_assert exact_3074 complete

theorem exact_3075 : Law3075.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3075
spectrum_assert exact_3075 complete

theorem exact_3076 : Law3076.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3076
spectrum_assert exact_3076 complete

theorem exact_3077 : Law3077.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3077
spectrum_assert exact_3077 complete

theorem exact_3078 : Law3078.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3078
spectrum_assert exact_3078 complete

theorem exact_3079 : Law3079.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3079
spectrum_assert exact_3079 complete

theorem exact_3080 : Law3080.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3080
spectrum_assert exact_3080 complete

theorem exact_3081 : Law3081.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3081
spectrum_assert exact_3081 complete

theorem exact_3082 : Law3082.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3082
spectrum_assert exact_3082 complete

theorem exact_3083 : Law3083.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3083
spectrum_assert exact_3083 complete

theorem exact_3084 : Law3084.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3084
spectrum_assert exact_3084 complete

theorem exact_3085 : Law3085.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3085
spectrum_assert exact_3085 complete

theorem exact_3086 : Law3086.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3086
spectrum_assert exact_3086 complete

theorem exact_3087 : Law3087.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3087
spectrum_assert exact_3087 complete

theorem exact_3088 : Law3088.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3088
spectrum_assert exact_3088 complete

theorem exact_3089 : Law3089.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3089
spectrum_assert exact_3089 complete

theorem exact_3090 : Law3090.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3090
spectrum_assert exact_3090 complete

theorem exact_3091 : Law3091.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3091
spectrum_assert exact_3091 complete

theorem exact_3092 : Law3092.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3092
spectrum_assert exact_3092 complete

theorem exact_3093 : Law3093.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3093
spectrum_assert exact_3093 complete

theorem exact_3094 : Law3094.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3094
spectrum_assert exact_3094 complete

theorem exact_3095 : Law3095.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3095
spectrum_assert exact_3095 complete

theorem exact_3096 : Law3096.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3096
spectrum_assert exact_3096 complete

theorem exact_3097 : Law3097.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3097
spectrum_assert exact_3097 complete

theorem exact_3098 : Law3098.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3098
spectrum_assert exact_3098 complete

theorem exact_3099 : Law3099.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3099
spectrum_assert exact_3099 complete

theorem exact_3100 : Law3100.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3100
spectrum_assert exact_3100 complete

theorem exact_3101 : Law3101.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3101
spectrum_assert exact_3101 complete

theorem exact_3102 : Law3102.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3102
spectrum_assert exact_3102 complete

theorem exact_3103 : Law3103.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3103
spectrum_assert exact_3103 complete

theorem exact_3104 : Law3104.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3104
spectrum_assert exact_3104 complete

theorem exact_3105 : Law3105.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3105
spectrum_assert exact_3105 complete

-- UNKNOWN exact spectrum (PDF representative E501).
theorem lower_3106 : (({1, 4, 5, 8, 9} : Set ℕ)) ⊆ Law3106.spectrum := by
  rw [ImplicationTransfer.spectrum_3106_eq_501]
  exact Note.lower_501
spectrum_assert lower_3106 complete

theorem upper_3106 : Law3106.spectrum ⊆ (positiveExcept {2}) := by
  rw [ImplicationTransfer.spectrum_3106_eq_501]
  exact Note.upper_501
spectrum_assert upper_3106 complete

theorem exact_3107 : Law3107.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3107
spectrum_assert exact_3107 complete

theorem exact_3108 : Law3108.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3108
spectrum_assert exact_3108 complete

theorem exact_3109 : Law3109.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3109
spectrum_assert exact_3109 complete

theorem exact_3110 : Law3110.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3110
spectrum_assert exact_3110 complete

theorem exact_3111 : Law3111.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3111
spectrum_assert exact_3111 complete

theorem exact_3112 : Law3112.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3112
spectrum_assert exact_3112 complete

theorem exact_3113 : Law3113.spectrum = (positiveExcept {2, 4}) :=
  ImplicationTransfer.spectrum_3113_eq_474 |>.trans Note.exact_474
spectrum_assert exact_3113 complete

theorem exact_3114 : Law3114.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3114
spectrum_assert exact_3114 complete

theorem exact_3115 : Law3115.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3115
spectrum_assert exact_3115 complete

theorem exact_3116 : Law3116.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3116
spectrum_assert exact_3116 complete

theorem exact_3117 : Law3117.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3117
spectrum_assert exact_3117 complete

theorem exact_3118 : Law3118.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3118
spectrum_assert exact_3118 complete

theorem exact_3119 : Law3119.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3119
spectrum_assert exact_3119 complete

theorem exact_3120 : Law3120.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3120
spectrum_assert exact_3120 complete

theorem exact_3121 : Law3121.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3121
spectrum_assert exact_3121 complete

theorem exact_3122 : Law3122.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3122
spectrum_assert exact_3122 complete

theorem exact_3123 : Law3123.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3123
spectrum_assert exact_3123 complete

theorem exact_3124 : Law3124.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3124
spectrum_assert exact_3124 complete

theorem exact_3125 : Law3125.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3125
spectrum_assert exact_3125 complete

theorem exact_3126 : Law3126.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3126
spectrum_assert exact_3126 complete

theorem exact_3127 : Law3127.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3127
spectrum_assert exact_3127 complete

theorem exact_3128 : Law3128.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_3128_eq_556 |>.trans Note.exact_556
spectrum_assert exact_3128 complete

theorem exact_3129 : Law3129.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3129
spectrum_assert exact_3129 complete

theorem exact_3130 : Law3130.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3130
spectrum_assert exact_3130 complete

theorem exact_3131 : Law3131.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3131
spectrum_assert exact_3131 complete

theorem exact_3132 : Law3132.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3132
spectrum_assert exact_3132 complete

theorem exact_3133 : Law3133.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3133
spectrum_assert exact_3133 complete

theorem exact_3134 : Law3134.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3134
spectrum_assert exact_3134 complete

theorem exact_3135 : Law3135.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3135
spectrum_assert exact_3135 complete

theorem exact_3136 : Law3136.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3136
spectrum_assert exact_3136 complete

theorem exact_3137 : Law3137.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3137
spectrum_assert exact_3137 complete

theorem exact_3138 : Law3138.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3138
spectrum_assert exact_3138 complete

theorem exact_3139 : Law3139.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3139
spectrum_assert exact_3139 complete

-- UNKNOWN exact spectrum (PDF representative E467).
theorem lower_3140 : (({1, 5, 7, 8} : Set ℕ) ∪ (oddSumTwoSquares)) ⊆ Law3140.spectrum := by
  rw [ImplicationTransfer.spectrum_3140_eq_467]
  exact Note.lower_467
spectrum_assert lower_3140 proofAvailable

theorem upper_3140 : Law3140.spectrum ⊆ (positiveExcept {2, 3, 4, 6}) := by
  rw [ImplicationTransfer.spectrum_3140_eq_467]
  exact Note.upper_467
spectrum_assert upper_3140 proofAvailable

theorem cofinite_3140 : CofiniteSpectrum Law3140 := by
  unfold CofiniteSpectrum
  rw [ImplicationTransfer.spectrum_3140_eq_467]
  exact Note.cofinite_467
spectrum_assert cofinite_3140 proofAvailable

theorem exact_3141 : Law3141.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3141
spectrum_assert exact_3141 complete

theorem exact_3142 : Law3142.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3142
spectrum_assert exact_3142 complete

theorem exact_3143 : Law3143.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3143
spectrum_assert exact_3143 complete

theorem exact_3144 : Law3144.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3144
spectrum_assert exact_3144 complete

theorem exact_3145 : Law3145.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3145
spectrum_assert exact_3145 complete

theorem exact_3146 : Law3146.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3146
spectrum_assert exact_3146 complete

theorem exact_3147 : Law3147.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3147
spectrum_assert exact_3147 complete

theorem exact_3148 : Law3148.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3148
spectrum_assert exact_3148 complete

theorem exact_3149 : Law3149.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3149
spectrum_assert exact_3149 complete

theorem exact_3150 : Law3150.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3150
spectrum_assert exact_3150 complete

theorem exact_3151 : Law3151.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3151
spectrum_assert exact_3151 complete

theorem exact_3152 : Law3152.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3152
spectrum_assert exact_3152 complete

theorem exact_3153 : Law3153.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3153
spectrum_assert exact_3153 complete

theorem exact_3154 : Law3154.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3154
spectrum_assert exact_3154 complete

theorem exact_3155 : Law3155.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3155
spectrum_assert exact_3155 complete

theorem exact_3156 : Law3156.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3156
spectrum_assert exact_3156 complete

theorem exact_3157 : Law3157.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3157
spectrum_assert exact_3157 complete

theorem exact_3158 : Law3158.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3158
spectrum_assert exact_3158 complete

theorem exact_3159 : Law3159.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3159
spectrum_assert exact_3159 complete

theorem exact_3160 : Law3160.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3160
spectrum_assert exact_3160 complete

-- UNKNOWN exact spectrum (PDF representative E481).
theorem lower_3161 : (({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law3161.spectrum := by
  rw [ImplicationTransfer.spectrum_3161_eq_481]
  exact Note.lower_481
spectrum_assert lower_3161 proofAvailable

theorem upper_3161 : Law3161.spectrum ⊆ (positiveExcept {3, 6}) := by
  rw [ImplicationTransfer.spectrum_3161_eq_481]
  exact Note.upper_481
spectrum_assert upper_3161 proofAvailable

theorem exact_3162 : Law3162.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3162
spectrum_assert exact_3162 complete

theorem exact_3163 : Law3163.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3163
spectrum_assert exact_3163 complete

theorem exact_3164 : Law3164.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3164
spectrum_assert exact_3164 complete

theorem exact_3165 : Law3165.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3165
spectrum_assert exact_3165 complete

theorem exact_3166 : Law3166.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3166
spectrum_assert exact_3166 complete

theorem exact_3167 : Law3167.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3167
spectrum_assert exact_3167 complete

theorem exact_3168 : Law3168.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3168
spectrum_assert exact_3168 complete

theorem exact_3169 : Law3169.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3169
spectrum_assert exact_3169 complete

theorem exact_3170 : Law3170.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3170
spectrum_assert exact_3170 complete

theorem exact_3171 : Law3171.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3171
spectrum_assert exact_3171 complete

theorem exact_3172 : Law3172.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3172
spectrum_assert exact_3172 complete

theorem exact_3173 : Law3173.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3173
spectrum_assert exact_3173 complete

theorem exact_3174 : Law3174.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3174
spectrum_assert exact_3174 complete

theorem exact_3175 : Law3175.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3175
spectrum_assert exact_3175 complete

theorem exact_3176 : Law3176.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3176
spectrum_assert exact_3176 complete

theorem exact_3177 : Law3177.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3177
spectrum_assert exact_3177 complete

theorem exact_3178 : Law3178.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3178
spectrum_assert exact_3178 complete

theorem exact_3179 : Law3179.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3179
spectrum_assert exact_3179 complete

theorem exact_3180 : Law3180.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3180
spectrum_assert exact_3180 complete

theorem exact_3181 : Law3181.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3181
spectrum_assert exact_3181 complete

theorem exact_3182 : Law3182.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3182
spectrum_assert exact_3182 complete

theorem exact_3183 : Law3183.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3183
spectrum_assert exact_3183 complete

theorem exact_3184 : Law3184.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3184
spectrum_assert exact_3184 complete

theorem exact_3185 : Law3185.spectrum = (sumTwoSquares) :=
  ImplicationTransfer.spectrum_3185_eq_546 |>.trans Note.exact_546
spectrum_assert exact_3185 complete

theorem exact_3186 : Law3186.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3186
spectrum_assert exact_3186 complete

theorem exact_3187 : Law3187.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3187
spectrum_assert exact_3187 complete

theorem exact_3188 : Law3188.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3188
spectrum_assert exact_3188 complete

theorem exact_3189 : Law3189.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3189
spectrum_assert exact_3189 complete

theorem exact_3190 : Law3190.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3190
spectrum_assert exact_3190 complete

theorem exact_3191 : Law3191.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3191
spectrum_assert exact_3191 complete

theorem exact_3192 : Law3192.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3192
spectrum_assert exact_3192 complete

theorem exact_3193 : Law3193.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3193
spectrum_assert exact_3193 complete

theorem exact_3194 : Law3194.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3194
spectrum_assert exact_3194 complete

theorem exact_3195 : Law3195.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3195
spectrum_assert exact_3195 complete

theorem exact_3196 : Law3196.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3196
spectrum_assert exact_3196 complete

theorem exact_3197 : Law3197.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3197
spectrum_assert exact_3197 complete

theorem exact_3198 : Law3198.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3198
spectrum_assert exact_3198 complete

theorem exact_3199 : Law3199.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3199
spectrum_assert exact_3199 complete

theorem exact_3200 : Law3200.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3200
spectrum_assert exact_3200 complete

theorem exact_3201 : Law3201.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3201
spectrum_assert exact_3201 complete

theorem exact_3202 : Law3202.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3202
spectrum_assert exact_3202 complete

theorem exact_3203 : Law3203.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3203
spectrum_assert exact_3203 complete

theorem exact_3204 : Law3204.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3204
spectrum_assert exact_3204 complete

theorem exact_3205 : Law3205.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3205
spectrum_assert exact_3205 complete

theorem exact_3206 : Law3206.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3206
spectrum_assert exact_3206 complete

theorem exact_3207 : Law3207.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3207
spectrum_assert exact_3207 complete

theorem exact_3208 : Law3208.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3208
spectrum_assert exact_3208 complete

theorem exact_3209 : Law3209.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3209
spectrum_assert exact_3209 complete

theorem exact_3210 : Law3210.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3210
spectrum_assert exact_3210 complete

theorem exact_3211 : Law3211.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3211
spectrum_assert exact_3211 complete

theorem exact_3212 : Law3212.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3212
spectrum_assert exact_3212 complete

theorem exact_3213 : Law3213.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3213
spectrum_assert exact_3213 complete

theorem exact_3214 : Law3214.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3214
spectrum_assert exact_3214 complete

theorem exact_3215 : Law3215.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3215
spectrum_assert exact_3215 complete

theorem exact_3216 : Law3216.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3216
spectrum_assert exact_3216 complete

theorem exact_3217 : Law3217.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3217
spectrum_assert exact_3217 complete

theorem exact_3218 : Law3218.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3218
spectrum_assert exact_3218 complete

theorem exact_3219 : Law3219.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3219
spectrum_assert exact_3219 complete

theorem exact_3220 : Law3220.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3220
spectrum_assert exact_3220 complete

theorem exact_3221 : Law3221.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3221
spectrum_assert exact_3221 complete

theorem exact_3222 : Law3222.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3222
spectrum_assert exact_3222 complete

theorem exact_3223 : Law3223.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3223
spectrum_assert exact_3223 complete

theorem exact_3224 : Law3224.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3224
spectrum_assert exact_3224 complete

theorem exact_3225 : Law3225.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3225
spectrum_assert exact_3225 complete

theorem exact_3226 : Law3226.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3226
spectrum_assert exact_3226 complete

theorem exact_3227 : Law3227.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3227
spectrum_assert exact_3227 complete

theorem exact_3228 : Law3228.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3228
spectrum_assert exact_3228 complete

theorem exact_3229 : Law3229.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3229
spectrum_assert exact_3229 complete

theorem exact_3230 : Law3230.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3230
spectrum_assert exact_3230 complete

theorem exact_3231 : Law3231.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3231
spectrum_assert exact_3231 complete

theorem exact_3232 : Law3232.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3232
spectrum_assert exact_3232 complete

theorem exact_3233 : Law3233.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3233
spectrum_assert exact_3233 complete

theorem exact_3234 : Law3234.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3234
spectrum_assert exact_3234 complete

theorem exact_3235 : Law3235.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3235
spectrum_assert exact_3235 complete

theorem exact_3236 : Law3236.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3236
spectrum_assert exact_3236 complete

theorem exact_3237 : Law3237.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3237
spectrum_assert exact_3237 complete

theorem exact_3238 : Law3238.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3238
spectrum_assert exact_3238 complete

theorem exact_3239 : Law3239.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3239
spectrum_assert exact_3239 complete

theorem exact_3240 : Law3240.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3240
spectrum_assert exact_3240 complete

theorem exact_3241 : Law3241.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3241
spectrum_assert exact_3241 complete

theorem exact_3242 : Law3242.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3242
spectrum_assert exact_3242 complete

theorem exact_3243 : Law3243.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3243
spectrum_assert exact_3243 complete

theorem exact_3244 : Law3244.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3244
spectrum_assert exact_3244 complete

theorem exact_3245 : Law3245.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3245
spectrum_assert exact_3245 complete

theorem exact_3246 : Law3246.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3246
spectrum_assert exact_3246 complete

theorem exact_3247 : Law3247.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3247
spectrum_assert exact_3247 complete

theorem exact_3248 : Law3248.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3248
spectrum_assert exact_3248 complete

theorem exact_3249 : Law3249.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3249
spectrum_assert exact_3249 complete

theorem exact_3250 : Law3250.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3250
spectrum_assert exact_3250 complete

theorem exact_3251 : Law3251.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3251
spectrum_assert exact_3251 complete

theorem exact_3252 : Law3252.spectrum = ({1}) :=
  ImplicationTransfer.singleton_3252
spectrum_assert exact_3252 complete

theorem exact_3253 : Law3253.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3253
spectrum_assert exact_3253 complete

theorem exact_3254 : Law3254.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3254
spectrum_assert exact_3254 complete

theorem exact_3255 : Law3255.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3255
spectrum_assert exact_3255 complete

theorem exact_3256 : Law3256.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3256
spectrum_assert exact_3256 complete

theorem exact_3257 : Law3257.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3257
spectrum_assert exact_3257 complete

theorem exact_3258 : Law3258.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3258
spectrum_assert exact_3258 complete

theorem exact_3259 : Law3259.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3259
spectrum_assert exact_3259 complete

theorem exact_3260 : Law3260.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3260
spectrum_assert exact_3260 complete

theorem exact_3261 : Law3261.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3261
spectrum_assert exact_3261 complete

theorem exact_3262 : Law3262.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3262
spectrum_assert exact_3262 complete

theorem exact_3263 : Law3263.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3263
spectrum_assert exact_3263 complete

theorem exact_3264 : Law3264.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3264
spectrum_assert exact_3264 complete

theorem exact_3265 : Law3265.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3265
spectrum_assert exact_3265 complete

theorem exact_3266 : Law3266.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3266
spectrum_assert exact_3266 complete

theorem exact_3267 : Law3267.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3267
spectrum_assert exact_3267 complete

theorem exact_3268 : Law3268.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3268
spectrum_assert exact_3268 complete

theorem exact_3269 : Law3269.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3269
spectrum_assert exact_3269 complete

theorem exact_3270 : Law3270.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3270
spectrum_assert exact_3270 complete

theorem exact_3271 : Law3271.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3271
spectrum_assert exact_3271 complete

theorem exact_3272 : Law3272.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3272
spectrum_assert exact_3272 complete

theorem exact_3273 : Law3273.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3273
spectrum_assert exact_3273 complete

theorem exact_3274 : Law3274.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3274
spectrum_assert exact_3274 complete

theorem exact_3275 : Law3275.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3275
spectrum_assert exact_3275 complete

theorem exact_3276 : Law3276.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3276
spectrum_assert exact_3276 complete

theorem exact_3277 : Law3277.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3277
spectrum_assert exact_3277 complete

theorem exact_3278 : Law3278.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3278
spectrum_assert exact_3278 complete

theorem exact_3279 : Law3279.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3279
spectrum_assert exact_3279 complete

theorem exact_3280 : Law3280.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3280
spectrum_assert exact_3280 complete

theorem exact_3281 : Law3281.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3281
spectrum_assert exact_3281 complete

theorem exact_3282 : Law3282.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3282
spectrum_assert exact_3282 complete

theorem exact_3283 : Law3283.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3283
spectrum_assert exact_3283 complete

theorem exact_3284 : Law3284.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3284
spectrum_assert exact_3284 complete

theorem exact_3285 : Law3285.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3285
spectrum_assert exact_3285 complete

theorem exact_3286 : Law3286.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3286
spectrum_assert exact_3286 complete

theorem exact_3287 : Law3287.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3287
spectrum_assert exact_3287 complete

theorem exact_3288 : Law3288.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3288
spectrum_assert exact_3288 complete

theorem exact_3289 : Law3289.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3289
spectrum_assert exact_3289 complete

theorem exact_3290 : Law3290.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3290
spectrum_assert exact_3290 complete

theorem exact_3291 : Law3291.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3291
spectrum_assert exact_3291 complete

theorem exact_3292 : Law3292.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3292
spectrum_assert exact_3292 complete

theorem exact_3293 : Law3293.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3293
spectrum_assert exact_3293 complete

theorem exact_3294 : Law3294.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3294
spectrum_assert exact_3294 complete

theorem exact_3295 : Law3295.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3295
spectrum_assert exact_3295 complete

theorem exact_3296 : Law3296.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3296
spectrum_assert exact_3296 complete

theorem exact_3297 : Law3297.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3297
spectrum_assert exact_3297 complete

theorem exact_3298 : Law3298.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3298
spectrum_assert exact_3298 complete

theorem exact_3299 : Law3299.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3299
spectrum_assert exact_3299 complete

theorem exact_3300 : Law3300.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3300
spectrum_assert exact_3300 complete

theorem exact_3301 : Law3301.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3301
spectrum_assert exact_3301 complete

theorem exact_3302 : Law3302.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3302
spectrum_assert exact_3302 complete

theorem exact_3303 : Law3303.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3303
spectrum_assert exact_3303 complete

theorem exact_3304 : Law3304.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3304
spectrum_assert exact_3304 complete

theorem exact_3305 : Law3305.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3305
spectrum_assert exact_3305 complete

theorem exact_3306 : Law3306.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3306
spectrum_assert exact_3306 complete

theorem exact_3307 : Law3307.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3307
spectrum_assert exact_3307 complete

theorem exact_3308 : Law3308.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3308
spectrum_assert exact_3308 complete

theorem exact_3309 : Law3309.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3309
spectrum_assert exact_3309 complete

theorem exact_3310 : Law3310.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3310
spectrum_assert exact_3310 complete

theorem exact_3311 : Law3311.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3311
spectrum_assert exact_3311 complete

theorem exact_3312 : Law3312.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3312
spectrum_assert exact_3312 complete

theorem exact_3313 : Law3313.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3313
spectrum_assert exact_3313 complete

theorem exact_3314 : Law3314.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3314
spectrum_assert exact_3314 complete

theorem exact_3315 : Law3315.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3315
spectrum_assert exact_3315 complete

theorem exact_3316 : Law3316.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3316
spectrum_assert exact_3316 complete

theorem exact_3317 : Law3317.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3317
spectrum_assert exact_3317 complete

theorem exact_3318 : Law3318.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3318
spectrum_assert exact_3318 complete

theorem exact_3319 : Law3319.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3319
spectrum_assert exact_3319 complete

theorem exact_3320 : Law3320.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3320
spectrum_assert exact_3320 complete

theorem exact_3321 : Law3321.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3321
spectrum_assert exact_3321 complete

theorem exact_3322 : Law3322.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3322
spectrum_assert exact_3322 complete

theorem exact_3323 : Law3323.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3323
spectrum_assert exact_3323 complete

theorem exact_3324 : Law3324.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3324
spectrum_assert exact_3324 complete

theorem exact_3325 : Law3325.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3325
spectrum_assert exact_3325 complete

theorem exact_3326 : Law3326.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3326
spectrum_assert exact_3326 complete

theorem exact_3327 : Law3327.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3327
spectrum_assert exact_3327 complete

theorem exact_3328 : Law3328.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3328
spectrum_assert exact_3328 complete

theorem exact_3329 : Law3329.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3329
spectrum_assert exact_3329 complete

theorem exact_3330 : Law3330.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3330
spectrum_assert exact_3330 complete

theorem exact_3331 : Law3331.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3331
spectrum_assert exact_3331 complete

theorem exact_3332 : Law3332.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3332
spectrum_assert exact_3332 complete

theorem exact_3333 : Law3333.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3333
spectrum_assert exact_3333 complete

theorem exact_3334 : Law3334.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3334
spectrum_assert exact_3334 complete

theorem exact_3335 : Law3335.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3335
spectrum_assert exact_3335 complete

theorem exact_3336 : Law3336.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3336
spectrum_assert exact_3336 complete

theorem exact_3337 : Law3337.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3337
spectrum_assert exact_3337 complete

theorem exact_3338 : Law3338.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3338
spectrum_assert exact_3338 complete

theorem exact_3339 : Law3339.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3339
spectrum_assert exact_3339 complete

theorem exact_3340 : Law3340.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3340
spectrum_assert exact_3340 complete

theorem exact_3341 : Law3341.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3341
spectrum_assert exact_3341 complete

theorem exact_3342 : Law3342.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3342
spectrum_assert exact_3342 complete

theorem exact_3343 : Law3343.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3343
spectrum_assert exact_3343 complete

theorem exact_3344 : Law3344.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3344
spectrum_assert exact_3344 complete

theorem exact_3345 : Law3345.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3345
spectrum_assert exact_3345 complete

theorem exact_3346 : Law3346.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3346
spectrum_assert exact_3346 complete

theorem exact_3347 : Law3347.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3347
spectrum_assert exact_3347 complete

theorem exact_3348 : Law3348.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3348
spectrum_assert exact_3348 complete

theorem exact_3349 : Law3349.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3349
spectrum_assert exact_3349 complete

theorem exact_3350 : Law3350.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3350
spectrum_assert exact_3350 complete

theorem exact_3351 : Law3351.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3351
spectrum_assert exact_3351 complete

theorem exact_3352 : Law3352.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3352
spectrum_assert exact_3352 complete

theorem exact_3353 : Law3353.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3353
spectrum_assert exact_3353 complete

theorem exact_3354 : Law3354.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3354
spectrum_assert exact_3354 complete

theorem exact_3355 : Law3355.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3355
spectrum_assert exact_3355 complete

theorem exact_3356 : Law3356.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3356
spectrum_assert exact_3356 complete

theorem exact_3357 : Law3357.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3357
spectrum_assert exact_3357 complete

theorem exact_3358 : Law3358.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3358
spectrum_assert exact_3358 complete

theorem exact_3359 : Law3359.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3359
spectrum_assert exact_3359 complete

theorem exact_3360 : Law3360.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3360
spectrum_assert exact_3360 complete

theorem exact_3361 : Law3361.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3361
spectrum_assert exact_3361 complete

theorem exact_3362 : Law3362.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3362
spectrum_assert exact_3362 complete

theorem exact_3363 : Law3363.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3363
spectrum_assert exact_3363 complete

theorem exact_3364 : Law3364.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3364
spectrum_assert exact_3364 complete

theorem exact_3365 : Law3365.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3365
spectrum_assert exact_3365 complete

theorem exact_3366 : Law3366.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3366
spectrum_assert exact_3366 complete

theorem exact_3367 : Law3367.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3367
spectrum_assert exact_3367 complete

theorem exact_3368 : Law3368.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3368
spectrum_assert exact_3368 complete

theorem exact_3369 : Law3369.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3369
spectrum_assert exact_3369 complete

theorem exact_3370 : Law3370.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3370
spectrum_assert exact_3370 complete

theorem exact_3371 : Law3371.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3371
spectrum_assert exact_3371 complete

theorem exact_3372 : Law3372.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3372
spectrum_assert exact_3372 complete

theorem exact_3373 : Law3373.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3373
spectrum_assert exact_3373 complete

theorem exact_3374 : Law3374.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3374
spectrum_assert exact_3374 complete

theorem exact_3375 : Law3375.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3375
spectrum_assert exact_3375 complete

theorem exact_3376 : Law3376.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3376
spectrum_assert exact_3376 complete

theorem exact_3377 : Law3377.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3377
spectrum_assert exact_3377 complete

theorem exact_3378 : Law3378.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3378
spectrum_assert exact_3378 complete

theorem exact_3379 : Law3379.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3379
spectrum_assert exact_3379 complete

theorem exact_3380 : Law3380.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3380
spectrum_assert exact_3380 complete

theorem exact_3381 : Law3381.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3381
spectrum_assert exact_3381 complete

theorem exact_3382 : Law3382.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3382
spectrum_assert exact_3382 complete

theorem exact_3383 : Law3383.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3383
spectrum_assert exact_3383 complete

theorem exact_3384 : Law3384.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3384
spectrum_assert exact_3384 complete

theorem exact_3385 : Law3385.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3385
spectrum_assert exact_3385 complete

theorem exact_3386 : Law3386.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3386
spectrum_assert exact_3386 complete

theorem exact_3387 : Law3387.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3387
spectrum_assert exact_3387 complete

theorem exact_3388 : Law3388.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3388
spectrum_assert exact_3388 complete

theorem exact_3389 : Law3389.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3389
spectrum_assert exact_3389 complete

theorem exact_3390 : Law3390.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3390
spectrum_assert exact_3390 complete

theorem exact_3391 : Law3391.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3391
spectrum_assert exact_3391 complete

theorem exact_3392 : Law3392.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3392
spectrum_assert exact_3392 complete

theorem exact_3393 : Law3393.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3393
spectrum_assert exact_3393 complete

theorem exact_3394 : Law3394.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3394
spectrum_assert exact_3394 complete

theorem exact_3395 : Law3395.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3395
spectrum_assert exact_3395 complete

theorem exact_3396 : Law3396.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3396
spectrum_assert exact_3396 complete

theorem exact_3397 : Law3397.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3397
spectrum_assert exact_3397 complete

theorem exact_3398 : Law3398.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3398
spectrum_assert exact_3398 complete

theorem exact_3399 : Law3399.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3399
spectrum_assert exact_3399 complete

theorem exact_3400 : Law3400.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3400
spectrum_assert exact_3400 complete

theorem exact_3401 : Law3401.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3401
spectrum_assert exact_3401 complete

theorem exact_3402 : Law3402.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3402
spectrum_assert exact_3402 complete

theorem exact_3403 : Law3403.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3403
spectrum_assert exact_3403 complete

theorem exact_3404 : Law3404.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3404
spectrum_assert exact_3404 complete

theorem exact_3405 : Law3405.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3405
spectrum_assert exact_3405 complete

theorem exact_3406 : Law3406.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3406
spectrum_assert exact_3406 complete

theorem exact_3407 : Law3407.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3407
spectrum_assert exact_3407 complete

theorem exact_3408 : Law3408.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3408
spectrum_assert exact_3408 complete

theorem exact_3409 : Law3409.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3409
spectrum_assert exact_3409 complete

theorem exact_3410 : Law3410.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3410
spectrum_assert exact_3410 complete

theorem exact_3411 : Law3411.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3411
spectrum_assert exact_3411 complete

theorem exact_3412 : Law3412.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3412
spectrum_assert exact_3412 complete

theorem exact_3413 : Law3413.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3413
spectrum_assert exact_3413 complete

theorem exact_3414 : Law3414.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3414
spectrum_assert exact_3414 complete

theorem exact_3415 : Law3415.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3415
spectrum_assert exact_3415 complete

theorem exact_3416 : Law3416.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3416
spectrum_assert exact_3416 complete

theorem exact_3417 : Law3417.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3417
spectrum_assert exact_3417 complete

theorem exact_3418 : Law3418.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3418
spectrum_assert exact_3418 complete

theorem exact_3419 : Law3419.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3419
spectrum_assert exact_3419 complete

theorem exact_3420 : Law3420.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3420
spectrum_assert exact_3420 complete

theorem exact_3421 : Law3421.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3421
spectrum_assert exact_3421 complete

theorem exact_3422 : Law3422.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3422
spectrum_assert exact_3422 complete

theorem exact_3423 : Law3423.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3423
spectrum_assert exact_3423 complete

theorem exact_3424 : Law3424.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3424
spectrum_assert exact_3424 complete

theorem exact_3425 : Law3425.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3425
spectrum_assert exact_3425 complete

theorem exact_3426 : Law3426.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3426
spectrum_assert exact_3426 complete

theorem exact_3427 : Law3427.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3427
spectrum_assert exact_3427 complete

theorem exact_3428 : Law3428.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3428
spectrum_assert exact_3428 complete

theorem exact_3429 : Law3429.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3429
spectrum_assert exact_3429 complete

theorem exact_3430 : Law3430.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3430
spectrum_assert exact_3430 complete

theorem exact_3431 : Law3431.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3431
spectrum_assert exact_3431 complete

theorem exact_3432 : Law3432.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3432
spectrum_assert exact_3432 complete

theorem exact_3433 : Law3433.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3433
spectrum_assert exact_3433 complete

theorem exact_3434 : Law3434.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3434
spectrum_assert exact_3434 complete

theorem exact_3435 : Law3435.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3435
spectrum_assert exact_3435 complete

theorem exact_3436 : Law3436.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3436
spectrum_assert exact_3436 complete

theorem exact_3437 : Law3437.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3437
spectrum_assert exact_3437 complete

theorem exact_3438 : Law3438.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3438
spectrum_assert exact_3438 complete

theorem exact_3439 : Law3439.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3439
spectrum_assert exact_3439 complete

theorem exact_3440 : Law3440.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3440
spectrum_assert exact_3440 complete

theorem exact_3441 : Law3441.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3441
spectrum_assert exact_3441 complete

theorem exact_3442 : Law3442.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3442
spectrum_assert exact_3442 complete

theorem exact_3443 : Law3443.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3443
spectrum_assert exact_3443 complete

theorem exact_3444 : Law3444.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3444
spectrum_assert exact_3444 complete

theorem exact_3445 : Law3445.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3445
spectrum_assert exact_3445 complete

theorem exact_3446 : Law3446.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3446
spectrum_assert exact_3446 complete

theorem exact_3447 : Law3447.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3447
spectrum_assert exact_3447 complete

theorem exact_3448 : Law3448.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3448
spectrum_assert exact_3448 complete

theorem exact_3449 : Law3449.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3449
spectrum_assert exact_3449 complete

theorem exact_3450 : Law3450.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3450
spectrum_assert exact_3450 complete

theorem exact_3451 : Law3451.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3451
spectrum_assert exact_3451 complete

theorem exact_3452 : Law3452.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3452
spectrum_assert exact_3452 complete

theorem exact_3453 : Law3453.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3453
spectrum_assert exact_3453 complete

theorem exact_3454 : Law3454.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3454
spectrum_assert exact_3454 complete

theorem exact_3455 : Law3455.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3455
spectrum_assert exact_3455 complete

theorem exact_3456 : Law3456.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3456
spectrum_assert exact_3456 complete

theorem exact_3457 : Law3457.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3457
spectrum_assert exact_3457 complete

theorem exact_3458 : Law3458.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3458
spectrum_assert exact_3458 complete

theorem exact_3459 : Law3459.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3459
spectrum_assert exact_3459 complete

theorem exact_3460 : Law3460.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3460
spectrum_assert exact_3460 complete

theorem exact_3461 : Law3461.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3461
spectrum_assert exact_3461 complete

theorem exact_3462 : Law3462.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3462
spectrum_assert exact_3462 complete

theorem exact_3463 : Law3463.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3463
spectrum_assert exact_3463 complete

theorem exact_3464 : Law3464.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3464
spectrum_assert exact_3464 complete

theorem exact_3465 : Law3465.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3465
spectrum_assert exact_3465 complete

theorem exact_3466 : Law3466.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3466
spectrum_assert exact_3466 complete

theorem exact_3467 : Law3467.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3467
spectrum_assert exact_3467 complete

theorem exact_3468 : Law3468.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3468
spectrum_assert exact_3468 complete

theorem exact_3469 : Law3469.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3469
spectrum_assert exact_3469 complete

theorem exact_3470 : Law3470.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3470
spectrum_assert exact_3470 complete

theorem exact_3471 : Law3471.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3471
spectrum_assert exact_3471 complete

theorem exact_3472 : Law3472.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3472
spectrum_assert exact_3472 complete

theorem exact_3473 : Law3473.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3473
spectrum_assert exact_3473 complete

theorem exact_3474 : Law3474.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3474
spectrum_assert exact_3474 complete

theorem exact_3475 : Law3475.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3475
spectrum_assert exact_3475 complete

theorem exact_3476 : Law3476.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3476
spectrum_assert exact_3476 complete

theorem exact_3477 : Law3477.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3477
spectrum_assert exact_3477 complete

theorem exact_3478 : Law3478.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3478
spectrum_assert exact_3478 complete

theorem exact_3479 : Law3479.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3479
spectrum_assert exact_3479 complete

theorem exact_3480 : Law3480.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3480
spectrum_assert exact_3480 complete

theorem exact_3481 : Law3481.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3481
spectrum_assert exact_3481 complete

theorem exact_3482 : Law3482.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3482
spectrum_assert exact_3482 complete

theorem exact_3483 : Law3483.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3483
spectrum_assert exact_3483 complete

theorem exact_3484 : Law3484.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3484
spectrum_assert exact_3484 complete

theorem exact_3485 : Law3485.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3485
spectrum_assert exact_3485 complete

theorem exact_3486 : Law3486.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3486
spectrum_assert exact_3486 complete

theorem exact_3487 : Law3487.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3487
spectrum_assert exact_3487 complete

theorem exact_3488 : Law3488.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3488
spectrum_assert exact_3488 complete

theorem exact_3489 : Law3489.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3489
spectrum_assert exact_3489 complete

theorem exact_3490 : Law3490.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3490
spectrum_assert exact_3490 complete

theorem exact_3491 : Law3491.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3491
spectrum_assert exact_3491 complete

theorem exact_3492 : Law3492.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3492
spectrum_assert exact_3492 complete

theorem exact_3493 : Law3493.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3493
spectrum_assert exact_3493 complete

theorem exact_3494 : Law3494.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3494
spectrum_assert exact_3494 complete

theorem exact_3495 : Law3495.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3495
spectrum_assert exact_3495 complete

theorem exact_3496 : Law3496.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3496
spectrum_assert exact_3496 complete

theorem exact_3497 : Law3497.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3497
spectrum_assert exact_3497 complete

theorem exact_3498 : Law3498.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3498
spectrum_assert exact_3498 complete

theorem exact_3499 : Law3499.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3499
spectrum_assert exact_3499 complete

theorem exact_3500 : Law3500.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3500
spectrum_assert exact_3500 complete

theorem exact_3501 : Law3501.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3501
spectrum_assert exact_3501 complete

theorem exact_3502 : Law3502.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3502
spectrum_assert exact_3502 complete

theorem exact_3503 : Law3503.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3503
spectrum_assert exact_3503 complete

theorem exact_3504 : Law3504.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3504
spectrum_assert exact_3504 complete

theorem exact_3505 : Law3505.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3505
spectrum_assert exact_3505 complete

theorem exact_3506 : Law3506.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3506
spectrum_assert exact_3506 complete

theorem exact_3507 : Law3507.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3507
spectrum_assert exact_3507 complete

theorem exact_3508 : Law3508.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3508
spectrum_assert exact_3508 complete

theorem exact_3509 : Law3509.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3509
spectrum_assert exact_3509 complete

theorem exact_3510 : Law3510.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3510
spectrum_assert exact_3510 complete

theorem exact_3511 : Law3511.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3511
spectrum_assert exact_3511 complete

theorem exact_3512 : Law3512.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3512
spectrum_assert exact_3512 complete

theorem exact_3513 : Law3513.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3513
spectrum_assert exact_3513 complete

theorem exact_3514 : Law3514.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3514
spectrum_assert exact_3514 complete

theorem exact_3515 : Law3515.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3515
spectrum_assert exact_3515 complete

theorem exact_3516 : Law3516.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3516
spectrum_assert exact_3516 complete

theorem exact_3517 : Law3517.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3517
spectrum_assert exact_3517 complete

theorem exact_3518 : Law3518.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3518
spectrum_assert exact_3518 complete

theorem exact_3519 : Law3519.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3519
spectrum_assert exact_3519 complete

theorem exact_3520 : Law3520.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3520
spectrum_assert exact_3520 complete

theorem exact_3521 : Law3521.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3521
spectrum_assert exact_3521 complete

theorem exact_3522 : Law3522.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3522
spectrum_assert exact_3522 complete

theorem exact_3523 : Law3523.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3523
spectrum_assert exact_3523 complete

theorem exact_3524 : Law3524.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3524
spectrum_assert exact_3524 complete

theorem exact_3525 : Law3525.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3525
spectrum_assert exact_3525 complete

theorem exact_3526 : Law3526.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3526
spectrum_assert exact_3526 complete

theorem exact_3527 : Law3527.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3527
spectrum_assert exact_3527 complete

theorem exact_3528 : Law3528.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3528
spectrum_assert exact_3528 complete

theorem exact_3529 : Law3529.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3529
spectrum_assert exact_3529 complete

theorem exact_3530 : Law3530.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3530
spectrum_assert exact_3530 complete

theorem exact_3531 : Law3531.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3531
spectrum_assert exact_3531 complete

theorem exact_3532 : Law3532.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3532
spectrum_assert exact_3532 complete

theorem exact_3533 : Law3533.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3533
spectrum_assert exact_3533 complete

theorem exact_3534 : Law3534.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3534
spectrum_assert exact_3534 complete

theorem exact_3535 : Law3535.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3535
spectrum_assert exact_3535 complete

theorem exact_3536 : Law3536.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3536
spectrum_assert exact_3536 complete

theorem exact_3537 : Law3537.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3537
spectrum_assert exact_3537 complete

theorem exact_3538 : Law3538.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3538
spectrum_assert exact_3538 complete

theorem exact_3539 : Law3539.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3539
spectrum_assert exact_3539 complete

theorem exact_3540 : Law3540.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3540
spectrum_assert exact_3540 complete

theorem exact_3541 : Law3541.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3541
spectrum_assert exact_3541 complete

theorem exact_3542 : Law3542.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3542
spectrum_assert exact_3542 complete

theorem exact_3543 : Law3543.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3543
spectrum_assert exact_3543 complete

theorem exact_3544 : Law3544.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3544
spectrum_assert exact_3544 complete

theorem exact_3545 : Law3545.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3545
spectrum_assert exact_3545 complete

theorem exact_3546 : Law3546.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3546
spectrum_assert exact_3546 complete

theorem exact_3547 : Law3547.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3547
spectrum_assert exact_3547 complete

theorem exact_3548 : Law3548.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3548
spectrum_assert exact_3548 complete

theorem exact_3549 : Law3549.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3549
spectrum_assert exact_3549 complete

theorem exact_3550 : Law3550.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3550
spectrum_assert exact_3550 complete

theorem exact_3551 : Law3551.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3551
spectrum_assert exact_3551 complete

theorem exact_3552 : Law3552.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3552
spectrum_assert exact_3552 complete

theorem exact_3553 : Law3553.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3553
spectrum_assert exact_3553 complete

theorem exact_3554 : Law3554.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3554
spectrum_assert exact_3554 complete

theorem exact_3555 : Law3555.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3555
spectrum_assert exact_3555 complete

theorem exact_3556 : Law3556.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3556
spectrum_assert exact_3556 complete

theorem exact_3557 : Law3557.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3557
spectrum_assert exact_3557 complete

theorem exact_3558 : Law3558.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3558
spectrum_assert exact_3558 complete

theorem exact_3559 : Law3559.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3559
spectrum_assert exact_3559 complete

theorem exact_3560 : Law3560.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3560
spectrum_assert exact_3560 complete

theorem exact_3561 : Law3561.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3561
spectrum_assert exact_3561 complete

theorem exact_3562 : Law3562.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3562
spectrum_assert exact_3562 complete

theorem exact_3563 : Law3563.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3563
spectrum_assert exact_3563 complete

theorem exact_3564 : Law3564.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3564
spectrum_assert exact_3564 complete

theorem exact_3565 : Law3565.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3565
spectrum_assert exact_3565 complete

theorem exact_3566 : Law3566.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3566
spectrum_assert exact_3566 complete

theorem exact_3567 : Law3567.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3567
spectrum_assert exact_3567 complete

theorem exact_3568 : Law3568.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3568
spectrum_assert exact_3568 complete

theorem exact_3569 : Law3569.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3569
spectrum_assert exact_3569 complete

theorem exact_3570 : Law3570.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3570
spectrum_assert exact_3570 complete

theorem exact_3571 : Law3571.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3571
spectrum_assert exact_3571 complete

theorem exact_3572 : Law3572.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3572
spectrum_assert exact_3572 complete

theorem exact_3573 : Law3573.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3573
spectrum_assert exact_3573 complete

theorem exact_3574 : Law3574.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3574
spectrum_assert exact_3574 complete

theorem exact_3575 : Law3575.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3575
spectrum_assert exact_3575 complete

theorem exact_3576 : Law3576.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3576
spectrum_assert exact_3576 complete

theorem exact_3577 : Law3577.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3577
spectrum_assert exact_3577 complete

theorem exact_3578 : Law3578.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3578
spectrum_assert exact_3578 complete

theorem exact_3579 : Law3579.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3579
spectrum_assert exact_3579 complete

theorem exact_3580 : Law3580.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3580
spectrum_assert exact_3580 complete

theorem exact_3581 : Law3581.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3581
spectrum_assert exact_3581 complete

theorem exact_3582 : Law3582.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3582
spectrum_assert exact_3582 complete

theorem exact_3583 : Law3583.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3583
spectrum_assert exact_3583 complete

theorem exact_3584 : Law3584.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3584
spectrum_assert exact_3584 complete

theorem exact_3585 : Law3585.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3585
spectrum_assert exact_3585 complete

theorem exact_3586 : Law3586.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3586
spectrum_assert exact_3586 complete

theorem exact_3587 : Law3587.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3587
spectrum_assert exact_3587 complete

theorem exact_3588 : Law3588.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3588
spectrum_assert exact_3588 complete

theorem exact_3589 : Law3589.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3589
spectrum_assert exact_3589 complete

theorem exact_3590 : Law3590.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3590
spectrum_assert exact_3590 complete

theorem exact_3591 : Law3591.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3591
spectrum_assert exact_3591 complete

theorem exact_3592 : Law3592.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3592
spectrum_assert exact_3592 complete

theorem exact_3593 : Law3593.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3593
spectrum_assert exact_3593 complete

theorem exact_3594 : Law3594.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3594
spectrum_assert exact_3594 complete

theorem exact_3595 : Law3595.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3595
spectrum_assert exact_3595 complete

theorem exact_3596 : Law3596.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3596
spectrum_assert exact_3596 complete

theorem exact_3597 : Law3597.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3597
spectrum_assert exact_3597 complete

theorem exact_3598 : Law3598.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3598
spectrum_assert exact_3598 complete

theorem exact_3599 : Law3599.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3599
spectrum_assert exact_3599 complete

theorem exact_3600 : Law3600.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3600
spectrum_assert exact_3600 complete

theorem exact_3601 : Law3601.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3601
spectrum_assert exact_3601 complete

theorem exact_3602 : Law3602.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3602
spectrum_assert exact_3602 complete

theorem exact_3603 : Law3603.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3603
spectrum_assert exact_3603 complete

theorem exact_3604 : Law3604.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3604
spectrum_assert exact_3604 complete

theorem exact_3605 : Law3605.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3605
spectrum_assert exact_3605 complete

theorem exact_3606 : Law3606.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3606
spectrum_assert exact_3606 complete

theorem exact_3607 : Law3607.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3607
spectrum_assert exact_3607 complete

theorem exact_3608 : Law3608.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3608
spectrum_assert exact_3608 complete

theorem exact_3609 : Law3609.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3609
spectrum_assert exact_3609 complete

theorem exact_3610 : Law3610.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3610
spectrum_assert exact_3610 complete

theorem exact_3611 : Law3611.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3611
spectrum_assert exact_3611 complete

theorem exact_3612 : Law3612.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3612
spectrum_assert exact_3612 complete

theorem exact_3613 : Law3613.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3613
spectrum_assert exact_3613 complete

theorem exact_3614 : Law3614.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3614
spectrum_assert exact_3614 complete

theorem exact_3615 : Law3615.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3615
spectrum_assert exact_3615 complete

theorem exact_3616 : Law3616.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3616
spectrum_assert exact_3616 complete

theorem exact_3617 : Law3617.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3617
spectrum_assert exact_3617 complete

theorem exact_3618 : Law3618.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3618
spectrum_assert exact_3618 complete

theorem exact_3619 : Law3619.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3619
spectrum_assert exact_3619 complete

theorem exact_3620 : Law3620.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3620
spectrum_assert exact_3620 complete

theorem exact_3621 : Law3621.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3621
spectrum_assert exact_3621 complete

theorem exact_3622 : Law3622.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3622
spectrum_assert exact_3622 complete

theorem exact_3623 : Law3623.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3623
spectrum_assert exact_3623 complete

theorem exact_3624 : Law3624.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3624
spectrum_assert exact_3624 complete

theorem exact_3625 : Law3625.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3625
spectrum_assert exact_3625 complete

theorem exact_3626 : Law3626.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3626
spectrum_assert exact_3626 complete

theorem exact_3627 : Law3627.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3627
spectrum_assert exact_3627 complete

theorem exact_3628 : Law3628.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3628
spectrum_assert exact_3628 complete

theorem exact_3629 : Law3629.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3629
spectrum_assert exact_3629 complete

theorem exact_3630 : Law3630.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3630
spectrum_assert exact_3630 complete

theorem exact_3631 : Law3631.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3631
spectrum_assert exact_3631 complete

theorem exact_3632 : Law3632.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3632
spectrum_assert exact_3632 complete

theorem exact_3633 : Law3633.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3633
spectrum_assert exact_3633 complete

theorem exact_3634 : Law3634.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3634
spectrum_assert exact_3634 complete

theorem exact_3635 : Law3635.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3635
spectrum_assert exact_3635 complete

theorem exact_3636 : Law3636.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3636
spectrum_assert exact_3636 complete

theorem exact_3637 : Law3637.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3637
spectrum_assert exact_3637 complete

theorem exact_3638 : Law3638.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3638
spectrum_assert exact_3638 complete

theorem exact_3639 : Law3639.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3639
spectrum_assert exact_3639 complete

theorem exact_3640 : Law3640.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3640
spectrum_assert exact_3640 complete

theorem exact_3641 : Law3641.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3641
spectrum_assert exact_3641 complete

theorem exact_3642 : Law3642.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3642
spectrum_assert exact_3642 complete

theorem exact_3643 : Law3643.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3643
spectrum_assert exact_3643 complete

theorem exact_3644 : Law3644.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3644
spectrum_assert exact_3644 complete

theorem exact_3645 : Law3645.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3645
spectrum_assert exact_3645 complete

theorem exact_3646 : Law3646.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3646
spectrum_assert exact_3646 complete

theorem exact_3647 : Law3647.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3647
spectrum_assert exact_3647 complete

theorem exact_3648 : Law3648.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3648
spectrum_assert exact_3648 complete

theorem exact_3649 : Law3649.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3649
spectrum_assert exact_3649 complete

theorem exact_3650 : Law3650.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3650
spectrum_assert exact_3650 complete

theorem exact_3651 : Law3651.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3651
spectrum_assert exact_3651 complete

theorem exact_3652 : Law3652.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3652
spectrum_assert exact_3652 complete

theorem exact_3653 : Law3653.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3653
spectrum_assert exact_3653 complete

theorem exact_3654 : Law3654.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3654
spectrum_assert exact_3654 complete

theorem exact_3655 : Law3655.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3655
spectrum_assert exact_3655 complete

theorem exact_3656 : Law3656.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3656
spectrum_assert exact_3656 complete

theorem exact_3657 : Law3657.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3657
spectrum_assert exact_3657 complete

theorem exact_3658 : Law3658.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3658
spectrum_assert exact_3658 complete

theorem exact_3659 : Law3659.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3659
spectrum_assert exact_3659 complete

theorem exact_3660 : Law3660.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3660
spectrum_assert exact_3660 complete

theorem exact_3661 : Law3661.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3661
spectrum_assert exact_3661 complete

theorem exact_3662 : Law3662.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3662
spectrum_assert exact_3662 complete

theorem exact_3663 : Law3663.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3663
spectrum_assert exact_3663 complete

theorem exact_3664 : Law3664.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3664
spectrum_assert exact_3664 complete

theorem exact_3665 : Law3665.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3665
spectrum_assert exact_3665 complete

theorem exact_3666 : Law3666.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3666
spectrum_assert exact_3666 complete

theorem exact_3667 : Law3667.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3667
spectrum_assert exact_3667 complete

theorem exact_3668 : Law3668.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3668
spectrum_assert exact_3668 complete

theorem exact_3669 : Law3669.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3669
spectrum_assert exact_3669 complete

theorem exact_3670 : Law3670.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3670
spectrum_assert exact_3670 complete

theorem exact_3671 : Law3671.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3671
spectrum_assert exact_3671 complete

theorem exact_3672 : Law3672.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3672
spectrum_assert exact_3672 complete

theorem exact_3673 : Law3673.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3673
spectrum_assert exact_3673 complete

theorem exact_3674 : Law3674.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3674
spectrum_assert exact_3674 complete

theorem exact_3675 : Law3675.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3675
spectrum_assert exact_3675 complete

theorem exact_3676 : Law3676.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3676
spectrum_assert exact_3676 complete

theorem exact_3677 : Law3677.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3677
spectrum_assert exact_3677 complete

theorem exact_3678 : Law3678.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3678
spectrum_assert exact_3678 complete

theorem exact_3679 : Law3679.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3679
spectrum_assert exact_3679 complete

theorem exact_3680 : Law3680.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3680
spectrum_assert exact_3680 complete

theorem exact_3681 : Law3681.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3681
spectrum_assert exact_3681 complete

theorem exact_3682 : Law3682.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3682
spectrum_assert exact_3682 complete

theorem exact_3683 : Law3683.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3683
spectrum_assert exact_3683 complete

theorem exact_3684 : Law3684.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3684
spectrum_assert exact_3684 complete

theorem exact_3685 : Law3685.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3685
spectrum_assert exact_3685 complete

theorem exact_3686 : Law3686.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3686
spectrum_assert exact_3686 complete

theorem exact_3687 : Law3687.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3687
spectrum_assert exact_3687 complete

theorem exact_3688 : Law3688.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3688
spectrum_assert exact_3688 complete

theorem exact_3689 : Law3689.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3689
spectrum_assert exact_3689 complete

theorem exact_3690 : Law3690.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3690
spectrum_assert exact_3690 complete

theorem exact_3691 : Law3691.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3691
spectrum_assert exact_3691 complete

theorem exact_3692 : Law3692.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3692
spectrum_assert exact_3692 complete

theorem exact_3693 : Law3693.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3693
spectrum_assert exact_3693 complete

theorem exact_3694 : Law3694.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3694
spectrum_assert exact_3694 complete

theorem exact_3695 : Law3695.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3695
spectrum_assert exact_3695 complete

theorem exact_3696 : Law3696.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3696
spectrum_assert exact_3696 complete

theorem exact_3697 : Law3697.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3697
spectrum_assert exact_3697 complete

theorem exact_3698 : Law3698.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3698
spectrum_assert exact_3698 complete

theorem exact_3699 : Law3699.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3699
spectrum_assert exact_3699 complete

theorem exact_3700 : Law3700.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3700
spectrum_assert exact_3700 complete

theorem exact_3701 : Law3701.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3701
spectrum_assert exact_3701 complete

theorem exact_3702 : Law3702.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3702
spectrum_assert exact_3702 complete

theorem exact_3703 : Law3703.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3703
spectrum_assert exact_3703 complete

theorem exact_3704 : Law3704.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3704
spectrum_assert exact_3704 complete

theorem exact_3705 : Law3705.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3705
spectrum_assert exact_3705 complete

theorem exact_3706 : Law3706.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3706
spectrum_assert exact_3706 complete

theorem exact_3707 : Law3707.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3707
spectrum_assert exact_3707 complete

theorem exact_3708 : Law3708.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3708
spectrum_assert exact_3708 complete

theorem exact_3709 : Law3709.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3709
spectrum_assert exact_3709 complete

theorem exact_3710 : Law3710.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3710
spectrum_assert exact_3710 complete

theorem exact_3711 : Law3711.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3711
spectrum_assert exact_3711 complete

theorem exact_3712 : Law3712.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3712
spectrum_assert exact_3712 complete

theorem exact_3713 : Law3713.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3713
spectrum_assert exact_3713 complete

theorem exact_3714 : Law3714.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3714
spectrum_assert exact_3714 complete

theorem exact_3715 : Law3715.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3715
spectrum_assert exact_3715 complete

theorem exact_3716 : Law3716.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3716
spectrum_assert exact_3716 complete

theorem exact_3717 : Law3717.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3717
spectrum_assert exact_3717 complete

theorem exact_3718 : Law3718.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3718
spectrum_assert exact_3718 complete

theorem exact_3719 : Law3719.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3719
spectrum_assert exact_3719 complete

theorem exact_3720 : Law3720.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3720
spectrum_assert exact_3720 complete

theorem exact_3721 : Law3721.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3721
spectrum_assert exact_3721 complete

theorem exact_3722 : Law3722.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3722
spectrum_assert exact_3722 complete

theorem exact_3723 : Law3723.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3723
spectrum_assert exact_3723 complete

theorem exact_3724 : Law3724.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3724
spectrum_assert exact_3724 complete

theorem exact_3725 : Law3725.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3725
spectrum_assert exact_3725 complete

theorem exact_3726 : Law3726.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3726
spectrum_assert exact_3726 complete

theorem exact_3727 : Law3727.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3727
spectrum_assert exact_3727 complete

theorem exact_3728 : Law3728.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3728
spectrum_assert exact_3728 complete

theorem exact_3729 : Law3729.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3729
spectrum_assert exact_3729 complete

theorem exact_3730 : Law3730.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3730
spectrum_assert exact_3730 complete

theorem exact_3731 : Law3731.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3731
spectrum_assert exact_3731 complete

theorem exact_3732 : Law3732.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3732
spectrum_assert exact_3732 complete

theorem exact_3733 : Law3733.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3733
spectrum_assert exact_3733 complete

theorem exact_3734 : Law3734.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3734
spectrum_assert exact_3734 complete

theorem exact_3735 : Law3735.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3735
spectrum_assert exact_3735 complete

theorem exact_3736 : Law3736.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3736
spectrum_assert exact_3736 complete

theorem exact_3737 : Law3737.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3737
spectrum_assert exact_3737 complete

theorem exact_3738 : Law3738.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3738
spectrum_assert exact_3738 complete

theorem exact_3739 : Law3739.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3739
spectrum_assert exact_3739 complete

theorem exact_3740 : Law3740.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3740
spectrum_assert exact_3740 complete

theorem exact_3741 : Law3741.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3741
spectrum_assert exact_3741 complete

theorem exact_3742 : Law3742.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3742
spectrum_assert exact_3742 complete

theorem exact_3743 : Law3743.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3743
spectrum_assert exact_3743 complete

theorem exact_3744 : Law3744.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3744
spectrum_assert exact_3744 complete

theorem exact_3745 : Law3745.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3745
spectrum_assert exact_3745 complete

theorem exact_3746 : Law3746.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3746
spectrum_assert exact_3746 complete

theorem exact_3747 : Law3747.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3747
spectrum_assert exact_3747 complete

theorem exact_3748 : Law3748.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3748
spectrum_assert exact_3748 complete

theorem exact_3749 : Law3749.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3749
spectrum_assert exact_3749 complete

theorem exact_3750 : Law3750.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3750
spectrum_assert exact_3750 complete

theorem exact_3751 : Law3751.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3751
spectrum_assert exact_3751 complete

theorem exact_3752 : Law3752.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3752
spectrum_assert exact_3752 complete

theorem exact_3753 : Law3753.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3753
spectrum_assert exact_3753 complete

theorem exact_3754 : Law3754.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3754
spectrum_assert exact_3754 complete

theorem exact_3755 : Law3755.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3755
spectrum_assert exact_3755 complete

theorem exact_3756 : Law3756.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3756
spectrum_assert exact_3756 complete

theorem exact_3757 : Law3757.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3757
spectrum_assert exact_3757 complete

theorem exact_3758 : Law3758.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3758
spectrum_assert exact_3758 complete

theorem exact_3759 : Law3759.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3759
spectrum_assert exact_3759 complete

theorem exact_3760 : Law3760.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3760
spectrum_assert exact_3760 complete

theorem exact_3761 : Law3761.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3761
spectrum_assert exact_3761 complete

theorem exact_3762 : Law3762.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3762
spectrum_assert exact_3762 complete

theorem exact_3763 : Law3763.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3763
spectrum_assert exact_3763 complete

theorem exact_3764 : Law3764.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3764
spectrum_assert exact_3764 complete

theorem exact_3765 : Law3765.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3765
spectrum_assert exact_3765 complete

theorem exact_3766 : Law3766.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3766
spectrum_assert exact_3766 complete

theorem exact_3767 : Law3767.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3767
spectrum_assert exact_3767 complete

theorem exact_3768 : Law3768.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3768
spectrum_assert exact_3768 complete

theorem exact_3769 : Law3769.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3769
spectrum_assert exact_3769 complete

theorem exact_3770 : Law3770.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3770
spectrum_assert exact_3770 complete

theorem exact_3771 : Law3771.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3771
spectrum_assert exact_3771 complete

theorem exact_3772 : Law3772.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3772
spectrum_assert exact_3772 complete

theorem exact_3773 : Law3773.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3773
spectrum_assert exact_3773 complete

theorem exact_3774 : Law3774.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3774
spectrum_assert exact_3774 complete

theorem exact_3775 : Law3775.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3775
spectrum_assert exact_3775 complete

theorem exact_3776 : Law3776.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3776
spectrum_assert exact_3776 complete

theorem exact_3777 : Law3777.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3777
spectrum_assert exact_3777 complete

theorem exact_3778 : Law3778.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3778
spectrum_assert exact_3778 complete

theorem exact_3779 : Law3779.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3779
spectrum_assert exact_3779 complete

theorem exact_3780 : Law3780.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3780
spectrum_assert exact_3780 complete

theorem exact_3781 : Law3781.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3781
spectrum_assert exact_3781 complete

theorem exact_3782 : Law3782.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3782
spectrum_assert exact_3782 complete

theorem exact_3783 : Law3783.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3783
spectrum_assert exact_3783 complete

theorem exact_3784 : Law3784.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3784
spectrum_assert exact_3784 complete

theorem exact_3785 : Law3785.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3785
spectrum_assert exact_3785 complete

theorem exact_3786 : Law3786.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3786
spectrum_assert exact_3786 complete

theorem exact_3787 : Law3787.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3787
spectrum_assert exact_3787 complete

theorem exact_3788 : Law3788.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3788
spectrum_assert exact_3788 complete

theorem exact_3789 : Law3789.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3789
spectrum_assert exact_3789 complete

theorem exact_3790 : Law3790.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3790
spectrum_assert exact_3790 complete

theorem exact_3791 : Law3791.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3791
spectrum_assert exact_3791 complete

theorem exact_3792 : Law3792.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3792
spectrum_assert exact_3792 complete

theorem exact_3793 : Law3793.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3793
spectrum_assert exact_3793 complete

theorem exact_3794 : Law3794.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3794
spectrum_assert exact_3794 complete

theorem exact_3795 : Law3795.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3795
spectrum_assert exact_3795 complete

theorem exact_3796 : Law3796.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3796
spectrum_assert exact_3796 complete

theorem exact_3797 : Law3797.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3797
spectrum_assert exact_3797 complete

theorem exact_3798 : Law3798.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3798
spectrum_assert exact_3798 complete

theorem exact_3799 : Law3799.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3799
spectrum_assert exact_3799 complete

theorem exact_3800 : Law3800.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3800
spectrum_assert exact_3800 complete

theorem exact_3801 : Law3801.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3801
spectrum_assert exact_3801 complete

theorem exact_3802 : Law3802.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3802
spectrum_assert exact_3802 complete

theorem exact_3803 : Law3803.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3803
spectrum_assert exact_3803 complete

theorem exact_3804 : Law3804.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3804
spectrum_assert exact_3804 complete

theorem exact_3805 : Law3805.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3805
spectrum_assert exact_3805 complete

theorem exact_3806 : Law3806.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3806
spectrum_assert exact_3806 complete

theorem exact_3807 : Law3807.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3807
spectrum_assert exact_3807 complete

theorem exact_3808 : Law3808.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3808
spectrum_assert exact_3808 complete

theorem exact_3809 : Law3809.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3809
spectrum_assert exact_3809 complete

theorem exact_3810 : Law3810.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3810
spectrum_assert exact_3810 complete

theorem exact_3811 : Law3811.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3811
spectrum_assert exact_3811 complete

theorem exact_3812 : Law3812.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3812
spectrum_assert exact_3812 complete

theorem exact_3813 : Law3813.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3813
spectrum_assert exact_3813 complete

theorem exact_3814 : Law3814.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3814
spectrum_assert exact_3814 complete

theorem exact_3815 : Law3815.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3815
spectrum_assert exact_3815 complete

theorem exact_3816 : Law3816.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3816
spectrum_assert exact_3816 complete

theorem exact_3817 : Law3817.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3817
spectrum_assert exact_3817 complete

theorem exact_3818 : Law3818.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3818
spectrum_assert exact_3818 complete

theorem exact_3819 : Law3819.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3819
spectrum_assert exact_3819 complete

theorem exact_3820 : Law3820.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3820
spectrum_assert exact_3820 complete

theorem exact_3821 : Law3821.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3821
spectrum_assert exact_3821 complete

theorem exact_3822 : Law3822.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3822
spectrum_assert exact_3822 complete

theorem exact_3823 : Law3823.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3823
spectrum_assert exact_3823 complete

theorem exact_3824 : Law3824.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3824
spectrum_assert exact_3824 complete

theorem exact_3825 : Law3825.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3825
spectrum_assert exact_3825 complete

theorem exact_3826 : Law3826.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3826
spectrum_assert exact_3826 complete

theorem exact_3827 : Law3827.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3827
spectrum_assert exact_3827 complete

theorem exact_3828 : Law3828.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3828
spectrum_assert exact_3828 complete

theorem exact_3829 : Law3829.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3829
spectrum_assert exact_3829 complete

theorem exact_3830 : Law3830.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3830
spectrum_assert exact_3830 complete

theorem exact_3831 : Law3831.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3831
spectrum_assert exact_3831 complete

theorem exact_3832 : Law3832.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3832
spectrum_assert exact_3832 complete

theorem exact_3833 : Law3833.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3833
spectrum_assert exact_3833 complete

theorem exact_3834 : Law3834.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3834
spectrum_assert exact_3834 complete

theorem exact_3835 : Law3835.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3835
spectrum_assert exact_3835 complete

theorem exact_3836 : Law3836.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3836
spectrum_assert exact_3836 complete

theorem exact_3837 : Law3837.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3837
spectrum_assert exact_3837 complete

theorem exact_3838 : Law3838.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3838
spectrum_assert exact_3838 complete

theorem exact_3839 : Law3839.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3839
spectrum_assert exact_3839 complete

theorem exact_3840 : Law3840.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3840
spectrum_assert exact_3840 complete

theorem exact_3841 : Law3841.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3841
spectrum_assert exact_3841 complete

theorem exact_3842 : Law3842.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3842
spectrum_assert exact_3842 complete

theorem exact_3843 : Law3843.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3843
spectrum_assert exact_3843 complete

theorem exact_3844 : Law3844.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3844
spectrum_assert exact_3844 complete

theorem exact_3845 : Law3845.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3845
spectrum_assert exact_3845 complete

theorem exact_3846 : Law3846.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3846
spectrum_assert exact_3846 complete

theorem exact_3847 : Law3847.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3847
spectrum_assert exact_3847 complete

theorem exact_3848 : Law3848.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3848
spectrum_assert exact_3848 complete

theorem exact_3849 : Law3849.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3849
spectrum_assert exact_3849 complete

theorem exact_3850 : Law3850.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3850
spectrum_assert exact_3850 complete

theorem exact_3851 : Law3851.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3851
spectrum_assert exact_3851 complete

theorem exact_3852 : Law3852.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3852
spectrum_assert exact_3852 complete

theorem exact_3853 : Law3853.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3853
spectrum_assert exact_3853 complete

theorem exact_3854 : Law3854.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3854
spectrum_assert exact_3854 complete

theorem exact_3855 : Law3855.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3855
spectrum_assert exact_3855 complete

theorem exact_3856 : Law3856.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3856
spectrum_assert exact_3856 complete

theorem exact_3857 : Law3857.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3857
spectrum_assert exact_3857 complete

theorem exact_3858 : Law3858.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3858
spectrum_assert exact_3858 complete

theorem exact_3859 : Law3859.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3859
spectrum_assert exact_3859 complete

theorem exact_3860 : Law3860.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3860
spectrum_assert exact_3860 complete

theorem exact_3861 : Law3861.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3861
spectrum_assert exact_3861 complete

theorem exact_3862 : Law3862.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3862
spectrum_assert exact_3862 complete

theorem exact_3863 : Law3863.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3863
spectrum_assert exact_3863 complete

theorem exact_3864 : Law3864.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3864
spectrum_assert exact_3864 complete

theorem exact_3865 : Law3865.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3865
spectrum_assert exact_3865 complete

theorem exact_3866 : Law3866.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3866
spectrum_assert exact_3866 complete

theorem exact_3867 : Law3867.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3867
spectrum_assert exact_3867 complete

theorem exact_3868 : Law3868.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3868
spectrum_assert exact_3868 complete

theorem exact_3869 : Law3869.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3869
spectrum_assert exact_3869 complete

theorem exact_3870 : Law3870.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3870
spectrum_assert exact_3870 complete

theorem exact_3871 : Law3871.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3871
spectrum_assert exact_3871 complete

theorem exact_3872 : Law3872.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3872
spectrum_assert exact_3872 complete

theorem exact_3873 : Law3873.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3873
spectrum_assert exact_3873 complete

theorem exact_3874 : Law3874.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3874
spectrum_assert exact_3874 complete

theorem exact_3875 : Law3875.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3875
spectrum_assert exact_3875 complete

theorem exact_3876 : Law3876.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3876
spectrum_assert exact_3876 complete

theorem exact_3877 : Law3877.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3877
spectrum_assert exact_3877 complete

theorem exact_3878 : Law3878.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3878
spectrum_assert exact_3878 complete

theorem exact_3879 : Law3879.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3879
spectrum_assert exact_3879 complete

theorem exact_3880 : Law3880.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3880
spectrum_assert exact_3880 complete

theorem exact_3881 : Law3881.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3881
spectrum_assert exact_3881 complete

theorem exact_3882 : Law3882.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3882
spectrum_assert exact_3882 complete

theorem exact_3883 : Law3883.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3883
spectrum_assert exact_3883 complete

theorem exact_3884 : Law3884.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3884
spectrum_assert exact_3884 complete

theorem exact_3885 : Law3885.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3885
spectrum_assert exact_3885 complete

theorem exact_3886 : Law3886.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3886
spectrum_assert exact_3886 complete

theorem exact_3887 : Law3887.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3887
spectrum_assert exact_3887 complete

theorem exact_3888 : Law3888.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3888
spectrum_assert exact_3888 complete

theorem exact_3889 : Law3889.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3889
spectrum_assert exact_3889 complete

theorem exact_3890 : Law3890.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3890
spectrum_assert exact_3890 complete

theorem exact_3891 : Law3891.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3891
spectrum_assert exact_3891 complete

theorem exact_3892 : Law3892.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3892
spectrum_assert exact_3892 complete

theorem exact_3893 : Law3893.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3893
spectrum_assert exact_3893 complete

theorem exact_3894 : Law3894.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3894
spectrum_assert exact_3894 complete

theorem exact_3895 : Law3895.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3895
spectrum_assert exact_3895 complete

theorem exact_3896 : Law3896.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3896
spectrum_assert exact_3896 complete

theorem exact_3897 : Law3897.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3897
spectrum_assert exact_3897 complete

theorem exact_3898 : Law3898.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3898
spectrum_assert exact_3898 complete

theorem exact_3899 : Law3899.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3899
spectrum_assert exact_3899 complete

theorem exact_3900 : Law3900.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3900
spectrum_assert exact_3900 complete

theorem exact_3901 : Law3901.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3901
spectrum_assert exact_3901 complete

theorem exact_3902 : Law3902.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3902
spectrum_assert exact_3902 complete

theorem exact_3903 : Law3903.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3903
spectrum_assert exact_3903 complete

theorem exact_3904 : Law3904.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3904
spectrum_assert exact_3904 complete

theorem exact_3905 : Law3905.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3905
spectrum_assert exact_3905 complete

theorem exact_3906 : Law3906.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3906
spectrum_assert exact_3906 complete

theorem exact_3907 : Law3907.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3907
spectrum_assert exact_3907 complete

theorem exact_3908 : Law3908.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3908
spectrum_assert exact_3908 complete

theorem exact_3909 : Law3909.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3909
spectrum_assert exact_3909 complete

theorem exact_3910 : Law3910.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3910
spectrum_assert exact_3910 complete

theorem exact_3911 : Law3911.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3911
spectrum_assert exact_3911 complete

theorem exact_3912 : Law3912.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3912
spectrum_assert exact_3912 complete

theorem exact_3913 : Law3913.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3913
spectrum_assert exact_3913 complete

theorem exact_3914 : Law3914.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3914
spectrum_assert exact_3914 complete

theorem exact_3915 : Law3915.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3915
spectrum_assert exact_3915 complete

theorem exact_3916 : Law3916.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3916
spectrum_assert exact_3916 complete

theorem exact_3917 : Law3917.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3917
spectrum_assert exact_3917 complete

theorem exact_3918 : Law3918.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3918
spectrum_assert exact_3918 complete

theorem exact_3919 : Law3919.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3919
spectrum_assert exact_3919 complete

theorem exact_3920 : Law3920.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3920
spectrum_assert exact_3920 complete

theorem exact_3921 : Law3921.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3921
spectrum_assert exact_3921 complete

theorem exact_3922 : Law3922.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3922
spectrum_assert exact_3922 complete

theorem exact_3923 : Law3923.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3923
spectrum_assert exact_3923 complete

theorem exact_3924 : Law3924.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3924
spectrum_assert exact_3924 complete

theorem exact_3925 : Law3925.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3925
spectrum_assert exact_3925 complete

theorem exact_3926 : Law3926.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3926
spectrum_assert exact_3926 complete

theorem exact_3927 : Law3927.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3927
spectrum_assert exact_3927 complete

theorem exact_3928 : Law3928.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3928
spectrum_assert exact_3928 complete

theorem exact_3929 : Law3929.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3929
spectrum_assert exact_3929 complete

theorem exact_3930 : Law3930.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3930
spectrum_assert exact_3930 complete

theorem exact_3931 : Law3931.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3931
spectrum_assert exact_3931 complete

theorem exact_3932 : Law3932.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3932
spectrum_assert exact_3932 complete

theorem exact_3933 : Law3933.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3933
spectrum_assert exact_3933 complete

theorem exact_3934 : Law3934.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3934
spectrum_assert exact_3934 complete

theorem exact_3935 : Law3935.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3935
spectrum_assert exact_3935 complete

theorem exact_3936 : Law3936.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3936
spectrum_assert exact_3936 complete

theorem exact_3937 : Law3937.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3937
spectrum_assert exact_3937 complete

theorem exact_3938 : Law3938.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3938
spectrum_assert exact_3938 complete

theorem exact_3939 : Law3939.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3939
spectrum_assert exact_3939 complete

theorem exact_3940 : Law3940.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3940
spectrum_assert exact_3940 complete

theorem exact_3941 : Law3941.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3941
spectrum_assert exact_3941 complete

theorem exact_3942 : Law3942.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3942
spectrum_assert exact_3942 complete

theorem exact_3943 : Law3943.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3943
spectrum_assert exact_3943 complete

theorem exact_3944 : Law3944.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3944
spectrum_assert exact_3944 complete

theorem exact_3945 : Law3945.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3945
spectrum_assert exact_3945 complete

theorem exact_3946 : Law3946.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3946
spectrum_assert exact_3946 complete

theorem exact_3947 : Law3947.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3947
spectrum_assert exact_3947 complete

theorem exact_3948 : Law3948.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3948
spectrum_assert exact_3948 complete

theorem exact_3949 : Law3949.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3949
spectrum_assert exact_3949 complete

theorem exact_3950 : Law3950.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3950
spectrum_assert exact_3950 complete

theorem exact_3951 : Law3951.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3951
spectrum_assert exact_3951 complete

theorem exact_3952 : Law3952.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3952
spectrum_assert exact_3952 complete

theorem exact_3953 : Law3953.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3953
spectrum_assert exact_3953 complete

theorem exact_3954 : Law3954.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3954
spectrum_assert exact_3954 complete

theorem exact_3955 : Law3955.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3955
spectrum_assert exact_3955 complete

theorem exact_3956 : Law3956.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3956
spectrum_assert exact_3956 complete

theorem exact_3957 : Law3957.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3957
spectrum_assert exact_3957 complete

theorem exact_3958 : Law3958.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3958
spectrum_assert exact_3958 complete

theorem exact_3959 : Law3959.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3959
spectrum_assert exact_3959 complete

theorem exact_3960 : Law3960.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3960
spectrum_assert exact_3960 complete

theorem exact_3961 : Law3961.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3961
spectrum_assert exact_3961 complete

theorem exact_3962 : Law3962.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3962
spectrum_assert exact_3962 complete

theorem exact_3963 : Law3963.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3963
spectrum_assert exact_3963 complete

theorem exact_3964 : Law3964.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3964
spectrum_assert exact_3964 complete

theorem exact_3965 : Law3965.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3965
spectrum_assert exact_3965 complete

theorem exact_3966 : Law3966.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3966
spectrum_assert exact_3966 complete

theorem exact_3967 : Law3967.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3967
spectrum_assert exact_3967 complete

theorem exact_3968 : Law3968.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3968
spectrum_assert exact_3968 complete

theorem exact_3969 : Law3969.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3969
spectrum_assert exact_3969 complete

theorem exact_3970 : Law3970.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3970
spectrum_assert exact_3970 complete

theorem exact_3971 : Law3971.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3971
spectrum_assert exact_3971 complete

theorem exact_3972 : Law3972.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3972
spectrum_assert exact_3972 complete

theorem exact_3973 : Law3973.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3973
spectrum_assert exact_3973 complete

theorem exact_3974 : Law3974.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3974
spectrum_assert exact_3974 complete

theorem exact_3975 : Law3975.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3975
spectrum_assert exact_3975 complete

theorem exact_3976 : Law3976.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3976
spectrum_assert exact_3976 complete

theorem exact_3977 : Law3977.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3977
spectrum_assert exact_3977 complete

theorem exact_3978 : Law3978.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3978
spectrum_assert exact_3978 complete

theorem exact_3979 : Law3979.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3979
spectrum_assert exact_3979 complete

theorem exact_3980 : Law3980.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3980
spectrum_assert exact_3980 complete

theorem exact_3981 : Law3981.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3981
spectrum_assert exact_3981 complete

theorem exact_3982 : Law3982.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3982
spectrum_assert exact_3982 complete

theorem exact_3983 : Law3983.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3983
spectrum_assert exact_3983 complete

theorem exact_3984 : Law3984.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3984
spectrum_assert exact_3984 complete

theorem exact_3985 : Law3985.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3985
spectrum_assert exact_3985 complete

theorem exact_3986 : Law3986.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3986
spectrum_assert exact_3986 complete

theorem exact_3987 : Law3987.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3987
spectrum_assert exact_3987 complete

theorem exact_3988 : Law3988.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3988
spectrum_assert exact_3988 complete

theorem exact_3989 : Law3989.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3989
spectrum_assert exact_3989 complete

theorem exact_3990 : Law3990.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3990
spectrum_assert exact_3990 complete

theorem exact_3991 : Law3991.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3991
spectrum_assert exact_3991 complete

theorem exact_3992 : Law3992.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3992
spectrum_assert exact_3992 complete

theorem exact_3993 : Law3993.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3993
spectrum_assert exact_3993 complete

theorem exact_3994 : Law3994.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3994
spectrum_assert exact_3994 complete

theorem exact_3995 : Law3995.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3995
spectrum_assert exact_3995 complete

theorem exact_3996 : Law3996.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3996
spectrum_assert exact_3996 complete

theorem exact_3997 : Law3997.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3997
spectrum_assert exact_3997 complete

theorem exact_3998 : Law3998.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3998
spectrum_assert exact_3998 complete

theorem exact_3999 : Law3999.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_3999
spectrum_assert exact_3999 complete

theorem exact_4000 : Law4000.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4000
spectrum_assert exact_4000 complete

theorem exact_4001 : Law4001.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4001
spectrum_assert exact_4001 complete

theorem exact_4002 : Law4002.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4002
spectrum_assert exact_4002 complete

theorem exact_4003 : Law4003.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4003
spectrum_assert exact_4003 complete

theorem exact_4004 : Law4004.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4004
spectrum_assert exact_4004 complete

theorem exact_4005 : Law4005.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4005
spectrum_assert exact_4005 complete

theorem exact_4006 : Law4006.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4006
spectrum_assert exact_4006 complete

theorem exact_4007 : Law4007.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4007
spectrum_assert exact_4007 complete

theorem exact_4008 : Law4008.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4008
spectrum_assert exact_4008 complete

theorem exact_4009 : Law4009.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4009
spectrum_assert exact_4009 complete

theorem exact_4010 : Law4010.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4010
spectrum_assert exact_4010 complete

theorem exact_4011 : Law4011.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4011
spectrum_assert exact_4011 complete

theorem exact_4012 : Law4012.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4012
spectrum_assert exact_4012 complete

theorem exact_4013 : Law4013.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4013
spectrum_assert exact_4013 complete

theorem exact_4014 : Law4014.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4014
spectrum_assert exact_4014 complete

theorem exact_4015 : Law4015.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4015
spectrum_assert exact_4015 complete

theorem exact_4016 : Law4016.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4016
spectrum_assert exact_4016 complete

theorem exact_4017 : Law4017.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4017
spectrum_assert exact_4017 complete

theorem exact_4018 : Law4018.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4018
spectrum_assert exact_4018 complete

theorem exact_4019 : Law4019.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4019
spectrum_assert exact_4019 complete

theorem exact_4020 : Law4020.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4020
spectrum_assert exact_4020 complete

theorem exact_4021 : Law4021.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4021
spectrum_assert exact_4021 complete

theorem exact_4022 : Law4022.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4022
spectrum_assert exact_4022 complete

theorem exact_4023 : Law4023.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4023
spectrum_assert exact_4023 complete

theorem exact_4024 : Law4024.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4024
spectrum_assert exact_4024 complete

theorem exact_4025 : Law4025.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4025
spectrum_assert exact_4025 complete

theorem exact_4026 : Law4026.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4026
spectrum_assert exact_4026 complete

theorem exact_4027 : Law4027.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4027
spectrum_assert exact_4027 complete

theorem exact_4028 : Law4028.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4028
spectrum_assert exact_4028 complete

theorem exact_4029 : Law4029.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4029
spectrum_assert exact_4029 complete

theorem exact_4030 : Law4030.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4030
spectrum_assert exact_4030 complete

theorem exact_4031 : Law4031.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4031
spectrum_assert exact_4031 complete

theorem exact_4032 : Law4032.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4032
spectrum_assert exact_4032 complete

theorem exact_4033 : Law4033.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4033
spectrum_assert exact_4033 complete

theorem exact_4034 : Law4034.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4034
spectrum_assert exact_4034 complete

theorem exact_4035 : Law4035.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4035
spectrum_assert exact_4035 complete

theorem exact_4036 : Law4036.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4036
spectrum_assert exact_4036 complete

theorem exact_4037 : Law4037.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4037
spectrum_assert exact_4037 complete

theorem exact_4038 : Law4038.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4038
spectrum_assert exact_4038 complete

theorem exact_4039 : Law4039.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4039
spectrum_assert exact_4039 complete

theorem exact_4040 : Law4040.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4040
spectrum_assert exact_4040 complete

theorem exact_4041 : Law4041.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4041
spectrum_assert exact_4041 complete

theorem exact_4042 : Law4042.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4042
spectrum_assert exact_4042 complete

theorem exact_4043 : Law4043.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4043
spectrum_assert exact_4043 complete

theorem exact_4044 : Law4044.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4044
spectrum_assert exact_4044 complete

theorem exact_4045 : Law4045.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4045
spectrum_assert exact_4045 complete

theorem exact_4046 : Law4046.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4046
spectrum_assert exact_4046 complete

theorem exact_4047 : Law4047.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4047
spectrum_assert exact_4047 complete

theorem exact_4048 : Law4048.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4048
spectrum_assert exact_4048 complete

theorem exact_4049 : Law4049.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4049
spectrum_assert exact_4049 complete

theorem exact_4050 : Law4050.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4050
spectrum_assert exact_4050 complete

theorem exact_4051 : Law4051.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4051
spectrum_assert exact_4051 complete

theorem exact_4052 : Law4052.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4052
spectrum_assert exact_4052 complete

theorem exact_4053 : Law4053.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4053
spectrum_assert exact_4053 complete

theorem exact_4054 : Law4054.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4054
spectrum_assert exact_4054 complete

theorem exact_4055 : Law4055.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4055
spectrum_assert exact_4055 complete

theorem exact_4056 : Law4056.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4056
spectrum_assert exact_4056 complete

theorem exact_4057 : Law4057.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4057
spectrum_assert exact_4057 complete

theorem exact_4058 : Law4058.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4058
spectrum_assert exact_4058 complete

theorem exact_4059 : Law4059.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4059
spectrum_assert exact_4059 complete

theorem exact_4060 : Law4060.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4060
spectrum_assert exact_4060 complete

theorem exact_4061 : Law4061.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4061
spectrum_assert exact_4061 complete

theorem exact_4062 : Law4062.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4062
spectrum_assert exact_4062 complete

theorem exact_4063 : Law4063.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4063
spectrum_assert exact_4063 complete

theorem exact_4064 : Law4064.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4064
spectrum_assert exact_4064 complete

theorem exact_4065 : Law4065.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4065
spectrum_assert exact_4065 complete

theorem exact_4066 : Law4066.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4066
spectrum_assert exact_4066 complete

theorem exact_4067 : Law4067.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4067
spectrum_assert exact_4067 complete

theorem exact_4068 : Law4068.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4068
spectrum_assert exact_4068 complete

theorem exact_4069 : Law4069.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4069
spectrum_assert exact_4069 complete

theorem exact_4070 : Law4070.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4070
spectrum_assert exact_4070 complete

theorem exact_4071 : Law4071.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4071
spectrum_assert exact_4071 complete

theorem exact_4072 : Law4072.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4072
spectrum_assert exact_4072 complete

theorem exact_4073 : Law4073.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4073
spectrum_assert exact_4073 complete

theorem exact_4074 : Law4074.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4074
spectrum_assert exact_4074 complete

theorem exact_4075 : Law4075.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4075
spectrum_assert exact_4075 complete

theorem exact_4076 : Law4076.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4076
spectrum_assert exact_4076 complete

theorem exact_4077 : Law4077.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4077
spectrum_assert exact_4077 complete

theorem exact_4078 : Law4078.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4078
spectrum_assert exact_4078 complete

theorem exact_4079 : Law4079.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4079
spectrum_assert exact_4079 complete

theorem exact_4080 : Law4080.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4080
spectrum_assert exact_4080 complete

theorem exact_4081 : Law4081.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4081
spectrum_assert exact_4081 complete

theorem exact_4082 : Law4082.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4082
spectrum_assert exact_4082 complete

theorem exact_4083 : Law4083.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4083
spectrum_assert exact_4083 complete

theorem exact_4084 : Law4084.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4084
spectrum_assert exact_4084 complete

theorem exact_4085 : Law4085.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4085
spectrum_assert exact_4085 complete

theorem exact_4086 : Law4086.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4086
spectrum_assert exact_4086 complete

theorem exact_4087 : Law4087.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4087
spectrum_assert exact_4087 complete

theorem exact_4088 : Law4088.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4088
spectrum_assert exact_4088 complete

theorem exact_4089 : Law4089.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4089
spectrum_assert exact_4089 complete

theorem exact_4090 : Law4090.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4090
spectrum_assert exact_4090 complete

theorem exact_4091 : Law4091.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4091
spectrum_assert exact_4091 complete

theorem exact_4092 : Law4092.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4092
spectrum_assert exact_4092 complete

theorem exact_4093 : Law4093.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4093
spectrum_assert exact_4093 complete

theorem exact_4094 : Law4094.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4094
spectrum_assert exact_4094 complete

theorem exact_4095 : Law4095.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4095
spectrum_assert exact_4095 complete

theorem exact_4096 : Law4096.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4096
spectrum_assert exact_4096 complete

theorem exact_4097 : Law4097.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4097
spectrum_assert exact_4097 complete

theorem exact_4098 : Law4098.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4098
spectrum_assert exact_4098 complete

theorem exact_4099 : Law4099.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4099
spectrum_assert exact_4099 complete

theorem exact_4100 : Law4100.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4100
spectrum_assert exact_4100 complete

theorem exact_4101 : Law4101.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4101
spectrum_assert exact_4101 complete

theorem exact_4102 : Law4102.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4102
spectrum_assert exact_4102 complete

theorem exact_4103 : Law4103.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4103
spectrum_assert exact_4103 complete

theorem exact_4104 : Law4104.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4104
spectrum_assert exact_4104 complete

theorem exact_4105 : Law4105.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4105
spectrum_assert exact_4105 complete

theorem exact_4106 : Law4106.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4106
spectrum_assert exact_4106 complete

theorem exact_4107 : Law4107.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4107
spectrum_assert exact_4107 complete

theorem exact_4108 : Law4108.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4108
spectrum_assert exact_4108 complete

theorem exact_4109 : Law4109.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4109
spectrum_assert exact_4109 complete

theorem exact_4110 : Law4110.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4110
spectrum_assert exact_4110 complete

theorem exact_4111 : Law4111.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4111
spectrum_assert exact_4111 complete

theorem exact_4112 : Law4112.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4112
spectrum_assert exact_4112 complete

theorem exact_4113 : Law4113.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4113
spectrum_assert exact_4113 complete

theorem exact_4114 : Law4114.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4114
spectrum_assert exact_4114 complete

theorem exact_4115 : Law4115.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4115
spectrum_assert exact_4115 complete

theorem exact_4116 : Law4116.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4116
spectrum_assert exact_4116 complete

theorem exact_4117 : Law4117.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4117
spectrum_assert exact_4117 complete

theorem exact_4118 : Law4118.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4118
spectrum_assert exact_4118 complete

theorem exact_4119 : Law4119.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4119
spectrum_assert exact_4119 complete

theorem exact_4120 : Law4120.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4120
spectrum_assert exact_4120 complete

theorem exact_4121 : Law4121.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4121
spectrum_assert exact_4121 complete

theorem exact_4122 : Law4122.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4122
spectrum_assert exact_4122 complete

theorem exact_4123 : Law4123.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4123
spectrum_assert exact_4123 complete

theorem exact_4124 : Law4124.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4124
spectrum_assert exact_4124 complete

theorem exact_4125 : Law4125.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4125
spectrum_assert exact_4125 complete

theorem exact_4126 : Law4126.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4126
spectrum_assert exact_4126 complete

theorem exact_4127 : Law4127.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4127
spectrum_assert exact_4127 complete

theorem exact_4128 : Law4128.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4128
spectrum_assert exact_4128 complete

theorem exact_4129 : Law4129.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4129
spectrum_assert exact_4129 complete

theorem exact_4130 : Law4130.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4130
spectrum_assert exact_4130 complete

theorem exact_4131 : Law4131.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4131
spectrum_assert exact_4131 complete

theorem exact_4132 : Law4132.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4132
spectrum_assert exact_4132 complete

theorem exact_4133 : Law4133.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4133
spectrum_assert exact_4133 complete

theorem exact_4134 : Law4134.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4134
spectrum_assert exact_4134 complete

theorem exact_4135 : Law4135.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4135
spectrum_assert exact_4135 complete

theorem exact_4136 : Law4136.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4136
spectrum_assert exact_4136 complete

theorem exact_4137 : Law4137.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4137
spectrum_assert exact_4137 complete

theorem exact_4138 : Law4138.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4138
spectrum_assert exact_4138 complete

theorem exact_4139 : Law4139.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4139
spectrum_assert exact_4139 complete

theorem exact_4140 : Law4140.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4140
spectrum_assert exact_4140 complete

theorem exact_4141 : Law4141.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4141
spectrum_assert exact_4141 complete

theorem exact_4142 : Law4142.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4142
spectrum_assert exact_4142 complete

theorem exact_4143 : Law4143.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4143
spectrum_assert exact_4143 complete

theorem exact_4144 : Law4144.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4144
spectrum_assert exact_4144 complete

theorem exact_4145 : Law4145.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4145
spectrum_assert exact_4145 complete

theorem exact_4146 : Law4146.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4146
spectrum_assert exact_4146 complete

theorem exact_4147 : Law4147.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4147
spectrum_assert exact_4147 complete

theorem exact_4148 : Law4148.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4148
spectrum_assert exact_4148 complete

theorem exact_4149 : Law4149.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4149
spectrum_assert exact_4149 complete

theorem exact_4150 : Law4150.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4150
spectrum_assert exact_4150 complete

theorem exact_4151 : Law4151.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4151
spectrum_assert exact_4151 complete

theorem exact_4152 : Law4152.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4152
spectrum_assert exact_4152 complete

theorem exact_4153 : Law4153.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4153
spectrum_assert exact_4153 complete

theorem exact_4154 : Law4154.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4154
spectrum_assert exact_4154 complete

theorem exact_4155 : Law4155.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4155
spectrum_assert exact_4155 complete

theorem exact_4156 : Law4156.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4156
spectrum_assert exact_4156 complete

theorem exact_4157 : Law4157.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4157
spectrum_assert exact_4157 complete

theorem exact_4158 : Law4158.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4158
spectrum_assert exact_4158 complete

theorem exact_4159 : Law4159.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4159
spectrum_assert exact_4159 complete

theorem exact_4160 : Law4160.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4160
spectrum_assert exact_4160 complete

theorem exact_4161 : Law4161.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4161
spectrum_assert exact_4161 complete

theorem exact_4162 : Law4162.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4162
spectrum_assert exact_4162 complete

theorem exact_4163 : Law4163.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4163
spectrum_assert exact_4163 complete

theorem exact_4164 : Law4164.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4164
spectrum_assert exact_4164 complete

theorem exact_4165 : Law4165.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4165
spectrum_assert exact_4165 complete

theorem exact_4166 : Law4166.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4166
spectrum_assert exact_4166 complete

theorem exact_4167 : Law4167.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4167
spectrum_assert exact_4167 complete

theorem exact_4168 : Law4168.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4168
spectrum_assert exact_4168 complete

theorem exact_4169 : Law4169.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4169
spectrum_assert exact_4169 complete

theorem exact_4170 : Law4170.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4170
spectrum_assert exact_4170 complete

theorem exact_4171 : Law4171.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4171
spectrum_assert exact_4171 complete

theorem exact_4172 : Law4172.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4172
spectrum_assert exact_4172 complete

theorem exact_4173 : Law4173.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4173
spectrum_assert exact_4173 complete

theorem exact_4174 : Law4174.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4174
spectrum_assert exact_4174 complete

theorem exact_4175 : Law4175.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4175
spectrum_assert exact_4175 complete

theorem exact_4176 : Law4176.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4176
spectrum_assert exact_4176 complete

theorem exact_4177 : Law4177.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4177
spectrum_assert exact_4177 complete

theorem exact_4178 : Law4178.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4178
spectrum_assert exact_4178 complete

theorem exact_4179 : Law4179.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4179
spectrum_assert exact_4179 complete

theorem exact_4180 : Law4180.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4180
spectrum_assert exact_4180 complete

theorem exact_4181 : Law4181.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4181
spectrum_assert exact_4181 complete

theorem exact_4182 : Law4182.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4182
spectrum_assert exact_4182 complete

theorem exact_4183 : Law4183.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4183
spectrum_assert exact_4183 complete

theorem exact_4184 : Law4184.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4184
spectrum_assert exact_4184 complete

theorem exact_4185 : Law4185.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4185
spectrum_assert exact_4185 complete

theorem exact_4186 : Law4186.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4186
spectrum_assert exact_4186 complete

theorem exact_4187 : Law4187.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4187
spectrum_assert exact_4187 complete

theorem exact_4188 : Law4188.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4188
spectrum_assert exact_4188 complete

theorem exact_4189 : Law4189.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4189
spectrum_assert exact_4189 complete

theorem exact_4190 : Law4190.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4190
spectrum_assert exact_4190 complete

theorem exact_4191 : Law4191.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4191
spectrum_assert exact_4191 complete

theorem exact_4192 : Law4192.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4192
spectrum_assert exact_4192 complete

theorem exact_4193 : Law4193.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4193
spectrum_assert exact_4193 complete

theorem exact_4194 : Law4194.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4194
spectrum_assert exact_4194 complete

theorem exact_4195 : Law4195.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4195
spectrum_assert exact_4195 complete

theorem exact_4196 : Law4196.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4196
spectrum_assert exact_4196 complete

theorem exact_4197 : Law4197.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4197
spectrum_assert exact_4197 complete

theorem exact_4198 : Law4198.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4198
spectrum_assert exact_4198 complete

theorem exact_4199 : Law4199.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4199
spectrum_assert exact_4199 complete

theorem exact_4200 : Law4200.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4200
spectrum_assert exact_4200 complete

theorem exact_4201 : Law4201.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4201
spectrum_assert exact_4201 complete

theorem exact_4202 : Law4202.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4202
spectrum_assert exact_4202 complete

theorem exact_4203 : Law4203.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4203
spectrum_assert exact_4203 complete

theorem exact_4204 : Law4204.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4204
spectrum_assert exact_4204 complete

theorem exact_4205 : Law4205.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4205
spectrum_assert exact_4205 complete

theorem exact_4206 : Law4206.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4206
spectrum_assert exact_4206 complete

theorem exact_4207 : Law4207.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4207
spectrum_assert exact_4207 complete

theorem exact_4208 : Law4208.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4208
spectrum_assert exact_4208 complete

theorem exact_4209 : Law4209.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4209
spectrum_assert exact_4209 complete

theorem exact_4210 : Law4210.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4210
spectrum_assert exact_4210 complete

theorem exact_4211 : Law4211.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4211
spectrum_assert exact_4211 complete

theorem exact_4212 : Law4212.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4212
spectrum_assert exact_4212 complete

theorem exact_4213 : Law4213.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4213
spectrum_assert exact_4213 complete

theorem exact_4214 : Law4214.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4214
spectrum_assert exact_4214 complete

theorem exact_4215 : Law4215.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4215
spectrum_assert exact_4215 complete

theorem exact_4216 : Law4216.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4216
spectrum_assert exact_4216 complete

theorem exact_4217 : Law4217.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4217
spectrum_assert exact_4217 complete

theorem exact_4218 : Law4218.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4218
spectrum_assert exact_4218 complete

theorem exact_4219 : Law4219.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4219
spectrum_assert exact_4219 complete

theorem exact_4220 : Law4220.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4220
spectrum_assert exact_4220 complete

theorem exact_4221 : Law4221.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4221
spectrum_assert exact_4221 complete

theorem exact_4222 : Law4222.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4222
spectrum_assert exact_4222 complete

theorem exact_4223 : Law4223.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4223
spectrum_assert exact_4223 complete

theorem exact_4224 : Law4224.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4224
spectrum_assert exact_4224 complete

theorem exact_4225 : Law4225.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4225
spectrum_assert exact_4225 complete

theorem exact_4226 : Law4226.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4226
spectrum_assert exact_4226 complete

theorem exact_4227 : Law4227.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4227
spectrum_assert exact_4227 complete

theorem exact_4228 : Law4228.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4228
spectrum_assert exact_4228 complete

theorem exact_4229 : Law4229.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4229
spectrum_assert exact_4229 complete

theorem exact_4230 : Law4230.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4230
spectrum_assert exact_4230 complete

theorem exact_4231 : Law4231.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4231
spectrum_assert exact_4231 complete

theorem exact_4232 : Law4232.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4232
spectrum_assert exact_4232 complete

theorem exact_4233 : Law4233.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4233
spectrum_assert exact_4233 complete

theorem exact_4234 : Law4234.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4234
spectrum_assert exact_4234 complete

theorem exact_4235 : Law4235.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4235
spectrum_assert exact_4235 complete

theorem exact_4236 : Law4236.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4236
spectrum_assert exact_4236 complete

theorem exact_4237 : Law4237.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4237
spectrum_assert exact_4237 complete

theorem exact_4238 : Law4238.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4238
spectrum_assert exact_4238 complete

theorem exact_4239 : Law4239.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4239
spectrum_assert exact_4239 complete

theorem exact_4240 : Law4240.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4240
spectrum_assert exact_4240 complete

theorem exact_4241 : Law4241.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4241
spectrum_assert exact_4241 complete

theorem exact_4242 : Law4242.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4242
spectrum_assert exact_4242 complete

theorem exact_4243 : Law4243.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4243
spectrum_assert exact_4243 complete

theorem exact_4244 : Law4244.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4244
spectrum_assert exact_4244 complete

theorem exact_4245 : Law4245.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4245
spectrum_assert exact_4245 complete

theorem exact_4246 : Law4246.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4246
spectrum_assert exact_4246 complete

theorem exact_4247 : Law4247.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4247
spectrum_assert exact_4247 complete

theorem exact_4248 : Law4248.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4248
spectrum_assert exact_4248 complete

theorem exact_4249 : Law4249.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4249
spectrum_assert exact_4249 complete

theorem exact_4250 : Law4250.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4250
spectrum_assert exact_4250 complete

theorem exact_4251 : Law4251.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4251
spectrum_assert exact_4251 complete

theorem exact_4252 : Law4252.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4252
spectrum_assert exact_4252 complete

theorem exact_4253 : Law4253.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4253
spectrum_assert exact_4253 complete

theorem exact_4254 : Law4254.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4254
spectrum_assert exact_4254 complete

theorem exact_4255 : Law4255.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4255
spectrum_assert exact_4255 complete

theorem exact_4256 : Law4256.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4256
spectrum_assert exact_4256 complete

theorem exact_4257 : Law4257.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4257
spectrum_assert exact_4257 complete

theorem exact_4258 : Law4258.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4258
spectrum_assert exact_4258 complete

theorem exact_4259 : Law4259.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4259
spectrum_assert exact_4259 complete

theorem exact_4260 : Law4260.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4260
spectrum_assert exact_4260 complete

theorem exact_4261 : Law4261.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4261
spectrum_assert exact_4261 complete

theorem exact_4262 : Law4262.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4262
spectrum_assert exact_4262 complete

theorem exact_4263 : Law4263.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4263
spectrum_assert exact_4263 complete

theorem exact_4264 : Law4264.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4264
spectrum_assert exact_4264 complete

theorem exact_4265 : Law4265.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4265
spectrum_assert exact_4265 complete

theorem exact_4266 : Law4266.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4266
spectrum_assert exact_4266 complete

theorem exact_4267 : Law4267.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4267
spectrum_assert exact_4267 complete

theorem exact_4268 : Law4268.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4268
spectrum_assert exact_4268 complete

theorem exact_4269 : Law4269.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4269
spectrum_assert exact_4269 complete

theorem exact_4270 : Law4270.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4270
spectrum_assert exact_4270 complete

theorem exact_4271 : Law4271.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4271
spectrum_assert exact_4271 complete

theorem exact_4272 : Law4272.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4272
spectrum_assert exact_4272 complete

theorem exact_4273 : Law4273.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4273
spectrum_assert exact_4273 complete

theorem exact_4274 : Law4274.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4274
spectrum_assert exact_4274 complete

theorem exact_4275 : Law4275.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4275
spectrum_assert exact_4275 complete

theorem exact_4276 : Law4276.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4276
spectrum_assert exact_4276 complete

theorem exact_4277 : Law4277.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4277
spectrum_assert exact_4277 complete

theorem exact_4278 : Law4278.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4278
spectrum_assert exact_4278 complete

theorem exact_4279 : Law4279.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4279
spectrum_assert exact_4279 complete

theorem exact_4280 : Law4280.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4280
spectrum_assert exact_4280 complete

theorem exact_4281 : Law4281.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4281
spectrum_assert exact_4281 complete

theorem exact_4282 : Law4282.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4282
spectrum_assert exact_4282 complete

theorem exact_4283 : Law4283.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4283
spectrum_assert exact_4283 complete

theorem exact_4284 : Law4284.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4284
spectrum_assert exact_4284 complete

theorem exact_4285 : Law4285.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4285
spectrum_assert exact_4285 complete

theorem exact_4286 : Law4286.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4286
spectrum_assert exact_4286 complete

theorem exact_4287 : Law4287.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4287
spectrum_assert exact_4287 complete

theorem exact_4288 : Law4288.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4288
spectrum_assert exact_4288 complete

theorem exact_4289 : Law4289.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4289
spectrum_assert exact_4289 complete

theorem exact_4290 : Law4290.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4290
spectrum_assert exact_4290 complete

theorem exact_4291 : Law4291.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4291
spectrum_assert exact_4291 complete

theorem exact_4292 : Law4292.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4292
spectrum_assert exact_4292 complete

theorem exact_4293 : Law4293.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4293
spectrum_assert exact_4293 complete

theorem exact_4294 : Law4294.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4294
spectrum_assert exact_4294 complete

theorem exact_4295 : Law4295.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4295
spectrum_assert exact_4295 complete

theorem exact_4296 : Law4296.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4296
spectrum_assert exact_4296 complete

theorem exact_4297 : Law4297.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4297
spectrum_assert exact_4297 complete

theorem exact_4298 : Law4298.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4298
spectrum_assert exact_4298 complete

theorem exact_4299 : Law4299.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4299
spectrum_assert exact_4299 complete

theorem exact_4300 : Law4300.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4300
spectrum_assert exact_4300 complete

theorem exact_4301 : Law4301.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4301
spectrum_assert exact_4301 complete

theorem exact_4302 : Law4302.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4302
spectrum_assert exact_4302 complete

theorem exact_4303 : Law4303.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4303
spectrum_assert exact_4303 complete

theorem exact_4304 : Law4304.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4304
spectrum_assert exact_4304 complete

theorem exact_4305 : Law4305.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4305
spectrum_assert exact_4305 complete

theorem exact_4306 : Law4306.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4306
spectrum_assert exact_4306 complete

theorem exact_4307 : Law4307.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4307
spectrum_assert exact_4307 complete

theorem exact_4308 : Law4308.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4308
spectrum_assert exact_4308 complete

theorem exact_4309 : Law4309.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4309
spectrum_assert exact_4309 complete

theorem exact_4310 : Law4310.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4310
spectrum_assert exact_4310 complete

theorem exact_4311 : Law4311.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4311
spectrum_assert exact_4311 complete

theorem exact_4312 : Law4312.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4312
spectrum_assert exact_4312 complete

theorem exact_4313 : Law4313.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4313
spectrum_assert exact_4313 complete

theorem exact_4314 : Law4314.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4314
spectrum_assert exact_4314 complete

theorem exact_4315 : Law4315.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4315
spectrum_assert exact_4315 complete

theorem exact_4316 : Law4316.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4316
spectrum_assert exact_4316 complete

theorem exact_4317 : Law4317.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4317
spectrum_assert exact_4317 complete

theorem exact_4318 : Law4318.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4318
spectrum_assert exact_4318 complete

theorem exact_4319 : Law4319.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4319
spectrum_assert exact_4319 complete

theorem exact_4320 : Law4320.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4320
spectrum_assert exact_4320 complete

theorem exact_4321 : Law4321.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4321
spectrum_assert exact_4321 complete

theorem exact_4322 : Law4322.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4322
spectrum_assert exact_4322 complete

theorem exact_4323 : Law4323.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4323
spectrum_assert exact_4323 complete

theorem exact_4324 : Law4324.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4324
spectrum_assert exact_4324 complete

theorem exact_4325 : Law4325.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4325
spectrum_assert exact_4325 complete

theorem exact_4326 : Law4326.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4326
spectrum_assert exact_4326 complete

theorem exact_4327 : Law4327.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4327
spectrum_assert exact_4327 complete

theorem exact_4328 : Law4328.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4328
spectrum_assert exact_4328 complete

theorem exact_4329 : Law4329.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4329
spectrum_assert exact_4329 complete

theorem exact_4330 : Law4330.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4330
spectrum_assert exact_4330 complete

theorem exact_4331 : Law4331.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4331
spectrum_assert exact_4331 complete

theorem exact_4332 : Law4332.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4332
spectrum_assert exact_4332 complete

theorem exact_4333 : Law4333.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4333
spectrum_assert exact_4333 complete

theorem exact_4334 : Law4334.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4334
spectrum_assert exact_4334 complete

theorem exact_4335 : Law4335.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4335
spectrum_assert exact_4335 complete

theorem exact_4336 : Law4336.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4336
spectrum_assert exact_4336 complete

theorem exact_4337 : Law4337.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4337
spectrum_assert exact_4337 complete

theorem exact_4338 : Law4338.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4338
spectrum_assert exact_4338 complete

theorem exact_4339 : Law4339.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4339
spectrum_assert exact_4339 complete

theorem exact_4340 : Law4340.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4340
spectrum_assert exact_4340 complete

theorem exact_4341 : Law4341.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4341
spectrum_assert exact_4341 complete

theorem exact_4342 : Law4342.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4342
spectrum_assert exact_4342 complete

theorem exact_4343 : Law4343.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4343
spectrum_assert exact_4343 complete

theorem exact_4344 : Law4344.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4344
spectrum_assert exact_4344 complete

theorem exact_4345 : Law4345.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4345
spectrum_assert exact_4345 complete

theorem exact_4346 : Law4346.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4346
spectrum_assert exact_4346 complete

theorem exact_4347 : Law4347.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4347
spectrum_assert exact_4347 complete

theorem exact_4348 : Law4348.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4348
spectrum_assert exact_4348 complete

theorem exact_4349 : Law4349.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4349
spectrum_assert exact_4349 complete

theorem exact_4350 : Law4350.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4350
spectrum_assert exact_4350 complete

theorem exact_4351 : Law4351.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4351
spectrum_assert exact_4351 complete

theorem exact_4352 : Law4352.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4352
spectrum_assert exact_4352 complete

theorem exact_4353 : Law4353.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4353
spectrum_assert exact_4353 complete

theorem exact_4354 : Law4354.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4354
spectrum_assert exact_4354 complete

theorem exact_4355 : Law4355.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4355
spectrum_assert exact_4355 complete

theorem exact_4356 : Law4356.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4356
spectrum_assert exact_4356 complete

theorem exact_4357 : Law4357.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4357
spectrum_assert exact_4357 complete

theorem exact_4358 : Law4358.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4358
spectrum_assert exact_4358 complete

theorem exact_4359 : Law4359.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4359
spectrum_assert exact_4359 complete

theorem exact_4360 : Law4360.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4360
spectrum_assert exact_4360 complete

theorem exact_4361 : Law4361.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4361
spectrum_assert exact_4361 complete

theorem exact_4362 : Law4362.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4362
spectrum_assert exact_4362 complete

theorem exact_4363 : Law4363.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4363
spectrum_assert exact_4363 complete

theorem exact_4364 : Law4364.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4364
spectrum_assert exact_4364 complete

theorem exact_4365 : Law4365.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4365
spectrum_assert exact_4365 complete

theorem exact_4366 : Law4366.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4366
spectrum_assert exact_4366 complete

theorem exact_4367 : Law4367.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4367
spectrum_assert exact_4367 complete

theorem exact_4368 : Law4368.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4368
spectrum_assert exact_4368 complete

theorem exact_4369 : Law4369.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4369
spectrum_assert exact_4369 complete

theorem exact_4370 : Law4370.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4370
spectrum_assert exact_4370 complete

theorem exact_4371 : Law4371.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4371
spectrum_assert exact_4371 complete

theorem exact_4372 : Law4372.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4372
spectrum_assert exact_4372 complete

theorem exact_4373 : Law4373.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4373
spectrum_assert exact_4373 complete

theorem exact_4374 : Law4374.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4374
spectrum_assert exact_4374 complete

theorem exact_4375 : Law4375.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4375
spectrum_assert exact_4375 complete

theorem exact_4376 : Law4376.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4376
spectrum_assert exact_4376 complete

theorem exact_4377 : Law4377.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4377
spectrum_assert exact_4377 complete

theorem exact_4378 : Law4378.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4378
spectrum_assert exact_4378 complete

theorem exact_4379 : Law4379.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4379
spectrum_assert exact_4379 complete

theorem exact_4380 : Law4380.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4380
spectrum_assert exact_4380 complete

theorem exact_4381 : Law4381.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4381
spectrum_assert exact_4381 complete

theorem exact_4382 : Law4382.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4382
spectrum_assert exact_4382 complete

theorem exact_4383 : Law4383.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4383
spectrum_assert exact_4383 complete

theorem exact_4384 : Law4384.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4384
spectrum_assert exact_4384 complete

theorem exact_4385 : Law4385.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4385
spectrum_assert exact_4385 complete

theorem exact_4386 : Law4386.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4386
spectrum_assert exact_4386 complete

theorem exact_4387 : Law4387.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4387
spectrum_assert exact_4387 complete

theorem exact_4388 : Law4388.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4388
spectrum_assert exact_4388 complete

theorem exact_4389 : Law4389.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4389
spectrum_assert exact_4389 complete

theorem exact_4390 : Law4390.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4390
spectrum_assert exact_4390 complete

theorem exact_4391 : Law4391.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4391
spectrum_assert exact_4391 complete

theorem exact_4392 : Law4392.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4392
spectrum_assert exact_4392 complete

theorem exact_4393 : Law4393.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4393
spectrum_assert exact_4393 complete

theorem exact_4394 : Law4394.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4394
spectrum_assert exact_4394 complete

theorem exact_4395 : Law4395.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4395
spectrum_assert exact_4395 complete

theorem exact_4396 : Law4396.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4396
spectrum_assert exact_4396 complete

theorem exact_4397 : Law4397.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4397
spectrum_assert exact_4397 complete

theorem exact_4398 : Law4398.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4398
spectrum_assert exact_4398 complete

theorem exact_4399 : Law4399.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4399
spectrum_assert exact_4399 complete

theorem exact_4400 : Law4400.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4400
spectrum_assert exact_4400 complete

theorem exact_4401 : Law4401.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4401
spectrum_assert exact_4401 complete

theorem exact_4402 : Law4402.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4402
spectrum_assert exact_4402 complete

theorem exact_4403 : Law4403.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4403
spectrum_assert exact_4403 complete

theorem exact_4404 : Law4404.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4404
spectrum_assert exact_4404 complete

theorem exact_4405 : Law4405.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4405
spectrum_assert exact_4405 complete

theorem exact_4406 : Law4406.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4406
spectrum_assert exact_4406 complete

theorem exact_4407 : Law4407.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4407
spectrum_assert exact_4407 complete

theorem exact_4408 : Law4408.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4408
spectrum_assert exact_4408 complete

theorem exact_4409 : Law4409.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4409
spectrum_assert exact_4409 complete

theorem exact_4410 : Law4410.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4410
spectrum_assert exact_4410 complete

theorem exact_4411 : Law4411.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4411
spectrum_assert exact_4411 complete

theorem exact_4412 : Law4412.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4412
spectrum_assert exact_4412 complete

theorem exact_4413 : Law4413.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4413
spectrum_assert exact_4413 complete

theorem exact_4414 : Law4414.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4414
spectrum_assert exact_4414 complete

theorem exact_4415 : Law4415.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4415
spectrum_assert exact_4415 complete

theorem exact_4416 : Law4416.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4416
spectrum_assert exact_4416 complete

theorem exact_4417 : Law4417.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4417
spectrum_assert exact_4417 complete

theorem exact_4418 : Law4418.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4418
spectrum_assert exact_4418 complete

theorem exact_4419 : Law4419.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4419
spectrum_assert exact_4419 complete

theorem exact_4420 : Law4420.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4420
spectrum_assert exact_4420 complete

theorem exact_4421 : Law4421.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4421
spectrum_assert exact_4421 complete

theorem exact_4422 : Law4422.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4422
spectrum_assert exact_4422 complete

theorem exact_4423 : Law4423.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4423
spectrum_assert exact_4423 complete

theorem exact_4424 : Law4424.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4424
spectrum_assert exact_4424 complete

theorem exact_4425 : Law4425.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4425
spectrum_assert exact_4425 complete

theorem exact_4426 : Law4426.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4426
spectrum_assert exact_4426 complete

theorem exact_4427 : Law4427.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4427
spectrum_assert exact_4427 complete

theorem exact_4428 : Law4428.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4428
spectrum_assert exact_4428 complete

theorem exact_4429 : Law4429.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4429
spectrum_assert exact_4429 complete

theorem exact_4430 : Law4430.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4430
spectrum_assert exact_4430 complete

theorem exact_4431 : Law4431.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4431
spectrum_assert exact_4431 complete

theorem exact_4432 : Law4432.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4432
spectrum_assert exact_4432 complete

theorem exact_4433 : Law4433.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4433
spectrum_assert exact_4433 complete

theorem exact_4434 : Law4434.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4434
spectrum_assert exact_4434 complete

theorem exact_4435 : Law4435.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4435
spectrum_assert exact_4435 complete

theorem exact_4436 : Law4436.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4436
spectrum_assert exact_4436 complete

theorem exact_4437 : Law4437.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4437
spectrum_assert exact_4437 complete

theorem exact_4438 : Law4438.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4438
spectrum_assert exact_4438 complete

theorem exact_4439 : Law4439.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4439
spectrum_assert exact_4439 complete

theorem exact_4440 : Law4440.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4440
spectrum_assert exact_4440 complete

theorem exact_4441 : Law4441.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4441
spectrum_assert exact_4441 complete

theorem exact_4442 : Law4442.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4442
spectrum_assert exact_4442 complete

theorem exact_4443 : Law4443.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4443
spectrum_assert exact_4443 complete

theorem exact_4444 : Law4444.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4444
spectrum_assert exact_4444 complete

theorem exact_4445 : Law4445.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4445
spectrum_assert exact_4445 complete

theorem exact_4446 : Law4446.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4446
spectrum_assert exact_4446 complete

theorem exact_4447 : Law4447.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4447
spectrum_assert exact_4447 complete

theorem exact_4448 : Law4448.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4448
spectrum_assert exact_4448 complete

theorem exact_4449 : Law4449.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4449
spectrum_assert exact_4449 complete

theorem exact_4450 : Law4450.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4450
spectrum_assert exact_4450 complete

theorem exact_4451 : Law4451.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4451
spectrum_assert exact_4451 complete

theorem exact_4452 : Law4452.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4452
spectrum_assert exact_4452 complete

theorem exact_4453 : Law4453.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4453
spectrum_assert exact_4453 complete

theorem exact_4454 : Law4454.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4454
spectrum_assert exact_4454 complete

theorem exact_4455 : Law4455.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4455
spectrum_assert exact_4455 complete

theorem exact_4456 : Law4456.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4456
spectrum_assert exact_4456 complete

theorem exact_4457 : Law4457.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4457
spectrum_assert exact_4457 complete

theorem exact_4458 : Law4458.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4458
spectrum_assert exact_4458 complete

theorem exact_4459 : Law4459.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4459
spectrum_assert exact_4459 complete

theorem exact_4460 : Law4460.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4460
spectrum_assert exact_4460 complete

theorem exact_4461 : Law4461.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4461
spectrum_assert exact_4461 complete

theorem exact_4462 : Law4462.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4462
spectrum_assert exact_4462 complete

theorem exact_4463 : Law4463.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4463
spectrum_assert exact_4463 complete

theorem exact_4464 : Law4464.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4464
spectrum_assert exact_4464 complete

theorem exact_4465 : Law4465.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4465
spectrum_assert exact_4465 complete

theorem exact_4466 : Law4466.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4466
spectrum_assert exact_4466 complete

theorem exact_4467 : Law4467.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4467
spectrum_assert exact_4467 complete

theorem exact_4468 : Law4468.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4468
spectrum_assert exact_4468 complete

theorem exact_4469 : Law4469.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4469
spectrum_assert exact_4469 complete

theorem exact_4470 : Law4470.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4470
spectrum_assert exact_4470 complete

theorem exact_4471 : Law4471.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4471
spectrum_assert exact_4471 complete

theorem exact_4472 : Law4472.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4472
spectrum_assert exact_4472 complete

theorem exact_4473 : Law4473.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4473
spectrum_assert exact_4473 complete

theorem exact_4474 : Law4474.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4474
spectrum_assert exact_4474 complete

theorem exact_4475 : Law4475.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4475
spectrum_assert exact_4475 complete

theorem exact_4476 : Law4476.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4476
spectrum_assert exact_4476 complete

theorem exact_4477 : Law4477.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4477
spectrum_assert exact_4477 complete

theorem exact_4478 : Law4478.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4478
spectrum_assert exact_4478 complete

theorem exact_4479 : Law4479.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4479
spectrum_assert exact_4479 complete

theorem exact_4480 : Law4480.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4480
spectrum_assert exact_4480 complete

theorem exact_4481 : Law4481.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4481
spectrum_assert exact_4481 complete

theorem exact_4482 : Law4482.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4482
spectrum_assert exact_4482 complete

theorem exact_4483 : Law4483.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4483
spectrum_assert exact_4483 complete

theorem exact_4484 : Law4484.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4484
spectrum_assert exact_4484 complete

theorem exact_4485 : Law4485.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4485
spectrum_assert exact_4485 complete

theorem exact_4486 : Law4486.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4486
spectrum_assert exact_4486 complete

theorem exact_4487 : Law4487.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4487
spectrum_assert exact_4487 complete

theorem exact_4488 : Law4488.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4488
spectrum_assert exact_4488 complete

theorem exact_4489 : Law4489.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4489
spectrum_assert exact_4489 complete

theorem exact_4490 : Law4490.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4490
spectrum_assert exact_4490 complete

theorem exact_4491 : Law4491.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4491
spectrum_assert exact_4491 complete

theorem exact_4492 : Law4492.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4492
spectrum_assert exact_4492 complete

theorem exact_4493 : Law4493.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4493
spectrum_assert exact_4493 complete

theorem exact_4494 : Law4494.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4494
spectrum_assert exact_4494 complete

theorem exact_4495 : Law4495.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4495
spectrum_assert exact_4495 complete

theorem exact_4496 : Law4496.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4496
spectrum_assert exact_4496 complete

theorem exact_4497 : Law4497.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4497
spectrum_assert exact_4497 complete

theorem exact_4498 : Law4498.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4498
spectrum_assert exact_4498 complete

theorem exact_4499 : Law4499.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4499
spectrum_assert exact_4499 complete

theorem exact_4500 : Law4500.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4500
spectrum_assert exact_4500 complete

theorem exact_4501 : Law4501.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4501
spectrum_assert exact_4501 complete

theorem exact_4502 : Law4502.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4502
spectrum_assert exact_4502 complete

theorem exact_4503 : Law4503.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4503
spectrum_assert exact_4503 complete

theorem exact_4504 : Law4504.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4504
spectrum_assert exact_4504 complete

theorem exact_4505 : Law4505.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4505
spectrum_assert exact_4505 complete

theorem exact_4506 : Law4506.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4506
spectrum_assert exact_4506 complete

theorem exact_4507 : Law4507.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4507
spectrum_assert exact_4507 complete

theorem exact_4508 : Law4508.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4508
spectrum_assert exact_4508 complete

theorem exact_4509 : Law4509.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4509
spectrum_assert exact_4509 complete

theorem exact_4510 : Law4510.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4510
spectrum_assert exact_4510 complete

theorem exact_4511 : Law4511.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4511
spectrum_assert exact_4511 complete

theorem exact_4512 : Law4512.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4512
spectrum_assert exact_4512 complete

theorem exact_4513 : Law4513.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4513
spectrum_assert exact_4513 complete

theorem exact_4514 : Law4514.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4514
spectrum_assert exact_4514 complete

theorem exact_4515 : Law4515.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4515
spectrum_assert exact_4515 complete

theorem exact_4516 : Law4516.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4516
spectrum_assert exact_4516 complete

theorem exact_4517 : Law4517.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4517
spectrum_assert exact_4517 complete

theorem exact_4518 : Law4518.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4518
spectrum_assert exact_4518 complete

theorem exact_4519 : Law4519.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4519
spectrum_assert exact_4519 complete

theorem exact_4520 : Law4520.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4520
spectrum_assert exact_4520 complete

theorem exact_4521 : Law4521.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4521
spectrum_assert exact_4521 complete

theorem exact_4522 : Law4522.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4522
spectrum_assert exact_4522 complete

theorem exact_4523 : Law4523.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4523
spectrum_assert exact_4523 complete

theorem exact_4524 : Law4524.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4524
spectrum_assert exact_4524 complete

theorem exact_4525 : Law4525.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4525
spectrum_assert exact_4525 complete

theorem exact_4526 : Law4526.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4526
spectrum_assert exact_4526 complete

theorem exact_4527 : Law4527.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4527
spectrum_assert exact_4527 complete

theorem exact_4528 : Law4528.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4528
spectrum_assert exact_4528 complete

theorem exact_4529 : Law4529.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4529
spectrum_assert exact_4529 complete

theorem exact_4530 : Law4530.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4530
spectrum_assert exact_4530 complete

theorem exact_4531 : Law4531.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4531
spectrum_assert exact_4531 complete

theorem exact_4532 : Law4532.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4532
spectrum_assert exact_4532 complete

theorem exact_4533 : Law4533.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4533
spectrum_assert exact_4533 complete

theorem exact_4534 : Law4534.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4534
spectrum_assert exact_4534 complete

theorem exact_4535 : Law4535.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4535
spectrum_assert exact_4535 complete

theorem exact_4536 : Law4536.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4536
spectrum_assert exact_4536 complete

theorem exact_4537 : Law4537.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4537
spectrum_assert exact_4537 complete

theorem exact_4538 : Law4538.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4538
spectrum_assert exact_4538 complete

theorem exact_4539 : Law4539.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4539
spectrum_assert exact_4539 complete

theorem exact_4540 : Law4540.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4540
spectrum_assert exact_4540 complete

theorem exact_4541 : Law4541.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4541
spectrum_assert exact_4541 complete

theorem exact_4542 : Law4542.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4542
spectrum_assert exact_4542 complete

theorem exact_4543 : Law4543.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4543
spectrum_assert exact_4543 complete

theorem exact_4544 : Law4544.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4544
spectrum_assert exact_4544 complete

theorem exact_4545 : Law4545.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4545
spectrum_assert exact_4545 complete

theorem exact_4546 : Law4546.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4546
spectrum_assert exact_4546 complete

theorem exact_4547 : Law4547.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4547
spectrum_assert exact_4547 complete

theorem exact_4548 : Law4548.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4548
spectrum_assert exact_4548 complete

theorem exact_4549 : Law4549.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4549
spectrum_assert exact_4549 complete

theorem exact_4550 : Law4550.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4550
spectrum_assert exact_4550 complete

theorem exact_4551 : Law4551.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4551
spectrum_assert exact_4551 complete

theorem exact_4552 : Law4552.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4552
spectrum_assert exact_4552 complete

theorem exact_4553 : Law4553.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4553
spectrum_assert exact_4553 complete

theorem exact_4554 : Law4554.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4554
spectrum_assert exact_4554 complete

theorem exact_4555 : Law4555.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4555
spectrum_assert exact_4555 complete

theorem exact_4556 : Law4556.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4556
spectrum_assert exact_4556 complete

theorem exact_4557 : Law4557.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4557
spectrum_assert exact_4557 complete

theorem exact_4558 : Law4558.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4558
spectrum_assert exact_4558 complete

theorem exact_4559 : Law4559.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4559
spectrum_assert exact_4559 complete

theorem exact_4560 : Law4560.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4560
spectrum_assert exact_4560 complete

theorem exact_4561 : Law4561.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4561
spectrum_assert exact_4561 complete

theorem exact_4562 : Law4562.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4562
spectrum_assert exact_4562 complete

theorem exact_4563 : Law4563.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4563
spectrum_assert exact_4563 complete

theorem exact_4564 : Law4564.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4564
spectrum_assert exact_4564 complete

theorem exact_4565 : Law4565.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4565
spectrum_assert exact_4565 complete

theorem exact_4566 : Law4566.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4566
spectrum_assert exact_4566 complete

theorem exact_4567 : Law4567.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4567
spectrum_assert exact_4567 complete

theorem exact_4568 : Law4568.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4568
spectrum_assert exact_4568 complete

theorem exact_4569 : Law4569.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4569
spectrum_assert exact_4569 complete

theorem exact_4570 : Law4570.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4570
spectrum_assert exact_4570 complete

theorem exact_4571 : Law4571.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4571
spectrum_assert exact_4571 complete

theorem exact_4572 : Law4572.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4572
spectrum_assert exact_4572 complete

theorem exact_4573 : Law4573.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4573
spectrum_assert exact_4573 complete

theorem exact_4574 : Law4574.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4574
spectrum_assert exact_4574 complete

theorem exact_4575 : Law4575.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4575
spectrum_assert exact_4575 complete

theorem exact_4576 : Law4576.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4576
spectrum_assert exact_4576 complete

theorem exact_4577 : Law4577.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4577
spectrum_assert exact_4577 complete

theorem exact_4578 : Law4578.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4578
spectrum_assert exact_4578 complete

theorem exact_4579 : Law4579.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4579
spectrum_assert exact_4579 complete

theorem exact_4580 : Law4580.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4580
spectrum_assert exact_4580 complete

theorem exact_4581 : Law4581.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4581
spectrum_assert exact_4581 complete

theorem exact_4582 : Law4582.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4582
spectrum_assert exact_4582 complete

theorem exact_4583 : Law4583.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4583
spectrum_assert exact_4583 complete

theorem exact_4584 : Law4584.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4584
spectrum_assert exact_4584 complete

theorem exact_4585 : Law4585.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4585
spectrum_assert exact_4585 complete

theorem exact_4586 : Law4586.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4586
spectrum_assert exact_4586 complete

theorem exact_4587 : Law4587.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4587
spectrum_assert exact_4587 complete

theorem exact_4588 : Law4588.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4588
spectrum_assert exact_4588 complete

theorem exact_4589 : Law4589.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4589
spectrum_assert exact_4589 complete

theorem exact_4590 : Law4590.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4590
spectrum_assert exact_4590 complete

theorem exact_4591 : Law4591.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4591
spectrum_assert exact_4591 complete

theorem exact_4592 : Law4592.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4592
spectrum_assert exact_4592 complete

theorem exact_4593 : Law4593.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4593
spectrum_assert exact_4593 complete

theorem exact_4594 : Law4594.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4594
spectrum_assert exact_4594 complete

theorem exact_4595 : Law4595.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4595
spectrum_assert exact_4595 complete

theorem exact_4596 : Law4596.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4596
spectrum_assert exact_4596 complete

theorem exact_4597 : Law4597.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4597
spectrum_assert exact_4597 complete

theorem exact_4598 : Law4598.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4598
spectrum_assert exact_4598 complete

theorem exact_4599 : Law4599.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4599
spectrum_assert exact_4599 complete

theorem exact_4600 : Law4600.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4600
spectrum_assert exact_4600 complete

theorem exact_4601 : Law4601.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4601
spectrum_assert exact_4601 complete

theorem exact_4602 : Law4602.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4602
spectrum_assert exact_4602 complete

theorem exact_4603 : Law4603.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4603
spectrum_assert exact_4603 complete

theorem exact_4604 : Law4604.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4604
spectrum_assert exact_4604 complete

theorem exact_4605 : Law4605.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4605
spectrum_assert exact_4605 complete

theorem exact_4606 : Law4606.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4606
spectrum_assert exact_4606 complete

theorem exact_4607 : Law4607.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4607
spectrum_assert exact_4607 complete

theorem exact_4608 : Law4608.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4608
spectrum_assert exact_4608 complete

theorem exact_4609 : Law4609.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4609
spectrum_assert exact_4609 complete

theorem exact_4610 : Law4610.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4610
spectrum_assert exact_4610 complete

theorem exact_4611 : Law4611.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4611
spectrum_assert exact_4611 complete

theorem exact_4612 : Law4612.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4612
spectrum_assert exact_4612 complete

theorem exact_4613 : Law4613.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4613
spectrum_assert exact_4613 complete

theorem exact_4614 : Law4614.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4614
spectrum_assert exact_4614 complete

theorem exact_4615 : Law4615.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4615
spectrum_assert exact_4615 complete

theorem exact_4616 : Law4616.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4616
spectrum_assert exact_4616 complete

theorem exact_4617 : Law4617.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4617
spectrum_assert exact_4617 complete

theorem exact_4618 : Law4618.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4618
spectrum_assert exact_4618 complete

theorem exact_4619 : Law4619.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4619
spectrum_assert exact_4619 complete

theorem exact_4620 : Law4620.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4620
spectrum_assert exact_4620 complete

theorem exact_4621 : Law4621.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4621
spectrum_assert exact_4621 complete

theorem exact_4622 : Law4622.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4622
spectrum_assert exact_4622 complete

theorem exact_4623 : Law4623.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4623
spectrum_assert exact_4623 complete

theorem exact_4624 : Law4624.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4624
spectrum_assert exact_4624 complete

theorem exact_4625 : Law4625.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4625
spectrum_assert exact_4625 complete

theorem exact_4626 : Law4626.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4626
spectrum_assert exact_4626 complete

theorem exact_4627 : Law4627.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4627
spectrum_assert exact_4627 complete

theorem exact_4628 : Law4628.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4628
spectrum_assert exact_4628 complete

theorem exact_4629 : Law4629.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4629
spectrum_assert exact_4629 complete

theorem exact_4630 : Law4630.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4630
spectrum_assert exact_4630 complete

theorem exact_4631 : Law4631.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4631
spectrum_assert exact_4631 complete

theorem exact_4632 : Law4632.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4632
spectrum_assert exact_4632 complete

theorem exact_4633 : Law4633.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4633
spectrum_assert exact_4633 complete

theorem exact_4634 : Law4634.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4634
spectrum_assert exact_4634 complete

theorem exact_4635 : Law4635.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4635
spectrum_assert exact_4635 complete

theorem exact_4636 : Law4636.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4636
spectrum_assert exact_4636 complete

theorem exact_4637 : Law4637.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4637
spectrum_assert exact_4637 complete

theorem exact_4638 : Law4638.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4638
spectrum_assert exact_4638 complete

theorem exact_4639 : Law4639.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4639
spectrum_assert exact_4639 complete

theorem exact_4640 : Law4640.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4640
spectrum_assert exact_4640 complete

theorem exact_4641 : Law4641.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4641
spectrum_assert exact_4641 complete

theorem exact_4642 : Law4642.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4642
spectrum_assert exact_4642 complete

theorem exact_4643 : Law4643.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4643
spectrum_assert exact_4643 complete

theorem exact_4644 : Law4644.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4644
spectrum_assert exact_4644 complete

theorem exact_4645 : Law4645.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4645
spectrum_assert exact_4645 complete

theorem exact_4646 : Law4646.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4646
spectrum_assert exact_4646 complete

theorem exact_4647 : Law4647.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4647
spectrum_assert exact_4647 complete

theorem exact_4648 : Law4648.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4648
spectrum_assert exact_4648 complete

theorem exact_4649 : Law4649.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4649
spectrum_assert exact_4649 complete

theorem exact_4650 : Law4650.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4650
spectrum_assert exact_4650 complete

theorem exact_4651 : Law4651.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4651
spectrum_assert exact_4651 complete

theorem exact_4652 : Law4652.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4652
spectrum_assert exact_4652 complete

theorem exact_4653 : Law4653.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4653
spectrum_assert exact_4653 complete

theorem exact_4654 : Law4654.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4654
spectrum_assert exact_4654 complete

theorem exact_4655 : Law4655.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4655
spectrum_assert exact_4655 complete

theorem exact_4656 : Law4656.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4656
spectrum_assert exact_4656 complete

theorem exact_4657 : Law4657.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4657
spectrum_assert exact_4657 complete

theorem exact_4658 : Law4658.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4658
spectrum_assert exact_4658 complete

theorem exact_4659 : Law4659.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4659
spectrum_assert exact_4659 complete

theorem exact_4660 : Law4660.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4660
spectrum_assert exact_4660 complete

theorem exact_4661 : Law4661.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4661
spectrum_assert exact_4661 complete

theorem exact_4662 : Law4662.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4662
spectrum_assert exact_4662 complete

theorem exact_4663 : Law4663.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4663
spectrum_assert exact_4663 complete

theorem exact_4664 : Law4664.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4664
spectrum_assert exact_4664 complete

theorem exact_4665 : Law4665.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4665
spectrum_assert exact_4665 complete

theorem exact_4666 : Law4666.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4666
spectrum_assert exact_4666 complete

theorem exact_4667 : Law4667.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4667
spectrum_assert exact_4667 complete

theorem exact_4668 : Law4668.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4668
spectrum_assert exact_4668 complete

theorem exact_4669 : Law4669.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4669
spectrum_assert exact_4669 complete

theorem exact_4670 : Law4670.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4670
spectrum_assert exact_4670 complete

theorem exact_4671 : Law4671.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4671
spectrum_assert exact_4671 complete

theorem exact_4672 : Law4672.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4672
spectrum_assert exact_4672 complete

theorem exact_4673 : Law4673.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4673
spectrum_assert exact_4673 complete

theorem exact_4674 : Law4674.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4674
spectrum_assert exact_4674 complete

theorem exact_4675 : Law4675.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4675
spectrum_assert exact_4675 complete

theorem exact_4676 : Law4676.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4676
spectrum_assert exact_4676 complete

theorem exact_4677 : Law4677.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4677
spectrum_assert exact_4677 complete

theorem exact_4678 : Law4678.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4678
spectrum_assert exact_4678 complete

theorem exact_4679 : Law4679.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4679
spectrum_assert exact_4679 complete

theorem exact_4680 : Law4680.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4680
spectrum_assert exact_4680 complete

theorem exact_4681 : Law4681.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4681
spectrum_assert exact_4681 complete

theorem exact_4682 : Law4682.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4682
spectrum_assert exact_4682 complete

theorem exact_4683 : Law4683.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4683
spectrum_assert exact_4683 complete

theorem exact_4684 : Law4684.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4684
spectrum_assert exact_4684 complete

theorem exact_4685 : Law4685.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4685
spectrum_assert exact_4685 complete

theorem exact_4686 : Law4686.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4686
spectrum_assert exact_4686 complete

theorem exact_4687 : Law4687.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4687
spectrum_assert exact_4687 complete

theorem exact_4688 : Law4688.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4688
spectrum_assert exact_4688 complete

theorem exact_4689 : Law4689.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4689
spectrum_assert exact_4689 complete

theorem exact_4690 : Law4690.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4690
spectrum_assert exact_4690 complete

theorem exact_4691 : Law4691.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4691
spectrum_assert exact_4691 complete

theorem exact_4692 : Law4692.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4692
spectrum_assert exact_4692 complete

theorem exact_4693 : Law4693.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4693
spectrum_assert exact_4693 complete

theorem exact_4694 : Law4694.spectrum = ({n : ℕ | 0 < n}) :=
  (hasFullSpectrum_iff_spectrum).mp full_4694
spectrum_assert exact_4694 complete

/-- Exact spectra still open after recorded supplements; independent of bound proofs. -/
def openProblems : List Status.OpenIssue := [
  ⟨63, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E63."⟩,
  ⟨73, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E73."⟩,
  ⟨115, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E115."⟩,
  ⟨118, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E118."⟩,
  ⟨125, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E125."⟩,
  ⟨219, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E115."⟩,
  ⟨222, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E125."⟩,
  ⟨229, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E118."⟩,
  ⟨271, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E63."⟩,
  ⟨274, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E73."⟩,
  ⟨467, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E467."⟩,
  ⟨481, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E481."⟩,
  ⟨501, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E501."⟩,
  ⟨667, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E667."⟩,
  ⟨670, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E670."⟩,
  ⟨677, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E677."⟩,
  ⟨704, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E704."⟩,
  ⟨873, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E873."⟩,
  ⟨880, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E880."⟩,
  ⟨883, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E883."⟩,
  ⟨907, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E907."⟩,
  ⟨1076, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1076."⟩,
  ⟨1083, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1083."⟩,
  ⟨1110, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1110."⟩,
  ⟨1279, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1279."⟩,
  ⟨1286, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1286."⟩,
  ⟨1313, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1313."⟩,
  ⟨1323, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1323."⟩,
  ⟨1480, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1480."⟩,
  ⟨1483, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1483."⟩,
  ⟨1486, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1486."⟩,
  ⟨1489, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1489."⟩,
  ⟨1496, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1496."⟩,
  ⟨1516, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1516."⟩,
  ⟨1526, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1526."⟩,
  ⟨1692, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1692."⟩,
  ⟨1719, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1719."⟩,
  ⟨1888, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1719."⟩,
  ⟨1895, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1692."⟩,
  ⟨2089, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1480."⟩,
  ⟨2091, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1516."⟩,
  ⟨2098, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1489."⟩,
  ⟨2101, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1526."⟩,
  ⟨2126, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1486."⟩,
  ⟨2146, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1496."⟩,
  ⟨2163, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1483."⟩,
  ⟨2294, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1313."⟩,
  ⟨2301, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1286."⟩,
  ⟨2304, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1323."⟩,
  ⟨2328, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1279."⟩,
  ⟨2497, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1110."⟩,
  ⟨2504, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1083."⟩,
  ⟨2531, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E1076."⟩,
  ⟨2700, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E907."⟩,
  ⟨2707, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E880."⟩,
  ⟨2734, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E873."⟩,
  ⟨2744, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E883."⟩,
  ⟨2900, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E667."⟩,
  ⟨2903, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E704."⟩,
  ⟨2910, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E677."⟩,
  ⟨2937, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E670."⟩,
  ⟨3106, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E501."⟩,
  ⟨3140, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E467."⟩,
  ⟨3161, .mathematicallyOpen, "Exact spectrum still UNKNOWN; note representative E481."⟩]

/-- E1313's cofiniteness is asserted in §3.8 but left open in §3.1. -/
def sourceConflicts : List Status.OpenIssue := [
  ⟨1313, .sourceConflict, "Cofiniteness: §3.1 UNKNOWN versus §3.8 affirmative. No cofinite theorem asserted."⟩]

#guard openProblems.length == 64

end Spectrum.Catalogue
