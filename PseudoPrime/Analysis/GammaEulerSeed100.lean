/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerRowBlocks

/-! # Compact kernel-checked Euler prefix seed through 100 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: ten grid numerators and a resolvent node. Definition: consecutive millionth
endpoints selected by the fixed node order. Output: a rational power interval.
Role: supply compact data whose twentieth-power checks are verified below. -/
def smallSeedRatios (rs : List ℕ) (a : ℚ) : ℚ × ℚ :=
  let r := rs[(gammaResolventCoefficients.map Prod.fst).idxOf a]?.getD 0
  ((r : ℚ) / 1000000, ((r + 1 : ℕ) : ℚ) / 1000000)

/-- Input: prime, exponent minus one, logarithm scale and grid endpoints, and power data.
Definition: the existing finite Euler row with twenty logarithm terms.
Output: row data. Role: separate endpoint discovery from kernel verification. -/
def smallSeedRow (p k j l u : ℕ) (rs : List ℕ) : GammaFiniteEulerRow :=
  { prime := p, exponent := k, logScale := j, logTerms := 20, logLower := (l : ℚ) / 100000,
    logUpper := (u : ℚ) / 100000, ratios := smallSeedRatios rs }

/-- Definition: 35 prime-power rows through 100, with conservative rational intervals.
Output: a small seed payload. All validity and support conditions are proved below.
Role: avoid a large prefix payload at the eventual witness cutoff. -/
def smallSeedRows : List GammaFiniteEulerRow :=
  [smallSeedRow 2 0 1 69313 69316
      [482968, 450625, 406126, 353553, 287174, 217637, 143587, 76946, 31250, 5524],
    smallSeedRow 2 1 1 69313 69316
      [233258, 203063, 164938, 125000, 82469, 47366, 20617, 5920, 976, 30],
    smallSeedRow 2 2 1 69313 69316 [112656, 91505, 66985, 44194, 23683, 10308, 2960, 455, 30, 0],
    smallSeedRow 2 3 1 69313 69316 [54409, 41234, 27204, 15625, 6801, 2243, 425, 35, 0, 0],
    smallSeedRow 2 4 1 69313 69316 [26278, 18581, 11048, 5524, 1953, 488, 61, 2, 0, 0],
    smallSeedRow 2 5 1 69313 69316 [12691, 8373, 4487, 1953, 560, 106, 8, 0, 0, 0],
    smallSeedRow 3 0 2 109860 109863
      [315516, 282690, 239741, 192450, 138414, 89193, 46138, 17165, 4115, 263],
    smallSeedRow 3 1 2 109860 109863 [99550, 79913, 57475, 37037, 19158, 7955, 2128, 294, 16, 0],
    smallSeedRow 3 2 2 109860 109863 [31410, 22590, 13779, 7127, 2651, 709, 98, 5, 0, 0],
    smallSeedRow 3 3 2 109860 109863 [9910, 6386, 3303, 1371, 367, 63, 4, 0, 0, 0],
    smallSeedRow 5 0 3 160942 160945
      [184536, 157103, 123406, 89442, 55189, 28991, 11037, 2593, 320, 5],
    smallSeedRow 5 1 3 160942 160945 [34053, 24681, 15229, 8000, 3045, 840, 121, 6, 0, 0],
    smallSeedRow 7 0 3 194590 194593 [129612, 106693, 79684, 53994, 30117, 13828, 4302, 746, 59, 0],
    smallSeedRow 7 1 3 194590 194593 [16799, 11383, 6349, 2915, 907, 191, 18, 0, 0, 0],
    smallSeedRow 11 0 4 239788 239791 [80637, 63445, 44278, 27410, 13350, 5116, 1213, 140, 6, 0],
    smallSeedRow 13 0 4 256493 256496 [67664, 52355, 35634, 21334, 9883, 3542, 760, 75, 2, 0],
    smallSeedRow 17 0 5 283320 283323 [51053, 38457, 25142, 14266, 6098, 1963, 358, 28, 0, 0],
    smallSeedRow 19 0 5 294442 294445 [45426, 33840, 21758, 12074, 4991, 1537, 262, 18, 0, 0],
    smallSeedRow 23 0 5 313548 313551 [37169, 27165, 16972, 9065, 3539, 1009, 153, 9, 0, 0],
    smallSeedRow 29 0 5 336728 336731 [29139, 20808, 12556, 6403, 2331, 606, 80, 3, 0, 0],
    smallSeedRow 31 0 5 343397 343400 [27168, 19272, 11514, 5793, 2067, 523, 66, 3, 0, 0],
    smallSeedRow 37 0 6 361090 361093 [22562, 15724, 9148, 4443, 1503, 354, 40, 1, 0, 0],
    smallSeedRow 41 0 6 371356 371359 [20257, 13973, 8005, 3809, 1250, 283, 30, 1, 0, 0],
    smallSeedRow 43 0 6 376119 376122 [19268, 13228, 7524, 3546, 1147, 254, 26, 0, 0, 0],
    smallSeedRow 47 0 6 385013 385016 [17550, 11942, 6703, 3103, 977, 209, 20, 0, 0, 0],
    smallSeedRow 53 0 6 397028 397031 [15470, 10401, 5733, 2591, 787, 160, 14, 0, 0, 0],
    smallSeedRow 59 0 6 407752 407755 [13823, 9194, 4987, 2206, 649, 127, 11, 0, 0, 0],
    smallSeedRow 61 0 6 411086 411089 [13347, 8848, 4776, 2098, 611, 118, 10, 0, 0, 0],
    smallSeedRow 67 0 7 420468 420471 [12095, 7943, 4227, 1823, 516, 96, 7, 0, 0, 0],
    smallSeedRow 71 0 7 426266 426269 [11380, 7431, 3920, 1671, 465, 84, 6, 0, 0, 0],
    smallSeedRow 73 0 7 429044 429047 [11053, 7197, 3781, 1603, 442, 79, 6, 0, 0, 0],
    smallSeedRow 79 0 7 436943 436946 [10173, 6572, 3412, 1424, 383, 66, 4, 0, 0, 0],
    smallSeedRow 83 0 7 441883 441886 [9659, 6209, 3200, 1322, 351, 59, 4, 0, 0, 0],
    smallSeedRow 89 0 7 448862 448865 [8977, 5730, 2922, 1191, 309, 51, 3, 0, 0, 0],
    smallSeedRow 97 0 7 457470 457473 [8201, 5190, 2613, 1046, 265, 42, 2, 0, 0, 0]]

/-- Claim: every seed row passes the existing logarithm and power checks.
Proof: exact kernel reduction. Role: certify all real interval meanings. -/
theorem small_seed_rows_check : smallSeedRows.Forall (fun r ↦ r.check = true) := by decide +kernel

/-- Claim: the sum of rational row allowances is at least 317/100.
Proof: exact rational kernel reduction. Role: supply the numerical seed prefix bound. -/
theorem small_seed_sum_lower :
    (317 / 100 : ℚ) ≤ (smallSeedRows.map GammaFiniteEulerRow.lower).sum := by decide +kernel

/-- Claim: all row bases are prime. Proof: kernel arithmetic reduction.
Role: justify Mangoldt evaluation at the seed prime powers. -/
theorem small_seed_primes : smallSeedRows.Forall (fun r ↦ r.prime.Prime) := by decide +kernel

/-- Claim: seed prime-power indices are distinct. Proof: exact kernel reduction.
Role: prevent double counting in the finite sum comparison. -/
theorem small_seed_distinct : (smallSeedRows.map GammaFiniteEulerRow.index).Nodup := by
  decide +kernel

/-- Claim: every seed index belongs to (0,100]. Proof: kernel arithmetic reduction.
Role: embed the row sum in the actual prefix without requiring exhaustive coverage. -/
theorem small_seed_members : smallSeedRows.Forall (fun r ↦ 0 < r.index ∧ r.index ≤ 100) := by
  decide +kernel

/-- Claim: the actual signed Mangoldt Euler prefix through 100 is at least 317/100.
Proof: sum the validated prime-power rows and use nonnegativity on omitted inputs.
Role: provide the small-cutoff input for analytic prefix transport, without RH. -/
theorem gamma_euler_prefix_lower_100 :
    (317 / 100 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 100, gammaResolventMangoldtWeight m := by
  have h :=
    gamma_finite_row_block_lower smallSeedRows 0 100 small_seed_primes small_seed_rows_check
      small_seed_distinct small_seed_members
  have hs := (Rat.cast_le (K := ℝ)).mpr small_seed_sum_lower
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact hs.trans h

end PseudoPrime.Analysis
