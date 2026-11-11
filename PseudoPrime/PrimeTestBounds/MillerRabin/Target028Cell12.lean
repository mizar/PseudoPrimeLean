/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 12 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 499. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell12Rows : List Target028GeneralWeightRow :=
  [⟨499, 2, 8, 5517, 5522, 8799, 1415, 150883, 46717⟩,
    ⟨499, 3, 7, 5111, 5116, 8361, 1733, 233810, 45770⟩,
    ⟨499, 4, 7, 4824, 4829, 8051, 2000, 318782, 44760⟩,
    ⟨499, 5, 7, 4601, 4606, 7810, 2237, 405658, 43744⟩,
    ⟨499, 7, 6, 4264, 4269, 7446, 2646, 583772, 41915⟩,
    ⟨499, 8, 6, 4131, 4136, 7302, 2829, 674189, 41070⟩,
    ⟨499, 9, 6, 4013, 4018, 7175, 3000, 765485, 40266⟩,
    ⟨499, 19, 5, 3266, 3271, 6368, 4359, 1715586, 34190⟩,
    ⟨499, 28, 4, 2878, 2883, 5949, 5292, 2608447, 30457⟩,
    ⟨499, 37, 4, 2599, 2604, 5648, 6083, 3524558, 27601⟩,
    ⟨499, 46, 3, 2381, 2386, 5412, 6783, 4462705, 25326⟩,
    ⟨499, 55, 3, 2203, 2208, 5220, 7417, 5407329, 23416⟩,
    ⟨499, 64, 3, 2051, 2056, 5056, 8000, 6370992, 21798⟩,
    ⟨499, 73, 3, 1920, 1925, 4914, 8545, 7343057, 20406⟩,
    ⟨499, 82, 3, 1803, 1808, 4788, 9056, 8329098, 19170⟩,
    ⟨499, 91, 2, 1699, 1704, 4676, 9540, 9316204, 18074⟩,
    ⟨499, 100, 2, 1605, 1610, 4574, 10000, 10316610, 17107⟩,
    ⟨499, 109, 2, 1519, 1524, 4481, 10441, 11322085, 16226⟩,
    ⟨499, 118, 2, 1439, 1444, 4395, 10863, 12338880, 15418⟩,
    ⟨499, 127, 2, 1366, 1371, 4316, 11270, 13353189, 14689⟩,
    ⟨499, 136, 2, 1297, 1302, 4242, 11662, 14378805, 14009⟩,
    ⟨499, 145, 2, 1233, 1238, 4173, 12042, 15405972, 13388⟩,
    ⟨499, 154, 2, 1173, 1178, 4108, 12410, 16440622, 12819⟩,
    ⟨499, 163, 2, 1116, 1121, 4046, 12768, 17492203, 12291⟩,
    ⟨499, 172, 2, 1063, 1068, 3989, 13115, 18518223, 11795⟩,
    ⟨499, 181, 1, 1012, 1017, 3934, 13454, 19565254, 11331⟩,
    ⟨499, 199, 1, 917, 922, 3831, 14107, 21687916, 10494⟩,
    ⟨499, 217, 1, 830, 835, 3737, 14731, 23825472, 9749⟩,
    ⟨499, 226, 1, 790, 795, 3694, 15034, 24872313, 9408⟩,
    ⟨499, 235, 1, 751, 756, 3652, 15330, 25939198, 9085⟩,
    ⟨499, 244, 1, 713, 718, 3611, 15621, 27024808, 8778⟩,
    ⟨499, 253, 1, 677, 682, 3572, 15906, 28099598, 8491⟩,
    ⟨499, 262, 1, 642, 647, 3534, 16187, 29187930, 8217⟩,
    ⟨499, 271, 1, 608, 613, 3498, 16463, 30257838, 7948⟩,
    ⟨499, 280, 1, 575, 580, 3462, 16734, 31366965, 7701⟩,
    ⟨499, 289, 1, 544, 549, 3428, 17000, 32451779, 7470⟩,
    ⟨499, 298, 1, 513, 518, 3395, 17263, 33540554, 7238⟩,
    ⟨499, 307, 1, 483, 488, 3363, 17522, 34631209, 7018⟩,
    ⟨499, 316, 1, 454, 459, 3331, 17777, 35757329, 6815⟩,
    ⟨499, 325, 1, 426, 431, 3301, 18028, 36846302, 6615⟩,
    ⟨499, 334, 1, 399, 404, 3272, 18276, 37930490, 6426⟩,
    ⟨499, 343, 1, 372, 377, 3243, 18521, 39046579, 6241⟩,
    ⟨499, 352, 1, 346, 351, 3215, 18762, 40155333, 6066⟩,
    ⟨499, 361, 0, 321, 326, 3188, 19000, 41254297, 5899⟩,
    ⟨499, 370, 0, 297, 302, 3162, 19236, 42340974, 5740⟩,
    ⟨499, 379, 0, 273, 278, 3136, 19468, 43456275, 5586⟩,
    ⟨499, 388, 0, 249, 254, 3110, 19698, 44600955, 5436⟩,
    ⟨499, 397, 0, 226, 231, 3085, 19925, 45730033, 5293⟩,
    ⟨499, 406, 0, 204, 209, 3061, 20150, 46840830, 5157⟩,
    ⟨499, 415, 0, 182, 187, 3037, 20372, 47978609, 5025⟩,
    ⟨499, 424, 0, 160, 165, 3014, 20592, 49094905, 4891⟩,
    ⟨499, 433, 0, 139, 144, 2991, 20809, 50237174, 4768⟩,
    ⟨499, 442, 0, 119, 124, 2969, 21024, 51354639, 4652⟩,
    ⟨499, 451, 0, 99, 104, 2948, 21237, 52444490, 4535⟩,
    ⟨499, 460, 0, 79, 84, 2926, 21448, 53611053, 4424⟩,
    ⟨499, 469, 0, 60, 65, 2906, 21657, 54694069, 4315⟩,
    ⟨499, 487, 0, 22, 27, 2865, 22069, 56983131, 4108⟩,
    ⟨499, 496, 0, 4, 9, 2845, 22272, 58134266, 4013⟩,
    ⟨499, 499, 0, -2, 2, 2838, 22339, 58542634, 3984⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell12_rows_check : ∀ r ∈ target028Cell12Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell12Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 499)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell12RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell12Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨499, 499, 0, -2, 2, 2838, 22339, 58542634, 3984⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell12Weight (n : ℕ) : ℚ :=
  ((target028Cell12RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell12_select :
    ∀ n ∈ target028Cell12Prefix,
      1 ≤ n ∧
        target028Cell12RowFor n ∈ target028Cell12Rows ∧
        n ≤ (target028Cell12RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell12RowFor n).b) ∧ (target028Cell12RowFor n).cut = 499 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell12_sum_check :
    (57287 / 10000 : ℚ) <
      ∑ n ∈ target028Cell12Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell12Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell12_principal :
    (57287 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(499 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 499 n).re := by
  have hs : target028Cell12Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell12Prefix ⊆ Finset.Ioc 0 ⌊(499 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell12_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell12Prefix, 0 ≤ target028Cell12Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell12Prefix, (target028Cell12Weight n : ℝ) ≤ refinedScaledWeight 499 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell12_select n hn
    have hcheck := target028_cell12_rows_check (target028Cell12RowFor n) hm
    have hrow := (target028Cell12RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell12RowFor n).b ≤ 499 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 499 (target028Cell12RowFor n).b ≤ refinedScaledWeight 499 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 499) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell12Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 499) target028Cell12Prefix
      target028Cell12Weight hs ht hw0 hw
  have hr :
    ((57287 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell12Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell12Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell12_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
