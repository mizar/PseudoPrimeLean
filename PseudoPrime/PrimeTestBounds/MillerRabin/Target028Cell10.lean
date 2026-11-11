/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 411. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell10Rows : List Target028GeneralWeightRow :=
  [⟨411, 2, 8, 5323, 5328, 8590, 1415, 185956, 51036⟩,
    ⟨411, 3, 7, 4917, 4922, 8151, 1733, 288446, 49732⟩,
    ⟨411, 4, 7, 4630, 4635, 7841, 2000, 393275, 48393⟩,
    ⟨411, 5, 6, 4407, 4412, 7600, 2237, 500451, 47100⟩,
    ⟨411, 7, 6, 4070, 4075, 7236, 2646, 720186, 44827⟩,
    ⟨411, 8, 6, 3937, 3942, 7093, 2829, 830900, 43755⟩,
    ⟨411, 9, 6, 3819, 3824, 6965, 3000, 944362, 42828⟩,
    ⟨411, 18, 5, 3126, 3131, 6217, 4243, 1995221, 36221⟩,
    ⟨411, 26, 4, 2758, 2763, 5820, 5100, 2967605, 32202⟩,
    ⟨411, 34, 4, 2490, 2495, 5530, 5831, 3965989, 29159⟩,
    ⟨411, 42, 3, 2278, 2283, 5301, 6481, 4986604, 26693⟩,
    ⟨411, 50, 3, 2104, 2109, 5113, 7072, 6018001, 24643⟩,
    ⟨411, 58, 3, 1956, 1961, 4953, 7616, 7062190, 22906⟩,
    ⟨411, 66, 3, 1826, 1831, 4813, 8125, 8123452, 21386⟩,
    ⟨411, 74, 2, 1712, 1717, 4690, 8603, 9186686, 20062⟩,
    ⟨411, 82, 2, 1609, 1614, 4579, 9056, 10265156, 18885⟩,
    ⟨411, 90, 2, 1516, 1521, 4478, 9487, 11356102, 17846⟩,
    ⟨411, 98, 2, 1431, 1436, 4386, 9900, 12450431, 16903⟩,
    ⟨411, 106, 2, 1353, 1358, 4302, 10296, 13541449, 16041⟩,
    ⟨411, 114, 2, 1280, 1285, 4223, 10678, 14654614, 15259⟩,
    ⟨411, 122, 2, 1212, 1217, 4150, 11046, 15764416, 14533⟩,
    ⟨411, 130, 2, 1149, 1154, 4082, 11402, 16873684, 13873⟩,
    ⟨411, 138, 2, 1089, 1094, 4017, 11748, 18006904, 13262⟩,
    ⟨411, 146, 1, 1032, 1037, 3955, 12084, 19158668, 12697⟩,
    ⟨411, 154, 1, 979, 984, 3898, 12410, 20282435, 12167⟩,
    ⟨411, 162, 1, 928, 933, 3843, 12728, 21429217, 11672⟩,
    ⟨411, 170, 1, 880, 885, 3791, 13039, 22573017, 11213⟩,
    ⟨411, 178, 1, 834, 839, 3742, 13342, 23706642, 10773⟩,
    ⟨411, 186, 1, 790, 795, 3694, 13639, 24872313, 10371⟩,
    ⟨411, 194, 1, 748, 753, 3649, 13929, 26017132, 9985⟩,
    ⟨411, 202, 1, 708, 713, 3606, 14213, 27160270, 9624⟩,
    ⟨411, 218, 1, 632, 637, 3523, 14765, 29510769, 8969⟩,
    ⟨411, 226, 1, 596, 601, 3485, 15034, 30653758, 8655⟩,
    ⟨411, 234, 1, 561, 566, 3447, 15298, 31841016, 8366⟩,
    ⟨411, 242, 1, 527, 532, 3410, 15557, 33041200, 8090⟩,
    ⟨411, 250, 1, 495, 500, 3375, 15812, 34218118, 7833⟩,
    ⟨411, 258, 1, 463, 468, 3341, 16063, 35401538, 7577⟩,
    ⟨411, 266, 1, 433, 438, 3309, 16310, 36552708, 7338⟩,
    ⟨411, 274, 1, 403, 408, 3276, 16553, 37779071, 7113⟩,
    ⟨411, 282, 1, 374, 379, 3245, 16793, 38968564, 6892⟩,
    ⟨411, 290, 1, 346, 351, 3215, 17030, 40155333, 6683⟩,
    ⟨411, 298, 0, 319, 324, 3185, 17263, 41378245, 6490⟩,
    ⟨411, 314, 0, 267, 272, 3129, 17721, 43761536, 6116⟩,
    ⟨411, 322, 0, 242, 247, 3102, 17945, 44959193, 5942⟩,
    ⟨411, 338, 0, 193, 198, 3049, 18385, 47406306, 5610⟩,
    ⟨411, 346, 0, 170, 175, 3024, 18602, 48606403, 5457⟩,
    ⟨411, 354, 0, 147, 152, 3000, 18815, 49787068, 5302⟩,
    ⟨411, 362, 0, 124, 129, 2975, 19027, 51047433, 5157⟩,
    ⟨411, 370, 0, 103, 108, 2952, 19236, 52235131, 5023⟩,
    ⟨411, 378, 0, 81, 86, 2928, 19443, 53503939, 4888⟩,
    ⟨411, 386, 0, 60, 65, 2906, 19647, 54694069, 4756⟩,
    ⟨411, 394, 0, 40, 45, 2884, 19850, 55910672, 4636⟩,
    ⟨411, 402, 0, 20, 25, 2862, 20050, 57154337, 4518⟩,
    ⟨411, 410, 0, 0, 5, 2841, 20249, 58367269, 4398⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell10_rows_check : ∀ r ∈ target028Cell10Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell10Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 411)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell10RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell10Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨411, 410, 0, 0, 5, 2841, 20249, 58367269, 4398⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell10Weight (n : ℕ) : ℚ :=
  ((target028Cell10RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell10_select :
    ∀ n ∈ target028Cell10Prefix,
      1 ≤ n ∧
        target028Cell10RowFor n ∈ target028Cell10Rows ∧
        n ≤ (target028Cell10RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell10RowFor n).b) ∧ (target028Cell10RowFor n).cut = 411 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell10_sum_check :
    (51479 / 10000 : ℚ) <
      ∑ n ∈ target028Cell10Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell10Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell10_principal :
    (51479 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(411 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 411 n).re := by
  have hs : target028Cell10Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell10Prefix ⊆ Finset.Ioc 0 ⌊(411 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell10_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell10Prefix, 0 ≤ target028Cell10Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell10Prefix, (target028Cell10Weight n : ℝ) ≤ refinedScaledWeight 411 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell10_select n hn
    have hcheck := target028_cell10_rows_check (target028Cell10RowFor n) hm
    have hrow := (target028Cell10RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell10RowFor n).b ≤ 411 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 411 (target028Cell10RowFor n).b ≤ refinedScaledWeight 411 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 411) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell10Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 411) target028Cell10Prefix
      target028Cell10Weight hs ht hw0 hw
  have hr :
    ((51479 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell10Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell10Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell10_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
