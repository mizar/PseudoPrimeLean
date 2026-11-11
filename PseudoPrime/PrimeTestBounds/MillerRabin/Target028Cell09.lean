/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 378. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell09Rows : List Target028GeneralWeightRow :=
  [⟨378, 2, 8, 5239, 5244, 8499, 1415, 203671, 53006⟩,
    ⟨378, 3, 7, 4834, 4839, 8062, 1733, 315295, 51435⟩,
    ⟨378, 4, 7, 4546, 4551, 7751, 2000, 430312, 49956⟩,
    ⟨378, 5, 6, 4323, 4328, 7510, 2237, 547581, 48530⟩,
    ⟨378, 7, 6, 3986, 3991, 7146, 2646, 788009, 46048⟩,
    ⟨378, 8, 6, 3853, 3858, 7002, 2829, 910060, 44934⟩,
    ⟨378, 9, 5, 3735, 3740, 6875, 3000, 1033297, 43886⟩,
    ⟨378, 17, 4, 3099, 3104, 6188, 4124, 2053930, 37471⟩,
    ⟨378, 24, 4, 2754, 2759, 5815, 4899, 2982480, 33567⟩,
    ⟨378, 31, 4, 2498, 2503, 5539, 5568, 3930455, 30500⟩,
    ⟨378, 38, 3, 2295, 2300, 5319, 6165, 4897648, 28042⟩,
    ⟨378, 45, 3, 2126, 2131, 5137, 6709, 5875289, 25955⟩,
    ⟨378, 52, 3, 1981, 1986, 4980, 7212, 6874062, 24194⟩,
    ⟨378, 59, 3, 1855, 1860, 4844, 7682, 7875489, 22653⟩,
    ⟨378, 66, 3, 1743, 1748, 4723, 8125, 8888473, 21298⟩,
    ⟨378, 73, 2, 1642, 1647, 4614, 8545, 9912090, 20091⟩,
    ⟨378, 80, 2, 1550, 1555, 4515, 8945, 10943605, 19002⟩,
    ⟨378, 87, 2, 1466, 1471, 4424, 9328, 11986191, 18029⟩,
    ⟨378, 94, 2, 1389, 1394, 4341, 9696, 13023498, 17137⟩,
    ⟨378, 101, 2, 1317, 1322, 4263, 10050, 14079998, 16328⟩,
    ⟨378, 108, 2, 1250, 1255, 4191, 10393, 15131146, 15574⟩,
    ⟨378, 115, 2, 1187, 1192, 4123, 10724, 16195853, 14885⟩,
    ⟨378, 122, 2, 1128, 1133, 4059, 11046, 17266276, 14250⟩,
    ⟨378, 129, 2, 1073, 1078, 4000, 11358, 18315638, 13655⟩,
    ⟨378, 136, 1, 1020, 1025, 3942, 11662, 19409357, 13111⟩,
    ⟨378, 143, 1, 970, 975, 3888, 11959, 20486277, 12595⟩,
    ⟨378, 150, 1, 922, 927, 3837, 12248, 21558178, 12100⟩,
    ⟨378, 157, 1, 876, 881, 3787, 12530, 22663490, 11648⟩,
    ⟨378, 164, 1, 833, 838, 3741, 12807, 23730360, 11218⟩,
    ⟨378, 171, 1, 791, 796, 3695, 13077, 24847453, 10821⟩,
    ⟨378, 178, 1, 751, 756, 3652, 13342, 25939198, 10439⟩,
    ⟨378, 185, 1, 712, 717, 3610, 13602, 27051846, 10076⟩,
    ⟨378, 192, 1, 675, 680, 3570, 13857, 28155853, 9736⟩,
    ⟨378, 199, 1, 639, 644, 3531, 14107, 29275625, 9413⟩,
    ⟨378, 213, 1, 571, 576, 3458, 14595, 31492684, 8810⟩,
    ⟨378, 227, 1, 507, 512, 3388, 15067, 33776161, 8272⟩,
    ⟨378, 234, 1, 477, 482, 3356, 15298, 34874478, 8017⟩,
    ⟨378, 241, 1, 448, 453, 3325, 15525, 35972518, 7774⟩,
    ⟨378, 248, 1, 419, 424, 3293, 15749, 37142255, 7547⟩,
    ⟨378, 255, 1, 391, 396, 3263, 15969, 38273405, 7323⟩,
    ⟨378, 262, 1, 364, 369, 3234, 16187, 39399584, 7110⟩,
    ⟨378, 269, 0, 338, 343, 3206, 16402, 40518362, 6907⟩,
    ⟨378, 276, 0, 312, 317, 3178, 16614, 41668909, 6711⟩,
    ⟨378, 283, 0, 287, 292, 3151, 16823, 42809296, 6524⟩,
    ⟨378, 290, 0, 263, 268, 3125, 17030, 43936933, 6346⟩,
    ⟨378, 297, 0, 239, 244, 3099, 17234, 45094274, 6173⟩,
    ⟨378, 311, 0, 193, 198, 3049, 17636, 47406306, 5848⟩,
    ⟨378, 318, 0, 170, 175, 3024, 17833, 48606403, 5692⟩,
    ⟨378, 332, 0, 127, 132, 2978, 18221, 50894521, 5398⟩,
    ⟨378, 339, 0, 106, 111, 2955, 18412, 52078660, 5261⟩,
    ⟨378, 346, 0, 86, 91, 2934, 18602, 53183876, 5126⟩,
    ⟨378, 353, 0, 66, 71, 2912, 18789, 54366887, 4999⟩,
    ⟨378, 360, 0, 46, 51, 2891, 18974, 55520664, 4870⟩,
    ⟨378, 367, 0, 27, 32, 2870, 19158, 56698926, 4753⟩,
    ⟨378, 374, 0, 8, 13, 2850, 19340, 57844320, 4634⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell09_rows_check : ∀ r ∈ target028Cell09Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell09Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 378)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell09RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell09Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨378, 374, 0, 8, 13, 2850, 19340, 57844320, 4634⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell09Weight (n : ℕ) : ℚ :=
  ((target028Cell09RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell09_select :
    ∀ n ∈ target028Cell09Prefix,
      1 ≤ n ∧
        target028Cell09RowFor n ∈ target028Cell09Rows ∧
        n ≤ (target028Cell09RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell09RowFor n).b) ∧ (target028Cell09RowFor n).cut = 378 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell09_sum_check :
    (49451 / 10000 : ℚ) <
      ∑ n ∈ target028Cell09Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell09Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell09_principal :
    (49451 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(378 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 378 n).re := by
  have hs : target028Cell09Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell09Prefix ⊆ Finset.Ioc 0 ⌊(378 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell09_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell09Prefix, 0 ≤ target028Cell09Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell09Prefix, (target028Cell09Weight n : ℝ) ≤ refinedScaledWeight 378 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell09_select n hn
    have hcheck := target028_cell09_rows_check (target028Cell09RowFor n) hm
    have hrow := (target028Cell09RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell09RowFor n).b ≤ 378 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 378 (target028Cell09RowFor n).b ≤ refinedScaledWeight 378 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 378) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell09Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 378) target028Cell09Prefix
      target028Cell09Weight hs ht hw0 hw
  have hr :
    ((49451 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell09Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell09Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell09_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
