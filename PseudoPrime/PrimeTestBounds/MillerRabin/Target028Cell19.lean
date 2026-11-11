/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 19 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 885. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell19Rows : List Target028GeneralWeightRow :=
  [⟨885, 2, 9, 6090, 6095, 9418, 1415, 81248, 35345⟩,
    ⟨885, 3, 8, 5684, 5689, 8980, 1733, 125902, 35230⟩,
    ⟨885, 4, 8, 5397, 5402, 8670, 2000, 171659, 34913⟩,
    ⟨885, 5, 7, 5174, 5179, 8429, 2237, 218439, 34498⟩,
    ⟨885, 7, 7, 4837, 4842, 8065, 2646, 314351, 33654⟩,
    ⟨885, 8, 7, 4704, 4709, 7921, 2829, 363039, 33226⟩,
    ⟨885, 9, 7, 4586, 4591, 7794, 3000, 412200, 32802⟩,
    ⟨885, 27, 5, 3487, 3492, 6607, 5197, 1350878, 27146⟩,
    ⟨885, 44, 4, 2999, 3004, 6080, 6634, 2288176, 23761⟩,
    ⟨885, 61, 4, 2672, 2677, 5727, 7811, 3256833, 21290⟩,
    ⟨885, 78, 4, 2426, 2431, 5461, 8832, 4249304, 19367⟩,
    ⟨885, 95, 3, 2229, 2234, 5248, 9747, 5258023, 17798⟩,
    ⟨885, 112, 3, 2065, 2070, 5071, 10584, 6276140, 16475⟩,
    ⟨885, 129, 3, 1923, 1928, 4918, 11358, 7313743, 15341⟩,
    ⟨885, 146, 3, 1799, 1804, 4784, 12084, 8362482, 14359⟩,
    ⟨885, 163, 2, 1689, 1694, 4665, 12768, 9419248, 13496⟩,
    ⟨885, 180, 2, 1590, 1595, 4558, 13417, 10483003, 12727⟩,
    ⟨885, 197, 2, 1500, 1505, 4461, 14036, 11550806, 12034⟩,
    ⟨885, 214, 2, 1417, 1422, 4371, 14629, 12638595, 11413⟩,
    ⟨885, 231, 2, 1341, 1346, 4289, 15199, 13718637, 10844⟩,
    ⟨885, 248, 2, 1270, 1275, 4212, 15749, 14816705, 10326⟩,
    ⟨885, 265, 2, 1203, 1208, 4140, 16279, 15922851, 9844⟩,
    ⟨885, 282, 2, 1141, 1146, 4073, 16793, 17026233, 9404⟩,
    ⟨885, 299, 2, 1083, 1088, 4011, 17292, 18115270, 8991⟩,
    ⟨885, 316, 1, 1027, 1032, 3950, 17777, 19254701, 8615⟩,
    ⟨885, 333, 1, 975, 980, 3894, 18249, 20363727, 8261⟩,
    ⟨885, 350, 1, 925, 930, 3840, 18709, 21493601, 7931⟩,
    ⟨885, 367, 1, 878, 883, 3789, 19158, 22618208, 7625⟩,
    ⟨885, 384, 1, 832, 837, 3739, 19596, 23777869, 7335⟩,
    ⟨885, 401, 1, 789, 794, 3693, 20025, 24897198, 7060⟩,
    ⟨885, 418, 1, 748, 753, 3649, 20446, 26017132, 6802⟩,
    ⟨885, 435, 1, 708, 713, 3606, 20857, 27160270, 6558⟩,
    ⟨885, 452, 1, 669, 674, 3563, 21261, 28353636, 6332⟩,
    ⟨885, 469, 1, 632, 637, 3523, 21657, 29510769, 6115⟩,
    ⟨885, 486, 1, 597, 602, 3486, 22046, 30623119, 5905⟩,
    ⟨885, 503, 1, 562, 567, 3448, 22428, 31809191, 5709⟩,
    ⟨885, 520, 1, 529, 534, 3412, 22804, 32975183, 5526⟩,
    ⟨885, 537, 1, 497, 502, 3378, 23174, 34115617, 5346⟩,
    ⟨885, 554, 1, 466, 471, 3344, 23538, 35295492, 5180⟩,
    ⟨885, 571, 1, 436, 441, 3312, 23896, 36443214, 5018⟩,
    ⟨885, 588, 1, 406, 411, 3279, 24249, 37665903, 4865⟩,
    ⟨885, 605, 1, 378, 383, 3249, 24597, 38813001, 4718⟩,
    ⟨885, 622, 1, 350, 355, 3219, 24940, 39995033, 4575⟩,
    ⟨885, 639, 0, 323, 328, 3190, 25279, 41171870, 4440⟩,
    ⟨885, 656, 0, 297, 302, 3162, 25613, 42340974, 4311⟩,
    ⟨885, 673, 0, 271, 276, 3134, 25943, 43543275, 4186⟩,
    ⟨885, 690, 0, 246, 251, 3107, 26268, 44734959, 4067⟩,
    ⟨885, 707, 0, 222, 227, 3081, 26590, 45913320, 3954⟩,
    ⟨885, 724, 0, 198, 203, 3055, 26908, 47122720, 3844⟩,
    ⟨885, 741, 0, 175, 180, 3030, 27222, 48315638, 3740⟩,
    ⟨885, 758, 0, 152, 157, 3005, 27532, 49538754, 3638⟩,
    ⟨885, 775, 0, 130, 135, 2981, 27839, 50742066, 3542⟩,
    ⟨885, 792, 0, 109, 114, 2959, 28143, 51870761, 3447⟩,
    ⟨885, 809, 0, 87, 92, 2935, 28443, 53130719, 3355⟩,
    ⟨885, 826, 0, 66, 71, 2912, 28741, 54366887, 3268⟩,
    ⟨885, 843, 0, 46, 51, 2891, 29035, 55520664, 3183⟩,
    ⟨885, 860, 0, 26, 31, 2869, 29326, 56755653, 3102⟩,
    ⟨885, 877, 0, 7, 12, 2848, 29615, 57960125, 3026⟩,
    ⟨885, 885, 0, -2, 2, 2838, 29749, 58542634, 2991⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell19_rows_check : ∀ r ∈ target028Cell19Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell19Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 885)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell19RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell19Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨885, 885, 0, -2, 2, 2838, 29749, 58542634, 2991⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell19Weight (n : ℕ) : ℚ :=
  ((target028Cell19RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell19_select :
    ∀ n ∈ target028Cell19Prefix,
      1 ≤ n ∧
        target028Cell19RowFor n ∈ target028Cell19Rows ∧
        n ≤ (target028Cell19RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell19RowFor n).b) ∧ (target028Cell19RowFor n).cut = 885 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell19_sum_check :
    (763 / 100 : ℚ) <
      ∑ n ∈ target028Cell19Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell19Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell19_principal :
    (763 / 100 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(885 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 885 n).re := by
  have hs : target028Cell19Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell19Prefix ⊆ Finset.Ioc 0 ⌊(885 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell19_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell19Prefix, 0 ≤ target028Cell19Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell19Prefix, (target028Cell19Weight n : ℝ) ≤ refinedScaledWeight 885 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell19_select n hn
    have hcheck := target028_cell19_rows_check (target028Cell19RowFor n) hm
    have hrow := (target028Cell19RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell19RowFor n).b ≤ 885 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 885 (target028Cell19RowFor n).b ≤ refinedScaledWeight 885 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 885) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell19Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 885) target028Cell19Prefix
      target028Cell19Weight hs ht hw0 hw
  have hr :
    ((763 / 100 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell19Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell19Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell19_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
