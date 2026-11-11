/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 328. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell07Rows : List Target028GeneralWeightRow :=
  [⟨328, 2, 7, 5097, 5102, 8346, 1415, 237343, 56390⟩,
    ⟨328, 3, 7, 4692, 4697, 7908, 1733, 367789, 54500⟩,
    ⟨328, 4, 6, 4404, 4409, 7597, 2000, 501955, 52727⟩,
    ⟨328, 5, 6, 4181, 4186, 7356, 2237, 638748, 51057⟩,
    ⟨328, 7, 6, 3845, 3850, 6993, 2646, 918287, 48177⟩,
    ⟨328, 8, 5, 3711, 3716, 6849, 2829, 1060515, 46870⟩,
    ⟨328, 9, 5, 3593, 3598, 6721, 3000, 1205332, 45727⟩,
    ⟨328, 16, 4, 3018, 3023, 6100, 4000, 2242867, 39285⟩,
    ⟨328, 22, 4, 2699, 2704, 5756, 4691, 3163741, 35323⟩,
    ⟨328, 28, 4, 2458, 2463, 5496, 5292, 4103151, 32213⟩,
    ⟨328, 34, 3, 2264, 2269, 5286, 5831, 5061967, 29690⟩,
    ⟨328, 40, 3, 2102, 2107, 5111, 6325, 6030049, 27550⟩,
    ⟨328, 46, 3, 1962, 1967, 4960, 6783, 7012927, 25707⟩,
    ⟨328, 52, 3, 1839, 1844, 4827, 7212, 8010516, 24108⟩,
    ⟨328, 58, 2, 1730, 1735, 4709, 7616, 9013786, 22701⟩,
    ⟨328, 64, 2, 1632, 1637, 4603, 8000, 10021725, 21444⟩,
    ⟨328, 70, 2, 1542, 1547, 4506, 8367, 11042542, 20302⟩,
    ⟨328, 76, 2, 1460, 1465, 4418, 8718, 12058324, 19264⟩,
    ⟨328, 82, 2, 1384, 1389, 4336, 9056, 13088778, 18326⟩,
    ⟨328, 88, 2, 1313, 1318, 4259, 9381, 14136431, 17474⟩,
    ⟨328, 94, 2, 1247, 1252, 4188, 9696, 15176607, 16680⟩,
    ⟨328, 100, 2, 1185, 1190, 4121, 10000, 16228278, 15952⟩,
    ⟨328, 106, 2, 1127, 1132, 4058, 10296, 17283551, 15283⟩,
    ⟨328, 112, 2, 1072, 1077, 3999, 10584, 18333963, 14648⟩,
    ⟨328, 118, 1, 1020, 1025, 3942, 10863, 19409357, 14076⟩,
    ⟨328, 124, 1, 970, 975, 3888, 11136, 20486277, 13525⟩,
    ⟨328, 130, 1, 923, 928, 3838, 11402, 21536631, 13003⟩,
    ⟨328, 136, 1, 878, 883, 3789, 11662, 22618208, 12526⟩,
    ⟨328, 142, 1, 835, 840, 3743, 11917, 23682947, 12066⟩,
    ⟨328, 154, 1, 754, 759, 3655, 12410, 25861497, 11239⟩,
    ⟨328, 160, 1, 715, 720, 3613, 12650, 26970812, 10851⟩,
    ⟨328, 166, 1, 679, 684, 3574, 12885, 28043455, 10492⟩,
    ⟨328, 172, 1, 643, 648, 3535, 13115, 29158756, 10147⟩,
    ⟨328, 178, 1, 609, 614, 3499, 13342, 30227595, 9813⟩,
    ⟨328, 184, 1, 576, 581, 3463, 13565, 31335613, 9505⟩,
    ⟨328, 196, 1, 512, 517, 3394, 14000, 33574111, 8920⟩,
    ⟨328, 202, 1, 482, 487, 3361, 14213, 34700541, 8655⟩,
    ⟨328, 214, 1, 425, 430, 3300, 14629, 36883167, 8147⟩,
    ⟨328, 226, 1, 370, 375, 3240, 15034, 39163895, 7686⟩,
    ⟨328, 232, 0, 344, 349, 3212, 15232, 40275980, 7469⟩,
    ⟨328, 238, 0, 318, 323, 3184, 15428, 41419644, 7257⟩,
    ⟨328, 244, 0, 293, 298, 3157, 15621, 42553209, 7056⟩,
    ⟨328, 256, 0, 245, 250, 3105, 16000, 44824518, 6679⟩,
    ⟨328, 262, 0, 222, 227, 3081, 16187, 45913320, 6496⟩,
    ⟨328, 268, 0, 200, 205, 3057, 16371, 47028569, 6328⟩,
    ⟨328, 274, 0, 177, 182, 3032, 16553, 48219103, 6160⟩,
    ⟨328, 280, 0, 156, 161, 3009, 16734, 49340995, 6005⟩,
    ⟨328, 286, 0, 135, 140, 2987, 16912, 50438525, 5848⟩,
    ⟨328, 292, 0, 114, 119, 2964, 17089, 51612055, 5700⟩,
    ⟨328, 298, 0, 93, 98, 2941, 17263, 52812889, 5556⟩,
    ⟨328, 310, 0, 54, 59, 2899, 17607, 55078270, 5285⟩,
    ⟨328, 316, 0, 35, 40, 2879, 17777, 56190925, 5154⟩,
    ⟨328, 322, 0, 16, 21, 2858, 17945, 57383412, 5030⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell07_rows_check : ∀ r ∈ target028Cell07Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell07Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 328)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell07RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell07Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨328, 322, 0, 16, 21, 2858, 17945, 57383412, 5030⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell07Weight (n : ℕ) : ℚ :=
  ((target028Cell07RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell07_select :
    ∀ n ∈ target028Cell07Prefix,
      1 ≤ n ∧
        target028Cell07RowFor n ∈ target028Cell07Rows ∧
        n ≤ (target028Cell07RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell07RowFor n).b) ∧ (target028Cell07RowFor n).cut = 328 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell07_sum_check :
    (4541 / 1000 : ℚ) <
      ∑ n ∈ target028Cell07Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell07Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell07_principal :
    (4541 / 1000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(328 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 328 n).re := by
  have hs : target028Cell07Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell07Prefix ⊆ Finset.Ioc 0 ⌊(328 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell07_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell07Prefix, 0 ≤ target028Cell07Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell07Prefix, (target028Cell07Weight n : ℝ) ≤ refinedScaledWeight 328 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell07_select n hn
    have hcheck := target028_cell07_rows_check (target028Cell07RowFor n) hm
    have hrow := (target028Cell07RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell07RowFor n).b ≤ 328 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 328 (target028Cell07RowFor n).b ≤ refinedScaledWeight 328 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 328) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell07Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 328) target028Cell07Prefix
      target028Cell07Weight hs ht hw0 hw
  have hr :
    ((4541 / 1000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell07Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell07Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell07_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
