/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 292. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell05Rows : List Target028GeneralWeightRow :=
  [⟨292, 2, 7, 4981, 4986, 8220, 1415, 269215, 59300⟩,
    ⟨292, 3, 7, 4576, 4581, 7783, 1733, 416760, 57014⟩,
    ⟨292, 4, 6, 4288, 4293, 7472, 2000, 568789, 54978⟩,
    ⟨292, 5, 6, 4065, 4070, 7231, 2237, 723796, 53090⟩,
    ⟨292, 7, 5, 3728, 3733, 6867, 2646, 1041597, 49881⟩,
    ⟨292, 8, 5, 3595, 3600, 6724, 2829, 1201721, 48423⟩,
    ⟨292, 9, 5, 3477, 3482, 6596, 3000, 1365820, 47159⟩,
    ⟨292, 15, 4, 2966, 2971, 6044, 3873, 2372051, 40969⟩,
    ⟨292, 20, 4, 2679, 2684, 5734, 4473, 3234114, 37163⟩,
    ⟨292, 25, 4, 2455, 2460, 5492, 5000, 4119596, 34130⟩,
    ⟨292, 30, 3, 2273, 2278, 5296, 5478, 5011600, 31578⟩,
    ⟨292, 35, 3, 2119, 2124, 5129, 5917, 5922479, 29448⟩,
    ⟨292, 40, 3, 1985, 1990, 4985, 6325, 6839778, 27569⟩,
    ⟨292, 45, 3, 1868, 1873, 4858, 6709, 7766000, 25951⟩,
    ⟨292, 50, 3, 1762, 1767, 4744, 7072, 8703761, 24487⟩,
    ⟨292, 55, 2, 1667, 1672, 4641, 7417, 9648044, 23197⟩,
    ⟨292, 60, 2, 1580, 1585, 4547, 7746, 10598953, 22026⟩,
    ⟨292, 65, 2, 1500, 1505, 4461, 8063, 11550806, 20949⟩,
    ⟨292, 70, 2, 1426, 1431, 4381, 8367, 12512839, 19977⟩,
    ⟨292, 75, 2, 1357, 1362, 4306, 8661, 13487391, 19089⟩,
    ⟨292, 80, 2, 1292, 1297, 4236, 8945, 14465337, 18258⟩,
    ⟨292, 85, 2, 1232, 1237, 4171, 9220, 15436815, 17498⟩,
    ⟨292, 90, 2, 1174, 1179, 4109, 9487, 16424190, 16774⟩,
    ⟨292, 100, 2, 1069, 1074, 3995, 10000, 18407446, 15502⟩,
    ⟨292, 105, 1, 1020, 1025, 3942, 10247, 19409357, 14922⟩,
    ⟨292, 110, 1, 974, 979, 3893, 10489, 20384101, 14368⟩,
    ⟨292, 115, 1, 929, 934, 3844, 10724, 21407798, 13859⟩,
    ⟨292, 125, 1, 846, 851, 3755, 11181, 23400450, 12910⟩,
    ⟨292, 130, 1, 807, 812, 3712, 11402, 24428617, 12490⟩,
    ⟨292, 135, 1, 769, 774, 3671, 11619, 25451006, 12079⟩,
    ⟨292, 140, 1, 733, 738, 3633, 11833, 26436755, 11680⟩,
    ⟨292, 150, 1, 664, 669, 3558, 12248, 28495759, 10964⟩,
    ⟨292, 155, 1, 631, 636, 3522, 12450, 29540295, 10631⟩,
    ⟨292, 160, 1, 599, 604, 3488, 12650, 30561934, 10303⟩,
    ⟨292, 165, 1, 568, 573, 3454, 12846, 31618907, 10002⟩,
    ⟨292, 170, 1, 538, 543, 3422, 13039, 32647075, 9705⟩,
    ⟨292, 175, 1, 509, 514, 3391, 13229, 33674985, 9423⟩,
    ⟨292, 180, 1, 481, 486, 3360, 13417, 34735258, 9163⟩,
    ⟨292, 185, 1, 454, 459, 3331, 13602, 35757329, 8907⟩,
    ⟨292, 195, 1, 401, 406, 3274, 13965, 37854704, 8420⟩,
    ⟨292, 200, 1, 376, 381, 3247, 14143, 38890705, 8195⟩,
    ⟨292, 215, 0, 304, 309, 3169, 14663, 42045622, 7568⟩,
    ⟨292, 225, 0, 258, 263, 3120, 15000, 44157168, 7179⟩,
    ⟨292, 230, 0, 236, 241, 3096, 15166, 45229760, 6999⟩,
    ⟨292, 235, 0, 215, 220, 3073, 15330, 46282100, 6829⟩,
    ⟨292, 240, 0, 194, 199, 3050, 15492, 47358924, 6663⟩,
    ⟨292, 245, 0, 173, 178, 3028, 15653, 48412366, 6494⟩,
    ⟨292, 255, 0, 133, 138, 2985, 15969, 50539503, 6183⟩,
    ⟨292, 260, 0, 114, 119, 2964, 16125, 51612055, 6041⟩,
    ⟨292, 265, 0, 95, 100, 2943, 16279, 52707369, 5902⟩,
    ⟨292, 270, 0, 76, 81, 2923, 16432, 53772128, 5760⟩,
    ⟨292, 275, 0, 57, 62, 2902, 16584, 54913283, 5626⟩,
    ⟨292, 280, 0, 39, 44, 2883, 16734, 55966610, 5494⟩,
    ⟨292, 285, 0, 22, 27, 2865, 16882, 56983131, 5370⟩,
    ⟨292, 290, 0, 4, 9, 2845, 17030, 58134266, 5249⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell05_rows_check : ∀ r ∈ target028Cell05Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell05Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 292)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell05RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell05Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨292, 290, 0, 4, 9, 2845, 17030, 58134266, 5249⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell05Weight (n : ℕ) : ℚ :=
  ((target028Cell05RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell05_select :
    ∀ n ∈ target028Cell05Prefix,
      1 ≤ n ∧
        target028Cell05RowFor n ∈ target028Cell05Rows ∧
        n ≤ (target028Cell05RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell05RowFor n).b) ∧ (target028Cell05RowFor n).cut = 292 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell05_sum_check :
    (2718 / 625 : ℚ) <
      ∑ n ∈ target028Cell05Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell05Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell05_principal :
    (2718 / 625 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(292 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 292 n).re := by
  have hs : target028Cell05Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell05Prefix ⊆ Finset.Ioc 0 ⌊(292 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell05_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell05Prefix, 0 ≤ target028Cell05Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell05Prefix, (target028Cell05Weight n : ℝ) ≤ refinedScaledWeight 292 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell05_select n hn
    have hcheck := target028_cell05_rows_check (target028Cell05RowFor n) hm
    have hrow := (target028Cell05RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell05RowFor n).b ≤ 292 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 292 (target028Cell05RowFor n).b ≤ refinedScaledWeight 292 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 292) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell05Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 292) target028Cell05Prefix
      target028Cell05Weight hs ht hw0 hw
  have hr :
    ((2718 / 625 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell05Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell05Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell05_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
