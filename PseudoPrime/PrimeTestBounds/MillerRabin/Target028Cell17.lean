/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Uniform analytic cell 17 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 763. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell17Rows : List Target028GeneralWeightRow :=
  [⟨763, 2, 9, 5942, 5947, 9258, 1415, 95345, 38073⟩,
    ⟨763, 3, 8, 5536, 5541, 8820, 1733, 147748, 37790⟩,
    ⟨763, 4, 8, 5248, 5253, 8509, 2000, 201645, 37341⟩,
    ⟨763, 5, 7, 5025, 5030, 8268, 2237, 256597, 36798⟩,
    ⟨763, 7, 7, 4689, 4694, 7905, 2646, 368894, 35729⟩,
    ⟨763, 8, 7, 4555, 4560, 7760, 2829, 426456, 35220⟩,
    ⟨763, 9, 6, 4438, 4443, 7634, 3000, 483722, 34702⟩,
    ⟨763, 25, 5, 3416, 3421, 6530, 5000, 1459005, 28745⟩,
    ⟨763, 40, 4, 2946, 2951, 6023, 6325, 2422391, 25164⟩,
    ⟨763, 55, 4, 2627, 2632, 5678, 7417, 3420392, 22563⟩,
    ⟨763, 70, 3, 2386, 2391, 5418, 8367, 4436009, 20510⟩,
    ⟨763, 85, 3, 2192, 2197, 5208, 9220, 5472607, 18848⟩,
    ⟨763, 100, 3, 2030, 2035, 5033, 10000, 6519223, 17447⟩,
    ⟨763, 115, 3, 1890, 1895, 4882, 10724, 7581835, 16242⟩,
    ⟨763, 130, 3, 1767, 1772, 4749, 11402, 8660351, 15198⟩,
    ⟨763, 145, 2, 1658, 1663, 4632, 12042, 9735269, 14266⟩,
    ⟨763, 160, 2, 1560, 1565, 4526, 12650, 10823885, 13449⟩,
    ⟨763, 175, 2, 1470, 1475, 4428, 13229, 11938342, 12724⟩,
    ⟨763, 190, 2, 1388, 1393, 4340, 13785, 13036528, 12051⟩,
    ⟨763, 205, 2, 1312, 1317, 4258, 14318, 14150575, 11446⟩,
    ⟨763, 220, 2, 1241, 1246, 4181, 14833, 15283216, 10895⟩,
    ⟨763, 235, 2, 1175, 1180, 4110, 15330, 16407774, 10383⟩,
    ⟨763, 250, 2, 1113, 1118, 4043, 15812, 17544759, 9915⟩,
    ⟨763, 265, 2, 1055, 1060, 3980, 16279, 18685639, 9485⟩,
    ⟨763, 280, 1, 1000, 1005, 3921, 16734, 19821263, 9078⟩,
    ⟨763, 295, 1, 948, 953, 3865, 17176, 20962922, 8702⟩,
    ⟨763, 310, 1, 898, 903, 3811, 17607, 22126041, 8350⟩,
    ⟨763, 325, 1, 851, 856, 3760, 18028, 23283740, 8024⟩,
    ⟨763, 340, 1, 806, 811, 3711, 18440, 24453057, 7719⟩,
    ⟨763, 355, 1, 763, 768, 3665, 18842, 25604171, 7427⟩,
    ⟨763, 370, 1, 721, 726, 3620, 19236, 26782676, 7150⟩,
    ⟨763, 385, 1, 682, 687, 3577, 19622, 27959450, 6900⟩,
    ⟨763, 400, 1, 643, 648, 3535, 20000, 29158756, 6654⟩,
    ⟨763, 415, 1, 606, 611, 3495, 20372, 30348748, 6422⟩,
    ⟨763, 430, 1, 571, 576, 3458, 20737, 31492684, 6200⟩,
    ⟨763, 445, 1, 537, 542, 3421, 21096, 32679738, 5995⟩,
    ⟨763, 460, 1, 504, 509, 3385, 21448, 33877642, 5800⟩,
    ⟨763, 475, 1, 471, 476, 3350, 21795, 35084354, 5606⟩,
    ⟨763, 490, 1, 440, 445, 3316, 22136, 36297732, 5430⟩,
    ⟨763, 505, 1, 410, 415, 3284, 22473, 37478044, 5258⟩,
    ⟨763, 520, 1, 381, 386, 3252, 22804, 38696736, 5099⟩,
    ⟨763, 535, 1, 352, 357, 3221, 23131, 39915123, 4940⟩,
    ⟨763, 550, 0, 325, 330, 3192, 23453, 41089609, 4792⟩,
    ⟨763, 565, 0, 298, 303, 3163, 23770, 42298654, 4649⟩,
    ⟨763, 580, 0, 272, 277, 3135, 24084, 43499753, 4512⟩,
    ⟨763, 595, 0, 246, 251, 3107, 24393, 44734959, 4380⟩,
    ⟨763, 610, 0, 221, 226, 3080, 24699, 45959256, 4254⟩,
    ⟨763, 625, 0, 197, 202, 3054, 25000, 47169867, 4134⟩,
    ⟨763, 640, 0, 173, 178, 3028, 25299, 48412366, 4018⟩,
    ⟨763, 655, 0, 150, 155, 3003, 25593, 49637930, 3907⟩,
    ⟨763, 670, 0, 127, 132, 2978, 25885, 50894521, 3800⟩,
    ⟨763, 685, 0, 105, 110, 2954, 26173, 52130765, 3698⟩,
    ⟨763, 700, 0, 84, 89, 2932, 26458, 53290350, 3598⟩,
    ⟨763, 715, 0, 62, 67, 2908, 26740, 54584790, 3500⟩,
    ⟨763, 730, 0, 42, 47, 2886, 27019, 55798962, 3412⟩,
    ⟨763, 745, 0, 21, 26, 2864, 27295, 57040142, 3318⟩,
    ⟨763, 760, 0, 1, 6, 2842, 27569, 58308931, 3233⟩,
    ⟨763, 763, 0, -2, 2, 2838, 27623, 58542634, 3222⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell17_rows_check : ∀ r ∈ target028Cell17Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell17Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 763)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell17RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell17Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨763, 763, 0, -2, 2, 2838, 27623, 58542634, 3222⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell17Weight (n : ℕ) : ℚ :=
  ((target028Cell17RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell17_select :
    ∀ n ∈ target028Cell17Prefix,
      1 ≤ n ∧
        target028Cell17RowFor n ∈ target028Cell17Rows ∧
        n ≤ (target028Cell17RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell17RowFor n).b) ∧ (target028Cell17RowFor n).cut = 763 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell17_sum_check :
    (70489 / 10000 : ℚ) <
      ∑ n ∈ target028Cell17Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell17Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell17_principal :
    (70489 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(763 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 763 n).re := by
  have hs : target028Cell17Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell17Prefix ⊆ Finset.Ioc 0 ⌊(763 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell17_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell17Prefix, 0 ≤ target028Cell17Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell17Prefix, (target028Cell17Weight n : ℝ) ≤ refinedScaledWeight 763 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell17_select n hn
    have hcheck := target028_cell17_rows_check (target028Cell17RowFor n) hm
    have hrow := (target028Cell17RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell17RowFor n).b ≤ 763 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 763 (target028Cell17RowFor n).b ≤ refinedScaledWeight 763 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 763) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell17Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 763) target028Cell17Prefix
      target028Cell17Weight hs ht hw0 hw
  have hr :
    ((70489 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell17Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell17Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell17_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
