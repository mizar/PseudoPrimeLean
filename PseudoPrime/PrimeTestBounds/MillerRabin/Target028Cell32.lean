/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 32 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1893. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell32Rows : List Target028GeneralWeightRow :=
  [⟨1893, 2, 10, 6850, 6855, 10239, 1415, 35748, 23622⟩,
    ⟨1893, 3, 9, 6445, 6450, 9802, 1733, 55340, 24000⟩,
    ⟨1893, 4, 9, 6157, 6162, 9490, 2000, 75604, 24177⟩,
    ⟨1893, 5, 9, 5934, 5939, 9250, 2237, 96111, 24163⟩,
    ⟨1893, 7, 8, 5598, 5603, 8887, 2646, 138173, 24039⟩,
    ⟨1893, 8, 8, 5464, 5469, 8742, 2829, 159734, 23942⟩,
    ⟨1893, 9, 8, 5346, 5351, 8615, 3000, 181364, 23819⟩,
    ⟨1893, 47, 5, 3693, 3698, 6829, 6856, 1081939, 19452⟩,
    ⟨1893, 84, 4, 3113, 3118, 6203, 9166, 2023351, 16812⟩,
    ⟨1893, 121, 4, 2748, 2753, 5809, 11000, 3000429, 14955⟩,
    ⟨1893, 158, 4, 2481, 2486, 5520, 12570, 4005847, 13542⟩,
    ⟨1893, 195, 3, 2270, 2275, 5292, 13965, 5031686, 12398⟩,
    ⟨1893, 232, 3, 2097, 2102, 5106, 15232, 6060275, 11436⟩,
    ⟨1893, 269, 3, 1949, 1954, 4946, 16402, 7111799, 10629⟩,
    ⟨1893, 306, 3, 1820, 1825, 4806, 17493, 8180516, 9936⟩,
    ⟨1893, 343, 2, 1706, 1711, 4683, 18521, 9251218, 9319⟩,
    ⟨1893, 380, 2, 1603, 1608, 4572, 19494, 10337264, 8772⟩,
    ⟨1893, 417, 2, 1510, 1515, 4472, 20421, 11424444, 8280⟩,
    ⟨1893, 454, 2, 1425, 1430, 4380, 21308, 12525358, 7842⟩,
    ⟨1893, 491, 2, 1347, 1352, 4296, 22159, 13622941, 7442⟩,
    ⟨1893, 528, 2, 1274, 1279, 4217, 22979, 14742806, 7078⟩,
    ⟨1893, 565, 2, 1207, 1212, 4144, 23770, 15859287, 6750⟩,
    ⟨1893, 602, 2, 1143, 1148, 4075, 24536, 16992214, 6440⟩,
    ⟨1893, 639, 2, 1084, 1089, 4012, 25279, 18097164, 6152⟩,
    ⟨1893, 676, 1, 1027, 1032, 3950, 26000, 19254701, 5890⟩,
    ⟨1893, 713, 1, 974, 979, 3893, 26703, 20384101, 5643⟩,
    ⟨1893, 750, 1, 923, 928, 3838, 27387, 21536631, 5413⟩,
    ⟨1893, 787, 1, 875, 880, 3786, 28054, 22686165, 5200⟩,
    ⟨1893, 824, 1, 829, 834, 3736, 28706, 23849309, 5000⟩,
    ⟨1893, 861, 1, 785, 790, 3689, 29343, 24996986, 4809⟩,
    ⟨1893, 898, 1, 743, 748, 3643, 29967, 26173704, 4634⟩,
    ⟨1893, 935, 1, 703, 708, 3600, 30578, 27323722, 4466⟩,
    ⟨1893, 972, 1, 664, 669, 3558, 31177, 28495759, 4307⟩,
    ⟨1893, 1009, 1, 627, 632, 3518, 31765, 29658693, 4158⟩,
    ⟨1893, 1046, 1, 591, 596, 3479, 32342, 30838233, 4016⟩,
    ⟨1893, 1083, 1, 556, 561, 3441, 32909, 32032636, 3881⟩,
    ⟨1893, 1120, 1, 522, 527, 3405, 33467, 33206820, 3750⟩,
    ⟨1893, 1157, 1, 490, 495, 3370, 34015, 34389637, 3630⟩,
    ⟨1893, 1194, 1, 458, 463, 3336, 34555, 35578989, 3511⟩,
    ⟨1893, 1231, 1, 428, 433, 3303, 35086, 36772683, 3403⟩,
    ⟨1893, 1268, 1, 398, 403, 3271, 35609, 37968439, 3296⟩,
    ⟨1893, 1305, 1, 369, 374, 3239, 36125, 39203078, 3196⟩,
    ⟨1893, 1342, 0, 342, 347, 3210, 36634, 40356613, 3101⟩,
    ⟨1893, 1379, 0, 314, 319, 3180, 37135, 41585655, 3006⟩,
    ⟨1893, 1416, 0, 288, 293, 3152, 37630, 42766508, 2918⟩,
    ⟨1893, 1453, 0, 262, 267, 3124, 38119, 43980892, 2833⟩,
    ⟨1893, 1490, 0, 237, 242, 3097, 38601, 45184552, 2752⟩,
    ⟨1893, 1527, 0, 212, 217, 3070, 39077, 46421154, 2673⟩,
    ⟨1893, 1564, 0, 188, 193, 3044, 39548, 47643932, 2598⟩,
    ⟨1893, 1601, 0, 165, 170, 3019, 40013, 48850043, 2527⟩,
    ⟨1893, 1638, 0, 142, 147, 2994, 40473, 50086688, 2457⟩,
    ⟨1893, 1675, 0, 120, 125, 2970, 40927, 51303310, 2392⟩,
    ⟨1893, 1712, 0, 98, 103, 2947, 41377, 52496960, 2325⟩,
    ⟨1893, 1749, 0, 77, 82, 2924, 41822, 53718383, 2265⟩,
    ⟨1893, 1786, 0, 56, 61, 2901, 42262, 54968224, 2205⟩,
    ⟨1893, 1823, 0, 35, 40, 2879, 42697, 56190925, 2145⟩,
    ⟨1893, 1860, 0, 15, 20, 2857, 43128, 57440824, 2091⟩,
    ⟨1893, 1893, 0, -2, 2, 2838, 43509, 58542634, 2045⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell32_rows_check : ∀ r ∈ target028Cell32Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell32Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1893)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell32RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell32Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1893, 1893, 0, -2, 2, 2838, 43509, 58542634, 2045⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell32Weight (n : ℕ) : ℚ :=
  ((target028Cell32RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell32_select :
    ∀ n ∈ target028Cell32Prefix,
      1 ≤ n ∧
        target028Cell32RowFor n ∈ target028Cell32Rows ∧
        n ≤ (target028Cell32RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell32RowFor n).b) ∧ (target028Cell32RowFor n).cut = 1893 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell32_sum_check :
    (55751 / 5000 : ℚ) <
      ∑ n ∈ target028Cell32Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell32Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell32_principal :
    (55751 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1893 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1893 n).re := by
  have hs : target028Cell32Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell32Prefix ⊆ Finset.Ioc 0 ⌊(1893 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell32_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell32Prefix, 0 ≤ target028Cell32Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell32Prefix, (target028Cell32Weight n : ℝ) ≤ refinedScaledWeight 1893 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell32_select n hn
    have hcheck := target028_cell32_rows_check (target028Cell32RowFor n) hm
    have hrow := (target028Cell32RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell32RowFor n).b ≤ 1893 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1893 (target028Cell32RowFor n).b ≤ refinedScaledWeight 1893 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1893) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell32Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1893) target028Cell32Prefix
      target028EulerData2701 target028Cell32Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((55751 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell32Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell32Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell32_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell32_budget :
    target028MomentBudget 1893 (84225 / 1000) ≤ 4 * (55751 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1893 11 32 0 (37731 / 5000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1893 0 (36107 / 125000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1893 ≤ (37731 / 5000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1893 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (36107 / 125000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (43507 / 1000 : ℝ) ≤ Real.sqrt 1893 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1893 ≤ (4351 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1893) (U := 84225 / 1000) (L := 37731 / 5000) (P :=
      36107 / 125000000) (s := 43507 / 1000) (t := 4351 / 100) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell32_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (82225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 84225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1893 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1893) (U := 84225 / 1000) (S := 55751 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell32_principal) target028_cell32_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
