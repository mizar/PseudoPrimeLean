/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 24 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1228. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell24Rows : List Target028GeneralWeightRow :=
  [⟨1228, 2, 9, 6417, 6422, 9771, 1415, 57083, 29854⟩,
    ⟨1228, 3, 9, 6012, 6017, 9334, 1733, 88368, 30008⟩,
    ⟨1228, 4, 8, 5724, 5729, 9023, 2000, 120603, 29952⟩,
    ⟨1228, 5, 8, 5501, 5506, 8782, 2237, 153470, 29763⟩,
    ⟨1228, 7, 7, 5165, 5170, 8419, 2646, 220635, 29289⟩,
    ⟨1228, 8, 7, 5031, 5036, 8274, 2829, 255062, 29037⟩,
    ⟨1228, 9, 7, 4913, 4918, 8147, 3000, 289602, 28767⟩,
    ⟨1228, 34, 5, 3584, 3589, 6712, 5831, 1216229, 23567⟩,
    ⟨1228, 58, 4, 3050, 3055, 6135, 7616, 2165725, 20494⟩,
    ⟨1228, 82, 4, 2704, 2709, 5761, 9056, 3147962, 18291⟩,
    ⟨1228, 106, 4, 2447, 2452, 5484, 10296, 4152685, 16576⟩,
    ⟨1228, 130, 3, 2243, 2248, 5263, 11402, 5179742, 15206⟩,
    ⟨1228, 154, 3, 2074, 2079, 5081, 12410, 6213692, 14045⟩,
    ⟨1228, 178, 3, 1929, 1934, 4924, 13342, 7269992, 13068⟩,
    ⟨1228, 202, 3, 1802, 1807, 4787, 14213, 8337432, 12213⟩,
    ⟨1228, 226, 2, 1690, 1695, 4666, 15034, 9409833, 11464⟩,
    ⟨1228, 250, 2, 1589, 1594, 4557, 15812, 10493492, 10798⟩,
    ⟨1228, 274, 2, 1498, 1503, 4459, 16553, 11573931, 10200⟩,
    ⟨1228, 298, 2, 1414, 1419, 4368, 17263, 12676568, 9664⟩,
    ⟨1228, 322, 2, 1336, 1341, 4284, 17945, 13787402, 9172⟩,
    ⟨1228, 346, 2, 1264, 1269, 4206, 18602, 14905872, 8728⟩,
    ⟨1228, 370, 2, 1197, 1202, 4134, 19236, 16018675, 8315⟩,
    ⟨1228, 394, 2, 1134, 1139, 4066, 19850, 17145834, 7937⟩,
    ⟨1228, 418, 2, 1075, 1080, 4002, 20446, 18279044, 7590⟩,
    ⟨1228, 442, 1, 1019, 1024, 3941, 21024, 19428776, 7270⟩,
    ⟨1228, 466, 1, 966, 971, 3884, 21588, 20568386, 6966⟩,
    ⟨1228, 490, 1, 916, 921, 3830, 22136, 21709615, 6685⟩,
    ⟨1228, 514, 1, 868, 873, 3778, 22672, 22868382, 6422⟩,
    ⟨1228, 538, 1, 823, 828, 3730, 23195, 23992835, 6172⟩,
    ⟨1228, 562, 1, 779, 784, 3682, 23707, 25172579, 5942⟩,
    ⟨1228, 586, 1, 737, 742, 3637, 24208, 26331219, 5720⟩,
    ⟨1228, 610, 1, 697, 702, 3594, 24699, 27488157, 5513⟩,
    ⟨1228, 634, 1, 659, 664, 3553, 25180, 28638594, 5319⟩,
    ⟨1228, 658, 1, 621, 626, 3512, 25652, 29837180, 5132⟩,
    ⟨1228, 682, 1, 586, 591, 3474, 26116, 30992811, 4960⟩,
    ⟨1228, 706, 1, 551, 556, 3436, 26571, 32193200, 4793⟩,
    ⟨1228, 730, 1, 518, 523, 3400, 27019, 33373269, 4638⟩,
    ⟨1228, 754, 1, 485, 490, 3365, 27460, 34562016, 4483⟩,
    ⟨1228, 778, 1, 454, 459, 3331, 27893, 35757329, 4343⟩,
    ⟨1228, 802, 1, 424, 429, 3299, 28320, 36920068, 4206⟩,
    ⟨1228, 826, 1, 394, 399, 3266, 28741, 38158757, 4077⟩,
    ⟨1228, 850, 1, 365, 370, 3235, 29155, 39360204, 3950⟩,
    ⟨1228, 874, 0, 338, 343, 3206, 29564, 40518362, 3832⟩,
    ⟨1228, 898, 0, 310, 315, 3176, 29967, 41752330, 3715⟩,
    ⟨1228, 922, 0, 284, 289, 3148, 30365, 42937916, 3606⟩,
    ⟨1228, 946, 0, 258, 263, 3120, 30758, 44157168, 3501⟩,
    ⟨1228, 970, 0, 233, 238, 3093, 31145, 45365653, 3400⟩,
    ⟨1228, 994, 0, 209, 214, 3067, 31528, 46560627, 3305⟩,
    ⟨1228, 1018, 0, 185, 190, 3041, 31907, 47787078, 3212⟩,
    ⟨1228, 1042, 0, 162, 167, 3016, 32281, 48996814, 3124⟩,
    ⟨1228, 1066, 0, 139, 144, 2991, 32650, 50237174, 3039⟩,
    ⟨1228, 1090, 0, 117, 122, 2967, 33016, 51457451, 2958⟩,
    ⟨1228, 1114, 0, 95, 100, 2943, 33377, 52707369, 2878⟩,
    ⟨1228, 1138, 0, 74, 79, 2921, 33735, 53879780, 2800⟩,
    ⟨1228, 1162, 0, 53, 58, 2898, 34089, 55133376, 2727⟩,
    ⟨1228, 1186, 0, 32, 37, 2875, 34439, 56416139, 2656⟩,
    ⟨1228, 1210, 0, 12, 17, 2854, 34786, 57613405, 2585⟩,
    ⟨1228, 1228, 0, -2, 2, 2838, 35043, 58542634, 2539⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell24_rows_check : ∀ r ∈ target028Cell24Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell24Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1228)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell24RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell24Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1228, 1228, 0, -2, 2, 2838, 35043, 58542634, 2539⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell24Weight (n : ℕ) : ℚ :=
  ((target028Cell24RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell24_select :
    ∀ n ∈ target028Cell24Prefix,
      1 ≤ n ∧
        target028Cell24RowFor n ∈ target028Cell24Rows ∧
        n ≤ (target028Cell24RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell24RowFor n).b) ∧ (target028Cell24RowFor n).cut = 1228 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell24_sum_check :
    (89271 / 10000 : ℚ) <
      ∑ n ∈ target028Cell24Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell24Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell24_principal :
    (89271 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1228 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1228 n).re := by
  have hs : target028Cell24Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell24Prefix ⊆ Finset.Ioc 0 ⌊(1228 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell24_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell24Prefix, 0 ≤ target028Cell24Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell24Prefix, (target028Cell24Weight n : ℝ) ≤ refinedScaledWeight 1228 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell24_select n hn
    have hcheck := target028_cell24_rows_check (target028Cell24RowFor n) hm
    have hrow := (target028Cell24RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell24RowFor n).b ≤ 1228 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1228 (target028Cell24RowFor n).b ≤ refinedScaledWeight 1228 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1228) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell24Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1228) target028Cell24Prefix
      target028EulerData2701 target028Cell24Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((89271 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell24Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell24Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell24_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell24_budget :
    target028MomentBudget 1228 (68225 / 1000) ≤ 4 * (89271 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1228 10 32 0 (35567 / 5000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1228 0 (92193 / 200000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1228 ≤ (35567 / 5000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1228 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (92193 / 200000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (35041 / 1000 : ℝ) ≤ Real.sqrt 1228 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1228 ≤ (8761 / 250 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1228) (U := 68225 / 1000) (L := 35567 / 5000) (P :=
      92193 / 200000000) (s := 35041 / 1000) (t := 8761 / 250) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell24_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (66225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 68225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1228 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1228) (U := 68225 / 1000) (S := 89271 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell24_principal) target028_cell24_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
