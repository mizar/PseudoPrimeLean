/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 31 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1802. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell31Rows : List Target028GeneralWeightRow :=
  [⟨1802, 2, 10, 6801, 6806, 10186, 1415, 37694, 24271⟩,
    ⟨1802, 3, 9, 6396, 6401, 9749, 1733, 58352, 24630⟩,
    ⟨1802, 4, 9, 6108, 6113, 9438, 2000, 79639, 24765⟩,
    ⟨1802, 5, 8, 5885, 5890, 9197, 2237, 101342, 24757⟩,
    ⟨1802, 7, 8, 5548, 5553, 8833, 2646, 145840, 24611⟩,
    ⟨1802, 8, 8, 5415, 5420, 8689, 2829, 168428, 24490⟩,
    ⟨1802, 9, 8, 5297, 5302, 8562, 3000, 191236, 24353⟩,
    ⟨1802, 46, 5, 3666, 3671, 6800, 6783, 1113775, 19811⟩,
    ⟨1802, 82, 4, 3087, 3092, 6175, 9056, 2080805, 17106⟩,
    ⟨1802, 118, 4, 2723, 2728, 5782, 10863, 3082544, 15200⟩,
    ⟨1802, 154, 4, 2457, 2462, 5494, 12410, 4111365, 13750⟩,
    ⟨1802, 190, 3, 2247, 2252, 5268, 13785, 5153908, 12566⟩,
    ⟨1802, 226, 3, 2074, 2079, 5081, 15034, 6213692, 11594⟩,
    ⟨1802, 262, 3, 1926, 1931, 4921, 16187, 7291835, 10768⟩,
    ⟨1802, 298, 3, 1797, 1802, 4782, 17263, 8379223, 10048⟩,
    ⟨1802, 334, 2, 1683, 1688, 4659, 18276, 9475933, 9420⟩,
    ⟨1802, 370, 2, 1581, 1586, 4548, 19236, 10588359, 8871⟩,
    ⟨1802, 406, 2, 1488, 1493, 4448, 20150, 11701947, 8369⟩,
    ⟨1802, 442, 2, 1403, 1408, 4356, 21024, 12829603, 7922⟩,
    ⟨1802, 478, 2, 1325, 1330, 4272, 21864, 13953847, 7514⟩,
    ⟨1802, 514, 2, 1252, 1257, 4193, 22672, 15100914, 7143⟩,
    ⟨1802, 550, 2, 1184, 1189, 4120, 23453, 16244514, 6799⟩,
    ⟨1802, 586, 2, 1121, 1126, 4052, 24208, 17387564, 6487⟩,
    ⟨1802, 622, 2, 1061, 1066, 3987, 24940, 18555296, 6198⟩,
    ⟨1802, 658, 1, 1005, 1010, 3926, 25652, 19722404, 5933⟩,
    ⟨1802, 694, 1, 952, 957, 3869, 26344, 20879238, 5682⟩,
    ⟨1802, 730, 1, 901, 906, 3814, 27019, 22059763, 5448⟩,
    ⟨1802, 766, 1, 853, 858, 3762, 27677, 23237219, 5231⟩,
    ⟨1802, 802, 1, 807, 812, 3712, 28320, 24428617, 5028⟩,
    ⟨1802, 838, 1, 763, 768, 3665, 28949, 25604171, 4834⟩,
    ⟨1802, 874, 1, 721, 726, 3620, 29564, 26782676, 4652⟩,
    ⟨1802, 910, 1, 681, 686, 3576, 30167, 27987424, 4486⟩,
    ⟨1802, 946, 1, 642, 647, 3534, 30758, 29187930, 4324⟩,
    ⟨1802, 982, 1, 605, 610, 3494, 31337, 30379112, 4173⟩,
    ⟨1802, 1018, 1, 569, 574, 3455, 31907, 31587304, 4029⟩,
    ⟨1802, 1054, 1, 534, 539, 3418, 32466, 32777925, 3889⟩,
    ⟨1802, 1090, 1, 500, 505, 3381, 33016, 34013424, 3759⟩,
    ⟨1802, 1126, 1, 468, 473, 3346, 33556, 35224972, 3638⟩,
    ⟨1802, 1162, 1, 436, 441, 3312, 34089, 36443214, 3517⟩,
    ⟨1802, 1198, 1, 406, 411, 3279, 34613, 37665903, 3408⟩,
    ⟨1802, 1234, 1, 376, 381, 3247, 35129, 38890705, 3299⟩,
    ⟨1802, 1270, 1, 347, 352, 3216, 35638, 40115198, 3195⟩,
    ⟨1802, 1306, 0, 319, 324, 3185, 36139, 41378245, 3100⟩,
    ⟨1802, 1342, 0, 292, 297, 3156, 36634, 42595783, 3006⟩,
    ⟨1802, 1378, 0, 266, 271, 3128, 37122, 43805320, 2917⟩,
    ⟨1802, 1414, 0, 240, 245, 3100, 37604, 45049202, 2831⟩,
    ⟨1802, 1450, 0, 215, 220, 3073, 38079, 46282100, 2749⟩,
    ⟨1802, 1486, 0, 190, 195, 3046, 38549, 47548739, 2669⟩,
    ⟨1802, 1522, 0, 166, 171, 3020, 39013, 48801218, 2593⟩,
    ⟨1802, 1558, 0, 143, 148, 2995, 39472, 50036627, 2522⟩,
    ⟨1802, 1594, 0, 120, 125, 2970, 39925, 51303310, 2452⟩,
    ⟨1802, 1630, 0, 98, 103, 2947, 40374, 52496960, 2383⟩,
    ⟨1802, 1666, 0, 76, 81, 2923, 40817, 53772128, 2318⟩,
    ⟨1802, 1702, 0, 55, 60, 2900, 41256, 55023219, 2257⟩,
    ⟨1802, 1738, 0, 34, 39, 2878, 41690, 56247144, 2195⟩,
    ⟨1802, 1774, 0, 13, 18, 2855, 42119, 57555821, 2137⟩,
    ⟨1802, 1802, 0, -2, 2, 2838, 42450, 58542634, 2096⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell31_rows_check : ∀ r ∈ target028Cell31Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell31Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1802)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell31RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell31Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1802, 1802, 0, -2, 2, 2838, 42450, 58542634, 2096⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell31Weight (n : ℕ) : ℚ :=
  ((target028Cell31RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell31_select :
    ∀ n ∈ target028Cell31Prefix,
      1 ≤ n ∧
        target028Cell31RowFor n ∈ target028Cell31Rows ∧
        n ≤ (target028Cell31RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell31RowFor n).b) ∧ (target028Cell31RowFor n).cut = 1802 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell31_sum_check :
    (13569 / 1250 : ℚ) <
      ∑ n ∈ target028Cell31Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell31Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell31_principal :
    (13569 / 1250 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1802 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1802 n).re := by
  have hs : target028Cell31Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell31Prefix ⊆ Finset.Ioc 0 ⌊(1802 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell31_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell31Prefix, 0 ≤ target028Cell31Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell31Prefix, (target028Cell31Weight n : ℝ) ≤ refinedScaledWeight 1802 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell31_select n hn
    have hcheck := target028_cell31_rows_check (target028Cell31RowFor n) hm
    have hrow := (target028Cell31RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell31RowFor n).b ≤ 1802 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1802 (target028Cell31RowFor n).b ≤ refinedScaledWeight 1802 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1802) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell31Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1802) target028Cell31Prefix
      target028EulerData2701 target028Cell31Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((13569 / 1250 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell31Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell31Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell31_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell31_budget :
    target028MomentBudget 1802 (82225 / 1000) ≤ 4 * (13569 / 1250 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1802 11 32 0 (74969 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1802 0 (304641 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1802 ≤ (74969 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1802 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (304641 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (5306 / 125 : ℝ) ≤ Real.sqrt 1802 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1802 ≤ (42451 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1802) (U := 82225 / 1000) (L := 74969 / 10000) (P :=
      304641 / 1000000000) (s := 5306 / 125) (t := 42451 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell31_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (80225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 82225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1802 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1802) (U := 82225 / 1000) (S := 13569 / 1250) (by norm_num only) hU hcut
      (le_of_lt target028_cell31_principal) target028_cell31_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
