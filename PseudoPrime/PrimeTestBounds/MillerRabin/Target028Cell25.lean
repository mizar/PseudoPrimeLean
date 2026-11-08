/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 25 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1303. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell25Rows : List Target028GeneralWeightRow :=
  [⟨1303, 2, 9, 6477, 6482, 9836, 1415, 53490, 28915⟩,
    ⟨1303, 3, 9, 6071, 6076, 9398, 1733, 82889, 29122⟩,
    ⟨1303, 4, 8, 5784, 5789, 9088, 2000, 113013, 29090⟩,
    ⟨1303, 5, 8, 5560, 5565, 8846, 2237, 143956, 28946⟩,
    ⟨1303, 7, 8, 5224, 5229, 8483, 2646, 206956, 28529⟩,
    ⟨1303, 8, 7, 5090, 5095, 8338, 2829, 239250, 28303⟩,
    ⟨1303, 9, 7, 4973, 4978, 8212, 3000, 271377, 28046⟩,
    ⟨1303, 36, 5, 3586, 3591, 6714, 6000, 1213799, 22895⟩,
    ⟨1303, 62, 4, 3043, 3048, 6127, 7875, 2183120, 19857⟩,
    ⟨1303, 88, 4, 2693, 2698, 5749, 9381, 3185965, 17687⟩,
    ⟨1303, 114, 4, 2434, 2439, 5470, 10678, 4211232, 16002⟩,
    ⟨1303, 140, 3, 2228, 2233, 5247, 11833, 5263284, 14660⟩,
    ⟨1303, 166, 3, 2058, 2063, 5064, 12885, 6320227, 13527⟩,
    ⟨1303, 192, 3, 1912, 1917, 4906, 13857, 7402037, 12573⟩,
    ⟨1303, 218, 3, 1785, 1790, 4769, 14765, 8488864, 11742⟩,
    ⟨1303, 244, 2, 1673, 1678, 4648, 15621, 9580744, 11014⟩,
    ⟨1303, 270, 2, 1572, 1577, 4539, 16432, 10684085, 10367⟩,
    ⟨1303, 296, 2, 1480, 1485, 4439, 17205, 11807740, 9795⟩,
    ⟨1303, 322, 2, 1395, 1400, 4347, 17945, 12945591, 9273⟩,
    ⟨1303, 348, 2, 1318, 1323, 4264, 18655, 14065926, 8799⟩,
    ⟨1303, 374, 2, 1246, 1251, 4187, 19340, 15191791, 8359⟩,
    ⟨1303, 400, 2, 1178, 1183, 4113, 20000, 16358624, 7966⟩,
    ⟨1303, 426, 2, 1115, 1120, 4045, 20640, 17509704, 7600⟩,
    ⟨1303, 452, 2, 1056, 1061, 3981, 21261, 18666963, 7265⟩,
    ⟨1303, 478, 1, 1000, 1005, 3921, 21864, 19821263, 6948⟩,
    ⟨1303, 504, 1, 947, 952, 3864, 22450, 20983895, 6655⟩,
    ⟨1303, 530, 1, 897, 902, 3810, 23022, 22148178, 6383⟩,
    ⟨1303, 556, 1, 849, 854, 3758, 23580, 23330354, 6130⟩,
    ⟨1303, 582, 1, 803, 808, 3708, 24125, 24526527, 5892⟩,
    ⟨1303, 608, 1, 760, 765, 3662, 24658, 25681099, 5667⟩,
    ⟨1303, 634, 1, 718, 723, 3616, 25180, 26890021, 5459⟩,
    ⟨1303, 660, 1, 678, 683, 3573, 25691, 28071512, 5259⟩,
    ⟨1303, 686, 1, 639, 644, 3531, 26192, 29275625, 5070⟩,
    ⟨1303, 712, 1, 602, 607, 3491, 26684, 30470386, 4892⟩,
    ⟨1303, 738, 1, 566, 571, 3452, 27167, 31682208, 4724⟩,
    ⟨1303, 764, 1, 531, 536, 3414, 27641, 32909299, 4564⟩,
    ⟨1303, 790, 1, 498, 503, 3379, 28107, 34081519, 4410⟩,
    ⟨1303, 816, 1, 466, 471, 3344, 28566, 35295492, 4268⟩,
    ⟨1303, 842, 1, 434, 439, 3310, 29018, 36516173, 4127⟩,
    ⟨1303, 868, 1, 404, 409, 3277, 29462, 37741311, 3999⟩,
    ⟨1303, 894, 1, 374, 379, 3245, 29900, 38968564, 3871⟩,
    ⟨1303, 920, 1, 346, 351, 3215, 30332, 40155333, 3752⟩,
    ⟨1303, 946, 0, 318, 323, 3184, 30758, 41419644, 3640⟩,
    ⟨1303, 972, 0, 291, 296, 3155, 31177, 42638400, 3530⟩,
    ⟨1303, 998, 0, 264, 269, 3126, 31592, 43893018, 3423⟩,
    ⟨1303, 1024, 0, 238, 243, 3098, 32000, 45139390, 3322⟩,
    ⟨1303, 1050, 0, 213, 218, 3071, 32404, 46374756, 3226⟩,
    ⟨1303, 1076, 0, 189, 194, 3045, 32803, 47596311, 3134⟩,
    ⟨1303, 1102, 0, 165, 170, 3019, 33197, 48850043, 3045⟩,
    ⟨1303, 1128, 0, 142, 147, 2994, 33586, 50086688, 2961⟩,
    ⟨1303, 1154, 0, 119, 124, 2969, 33971, 51354639, 2879⟩,
    ⟨1303, 1180, 0, 97, 102, 2946, 34352, 52549483, 2798⟩,
    ⟨1303, 1206, 0, 75, 80, 2922, 34728, 53825927, 2723⟩,
    ⟨1303, 1232, 0, 54, 59, 2899, 35100, 55078270, 2651⟩,
    ⟨1303, 1258, 0, 33, 38, 2877, 35469, 56303419, 2578⟩,
    ⟨1303, 1284, 0, 12, 17, 2854, 35833, 57613405, 2510⟩,
    ⟨1303, 1303, 0, -2, 2, 2838, 36098, 58542634, 2465⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell25_rows_check : ∀ r ∈ target028Cell25Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell25Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1303)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell25RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell25Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1303, 1303, 0, -2, 2, 2838, 36098, 58542634, 2465⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell25Weight (n : ℕ) : ℚ :=
  ((target028Cell25RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell25_select :
    ∀ n ∈ target028Cell25Prefix,
      1 ≤ n ∧
        target028Cell25RowFor n ∈ target028Cell25Rows ∧
        n ≤ (target028Cell25RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell25RowFor n).b) ∧ (target028Cell25RowFor n).cut = 1303 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell25_sum_check :
    (92631 / 10000 : ℚ) <
      ∑ n ∈ target028Cell25Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell25Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell25_principal :
    (92631 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1303 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1303 n).re := by
  have hs : target028Cell25Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell25Prefix ⊆ Finset.Ioc 0 ⌊(1303 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell25_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell25Prefix, 0 ≤ target028Cell25Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell25Prefix, (target028Cell25Weight n : ℝ) ≤ refinedScaledWeight 1303 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell25_select n hn
    have hcheck := target028_cell25_rows_check (target028Cell25RowFor n) hm
    have hrow := (target028Cell25RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell25RowFor n).b ≤ 1303 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1303 (target028Cell25RowFor n).b ≤ refinedScaledWeight 1303 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1303) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell25Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1303) target028Cell25Prefix
      target028EulerData2701 target028Cell25Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((92631 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell25Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell25Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell25_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell25_budget :
    target028MomentBudget 1303 (70225 / 1000) ≤ 4 * (92631 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1303 10 32 0 (71727 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1303 0 (432377 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1303 ≤ (71727 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1303 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (432377 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (4512 / 125 : ℝ) ≤ Real.sqrt 1303 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1303 ≤ (36099 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1303) (U := 70225 / 1000) (L := 71727 / 10000) (P :=
      432377 / 1000000000) (s := 4512 / 125) (t := 36099 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell25_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (68225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 70225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1303 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1303) (U := 70225 / 1000) (S := 92631 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell25_principal) target028_cell25_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
