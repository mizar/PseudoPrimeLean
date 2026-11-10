/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 29 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1626. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell29Rows : List Target028GeneralWeightRow :=
  [⟨1626, 2, 10, 6698, 6703, 10075, 1415, 42119, 25670⟩,
    ⟨1626, 3, 9, 6293, 6298, 9637, 1733, 65268, 26012⟩,
    ⟨1626, 4, 9, 6005, 6010, 9326, 2000, 89077, 26105⟩,
    ⟨1626, 5, 8, 5782, 5787, 9085, 2237, 113353, 26056⟩,
    ⟨1626, 7, 8, 5445, 5450, 8721, 2646, 163123, 25836⟩,
    ⟨1626, 8, 8, 5312, 5317, 8578, 2829, 188201, 25657⟩,
    ⟨1626, 9, 7, 5194, 5199, 8450, 3000, 213900, 25514⟩,
    ⟨1626, 42, 5, 3654, 3659, 6787, 6481, 1128348, 20806⟩,
    ⟨1626, 74, 4, 3087, 3092, 6175, 8603, 2080805, 18007⟩,
    ⟨1626, 106, 4, 2728, 2733, 5787, 10296, 3067169, 16032⟩,
    ⟨1626, 138, 4, 2464, 2469, 5502, 11748, 4078606, 14509⟩,
    ⟨1626, 170, 3, 2256, 2261, 5277, 13039, 5107731, 13288⟩,
    ⟨1626, 202, 3, 2083, 2088, 5091, 14213, 6151864, 12258⟩,
    ⟨1626, 234, 3, 1936, 1941, 4932, 15298, 7212064, 11393⟩,
    ⟨1626, 266, 3, 1808, 1813, 4794, 16310, 8279273, 10640⟩,
    ⟨1626, 298, 2, 1694, 1699, 4670, 17263, 9372269, 9990⟩,
    ⟨1626, 330, 2, 1592, 1597, 4560, 18166, 10462058, 9404⟩,
    ⟨1626, 362, 2, 1500, 1505, 4461, 19027, 11550806, 8877⟩,
    ⟨1626, 394, 2, 1415, 1420, 4369, 19850, 12663898, 8407⟩,
    ⟨1626, 426, 2, 1337, 1342, 4285, 20640, 13773621, 7977⟩,
    ⟨1626, 458, 2, 1265, 1270, 4207, 21401, 14890974, 7588⟩,
    ⟨1626, 490, 2, 1197, 1202, 4134, 22136, 16018675, 7226⟩,
    ⟨1626, 522, 2, 1134, 1139, 4066, 22848, 17145834, 6896⟩,
    ⟨1626, 554, 2, 1074, 1079, 4001, 23538, 18297332, 6591⟩,
    ⟨1626, 586, 1, 1018, 1023, 3940, 24208, 19448214, 6311⟩,
    ⟨1626, 618, 1, 965, 970, 3883, 24860, 20588965, 6047⟩,
    ⟨1626, 650, 1, 914, 919, 3828, 25496, 21753078, 5799⟩,
    ⟨1626, 682, 1, 866, 871, 3776, 26116, 22914165, 5570⟩,
    ⟨1626, 714, 1, 820, 825, 3726, 26721, 24088999, 5356⟩,
    ⟨1626, 746, 1, 777, 782, 3680, 27314, 25222974, 5152⟩,
    ⟨1626, 778, 1, 735, 740, 3635, 27893, 26383934, 4959⟩,
    ⟨1626, 810, 1, 694, 699, 3590, 28461, 27598330, 4781⟩,
    ⟨1626, 842, 1, 656, 661, 3549, 29018, 28753378, 4613⟩,
    ⟨1626, 874, 1, 618, 623, 3508, 29564, 29956768, 4450⟩,
    ⟨1626, 906, 1, 582, 587, 3469, 30100, 31148163, 4298⟩,
    ⟨1626, 938, 1, 548, 553, 3433, 30627, 32289925, 4151⟩,
    ⟨1626, 970, 1, 514, 519, 3396, 31145, 33507030, 4014⟩,
    ⟨1626, 1002, 1, 482, 487, 3361, 31655, 34700541, 3886⟩,
    ⟨1626, 1034, 1, 450, 455, 3327, 32156, 35900645, 3758⟩,
    ⟨1626, 1066, 1, 420, 425, 3294, 32650, 37105131, 3642⟩,
    ⟨1626, 1098, 1, 390, 395, 3262, 33137, 38311697, 3526⟩,
    ⟨1626, 1130, 1, 361, 366, 3231, 33616, 39517961, 3416⟩,
    ⟨1626, 1162, 0, 333, 338, 3201, 34089, 40721462, 3312⟩,
    ⟨1626, 1194, 0, 306, 311, 3171, 34555, 41961615, 3216⟩,
    ⟨1626, 1226, 0, 280, 285, 3143, 35015, 43153144, 3121⟩,
    ⟨1626, 1258, 0, 254, 259, 3115, 35469, 44378507, 3030⟩,
    ⟨1626, 1290, 0, 229, 234, 3088, 35917, 45593049, 2943⟩,
    ⟨1626, 1322, 0, 204, 209, 3061, 36360, 46840830, 2858⟩,
    ⟨1626, 1354, 0, 181, 186, 3036, 36797, 48026612, 2780⟩,
    ⟨1626, 1386, 0, 157, 162, 3010, 37230, 49291678, 2701⟩,
    ⟨1626, 1418, 0, 134, 139, 2986, 37657, 50488989, 2624⟩,
    ⟨1626, 1450, 0, 112, 117, 2962, 38079, 51715382, 2554⟩,
    ⟨1626, 1482, 0, 90, 95, 2938, 38497, 52971565, 2485⟩,
    ⟨1626, 1514, 0, 69, 74, 2915, 38911, 54204030, 2420⟩,
    ⟨1626, 1546, 0, 48, 53, 2893, 39320, 55409733, 2354⟩,
    ⟨1626, 1578, 0, 27, 32, 2870, 39725, 56698926, 2292⟩,
    ⟨1626, 1610, 0, 7, 12, 2848, 40125, 57960125, 2233⟩,
    ⟨1626, 1626, 0, -2, 2, 2838, 40324, 58542634, 2207⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell29_rows_check : ∀ r ∈ target028Cell29Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell29Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1626)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell29RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell29Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1626, 1626, 0, -2, 2, 2838, 40324, 58542634, 2207⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell29Weight (n : ℕ) : ℚ :=
  ((target028Cell29RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell29_select :
    ∀ n ∈ target028Cell29Prefix,
      1 ≤ n ∧
        target028Cell29RowFor n ∈ target028Cell29Rows ∧
        n ≤ (target028Cell29RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell29RowFor n).b) ∧ (target028Cell29RowFor n).cut = 1626 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell29_sum_check :
    (103561 / 10000 : ℚ) <
      ∑ n ∈ target028Cell29Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell29Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell29_principal :
    (103561 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1626 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1626 n).re := by
  have hs : target028Cell29Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell29Prefix ⊆ Finset.Ioc 0 ⌊(1626 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell29_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell29Prefix, 0 ≤ target028Cell29Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell29Prefix, (target028Cell29Weight n : ℝ) ≤ refinedScaledWeight 1626 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell29_select n hn
    have hcheck := target028_cell29_rows_check (target028Cell29RowFor n) hm
    have hrow := (target028Cell29RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell29RowFor n).b ≤ 1626 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1626 (target028Cell29RowFor n).b ≤ refinedScaledWeight 1626 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1626) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell29Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1626) target028Cell29Prefix
      target028EulerData2701 target028Cell29Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((103561 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell29Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell29Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell29_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell29_budget :
    target028MomentBudget 1626 (78225 / 1000) ≤ 4 * (103561 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1626 11 32 0 (73941 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1626 0 (340403 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1626 ≤ (73941 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1626 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (340403 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (20161 / 500 : ℝ) ≤ Real.sqrt 1626 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1626 ≤ (1613 / 40 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1626) (U := 78225 / 1000) (L := 73941 / 10000) (P :=
      340403 / 1000000000) (s := 20161 / 500) (t := 1613 / 40) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell29_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (76225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 78225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1626 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1626) (U := 78225 / 1000) (S := 103561 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell29_principal) target028_cell29_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
