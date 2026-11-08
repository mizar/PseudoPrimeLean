/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 11 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 453. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell11Rows : List Target028GeneralWeightRow :=
  [⟨453, 2, 8, 5420, 5425, 8694, 1415, 167588, 48871⟩,
    ⟨453, 3, 7, 5015, 5020, 8257, 1733, 259436, 47712⟩,
    ⟨453, 4, 7, 4727, 4732, 7946, 2000, 354075, 46561⟩,
    ⟨453, 5, 7, 4504, 4509, 7705, 2237, 450568, 45412⟩,
    ⟨453, 7, 6, 4167, 4172, 7341, 2646, 648401, 43369⟩,
    ⟨453, 8, 6, 4034, 4039, 7198, 2829, 748080, 42393⟩,
    ⟨453, 9, 6, 3916, 3921, 7070, 3000, 850233, 41550⟩,
    ⟨453, 19, 5, 3169, 3174, 6263, 4359, 1905520, 34950⟩,
    ⟨453, 28, 4, 2781, 2786, 5844, 5292, 2897230, 30951⟩,
    ⟨453, 37, 4, 2502, 2507, 5543, 6083, 3914764, 27915⟩,
    ⟨453, 46, 3, 2285, 2290, 5309, 6783, 4946871, 25483⟩,
    ⟨453, 55, 3, 2106, 2111, 5115, 7417, 6005977, 23499⟩,
    ⟨453, 64, 3, 1955, 1960, 4952, 8000, 7069256, 21804⟩,
    ⟨453, 73, 3, 1823, 1828, 4810, 8545, 8147859, 20327⟩,
    ⟨453, 82, 2, 1707, 1712, 4684, 9056, 9241971, 19063⟩,
    ⟨453, 91, 2, 1603, 1608, 4572, 9540, 10337264, 17925⟩,
    ⟨453, 100, 2, 1508, 1513, 4470, 10000, 11447315, 16903⟩,
    ⟨453, 109, 2, 1422, 1427, 4377, 10441, 12562991, 15993⟩,
    ⟨453, 118, 2, 1343, 1348, 4291, 10863, 13691227, 15180⟩,
    ⟨453, 127, 2, 1269, 1274, 4211, 11270, 14831529, 14427⟩,
    ⟨453, 136, 2, 1201, 1206, 4138, 11662, 15954729, 13733⟩,
    ⟨453, 145, 2, 1137, 1142, 4069, 12042, 17094474, 13097⟩,
    ⟨453, 154, 2, 1076, 1081, 4003, 12410, 18260774, 12510⟩,
    ⟨453, 163, 1, 1020, 1025, 3942, 12768, 19409357, 11976⟩,
    ⟨453, 172, 1, 966, 971, 3884, 13115, 20568386, 11466⟩,
    ⟨453, 181, 1, 915, 920, 3829, 13454, 21731336, 10994⟩,
    ⟨453, 199, 1, 820, 825, 3726, 14107, 24088999, 10145⟩,
    ⟨453, 217, 1, 733, 738, 3633, 14731, 26436755, 9382⟩,
    ⟨453, 226, 1, 693, 698, 3589, 15034, 27625942, 9048⟩,
    ⟨453, 235, 1, 654, 659, 3547, 15330, 28810942, 8722⟩,
    ⟨453, 244, 1, 616, 621, 3506, 15621, 30016741, 8413⟩,
    ⟨453, 253, 1, 580, 585, 3467, 15906, 31210521, 8124⟩,
    ⟨453, 262, 1, 545, 550, 3429, 16187, 32419343, 7850⟩,
    ⟨453, 271, 1, 511, 516, 3393, 16463, 33607702, 7581⟩,
    ⟨453, 280, 1, 479, 484, 3358, 16734, 34804798, 7338⟩,
    ⟨453, 289, 1, 447, 452, 3324, 17000, 36008509, 7095⟩,
    ⟨453, 298, 1, 416, 421, 3290, 17263, 37253849, 6871⟩,
    ⟨453, 307, 1, 387, 392, 3259, 17522, 38426805, 6656⟩,
    ⟨453, 316, 1, 358, 363, 3228, 17777, 39636692, 6448⟩,
    ⟨453, 325, 0, 330, 335, 3197, 18028, 40884674, 6256⟩,
    ⟨453, 334, 0, 302, 307, 3167, 18276, 42129797, 6064⟩,
    ⟨453, 343, 0, 276, 281, 3139, 18521, 43326102, 5885⟩,
    ⟨453, 352, 0, 250, 255, 3111, 18762, 44556376, 5711⟩,
    ⟨453, 361, 0, 225, 230, 3084, 19000, 45775786, 5546⟩,
    ⟨453, 370, 0, 200, 205, 3057, 19236, 47028569, 5386⟩,
    ⟨453, 379, 0, 176, 181, 3031, 19468, 48267346, 5234⟩,
    ⟨453, 388, 0, 152, 157, 3005, 19698, 49538754, 5085⟩,
    ⟨453, 397, 0, 129, 134, 2980, 19925, 50792833, 4944⟩,
    ⟨453, 406, 0, 107, 112, 2956, 20150, 52026607, 4811⟩,
    ⟨453, 415, 0, 85, 90, 2933, 20372, 53237087, 4676⟩,
    ⟨453, 424, 0, 64, 69, 2910, 20592, 54475729, 4554⟩,
    ⟨453, 433, 0, 43, 48, 2887, 20809, 55743191, 4434⟩,
    ⟨453, 442, 0, 22, 27, 2865, 21024, 56983131, 4312⟩,
    ⟨453, 451, 0, 2, 7, 2843, 21237, 58250651, 4201⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell11_rows_check : ∀ r ∈ target028Cell11Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell11Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 453)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell11RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell11Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨453, 451, 0, 2, 7, 2843, 21237, 58250651, 4201⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell11Weight (n : ℕ) : ℚ :=
  ((target028Cell11RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell11_select :
    ∀ n ∈ target028Cell11Prefix,
      1 ≤ n ∧
        target028Cell11RowFor n ∈ target028Cell11Rows ∧
        n ≤ (target028Cell11RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell11RowFor n).b) ∧ (target028Cell11RowFor n).cut = 453 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell11_sum_check :
    (6783 / 1250 : ℚ) <
      ∑ n ∈ target028Cell11Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell11Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell11_principal :
    (6783 / 1250 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(453 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 453 n).re := by
  have hs : target028Cell11Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell11Prefix ⊆ Finset.Ioc 0 ⌊(453 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell11_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell11Prefix, 0 ≤ target028Cell11Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell11Prefix, (target028Cell11Weight n : ℝ) ≤ refinedScaledWeight 453 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell11_select n hn
    have hcheck := target028_cell11_rows_check (target028Cell11RowFor n) hm
    have hrow := (target028Cell11RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell11RowFor n).b ≤ 453 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 453 (target028Cell11RowFor n).b ≤ refinedScaledWeight 453 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 453) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell11Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 453) target028Cell11Prefix
      target028Cell11Weight hs ht hw0 hw
  have hr :
    ((6783 / 1250 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell11Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell11Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell11_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell11_budget :
    target028MomentBudget 453 (42225 / 1000) ≤ 4 * (6783 / 1250 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 453 9 32 0 (61161 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 453 0 (338341 / 250000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 453 ≤ (61161 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (453 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (338341 / 250000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (10641 / 500 : ℝ) ≤ Real.sqrt 453 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 453 ≤ (4257 / 200 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 453) (U := 42225 / 1000) (L := 61161 / 10000) (P :=
      338341 / 250000000) (s := 10641 / 500) (t := 4257 / 200) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell11_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (40225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 42225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (453 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 453) (U := 42225 / 1000) (S := 6783 / 1250) (by norm_num only) hU hcut
      (le_of_lt target028_cell11_principal) target028_cell11_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
