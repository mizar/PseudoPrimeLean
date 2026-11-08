/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 38 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2485. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell38Rows : List Target028GeneralWeightRow :=
  [⟨2485, 2, 10, 7122, 7127, 10533, 1415, 26642, 20281⟩,
    ⟨2485, 3, 10, 6717, 6722, 10095, 1733, 41285, 20755⟩,
    ⟨2485, 4, 9, 6429, 6434, 9784, 2000, 56345, 20987⟩,
    ⟨2485, 5, 9, 6206, 6211, 9543, 2237, 71701, 21078⟩,
    ⟨2485, 7, 8, 5870, 5875, 9180, 2646, 103080, 21102⟩,
    ⟨2485, 8, 8, 5736, 5741, 9036, 2829, 119046, 21052⟩,
    ⟨2485, 9, 8, 5618, 5623, 8908, 3000, 135302, 21015⟩,
    ⟨2485, 59, 5, 3738, 3743, 6878, 7682, 1030202, 17127⟩,
    ⟨2485, 108, 5, 3133, 3138, 6225, 10393, 1979323, 14759⟩,
    ⟨2485, 157, 4, 2759, 2764, 5821, 12530, 2964639, 13106⟩,
    ⟨2485, 206, 4, 2488, 2493, 5528, 14353, 3973929, 11846⟩,
    ⟨2485, 255, 3, 2274, 2279, 5297, 15969, 5006591, 10832⟩,
    ⟨2485, 304, 3, 2099, 2104, 5108, 17436, 6048167, 9992⟩,
    ⟨2485, 353, 3, 1949, 1954, 4946, 18789, 7111799, 9278⟩,
    ⟨2485, 402, 3, 1819, 1824, 4805, 20050, 8188701, 8667⟩,
    ⟨2485, 451, 2, 1704, 1709, 4681, 21237, 9269739, 8125⟩,
    ⟨2485, 500, 2, 1601, 1606, 4570, 22361, 10357959, 7644⟩,
    ⟨2485, 549, 2, 1507, 1512, 4468, 23431, 11470233, 7219⟩,
    ⟨2485, 598, 2, 1422, 1427, 4377, 24455, 12562991, 6828⟩,
    ⟨2485, 647, 2, 1343, 1348, 4291, 25437, 13691227, 6482⟩,
    ⟨2485, 696, 2, 1270, 1275, 4212, 26382, 14816705, 6164⟩,
    ⟨2485, 745, 2, 1202, 1207, 4139, 27295, 15938782, 5869⟩,
    ⟨2485, 794, 2, 1138, 1143, 4070, 28179, 17077388, 5598⟩,
    ⟨2485, 843, 2, 1079, 1084, 4006, 29035, 18206074, 5352⟩,
    ⟨2485, 892, 1, 1022, 1027, 3945, 29867, 19351216, 5118⟩,
    ⟨2485, 941, 1, 969, 974, 3887, 30676, 20506774, 4908⟩,
    ⟨2485, 990, 1, 918, 923, 3832, 31465, 21666239, 4707⟩,
    ⟨2485, 1039, 1, 870, 875, 3781, 32234, 22799880, 4516⟩,
    ⟨2485, 1088, 1, 823, 828, 3730, 32985, 23992835, 4340⟩,
    ⟨2485, 1137, 1, 779, 784, 3682, 33720, 25172579, 4177⟩,
    ⟨2485, 1186, 1, 737, 742, 3637, 34439, 26331219, 4021⟩,
    ⟨2485, 1235, 1, 697, 702, 3594, 35143, 27488157, 3874⟩,
    ⟨2485, 1284, 1, 658, 663, 3552, 35833, 28667247, 3735⟩,
    ⟨2485, 1333, 1, 620, 625, 3510, 36511, 29896914, 3607⟩,
    ⟨2485, 1382, 1, 584, 589, 3472, 37176, 31054858, 3480⟩,
    ⟨2485, 1431, 1, 549, 554, 3434, 37829, 32257651, 3363⟩,
    ⟨2485, 1480, 1, 516, 521, 3398, 38471, 33440083, 3253⟩,
    ⟨2485, 1529, 1, 483, 488, 3363, 39103, 34631209, 3144⟩,
    ⟨2485, 1578, 1, 452, 457, 3329, 39725, 35828916, 3046⟩,
    ⟨2485, 1627, 1, 421, 426, 3296, 40337, 37030995, 2947⟩,
    ⟨2485, 1676, 1, 391, 396, 3263, 40939, 38273405, 2856⟩,
    ⟨2485, 1725, 1, 363, 368, 3233, 41534, 39439004, 2769⟩,
    ⟨2485, 1774, 0, 335, 340, 3203, 42119, 40640100, 2684⟩,
    ⟨2485, 1823, 0, 307, 312, 3172, 42697, 41919674, 2604⟩,
    ⟨2485, 1872, 0, 281, 286, 3144, 43267, 43110012, 2528⟩,
    ⟨2485, 1921, 0, 255, 260, 3116, 43830, 44334150, 2453⟩,
    ⟨2485, 1970, 0, 230, 235, 3089, 44385, 45547479, 2383⟩,
    ⟨2485, 2019, 0, 205, 210, 3062, 44934, 46794013, 2314⟩,
    ⟨2485, 2068, 0, 181, 186, 3036, 45476, 48026612, 2249⟩,
    ⟨2485, 2117, 0, 158, 163, 3012, 46011, 49193193, 2185⟩,
    ⟨2485, 2166, 0, 135, 140, 2987, 46541, 50438525, 2125⟩,
    ⟨2485, 2215, 0, 113, 118, 2963, 47064, 51663693, 2068⟩,
    ⟨2485, 2264, 0, 91, 96, 2939, 47582, 52918620, 2012⟩,
    ⟨2485, 2313, 0, 69, 74, 2915, 48094, 54204030, 1958⟩,
    ⟨2485, 2362, 0, 48, 53, 2893, 48601, 55409733, 1904⟩,
    ⟨2485, 2411, 0, 28, 33, 2871, 49102, 56642255, 1856⟩,
    ⟨2485, 2460, 0, 8, 13, 2850, 49599, 57844320, 1807⟩,
    ⟨2485, 2485, 0, -2, 2, 2838, 49850, 58542634, 1785⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell38_rows_check : ∀ r ∈ target028Cell38Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell38Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2485)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell38RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell38Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2485, 2485, 0, -2, 2, 2838, 49850, 58542634, 1785⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell38Weight (n : ℕ) : ℚ :=
  ((target028Cell38RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell38_select :
    ∀ n ∈ target028Cell38Prefix,
      1 ≤ n ∧
        target028Cell38RowFor n ∈ target028Cell38Rows ∧
        n ≤ (target028Cell38RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell38RowFor n).b) ∧ (target028Cell38RowFor n).cut = 2485 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell38_sum_check :
    (127931 / 10000 : ℚ) <
      ∑ n ∈ target028Cell38Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell38Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell38_principal :
    (127931 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2485 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2485 n).re := by
  have hs : target028Cell38Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell38Prefix ⊆ Finset.Ioc 0 ⌊(2485 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell38_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell38Prefix, 0 ≤ target028Cell38Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell38Prefix, (target028Cell38Weight n : ℝ) ≤ refinedScaledWeight 2485 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell38_select n hn
    have hcheck := target028_cell38_rows_check (target028Cell38RowFor n) hm
    have hrow := (target028Cell38RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell38RowFor n).b ≤ 2485 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2485 (target028Cell38RowFor n).b ≤ refinedScaledWeight 2485 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2485) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell38Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2485) target028Cell38Prefix
      target028EulerData2701 target028Cell38Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((127931 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell38Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell38Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell38_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell38_budget :
    target028MomentBudget 2485 (96225 / 1000) ≤ 4 * (127931 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2485 11 32 0 (78183 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2485 0 (26913 / 125000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2485 ≤ (78183 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2485 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (26913 / 125000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (6231 / 125 : ℝ) ≤ Real.sqrt 2485 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2485 ≤ (49851 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2485) (U := 96225 / 1000) (L := 78183 / 10000) (P :=
      26913 / 125000000) (s := 6231 / 125) (t := 49851 / 1000) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell38_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (94225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 96225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2485 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2485) (U := 96225 / 1000) (S := 127931 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell38_principal) target028_cell38_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
