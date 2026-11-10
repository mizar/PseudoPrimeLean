/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 14 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 598. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell14Rows : List Target028GeneralWeightRow :=
  [⟨598, 2, 8, 5698, 5703, 8995, 1415, 124028, 42864⟩,
    ⟨598, 3, 8, 5292, 5297, 8556, 1733, 192387, 42278⟩,
    ⟨598, 4, 7, 5005, 5010, 8246, 2000, 262305, 41527⟩,
    ⟨598, 5, 7, 4782, 4787, 8005, 2237, 333789, 40733⟩,
    ⟨598, 7, 6, 4445, 4450, 7641, 2646, 480347, 39264⟩,
    ⟨598, 8, 6, 4312, 4317, 7498, 2829, 554191, 38532⟩,
    ⟨598, 9, 6, 4194, 4199, 7370, 3000, 629868, 37902⟩,
    ⟨598, 21, 5, 3347, 3352, 6456, 4583, 1571067, 31884⟩,
    ⟨598, 32, 4, 2925, 2930, 6000, 5657, 2478752, 28252⟩,
    ⟨598, 43, 4, 2630, 2635, 5681, 6558, 3410146, 25515⟩,
    ⟨598, 54, 3, 2402, 2407, 5435, 7349, 4361235, 23327⟩,
    ⟨598, 65, 3, 2217, 2222, 5235, 8063, 5326824, 21529⟩,
    ⟨598, 76, 3, 2060, 2065, 5066, 8718, 6307600, 19995⟩,
    ⟨598, 87, 3, 1925, 1930, 4920, 9328, 7299130, 18684⟩,
    ⟨598, 98, 3, 1806, 1811, 4791, 9900, 8304149, 17543⟩,
    ⟨598, 109, 2, 1700, 1705, 4677, 10441, 9306892, 16516⟩,
    ⟨598, 120, 2, 1604, 1609, 4573, 10955, 10326932, 15612⟩,
    ⟨598, 131, 2, 1516, 1521, 4478, 11446, 11356102, 14792⟩,
    ⟨598, 142, 2, 1435, 1440, 4391, 11917, 12388334, 14041⟩,
    ⟨598, 153, 2, 1361, 1366, 4311, 12370, 13420122, 13366⟩,
    ⟨598, 164, 2, 1291, 1296, 4235, 12807, 14479810, 12748⟩,
    ⟨598, 175, 2, 1226, 1231, 4165, 13229, 15529714, 12174⟩,
    ⟨598, 186, 2, 1165, 1170, 4099, 13639, 16589256, 11646⟩,
    ⟨598, 197, 2, 1108, 1113, 4038, 14036, 17632702, 11150⟩,
    ⟨598, 208, 2, 1054, 1059, 3979, 14423, 18704334, 10702⟩,
    ⟨598, 219, 1, 1002, 1007, 3923, 14799, 19781660, 10273⟩,
    ⟨598, 230, 1, 953, 958, 3870, 15166, 20858369, 9875⟩,
    ⟨598, 241, 1, 906, 911, 3819, 15525, 21949739, 9502⟩,
    ⟨598, 252, 1, 862, 867, 3772, 15875, 23006005, 9147⟩,
    ⟨598, 263, 1, 819, 824, 3725, 16218, 24113100, 8820⟩,
    ⟨598, 274, 1, 778, 783, 3681, 16553, 25197764, 8506⟩,
    ⟨598, 285, 1, 739, 744, 3639, 16882, 26278609, 8210⟩,
    ⟨598, 296, 1, 701, 706, 3598, 17205, 27378424, 7930⟩,
    ⟨598, 307, 1, 664, 669, 3558, 17522, 28495759, 7663⟩,
    ⟨598, 318, 1, 629, 634, 3520, 17833, 29599435, 7414⟩,
    ⟨598, 340, 1, 562, 567, 3448, 18440, 31809191, 6944⟩,
    ⟨598, 351, 1, 530, 535, 3413, 18735, 32942225, 6730⟩,
    ⟨598, 362, 1, 499, 504, 3380, 19027, 34047454, 6519⟩,
    ⟨598, 373, 1, 470, 475, 3348, 19314, 35154592, 6329⟩,
    ⟨598, 384, 1, 440, 445, 3316, 19596, 36297732, 6134⟩,
    ⟨598, 395, 1, 412, 417, 3286, 19875, 37403163, 5953⟩,
    ⟨598, 406, 1, 385, 390, 3257, 20150, 38503736, 5780⟩,
    ⟨598, 417, 1, 358, 363, 3228, 20421, 39636692, 5613⟩,
    ⟨598, 428, 0, 332, 337, 3199, 20689, 40802986, 5459⟩,
    ⟨598, 439, 0, 307, 312, 3172, 20953, 41919674, 5307⟩,
    ⟨598, 450, 0, 282, 287, 3145, 21214, 43066923, 5160⟩,
    ⟨598, 461, 0, 258, 263, 3120, 21471, 44157168, 5015⟩,
    ⟨598, 472, 0, 234, 239, 3094, 21726, 45320310, 4878⟩,
    ⟨598, 483, 0, 211, 216, 3069, 21978, 46467599, 4749⟩,
    ⟨598, 494, 0, 189, 194, 3045, 22227, 47596311, 4626⟩,
    ⟨598, 505, 0, 167, 172, 3021, 22473, 48752441, 4506⟩,
    ⟨598, 516, 0, 145, 150, 2997, 22716, 49936653, 4389⟩,
    ⟨598, 527, 0, 124, 129, 2975, 22957, 51047433, 4274⟩,
    ⟨598, 538, 0, 103, 108, 2952, 23195, 52235131, 4166⟩,
    ⟨598, 549, 0, 83, 88, 2931, 23431, 53343667, 4059⟩,
    ⟨598, 560, 0, 63, 68, 2909, 23665, 54530232, 3959⟩,
    ⟨598, 571, 0, 44, 49, 2888, 23896, 55687476, 3864⟩,
    ⟨598, 582, 0, 25, 30, 2868, 24125, 56812437, 3768⟩,
    ⟨598, 593, 0, 6, 11, 2847, 24352, 58018114, 3677⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell14_rows_check : ∀ r ∈ target028Cell14Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell14Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 598)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell14RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell14Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨598, 593, 0, 6, 11, 2847, 24352, 58018114, 3677⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell14Weight (n : ℕ) : ℚ :=
  ((target028Cell14RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell14_select :
    ∀ n ∈ target028Cell14Prefix,
      1 ≤ n ∧
        target028Cell14RowFor n ∈ target028Cell14Rows ∧
        n ≤ (target028Cell14RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell14RowFor n).b) ∧ (target028Cell14RowFor n).cut = 598 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell14_sum_check :
    (62349 / 10000 : ℚ) <
      ∑ n ∈ target028Cell14Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell14Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell14_principal :
    (62349 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(598 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 598 n).re := by
  have hs : target028Cell14Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell14Prefix ⊆ Finset.Ioc 0 ⌊(598 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell14_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell14Prefix, 0 ≤ target028Cell14Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell14Prefix, (target028Cell14Weight n : ℝ) ≤ refinedScaledWeight 598 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell14_select n hn
    have hcheck := target028_cell14_rows_check (target028Cell14RowFor n) hm
    have hrow := (target028Cell14RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell14RowFor n).b ≤ 598 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 598 (target028Cell14RowFor n).b ≤ refinedScaledWeight 598 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 598) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell14Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 598) target028Cell14Prefix
      target028Cell14Weight hs ht hw0 hw
  have hr :
    ((62349 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell14Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell14Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell14_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell14_budget :
    target028MomentBudget 598 (48225 / 1000) ≤ 4 * (62349 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 598 9 32 0 (31969 / 5000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 598 0 (1002683 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 598 ≤ (31969 / 5000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (598 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (1002683 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (24453 / 1000 : ℝ) ≤ Real.sqrt 598 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 598 ≤ (3057 / 125 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 598) (U := 48225 / 1000) (L := 31969 / 5000) (P :=
      1002683 / 1000000000) (s := 24453 / 1000) (t := 3057 / 125) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell14_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (46225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 48225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (598 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 598) (U := 48225 / 1000) (S := 62349 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell14_principal) target028_cell14_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
