/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 39 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2592. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell39Rows : List Target028GeneralWeightRow :=
  [⟨2592, 2, 10, 7165, 7170, 10579, 1415, 25444, 19800⟩,
    ⟨2592, 3, 10, 6759, 6764, 10141, 1733, 39429, 20271⟩,
    ⟨2592, 4, 9, 6471, 6476, 9830, 2000, 53812, 20513⟩,
    ⟨2592, 5, 9, 6248, 6253, 9589, 2237, 68477, 20614⟩,
    ⟨2592, 7, 9, 5912, 5917, 9226, 2646, 98446, 20657⟩,
    ⟨2592, 8, 8, 5778, 5783, 9081, 2829, 113807, 20636⟩,
    ⟨2592, 9, 8, 5660, 5665, 8954, 3000, 129219, 20587⟩,
    ⟨2592, 61, 5, 3747, 3752, 6888, 7811, 1019951, 16795⟩,
    ⟨2592, 112, 5, 3139, 3144, 6231, 10584, 1967483, 14481⟩,
    ⟨2592, 163, 4, 2764, 2769, 5826, 12768, 2949852, 12857⟩,
    ⟨2592, 214, 4, 2492, 2497, 5532, 14629, 3958065, 11622⟩,
    ⟨2592, 265, 3, 2278, 2283, 5301, 16279, 4986604, 10627⟩,
    ⟨2592, 316, 3, 2102, 2107, 5111, 17777, 6030049, 9802⟩,
    ⟨2592, 367, 3, 1952, 1957, 4949, 19158, 7090495, 9102⟩,
    ⟨2592, 418, 3, 1822, 1827, 4809, 20446, 8156011, 8494⟩,
    ⟨2592, 469, 2, 1707, 1712, 4684, 21657, 9241971, 7971⟩,
    ⟨2592, 520, 2, 1604, 1609, 4573, 22804, 10326932, 7500⟩,
    ⟨2592, 571, 2, 1510, 1515, 4472, 23896, 11424444, 7076⟩,
    ⟨2592, 622, 2, 1425, 1430, 4380, 24940, 12525358, 6700⟩,
    ⟨2592, 673, 2, 1346, 1351, 4295, 25943, 13636571, 6355⟩,
    ⟨2592, 724, 2, 1273, 1278, 4216, 26908, 14757556, 6043⟩,
    ⟨2592, 775, 2, 1205, 1210, 4142, 27839, 15891037, 5760⟩,
    ⟨2592, 826, 2, 1141, 1146, 4073, 28741, 17026233, 5494⟩,
    ⟨2592, 877, 2, 1081, 1086, 4008, 29615, 18169698, 5251⟩,
    ⟨2592, 928, 1, 1025, 1030, 3948, 30464, 19293249, 5023⟩,
    ⟨2592, 979, 1, 971, 976, 3890, 31289, 20445346, 4811⟩,
    ⟨2592, 1030, 1, 920, 925, 3834, 32094, 21622950, 4618⟩,
    ⟨2592, 1081, 1, 872, 877, 3783, 32879, 22754325, 4431⟩,
    ⟨2592, 1132, 1, 826, 831, 3733, 33646, 23920965, 4260⟩,
    ⟨2592, 1183, 1, 782, 787, 3685, 34395, 25097174, 4101⟩,
    ⟨2592, 1234, 1, 740, 745, 3640, 35129, 26252343, 3947⟩,
    ⟨2592, 1285, 1, 699, 704, 3596, 35847, 27433236, 3802⟩,
    ⟨2592, 1336, 1, 660, 665, 3554, 36552, 28609970, 3666⟩,
    ⟨2592, 1387, 1, 623, 628, 3514, 37243, 29777565, 3538⟩,
    ⟨2592, 1438, 1, 587, 592, 3475, 37921, 30961833, 3417⟩,
    ⟨2592, 1489, 1, 552, 557, 3437, 38588, 32161023, 3302⟩,
    ⟨2592, 1540, 1, 518, 523, 3400, 39243, 33373269, 3193⟩,
    ⟨2592, 1591, 1, 486, 491, 3366, 39888, 34527471, 3088⟩,
    ⟨2592, 1642, 1, 454, 459, 3331, 40522, 35757329, 2989⟩,
    ⟨2592, 1693, 1, 423, 428, 3298, 41147, 36957007, 2893⟩,
    ⟨2592, 1744, 1, 394, 399, 3266, 41762, 38158757, 2805⟩,
    ⟨2592, 1795, 1, 365, 370, 3235, 42368, 39360204, 2718⟩,
    ⟨2592, 1846, 0, 337, 342, 3205, 42966, 40558901, 2635⟩,
    ⟨2592, 1897, 0, 310, 315, 3176, 43555, 41752330, 2556⟩,
    ⟨2592, 1948, 0, 283, 288, 3147, 44137, 42980876, 2479⟩,
    ⟨2592, 1999, 0, 257, 262, 3118, 44711, 44245571, 2409⟩,
    ⟨2592, 2050, 0, 232, 237, 3091, 45277, 45456475, 2339⟩,
    ⟨2592, 2101, 0, 208, 213, 3066, 45837, 46607211, 2271⟩,
    ⟨2592, 2152, 0, 184, 189, 3040, 46390, 47834889, 2208⟩,
    ⟨2592, 2203, 0, 160, 165, 3014, 46937, 49094905, 2145⟩,
    ⟨2592, 2254, 0, 137, 142, 2989, 47477, 50337749, 2086⟩,
    ⟨2592, 2305, 0, 115, 120, 2965, 48011, 51560469, 2030⟩,
    ⟨2592, 2356, 0, 93, 98, 2941, 48539, 52812889, 1976⟩,
    ⟨2592, 2407, 0, 72, 77, 2919, 49062, 53987647, 1922⟩,
    ⟨2592, 2458, 0, 51, 56, 2896, 49579, 55243753, 1872⟩,
    ⟨2592, 2509, 0, 30, 35, 2873, 50090, 56529084, 1822⟩,
    ⟨2592, 2560, 0, 10, 15, 2852, 50597, 57728747, 1774⟩,
    ⟨2592, 2592, 0, -2, 2, 2838, 50912, 58542634, 1748⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell39_rows_check : ∀ r ∈ target028Cell39Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell39Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2592)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell39RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell39Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2592, 2592, 0, -2, 2, 2838, 50912, 58542634, 1748⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell39Weight (n : ℕ) : ℚ :=
  ((target028Cell39RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell39_select :
    ∀ n ∈ target028Cell39Prefix,
      1 ≤ n ∧
        target028Cell39RowFor n ∈ target028Cell39Rows ∧
        n ≤ (target028Cell39RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell39RowFor n).b) ∧ (target028Cell39RowFor n).cut = 2592 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell39_sum_check :
    (651 / 50 : ℚ) <
      ∑ n ∈ target028Cell39Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell39Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell39_principal :
    (651 / 50 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2592 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2592 n).re := by
  have hs : target028Cell39Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell39Prefix ⊆ Finset.Ioc 0 ⌊(2592 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell39_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell39Prefix, 0 ≤ target028Cell39Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell39Prefix, (target028Cell39Weight n : ℝ) ≤ refinedScaledWeight 2592 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell39_select n hn
    have hcheck := target028_cell39_rows_check (target028Cell39RowFor n) hm
    have hrow := (target028Cell39RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell39RowFor n).b ≤ 2592 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2592 (target028Cell39RowFor n).b ≤ refinedScaledWeight 2592 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2592) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell39Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2592) target028Cell39Prefix
      target028EulerData2701 target028Cell39Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((651 / 50 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell39Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell39Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell39_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell39_budget :
    target028MomentBudget 2592 (98225 / 1000) ≤ 4 * (651 / 50 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2592 11 32 0 (19651 / 2500) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2592 0 (205721 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2592 ≤ (19651 / 2500 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2592 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (205721 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (5091 / 100 : ℝ) ≤ Real.sqrt 2592 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2592 ≤ (50913 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2592) (U := 98225 / 1000) (L := 19651 / 2500) (P :=
      205721 / 1000000000) (s := 5091 / 100) (t := 50913 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell39_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (96225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 98225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2592 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2592) (U := 98225 / 1000) (S := 651 / 50) (by norm_num only) hU hcut
      (le_of_lt target028_cell39_principal) target028_cell39_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
