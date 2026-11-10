/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 40 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2701. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell40Rows : List Target028GeneralWeightRow :=
  [⟨2701, 2, 10, 7206, 7211, 10623, 1415, 24349, 19348⟩,
    ⟨2701, 3, 10, 6800, 6805, 10185, 1733, 37732, 19826⟩,
    ⟨2701, 4, 9, 6513, 6518, 9875, 2000, 51444, 20067⟩,
    ⟨2701, 5, 9, 6289, 6294, 9633, 2237, 65530, 20187⟩,
    ⟨2701, 7, 9, 5953, 5958, 9270, 2646, 94208, 20247⟩,
    ⟨2701, 8, 8, 5819, 5824, 9125, 2829, 108908, 20235⟩,
    ⟨2701, 9, 8, 5702, 5707, 8999, 3000, 123533, 20185⟩,
    ⟨2701, 64, 5, 3740, 3745, 6880, 8000, 1028144, 16439⟩,
    ⟨2701, 118, 5, 3128, 3133, 6219, 10863, 1991235, 14144⟩,
    ⟨2701, 172, 4, 2751, 2756, 5812, 13115, 2991441, 12541⟩,
    ⟨2701, 226, 4, 2478, 2483, 5517, 15034, 4017883, 11323⟩,
    ⟨2701, 280, 3, 2264, 2269, 5286, 16734, 5061967, 10345⟩,
    ⟨2701, 334, 3, 2088, 2093, 5096, 18276, 6121182, 9536⟩,
    ⟨2701, 388, 3, 1938, 1943, 4934, 19698, 7197655, 8850⟩,
    ⟨2701, 442, 3, 1808, 1813, 4794, 21024, 8279273, 8254⟩,
    ⟨2701, 496, 2, 1692, 1697, 4668, 22272, 9391032, 7741⟩,
    ⟨2701, 550, 2, 1589, 1594, 4557, 23453, 10493492, 7280⟩,
    ⟨2701, 604, 2, 1495, 1500, 4455, 24577, 11620319, 6872⟩,
    ⟨2701, 658, 2, 1410, 1415, 4364, 25652, 12727376, 6497⟩,
    ⟨2701, 712, 2, 1331, 1336, 4278, 26684, 13870375, 6166⟩,
    ⟨2701, 766, 2, 1258, 1263, 4200, 27677, 14995576, 5856⟩,
    ⟨2701, 820, 2, 1190, 1195, 4126, 28636, 16147339, 5579⟩,
    ⟨2701, 874, 2, 1126, 1131, 4057, 29564, 17300843, 5320⟩,
    ⟨2701, 928, 2, 1066, 1071, 3992, 30464, 18462751, 5083⟩,
    ⟨2701, 982, 1, 1009, 1014, 3931, 31337, 19624038, 4859⟩,
    ⟨2701, 1036, 1, 956, 961, 3873, 32187, 20795888, 4658⟩,
    ⟨2701, 1090, 1, 905, 910, 3818, 33016, 21971700, 4466⟩,
    ⟨2701, 1144, 1, 857, 862, 3766, 33824, 23144456, 4288⟩,
    ⟨2701, 1198, 1, 810, 815, 3716, 34613, 24331097, 4116⟩,
    ⟨2701, 1252, 1, 766, 771, 3668, 35384, 25527473, 3960⟩,
    ⟨2701, 1306, 1, 724, 729, 3623, 36139, 26702448, 3811⟩,
    ⟨2701, 1360, 1, 684, 689, 3580, 36879, 27875698, 3671⟩,
    ⟨2701, 1414, 1, 645, 650, 3537, 37604, 29100497, 3542⟩,
    ⟨2701, 1468, 1, 607, 612, 3496, 38315, 30318414, 3416⟩,
    ⟨2701, 1522, 1, 571, 576, 3458, 39013, 31492684, 3295⟩,
    ⟨2701, 1576, 1, 536, 541, 3420, 39699, 32712434, 3184⟩,
    ⟨2701, 1630, 1, 503, 508, 3384, 40374, 33911536, 3079⟩,
    ⟨2701, 1684, 1, 470, 475, 3348, 41037, 35154592, 2978⟩,
    ⟨2701, 1738, 1, 438, 443, 3314, 41690, 36370400, 2879⟩,
    ⟨2701, 1792, 1, 408, 413, 3282, 42333, 37553075, 2787⟩,
    ⟨2701, 1846, 1, 378, 383, 3249, 42966, 38813001, 2701⟩,
    ⟨2701, 1900, 1, 349, 354, 3218, 43589, 40035048, 2616⟩,
    ⟨2701, 1954, 0, 321, 326, 3188, 44205, 41254297, 2535⟩,
    ⟨2701, 2008, 0, 294, 299, 3158, 44811, 42510677, 2461⟩,
    ⟨2701, 2062, 0, 267, 272, 3129, 45410, 43761536, 2387⟩,
    ⟨2701, 2116, 0, 242, 247, 3102, 46000, 44959193, 2318⟩,
    ⟨2701, 2170, 0, 216, 221, 3074, 46584, 46235841, 2249⟩,
    ⟨2701, 2224, 0, 192, 197, 3048, 47160, 47453736, 2185⟩,
    ⟨2701, 2278, 0, 168, 173, 3022, 47729, 48703713, 2123⟩,
    ⟨2701, 2332, 0, 144, 149, 2996, 48291, 49986615, 2063⟩,
    ⟨2701, 2386, 0, 122, 127, 2973, 48847, 51149630, 2005⟩,
    ⟨2701, 2440, 0, 99, 104, 2948, 49397, 52444490, 1949⟩,
    ⟨2701, 2494, 0, 77, 82, 2924, 49940, 53718383, 1896⟩,
    ⟨2701, 2548, 0, 56, 61, 2901, 50478, 54968224, 1846⟩,
    ⟨2701, 2602, 0, 35, 40, 2879, 51010, 56190925, 1796⟩,
    ⟨2701, 2656, 0, 14, 19, 2856, 51537, 57498293, 1748⟩,
    ⟨2701, 2701, 0, -2, 2, 2838, 51972, 58542634, 1712⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell40_rows_check : ∀ r ∈ target028Cell40Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell40Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2701)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell40RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell40Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2701, 2701, 0, -2, 2, 2838, 51972, 58542634, 1712⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell40Weight (n : ℕ) : ℚ :=
  ((target028Cell40RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell40_select :
    ∀ n ∈ target028Cell40Prefix,
      1 ≤ n ∧
        target028Cell40RowFor n ∈ target028Cell40Rows ∧
        n ≤ (target028Cell40RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell40RowFor n).b) ∧ (target028Cell40RowFor n).cut = 2701 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell40_sum_check :
    (132809 / 10000 : ℚ) <
      ∑ n ∈ target028Cell40Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell40Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell40_principal :
    (132809 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2701 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2701 n).re := by
  have hs : target028Cell40Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell40Prefix ⊆ Finset.Ioc 0 ⌊(2701 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell40_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell40Prefix, 0 ≤ target028Cell40Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell40Prefix, (target028Cell40Weight n : ℝ) ≤ refinedScaledWeight 2701 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell40_select n hn
    have hcheck := target028_cell40_rows_check (target028Cell40RowFor n) hm
    have hrow := (target028Cell40RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell40RowFor n).b ≤ 2701 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2701 (target028Cell40RowFor n).b ≤ refinedScaledWeight 2701 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2701) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell40Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2701) target028Cell40Prefix
      target028EulerData2701 target028Cell40Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((132809 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell40Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell40Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell40_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell40_budget :
    target028MomentBudget 2701 (100000 / 1000) ≤ 4 * (132809 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2701 11 32 0 (9877 / 1250) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2701 0 (19677 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2701 ≤ (9877 / 1250 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2701 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (19677 / 100000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (5197 / 100 : ℝ) ≤ Real.sqrt 2701 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2701 ≤ (51973 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2701) (U := 100000 / 1000) (L := 9877 / 1250) (P :=
      19677 / 100000000) (s := 5197 / 100) (t := 51973 / 1000) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell40_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (98225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 100000 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2701 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2701) (U := 100000 / 1000) (S := 132809 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell40_principal) target028_cell40_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
