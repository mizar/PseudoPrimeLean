/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 33 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1986. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell33Rows : List Target028GeneralWeightRow :=
  [⟨1986, 2, 10, 6898, 6903, 10291, 1415, 33937, 22999⟩,
    ⟨1986, 3, 9, 6493, 6498, 9853, 1733, 52589, 23417⟩,
    ⟨1986, 4, 9, 6205, 6210, 9542, 2000, 71773, 23586⟩,
    ⟨1986, 5, 9, 5982, 5987, 9301, 2237, 91332, 23613⟩,
    ⟨1986, 7, 8, 5645, 5650, 8938, 2646, 131303, 23504⟩,
    ⟨1986, 8, 8, 5512, 5517, 8794, 2829, 151640, 23412⟩,
    ⟨1986, 9, 8, 5394, 5399, 8666, 3000, 172347, 23324⟩,
    ⟨1986, 49, 5, 3700, 3705, 6837, 7000, 1073318, 19005⟩,
    ⟨1986, 88, 4, 3114, 3119, 6204, 9381, 2021329, 16425⟩,
    ⟨1986, 127, 4, 2747, 2752, 5808, 11270, 3003430, 14598⟩,
    ⟨1986, 166, 4, 2479, 2484, 5518, 12885, 4013867, 13212⟩,
    ⟨1986, 205, 3, 2268, 2273, 5290, 14318, 5041760, 12092⟩,
    ⟨1986, 244, 3, 2094, 2099, 5102, 15621, 6084565, 11161⟩,
    ⟨1986, 283, 3, 1946, 1951, 4943, 16823, 7133166, 10360⟩,
    ⟨1986, 322, 3, 1817, 1822, 4803, 17945, 8205094, 9682⟩,
    ⟨1986, 361, 2, 1702, 1707, 4679, 19000, 9288297, 9079⟩,
    ⟨1986, 400, 2, 1600, 1605, 4569, 20000, 10368322, 8545⟩,
    ⟨1986, 439, 2, 1507, 1512, 4468, 20953, 11470233, 8073⟩,
    ⟨1986, 478, 2, 1422, 1427, 4377, 21864, 12562991, 7637⟩,
    ⟨1986, 517, 2, 1343, 1348, 4291, 22738, 13691227, 7252⟩,
    ⟨1986, 556, 2, 1271, 1276, 4214, 23580, 14787101, 6892⟩,
    ⟨1986, 595, 2, 1203, 1208, 4140, 24393, 15922851, 6569⟩,
    ⟨1986, 634, 2, 1139, 1144, 4071, 25180, 17060319, 6267⟩,
    ⟨1986, 673, 2, 1080, 1085, 4007, 25943, 18187877, 5992⟩,
    ⟨1986, 712, 1, 1023, 1028, 3946, 26684, 19331874, 5731⟩,
    ⟨1986, 751, 1, 970, 975, 3888, 27405, 20486277, 5496⟩,
    ⟨1986, 790, 1, 919, 924, 3833, 28107, 21644584, 5271⟩,
    ⟨1986, 829, 1, 871, 876, 3782, 28793, 22777091, 5058⟩,
    ⟨1986, 868, 1, 825, 830, 3732, 29462, 23944898, 4863⟩,
    ⟨1986, 907, 1, 781, 786, 3684, 30117, 25122284, 4681⟩,
    ⟨1986, 946, 1, 739, 744, 3639, 30758, 26278609, 4506⟩,
    ⟨1986, 985, 1, 699, 704, 3596, 31385, 27433236, 4343⟩,
    ⟨1986, 1024, 1, 660, 665, 3554, 32000, 28609970, 4187⟩,
    ⟨1986, 1063, 1, 623, 628, 3514, 32604, 29777565, 4042⟩,
    ⟨1986, 1102, 1, 586, 591, 3474, 33197, 30992811, 3902⟩,
    ⟨1986, 1141, 1, 552, 557, 3437, 33779, 32161023, 3773⟩,
    ⟨1986, 1180, 1, 518, 523, 3400, 34352, 33373269, 3648⟩,
    ⟨1986, 1219, 1, 486, 491, 3366, 34915, 34527471, 3528⟩,
    ⟨1986, 1258, 1, 454, 459, 3331, 35469, 35757329, 3415⟩,
    ⟨1986, 1297, 1, 424, 429, 3299, 36014, 36920068, 3307⟩,
    ⟨1986, 1336, 1, 394, 399, 3266, 36552, 38158757, 3205⟩,
    ⟨1986, 1375, 1, 365, 370, 3235, 37081, 39360204, 3105⟩,
    ⟨1986, 1414, 0, 337, 342, 3205, 37604, 40558901, 3011⟩,
    ⟨1986, 1453, 0, 310, 315, 3176, 38119, 41752330, 2920⟩,
    ⟨1986, 1492, 0, 284, 289, 3148, 38627, 42937916, 2835⟩,
    ⟨1986, 1531, 0, 258, 263, 3120, 39128, 44157168, 2752⟩,
    ⟨1986, 1570, 0, 233, 238, 3093, 39624, 45365653, 2673⟩,
    ⟨1986, 1609, 0, 208, 213, 3066, 40113, 46607211, 2596⟩,
    ⟨1986, 1648, 0, 184, 189, 3040, 40596, 47834889, 2523⟩,
    ⟨1986, 1687, 0, 161, 166, 3015, 41074, 49045835, 2454⟩,
    ⟨1986, 1726, 0, 138, 143, 2990, 41546, 50287436, 2386⟩,
    ⟨1986, 1765, 0, 115, 120, 2965, 42012, 51560469, 2320⟩,
    ⟨1986, 1804, 0, 94, 99, 2942, 42474, 52760102, 2260⟩,
    ⟨1986, 1843, 0, 72, 77, 2919, 42931, 53987647, 2197⟩,
    ⟨1986, 1882, 0, 51, 56, 2896, 43383, 55243753, 2139⟩,
    ⟨1986, 1921, 0, 31, 36, 2874, 43830, 56472583, 2085⟩,
    ⟨1986, 1960, 0, 11, 16, 2853, 44272, 57671047, 2029⟩,
    ⟨1986, 1986, 0, -2, 2, 2838, 44565, 58542634, 1997⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell33_rows_check : ∀ r ∈ target028Cell33Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell33Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1986)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell33RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell33Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1986, 1986, 0, -2, 2, 2838, 44565, 58542634, 1997⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell33Weight (n : ℕ) : ℚ :=
  ((target028Cell33RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell33_select :
    ∀ n ∈ target028Cell33Prefix,
      1 ≤ n ∧
        target028Cell33RowFor n ∈ target028Cell33Rows ∧
        n ≤ (target028Cell33RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell33RowFor n).b) ∧ (target028Cell33RowFor n).cut = 1986 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell33_sum_check :
    (56909 / 5000 : ℚ) <
      ∑ n ∈ target028Cell33Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell33Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell33_principal :
    (56909 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1986 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1986 n).re := by
  have hs : target028Cell33Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell33Prefix ⊆ Finset.Ioc 0 ⌊(1986 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell33_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell33Prefix, 0 ≤ target028Cell33Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell33Prefix, (target028Cell33Weight n : ℝ) ≤ refinedScaledWeight 1986 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell33_select n hn
    have hcheck := target028_cell33_rows_check (target028Cell33RowFor n) hm
    have hrow := (target028Cell33RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell33RowFor n).b ≤ 1986 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1986 (target028Cell33RowFor n).b ≤ refinedScaledWeight 1986 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1986) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell33Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1986) target028Cell33Prefix
      target028EulerData2701 target028Cell33Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((56909 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell33Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell33Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell33_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell33_budget :
    target028MomentBudget 1986 (86225 / 1000) ≤ 4 * (56909 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1986 11 32 0 (75941 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1986 0 (10971 / 40000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1986 ≤ (75941 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1986 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (10971 / 40000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (44563 / 1000 : ℝ) ≤ Real.sqrt 1986 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1986 ≤ (22283 / 500 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1986) (U := 86225 / 1000) (L := 75941 / 10000) (P :=
      10971 / 40000000) (s := 44563 / 1000) (t := 22283 / 500) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell33_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (84225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 86225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1986 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1986) (U := 86225 / 1000) (S := 56909 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell33_principal) target028_cell33_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
