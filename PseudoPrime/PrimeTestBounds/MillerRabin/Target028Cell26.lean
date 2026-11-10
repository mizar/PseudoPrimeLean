/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 26 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1380. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell26Rows : List Target028GeneralWeightRow :=
  [⟨1380, 2, 9, 6534, 6539, 9898, 1415, 50275, 28039⟩,
    ⟨1380, 3, 9, 6129, 6134, 9460, 1733, 77906, 28297⟩,
    ⟨1380, 4, 8, 5841, 5846, 9149, 2000, 106326, 28309⟩,
    ⟨1380, 5, 8, 5618, 5623, 8908, 2237, 135302, 28183⟩,
    ⟨1380, 7, 8, 5281, 5286, 8544, 2646, 194709, 27830⟩,
    ⟨1380, 8, 7, 5148, 5153, 8401, 2829, 224642, 27589⟩,
    ⟨1380, 9, 7, 5030, 5035, 8273, 3000, 255318, 27391⟩,
    ⟨1380, 37, 5, 3616, 3621, 6746, 6083, 1175572, 22404⟩,
    ⟨1380, 64, 4, 3068, 3073, 6154, 8000, 2124964, 19449⟩,
    ⟨1380, 91, 4, 2716, 2721, 5774, 9540, 3107303, 17333⟩,
    ⟨1380, 118, 4, 2457, 2462, 5494, 10863, 4111365, 15708⟩,
    ⟨1380, 145, 3, 2251, 2256, 5272, 12042, 5133333, 14386⟩,
    ⟨1380, 172, 3, 2080, 2085, 5087, 13115, 6176521, 13295⟩,
    ⟨1380, 199, 3, 1934, 1939, 4930, 14107, 7226503, 12353⟩,
    ⟨1380, 226, 3, 1807, 1812, 4792, 15034, 8295849, 11553⟩,
    ⟨1380, 253, 2, 1694, 1699, 4670, 15906, 9372269, 10842⟩,
    ⟨1380, 280, 2, 1593, 1598, 4561, 16734, 10451602, 10210⟩,
    ⟨1380, 307, 2, 1500, 1505, 4461, 17522, 11550806, 9640⟩,
    ⟨1380, 334, 2, 1416, 1421, 4370, 18276, 12651240, 9133⟩,
    ⟨1380, 361, 2, 1338, 1343, 4286, 19000, 13759854, 8667⟩,
    ⟨1380, 388, 2, 1266, 1271, 4208, 19698, 14876090, 8247⟩,
    ⟨1380, 415, 2, 1199, 1204, 4136, 20372, 15986670, 7856⟩,
    ⟨1380, 442, 2, 1136, 1141, 4068, 21024, 17111577, 7499⟩,
    ⟨1380, 469, 2, 1077, 1082, 4004, 21657, 18242522, 7171⟩,
    ⟨1380, 496, 1, 1021, 1026, 3944, 22272, 19370577, 6861⟩,
    ⟨1380, 523, 1, 968, 973, 3886, 22870, 20527291, 6580⟩,
    ⟨1380, 550, 1, 917, 922, 3831, 23453, 21687916, 6312⟩,
    ⟨1380, 577, 1, 869, 874, 3779, 24021, 22845525, 6064⟩,
    ⟨1380, 604, 1, 824, 829, 3731, 24577, 23968854, 5828⟩,
    ⟨1380, 631, 1, 780, 785, 3683, 25120, 25147419, 5610⟩,
    ⟨1380, 658, 1, 738, 743, 3638, 25652, 26304901, 5401⟩,
    ⟨1380, 685, 1, 698, 703, 3595, 26173, 27460683, 5205⟩,
    ⟨1380, 712, 1, 659, 664, 3553, 26684, 28638594, 5019⟩,
    ⟨1380, 739, 1, 622, 627, 3513, 27185, 29807358, 4845⟩,
    ⟨1380, 766, 1, 586, 591, 3474, 27677, 30992811, 4680⟩,
    ⟨1380, 793, 1, 552, 557, 3437, 28161, 32161023, 4525⟩,
    ⟨1380, 820, 1, 518, 523, 3400, 28636, 33373269, 4376⟩,
    ⟨1380, 847, 1, 486, 491, 3366, 29104, 34527471, 4233⟩,
    ⟨1380, 874, 1, 454, 459, 3331, 29564, 35757329, 4098⟩,
    ⟨1380, 901, 1, 424, 429, 3299, 30017, 36920068, 3968⟩,
    ⟨1380, 928, 1, 394, 399, 3266, 30464, 38158757, 3846⟩,
    ⟨1380, 955, 1, 366, 371, 3236, 30904, 39320864, 3729⟩,
    ⟨1380, 982, 0, 338, 343, 3206, 31337, 40518362, 3615⟩,
    ⟨1380, 1009, 0, 311, 316, 3177, 31765, 41710599, 3507⟩,
    ⟨1380, 1036, 0, 284, 289, 3148, 32187, 42937916, 3402⟩,
    ⟨1380, 1063, 0, 258, 263, 3120, 32604, 44157168, 3302⟩,
    ⟨1380, 1090, 0, 233, 238, 3093, 33016, 45365653, 3208⟩,
    ⟨1380, 1117, 0, 209, 214, 3067, 33422, 46560627, 3118⟩,
    ⟨1380, 1144, 0, 185, 190, 3041, 33824, 47787078, 3030⟩,
    ⟨1380, 1171, 0, 162, 167, 3016, 34220, 48996814, 2947⟩,
    ⟨1380, 1198, 0, 139, 144, 2991, 34613, 50237174, 2866⟩,
    ⟨1380, 1225, 0, 117, 122, 2967, 35000, 51457451, 2790⟩,
    ⟨1380, 1252, 0, 95, 100, 2943, 35384, 52707369, 2715⟩,
    ⟨1380, 1279, 0, 74, 79, 2921, 35764, 53879780, 2641⟩,
    ⟨1380, 1306, 0, 53, 58, 2898, 36139, 55133376, 2572⟩,
    ⟨1380, 1333, 0, 32, 37, 2875, 36511, 56416139, 2505⟩,
    ⟨1380, 1380, 0, -2, 2, 2838, 37149, 58542634, 2395⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell26_rows_check : ∀ r ∈ target028Cell26Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell26Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1380)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell26RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell26Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1380, 1380, 0, -2, 2, 2838, 37149, 58542634, 2395⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell26Weight (n : ℕ) : ℚ :=
  ((target028Cell26RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell26_select :
    ∀ n ∈ target028Cell26Prefix,
      1 ≤ n ∧
        target028Cell26RowFor n ∈ target028Cell26Rows ∧
        n ≤ (target028Cell26RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell26RowFor n).b) ∧ (target028Cell26RowFor n).cut = 1380 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell26_sum_check :
    (94897 / 10000 : ℚ) <
      ∑ n ∈ target028Cell26Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell26Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell26_principal :
    (94897 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1380 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1380 n).re := by
  have hs : target028Cell26Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell26Prefix ⊆ Finset.Ioc 0 ⌊(1380 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell26_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell26Prefix, 0 ≤ target028Cell26Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell26Prefix, (target028Cell26Weight n : ℝ) ≤ refinedScaledWeight 1380 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell26_select n hn
    have hcheck := target028_cell26_rows_check (target028Cell26RowFor n) hm
    have hrow := (target028Cell26RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell26RowFor n).b ≤ 1380 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1380 (target028Cell26RowFor n).b ≤ refinedScaledWeight 1380 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1380) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell26Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1380) target028Cell26Prefix
      target028EulerData2701 target028Cell26Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((94897 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell26Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell26Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell26_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell26_budget :
    target028MomentBudget 1380 (72225 / 1000) ≤ 4 * (94897 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1380 10 32 0 (72301 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1380 0 (406381 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1380 ≤ (72301 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1380 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (406381 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (37147 / 1000 : ℝ) ≤ Real.sqrt 1380 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1380 ≤ (743 / 20 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1380) (U := 72225 / 1000) (L := 72301 / 10000) (P :=
      406381 / 1000000000) (s := 37147 / 1000) (t := 743 / 20) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell26_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (70225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 72225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1380 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1380) (U := 72225 / 1000) (S := 94897 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell26_principal) target028_cell26_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
