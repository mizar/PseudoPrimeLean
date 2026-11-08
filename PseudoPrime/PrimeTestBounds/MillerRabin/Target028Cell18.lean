/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 18 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 823. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell18Rows : List Target028GeneralWeightRow :=
  [⟨823, 2, 9, 6017, 6022, 9339, 1415, 87927, 36675⟩,
    ⟨823, 3, 8, 5612, 5617, 8902, 1733, 136116, 36466⟩,
    ⟨823, 4, 8, 5324, 5329, 8591, 2000, 185770, 36094⟩,
    ⟨823, 5, 7, 5101, 5106, 8350, 2237, 236396, 35619⟩,
    ⟨823, 7, 7, 4765, 4770, 7987, 2646, 339852, 34662⟩,
    ⟨823, 8, 7, 4631, 4636, 7842, 2829, 392882, 34202⟩,
    ⟨823, 9, 7, 4513, 4518, 7715, 3000, 446085, 33737⟩,
    ⟨823, 26, 5, 3452, 3457, 6569, 5100, 1403199, 27921⟩,
    ⟨823, 42, 4, 2973, 2978, 6052, 6481, 2353150, 24440⟩,
    ⟨823, 58, 4, 2650, 2655, 5703, 7616, 3335942, 21904⟩,
    ⟨823, 74, 3, 2406, 2411, 5439, 8603, 4343824, 19926⟩,
    ⟨823, 90, 3, 2211, 2216, 5229, 9487, 5358881, 18294⟩,
    ⟨823, 106, 3, 2047, 2052, 5052, 10296, 6396527, 16932⟩,
    ⟨823, 122, 3, 1906, 1911, 4899, 11046, 7454033, 15779⟩,
    ⟨823, 138, 3, 1783, 1788, 4767, 11748, 8505859, 14753⟩,
    ⟨823, 154, 2, 1674, 1679, 4649, 12410, 9571168, 13866⟩,
    ⟨823, 170, 2, 1575, 1580, 4542, 13039, 10652081, 13072⟩,
    ⟨823, 186, 2, 1485, 1490, 4445, 13639, 11737106, 12357⟩,
    ⟨823, 202, 2, 1402, 1407, 4355, 14213, 12842439, 11716⟩,
    ⟨823, 218, 2, 1326, 1331, 4273, 14765, 13939900, 11130⟩,
    ⟨823, 234, 2, 1255, 1260, 4196, 15298, 15055679, 10596⟩,
    ⟨823, 250, 2, 1189, 1194, 4125, 15812, 16163494, 10101⟩,
    ⟨823, 266, 2, 1127, 1132, 4058, 16310, 17283551, 9647⟩,
    ⟨823, 282, 2, 1069, 1074, 3995, 16793, 18407446, 9231⟩,
    ⟨823, 298, 1, 1013, 1018, 3935, 17263, 19545699, 8834⟩,
    ⟨823, 314, 1, 961, 966, 3879, 17721, 20671486, 8469⟩,
    ⟨823, 330, 1, 911, 916, 3825, 18166, 21818435, 8129⟩,
    ⟨823, 346, 1, 864, 869, 3774, 18602, 22960039, 7813⟩,
    ⟨823, 362, 1, 819, 824, 3725, 19027, 24113100, 7518⟩,
    ⟨823, 378, 1, 776, 781, 3679, 19443, 25248210, 7234⟩,
    ⟨823, 394, 1, 734, 739, 3634, 19850, 26410331, 6966⟩,
    ⟨823, 410, 1, 694, 699, 3590, 20249, 27598330, 6721⟩,
    ⟨823, 426, 1, 656, 661, 3549, 20640, 28753378, 6485⟩,
    ⟨823, 442, 1, 619, 624, 3509, 21024, 29926826, 6261⟩,
    ⟨823, 458, 1, 584, 589, 3472, 21401, 31054858, 6046⟩,
    ⟨823, 474, 1, 549, 554, 3434, 21772, 32257651, 5843⟩,
    ⟨823, 490, 1, 516, 521, 3398, 22136, 33440083, 5655⟩,
    ⟨823, 506, 1, 484, 489, 3364, 22495, 34596595, 5470⟩,
    ⟨823, 522, 1, 453, 458, 3330, 22848, 35793105, 5299⟩,
    ⟨823, 538, 1, 423, 428, 3298, 23195, 36957007, 5132⟩,
    ⟨823, 554, 1, 393, 398, 3265, 23538, 38196935, 4974⟩,
    ⟨823, 570, 1, 365, 370, 3235, 23875, 39360204, 4824⟩,
    ⟨823, 586, 0, 337, 342, 3205, 24208, 40558901, 4677⟩,
    ⟨823, 602, 0, 310, 315, 3176, 24536, 41752330, 4537⟩,
    ⟨823, 618, 0, 284, 289, 3148, 24860, 42937916, 4405⟩,
    ⟨823, 634, 0, 258, 263, 3120, 25180, 44157168, 4276⟩,
    ⟨823, 650, 0, 233, 238, 3093, 25496, 45365653, 4154⟩,
    ⟨823, 666, 0, 209, 214, 3067, 25807, 46560627, 4038⟩,
    ⟨823, 682, 0, 185, 190, 3041, 26116, 47787078, 3925⟩,
    ⟨823, 698, 0, 162, 167, 3016, 26420, 48996814, 3818⟩,
    ⟨823, 714, 0, 140, 145, 2992, 26721, 50186962, 3716⟩,
    ⟨823, 730, 0, 117, 122, 2967, 27019, 51457451, 3614⟩,
    ⟨823, 746, 0, 96, 101, 2945, 27314, 52602059, 3517⟩,
    ⟨823, 762, 0, 75, 80, 2922, 27605, 53825927, 3425⟩,
    ⟨823, 778, 0, 54, 59, 2899, 27893, 55078270, 3336⟩,
    ⟨823, 794, 0, 33, 38, 2877, 28179, 56303419, 3245⟩,
    ⟨823, 810, 0, 13, 18, 2855, 28461, 57555821, 3163⟩,
    ⟨823, 823, 0, -2, 2, 2838, 28688, 58542634, 3102⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell18_rows_check : ∀ r ∈ target028Cell18Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell18Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 823)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell18RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell18Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨823, 823, 0, -2, 2, 2838, 28688, 58542634, 3102⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell18Weight (n : ℕ) : ℚ :=
  ((target028Cell18RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell18_select :
    ∀ n ∈ target028Cell18Prefix,
      1 ≤ n ∧
        target028Cell18RowFor n ∈ target028Cell18Rows ∧
        n ≤ (target028Cell18RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell18RowFor n).b) ∧ (target028Cell18RowFor n).cut = 823 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell18_sum_check :
    (36581 / 5000 : ℚ) <
      ∑ n ∈ target028Cell18Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell18Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell18_principal :
    (36581 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(823 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 823 n).re := by
  have hs : target028Cell18Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell18Prefix ⊆ Finset.Ioc 0 ⌊(823 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell18_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell18Prefix, 0 ≤ target028Cell18Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell18Prefix, (target028Cell18Weight n : ℝ) ≤ refinedScaledWeight 823 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell18_select n hn
    have hcheck := target028_cell18_rows_check (target028Cell18RowFor n) hm
    have hrow := (target028Cell18RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell18RowFor n).b ≤ 823 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 823 (target028Cell18RowFor n).b ≤ refinedScaledWeight 823 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 823) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell18Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 823) target028Cell18Prefix
      target028Cell18Weight hs ht hw0 hw
  have hr :
    ((36581 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell18Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell18Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell18_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell18_budget :
    target028MomentBudget 823 (56225 / 1000) ≤ 4 * (36581 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 823 10 32 0 (16783 / 2500) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 823 0 (355091 / 500000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 823 ≤ (16783 / 2500 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (823 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (355091 / 500000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (14343 / 500 : ℝ) ≤ Real.sqrt 823 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 823 ≤ (28689 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 823) (U := 56225 / 1000) (L := 16783 / 2500) (P :=
      355091 / 500000000) (s := 14343 / 500) (t := 28689 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell18_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (54225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 56225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (823 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 823) (U := 56225 / 1000) (S := 36581 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell18_principal) target028_cell18_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
