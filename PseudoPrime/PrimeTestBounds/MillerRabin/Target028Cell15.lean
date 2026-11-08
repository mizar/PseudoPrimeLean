/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 15 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 651. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell15Rows : List Target028GeneralWeightRow :=
  [⟨651, 2, 8, 5783, 5788, 9087, 1415, 113126, 41134⟩,
    ⟨651, 3, 8, 5377, 5382, 8648, 1733, 175477, 40677⟩,
    ⟨651, 4, 7, 5090, 5095, 8338, 2000, 239250, 40034⟩,
    ⟨651, 5, 7, 4867, 4872, 8097, 2237, 304451, 39334⟩,
    ⟨651, 7, 7, 4530, 4535, 7733, 2646, 438127, 38018⟩,
    ⟨651, 8, 6, 4397, 4402, 7590, 2829, 505481, 37351⟩,
    ⟨651, 9, 6, 4279, 4284, 7462, 3000, 574506, 36780⟩,
    ⟨651, 23, 5, 3341, 3346, 6449, 4796, 1582103, 30528⟩,
    ⟨651, 36, 4, 2892, 2897, 5964, 6000, 2569612, 26802⟩,
    ⟨651, 49, 4, 2584, 2589, 5632, 7000, 3581405, 24025⟩,
    ⟨651, 62, 3, 2349, 2354, 5378, 7875, 4617046, 21856⟩,
    ⟨651, 75, 3, 2159, 2164, 5173, 8661, 5667540, 20077⟩,
    ⟨651, 88, 3, 1999, 2004, 5000, 9381, 6737946, 18591⟩,
    ⟨651, 101, 3, 1861, 1866, 4851, 10050, 7820553, 17310⟩,
    ⟨651, 114, 3, 1740, 1745, 4720, 10678, 8915178, 16199⟩,
    ⟨651, 127, 2, 1632, 1637, 4603, 11270, 10021725, 15222⟩,
    ⟨651, 140, 2, 1534, 1539, 4498, 11833, 11131236, 14332⟩,
    ⟨651, 153, 2, 1446, 1451, 4403, 12370, 12240563, 13547⟩,
    ⟨651, 166, 2, 1364, 1369, 4314, 12885, 13379922, 12841⟩,
    ⟨651, 179, 2, 1289, 1294, 4233, 13380, 14508798, 12195⟩,
    ⟨651, 192, 2, 1219, 1224, 4157, 13857, 15654450, 11609⟩,
    ⟨651, 205, 2, 1153, 1158, 4086, 14318, 16806324, 11062⟩,
    ⟨651, 218, 2, 1092, 1097, 4020, 14765, 17952964, 10563⟩,
    ⟨651, 231, 1, 1034, 1039, 3958, 15199, 19101278, 10092⟩,
    ⟨651, 244, 1, 979, 984, 3898, 15621, 20282435, 9666⟩,
    ⟨651, 257, 1, 927, 932, 3842, 16032, 21450657, 9263⟩,
    ⟨651, 270, 1, 878, 883, 3789, 16432, 22618208, 8890⟩,
    ⟨651, 283, 1, 831, 836, 3738, 16823, 23801658, 8541⟩,
    ⟨651, 296, 1, 786, 791, 3690, 17205, 24972002, 8206⟩,
    ⟨651, 309, 1, 743, 748, 3643, 17579, 26173704, 7900⟩,
    ⟨651, 322, 1, 701, 706, 3598, 17945, 27378424, 7603⟩,
    ⟨651, 335, 1, 662, 667, 3556, 18304, 28552807, 7328⟩,
    ⟨651, 348, 1, 624, 629, 3515, 18655, 29747802, 7068⟩,
    ⟨651, 361, 1, 587, 592, 3475, 19000, 30961833, 6821⟩,
    ⟨651, 374, 1, 552, 557, 3437, 19340, 32161023, 6590⟩,
    ⟨651, 387, 1, 518, 523, 3400, 19673, 33373269, 6370⟩,
    ⟨651, 400, 1, 485, 490, 3365, 20000, 34562016, 6156⟩,
    ⟨651, 413, 1, 453, 458, 3330, 20323, 35793105, 5957⟩,
    ⟨651, 426, 1, 422, 427, 3297, 20640, 36993983, 5763⟩,
    ⟨651, 439, 1, 392, 397, 3264, 20953, 38235151, 5585⟩,
    ⟨651, 452, 1, 362, 367, 3232, 21261, 39478462, 5406⟩,
    ⟨651, 465, 0, 334, 339, 3202, 21564, 40680760, 5239⟩,
    ⟨651, 478, 0, 306, 311, 3171, 21864, 41961615, 5083⟩,
    ⟨651, 491, 0, 280, 285, 3143, 22159, 43153144, 4933⟩,
    ⟨651, 504, 0, 253, 258, 3114, 22450, 44422907, 4783⟩,
    ⟨651, 517, 0, 228, 233, 3087, 22738, 45638665, 4645⟩,
    ⟨651, 530, 0, 203, 208, 3060, 23022, 46887695, 4510⟩,
    ⟨651, 543, 0, 179, 184, 3034, 23303, 48122761, 4382⟩,
    ⟨651, 556, 0, 155, 160, 3008, 23580, 49390360, 4258⟩,
    ⟨651, 569, 0, 132, 137, 2983, 23854, 50640683, 4140⟩,
    ⟨651, 582, 0, 110, 115, 2960, 24125, 51818917, 4024⟩,
    ⟨651, 595, 0, 87, 92, 2935, 24393, 53130719, 3912⟩,
    ⟨651, 608, 0, 66, 71, 2912, 24658, 54366887, 3809⟩,
    ⟨651, 621, 0, 45, 50, 2889, 24920, 55631816, 3709⟩,
    ⟨651, 634, 0, 24, 29, 2867, 25180, 56869278, 3607⟩,
    ⟨651, 647, 0, 4, 9, 2845, 25437, 58134266, 3514⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell15_rows_check : ∀ r ∈ target028Cell15Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell15Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 651)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell15RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell15Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨651, 647, 0, 4, 9, 2845, 25437, 58134266, 3514⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell15Weight (n : ℕ) : ℚ :=
  ((target028Cell15RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell15_select :
    ∀ n ∈ target028Cell15Prefix,
      1 ≤ n ∧
        target028Cell15RowFor n ∈ target028Cell15Rows ∧
        n ≤ (target028Cell15RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell15RowFor n).b) ∧ (target028Cell15RowFor n).cut = 651 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell15_sum_check :
    (65353 / 10000 : ℚ) <
      ∑ n ∈ target028Cell15Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell15Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell15_principal :
    (65353 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(651 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 651 n).re := by
  have hs : target028Cell15Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell15Prefix ⊆ Finset.Ioc 0 ⌊(651 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell15_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell15Prefix, 0 ≤ target028Cell15Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell15Prefix, (target028Cell15Weight n : ℝ) ≤ refinedScaledWeight 651 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell15_select n hn
    have hcheck := target028_cell15_rows_check (target028Cell15RowFor n) hm
    have hrow := (target028Cell15RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell15RowFor n).b ≤ 651 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 651 (target028Cell15RowFor n).b ≤ refinedScaledWeight 651 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 651) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell15Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 651) target028Cell15Prefix
      target028Cell15Weight hs ht hw0 hw
  have hr :
    ((65353 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell15Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell15Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell15_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell15_budget :
    target028MomentBudget 651 (50225 / 1000) ≤ 4 * (65353 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 651 9 32 0 (16197 / 2500) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 651 0 (7147 / 7812500) 27 25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 651 ≤ (16197 / 2500 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (651 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (7147 / 7812500 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (25513 / 1000 : ℝ) ≤ Real.sqrt 651 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 651 ≤ (6379 / 250 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 651) (U := 50225 / 1000) (L := 16197 / 2500) (P :=
      7147 / 7812500) (s := 25513 / 1000) (t := 6379 / 250) (by norm_num only) (by norm_num only) hl
      hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell15_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (48225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 50225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (651 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 651) (U := 50225 / 1000) (S := 65353 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell15_principal) target028_cell15_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
