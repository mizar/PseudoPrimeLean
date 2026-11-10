/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 310. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell06Rows : List Target028GeneralWeightRow :=
  [⟨310, 2, 7, 5041, 5046, 8285, 1415, 252272, 57795⟩,
    ⟨310, 3, 7, 4635, 4640, 7847, 1733, 390922, 55707⟩,
    ⟨310, 4, 6, 4348, 4353, 7537, 2000, 532994, 53793⟩,
    ⟨310, 5, 6, 4125, 4130, 7296, 2237, 678246, 52020⟩,
    ⟨310, 7, 5, 3788, 3793, 6932, 2646, 976046, 48991⟩,
    ⟨310, 8, 5, 3655, 3660, 6788, 2829, 1127220, 47655⟩,
    ⟨310, 9, 5, 3537, 3542, 6661, 3000, 1279865, 46407⟩,
    ⟨310, 16, 4, 2961, 2966, 6039, 4000, 2383941, 39689⟩,
    ⟨310, 22, 4, 2643, 2648, 5695, 4691, 3362737, 35611⟩,
    ⟨310, 28, 3, 2402, 2407, 5435, 5292, 4361235, 32394⟩,
    ⟨310, 34, 3, 2208, 2213, 5226, 5831, 5374982, 29761⟩,
    ⟨310, 40, 3, 2045, 2050, 5049, 6325, 6415745, 27587⟩,
    ⟨310, 46, 3, 1905, 1910, 4898, 6783, 7461491, 25694⟩,
    ⟨310, 52, 3, 1783, 1788, 4767, 7212, 8505859, 24032⟩,
    ⟨310, 58, 2, 1674, 1679, 4649, 7616, 9571168, 22595⟩,
    ⟨310, 64, 2, 1575, 1580, 4542, 8000, 10652081, 21307⟩,
    ⟨310, 70, 2, 1486, 1491, 4446, 8367, 11725374, 20147⟩,
    ⟨310, 76, 2, 1403, 1408, 4356, 8718, 12829603, 19106⟩,
    ⟨310, 82, 2, 1327, 1332, 4274, 9056, 13925967, 18151⟩,
    ⟨310, 88, 2, 1257, 1262, 4198, 9381, 15025597, 17290⟩,
    ⟨310, 94, 2, 1191, 1196, 4127, 9696, 16131199, 16483⟩,
    ⟨310, 100, 2, 1129, 1134, 4060, 10000, 17249019, 15746⟩,
    ⟨310, 106, 2, 1071, 1076, 3998, 10296, 18352306, 15052⟩,
    ⟨310, 112, 1, 1016, 1021, 3938, 10584, 19487150, 14425⟩,
    ⟨310, 118, 1, 963, 968, 3881, 10863, 20630184, 13827⟩,
    ⟨310, 124, 1, 914, 919, 3828, 11136, 21753078, 13277⟩,
    ⟨310, 130, 1, 867, 872, 3777, 11402, 22891262, 12764⟩,
    ⟨310, 136, 1, 821, 826, 3728, 11662, 24040869, 12265⟩,
    ⟨310, 142, 1, 778, 783, 3681, 11917, 25197764, 11815⟩,
    ⟨310, 154, 1, 697, 702, 3594, 12410, 27488157, 10972⟩,
    ⟨310, 160, 1, 659, 664, 3553, 12650, 28638594, 10588⟩,
    ⟨310, 166, 1, 622, 627, 3513, 12885, 29807358, 10223⟩,
    ⟨310, 172, 1, 587, 592, 3475, 13115, 30961833, 9882⟩,
    ⟨310, 178, 1, 552, 557, 3437, 13342, 32161023, 9552⟩,
    ⟨310, 184, 1, 519, 524, 3401, 13565, 33339913, 9244⟩,
    ⟨310, 196, 1, 456, 461, 3333, 14000, 35685886, 8664⟩,
    ⟨310, 202, 1, 426, 431, 3301, 14213, 36846302, 8391⟩,
    ⟨310, 214, 1, 368, 373, 3238, 14629, 39242301, 7888⟩,
    ⟨310, 226, 0, 314, 319, 3180, 15034, 41585655, 7426⟩,
    ⟨310, 232, 0, 287, 292, 3151, 15232, 42809296, 7205⟩,
    ⟨310, 238, 0, 262, 267, 3124, 15428, 43980892, 7000⟩,
    ⟨310, 244, 0, 237, 242, 3097, 15621, 45184552, 6800⟩,
    ⟨310, 256, 0, 189, 194, 3045, 16000, 47596311, 6427⟩,
    ⟨310, 262, 0, 166, 171, 3020, 16187, 48801218, 6251⟩,
    ⟨310, 268, 0, 143, 148, 2995, 16371, 50036627, 6081⟩,
    ⟨310, 274, 0, 121, 126, 2972, 16553, 51200806, 5913⟩,
    ⟨310, 280, 0, 99, 104, 2948, 16734, 52444490, 5755⟩,
    ⟨310, 286, 0, 78, 83, 2925, 16912, 53664691, 5606⟩,
    ⟨310, 292, 0, 57, 62, 2902, 17089, 54913283, 5459⟩,
    ⟨310, 298, 0, 37, 42, 2881, 17263, 56078656, 5316⟩,
    ⟨310, 310, 0, -2, 2, 2838, 17607, 58542634, 5054⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell06_rows_check : ∀ r ∈ target028Cell06Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell06Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 310)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell06RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell06Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨310, 310, 0, -2, 2, 2838, 17607, 58542634, 5054⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell06Weight (n : ℕ) : ℚ :=
  ((target028Cell06RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell06_select :
    ∀ n ∈ target028Cell06Prefix,
      1 ≤ n ∧
        target028Cell06RowFor n ∈ target028Cell06Rows ∧
        n ≤ (target028Cell06RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell06RowFor n).b) ∧ (target028Cell06RowFor n).cut = 310 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell06_sum_check :
    (44051 / 10000 : ℚ) <
      ∑ n ∈ target028Cell06Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell06Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell06_principal :
    (44051 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(310 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 310 n).re := by
  have hs : target028Cell06Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell06Prefix ⊆ Finset.Ioc 0 ⌊(310 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell06_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell06Prefix, 0 ≤ target028Cell06Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell06Prefix, (target028Cell06Weight n : ℝ) ≤ refinedScaledWeight 310 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell06_select n hn
    have hcheck := target028_cell06_rows_check (target028Cell06RowFor n) hm
    have hrow := (target028Cell06RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell06RowFor n).b ≤ 310 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 310 (target028Cell06RowFor n).b ≤ refinedScaledWeight 310 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 310) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell06Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 310) target028Cell06Prefix
      target028Cell06Weight hs ht hw0 hw
  have hr :
    ((44051 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell06Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell06Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell06_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell06_budget :
    target028MomentBudget 310 (34267 / 1000) ≤ 4 * (44051 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 310 8 32 0 (7171 / 1250) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 310 0 (203859 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 310 ≤ (7171 / 1250 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (310 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (203859 / 100000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (3521 / 200 : ℝ) ≤ Real.sqrt 310 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 310 ≤ (2201 / 125 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 310) (U := 34267 / 1000) (L := 7171 / 1250) (P :=
      203859 / 100000000) (s := 3521 / 200) (t := 2201 / 125) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell06_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (33274 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 34267 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (310 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 310) (U := 34267 / 1000) (S := 44051 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell06_principal) target028_cell06_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
