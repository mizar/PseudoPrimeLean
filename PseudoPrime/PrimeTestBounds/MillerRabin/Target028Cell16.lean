/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 16 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 706. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell16Rows : List Target028GeneralWeightRow :=
  [⟨706, 2, 8, 5864, 5869, 9174, 1415, 103700, 39558⟩,
    ⟨706, 3, 8, 5459, 5464, 8737, 1733, 160534, 39159⟩,
    ⟨706, 4, 7, 5171, 5176, 8426, 2000, 219096, 38627⟩,
    ⟨706, 5, 7, 4948, 4953, 8185, 2237, 278804, 38011⟩,
    ⟨706, 7, 7, 4611, 4616, 7821, 2646, 401220, 36831⟩,
    ⟨706, 8, 6, 4478, 4483, 7677, 2829, 463362, 36260⟩,
    ⟨706, 9, 6, 4360, 4365, 7550, 3000, 526110, 35704⟩,
    ⟨706, 24, 5, 3379, 3384, 6490, 4899, 1518549, 29611⟩,
    ⟨706, 38, 4, 2920, 2925, 5994, 6165, 2493669, 25962⟩,
    ⟨706, 52, 4, 2606, 2611, 5655, 7212, 3499973, 23273⟩,
    ⟨706, 66, 3, 2367, 2372, 5397, 8125, 4530151, 21164⟩,
    ⟨706, 80, 3, 2175, 2180, 5190, 8945, 5572006, 19434⟩,
    ⟨706, 94, 3, 2014, 2019, 5016, 9696, 6630997, 17990⟩,
    ⟨706, 108, 3, 1875, 1880, 4866, 10393, 7704120, 16748⟩,
    ⟨706, 122, 3, 1753, 1758, 4734, 11046, 8791235, 15673⟩,
    ⟨706, 136, 2, 1644, 1649, 4616, 11662, 9892286, 14726⟩,
    ⟨706, 150, 2, 1546, 1551, 4511, 12248, 10987467, 13866⟩,
    ⟨706, 164, 2, 1457, 1462, 4414, 12807, 12106654, 13118⟩,
    ⟨706, 178, 2, 1375, 1380, 4326, 13342, 13220323, 12423⟩,
    ⟨706, 192, 2, 1300, 1305, 4245, 13857, 14335733, 11800⟩,
    ⟨706, 206, 2, 1229, 1234, 4168, 14353, 15483195, 11230⟩,
    ⟨706, 220, 2, 1163, 1168, 4097, 14833, 16622468, 10701⟩,
    ⟨706, 234, 2, 1102, 1107, 4031, 15298, 17756564, 10220⟩,
    ⟨706, 248, 2, 1044, 1049, 3968, 15749, 18911217, 9775⟩,
    ⟨706, 262, 1, 989, 994, 3909, 16187, 20060551, 9355⟩,
    ⟨706, 276, 1, 937, 942, 3853, 16614, 21215992, 8965⟩,
    ⟨706, 290, 1, 887, 892, 3799, 17030, 22393153, 8602⟩,
    ⟨706, 304, 1, 840, 845, 3748, 17436, 23564828, 8265⟩,
    ⟨706, 318, 1, 795, 800, 3699, 17833, 24748262, 7950⟩,
    ⟨706, 332, 1, 752, 757, 3653, 18221, 25913272, 7647⟩,
    ⟨706, 346, 1, 711, 716, 3609, 18602, 27078912, 7364⟩,
    ⟨706, 360, 1, 671, 676, 3566, 18974, 28268702, 7096⟩,
    ⟨706, 374, 1, 633, 638, 3525, 19340, 29451807, 6844⟩,
    ⟨706, 388, 1, 596, 601, 3485, 19698, 30653758, 6606⟩,
    ⟨706, 402, 1, 561, 566, 3447, 20050, 31841016, 6383⟩,
    ⟨706, 416, 1, 526, 531, 3409, 20397, 33074258, 6167⟩,
    ⟨706, 430, 1, 493, 498, 3373, 20737, 34286622, 5966⟩,
    ⟨706, 444, 1, 461, 466, 3339, 21072, 35472412, 5769⟩,
    ⟨706, 458, 1, 430, 435, 3305, 21401, 36699211, 5587⟩,
    ⟨706, 472, 1, 400, 405, 3273, 21726, 37892578, 5409⟩,
    ⟨706, 486, 1, 371, 376, 3242, 22046, 39085645, 5240⟩,
    ⟨706, 500, 0, 343, 348, 3211, 22361, 40316276, 5084⟩,
    ⟨706, 514, 0, 315, 320, 3181, 22672, 41544090, 4928⟩,
    ⟨706, 528, 0, 288, 293, 3152, 22979, 42766508, 4779⟩,
    ⟨706, 542, 0, 262, 267, 3124, 23281, 43980892, 4639⟩,
    ⟨706, 556, 0, 236, 241, 3096, 23580, 45229760, 4502⟩,
    ⟨706, 570, 0, 211, 216, 3069, 23875, 46467599, 4371⟩,
    ⟨706, 584, 0, 187, 192, 3043, 24167, 47691599, 4248⟩,
    ⟨706, 598, 0, 164, 169, 3018, 24455, 48898918, 4131⟩,
    ⟨706, 612, 0, 140, 145, 2992, 24739, 50186962, 4014⟩,
    ⟨706, 626, 0, 118, 123, 2968, 25020, 51406019, 3906⟩,
    ⟨706, 640, 0, 96, 101, 2945, 25299, 52602059, 3797⟩,
    ⟨706, 654, 0, 74, 79, 2921, 25574, 53879780, 3694⟩,
    ⟨706, 668, 0, 53, 58, 2898, 25846, 55133376, 3597⟩,
    ⟨706, 682, 0, 32, 37, 2875, 26116, 56416139, 3502⟩,
    ⟨706, 696, 0, 12, 17, 2854, 26382, 57613405, 3409⟩,
    ⟨706, 706, 0, -2, 2, 2838, 26571, 58542634, 3349⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell16_rows_check : ∀ r ∈ target028Cell16Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell16Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 706)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell16RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell16Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨706, 706, 0, -2, 2, 2838, 26571, 58542634, 3349⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell16Weight (n : ℕ) : ℚ :=
  ((target028Cell16RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell16_select :
    ∀ n ∈ target028Cell16Prefix,
      1 ≤ n ∧
        target028Cell16RowFor n ∈ target028Cell16Rows ∧
        n ≤ (target028Cell16RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell16RowFor n).b) ∧ (target028Cell16RowFor n).cut = 706 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell16_sum_check :
    (67643 / 10000 : ℚ) <
      ∑ n ∈ target028Cell16Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell16Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell16_principal :
    (67643 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(706 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 706 n).re := by
  have hs : target028Cell16Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell16Prefix ⊆ Finset.Ioc 0 ⌊(706 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell16_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell16Prefix, 0 ≤ target028Cell16Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell16Prefix, (target028Cell16Weight n : ℝ) ≤ refinedScaledWeight 706 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell16_select n hn
    have hcheck := target028_cell16_rows_check (target028Cell16RowFor n) hm
    have hrow := (target028Cell16RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell16RowFor n).b ≤ 706 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 706 (target028Cell16RowFor n).b ≤ refinedScaledWeight 706 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 706) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell16Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 706) target028Cell16Prefix
      target028Cell16Weight hs ht hw0 hw
  have hr :
    ((67643 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell16Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell16Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell16_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell16_budget :
    target028MomentBudget 706 (52225 / 1000) ≤ 4 * (67643 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 706 9 32 0 (65599 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 706 0 (838093 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 706 ≤ (65599 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (706 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (838093 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (26569 / 1000 : ℝ) ≤ Real.sqrt 706 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 706 ≤ (6643 / 250 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 706) (U := 52225 / 1000) (L := 65599 / 10000) (P :=
      838093 / 1000000000) (s := 26569 / 1000) (t := 6643 / 250) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell16_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (50225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 52225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (706 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 706) (U := 52225 / 1000) (S := 67643 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell16_principal) target028_cell16_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
