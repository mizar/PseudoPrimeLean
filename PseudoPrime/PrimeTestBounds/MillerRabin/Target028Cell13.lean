/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 547. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell13Rows : List Target028GeneralWeightRow :=
  [⟨547, 2, 8, 5609, 5614, 8899, 1415, 136525, 44714⟩,
    ⟨547, 3, 8, 5203, 5208, 8460, 1733, 211772, 43980⟩,
    ⟨547, 4, 7, 4916, 4921, 8150, 2000, 288735, 43107⟩,
    ⟨547, 5, 7, 4693, 4698, 7909, 2237, 367421, 42208⟩,
    ⟨547, 7, 6, 4356, 4361, 7545, 2646, 528747, 40568⟩,
    ⟨547, 8, 6, 4223, 4228, 7402, 2829, 610031, 39762⟩,
    ⟨547, 9, 6, 4105, 4110, 7274, 3000, 693333, 39069⟩,
    ⟨547, 20, 5, 3306, 3311, 6411, 4473, 1643380, 33015⟩,
    ⟨547, 30, 4, 2901, 2906, 5974, 5478, 2544044, 29301⟩,
    ⟨547, 40, 4, 2613, 2618, 5663, 6325, 3472085, 26502⟩,
    ⟨547, 50, 3, 2390, 2395, 5422, 7072, 4418301, 24266⟩,
    ⟨547, 60, 3, 2208, 2213, 5226, 7746, 5374982, 22403⟩,
    ⟨547, 70, 3, 2053, 2058, 5058, 8367, 6358263, 20845⟩,
    ⟨547, 80, 3, 1920, 1925, 4914, 8945, 7343057, 19494⟩,
    ⟨547, 90, 3, 1802, 1807, 4787, 9487, 8337432, 18297⟩,
    ⟨547, 100, 2, 1697, 1702, 4674, 10000, 9334855, 17237⟩,
    ⟨547, 110, 2, 1601, 1606, 4570, 10489, 10357959, 16297⟩,
    ⟨547, 120, 2, 1514, 1519, 4476, 10955, 11378837, 15448⟩,
    ⟨547, 130, 2, 1434, 1439, 4390, 11402, 12400729, 14672⟩,
    ⟨547, 140, 2, 1360, 1365, 4310, 11833, 13433549, 13969⟩,
    ⟨547, 150, 2, 1291, 1296, 4235, 12248, 14479810, 13330⟩,
    ⟨547, 160, 2, 1227, 1232, 4166, 12650, 15514192, 12735⟩,
    ⟨547, 170, 2, 1166, 1171, 4100, 13039, 16572675, 12185⟩,
    ⟨547, 180, 2, 1109, 1114, 4039, 13417, 17615078, 11669⟩,
    ⟨547, 190, 2, 1055, 1060, 3980, 13785, 18685639, 11201⟩,
    ⟨547, 200, 1, 1004, 1009, 3925, 14143, 19742136, 10757⟩,
    ⟨547, 220, 1, 908, 913, 3822, 14833, 21883989, 9943⟩,
    ⟨547, 230, 1, 864, 869, 3774, 15166, 22960039, 9583⟩,
    ⟨547, 240, 1, 821, 826, 3728, 15492, 24040869, 9233⟩,
    ⟨547, 250, 1, 780, 785, 3683, 15812, 25147419, 8913⟩,
    ⟨547, 260, 1, 741, 746, 3641, 16125, 26226104, 8604⟩,
    ⟨547, 270, 1, 704, 709, 3601, 16432, 27296412, 8316⟩,
    ⟨547, 280, 1, 667, 672, 3561, 16734, 28410400, 8037⟩,
    ⟨547, 290, 1, 632, 637, 3523, 17030, 29510769, 7776⟩,
    ⟨547, 300, 1, 598, 603, 3487, 17321, 30592512, 7521⟩,
    ⟨547, 310, 1, 565, 570, 3451, 17607, 31713906, 7285⟩,
    ⟨547, 320, 1, 534, 539, 3418, 17889, 32777925, 7057⟩,
    ⟨547, 340, 1, 473, 478, 3352, 18440, 35014255, 6634⟩,
    ⟨547, 350, 1, 444, 449, 3320, 18709, 36152831, 6441⟩,
    ⟨547, 360, 1, 416, 421, 3290, 18974, 37253849, 6252⟩,
    ⟨547, 370, 1, 388, 393, 3260, 19236, 38388397, 6067⟩,
    ⟨547, 380, 1, 362, 367, 3232, 19494, 39478462, 5896⟩,
    ⟨547, 390, 0, 336, 341, 3204, 19749, 40599480, 5729⟩,
    ⟨547, 400, 0, 310, 315, 3176, 20000, 41752330, 5567⟩,
    ⟨547, 410, 0, 286, 291, 3150, 20249, 42852126, 5416⟩,
    ⟨547, 420, 0, 262, 267, 3124, 20494, 43980892, 5269⟩,
    ⟨547, 430, 0, 238, 243, 3098, 20737, 45139390, 5126⟩,
    ⟨547, 440, 0, 215, 220, 3073, 20977, 46282100, 4991⟩,
    ⟨547, 450, 0, 193, 198, 3049, 21214, 47406306, 4862⟩,
    ⟨547, 460, 0, 171, 176, 3026, 21448, 48509287, 4732⟩,
    ⟨547, 470, 0, 149, 154, 3002, 21680, 49687593, 4609⟩,
    ⟨547, 480, 0, 128, 133, 2979, 21909, 50843652, 4493⟩,
    ⟨547, 490, 0, 108, 113, 2958, 22136, 51922658, 4379⟩,
    ⟨547, 500, 0, 87, 92, 2935, 22361, 53130719, 4268⟩,
    ⟨547, 510, 0, 68, 73, 2914, 22584, 54258262, 4166⟩,
    ⟨547, 520, 0, 48, 53, 2893, 22804, 55409733, 4059⟩,
    ⟨547, 530, 0, 29, 34, 2872, 23022, 56585641, 3962⟩,
    ⟨547, 547, 0, -2, 2, 2838, 23389, 58542634, 3805⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell13_rows_check : ∀ r ∈ target028Cell13Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell13Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 547)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell13RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell13Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨547, 547, 0, -2, 2, 2838, 23389, 58542634, 3805⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell13Weight (n : ℕ) : ℚ :=
  ((target028Cell13RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell13_select :
    ∀ n ∈ target028Cell13Prefix,
      1 ≤ n ∧
        target028Cell13RowFor n ∈ target028Cell13Rows ∧
        n ≤ (target028Cell13RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell13RowFor n).b) ∧ (target028Cell13RowFor n).cut = 547 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell13_sum_check :
    (11917 / 2000 : ℚ) <
      ∑ n ∈ target028Cell13Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell13Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell13_principal :
    (11917 / 2000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(547 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 547 n).re := by
  have hs : target028Cell13Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell13Prefix ⊆ Finset.Ioc 0 ⌊(547 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell13_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell13Prefix, 0 ≤ target028Cell13Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell13Prefix, (target028Cell13Weight n : ℝ) ≤ refinedScaledWeight 547 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell13_select n hn
    have hcheck := target028_cell13_rows_check (target028Cell13RowFor n) hm
    have hrow := (target028Cell13RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell13RowFor n).b ≤ 547 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 547 (target028Cell13RowFor n).b ≤ refinedScaledWeight 547 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 547) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell13Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 547) target028Cell13Prefix
      target028Cell13Weight hs ht hw0 hw
  have hr :
    ((11917 / 2000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell13Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell13Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell13_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell13_budget :
    target028MomentBudget 547 (46225 / 1000) ≤ 4 * (11917 / 2000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 547 9 32 0 (63047 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 547 0 (552007 / 500000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 547 ≤ (63047 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (547 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (552007 / 500000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (23387 / 1000 : ℝ) ≤ Real.sqrt 547 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 547 ≤ (2339 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 547) (U := 46225 / 1000) (L := 63047 / 10000) (P :=
      552007 / 500000000) (s := 23387 / 1000) (t := 2339 / 100) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell13_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (44225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 46225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (547 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 547) (U := 46225 / 1000) (S := 11917 / 2000) (by norm_num only) hU hcut
      (le_of_lt target028_cell13_principal) target028_cell13_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
