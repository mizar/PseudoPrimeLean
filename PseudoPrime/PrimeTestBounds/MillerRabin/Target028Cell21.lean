/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 21 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1015. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell21Rows : List Target028GeneralWeightRow :=
  [⟨1015, 2, 9, 6227, 6232, 9566, 1415, 70071, 32955⟩,
    ⟨1015, 3, 8, 5822, 5827, 9129, 1733, 108474, 32959⟩,
    ⟨1015, 4, 8, 5534, 5539, 8818, 2000, 148044, 32770⟩,
    ⟨1015, 5, 8, 5311, 5316, 8577, 2237, 188389, 32459⟩,
    ⟨1015, 7, 7, 4974, 4979, 8213, 2646, 271106, 31788⟩,
    ⟨1015, 8, 7, 4841, 4846, 8069, 2829, 313096, 31435⟩,
    ⟨1015, 9, 7, 4723, 4728, 7942, 3000, 355494, 31080⟩,
    ⟨1015, 30, 5, 3519, 3524, 6641, 5478, 1305720, 25551⟩,
    ⟨1015, 50, 4, 3008, 3013, 6090, 7072, 2265408, 22245⟩,
    ⟨1015, 70, 4, 2672, 2677, 5727, 8367, 3256833, 19875⟩,
    ⟨1015, 90, 3, 2420, 2425, 5455, 9487, 4274876, 18031⟩,
    ⟨1015, 110, 3, 2220, 2225, 5238, 10489, 5310867, 16551⟩,
    ⟨1015, 130, 3, 2053, 2058, 5058, 11402, 6358263, 15296⟩,
    ⟨1015, 150, 3, 1910, 1915, 4904, 12248, 7416856, 14222⟩,
    ⟨1015, 170, 3, 1784, 1789, 4768, 13039, 8497357, 13294⟩,
    ⟨1015, 190, 2, 1673, 1678, 4648, 13785, 9580744, 12481⟩,
    ⟨1015, 210, 2, 1573, 1578, 4540, 14492, 10673406, 11757⟩,
    ⟨1015, 230, 2, 1482, 1487, 4441, 15166, 11784148, 11117⟩,
    ⟨1015, 250, 2, 1399, 1404, 4352, 15812, 12881024, 10524⟩,
    ⟨1015, 270, 2, 1322, 1327, 4269, 16432, 13995771, 9990⟩,
    ⟨1015, 290, 2, 1250, 1255, 4191, 17030, 15131146, 9505⟩,
    ⟨1015, 310, 2, 1184, 1189, 4120, 17607, 16244514, 9057⟩,
    ⟨1015, 330, 2, 1121, 1126, 4052, 18166, 17387564, 8644⟩,
    ⟨1015, 350, 2, 1062, 1067, 3988, 18709, 18536750, 8265⟩,
    ⟨1015, 370, 1, 1007, 1012, 3928, 19236, 19682999, 7918⟩,
    ⟨1015, 390, 1, 954, 959, 3871, 19749, 20837521, 7586⟩,
    ⟨1015, 410, 1, 904, 909, 3817, 20249, 21993683, 7279⟩,
    ⟨1015, 430, 1, 856, 861, 3765, 20737, 23167612, 6991⟩,
    ⟨1015, 450, 1, 811, 816, 3717, 21214, 24306778, 6719⟩,
    ⟨1015, 470, 1, 767, 772, 3669, 21680, 25501959, 6467⟩,
    ⟨1015, 490, 1, 726, 731, 3625, 22136, 26649097, 6228⟩,
    ⟨1015, 510, 1, 686, 691, 3582, 22584, 27820002, 6001⟩,
    ⟨1015, 530, 1, 647, 652, 3540, 23022, 29013327, 5787⟩,
    ⟨1015, 550, 1, 610, 615, 3500, 23453, 30197383, 5585⟩,
    ⟨1015, 570, 1, 575, 580, 3462, 23875, 31366965, 5397⟩,
    ⟨1015, 590, 1, 540, 545, 3424, 24290, 32581846, 5216⟩,
    ⟨1015, 610, 1, 507, 512, 3388, 24699, 33776161, 5046⟩,
    ⟨1015, 630, 1, 474, 479, 3353, 25100, 34979258, 4877⟩,
    ⟨1015, 650, 1, 443, 448, 3319, 25496, 36189002, 4724⟩,
    ⟨1015, 670, 1, 413, 418, 3287, 25885, 37365778, 4574⟩,
    ⟨1015, 690, 1, 383, 388, 3255, 26268, 38580820, 4428⟩,
    ⟨1015, 710, 1, 355, 360, 3224, 26646, 39795557, 4297⟩,
    ⟨1015, 730, 0, 327, 332, 3194, 27019, 41007512, 4165⟩,
    ⟨1015, 750, 0, 300, 305, 3165, 27387, 42214141, 4040⟩,
    ⟨1015, 770, 0, 274, 279, 3137, 27749, 43412841, 3922⟩,
    ⟨1015, 790, 0, 248, 253, 3109, 28107, 44645578, 3806⟩,
    ⟨1015, 810, 0, 223, 228, 3082, 28461, 45867429, 3697⟩,
    ⟨1015, 830, 0, 199, 204, 3056, 28810, 47075621, 3593⟩,
    ⟨1015, 850, 0, 175, 180, 3030, 29155, 48315638, 3492⟩,
    ⟨1015, 870, 0, 152, 157, 3005, 29496, 49538754, 3396⟩,
    ⟨1015, 890, 0, 129, 134, 2980, 29833, 50792833, 3302⟩,
    ⟨1015, 910, 0, 107, 112, 2956, 30167, 52026607, 3213⟩,
    ⟨1015, 930, 0, 85, 90, 2933, 30496, 53237087, 3124⟩,
    ⟨1015, 950, 0, 64, 69, 2910, 30823, 54475729, 3042⟩,
    ⟨1015, 970, 0, 43, 48, 2887, 31145, 55743191, 2962⟩,
    ⟨1015, 990, 0, 22, 27, 2865, 31465, 56983131, 2881⟩,
    ⟨1015, 1010, 0, 2, 7, 2843, 31781, 58250651, 2807⟩,
    ⟨1015, 1015, 0, -2, 2, 2838, 31860, 58542634, 2793⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell21_rows_check : ∀ r ∈ target028Cell21Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell21Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1015)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell21RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell21Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1015, 1015, 0, -2, 2, 2838, 31860, 58542634, 2793⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell21Weight (n : ℕ) : ℚ :=
  ((target028Cell21RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell21_select :
    ∀ n ∈ target028Cell21Prefix,
      1 ≤ n ∧
        target028Cell21RowFor n ∈ target028Cell21Rows ∧
        n ≤ (target028Cell21RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell21RowFor n).b) ∧ (target028Cell21RowFor n).cut = 1015 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell21_sum_check :
    (40643 / 5000 : ℚ) <
      ∑ n ∈ target028Cell21Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell21Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell21_principal :
    (40643 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1015 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1015 n).re := by
  have hs : target028Cell21Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell21Prefix ⊆ Finset.Ioc 0 ⌊(1015 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell21_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell21Prefix, 0 ≤ target028Cell21Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell21Prefix, (target028Cell21Weight n : ℝ) ≤ refinedScaledWeight 1015 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell21_select n hn
    have hcheck := target028_cell21_rows_check (target028Cell21RowFor n) hm
    have hrow := (target028Cell21RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell21RowFor n).b ≤ 1015 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1015 (target028Cell21RowFor n).b ≤ refinedScaledWeight 1015 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1015) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell21Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1015) target028Cell21Prefix
      target028EulerData2701 target028Cell21Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((40643 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell21Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell21Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell21_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell21_budget :
    target028MomentBudget 1015 (62225 / 1000) ≤ 4 * (40643 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1015 10 32 0 (69229 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1015 0 (70783 / 125000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1015 ≤ (69229 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1015 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (70783 / 125000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (15929 / 500 : ℝ) ≤ Real.sqrt 1015 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1015 ≤ (31861 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1015) (U := 62225 / 1000) (L := 69229 / 10000) (P :=
      70783 / 125000000) (s := 15929 / 500) (t := 31861 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell21_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (60225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 62225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1015 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1015) (U := 62225 / 1000) (S := 40643 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell21_principal) target028_cell21_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
