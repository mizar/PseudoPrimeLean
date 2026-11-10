/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 277. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell04Rows : List Target028GeneralWeightRow :=
  [⟨277, 2, 7, 4928, 4933, 8163, 1415, 285006, 60622⟩,
    ⟨277, 3, 7, 4523, 4528, 7726, 1733, 441205, 58170⟩,
    ⟨277, 4, 6, 4235, 4240, 7415, 2000, 602152, 56005⟩,
    ⟨277, 5, 6, 4012, 4017, 7174, 2237, 766251, 54013⟩,
    ⟨277, 7, 5, 3676, 3681, 6811, 2646, 1101590, 50630⟩,
    ⟨277, 8, 5, 3542, 3547, 6666, 2829, 1273482, 49166⟩,
    ⟨277, 9, 5, 3424, 3429, 6539, 3000, 1445933, 47794⟩,
    ⟨277, 15, 4, 2913, 2918, 5987, 3873, 2511186, 41355⟩,
    ⟨277, 20, 4, 2626, 2631, 5677, 4473, 3423814, 37416⟩,
    ⟨277, 25, 3, 2403, 2408, 5436, 5000, 4356875, 34286⟩,
    ⟨277, 30, 3, 2220, 2225, 5238, 5478, 5310867, 31692⟩,
    ⟨277, 35, 3, 2066, 2071, 5072, 5917, 6269867, 29472⟩,
    ⟨277, 40, 3, 1933, 1938, 4929, 6325, 7233733, 27549⟩,
    ⟨277, 45, 3, 1815, 1820, 4801, 6709, 8221521, 25890⟩,
    ⟨277, 50, 2, 1709, 1714, 4687, 7072, 9214287, 24395⟩,
    ⟨277, 55, 2, 1614, 1619, 4584, 7417, 10213958, 23079⟩,
    ⟨277, 60, 2, 1527, 1532, 4490, 7746, 11220643, 21885⟩,
    ⟨277, 65, 2, 1447, 1452, 4404, 8063, 12228328, 20789⟩,
    ⟨277, 70, 2, 1373, 1378, 4324, 8367, 13246790, 19801⟩,
    ⟨277, 75, 2, 1304, 1309, 4249, 8661, 14278505, 18900⟩,
    ⟨277, 80, 2, 1239, 1244, 4179, 8945, 15313813, 18056⟩,
    ⟨277, 85, 2, 1179, 1184, 4114, 9220, 16342274, 17287⟩,
    ⟨277, 90, 2, 1122, 1127, 4053, 9487, 17370185, 16558⟩,
    ⟨277, 100, 1, 1016, 1021, 3938, 10000, 19487150, 15268⟩,
    ⟨277, 105, 1, 968, 973, 3886, 10247, 20527291, 14687⟩,
    ⟨277, 110, 1, 921, 926, 3836, 10489, 21579747, 14123⟩,
    ⟨277, 115, 1, 877, 882, 3788, 10724, 22640838, 13616⟩,
    ⟨277, 125, 1, 793, 798, 3697, 11181, 24797808, 12668⟩,
    ⟨277, 130, 1, 754, 759, 3655, 11402, 25861497, 12233⟩,
    ⟨277, 135, 1, 716, 721, 3614, 11619, 26943855, 11819⟩,
    ⟨277, 140, 1, 680, 685, 3575, 11833, 28015425, 11431⟩,
    ⟨277, 150, 1, 611, 616, 3501, 12248, 30167201, 10701⟩,
    ⟨277, 155, 1, 578, 583, 3465, 12450, 31273005, 10368⟩,
    ⟨277, 160, 1, 546, 551, 3431, 12650, 32354569, 10040⟩,
    ⟨277, 165, 1, 516, 521, 3398, 12846, 33440083, 9744⟩,
    ⟨277, 170, 1, 486, 491, 3366, 13039, 34527471, 9448⟩,
    ⟨277, 175, 1, 457, 462, 3334, 13229, 35650218, 9175⟩,
    ⟨277, 180, 1, 429, 434, 3304, 13417, 36735929, 8906⟩,
    ⟨277, 185, 1, 401, 406, 3274, 13602, 37854704, 8645⟩,
    ⟨277, 195, 1, 349, 354, 3218, 13965, 40035048, 8166⟩,
    ⟨277, 200, 0, 323, 328, 3190, 14143, 41171870, 7936⟩,
    ⟨277, 215, 0, 251, 256, 3112, 14663, 44511842, 7313⟩,
    ⟨277, 225, 0, 205, 210, 3062, 15000, 46794013, 6933⟩,
    ⟨277, 230, 0, 183, 188, 3039, 15166, 47882748, 6748⟩,
    ⟨277, 235, 0, 162, 167, 3016, 15330, 48996814, 6580⟩,
    ⟨277, 240, 0, 141, 146, 2993, 15492, 50136800, 6415⟩,
    ⟨277, 245, 0, 120, 125, 2970, 15653, 51303310, 6254⟩,
    ⟨277, 255, 0, 80, 85, 2927, 15969, 53557469, 5947⟩,
    ⟨277, 260, 0, 61, 66, 2907, 16125, 54639402, 5800⟩,
    ⟨277, 265, 0, 42, 47, 2886, 16279, 55798962, 5663⟩,
    ⟨277, 270, 0, 23, 28, 2866, 16432, 56926176, 5522⟩,
    ⟨277, 275, 0, 5, 10, 2846, 16584, 58076161, 5395⟩,
    ⟨277, 277, 0, -2, 2, 2838, 16644, 58542634, 5347⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell04_rows_check : ∀ r ∈ target028Cell04Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell04Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 277)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell04RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell04Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨277, 277, 0, -2, 2, 2838, 16644, 58542634, 5347⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell04Weight (n : ℕ) : ℚ :=
  ((target028Cell04RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell04_select :
    ∀ n ∈ target028Cell04Prefix,
      1 ≤ n ∧
        target028Cell04RowFor n ∈ target028Cell04Rows ∧
        n ≤ (target028Cell04RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell04RowFor n).b) ∧ (target028Cell04RowFor n).cut = 277 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell04_sum_check :
    (42303 / 10000 : ℚ) <
      ∑ n ∈ target028Cell04Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell04Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell04_principal :
    (42303 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(277 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 277 n).re := by
  have hs : target028Cell04Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell04Prefix ⊆ Finset.Ioc 0 ⌊(277 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell04_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell04Prefix, 0 ≤ target028Cell04Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell04Prefix, (target028Cell04Weight n : ℝ) ≤ refinedScaledWeight 277 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell04_select n hn
    have hcheck := target028_cell04_rows_check (target028Cell04RowFor n) hm
    have hrow := (target028Cell04RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell04RowFor n).b ≤ 277 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 277 (target028Cell04RowFor n).b ≤ refinedScaledWeight 277 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 277) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell04Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 277) target028Cell04Prefix
      target028Cell04Weight hs ht hw0 hw
  have hr :
    ((42303 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell04Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell04Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell04_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell04_budget :
    target028MomentBudget 277 (32304 / 1000) ≤ 4 * (42303 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 277 8 32 0 (56243 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 277 0 (230209 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 277 ≤ (56243 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (277 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (230209 / 100000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (8321 / 500 : ℝ) ≤ Real.sqrt 277 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 277 ≤ (3329 / 200 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 277) (U := 32304 / 1000) (L := 56243 / 10000) (P :=
      230209 / 100000000) (s := 8321 / 500) (t := 3329 / 200) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell04_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (31484 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 32304 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (277 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 277) (U := 32304 / 1000) (S := 42303 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell04_principal) target028_cell04_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
