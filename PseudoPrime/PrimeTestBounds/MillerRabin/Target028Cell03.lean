/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 268. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell03Rows : List Target028GeneralWeightRow :=
  [⟨268, 2, 7, 4895, 4900, 8127, 1415, 295453, 61483⟩,
    ⟨268, 3, 6, 4490, 4495, 7690, 1733, 457378, 58923⟩,
    ⟨268, 4, 6, 4202, 4207, 7379, 2000, 624224, 56675⟩,
    ⟨268, 5, 6, 3979, 3984, 7138, 2237, 794339, 54615⟩,
    ⟨268, 7, 5, 3643, 3648, 6775, 2646, 1141970, 51126⟩,
    ⟨268, 8, 5, 3509, 3514, 6631, 2829, 1318843, 49569⟩,
    ⟨268, 9, 5, 3391, 3396, 6503, 3000, 1498935, 48210⟩,
    ⟨268, 15, 4, 2880, 2885, 5951, 3873, 2603235, 41609⟩,
    ⟨268, 20, 4, 2593, 2598, 5641, 4473, 3549317, 37584⟩,
    ⟨268, 25, 3, 2370, 2375, 5400, 5000, 4516580, 34391⟩,
    ⟨268, 30, 3, 2187, 2192, 5203, 5478, 5500039, 31718⟩,
    ⟨268, 35, 3, 2033, 2038, 5037, 5917, 6493198, 29464⟩,
    ⟨268, 40, 3, 1900, 1905, 4893, 6325, 7498892, 27540⟩,
    ⟨268, 45, 3, 1782, 1787, 4765, 6709, 8522888, 25857⟩,
    ⟨268, 50, 2, 1676, 1681, 4651, 7072, 9552045, 24341⟩,
    ⟨268, 55, 2, 1581, 1586, 4548, 7417, 10588359, 23008⟩,
    ⟨268, 60, 2, 1494, 1499, 4454, 7746, 11631946, 21800⟩,
    ⟨268, 65, 2, 1414, 1419, 4368, 8063, 12676568, 20692⟩,
    ⟨268, 70, 2, 1340, 1345, 4288, 8367, 13732362, 19693⟩,
    ⟨268, 75, 2, 1271, 1276, 4214, 8661, 14787101, 18764⟩,
    ⟨268, 80, 2, 1206, 1211, 4143, 8945, 15875154, 17932⟩,
    ⟨268, 85, 2, 1146, 1151, 4079, 9220, 16924381, 17139⟩,
    ⟨268, 90, 2, 1089, 1094, 4017, 9487, 18006904, 16423⟩,
    ⟨268, 100, 1, 983, 988, 3903, 10000, 20181276, 15108⟩,
    ⟨268, 105, 1, 935, 940, 3851, 10247, 21258467, 14525⟩,
    ⟨268, 110, 1, 888, 893, 3800, 10489, 22370771, 13972⟩,
    ⟨268, 115, 1, 844, 849, 3752, 10724, 23470757, 13462⟩,
    ⟨268, 125, 1, 760, 765, 3662, 11181, 25681099, 12498⟩,
    ⟨268, 130, 1, 721, 726, 3620, 11402, 26782676, 12062⟩,
    ⟨268, 135, 1, 683, 688, 3579, 11619, 27903587, 11648⟩,
    ⟨268, 140, 1, 647, 652, 3540, 11833, 29013327, 11259⟩,
    ⟨268, 150, 1, 578, 583, 3465, 12248, 31273005, 10539⟩,
    ⟨268, 155, 1, 545, 550, 3429, 12450, 32419343, 10206⟩,
    ⟨268, 160, 1, 513, 518, 3395, 12650, 33540554, 9878⟩,
    ⟨268, 165, 1, 483, 488, 3363, 12846, 34631209, 9572⟩,
    ⟨268, 170, 1, 453, 458, 3330, 13039, 35793105, 9286⟩,
    ⟨268, 175, 1, 424, 429, 3299, 13229, 36920068, 9004⟩,
    ⟨268, 180, 1, 396, 401, 3269, 13417, 38044452, 8736⟩,
    ⟨268, 185, 1, 368, 373, 3238, 13602, 39242301, 8484⟩,
    ⟨268, 195, 0, 315, 320, 3181, 13965, 41544090, 8000⟩,
    ⟨268, 200, 0, 290, 295, 3154, 14143, 42681060, 7777⟩,
    ⟨268, 215, 0, 218, 223, 3076, 14663, 46143461, 7156⟩,
    ⟨268, 225, 0, 172, 177, 3027, 15000, 48460802, 6771⟩,
    ⟨268, 230, 0, 150, 155, 3003, 15166, 49637930, 6594⟩,
    ⟨268, 235, 0, 129, 134, 2980, 15330, 50792833, 6427⟩,
    ⟨268, 240, 0, 108, 113, 2958, 15492, 51922658, 6257⟩,
    ⟨268, 245, 0, 87, 92, 2935, 15653, 53130719, 6097⟩,
    ⟨268, 255, 0, 47, 52, 2892, 15969, 55465171, 5792⟩,
    ⟨268, 260, 0, 28, 33, 2871, 16125, 56642255, 5652⟩,
    ⟨268, 265, 0, 9, 14, 2851, 16279, 57786505, 5510⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell03_rows_check : ∀ r ∈ target028Cell03Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell03Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 268)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell03RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell03Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨268, 265, 0, 9, 14, 2851, 16279, 57786505, 5510⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell03Weight (n : ℕ) : ℚ :=
  ((target028Cell03RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell03_select :
    ∀ n ∈ target028Cell03Prefix,
      1 ≤ n ∧
        target028Cell03RowFor n ∈ target028Cell03Rows ∧
        n ≤ (target028Cell03RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell03RowFor n).b) ∧ (target028Cell03RowFor n).cut = 268 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell03_sum_check :
    (8227 / 2000 : ℚ) <
      ∑ n ∈ target028Cell03Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell03Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell03_principal :
    (8227 / 2000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(268 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 268 n).re := by
  have hs : target028Cell03Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell03Prefix ⊆ Finset.Ioc 0 ⌊(268 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell03_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell03Prefix, 0 ≤ target028Cell03Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell03Prefix, (target028Cell03Weight n : ℝ) ≤ refinedScaledWeight 268 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell03_select n hn
    have hcheck := target028_cell03_rows_check (target028Cell03RowFor n) hm
    have hrow := (target028Cell03RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell03RowFor n).b ≤ 268 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 268 (target028Cell03RowFor n).b ≤ refinedScaledWeight 268 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 268) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell03Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 268) target028Cell03Prefix
      target028Cell03Weight hs ht hw0 hw
  have hr :
    ((8227 / 2000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell03Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell03Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell03_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell03_budget :
    target028MomentBudget 268 (31484 / 1000) ≤ 4 * (8227 / 2000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 268 8 32 0 (6989 / 1250) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 268 0 (477139 / 200000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 268 ≤ (6989 / 1250 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (268 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (477139 / 200000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (16369 / 1000 : ℝ) ≤ Real.sqrt 268 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 268 ≤ (4093 / 250 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 268) (U := 31484 / 1000) (L := 6989 / 1250) (P :=
      477139 / 200000000) (s := 16369 / 1000) (t := 4093 / 250) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell03_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (30960 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 31484 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (268 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 268) (U := 31484 / 1000) (S := 8227 / 2000) (by norm_num only) hU hcut
      (le_of_lt target028_cell03_principal) target028_cell03_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
