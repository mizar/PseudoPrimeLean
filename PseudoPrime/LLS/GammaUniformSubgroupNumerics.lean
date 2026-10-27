/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneCommonNumerics
public import PseudoPrime.LLS.GammaUniformLocalBounds
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters

/-! # Uniform scalar and local-loss budgets for the Gamma subgroup bound

The logarithmic ratio is bounded on the full half-line from 46000. Combined
with the prime-support split, this gives a local budget independent of the index.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 42875, log L / L^(1/3) ≤ 11/35 throughout the full half-line.
Use L ≥ 35^3 and the certified bound log 46000 < 11 and log u ≤ u-1 at the cube-root scale.
This controls the small-factor part of the uniform modulus loss. -/
theorem log_div_cuberoot_le_of_ge_42875 {L : ℝ} (hL : 42875 ≤ L) :
    Real.log L / L ^ (1 / 3 : ℝ) ≤ 11 / 35 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ 35 ^ 3)
      (show (35 : ℝ) ^ 3 ≤ L by linarith only [hL]) (by norm_num only : (0 : ℝ) ≤ 1 / 3)
  have he : ((35 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 35 := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 35)]
    norm_num only [Real.rpow_one]
  rw [he] at hc
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have ha :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 35 ^ 3)
      (show (35 : ℝ) ^ 3 ≤ 46000 by norm_num only)
  rw [Real.log_pow] at ha
  norm_num only at ha
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 35))
  rw [Real.log_div hu0.ne' (by norm_num only : (35 : ℝ) ≠ 0), Real.log_rpow hL0] at ht
  rw [div_le_iff₀ hu0]
  linarith only [hc, ha, log_46000_lt_eleven, ht]

/-- For nonzero q and log q ≥ 42875, twice the normalized nonunit exponential
loss at x=(32/99)(log q)^2 and cutoff (99/40)x is at most 4064/315.
Combine the split-prime bound with the full-range logarithmic ratio estimate.
This is the local error shared by every proper-subgroup index. -/
theorem gamma_commonFactor_budget_of_log_ge_42875 {q : ℕ} [NeZero q] (hL : 42875 ≤ Real.log q) :
    let L := Real.log q;
    let x := (32 / 99 : ℝ) * L ^ 2;
    2 *
        (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
          Real.sqrt x) ≤
      4064 / 315 := by
  let L := Real.log q
  let x := (32 / 99 : ℝ) * L ^ 2
  have h1 : 1 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 42875)]
  have hcut : 1 ≤ (99 / 40 : ℝ) * x := by linarith only [hx]
  have hroot := ramp_scale_sqrt_lower (zero_lt_one.trans h1).le
  have ht :=
    gamma_commonFactor_budget_of_ratio_sqrt (by norm_num only : (0 : ℝ) < 9 / 16) h1 hcut hroot
      (log_div_cuberoot_le_of_ge_42875 hL)
  norm_num only at ht
  exact ht

/-- For L ≥ 45731, the fixed error 40159/900 and local allowance 4064/315
sum to less than L/795. Verify the endpoint by rational arithmetic.
This strict budget closes the uniform Gamma main-term comparison. -/
theorem gamma_uniform_error_budget_of_ge_45731 {L : ℝ} (hL : 45731 ≤ L) :
    (40159 / 900 : ℝ) + 4064 / 315 < L / 795 := by linarith only [hL]

/-- For L ≥ 46000, log L / L^(1/3) ≤ 11/35 throughout the full half-line.
Use 35^3 ≤ 46000, log 46000 < 11 and log u ≤ u-1 at the cube-root scale.
This controls the small-factor part of the uniform modulus loss. -/
theorem log_div_cuberoot_le_of_ge_46000 {L : ℝ} (hL : 46000 ≤ L) :
    Real.log L / L ^ (1 / 3 : ℝ) ≤ 11 / 35 := by
  exact log_div_cuberoot_le_of_ge_42875 ((by norm_num only : (42875 : ℝ) ≤ 46000).trans hL)

/-- For nonzero q and log q ≥ 46000, twice the normalized nonunit exponential
loss at x=(32/99)(log q)^2 and cutoff (99/40)x is at most 4064/315.
Combine the split-prime bound with the full-range logarithmic ratio estimate.
This is the local error shared by every proper-subgroup index. -/
theorem gamma_commonFactor_budget_of_log_ge {q : ℕ} [NeZero q] (hL : 46000 ≤ Real.log q) :
    let L := Real.log q;
    let x := (32 / 99 : ℝ) * L ^ 2;
    2 *
        (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
          Real.sqrt x) ≤
      4064 / 315 := by
  exact
    gamma_commonFactor_budget_of_log_ge_42875 ((by norm_num only : (42875 : ℝ) ≤ 46000).trans hL)

/-- For L ≥ 46000, the fixed error 40159/900 and local allowance 4064/315
sum to less than L/795. Verify the endpoint by rational arithmetic.
This strict budget closes the uniform Gamma main-term comparison. -/
theorem gamma_uniform_error_budget {L : ℝ} (hL : 46000 ≤ L) :
    (40159 / 900 : ℝ) + 4064 / 315 < L / 795 := by
  exact gamma_uniform_error_budget_of_ge_45731 ((by norm_num only : (45731 : ℝ) ≤ 46000).trans hL)

end PseudoPrime.Analysis
