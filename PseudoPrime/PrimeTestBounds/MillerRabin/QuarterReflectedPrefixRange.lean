/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedLowerBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedPower200
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaLogLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMass

/-! # A uniform reflected Euler prefix saving -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Throughout radii 180 through 200, the reflected Euler prefix through 2701
is at least `7/1000`. Six independently certified moment lower bounds and
endpoint estimates provide the uniform comparison. -/
theorem quarter_reflected_prefix_180_200 {r : ℝ} (hr : 180 ≤ r) (hR : r ≤ 200) :
    (7 / 1000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) n := by
  have hr0 : 0 < r := by linarith only [hr]
  have hlo : (32400 : ℝ) ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 180)]
  have hhi : r ^ 2 ≤ (40000 : ℝ) := by nlinarith only [hr, hR, sq_nonneg (r - 200)]
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by linarith only [hlo]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 32400) hlo
  have hz : (13 : ℝ) ≤ 21 / 8 + Real.log (r ^ 2) := by linarith only [quarter_gamma_log_lower, hl]
  have hp2 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 13) hz 2
  have hp3 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 13) hz 3
  have hp4 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 13) hz 4
  have hp5 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 13) hz 5
  have hpoly :
    quarterMomentLowerPolynomial 13 ≤ quarterMomentLowerPolynomial (21 / 8 + Real.log (r ^ 2)) := by
    dsimp only [quarterMomentLowerPolynomial]
    linarith only [hz, hp2, hp3, hp4, hp5]
  have he : Real.exp (567 / 200 : ℝ) ≤ 18 := by linarith only [refined_six_pole_exp_cutoff]
  have hein := one_div_le_one_div_of_le (Real.exp_pos (567 / 200 : ℝ)) he
  have hexp : (1 / 18 : ℝ) ≤ Real.exp (-((27 / 25 : ℝ) * (21 / 8))) := by
    rw [Real.exp_neg]
    norm_num only at hein ⊢
    simpa only [one_div] using hein
  have hp : (1 / 100000 : ℝ) ≤ (r ^ 2) ^ (-(27 / 25 : ℝ)) :=
    quarter_reflected_power200.trans
      (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr0) hhi (by norm_num only))
  have hpoly0 : 0 ≤ quarterMomentLowerPolynomial 13 := by
    norm_num only [quarterMomentLowerPolynomial]
  have hm := mul_le_mul hexp hp (by norm_num only) (Real.exp_pos _).le
  have hm' :=
    mul_le_mul hm hpoly (by positivity)
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (sq_nonneg r) _))
  have h := quarter_reflected_prefix_lower hr2
  dsimp only [quarterMomentLowerPolynomial] at h hm'
  norm_num only at h hm' ⊢
  nlinarith only [h, hm']

end PseudoPrime.PrimeTestBounds.MillerRabin
