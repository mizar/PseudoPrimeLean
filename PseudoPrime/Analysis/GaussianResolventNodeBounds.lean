/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CoshFixedPointBounds
public import PseudoPrime.Analysis.ExponentialFixedPointExecution
public import PseudoPrime.Analysis.GaussianResolventCompact

/-! # Soundness of fixed-point Gaussian resolvent node checks

The squared comparison uses explicit lower cosh and exponential sums at scale 10^40.
Accepted checks imply the required scaled gap for the actual Gaussian norm.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Exact rational scaled majorant at j/1000 minus the required gap 9/100000.
Its nonnegative value is the proposed upper bound for the scaled Gaussian density. -/
def gaussianResolventNodeRadius (j : ℕ) : ℚ :=
  (1 + ((j : ℚ) / 1000) ^ 2) *
      (gaussianResolventCoefficients.map
          (fun ab ↦ ab.2 * (ab.1 / (ab.1 ^ 2 + ((j : ℚ) / 1000) ^ 2)))).sum -
    9 / 100000

/-- The degree-32 even Taylor lower bound at π_lower j/1000, rounded down
at scale 10^40 by the explicit cosh execution API. This supplies a rational node check. -/
def gaussianResolventNodeCoshLower (j : ℕ) : ℚ :=
  (coshFixedPointLowerSumFast (314159265358979323846 * j) (10 ^ 23) (10 ^ 40) 17 : ℚ) / (10 ^ 40)

/-- The 121-term exponential lower bound at (j/1000)²/2, rounded down
at scale 10^40. The explicit execution API is equal to the proved specification. -/
def gaussianResolventNodeExpLower (j : ℕ) : ℚ :=
  (expFixedPointLowerSumFast (j * j) 2000000 (10 ^ 40) 121 : ℚ) / (10 ^ 40)

/-- Boolean check of radius nonnegativity and the squared Gaussian comparison.
Only exact rational and natural arithmetic is evaluated; soundness connects it to the norm. -/
def gaussianResolventNodeCheck (j : ℕ) : Bool :=
  decide
    (0 ≤ gaussianResolventNodeRadius j ∧
      (314159265358979323847 / 10 ^ 20 : ℚ) * (1 + ((j : ℚ) / 1000) ^ 2) ^ 2 ≤
        gaussianResolventNodeRadius j ^ 2 *
          (gaussianResolventNodeCoshLower j * gaussianResolventNodeExpLower j))

/-- The rational radius casts to the real scaled majorant minus 9/100000.
Commute casts with the signed list sum and arithmetic without approximating coefficients. -/
theorem gaussianResolventNodeRadius_cast (j : ℕ) :
    (gaussianResolventNodeRadius j : ℝ) =
      gaussianResolventScaled ((j : ℝ) / 1000) - 9 / 100000 := by
  simp only [gaussianResolventNodeRadius, gaussianResolventScaled, gaussianResolventMajorant,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map]
  congr 2
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _hab
  simp only [Function.comp_apply, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat]

/-- The rational cosh lower bound is at most the actual cosh at the lower π
argument. Apply the fixed-point specification bound through the execution equality. -/
theorem gaussianResolventNodeCoshLower_le (j : ℕ) :
    (gaussianResolventNodeCoshLower j : ℝ) ≤
      Real.cosh ((314159265358979323846 / 10 ^ 20 : ℝ) * ((j : ℝ) / 1000)) := by
  have h := coshFixedPointLowerSum_le_cosh (314159265358979323846 * j) (10 ^ 23) (10 ^ 40) 17
  rw [← coshFixedPointLowerSumFast_eq] at h
  have he :
    ((314159265358979323846 * j : ℕ) : ℝ) / (10 ^ 23 : ℕ) =
      (314159265358979323846 / 10 ^ 20 : ℝ) * ((j : ℝ) / 1000) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [he] at h
  simp only [gaussianResolventNodeCoshLower, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat]
  apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 10 ^ 40)).mpr
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h

/-- The rational exponential lower bound is at most exp((j/1000)²/2).
Apply the fixed-point specification bound through the execution equality. -/
theorem gaussianResolventNodeExpLower_le (j : ℕ) :
    (gaussianResolventNodeExpLower j : ℝ) ≤ Real.exp (((j : ℝ) / 1000) ^ 2 / 2) := by
  have h := expFixedPointLowerSum_le_exp (j * j) 2000000 (10 ^ 40) 121
  rw [← expFixedPointLowerSumFast_eq] at h
  have he : ((j * j : ℕ) : ℝ) / (2000000 : ℕ) = ((j : ℝ) / 1000) ^ 2 / 2 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at h
  simp only [gaussianResolventNodeExpLower, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat]
  apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 10 ^ 40)).mpr
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h

/-- The scaled Gaussian density is nonnegative at every real height.
All polynomial, Gamma norm, and exponential factors are nonnegative. -/
theorem scaledGaussianGammaNorm_nonneg (t : ℝ) : 0 ≤ scaledGaussianGammaNorm t :=
  mul_nonneg
    (mul_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))
      (gammaHalfLineNorm_nonneg t))
    (Real.exp_pos _).le

/-- Squaring the actual density and multiplying by cosh(πt)exp(t²/2) gives
π(1+t²)². Euler reflection and exponential cancellation remove both transcendental factors. -/
theorem scaledGaussianGammaNorm_sq_cosh_exp (t : ℝ) :
    scaledGaussianGammaNorm t ^ 2 * Real.cosh (Real.pi * t) * Real.exp (t ^ 2 / 2) =
      Real.pi * (1 + t ^ 2) ^ 2 := by
  have hG : gammaHalfLineNorm t ^ 2 * Real.cosh (Real.pi * t) = Real.pi := by
    rw [gammaHalfLineNorm, Real.sq_sqrt (div_nonneg Real.pi_pos.le (Real.cosh_pos _).le),
      div_mul_cancel₀ _ (Real.cosh_pos _).ne']
  have hE : gaussianGammaDamping t ^ 2 * Real.exp (t ^ 2 / 2) = 1 := by
    dsimp only [gaussianGammaDamping]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add,
      show -(t ^ 2) / 4 + -(t ^ 2) / 4 + t ^ 2 / 2 = 0 by ring, Real.exp_zero]
  calc
    _ =
        (1 + t ^ 2) ^ 2 * (gammaHalfLineNorm t ^ 2 * Real.cosh (Real.pi * t)) *
          (gaussianGammaDamping t ^ 2 * Real.exp (t ^ 2 / 2)) :=
      by
      dsimp only [scaledGaussianGammaNorm, scaledGammaHalfLineNorm]
      ring
    _ = _ := by rw [hG, hE, mul_one, mul_comm]

/-- A nonnegative radius whose squared comparison holds bounds the actual
scaled Gaussian density. Cancel the positive cosh-exponential product and compare squares. -/
theorem scaledGaussianGammaNorm_le_of_square {t r : ℝ} (hr : 0 ≤ r)
    (h : Real.pi * (1 + t ^ 2) ^ 2 ≤ r ^ 2 * (Real.cosh (Real.pi * t) * Real.exp (t ^ 2 / 2))) :
    scaledGaussianGammaNorm t ≤ r := by
  have h' :
    scaledGaussianGammaNorm t ^ 2 * (Real.cosh (Real.pi * t) * Real.exp (t ^ 2 / 2)) ≤
      r ^ 2 * (Real.cosh (Real.pi * t) * Real.exp (t ^ 2 / 2)) := by
    rw [← mul_assoc, scaledGaussianGammaNorm_sq_cosh_exp]
    exact h
  exact
    (sq_le_sq₀ (scaledGaussianGammaNorm_nonneg t) hr).mp
      ((mul_le_mul_iff_left₀ (mul_pos (Real.cosh_pos _) (Real.exp_pos _))).mp h')

/-- An accepted exact node check implies scaled gap at least 9/100000.
Certified π bounds, lower cosh and exponential sums, and the squared norm identity
justify the comparison. No external numeric verification is trusted. -/
theorem gaussianResolventNodeCheck_sound (j : ℕ) (h : gaussianResolventNodeCheck j = true) :
    (9 / 100000 : ℝ) ≤ gaussianResolventScaledGap ((j : ℝ) / 1000) := by
  have hq := of_decide_eq_true h
  have hr : 0 ≤ (gaussianResolventNodeRadius j : ℝ) := Rat.cast_nonneg.mpr hq.1
  have hn :
    (314159265358979323847 / 10 ^ 20 : ℝ) * (1 + ((j : ℝ) / 1000) ^ 2) ^ 2 ≤
      (gaussianResolventNodeRadius j : ℝ) ^ 2 *
        ((gaussianResolventNodeCoshLower j : ℝ) * (gaussianResolventNodeExpLower j : ℝ)) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq.2
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat] using hcast
  have ht : 0 ≤ (j : ℝ) / 1000 := div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hpLo : (314159265358979323846 / 10 ^ 20 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hpHi : Real.pi ≤ (314159265358979323847 / 10 ^ 20 : ℝ) := by linarith only [Real.pi_lt_d20]
  have hc :
    Real.cosh ((314159265358979323846 / 10 ^ 20 : ℝ) * ((j : ℝ) / 1000)) ≤
      Real.cosh (Real.pi * ((j : ℝ) / 1000)) :=
    Real.cosh_le_cosh.mpr
      (by
        rw [abs_of_nonneg
            (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 314159265358979323846 / 10 ^ 20) ht),
          abs_of_nonneg (mul_nonneg Real.pi_pos.le ht)]
        exact mul_le_mul_of_nonneg_right hpLo ht)
  have he0 : (0 : ℝ) ≤ (gaussianResolventNodeExpLower j : ℝ) := by
    dsimp only [gaussianResolventNodeExpLower]
    exact Rat.cast_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (by norm_num only))
  have hce :=
    mul_le_mul ((gaussianResolventNodeCoshLower_le j).trans hc) (gaussianResolventNodeExpLower_le j)
      he0 (Real.cosh_pos _).le
  have hp := mul_le_mul_of_nonneg_right hpHi (sq_nonneg (1 + ((j : ℝ) / 1000) ^ 2))
  have hb :=
    hp.trans
      (hn.trans (mul_le_mul_of_nonneg_left hce (sq_nonneg (gaussianResolventNodeRadius j : ℝ))))
  have hm := scaledGaussianGammaNorm_le_of_square hr hb
  rw [gaussianResolventNodeRadius_cast] at hm
  change
    9 / 100000 ≤ gaussianResolventScaled ((j : ℝ) / 1000) - scaledGaussianGammaNorm ((j : ℝ) / 1000)
  linarith only [hm]

end PseudoPrime.Analysis
