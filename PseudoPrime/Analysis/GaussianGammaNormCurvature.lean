/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCriticalLineDerivatives
public import PseudoPrime.Analysis.GaussianGammaKernel

/-! # Curvature of the Gaussian-weighted critical-line Gamma norm

The scaled density has absolute second derivative at most 40 on the nonnegative
half-line. This supplies the target curvature in the Gaussian resolvent certificate.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative u and every natural degree k, the exponential tangent at one bounds
(8u/3)^k exp(-ku) by one. This supplies explicit polynomial decay moments. -/
theorem exponential_moment_tangent_bound {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    (8 / 3 * u) ^ k * Real.exp (-(k : ℝ) * u) ≤ 1 := by
  have hb := Real.add_one_le_exp (u - 1)
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := mul_le_mul he hb (by linarith only [hu] : 0 ≤ u - 1 + 1) (Real.exp_pos _).le
  rw [← Real.exp_add, show (1 + (u - 1) : ℝ) = u by ring] at hp
  have hp' : 8 / 3 * u ≤ Real.exp u := by linarith only [hp]
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8 / 3) hu) hp' k
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(k : ℝ) * u)).le
  have hx : Real.exp u ^ k * Real.exp (-(k : ℝ) * u) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, show (k : ℝ) * u + -(k : ℝ) * u = 0 by ring,
      Real.exp_zero]
  rw [hx] at hm
  exact hm

/-- At nonnegative height, t³ exp(-3t/2)≤27/64. Specialize the exponential
tangent moment to degree three; this controls Gaussian product-rule curvature. -/
theorem gaussian_cubic_exp_decay_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ 3 * Real.exp (-(3 / 2) * t) ≤ 27 / 64 := by
  have h := exponential_moment_tangent_bound (div_nonneg ht (by norm_num only : (0 : ℝ) ≤ 2)) 3
  norm_num only [Nat.cast_ofNat] at h
  have he : -(3 : ℝ) * (t / 2) = -(3 / 2) * t := by ring
  rw [he] at h
  nlinarith only [h]

/-- At nonnegative height, t⁴ exp(-3t/2)≤1. Specialize the exponential
tangent moment to degree four; this controls the quadratic Gaussian factor. -/
theorem gaussian_quartic_exp_decay_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ 4 * Real.exp (-(3 / 2) * t) ≤ 1 := by
  have h := exponential_moment_tangent_bound (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 8) ht) 4
  norm_num only [Nat.cast_ofNat] at h
  have he : -(4 : ℝ) * (3 / 8 * t) = -(3 / 2) * t := by ring
  rw [he] at h
  nlinarith only [h]

/-- The critical-line Gaussian factor exp(-t²/4). It multiplies the Gamma
norm density in the fixed Gaussian Mellin kernel. -/
noncomputable def gaussianGammaDamping (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / 4)

/-- The damping has derivative -t exp(-t²/4)/2 at every real height.
Differentiate its quadratic exponent for the weighted density product rule. -/
theorem hasDerivAt_gaussianGammaDamping (t : ℝ) :
    HasDerivAt gaussianGammaDamping (-t / 2 * gaussianGammaDamping t) t := by
  have h := (((hasDerivAt_id t).pow 2).neg.div_const 4).exp
  change
    HasDerivAt gaussianGammaDamping (gaussianGammaDamping t * (-(2 * t ^ (2 - 1) * 1) / 4)) t at h
  have he :
    -t / 2 * gaussianGammaDamping t = gaussianGammaDamping t * (-(2 * t ^ (2 - 1) * 1) / 4) := by
    ring
  rw [he]
  exact h

/-- The scaled critical-line Gaussian norm (1+t²)|Γ(1/2+it)|exp(-t²/4).
This is the target of the rational resolvent interpolation certificate. -/
noncomputable def scaledGaussianGammaNorm (t : ℝ) : ℝ :=
  scaledGammaHalfLineNorm t * gaussianGammaDamping t

/-- At every real height, the scaled density is (1+t²) times the actual Gaussian
kernel norm on the imaginary axis. The exact vertical norm and Euler reflection
identify the differentiated density with the zero-mass target. -/
theorem scaledGaussianGammaNorm_eq_kernel_norm (t : ℝ) :
    scaledGaussianGammaNorm t = (1 + t ^ 2) * ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ := by
  have h := norm_gaussianGammaFunction_vertical 0 t
  simp only [Complex.ofReal_zero, zero_add, zero_pow (by decide : 2 ≠ 0), zero_sub,
    add_comm (Complex.I * (t : ℂ)) (1 / 2), norm_Gamma_half_add_I] at h
  rw [h]
  exact mul_assoc _ _ _

/-- Product-rule first derivative of the scaled Gaussian norm.
Subtract t/2 times the scaled Gamma density before multiplying by damping. -/
noncomputable def scaledGaussianGammaNormDeriv (t : ℝ) : ℝ :=
  (scaledGammaHalfLineNormDeriv t - t / 2 * scaledGammaHalfLineNorm t) * gaussianGammaDamping t

/-- Product-rule second derivative of the scaled Gaussian norm.
Its three terms contain Gamma curvature, the cross term, and Gaussian curvature. -/
noncomputable def scaledGaussianGammaNormSecondDeriv (t : ℝ) : ℝ :=
  (scaledGammaHalfLineNormSecondDeriv t - t * scaledGammaHalfLineNormDeriv t +
      (t ^ 2 / 4 - 1 / 2) * scaledGammaHalfLineNorm t) *
    gaussianGammaDamping t

/-- At every height, the stated first derivative differentiates the weighted norm.
Apply the product rule to the existing scaled Gamma density and Gaussian damping. -/
theorem hasDerivAt_scaledGaussianGammaNorm (t : ℝ) :
    HasDerivAt scaledGaussianGammaNorm (scaledGaussianGammaNormDeriv t) t := by
  have h := (hasDerivAt_scaledGammaHalfLineNorm t).mul (hasDerivAt_gaussianGammaDamping t)
  change
    HasDerivAt scaledGaussianGammaNorm
      (scaledGammaHalfLineNormDeriv t * gaussianGammaDamping t +
        scaledGammaHalfLineNorm t * (-t / 2 * gaussianGammaDamping t))
      t at h
  have he :
    scaledGaussianGammaNormDeriv t =
      scaledGammaHalfLineNormDeriv t * gaussianGammaDamping t +
        scaledGammaHalfLineNorm t * (-t / 2 * gaussianGammaDamping t) := by
    dsimp only [scaledGaussianGammaNormDeriv]
    ring
  rw [he]
  exact h

/-- At every height, the stated second derivative differentiates the first.
Differentiate both products and collect the Gaussian cross terms. -/
theorem hasDerivAt_scaledGaussianGammaNormDeriv (t : ℝ) :
    HasDerivAt scaledGaussianGammaNormDeriv (scaledGaussianGammaNormSecondDeriv t) t := by
  have hp :=
    (hasDerivAt_scaledGammaHalfLineNormDeriv t).sub
      (((hasDerivAt_id t).div_const 2).mul (hasDerivAt_scaledGammaHalfLineNorm t))
  have h := hp.mul (hasDerivAt_gaussianGammaDamping t)
  change
    HasDerivAt scaledGaussianGammaNormDeriv
      ((scaledGammaHalfLineNormSecondDeriv t -
            (1 / 2 * scaledGammaHalfLineNorm t + t / 2 * scaledGammaHalfLineNormDeriv t)) *
          gaussianGammaDamping t +
        (scaledGammaHalfLineNormDeriv t - t / 2 * scaledGammaHalfLineNorm t) *
          (-t / 2 * gaussianGammaDamping t))
      t at h
  have he :
    scaledGaussianGammaNormSecondDeriv t =
      (scaledGammaHalfLineNormSecondDeriv t -
            (1 / 2 * scaledGammaHalfLineNorm t + t / 2 * scaledGammaHalfLineNormDeriv t)) *
          gaussianGammaDamping t +
        (scaledGammaHalfLineNormDeriv t - t / 2 * scaledGammaHalfLineNorm t) *
          (-t / 2 * gaussianGammaDamping t) := by
    dsimp only [scaledGaussianGammaNormSecondDeriv]
    ring
  rw [he]
  exact h

/-- At nonnegative height, t exp(-3t/2)≤1/4. The degree-one exponential
tangent bound controls the first moment in weighted curvature. -/
theorem gaussian_linear_exp_decay_le {t : ℝ} (ht : 0 ≤ t) :
    t * Real.exp (-(3 / 2) * t) ≤ 1 / 4 := by
  have h := exponential_moment_tangent_bound (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 2) ht) 1
  norm_num only [Nat.cast_one, pow_one] at h
  have he : -(1 : ℝ) * (3 / 2 * t) = -(3 / 2) * t := by ring
  rw [he] at h
  nlinarith only [h]

/-- At nonnegative height, t² exp(-3t/2)≤1/4. The degree-two exponential
tangent bound controls the second moment in weighted curvature. -/
theorem gaussian_quadratic_exp_decay_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-(3 / 2) * t) ≤ 1 / 4 := by
  have h := exponential_moment_tangent_bound (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) ht) 2
  norm_num only [Nat.cast_ofNat] at h
  have he : -(2 : ℝ) * (3 / 4 * t) = -(3 / 2) * t := by ring
  rw [he] at h
  nlinarith only [h]

/-- At nonnegative height, the scaled Gamma first derivative has absolute value
at most (2t+2(1+t²)) times the Gamma density. Use |Γ|'≤π|Γ|/2 and π<4. -/
theorem abs_scaledGammaHalfLineNormDeriv_bound {t : ℝ} (ht : 0 ≤ t) :
    |scaledGammaHalfLineNormDeriv t| ≤ (2 * t + 2 * (1 + t ^ 2)) * gammaHalfLineNorm t := by
  have h := abs_add_le (2 * t * gammaHalfLineNorm t) ((1 + t ^ 2) * gammaHalfLineNormDeriv t)
  have hp : Real.pi / 2 ≤ 2 := by linarith only [Real.pi_lt_four]
  have hb :=
    (abs_gammaHalfLineNormDeriv_le t).trans
      (mul_le_mul_of_nonneg_right hp (gammaHalfLineNorm_nonneg t))
  have hm :=
    mul_le_mul_of_nonneg_left hb (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))
  dsimp only [scaledGammaHalfLineNormDeriv]
  simp only [abs_mul, abs_of_nonneg ht, abs_of_nonneg (gammaHalfLineNorm_nonneg t),
    abs_of_pos (by norm_num only : (0 : ℝ) < 2),
    abs_of_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))] at h
  nlinarith only [h, hm]

/-- For nonnegative height, an exponential moment bound C gives the Gamma
norm moment bound 3C. Apply the existing critical-line exponential decay. -/
theorem gamma_norm_moment_le_of_exp_bound {t C : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (hm : t ^ k * Real.exp (-(3 / 2) * t) ≤ C) : t ^ k * gammaHalfLineNorm t ≤ 3 * C := by
  have h := mul_le_mul_of_nonneg_left (gammaHalfLineNorm_le_exp ht) (pow_nonneg ht k)
  nlinarith only [h, hm]

/-- At nonnegative height, the weighted curvature is bounded by 30 plus a quartic
polynomial times the Gamma density. Use product rules, absolute-value bounds, and damping≤1. -/
theorem abs_scaledGaussianGammaNormSecondDeriv_le_polynomial {t : ℝ} (ht : 0 ≤ t) :
    |scaledGaussianGammaNormSecondDeriv t| ≤
      30 + (1 / 2 + 2 * t + 11 / 4 * t ^ 2 + 2 * t ^ 3 + t ^ 4 / 4) * gammaHalfLineNorm t := by
  have hab : |t ^ 2 / 4 - 1 / 2| ≤ t ^ 2 / 4 + 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg t]
  have hS : 0 ≤ scaledGammaHalfLineNorm t :=
    mul_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))
      (gammaHalfLineNorm_nonneg t)
  have h :=
    (abs_add_le (scaledGammaHalfLineNormSecondDeriv t - t * scaledGammaHalfLineNormDeriv t)
          ((t ^ 2 / 4 - 1 / 2) * scaledGammaHalfLineNorm t)).trans
      (add_le_add_left
        (abs_sub (scaledGammaHalfLineNormSecondDeriv t) (t * scaledGammaHalfLineNormDeriv t))
        |(t ^ 2 / 4 - 1 / 2) * scaledGammaHalfLineNorm t|)
  simp only [abs_mul, abs_of_nonneg ht, abs_of_nonneg hS] at h
  have h1 := mul_le_mul_of_nonneg_left (abs_scaledGammaHalfLineNormDeriv_bound ht) ht
  have h2 := mul_le_mul_of_nonneg_right hab hS
  have h2' :
    |t ^ 2 / 4 - 1 / 2| * scaledGammaHalfLineNorm t ≤
      (t ^ 4 / 4 + 3 / 4 * t ^ 2 + 1 / 2) * gammaHalfLineNorm t := by
    dsimp only [scaledGammaHalfLineNorm] at h2 ⊢
    nlinarith only [h2]
  have hp :
    |scaledGammaHalfLineNormSecondDeriv t - t * scaledGammaHalfLineNormDeriv t +
          (t ^ 2 / 4 - 1 / 2) * scaledGammaHalfLineNorm t| ≤
      30 + (1 / 2 + 2 * t + 11 / 4 * t ^ 2 + 2 * t ^ 3 + t ^ 4 / 4) * gammaHalfLineNorm t := by
    nlinarith only [h, h1, h2', abs_scaledGammaHalfLineNormSecondDeriv_le_thirty ht]
  have he : gaussianGammaDamping t ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t])
  dsimp only [scaledGaussianGammaNormSecondDeriv]
  rw [abs_mul, abs_of_pos (show 0 < gaussianGammaDamping t from Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans (by simpa only [mul_one] using hp)

/-- At every nonnegative height, the weighted norm has absolute second derivative
at most 40. Combine the quartic polynomial estimate with four explicit decay moments.
This is stronger than the curvature allowance 74 required by the resolvent grid. -/
theorem abs_scaledGaussianGammaNormSecondDeriv_le_forty {t : ℝ} (ht : 0 ≤ t) :
    |scaledGaussianGammaNormSecondDeriv t| ≤ 40 := by
  have he : Real.exp (-(3 / 2) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht])
  have h0 := gamma_norm_moment_le_of_exp_bound ht 0 (by simpa only [pow_zero, one_mul] using he)
  have h1 :=
    gamma_norm_moment_le_of_exp_bound ht 1
      (by simpa only [pow_one] using gaussian_linear_exp_decay_le ht)
  have h2 := gamma_norm_moment_le_of_exp_bound ht 2 (gaussian_quadratic_exp_decay_le ht)
  have h3 := gamma_norm_moment_le_of_exp_bound ht 3 (gaussian_cubic_exp_decay_le ht)
  have h4 := gamma_norm_moment_le_of_exp_bound ht 4 (gaussian_quartic_exp_decay_le ht)
  norm_num only [pow_zero, pow_one, one_mul] at h0 h1
  nlinarith only [abs_scaledGaussianGammaNormSecondDeriv_le_polynomial ht, h0, h1, h2, h3, h4]

end PseudoPrime.Analysis
