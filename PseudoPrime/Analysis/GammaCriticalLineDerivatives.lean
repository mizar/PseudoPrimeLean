/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCriticalLine
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Real derivatives and curvature of the Gamma norm on Re s=1/2

Euler reflection reduces the norm to a positive real square root. Its scaled
second derivative has absolute value at most 30 on the nonnegative half-line.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Euler reflection's real expression sqrt(π/cosh(πt)) for the Gamma norm on
Re s=1/2. It is positive at every real height; differentiation uses real calculus. -/
noncomputable def gammaHalfLineNorm (t : ℝ) : ℝ :=
  Real.sqrt (Real.pi / Real.cosh (Real.pi * t))

/-- The real Gamma density has derivative -π tanh(πt)h(t)/2 at every t.
Differentiate sqrt(π/cosh(πt)) and use its positive square-root identity. -/
theorem hasDerivAt_gammaHalfLineNorm (t : ℝ) :
    HasDerivAt gammaHalfLineNorm (-Real.pi / 2 * Real.tanh (Real.pi * t) * gammaHalfLineNorm t)
      t := by
  have hp : 0 < Real.pi / Real.cosh (Real.pi * t) :=
    div_pos Real.pi_pos (Real.cosh_pos (Real.pi * t))
  have hc := (Real.hasDerivAt_cosh (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
  have hq := (hasDerivAt_const t Real.pi).div hc (Real.cosh_pos (Real.pi * t)).ne'
  have hs := hq.sqrt hp.ne'
  change
    HasDerivAt gammaHalfLineNorm
      ((0 * Real.cosh (Real.pi * t) - Real.pi * (Real.sinh (Real.pi * t) * (Real.pi * 1))) /
        Real.cosh (Real.pi * t) ^ 2 /
        (2 * gammaHalfLineNorm t))
      t at hs
  have he :
    -Real.pi / 2 * Real.tanh (Real.pi * t) * gammaHalfLineNorm t =
      ((0 * Real.cosh (Real.pi * t) - Real.pi * (Real.sinh (Real.pi * t) * (Real.pi * 1))) /
        Real.cosh (Real.pi * t) ^ 2 /
        (2 * gammaHalfLineNorm t)) := by
    have hg : gammaHalfLineNorm t ^ 2 * Real.cosh (Real.pi * t) = Real.pi := by
      rw [gammaHalfLineNorm, Real.sq_sqrt hp.le, div_mul_cancel₀ _ (Real.cosh_pos _).ne']
    have hg0 : gammaHalfLineNorm t ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp (discharger :=
      first
      | exact hg0
      | exact (Real.cosh_pos _).ne')
    have hm := congrArg (fun y : ℝ ↦ -Real.pi * Real.sinh (Real.pi * t) * y / 2) hg
    nlinarith only [hm]
  rw [he]
  exact hs

/-- The derivative of tanh(πt) is π/cosh(πt)². Differentiate sinh/cosh
and use cosh²-sinh²=1. This supplies the second derivative of the Gamma density. -/
private theorem hasDerivAt_tanh_pi_mul (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.tanh (Real.pi * x)) (Real.pi / Real.cosh (Real.pi * t) ^ 2) t := by
  have hs := (Real.hasDerivAt_sinh (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
  have hc := (Real.hasDerivAt_cosh (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
  have h := hs.div hc (Real.cosh_pos (Real.pi * t)).ne'
  have he :
    Real.pi =
      Real.cosh (Real.pi * t) * (Real.pi * 1) * Real.cosh (Real.pi * t) -
        Real.sinh (Real.pi * t) * (Real.sinh (Real.pi * t) * (Real.pi * 1)) := by
    have hm := congrArg (fun y : ℝ ↦ Real.pi * y) (Real.cosh_sq_sub_sinh_sq (Real.pi * t))
    nlinarith only [hm]
  change
    HasDerivAt (fun x ↦ Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x))
      ((Real.cosh (Real.pi * t) * (Real.pi * 1) * Real.cosh (Real.pi * t) -
          Real.sinh (Real.pi * t) * (Real.sinh (Real.pi * t) * (Real.pi * 1))) /
        Real.cosh (Real.pi * t) ^ 2)
      t at h
  simp only [Real.tanh_eq_sinh_div_cosh]
  rw [← he] at h
  exact h

/-- First derivative of the Gamma norm density, -π tanh(πt) h(t)/2.
The derivative theorem follows from the square-root and quotient rules. -/
noncomputable def gammaHalfLineNormDeriv (t : ℝ) : ℝ :=
  -Real.pi / 2 * Real.tanh (Real.pi * t) * gammaHalfLineNorm t

/-- Second derivative of the Gamma norm density, π²(1-3/cosh(πt)²)h(t)/4.
This expression makes its absolute value accessible to real inequalities. -/
noncomputable def gammaHalfLineNormSecondDeriv (t : ℝ) : ℝ :=
  Real.pi ^ 2 / 4 * (1 - 3 / Real.cosh (Real.pi * t) ^ 2) * gammaHalfLineNorm t

/-- The stated rational-hyperbolic second derivative differentiates the
Gamma density's first derivative. Apply the product rule and cosh²-sinh²=1. -/
theorem hasDerivAt_gammaHalfLineNormDeriv (t : ℝ) :
    HasDerivAt gammaHalfLineNormDeriv (gammaHalfLineNormSecondDeriv t) t := by
  have h :=
    ((hasDerivAt_tanh_pi_mul t).const_mul (-Real.pi / 2)).mul (hasDerivAt_gammaHalfLineNorm t)
  change
    HasDerivAt gammaHalfLineNormDeriv
      (-Real.pi / 2 * (Real.pi / Real.cosh (Real.pi * t) ^ 2) * gammaHalfLineNorm t +
        (-Real.pi / 2 * Real.tanh (Real.pi * t)) *
          (-Real.pi / 2 * Real.tanh (Real.pi * t) * gammaHalfLineNorm t))
      t at h
  have he :
    gammaHalfLineNormSecondDeriv t =
      -Real.pi / 2 * (Real.pi / Real.cosh (Real.pi * t) ^ 2) * gammaHalfLineNorm t +
        (-Real.pi / 2 * Real.tanh (Real.pi * t)) *
          (-Real.pi / 2 * Real.tanh (Real.pi * t) * gammaHalfLineNorm t) := by
    dsimp only [gammaHalfLineNormSecondDeriv]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp (discharger :=
      first
      | (norm_num only; done)
      | exact (Real.cosh_pos _).ne')
    have hm :=
      congrArg (fun y : ℝ ↦ Real.pi ^ 2 * gammaHalfLineNorm t * y)
        (Real.cosh_sq_sub_sinh_sq (Real.pi * t))
    nlinarith only [hm]
  rw [he]
  exact h

/-- The Gamma density is nonnegative because it is a real square root.
This permits multiplication of its derivative and decay estimates. -/
theorem gammaHalfLineNorm_nonneg (t : ℝ) : 0 ≤ gammaHalfLineNorm t :=
  Real.sqrt_nonneg _

/-- At every height, the absolute first derivative is at most πh(t)/2.
Use |tanh|<1 and nonnegativity of the density when bounding scaled curvature. -/
theorem abs_gammaHalfLineNormDeriv_le (t : ℝ) :
    |gammaHalfLineNormDeriv t| ≤ Real.pi / 2 * gammaHalfLineNorm t := by
  dsimp only [gammaHalfLineNormDeriv]
  rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
    abs_of_pos (by norm_num only : (0 : ℝ) < 2), abs_of_nonneg (gammaHalfLineNorm_nonneg t)]
  have h :=
    mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one (Real.pi * t)).le
      (div_nonneg Real.pi_pos.le (by norm_num only : (0 : ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_right h (gammaHalfLineNorm_nonneg t)
  simpa only [mul_one] using hm

/-- The absolute second derivative is at most π²h(t)/2 at every height.
Since cosh²≥1, the multiplier 1-3/cosh² lies between -2 and 1. -/
theorem abs_gammaHalfLineNormSecondDeriv_le (t : ℝ) :
    |gammaHalfLineNormSecondDeriv t| ≤ Real.pi ^ 2 / 2 * gammaHalfLineNorm t := by
  have hc : 1 ≤ Real.cosh (Real.pi * t) ^ 2 := one_le_pow₀ (Real.one_le_cosh (Real.pi * t))
  have hz : 0 ≤ 3 / Real.cosh (Real.pi * t) ^ 2 := div_nonneg (by norm_num only) (sq_nonneg _)
  have hu : 3 / Real.cosh (Real.pi * t) ^ 2 ≤ 3 :=
    (div_le_iff₀ (pow_pos (Real.cosh_pos _) 2)).mpr (by linarith only [hc])
  have hab : |1 - 3 / Real.cosh (Real.pi * t) ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith only [hz, hu]
  dsimp only [gammaHalfLineNormSecondDeriv]
  rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ 4)),
    abs_of_nonneg (gammaHalfLineNorm_nonneg t)]
  have hm :=
    mul_le_mul_of_nonneg_left hab (div_nonneg (sq_nonneg Real.pi) (by norm_num only : (0 : ℝ) ≤ 4))
  have h := mul_le_mul_of_nonneg_right hm (gammaHalfLineNorm_nonneg t)
  nlinarith only [h]

/-- The Gamma norm density multiplied by 1+t². This scaling matches the
signed resolvent certificate and its uniform curvature estimate. -/
noncomputable def scaledGammaHalfLineNorm (t : ℝ) : ℝ :=
  (1 + t ^ 2) * gammaHalfLineNorm t

/-- Product-rule first derivative of the scaled Gamma norm density.
It combines the polynomial derivative with the density's first derivative. -/
noncomputable def scaledGammaHalfLineNormDeriv (t : ℝ) : ℝ :=
  2 * t * gammaHalfLineNorm t + (1 + t ^ 2) * gammaHalfLineNormDeriv t

/-- Product-rule second derivative of the scaled Gamma norm density.
Its three terms are bounded by a polynomial times an exponentially decaying density. -/
noncomputable def scaledGammaHalfLineNormSecondDeriv (t : ℝ) : ℝ :=
  2 * gammaHalfLineNorm t + 4 * t * gammaHalfLineNormDeriv t +
    (1 + t ^ 2) * gammaHalfLineNormSecondDeriv t

/-- The product-rule expression differentiates the scaled Gamma density.
Combine the polynomial derivative with the density's actual first derivative. -/
theorem hasDerivAt_scaledGammaHalfLineNorm (t : ℝ) :
    HasDerivAt scaledGammaHalfLineNorm (scaledGammaHalfLineNormDeriv t) t := by
  have h :=
    ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_gammaHalfLineNorm t)
  change
    HasDerivAt scaledGammaHalfLineNorm
      ((0 + 2 * t ^ (2 - 1) * 1) * gammaHalfLineNorm t + (1 + t ^ 2) * gammaHalfLineNormDeriv t)
      t at h
  have he :
    scaledGammaHalfLineNormDeriv t =
      (0 + 2 * t ^ (2 - 1) * 1) * gammaHalfLineNorm t + (1 + t ^ 2) * gammaHalfLineNormDeriv t := by
    dsimp only [scaledGammaHalfLineNormDeriv]; ring
  rw [he]
  exact h

/-- The stated second-derivative expression differentiates the scaled first
derivative. Differentiate both products and collect the two cross terms. -/
theorem hasDerivAt_scaledGammaHalfLineNormDeriv (t : ℝ) :
    HasDerivAt scaledGammaHalfLineNormDeriv (scaledGammaHalfLineNormSecondDeriv t) t := by
  have h :=
    (((hasDerivAt_id t).const_mul 2).mul (hasDerivAt_gammaHalfLineNorm t)).add
      (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).mul
        (hasDerivAt_gammaHalfLineNormDeriv t))
  change
    HasDerivAt scaledGammaHalfLineNormDeriv
      (2 * 1 * gammaHalfLineNorm t + (2 * t) * gammaHalfLineNormDeriv t +
        ((0 + 2 * t ^ (2 - 1) * 1) * gammaHalfLineNormDeriv t +
          (1 + t ^ 2) * gammaHalfLineNormSecondDeriv t))
      t at h
  have he :
    scaledGammaHalfLineNormSecondDeriv t =
      2 * 1 * gammaHalfLineNorm t + (2 * t) * gammaHalfLineNormDeriv t +
        ((0 + 2 * t ^ (2 - 1) * 1) * gammaHalfLineNormDeriv t +
          (1 + t ^ 2) * gammaHalfLineNormSecondDeriv t) := by
    dsimp only [scaledGammaHalfLineNormSecondDeriv]
    ring
  rw [he]
  exact h

/-- At nonnegative t, the scaled density's absolute second derivative is at
most (7+7t+5t²)h(t). Apply the triangle inequality and the bounds 2π≤7, π²/2≤5. -/
theorem abs_scaledGammaHalfLineNormSecondDeriv_le_polynomial {t : ℝ} (ht : 0 ≤ t) :
    |scaledGammaHalfLineNormSecondDeriv t| ≤ (7 + 7 * t + 5 * t ^ 2) * gammaHalfLineNorm t := by
  have hb :=
    (abs_add_le (2 * gammaHalfLineNorm t + 4 * t * gammaHalfLineNormDeriv t)
          ((1 + t ^ 2) * gammaHalfLineNormSecondDeriv t)).trans
      (add_le_add_left (abs_add_le (2 * gammaHalfLineNorm t) (4 * t * gammaHalfLineNormDeriv t))
        |(1 + t ^ 2) * gammaHalfLineNormSecondDeriv t|)
  have hb' :
    |scaledGammaHalfLineNormSecondDeriv t| ≤
      2 * gammaHalfLineNorm t + 4 * t * |gammaHalfLineNormDeriv t| +
        (1 + t ^ 2) * |gammaHalfLineNormSecondDeriv t| := by
    dsimp only [scaledGammaHalfLineNormSecondDeriv]
    simpa only [abs_mul, abs_of_nonneg ht, abs_of_nonneg (gammaHalfLineNorm_nonneg t),
      abs_of_pos (by norm_num only : (0 : ℝ) < 2), abs_of_pos (by norm_num only : (0 : ℝ) < 4),
      abs_of_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))] using hb
  have h1 :=
    mul_le_mul_of_nonneg_left (abs_gammaHalfLineNormDeriv_le t)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) ht)
  have h2 :=
    mul_le_mul_of_nonneg_left (abs_gammaHalfLineNormSecondDeriv_le t)
      (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))
  have hp : 2 * Real.pi ≤ 7 := by linarith only [Real.pi_lt_d4]
  have hp2 : Real.pi ^ 2 / 2 ≤ 5 := by nlinarith only [Real.pi_lt_d4, Real.pi_pos]
  have hpi := mul_le_mul_of_nonneg_right hp (mul_nonneg ht (gammaHalfLineNorm_nonneg t))
  have hpi2 :=
    mul_le_mul_of_nonneg_right hp2
      (mul_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))
        (gammaHalfLineNorm_nonneg t))
  nlinarith only [hb', h1, h2, hpi, hpi2]

/-- For nonnegative height t, the Gamma density is at most 3 exp(-3t/2).
Euler reflection supplies exponential decay; 3<π<4 bounds its rate and prefactor. -/
theorem gammaHalfLineNorm_le_exp {t : ℝ} (ht : 0 ≤ t) :
    gammaHalfLineNorm t ≤ 3 * Real.exp (-(3 / 2) * t) := by
  have h : gammaHalfLineNorm t ≤ Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) := by
    rw [gammaHalfLineNorm, ← norm_Gamma_half_add_I]
    exact norm_Gamma_half_add_I_le_exp t
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by linarith only [Real.pi_lt_four]⟩
  have he : Real.exp (-|Real.pi * t| / 2) ≤ Real.exp (-(3 / 2) * t) := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le ht)]
    exact Real.exp_le_exp.mpr (by nlinarith only [Real.pi_gt_three, ht])
  exact h.trans (mul_le_mul hsqrt he (Real.exp_pos _).le (by norm_num only))

/-- For nonnegative t, t exp(-3t/2)≤1/4. The tangent inequality for exp
at 1 and the rational lower bound exp(1)≥8/3 control the linear moment. -/
private theorem linear_exp_decay_le_quarter {t : ℝ} (ht : 0 ≤ t) :
    t * Real.exp (-(3 / 2) * t) ≤ 1 / 4 := by
  have hb := Real.add_one_le_exp (3 / 2 * t - 1)
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := mul_le_mul he hb (by linarith only [ht] : 0 ≤ 3 / 2 * t - 1 + 1) (Real.exp_pos _).le
  rw [← Real.exp_add, show (1 + (3 / 2 * t - 1) : ℝ) = 3 / 2 * t by ring] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(3 / 2) * t)).le
  have hx : Real.exp (3 / 2 * t) * Real.exp (-(3 / 2) * t) = 1 := by
    rw [← Real.exp_add, show (3 / 2 * t + -(3 / 2) * t : ℝ) = 0 by ring, Real.exp_zero]
  rw [hx] at hm
  nlinarith only [hm]

/-- For nonnegative t, t² exp(-3t/2)≤1/4. Square the tangent estimate
at 3t/4 and cancel exponentials. This bounds the quadratic curvature term. -/
private theorem quadratic_exp_decay_le_quarter {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-(3 / 2) * t) ≤ 1 / 4 := by
  have hb := Real.add_one_le_exp (3 / 4 * t - 1)
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := mul_le_mul he hb (by linarith only [ht] : 0 ≤ 3 / 4 * t - 1 + 1) (Real.exp_pos _).le
  rw [← Real.exp_add, show (1 + (3 / 4 * t - 1) : ℝ) = 3 / 4 * t by ring] at hp
  have hs := pow_le_pow_left₀ (by nlinarith only [ht] : 0 ≤ 8 / 3 * (3 / 4 * t - 1 + 1)) hp 2
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(3 / 2) * t)).le
  have hx : Real.exp (3 / 4 * t) ^ 2 * Real.exp (-(3 / 2) * t) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  rw [hx] at hm
  nlinarith only [hm]

/-- At every nonnegative height, the scaled Gamma norm's absolute second
derivative is at most 30. Combine exponential decay with the zeroth, first and second
moment bounds. Together with resolvent curvature below 24, this gives the gap bound 54. -/
theorem abs_scaledGammaHalfLineNormSecondDeriv_le_thirty {t : ℝ} (ht : 0 ≤ t) :
    |scaledGammaHalfLineNormSecondDeriv t| ≤ 30 := by
  have hg :=
    mul_le_mul_of_nonneg_left (gammaHalfLineNorm_le_exp ht)
      (by nlinarith only [ht, sq_nonneg t] : 0 ≤ 7 + 7 * t + 5 * t ^ 2)
  have h := (abs_scaledGammaHalfLineNormSecondDeriv_le_polynomial ht).trans hg
  have h0 : Real.exp (-(3 / 2) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht])
  nlinarith only [h, h0, linear_exp_decay_le_quarter ht, quadratic_exp_decay_le_quarter ht]

end PseudoPrime.Analysis
