/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffDerivatives
public import PseudoPrime.Analysis.GaussianGammaKernel
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Curvature bound for the Gaussian cutoff midpoint certificate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative z, z²exp(-z) is at most two.
Multiply the quadratic Taylor lower bound for exp(z) by exp(-z).
This bounds the cutoff factor's second derivative uniformly in the cutoff. -/
theorem gaussian_sq_mul_exp_neg_le_two {z : ℝ} (hz : 0 ≤ z) : z ^ 2 * Real.exp (-z) ≤ 2 := by
  have h := mul_le_mul_of_nonneg_right (Real.quadratic_le_exp_of_nonneg hz) (Real.exp_pos (-z)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  nlinarith only [h, mul_nonneg hz (Real.exp_pos (-z)).le, (Real.exp_pos (-z)).le]

/-- The linear factor of a shifted Gaussian is bounded after multiplication by its
quadratic exponential decay. This supplies the derivative estimate needed for a sharper
uniform curvature bound. -/
theorem gaussian_linear_mul_exp_neg_sq_le_one (x : ℝ) : 2 * x * Real.exp (-(x ^ 2)) ≤ 1 := by
  have h := Real.quadratic_le_exp_of_nonneg (sq_nonneg x)
  have hlin : 2 * x ≤ 1 + x ^ 2 := by nlinarith only [sq_nonneg (x - 1)]
  have hexp : 1 + x ^ 2 ≤ Real.exp (x ^ 2) := by nlinarith only [h]
  have hp := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-(x ^ 2)))
  have hprod : Real.exp (x ^ 2) * Real.exp (-(x ^ 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    2 * x * Real.exp (-(x ^ 2)) ≤ (1 + x ^ 2) * Real.exp (-(x ^ 2)) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
    _ ≤ Real.exp (x ^ 2) * Real.exp (-(x ^ 2)) := hp
    _ = 1 := hprod

/-- After completing the square at `v = 1/4`, the tilted Gaussian's linear
derivative factor is bounded by `exp(1/16)`. -/
theorem gaussianTilt_derivative_factor_abs_le (v : ℝ) :
    |(-2 * v + 1 / 2) * Real.exp (-(v ^ 2) + v / 2)| ≤ Real.exp (1 / 16) := by
  let u := v - 1 / 4
  have h := gaussian_linear_mul_exp_neg_sq_le_one |u|
  have hscaled : 2 * |u| * Real.exp (-(u ^ 2)) ≤ 1 := by simpa only [sq_abs] using h
  have harg : -(v ^ 2) + v / 2 = 1 / 16 - u ^ 2 := by
    dsimp only [u]
    ring
  have hlin : -2 * v + 1 / 2 = -2 * u := by
    dsimp only [u]
    ring
  rw [harg, hlin]
  rw [show 1 / 16 - u ^ 2 = 1 / 16 + -(u ^ 2) by ring, Real.exp_add]
  simp only [abs_mul, abs_neg, abs_of_pos (by norm_num only : (0 : ℝ) < 2),
    abs_of_pos (Real.exp_pos (1 / 16)), abs_of_pos (Real.exp_pos (-(u ^ 2)))]
  calc
    2 * |u| * (Real.exp (1 / 16) * Real.exp (-(u ^ 2))) =
        Real.exp (1 / 16) * (2 * |u| * Real.exp (-(u ^ 2))) :=
      by ring
    _ ≤ Real.exp (1 / 16) * 1 := mul_le_mul_of_nonneg_left hscaled (Real.exp_nonneg _)
    _ = Real.exp (1 / 16) := by ring

/-- The quadratic factor of a shifted Gaussian, multiplied by its Gaussian decay,
has absolute value at most two. The proof treats the factor's sign on either side
of `x^2 = 1/2` and uses the quadratic Taylor lower bound for the exponential. -/
theorem gaussian_quadratic_mul_exp_neg_sq_abs_le_two (x : ℝ) :
    |(4 * x ^ 2 - 2) * Real.exp (-(x ^ 2))| ≤ 2 := by
  let t := x ^ 2
  have ht : 0 ≤ t := sq_nonneg x
  have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hq := Real.quadratic_le_exp_of_nonneg ht
  have hexp : 1 + t + t ^ 2 / 2 ≤ Real.exp t := by nlinarith only [hq]
  have hprod : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  change |(4 * t - 2) * Real.exp (-t)| ≤ 2
  have hlo : -2 ≤ (4 * t - 2) * Real.exp (-t) := by
    by_cases hhalf : t ≤ 1 / 2
    · have hfac : -2 ≤ 4 * t - 2 := by nlinarith only [ht]
      have hfac_nonpos : 4 * t - 2 ≤ 0 := by nlinarith only [hhalf]
      have hmul := mul_le_mul_of_nonpos_left he1 hfac_nonpos
      nlinarith only [hfac, hmul]
    · have hfac_nonneg : 0 ≤ 4 * t - 2 := by nlinarith only [lt_of_not_ge hhalf]
      exact le_trans (by norm_num only : (-2 : ℝ) ≤ 0) (mul_nonneg hfac_nonneg he0)
  have hhi : (4 * t - 2) * Real.exp (-t) ≤ 2 := by
    by_cases hhalf : t ≤ 1 / 2
    · have hfac_nonpos : 4 * t - 2 ≤ 0 := by nlinarith only [hhalf]
      exact (mul_nonpos_of_nonpos_of_nonneg hfac_nonpos he0).trans (by norm_num only : (0 : ℝ) ≤ 2)
    · have hlarge : 1 / 2 < t := lt_of_not_ge hhalf
      have hfac_nonneg : 0 ≤ 4 * t - 2 := by nlinarith only [hlarge]
      have hfac : 4 * t - 2 ≤ 2 * Real.exp t := by nlinarith only [hexp, sq_nonneg (t - 1)]
      have hmul := mul_le_mul_of_nonneg_right hfac he0
      calc
        (4 * t - 2) * Real.exp (-t) ≤ (2 * Real.exp t) * Real.exp (-t) := hmul
        _ = 2 := by rw [mul_assoc, hprod, mul_one]
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Completing the square transfers the quadratic Gaussian estimate to the
second derivative factor of the tilted Gaussian. -/
theorem gaussianTilt_second_derivative_factor_abs_le (v : ℝ) :
    |((-2 * v + 1 / 2) ^ 2 - 2) * Real.exp (-(v ^ 2) + v / 2)| ≤ 2 * Real.exp (1 / 16) := by
  let u := v - 1 / 4
  have harg : -(v ^ 2) + v / 2 = 1 / 16 - u ^ 2 := by
    dsimp only [u]
    ring
  have hlin : -2 * v + 1 / 2 = -2 * u := by
    dsimp only [u]
    ring
  have h := gaussian_quadratic_mul_exp_neg_sq_abs_le_two u
  rw [harg, hlin]
  rw [show 1 / 16 - u ^ 2 = 1 / 16 + -(u ^ 2) by ring, Real.exp_add]
  simp only [abs_mul, abs_of_pos (Real.exp_pos (1 / 16)), abs_of_pos (Real.exp_pos (-(u ^ 2)))]
  have hdecay : |4 * u ^ 2 - 2| * Real.exp (-(u ^ 2)) ≤ 2 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h
    exact h
  have hfactor : |(-2 * u) ^ 2 - 2| * Real.exp (-(u ^ 2)) ≤ 2 := by
    have hpoly : (-2 * u) ^ 2 - 2 = 4 * u ^ 2 - 2 := by ring
    rw [hpoly]
    exact hdecay
  calc
    |(-2 * u) ^ 2 - 2| * (Real.exp (1 / 16) * Real.exp (-(u ^ 2))) =
        Real.exp (1 / 16) * (|(-2 * u) ^ 2 - 2| * Real.exp (-(u ^ 2))) :=
      by ring
    _ ≤ Real.exp (1 / 16) * 2 := mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)
    _ = 2 * Real.exp (1 / 16) := by ring

/-- The normalized second derivative factor of the tilted Gaussian is at most `4/3`.
The exponential endpoint and `pi > 3` absorb the factor two from the Gaussian polynomial. -/
theorem gaussianTilt_second_derivative_normalized_abs_le_four_thirds (v : ℝ) :
    |((-2 * v + 1 / 2) ^ 2 - 2) * Real.exp (-(v ^ 2) + v / 2)| / Real.sqrt Real.pi ≤ 4 / 3 := by
  have hD := gaussianTilt_second_derivative_factor_abs_le v
  have hE : Real.exp (1 / 16) ≤ (2129 : ℝ) / 2000 := gaussian_endpoint_exp_le
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hroot : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hconst : 3 * (2 * ((2129 : ℝ) / 2000)) ≤ 4 * Real.sqrt Real.pi := by
    have hsq : (3 * (2 * ((2129 : ℝ) / 2000))) ^ 2 ≤ (4 * Real.sqrt Real.pi) ^ 2 := by
      nlinarith only [hpi, hroot]
    nlinarith only [hsq, Real.sqrt_nonneg Real.pi]
  have hDscaled :
    3 * |((-2 * v + 1 / 2) ^ 2 - 2) * Real.exp (-(v ^ 2) + v / 2)| ≤
      3 * (2 * Real.exp (1 / 16)) := by
    nlinarith only [hD]
  have hEscaled : 3 * (2 * Real.exp (1 / 16)) ≤ 3 * (2 * ((2129 : ℝ) / 2000)) := by
    nlinarith only [hE]
  have hscaled := hDscaled.trans (hEscaled.trans hconst)
  rw [div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)]
  nlinarith only [hscaled]

/-- The tilted Gaussian exp(-v²+v/2) is at most 11/10 on the real line.
Complete the square and apply exp(1/16) <= 16/15. This bounds the common amplitude. -/
theorem gaussianTilt_le_eleven_tenths (v : ℝ) : Real.exp (-(v ^ 2) + v / 2) ≤ 11 / 10 := by
  have he : -(v ^ 2) + v / 2 ≤ (1 : ℝ) / 16 := by nlinarith only [sq_nonneg (v - 1 / 4)]
  have h :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num only : (0 : ℝ) ≤ 1 / 16)
      (by norm_num only : (1 : ℝ) / 16 < 1)
  have hm := Real.exp_le_exp.mpr he
  norm_num only at h
  linarith only [hm, h]

/-- The tilted Gaussian is bounded by the certified endpoint multiplier
2129/2000. Complete the square and use the exact exponential bound. -/
theorem gaussianTilt_le_2129_two_thousandths (v : ℝ) :
    Real.exp (-(v ^ 2) + v / 2) ≤ 2129 / 2000 := by
  have he : -(v ^ 2) + v / 2 ≤ (1 : ℝ) / 16 := by nlinarith only [sq_nonneg (v - 1 / 4)]
  exact (Real.exp_le_exp.mpr he).trans gaussian_endpoint_exp_le

/-- The normalized tilted Gaussian amplitude is at most `2/3`.
The certified exponential endpoint and `pi > 3` give this uniform bound. -/
theorem gaussianTilt_normalized_le_two_thirds (v : ℝ) :
    Real.exp (-(v ^ 2) + v / 2) / Real.sqrt Real.pi ≤ 2 / 3 := by
  have hA := gaussianTilt_le_2129_two_thousandths v
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hroot : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hconst : 3 * ((2129 : ℝ) / 2000) ≤ 2 * Real.sqrt Real.pi := by
    have hsq : (3 * ((2129 : ℝ) / 2000)) ^ 2 ≤ (2 * Real.sqrt Real.pi) ^ 2 := by
      nlinarith only [hpi, hroot]
    nlinarith only [hsq, Real.sqrt_nonneg Real.pi]
  have hscaled : 3 * Real.exp (-(v ^ 2) + v / 2) ≤ 2 * Real.sqrt Real.pi := by
    nlinarith only [hA, hconst]
  rw [div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)]
  nlinarith only [hscaled]

/-- The normalized first derivative factor of the tilted Gaussian is at most `2/3`.
Completing the square reduces it to the uniform exponential-decay estimate above. -/
theorem gaussianTilt_derivative_normalized_abs_le_two_thirds (v : ℝ) :
    |(-2 * v + 1 / 2) * Real.exp (-(v ^ 2) + v / 2)| / Real.sqrt Real.pi ≤ 2 / 3 := by
  have hD := gaussianTilt_derivative_factor_abs_le v
  have hE : Real.exp (1 / 16) ≤ (2129 : ℝ) / 2000 := gaussian_endpoint_exp_le
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hroot : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hconst : 3 * ((2129 : ℝ) / 2000) ≤ 2 * Real.sqrt Real.pi := by
    have hsq : (3 * ((2129 : ℝ) / 2000)) ^ 2 ≤ (2 * Real.sqrt Real.pi) ^ 2 := by
      nlinarith only [hpi, hroot]
    nlinarith only [hsq, Real.sqrt_nonneg Real.pi]
  have hscaled : 3 * |(-2 * v + 1 / 2) * Real.exp (-(v ^ 2) + v / 2)| ≤ 2 * Real.sqrt Real.pi := by
    nlinarith only [hD, hE, hconst]
  rw [div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)]
  nlinarith only [hscaled]

/-- The cutoff factor and its first two derivatives admit the sharper uniform
bounds required by the `8/3` curvature estimate. The second derivative bound uses
the cubic Taylor lower bound for `exp` when `z` is at least one. -/
theorem cutoff_factor_tight_bounds {z : ℝ} (hz : 0 ≤ z) :
    |1 - Real.exp (-z)| ≤ 1 ∧
      |(-z) * Real.exp (-z)| ≤ 1 / 2 ∧ |(z - z ^ 2) * Real.exp (-z)| ≤ 1 := by
  have he : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  have he1 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have hq := Real.quadratic_le_exp_of_nonneg hz
  have hlin : 2 * z ≤ 1 + z + z ^ 2 / 2 := by nlinarith only [sq_nonneg (z - 1)]
  have hexp : 1 + z + z ^ 2 / 2 ≤ Real.exp z := by nlinarith only [hq]
  have hmul := mul_le_mul_of_nonneg_right hexp he
  have hprod : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : 2 * z * Real.exp (-z) ≤ 1 := by
    calc
      2 * z * Real.exp (-z) ≤ (1 + z + z ^ 2 / 2) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hlin he
      _ ≤ Real.exp z * Real.exp (-z) := hmul
      _ = 1 := hprod
  have hhalf : z * Real.exp (-z) ≤ 1 / 2 := by nlinarith only [h2]
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr he1)]
    linarith only [he]
  constructor
  · rw [abs_mul, abs_neg, abs_of_nonneg hz, abs_of_pos (Real.exp_pos _)]
    exact hhalf
  · by_cases hle : z ≤ 1
    · have hfac : 0 ≤ z - z ^ 2 := by
        have hp := mul_nonneg hz (sub_nonneg.mpr hle)
        nlinarith only [hp]
      have hbound : z - z ^ 2 ≤ 1 := by nlinarith only [hle, sq_nonneg z]
      rw [abs_of_nonneg (mul_nonneg hfac he)]
      calc
        (z - z ^ 2) * Real.exp (-z) ≤ z - z ^ 2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hfac
        _ ≤ 1 := hbound
    · have hlarge : 1 < z := lt_of_not_ge hle
      have htaylor := Real.sum_le_exp_of_nonneg hz 4
      have hpoly : z ^ 2 - z ≤ ∑ i ∈ Finset.range 4, z ^ i / (i.factorial : ℝ) := by
        norm_num only [Finset.sum_range_succ, Nat.factorial]
        nlinarith only [hz, pow_nonneg hz 3, sq_nonneg (z - 3)]
      have hupper := hpoly.trans htaylor
      have hmul' := mul_le_mul_of_nonneg_right hupper he
      have hfacnonpos : z - z ^ 2 ≤ 0 := by
        rw [show z - z ^ 2 = z * (1 - z) by ring]
        exact mul_nonpos_of_nonneg_of_nonpos hz (by linarith only [hlarge])
      have hneg : |z - z ^ 2| = z ^ 2 - z := by
        rw [abs_of_nonpos hfacnonpos]
        ring
      rw [abs_mul, hneg, abs_of_pos (Real.exp_pos _)]
      calc
        (z ^ 2 - z) * Real.exp (-z) ≤ Real.exp z * Real.exp (-z) := hmul'
        _ = 1 := hprod

/-- For nonnegative z, the cutoff factor and its first two derivatives
have absolute values at most 1,1,3. Exponential decay controls z and z².
These estimates are independent of the nonnegative cutoff parameter. -/
theorem cutoff_factor_bounds {z : ℝ} (hz : 0 ≤ z) :
    |1 - Real.exp (-z)| ≤ 1 ∧ |(-z) * Real.exp (-z)| ≤ 1 ∧ |(z - z ^ 2) * Real.exp (-z)| ≤ 3 := by
  have he := (Real.exp_pos (-z)).le
  have he1 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have hz1 : z * Real.exp (-z) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one z).trans
      (Real.exp_le_one_iff.mpr (by norm_num only : (-1 : ℝ) ≤ 0))
  have hz2 := gaussian_sq_mul_exp_neg_le_two hz
  have hn1 := mul_nonneg hz he
  have hn2 := mul_nonneg (sq_nonneg z) he
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr he1)]
    linarith only [he]
  constructor
  · rw [neg_mul, abs_neg, abs_of_nonneg hn1]
    exact hz1
  · calc
      |(z - z ^ 2) * Real.exp (-z)| = |z * Real.exp (-z) - z ^ 2 * Real.exp (-z)| := by rw [sub_mul]
      _ ≤ |z * Real.exp (-z)| + |z ^ 2 * Real.exp (-z)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (z * Real.exp (-z)) 0 (z ^ 2 * Real.exp (-z)))
      _ ≤ 3 := by
        rw [abs_of_nonneg hn1, abs_of_nonneg hn2]
        linarith only [hz1, hz2]

/-- On [-4,4], the Gaussian logarithmic derivative and curvature polynomial
have absolute values at most 17/2 and 74. Bound the linear factor before squaring.
This supplies the polynomial factors in the product-rule estimate. -/
theorem gaussianTilt_curvature_polynomial_bounds {v : ℝ} (hv : v ∈ Set.Icc (-4) 4) :
    |-2 * v + 1 / 2| ≤ 17 / 2 ∧ |(-2 * v + 1 / 2) ^ 2 - 2| ≤ 71 := by
  have hlo : -(17 / 2 : ℝ) ≤ -2 * v + 1 / 2 := by linarith only [hv.2]
  have hhi : -2 * v + 1 / 2 ≤ (17 / 2 : ℝ) := by linarith only [hv.1]
  have hs := sq_le_sq' hlo hhi
  have hlow : -(71 : ℝ) ≤ (-2 * v + 1 / 2) ^ 2 - 2 := by nlinarith only [sq_nonneg (-2 * v + 1 / 2)]
  have hhigh : (-2 * v + 1 / 2) ^ 2 - 2 ≤ 71 := by nlinarith only [hs]
  exact ⟨abs_le.mpr ⟨hlo, hhi⟩, abs_le.mpr ⟨hlow, hhigh⟩⟩

/-- Input: a nonnegative cutoff parameter and a point in [-4,4].
Claim: the normalized Gaussian cutoff density's second derivative has absolute value at most 8/3.
Proof: bound the normalized Gaussian factors by 2/3, 2/3, and 4/3, then use cutoff
factor bounds 1, 1/2, and 1 in the product rule.
Role: supplies the curvature error for the 128-point midpoint certificate. -/
theorem gaussianGammaCutoff_secondDeriv_abs_le {l v : ℝ} (hl : 0 ≤ l) (_hv : v ∈ Set.Icc (-4) 4) :
    |gaussianGammaCutoffIntegrandSecondDeriv l v| ≤ 8 / 3 := by
  let A := Real.exp (-(v ^ 2) + v / 2)
  let b := -2 * v + 1 / 2
  let z := l * Real.exp (-v)
  let C := 1 - Real.exp (-z)
  let D := -z * Real.exp (-z)
  let E := (z - z ^ 2) * Real.exp (-z)
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hA : |A| ≤ 2 / 3 * Real.sqrt Real.pi := by
    have h := gaussianTilt_normalized_le_two_thirds v
    rw [div_le_iff₀ hsqrt] at h
    change |Real.exp (-(v ^ 2) + v / 2)| ≤ 2 / 3 * Real.sqrt Real.pi
    rw [abs_of_pos (Real.exp_pos _)]
    exact h
  have hAb : |A * b| ≤ 2 / 3 * Real.sqrt Real.pi := by
    have h := gaussianTilt_derivative_normalized_abs_le_two_thirds v
    rw [div_le_iff₀ hsqrt] at h
    change |Real.exp (-(v ^ 2) + v / 2) * (-2 * v + 1 / 2)| ≤ 2 / 3 * Real.sqrt Real.pi
    rw [abs_mul] at h ⊢
    nlinarith only [h]
  have hAbb : |A * (b ^ 2 - 2)| ≤ 4 / 3 * Real.sqrt Real.pi := by
    have h := gaussianTilt_second_derivative_normalized_abs_le_four_thirds v
    rw [div_le_iff₀ hsqrt] at h
    change |Real.exp (-(v ^ 2) + v / 2) * ((-2 * v + 1 / 2) ^ 2 - 2)| ≤ 4 / 3 * Real.sqrt Real.pi
    rw [abs_mul] at h ⊢
    nlinarith only [h]
  have hz : 0 ≤ z := mul_nonneg hl (Real.exp_pos _).le
  have hc := cutoff_factor_tight_bounds hz
  have h1num : |A * (b ^ 2 - 2)| * |C| ≤ 4 / 3 * Real.sqrt Real.pi :=
    (mul_le_of_le_one_right (abs_nonneg _) hc.1).trans hAbb
  have h2prod : |A * b| * |D| ≤ (2 / 3 * Real.sqrt Real.pi) * (1 / 2) :=
    mul_le_mul hAb hc.2.1 (abs_nonneg _) (by positivity)
  have h2num : |2 * (A * b) * D| ≤ 2 / 3 * Real.sqrt Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
    nlinarith only [h2prod]
  have h3num : |A| * |E| ≤ 2 / 3 * Real.sqrt Real.pi :=
    (mul_le_of_le_one_right (abs_nonneg _) hc.2.2).trans hA
  have hsum : |A * (b ^ 2 - 2) * C + 2 * (A * b) * D + A * E| ≤ 8 / 3 * Real.sqrt Real.pi := by
    have ht :=
      (abs_add_le (A * (b ^ 2 - 2) * C + 2 * (A * b) * D) (A * E)).trans
        (add_le_add (abs_add_le (A * (b ^ 2 - 2) * C) (2 * (A * b) * D)) le_rfl)
    have ht1scaled : |A * (b ^ 2 - 2) * C| ≤ 4 / 3 * Real.sqrt Real.pi := by
      rw [abs_mul]
      exact h1num
    have ht2scaled : |2 * (A * b) * D| ≤ 2 / 3 * Real.sqrt Real.pi := h2num
    have ht3scaled : |A * E| ≤ 2 / 3 * Real.sqrt Real.pi := by
      rw [abs_mul]
      exact h3num
    calc
      _ ≤ |A * (b ^ 2 - 2) * C| + |2 * (A * b) * D| + |A * E| := ht
      _ ≤ (4 / 3 + 2 / 3 + 2 / 3) * Real.sqrt Real.pi := by
        nlinarith only [ht1scaled, ht2scaled, ht3scaled]
      _ = 8 / 3 * Real.sqrt Real.pi := by ring
  have heq :
    gaussianGammaCutoffIntegrandSecondDeriv l v =
      (A * (b ^ 2 - 2) * C + 2 * (A * b) * D + A * E) / Real.sqrt Real.pi := by
    dsimp only [gaussianGammaCutoffIntegrandSecondDeriv, A, b, z, C, D, E]
    simp only [neg_mul]
  rw [heq, abs_div, abs_of_pos hsqrt, div_le_iff₀ hsqrt]
  exact hsum

end PseudoPrime.Analysis
