/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ResidualMonotone
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEndpoints

/-! # Rational certificate for the 0.28 high-range residual -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational expression bounding the residual when the logarithm and negative
power are bounded above and the square root is bounded below. Its inputs are the
radius and those three bounds; it enables exact arithmetic at each entrance. -/
noncomputable def target028EndpointBound (r u v s : ℝ) : ℝ :=
  (2 * ((1000 / 529 : ℝ) * r)) *
          (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * v * ((21 / 8 : ℝ) + 2 * u) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000)) * 16 * v *
          (((21 / 8 : ℝ) + 2 * u) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
            (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) -
      (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    5 *
      ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        ((1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) / r) +
    4 * (119 / 1000 : ℝ) * ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * u) + 2) / r +
    4 * (9 / 100 : ℝ) * ((231 / 2500 : ℝ) * (7 / 3) / s + (1839 / 1000 : ℝ) / r)

/-- If the radius is at least one, certified logarithm and power upper bounds and
a positive square-root lower bound give the displayed rational residual bound.
Compare each nonnegative product using the supplied bounds and the fixed numerical
bounds for the exponential and kernel weights. -/
theorem target028_residual_le_endpoint_bound {r u v s : ℝ} (hr : 1 ≤ r) (hs : 0 < s)
    (hlog : Real.log r ≤ u) (hp : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ v) (hsqrt : s ≤ Real.sqrt r) :
    target028ResidualEnvelope r ≤ target028EndpointBound r u v s := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hu0 : 0 ≤ u := hl0.trans hlog
  have hp0 : 0 ≤ (r ^ 2) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (sq_nonneg r) _
  have hv0 : 0 ≤ v := hp0.trans hp
  have hE := refined_exp_neg_unit_le
  have hW : refinedWeight 1 ≤ (9 / 100 : ℝ) := (le_abs_self _).trans refined_weight_unit_lt.le
  have hD : |refinedWeightDeriv 1| ≤ (119 / 1000 : ℝ) := refined_deriv_unit_lt.le
  have hF0 : 0 ≤ ((21 / 8 : ℝ) + 2 * Real.log r) ^ 5 := by positivity
  have hF :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (21 / 8) + 2 * Real.log r by positivity)
      (show (21 / 8 : ℝ) + 2 * Real.log r ≤ 21 / 8 + 2 * u by linarith only [hlog]) 5
  have hEP := mul_le_mul hE hp hp0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hEP0 : 0 ≤ (588 / 10000 : ℝ) * v := mul_nonneg (by norm_num only) hv0
  have hEPF := mul_le_mul hEP hF hF0 hEP0
  have hQ0 :
    0 ≤
      (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27) +
        ((21 / 8 : ℝ) + 2 * Real.log r) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) := by
    positivity
  have hQ :=
    add_le_add_right
      (mul_le_mul_of_nonneg_right hF (show (0 : ℝ) ≤ (50 / 29 : ℝ) ^ 2 + 50 / 79 by positivity))
      ((100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27))
  have hEPQ := mul_le_mul hEP hQ hQ0 hEP0
  have hlin0 : 0 ≤ (1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2 := by positivity
  have hlin :
    (1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2 ≤
      (1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2 := by
    linarith only [hlog]
  have hlinupper0 : 0 ≤ (1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2 := hlin0.trans hlin
  have hder0 : 0 ≤ (231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2 := by positivity
  have hder :
    (231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2 ≤
      (231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * u) + 2 := by
    linarith only [hlog]
  have hDD := mul_le_mul hD hder hder0 (by norm_num only : (0 : ℝ) ≤ 119 / 1000)
  have hss := one_div_le_one_div_of_le hs hsqrt
  have hrest0 : 0 ≤ (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r + (1839 / 1000 : ℝ) / r := by
    positivity
  have hrest :
    (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r + (1839 / 1000 : ℝ) / r ≤
      (231 / 2500 : ℝ) * (7 / 3) / s + (1839 / 1000 : ℝ) / r := by
    have hm :=
      mul_le_mul_of_nonneg_left hss (show (0 : ℝ) ≤ (231 / 2500 : ℝ) * (7 / 3) by positivity)
    simp only [div_eq_mul_inv, one_mul] at hm ⊢
    linarith only [hm]
  have hWW := mul_le_mul hW hrest hrest0 (by norm_num only : (0 : ℝ) ≤ 9 / 100)
  have hC :=
    mul_le_mul_of_nonneg_left hEPF
      (show (0 : ℝ) ≤ 2 * (1000 / 529 * r) * ((27 / 25 : ℝ) ^ 5 / 120) by positivity)
  have hT :=
    mul_le_mul_of_nonneg_left hEPQ (show (0 : ℝ) ≤ ((27 / 25 : ℝ) ^ 5 / 120) * 16 by positivity)
  have hL :=
    mul_le_mul_of_nonneg_left hlin
      (show (0 : ℝ) ≤ 5 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) / r by positivity)
  have hD' := mul_le_mul_of_nonneg_left hDD (show (0 : ℝ) ≤ 4 / r by positivity)
  have hW' := mul_le_mul_of_nonneg_left hWW (show (0 : ℝ) ≤ 4 by norm_num only)
  dsimp only [target028ResidualEnvelope, target028PaperResidual, target028EndpointBound]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv] at hC hT hL hD' hW' ⊢
  nlinarith only [hC, hT, hL, hD', hW']

end PseudoPrime.PrimeTestBounds.MillerRabin
