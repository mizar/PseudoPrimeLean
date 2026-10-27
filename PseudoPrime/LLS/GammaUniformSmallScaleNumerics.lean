/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedShiftBounds

/-! # Uniform Gamma numerical budgets from scale 224 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For T ≥ 224, log T ≤ (3/112)T. Anchor the logarithm at 224 and bound
log 250 by six using the logarithms of two and five.
This controls the principal and ramp errors at much smaller scales. -/
theorem gamma_small_scale_log_bound {T : ℝ} (hT : 224 ≤ T) : Real.log T ≤ (3 / 112 : ℝ) * T := by
  have hT0 : 0 < T := by linarith only [hT]
  have h250 : Real.log (250 : ℝ) < 6 := by
    rw [show (250 : ℝ) = 2 * 5 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
        (pow_ne_zero 3 (by norm_num only : (5 : ℝ) ≠ 0)),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have h224 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 224) (by norm_num only : (224 : ℝ) ≤ 250)
  have ht := Real.log_le_sub_one_of_pos (div_pos hT0 (by norm_num only : (0 : ℝ) < 224))
  rw [Real.log_div hT0.ne' (by norm_num only : (224 : ℝ) ≠ 0)] at ht
  linarith only [ht, h224, h250, hT]

/-- For T ≥ 224, the ramp scale exceeds (9/5)^16, the principal normalized
error is at most 3/5 and the ramp normalized error is at most 23.
Combine the logarithmic tangent bound with the rational root lower bound.
These are the common small-scale numerical entrances. -/
theorem gamma_small_scale_bounds {T : ℝ} (hT : 224 ≤ T) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (9 / 5 : ℝ) ^ 16 ≤ x ∧
      Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 ≤
        (3 / 5 : ℝ) * Real.sqrt x ∧
      (135 / 20 : ℝ) * Real.sqrt x + 86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) ≤
        23 * Real.sqrt x := by
  let x := (32 / 99 : ℝ) * T ^ 2
  have hxlarge : (9 / 5 : ℝ) ^ 16 ≤ x := by
    dsimp only [x]
    norm_num only
    nlinarith only [hT, sq_nonneg (T - 224)]
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (9 / 5) ^ 16).trans hxlarge
  have hs := ramp_scale_sqrt_lower (show 0 ≤ T by linarith only [hT])
  have hl := gamma_small_scale_log_bound hT
  have hlogx :=
    Real.log_le_log (zero_lt_one.trans_le hx)
      (show x ≤ T ^ 2 by
        dsimp only [x]; nlinarith only [sq_nonneg T])
  rw [Real.log_pow] at hlogx
  norm_num only [Nat.cast_ofNat] at hlogx
  have hxX : 0 < x * (99 / 40 : ℝ) := mul_pos (zero_lt_one.trans_le hx) (by norm_num only)
  have hlogX :=
    Real.log_le_log hxX
      (show x * (99 / 40 : ℝ) ≤ T ^ 2 by
        dsimp only [x]; nlinarith only [sq_nonneg T])
  rw [Real.log_pow] at hlogX
  norm_num only [Nat.cast_ofNat] at hlogX
  refine ⟨hxlarge, ?_, ?_⟩
  · linarith only [hlogx, hl, hs, hT]
  · linarith only [hlogX, hl, hs, hT]

/-- For T ≥ 224, log T/T^(1/3) ≤ 1. Anchor the cube root at six,
use log six < two and a logarithmic tangent bound.
This controls the factor-support loss on the full small-scale half-line. -/
theorem gamma_small_scale_cuberoot_ratio {T : ℝ} (hT : 224 ≤ T) :
    Real.log T / T ^ (1 / 3 : ℝ) ≤ 1 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hc :=
    Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ 6 ^ 3)
      (show (6 : ℝ) ^ 3 ≤ T by linarith only [hT]) (by norm_num only : (0 : ℝ) ≤ 1 / 3)
  have he : ((6 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 6 := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 6)]
    norm_num only [Real.rpow_one]
  rw [he] at hc
  have hu0 := Real.rpow_pos_of_pos hT0 (1 / 3 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 6))
  rw [Real.log_div hu0.ne' (by norm_num only : (6 : ℝ) ≠ 0), Real.log_rpow hT0] at ht
  have h6 : Real.log (6 : ℝ) < 2 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0)]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  rw [div_le_iff₀ hu0]
  linarith only [hc, ht, h6]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- For T ≥ 224, sqrt x ≥ 9T/16 and Q ≤ T, the pole error is at most 211/100.
Clear the positive root denominator and compare rational coefficients.
This is the uniform pole allowance for the smaller-scale comparison. -/
theorem gamma_small_scale_pole_budget {T x Q : ℝ} (hT : 224 ≤ T)
    (hroot : (9 / 16 : ℝ) * T ≤ Real.sqrt x) (hQ : Q ≤ T) :
    ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 211 / 100 := by
  have hs : 0 < Real.sqrt x := by linarith only [hT, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hT, hroot, hQ]

/-- For T ≥ 224, x ≥ (9/5)^16, sqrt x ≥ 9T/16 and 0 ≤ Q ≤ T,
the left-contour error is at most eight. Retain the extra real-power decay
and clear the positive denominator. This supplies the smaller-scale contour allowance. -/
theorem gamma_small_scale_left_budget {T x Q : ℝ} (hT : 224 ≤ T) (hx : (9 / 5 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * T ≤ Real.sqrt x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ T) :
    x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Q + 283) + 5 / 3) ≤ 8 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hT]
  have hC : 0 ≤ (16 / 5 : ℝ) * (Q + 283) + 5 / 3 := by linarith only [hQ0]
  have hm :=
    mul_le_mul_of_nonneg_right
      (rpow_neg_nine_sixteenths_le_div_scale_sqrt (by norm_num only : (0 : ℝ) < 9 / 5) hx) hC
  apply hm.trans
  rw [one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 9 / 5) hs)]
  nlinarith only [hroot, hT, hQ]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.Analysis

/-- For nonzero q, T > 1, log q ≤ T, positive x and cutoff X ≥ 1,
a root lower coefficient a > 0, log X ≤ 2 log T and cube-root ratio beta give
twice the normalized nonunit loss at most (4/a)(beta+3/2).
Split the prime support at T^(2/3) and use the ambient logarithm upper bound.
This permits small logarithmic inputs with a larger shifted scale. -/
theorem gamma_commonFactor_budget_of_ambient_scale {q : ℕ} [NeZero q] {T x X a beta : ℝ}
    (ha : 0 < a) (hL : 1 < T) (hambient : Real.log q ≤ T) (hx0 : 0 < x) (hcut : 1 ≤ X)
    (hcutlog : Real.log X ≤ 2 * Real.log T) (hroot : a * T ≤ Real.sqrt x)
    (hlog : Real.log T / (T) ^ (1 / 3 : ℝ) ≤ beta) :
    2 * (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q / Real.sqrt x) ≤
      (4 / a) * (beta + 3 / 2) := by
  let L := T
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hs0 := Real.sqrt_pos.mpr hx0
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have hlog0 := Real.log_pos hL
  have hp : L ^ (2 / 3 : ℝ) = L / L ^ (1 / 3 : ℝ) := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hc := hcutlog
  have hF0 : 0 ≤ L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L :=
    add_nonneg (Real.rpow_pos_of_pos hL0 _).le (div_nonneg (by linarith only [hL0]) hlog0.le)
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_cutoff_add_log_div (NeZero.ne q)
      (Real.one_lt_rpow hL (by norm_num only : (0 : ℝ) < 2 / 3))
  rw [Real.log_rpow hL0] at hcard
  have hdiv :=
    div_le_div_of_nonneg_right hambient (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 / 3) hlog0.le)
  have hcancel : L / ((2 / 3 : ℝ) * Real.log L) = (3 / 2 : ℝ) * L / Real.log L := by
    rw [div_mul_eq_div_div]
    ring
  have hF : (q.primeFactors.card : ℝ) ≤ L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L := by
    rw [hcancel] at hdiv
    linarith only [hcard, hdiv]
  have hnum :=
    (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_card_mul_log (NeZero.ne q) hx0
          hcut).trans
      ((mul_le_mul_of_nonneg_right hF (Real.log_nonneg hcut)).trans
        (mul_le_mul_of_nonneg_left hc hF0))
  have he :
    (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) =
      2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by
    rw [hp]
    have hbcan : ((3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) = 3 * L := by
      calc
        _ = 2 * ((3 / 2 : ℝ) * L / Real.log L * Real.log L) := by ring
        _ = 2 * ((3 / 2 : ℝ) * L) := by rw [div_mul_cancel₀ _ hlog0.ne']
        _ = 3 * L := by ring
    rw [add_mul, hbcan]
    ring
  change
    AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q ≤
      (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) at hnum
  rw [he] at hnum
  have hB0 : 0 ≤ Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2 :=
    add_nonneg (div_nonneg hlog0.le hu0.le) (by norm_num only)
  have hr : L / Real.sqrt x ≤ 1 / a := by
    apply (div_le_div_iff₀ hs0 ha).mpr
    nlinarith only [hroot]
  have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hB0)
  have ht :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num only : (0 : ℝ) ≤ 2))
      (Real.sqrt_nonneg x)
  calc
    _ = 2 * AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q / Real.sqrt x := by
      ring
    _ ≤ 2 * (2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2)) / Real.sqrt x := ht
    _ = 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (L / Real.sqrt x) := by ring
    _ ≤ 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (1 / a) := hm
    _ = (4 / a) * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by ring
    _ ≤ (4 / a) * (beta + 3 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hlog (3 / 2 : ℝ))
        (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) ha.le)

end PseudoPrime.Analysis
