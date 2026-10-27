/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannChebyshevBounds
public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Explicit RH Chebyshev error for kernel truncation

The zeta smoothing constant 61/10 gives a finite-difference error below 38.
An elementary Chebyshev bound extends the result to all nonnegative cutoffs.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and x>1, the logarithmically weighted Mangoldt sum has error at most
(61/10)sqrt(x). Apply the explicit zeta formula, zero mass at most 1/40 and log(2π)<2.
The constant feeds the finite-difference Chebyshev estimate. -/
theorem logWeightedMangoldtSum_error_le_sqrt_sixty_one_tenths (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤ (61 / 10) * Real.sqrt x := by
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx))
  rw [Real.log_sqrt (zero_lt_one.trans hx).le] at hl
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by linarith only [hl]
  have hL : Real.log (2 * Real.pi) ≤ (2 : ℝ) := by linarith only [Analysis.log_two_mul_pi_lt]
  have hLmul := mul_le_mul_of_nonneg_right hL (Real.log_pos hx).le
  have hbmul :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have he := logWeightedMangoldtSum_error_le_log_sqrt hRH hx
  nlinarith only [he, hLmul, hbmul, hlog, hs]

/-- For 0≤x≤16, the elementary Chebyshev upper bound gives error at most
38sqrt(x)sqrt(sqrt(x)). Use psi(x)≤6x and x≤2sqrt(x)sqrt(sqrt(x)); no RH is needed.
This supplies the small-cutoff branch of the uniform estimate. -/
private theorem psi_error_le_thirty_eight_of_le_sixteen {x : ℝ} (hx : 0 ≤ x) (hx16 : x ≤ 16) :
    |Chebyshev.psi x - x| ≤ 38 * Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  have hlog4 : Real.log 4 ≤ (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num only, Real.log_pow]
    norm_num only at hlog2 ⊢
    linarith only [hlog2]
  have hp := Chebyshev.psi_le_const_mul_self hx
  have hlog := mul_le_mul_of_nonneg_right hlog4 hx
  have hp6 : Chebyshev.psi x ≤ 6 * x := by nlinarith only [hp, hlog]
  have hr4 : Real.sqrt x ≤ 4 :=
    Real.sqrt_le_iff.mpr
      ⟨by norm_num only, by
        norm_num only; exact hx16⟩
  have hs2 : Real.sqrt (Real.sqrt x) ≤ 2 :=
    Real.sqrt_le_iff.mpr
      ⟨by norm_num only, by
        norm_num only; exact hr4⟩
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hxq : x ≤ 2 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) := by
    calc
      x = Real.sqrt x * Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) := by
        rw [mul_assoc, ← pow_two, hsq, ← pow_two, Real.sq_sqrt hx]
      _ ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) * 2 :=
        mul_le_mul_of_nonneg_left hs2
          (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (Real.sqrt x)))
      _ = _ := by ring
  have hq : 0 ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (Real.sqrt x))
  rw [abs_le]
  constructor <;> nlinarith only [hp6, hxq, hq, Chebyshev.psi_nonneg x]

/-- Under RH at every nonnegative cutoff, the Chebyshev error is at most
38sqrt(x)sqrt(sqrt(x)). The smoothing constant 61/10 gives 188/5 above 16;
the elementary bound handles the remaining interval. -/
private theorem psi_error_le_thirty_eight_sqrt (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ 38 * Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  by_cases hl : x ≤ 16
  · exact psi_error_le_thirty_eight_of_le_sixteen hx hl
  · have h :=
      AnalyticNumberTheory.Arithmetic.psi_error_le_three_quarter_of_logWeighted_error
        (by norm_num only : (0 : ℝ) ≤ 61 / 10)
        (fun hu ↦ logWeightedMangoldtSum_error_le_sqrt_sixty_one_tenths hRH hu) (le_of_not_ge hl)
    have hq : 0 ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (Real.sqrt x))
    nlinarith only [h, hq]

/-- Under RH, |psi(x)-x|≤38x^(3/4) for every nonnegative real cutoff.
Express the iterated-square-root bound as a real power. This explicit estimate
supports fixed-kernel Abel comparisons without an unspecified error constant. -/
theorem psi_error_le_thirty_eight (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ 38 * x ^ (3 / 4 : ℝ) := by
  have he : Real.sqrt x * Real.sqrt (Real.sqrt x) = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    rw [←
      Real.rpow_add_of_nonneg hx (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (by norm_num only : (0 : ℝ) ≤ (1 / 2) * (1 / 2))]
    congr 1
    norm_num only
  have h := psi_error_le_thirty_eight_sqrt hRH hx
  rw [mul_assoc, he] at h
  exact h

/-- Under RH and x>1, the smoothed Mangoldt error is at most 2sqrt(x).
Use the logarithm tangent at sqrt(x)=2, log(2π)<1839/1000 and zero mass≤1/40.
The resulting constant gives the explicit Chebyshev error 13 by finite differences. -/
theorem logWeightedMangoldtSum_error_le_two_sqrt (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    |PseudoPrime.AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      2 * Real.sqrt x := by
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  have hsp := Real.sqrt_pos.mpr (zero_lt_one.trans hx)
  have ht := Real.log_le_sub_one_of_pos (div_pos hsp (by norm_num only : (0 : ℝ) < 2))
  rw [Real.log_div hsp.ne' (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_sqrt (zero_lt_one.trans hx).le] at ht
  have htwo : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have hlog : Real.log x ≤ Real.sqrt x - 3 / 5 := by linarith only [ht, htwo]
  have hLmul :=
    mul_le_mul_of_nonneg_right PseudoPrime.Analysis.log_two_mul_pi_lt.le (Real.log_pos hx).le
  have hbmul :=
    mul_le_mul_of_nonneg_right
      PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have he := PseudoPrime.LLS.logWeightedMangoldtSum_error_le_log_sqrt hRH hx
  nlinarith only [he, hLmul, hbmul, hlog, hs]

/-- For nonnegative x≤16, psi(x)≤6x and x≤2sqrt(x)sqrt(sqrt(x)) bound both
sides of the error by 13sqrt(x)sqrt(sqrt(x)). No RH or finite enumeration is needed.
This supplies the small-cutoff branch of the explicit RH estimate. -/
private theorem psi_error_le_thirteen_of_le_sixteen {x : ℝ} (hx : 0 ≤ x) (hx16 : x ≤ 16) :
    |Chebyshev.psi x - x| ≤ 13 * Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  have hlog4 : Real.log 4 ≤ (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num only, Real.log_pow]
    norm_num only at hlog2 ⊢
    linarith only [hlog2]
  have hp := Chebyshev.psi_le_const_mul_self hx
  have hlog := mul_le_mul_of_nonneg_right hlog4 hx
  have hp6 : Chebyshev.psi x ≤ 6 * x := by nlinarith only [hp, hlog]
  have hr4 : Real.sqrt x ≤ 4 :=
    Real.sqrt_le_iff.mpr
      ⟨by norm_num only, by
        norm_num only; exact hx16⟩
  have hs2 : Real.sqrt (Real.sqrt x) ≤ 2 :=
    Real.sqrt_le_iff.mpr
      ⟨by norm_num only, by
        norm_num only; exact hr4⟩
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hxq : x ≤ 2 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) := by
    calc
      x = Real.sqrt x * Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) := by
        rw [mul_assoc, ← pow_two, hsq, ← pow_two, Real.sq_sqrt hx]
      _ ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) * 2 :=
        mul_le_mul_of_nonneg_left hs2
          (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (Real.sqrt x)))
      _ = _ := by ring
  have hq : 0 ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (Real.sqrt x))
  rw [abs_le]
  constructor <;> nlinarith only [hp6, hxq, hq, Chebyshev.psi_nonneg x]

private theorem psi_error_le_thirteen_sqrt (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ 13 * Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  by_cases hl : x ≤ 16
  · exact psi_error_le_thirteen_of_le_sixteen hx hl
  · have h :=
      AnalyticNumberTheory.Arithmetic.psi_error_le_three_quarter_of_logWeighted_error
        (by norm_num only : (0 : ℝ) ≤ 2) (fun hu ↦ logWeightedMangoldtSum_error_le_two_sqrt hRH hu)
        (le_of_not_ge hl)
    have hq : 0 ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (Real.sqrt x))
    nlinarith only [h, hq]

/-- Under RH, |psi(x)-x|≤13x^(3/4) for every nonnegative real cutoff.
Express the iterated-square-root bound as a real power. This explicit estimate
supports fixed-kernel Abel comparisons without an unspecified error constant. -/
theorem psi_error_le_thirteen (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ 13 * x ^ (3 / 4 : ℝ) := by
  have he : Real.sqrt x * Real.sqrt (Real.sqrt x) = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    rw [←
      Real.rpow_add_of_nonneg hx (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (by norm_num only : (0 : ℝ) ≤ (1 / 2) * (1 / 2))]
    congr 1
    norm_num only
  have h := psi_error_le_thirteen_sqrt hRH hx
  rw [mul_assoc, he] at h
  exact h

end PseudoPrime.LLS
