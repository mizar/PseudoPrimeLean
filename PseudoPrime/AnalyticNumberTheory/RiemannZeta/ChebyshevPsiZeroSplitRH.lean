/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroError

/-! # Chebyshev error from split zero sums

Use symmetric integrated differences to bound the unsmoothed Chebyshev function.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, for `h > 0`, `x - h > 1` and a nonnegative cutoff `T`, bound
`|ψ(x) - x|` by the smoothing width, the low inverse-height zero sum and a
high inverse-square bound `C`. Apply the integrated error estimate on both
sides of `x` and the symmetric squeeze. The uniform high-tail estimate is an
explicit hypothesis. -/
theorem psi_error_of_zero_split (hRH : RiemannHypothesis) {T x h C : ℝ} (hT : 0 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h)
    (hC :
      ∀ m : ℕ,
        (∑
            ρ ∈
              ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                        (unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0)).filter
                (fun ρ ↦ ¬|ρ.im| ≤ T),
            (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
          C) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) + Real.sqrt (x + h) * zeroReciprocalSum T +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * C +
        1 / h := by
  have hx0 : 0 < x := by linarith only [hx, hh]
  have hxm : 0 < x - h := zero_lt_one.trans hx
  have hxp : 0 < x + h := by linarith only [hx0, hh]
  have hR : 0 ≤ zeroReciprocalSum T := by
    rw [zeroReciprocalSum_eq]
    exact Finset.sum_nonneg (fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have hC0 : 0 ≤ C := by
    have hs :
      0 ≤
        ∑
          ρ ∈
            ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower 0)
                      (unifiedTauRectangleUpper 2 0)).filter
                  (fun ρ ↦ ¬ρ.re < 0)).filter
              (fun ρ ↦ ¬|ρ.im| ≤ T),
          (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 :=
      Finset.sum_nonneg (fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    exact hs.trans (hC 0)
  have hsqrt : Real.sqrt x ≤ Real.sqrt (x + h) := Real.sqrt_le_sqrt (by linarith only [hh])
  have hp1 : (x - h) ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hxm.le (by linarith only [hh]) (by norm_num only)
  have hp2 : x ^ (3 / 2 : ℝ) ≤ (x + h) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx0.le (by linarith only [hh]) (by norm_num only)
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
  let E :=
    h * (Real.log (2 * Real.pi) + Real.sqrt (x + h) * zeroReciprocalSum T) +
      ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) * C +
      1
  have hupper :=
    psi1_error_of_zero_split hRH hT (by linarith only [hx, hh] : 1 < x)
      (show x < x + h by linarith only [hh]) hC
  have hlower := psi1_error_of_zero_split hRH hT hx (show x - h < x by linarith only [hh]) hC
  have hw1 : x - (x - h) = h := by ring
  have hw2 : x + h - x = h := by ring
  rw [hw1] at hlower
  rw [hw2] at hupper
  have hcancel (q : ℝ) : h * (q / h * C) = q * C := by
    calc
      _ = (q / h * h) * C := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hh.ne']
  simp only [mul_add] at hlower hupper
  rw [hcancel] at hlower hupper
  have hc1 := mul_le_mul_of_nonneg_right hp1 hC0
  have hc2 := mul_le_mul_of_nonneg_right hp2 hC0
  have hs := mul_le_mul_of_nonneg_right hsqrt hR
  have hleft :
    |(Arithmetic.psiIntegralSum x - Arithmetic.psiIntegralSum (x - h)) -
          (x ^ 2 - (x - h) ^ 2) / 2| ≤
      E := by
    have hx1 := (abs_le.mp hlower).1
    have hx2 := (abs_le.mp hlower).2
    dsimp only [E]
    have hs' := mul_le_mul_of_nonneg_left hs hh.le
    have hlog' := mul_nonneg hlog hh.le
    apply abs_le.mpr
    constructor <;> linarith only [hx1, hx2, hc1, hc2, hs', hlog']
  have hright :
    |(Arithmetic.psiIntegralSum (x + h) - Arithmetic.psiIntegralSum x) -
          ((x + h) ^ 2 - x ^ 2) / 2| ≤
      E := by
    have hx1 := (abs_le.mp hupper).1
    have hx2 := (abs_le.mp hupper).2
    dsimp only [E]
    have hlog' := mul_nonneg hlog hh.le
    apply abs_le.mpr
    constructor <;> linarith only [hx1, hx2, hlog']
  have hsqueeze := Arithmetic.psi1_symmetric_squeeze (by linarith only [hx] : h < x) hh hleft hright
  dsimp only [E] at hsqueeze
  have he :
    (h * (Real.log (2 * Real.pi) + Real.sqrt (x + h) * zeroReciprocalSum T) +
          ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) * C +
          1) /
        h =
      Real.log (2 * Real.pi) + Real.sqrt (x + h) * zeroReciprocalSum T +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * C +
        1 / h := by
    rw [add_div, add_div, mul_div_cancel_left₀ _ hh.ne']
    ring
  rw [he] at hsqueeze
  linarith only [hsqueeze]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
