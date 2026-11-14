/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombinedGeneralRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScale43

/-! # Normalization of a general combined zero budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, any combined zero budget `B` at cutoff `2/δ` gives the
displayed normalized ψ error bound when `0 < δ ≤ 1/2` and the lower smoothing
endpoint exceeds one. The geometric scale bounds are independent of `B`. -/
theorem psi_error_combined_scale (hRH : RiemannHypothesis) {x δ B : ℝ} (hx : 0 < x) (hd : 0 < δ)
    (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ)
    (hbudget : zeroReciprocalSum (2 / δ) + (2 / δ) * ordinateTail (2 / δ) ≤ B) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x + (1 + δ) * B +
        1 / (x * δ * Real.sqrt x) := by
  have hp := scale_power_bounds hx hd.le hd2
  have hs : Real.sqrt (x + x * δ) ≤ Real.sqrt x * (1 + δ) := by
    have hh := mul_nonneg (Real.sqrt_nonneg x) hd.le
    nlinarith only [hp.1, hh]
  have hpow : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hr := Real.rpow_add hx (1 : ℝ) (1 / 2 : ℝ)
    convert hr using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have htail :
    ((x + x * δ) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / (x * δ) ≤
      (Real.sqrt x * (1 + δ)) * (2 / δ) := by
    have ht := add_le_add hp.2 (le_refl (x ^ (3 / 2 : ℝ)))
    apply le_trans (div_le_div_of_nonneg_right ht (mul_nonneg hx.le hd.le))
    rw [hpow]
    have hxinv := mul_inv_cancel₀ hx.ne'
    simp only [div_eq_mul_inv, mul_inv_rev]
    have heq :
      (x * Real.sqrt x * (1 + 2 * δ) + x * Real.sqrt x) * (δ⁻¹ * x⁻¹) =
        Real.sqrt x * (1 + δ) * (2 * δ⁻¹) := by
      linear_combination (2 * Real.sqrt x * (1 + δ) * δ⁻¹) * hxinv
    exact le_of_eq heq
  have hA : 0 ≤ Real.sqrt x * (1 + δ) := mul_nonneg (Real.sqrt_nonneg x) (by linarith only [hd])
  have h :
    |Chebyshev.psi x - x| ≤
      x * δ / 2 + Real.log (2 * Real.pi) + Real.sqrt x * (1 + δ) * B + 1 / (x * δ) :=
    psi_error_of_combined hRH (div_nonneg (by norm_num only) hd.le) (mul_pos hx hd) hleft hA hs
      htail hbudget
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hi := mul_inv_cancel₀ hs0.ne'
  have hsx : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
    calc
      x * (Real.sqrt x)⁻¹ = Real.sqrt x ^ 2 * (Real.sqrt x)⁻¹ :=
        congrArg (fun z : ℝ ↦ z * (Real.sqrt x)⁻¹) (Real.sq_sqrt hx.le).symm
      _ = Real.sqrt x * (Real.sqrt x * (Real.sqrt x)⁻¹) := by ring
      _ = _ := by
        rw [hi]; ring
  have heq :
    (x * δ / 2 + Real.log (2 * Real.pi) + Real.sqrt x * (1 + δ) * B + 1 / (x * δ)) / Real.sqrt x =
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x + (1 + δ) * B +
        1 / (x * δ * Real.sqrt x) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination (δ / 2) * hsx + ((1 + δ) * B) * hi
  have hdiv := div_le_div_of_nonneg_right h hs0.le
  rw [heq] at hdiv
  exact hdiv

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
