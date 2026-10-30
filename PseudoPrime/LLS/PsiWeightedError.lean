/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbel

/-! # Weighted Mangoldt errors at the selected three-quarter power scale -/

public section

namespace PseudoPrime.LLS.PaperStatements
/-- A power bound for the Chebyshev error bounds the weighted finite-sum error by
an endpoint value and the weighted variation on `[2,x]`. This is the quantitative
Abel interface used by scaled smoothing kernels. -/
theorem mangoldt_weighted_error {x C : ℝ} (hx : 2 ≤ x) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 2 x))
    (hψ : ∀ t ∈ Set.Icc 2 x, |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * f n) -
      (∫ t : ℝ in (2:ℝ)..x, f t) - 2 * f 2| ≤
        C * (x ^ (3 / 4 : ℝ) * |f x| +
          ∫ t : ℝ in (2:ℝ)..x, t ^ (3 / 4 : ℝ) * |deriv f t|) := by
  have hW : IntervalIntegrable (fun t : ℝ ↦ t ^ (3 / 4 : ℝ) * |deriv f t|)
      MeasureTheory.volume 2 x := by
    have h := MeasureTheory.IntegrableOn.mul_continuousOn hi.norm
      (Real.continuous_rpow_const (by norm_num only : (0 : ℝ) ≤ 3 / 4)).continuousOn
      isCompact_Icc
    simpa only [Real.norm_eq_abs, mul_comm] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr h
  have hI := intervalIntegral.norm_integral_le_of_norm_le hx
    (f := fun t : ℝ ↦ (Chebyshev.psi t - t) * deriv f t)
    (g := fun t : ℝ ↦ C * (t ^ (3 / 4 : ℝ) * |deriv f t|))
    (Filter.Eventually.of_forall (fun t ht ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      have h := mul_le_mul_of_nonneg_right
        (hψ t ⟨ht.1.le, ht.2⟩) (abs_nonneg (deriv f t))
      convert h using 1
      ring))
    (hW.const_mul C)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hI
  rw [AnalyticNumberTheory.Arithmetic.mangoldt_weighted_abel hx hd hi]
  have he : (Chebyshev.psi x - x) * f x + 2 * f 2 -
      (∫ t : ℝ in (2:ℝ)..x, (Chebyshev.psi t - t) * deriv f t) - 2 * f 2 =
      (Chebyshev.psi x - x) * f x -
        ∫ t : ℝ in (2:ℝ)..x, (Chebyshev.psi t - t) * deriv f t := by ring
  rw [he]
  calc
    _ ≤ |(Chebyshev.psi x - x) * f x| +
        |∫ t : ℝ in (2:ℝ)..x, (Chebyshev.psi t - t) * deriv f t| := abs_sub _ _
    _ ≤ C * x ^ (3 / 4 : ℝ) * |f x| +
        C * (∫ t : ℝ in (2:ℝ)..x, t ^ (3 / 4 : ℝ) * |deriv f t|) := by
      rw [abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hψ x ⟨hx, le_rfl⟩) (abs_nonneg _)) hI
    _ = _ := by ring
end PseudoPrime.LLS.PaperStatements
