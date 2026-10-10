/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedGammaBounds
public import PseudoPrime.LLS.Extensions.PaperDefinitions

/-!
# Integrated gamma contribution for general L-functions

Gamma-shift residue series and their degree-dependent logarithmic error bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For general data and real `x, σ`, define the finite sum over gamma shifts of the residue
series `x^(-σ - shift j - 2m)/(σ + shift j + 2m)^2`, summed over natural `m`.
The countable sums are totalized; when `x > 1` and the shifts have nonnegative real parts,
the series is absolutely summable for `σ ≥ 1` and integrable over `σ > 1`.
This is the gamma contribution in the shifted logarithmic formula. -/
noncomputable def shiftedGammaSum (f : GeneralLFunction) (x σ : ℝ) : ℂ :=
  AnalyticNumberTheory.General.gammaShiftFamilySum f.shift x σ

/-- For general data and real `x`, define the integral of `shiftedGammaSum x σ` over
`σ > 1`, divided by the complex coercion of `log x`. The definition uses totalized
integration and division. For `x > 1` and shifts with nonnegative real parts, its norm is
bounded by `2 * degree / (x * (log x)^2)`; its real part supplies the gamma error in the
integrated logarithmic formula. -/
noncomputable def gammaLogRemainder (f : GeneralLFunction) (x : ℝ) : ℂ :=
  (∫ σ : ℝ in Set.Ioi 1, f.shiftedGammaSum x σ) / (Real.log x : ℂ)

/-- For x>1 and complex gamma shifts with nonnegative real parts, the gamma residue sum of f
is integrable on sigma>1. Apply the finite-family exponential majorant. -/
theorem integrableOn_shiftedGammaSum (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re) {x : ℝ}
    (hx : 1 < x) : MeasureTheory.IntegrableOn (f.shiftedGammaSum x) (Set.Ioi 1) :=
  AnalyticNumberTheory.General.integrableOn_gammaShiftFamilySum f.shift hx hκ

/-- For x>1 and complex gamma shifts with nonnegative real parts, integrate each gamma residue
termwise. Absolute integrability permits both the finite and countable exchanges. -/
theorem integral_shiftedGammaSum_eq_sum_tsum (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re)
    {x : ℝ} (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1, f.shiftedGammaSum x σ) =
      ∑ j : Fin f.degree,
        ∑' m : ℕ,
          ∫ σ : ℝ in Set.Ioi 1, AnalyticNumberTheory.General.gammaShiftResidue x (f.shift j) σ m :=
  AnalyticNumberTheory.General.integral_gammaShiftFamilySum_eq_sum_tsum f.shift hx hκ

/-- For x>1 and complex gamma shifts with nonnegative real parts, the normalized integrated gamma
sum has norm at most 2*degree/(x*log(x)^2). Sum the per-factor estimates. -/
theorem norm_gammaLogRemainder_le (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re) {x : ℝ}
    (hx : 1 < x) : ‖f.gammaLogRemainder x‖ ≤ 2 * (f.degree : ℝ) / (x * (Real.log x) ^ 2) :=
  AnalyticNumberTheory.General.norm_integrated_gammaShiftFamilySum_div_log_le f.shift hx hκ

/-- For x>1 and complex gamma shifts with nonnegative real parts, the real gamma remainder equals
2*degree*theta/(x*log(x)^2) with |theta|<=1. Normalize the norm bound;
a zero bound forces the remainder to vanish. This supplies the gamma error coefficient. -/
theorem gammaLogRemainder_eq_theta (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re) {x : ℝ}
    (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧ (f.gammaLogRemainder x).re = 2 * (f.degree : ℝ) * θ / (x * (Real.log x) ^ 2) := by
  let Z : ℂ := f.gammaLogRemainder x
  let B : ℝ := 2 * (f.degree : ℝ) / (x * (Real.log x) ^ 2)
  have hB : 0 ≤ B :=
    div_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _))
      (mul_nonneg (zero_lt_one.trans hx).le (sq_nonneg _))
  have hnorm : ‖Z‖ ≤ B := norm_gammaLogRemainder_le f hκ hx
  have habs : |Z.re| ≤ B := (Complex.abs_re_le_norm Z).trans hnorm
  by_cases hB0 : B = 0
  · have hZ : Z = 0 := norm_eq_zero.mp (le_antisymm (hB0 ▸ hnorm) (norm_nonneg _))
    refine ⟨0, by norm_num only [abs_zero, zero_le_one], ?_⟩
    change Z.re = _
    rw [hZ, Complex.zero_re, mul_zero, zero_div]
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    refine ⟨Z.re / B, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hBp]
      exact (div_le_one hBp).mpr habs
    · change Z.re = 2 * (f.degree : ℝ) * (Z.re / B) / (x * (Real.log x) ^ 2)
      calc
        Z.re = (Z.re / B) * B := (div_mul_cancel₀ _ hB0).symm
        _ = _ := by
          dsimp only [B]; ring

/-- For an admissible f and x>1, the real gamma remainder has a coefficient
of absolute value at most one with scale 2*degree/(x*log(x)^2).
Extract nonnegativity of the shifts' real parts from admissibility,
and apply the normalized bound. -/
theorem gammaLogRemainder_eq_theta_of_admissible (f : GeneralLFunction) (hf : f.IsAdmissible)
    {x : ℝ} (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧ (f.gammaLogRemainder x).re = 2 * (f.degree : ℝ) * θ / (x * (Real.log x) ^ 2) :=
  gammaLogRemainder_eq_theta f hf.2.2.2.1 hx

end PseudoPrime.LLS.Extensions.GeneralLFunction
