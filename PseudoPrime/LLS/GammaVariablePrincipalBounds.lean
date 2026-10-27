/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneComparison

/-! # Variable-scale principal Gamma and ramp bounds

Explicit errors apply at every scale at least one.
Combine them with the non-one comparison without a fixed logarithmic gate.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and scale x≥1, the actual normalized ramp Mangoldt sum is at least
 its exact mass times sqrt(x) minus the explicit variation error.
 Divide the proved error functional bound by the positive square root.
 This removes the fixed logarithmic threshold from the principal lower input. -/
theorem gamma_ramp_sum_lower_variable (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        ((135 / 20 : ℝ) * Real.sqrt x +
            86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20)) /
          Real.sqrt x ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x := by
  have hx0 := zero_lt_one.trans_le hx
  have he := gamma_ramp_error_functional_bound hRH hx
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0]
  have habs := (abs_le.mp he).1
  have hdiv := div_le_div_of_nonneg_right habs (Real.sqrt_nonneg x)
  rw [neg_div] at hdiv
  linarith only [hdiv]

/-- Under RH and x≥1, the full principal Gamma series is at most sqrt(x) plus
 the explicit exponential-sum error divided by sqrt(x). Bound every finite sum,
 then use absolute summability to pass to the full series.
 This supplies the principal upper input at variable scale. -/
theorem gamma_level_one_sum_upper_variable (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x +
        (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x := by
  have hx0 := zero_lt_one.trans_le hx
  apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
  intro N
  have heq :
    (∑ n ∈ Finset.Ioc 0 N,
        (PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) / Real.sqrt x := by
    simpa only [Nat.floor_natCast] using
      PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
  rw [heq]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
  rw [add_mul, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx0).ne', ← pow_two, Real.sq_sqrt hx0.le]
  simpa only [add_assoc] using exponentialMangoldtSum_upper_uniform hRH hx N

end PseudoPrime.LLS
