/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.TruncatedValueFormula
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-!
# Uniform bounds for truncated general L-values

The exact truncated formula has conductor-degree error bounds uniform in the L-function.
Arithmetic majorants are kept explicit for applying quantitative prime-sum estimates.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The conductor-centered truncation error bound, depending only on the cutoff, degree
and analytic conductor. Substitute universal conductor bounds for zero mass, reciprocal
remainder and zero-mass remainder, and include the real reciprocal Mangoldt majorant.
It bounds the error after the leading log-conductor term in the general L-value formula. -/
noncomputable def truncatedConductorErrorBound (f : GeneralLFunction) (x : ℝ) : ℝ :=
  let U := (17 / 7 : ℝ) * |Real.log f.analyticConductor| + (f.degree : ℝ) * zeroMassDegreeBound
  let R :=
    (|Real.log f.analyticConductor| +
          (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
          2 * U) /
        (2 * x) +
      (f.degree : ℝ) * ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x)
  let Z :=
    (f.degree : ℝ) *
        (2 * AnalyticNumberTheory.Gamma.digammaLogErrorBound + 3 * |zeroMassDegreeBound| +
          2 * (1 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) +
          2 * (Real.log 4 + 4)) +
      (58 / 7) * (|Real.log f.analyticConductor| / Real.sqrt x)
  U / (2 * x * Real.log x) + U / (Real.sqrt x * (Real.log x) ^ 2) +
    2 * (f.degree : ℝ) / (x * (Real.log x) ^ 2) +
    R / Real.log x +
    (2 * ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x) + Z) /
      (Real.sqrt x * Real.log x)

/-- For admissible RH data and cutoff at least two, a bounded real coefficient represents
the leading log-conductor term, with the remaining error bounded uniformly in the data.
Insert the conductor-degree mass bound and universal remainder estimates in the exact
conductor-centered formula. This reduces the final value estimate to arithmetic majorants. -/
theorem exists_truncatedValue_conductor_error_le_uniform (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        |Real.log ‖f.L 1‖ - (f.truncatedValueSum x).re -
              θ * Real.log f.analyticConductor / (Real.sqrt x * Real.log x)| ≤
          f.truncatedConductorErrorBound x := by
  have hx1 : 1 < x := lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  obtain ⟨θ, hθ, he⟩ := exists_truncatedValue_conductor_error_le f hf hRH hx
  refine ⟨θ, hθ, he.trans ?_⟩
  have hU := zeroMass_le_conductor_degree f hf hRH
  have h1 :=
    div_le_div_of_nonneg_right hU
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hx0.le) hl.le)
  have h2 := div_le_div_of_nonneg_right hU (mul_nonneg hs.le (sq_nonneg (Real.log x)))
  have hR := norm_reciprocalRemainder_le_conductor f hf hRH hx1
  have h3 :=
    div_le_div_of_nonneg_right
      (add_le_add
        (le_refl
          (|Real.log f.analyticConductor| +
            (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound))
        (mul_le_mul_of_nonneg_left hU (by norm_num only : (0 : ℝ) ≤ 2)))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hx0.le)
  have h4 :=
    div_le_div_of_nonneg_right
      (hR.trans
        (add_le_add h3
          (le_refl
            ((f.degree : ℝ) *
              ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x)))))
      hl.le
  have h5 :=
    div_le_div_of_nonneg_right
      (add_le_add
        (le_refl (2 * ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x)))
        (norm_zeroMassReciprocalRemainder_le_degree_add_conductor f hf hRH hx1))
      (mul_nonneg hs.le hl.le)
  unfold truncatedConductorErrorBound
  dsimp only
  linarith only [h1, h2, h4, h5]

/-- For admissible data and a cutoff above one, the truncated sum norm is at most the
 degree times the real Mangoldt majorant. Apply the coefficient norm bound and remove
 absolute values using nonnegative weights. This supplies the arithmetic value bound. -/
theorem norm_truncatedValueSum_le_majorant (f : GeneralLFunction) (hf : f.IsAdmissible) {x : ℝ}
    (hx : 1 < x) :
    ‖f.truncatedValueSum x‖ ≤
      (f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x := by
  have h := norm_truncatedValueSum_le f hf x
  have he :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        |ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x))|) =
      AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x := by
    apply Finset.sum_congr rfl
    intro n hn
    exact abs_of_nonneg (AnalyticNumberTheory.Arithmetic.truncatedMangoldtTerm_nonneg hx hn)
  exact he ▸ h

/-- For admissible RH data and cutoff at least two, the absolute logarithm of the L-value
is bounded by the degree times the truncated majorant, the leading conductor contribution
and the uniform truncation error. Bound the real truncated sum and the bounded coefficient
in the conductor-centered formula. This gives symmetric magnitude estimates. -/
theorem abs_log_norm_L_one_le_truncated_majorants (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |Real.log ‖f.L 1‖| ≤
      (f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x +
        |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
        f.truncatedConductorErrorBound x := by
  have hx1 : 1 < x := lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx
  obtain ⟨θ, hθ, he⟩ := exists_truncatedValue_conductor_error_le_uniform f hf hRH hx
  have hT :=
    (Complex.abs_re_le_norm (f.truncatedValueSum x)).trans
      (norm_truncatedValueSum_le_majorant f hf hx1)
  have hθC :
    |θ * Real.log f.analyticConductor / (Real.sqrt x * Real.log x)| ≤
      |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) := by
    rw [abs_div, abs_mul,
      abs_of_pos (mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx1)) (Real.log_pos hx1))]
    exact
      div_le_div_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hθ)
        (mul_nonneg (Real.sqrt_nonneg x) (Real.log_pos hx1).le)
  apply abs_le.mpr
  constructor <;>
    linarith only [(abs_le.mp he).1, (abs_le.mp he).2, (abs_le.mp hT).1, (abs_le.mp hT).2,
      (abs_le.mp hθC).1, (abs_le.mp hθC).2]

/-- For admissible RH data and cutoff at least two, both the L-value norm and its reciprocal
are at most the exponential of the arithmetic-conductor bound. Exponentiate the positive
and negative logarithm bounds. This is a coarse bound preceding the sharp LLS constants. -/
theorem norm_L_one_and_reciprocal_le_exp_truncated_majorants (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    ‖f.L 1‖ ≤
        Real.exp
          ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x +
            |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
            f.truncatedConductorErrorBound x) ∧
      1 / ‖f.L 1‖ ≤
        Real.exp
          ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x +
            |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
            f.truncatedConductorErrorBound x) := by
  have hb := abs_log_norm_L_one_le_truncated_majorants f hf hRH hx
  constructor
  · exact
      (Real.le_exp_log ‖f.L 1‖).trans
        (Real.exp_le_exp.mpr ((le_abs_self (Real.log ‖f.L 1‖)).trans hb))
  · apply (Real.le_exp_log (1 / ‖f.L 1‖)).trans
    apply Real.exp_le_exp.mpr
    rw [one_div, Real.log_inv]
    exact (neg_le_abs (Real.log ‖f.L 1‖)).trans hb

end PseudoPrime.LLS.Extensions.GeneralLFunction
