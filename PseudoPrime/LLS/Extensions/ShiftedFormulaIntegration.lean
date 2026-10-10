/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.RealAxisIntegration
public import PseudoPrime.LLS.Extensions.LogValueFormula

/-!
# Integration of the general shifted logarithmic formula

Finite arithmetic sums, shifted origin residues, and zero and gamma contributions
are integrated over the real shift. The resulting conditional identity converts an exact
shifted explicit formula into the logarithmic L-value decomposition.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The finite sum over 1 ≤ n ≤ floor x of
`a_f(n) Λ(n) n^(-σ) log(x/n)`, using the Mangoldt coefficients of f.
It is defined for all real x and σ without analytic assumptions.
Integration over σ > 1 supplies the factor 1/(n log n), connecting this sum
to the normalized arithmetic term in the logarithmic L-value formula. -/
noncomputable def shiftedArithmeticSum (f : GeneralLFunction) (x σ : ℝ) : ℂ :=
  AnalyticNumberTheory.General.logarithmicWeightedSum
    (AnalyticNumberTheory.General.shiftedLSeriesCoefficient
      (fun n ↦ f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
    x

/-- For every x, the shifted arithmetic sum is integrable over sigma>1.
Its finite terms decay exponentially for n>1, and the Mangoldt value at one vanishes. -/
theorem integrableOn_shiftedArithmeticSum (f : GeneralLFunction) (x : ℝ) :
    MeasureTheory.IntegrableOn (f.shiftedArithmeticSum x) (Set.Ioi 1) := by
  have ha : f.mangoldtCoefficient 1 * (ArithmeticFunction.vonMangoldt 1 : ℂ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero, mul_zero]
  change
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          AnalyticNumberTheory.General.shiftedLSeriesCoefficient
              (fun n ↦ f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ n *
            (Real.log (x / n) : ℂ))
      (Set.Ioi 1)
  apply MeasureTheory.integrable_finsetSum
  intro n hn
  exact AnalyticNumberTheory.General.integrableOn_shifted_log_term _ ha x (Finset.mem_Ioc.mp hn).1

/-- For arbitrary general L-function data and real x, logValueSum is the integral
of shiftedArithmeticSum over σ > 1, divided by the complex cast of log x.
Integrate the finite terms to obtain 1/(n log n); Λ(1) = 0 removes the constant term.
All divisions are totalized, so the identity also covers log x = 0.
This is the arithmetic part of the integrated shifted formula. -/
theorem logValueSum_eq_integrated_shiftedArithmeticSum (f : GeneralLFunction) (x : ℝ) :
    f.logValueSum x = (∫ σ : ℝ in Set.Ioi 1, f.shiftedArithmeticSum x σ) / (Real.log x : ℂ) := by
  have ha : f.mangoldtCoefficient 1 * (ArithmeticFunction.vonMangoldt 1 : ℂ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero, mul_zero]
  rw [show
      (fun σ : ℝ ↦ f.shiftedArithmeticSum x σ) =
        (fun σ ↦
          AnalyticNumberTheory.General.logarithmicWeightedSum
            (AnalyticNumberTheory.General.shiftedLSeriesCoefficient
              (fun n ↦ f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
            x)
      from rfl,
    AnalyticNumberTheory.General.integral_logarithmicWeightedSum_shifted _ ha]
  rw [Finset.sum_div]
  unfold logValueSum
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- For admissible RH data and x>1, the Mellin-origin regularization derivative is
integrable over sigma>1. Its two terms are the integrable logarithmic derivative
and its derivative; the local regularization identity identifies the integrand. -/
theorem integrableOn_originRegularization (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦
        deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ)) 0)
      (Set.Ioi 1) := by
  have hi :=
    (integrableOn_deriv_logDeriv_ordinary_real f hf hRH).neg.sub
      ((integrableOn_logDeriv_ordinary_real f hf hRH).mul_const (Real.log x : ℂ))
  apply hi.congr
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact
    (AnalyticNumberTheory.General.deriv_shiftedLogarithmicRegularization
        (analyticAt_ordinary_of_re_pos f hf
          (by simpa only [Complex.ofReal_re] using lt_trans zero_lt_one hσ))
        (ordinary_ne_zero_of_re_gt_half f hf hRH
          (by
            simpa only [Complex.ofReal_re] using
              lt_trans (show (1 / 2 : ℝ) < 1 by norm_num only) hσ))
        (zero_lt_one.trans hx)).symm

/-- For admissible data satisfying individual RH and x > 1, assume the exact shifted
arithmetic formula for every real σ > 1: origin contribution plus zeros minus gamma.
Then log (norm (L 1)) equals the finite arithmetic term, the gamma endpoint and
remainder, and the negative zero-mass and integrated-zero terms shown below.
Integrate the assumed identity, using summability-based integrability of the residue
terms and the proved origin endpoint. This connects an exact shifted formula
to the general logarithmic L-value decomposition. -/
theorem integrated_decomposition_of_shifted_formula (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hformula :
      ∀ σ : ℝ,
        1 < σ →
          f.shiftedArithmeticSum x σ =
            deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ)) 0 +
                f.shiftedZeroSum x σ -
              f.shiftedGammaSum x σ) :
    Real.log ‖f.L 1‖ =
      (f.logValueSum x).re + f.gammaLogDerivativeAtOne / Real.log x -
          f.zeroMass / (2 * Real.log x) -
          ((∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) / (Real.log x : ℂ)).re +
        (f.gammaLogRemainder x).re := by
  have ho := integrableOn_originRegularization f hf hRH hx
  have hz := integrableOn_shiftedZeroSum f hRH (summable_zeroMassTerm_of_admissible f hf hRH) hx
  have hg := integrableOn_shiftedGammaSum f hf.2.2.2.1 hx
  have he :
    (∫ σ : ℝ in Set.Ioi 1, f.shiftedArithmeticSum x σ) =
      (∫ σ : ℝ in Set.Ioi 1,
            deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ)) 0) +
          (∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) -
        (∫ σ : ℝ in Set.Ioi 1, f.shiftedGammaSum x σ) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hformula]
    have hsub := MeasureTheory.integral_sub (ho.add hz) hg
    simp only [Pi.add_apply] at hsub
    rw [hsub, MeasureTheory.integral_add ho hz]
  have hor := integral_origin_regularization_re_div_log_of_admissible f hf hRH hx
  have hre := Complex.reCLM.integral_comp_comm ho
  change
    (∫ σ : ℝ in Set.Ioi 1,
        (deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ))
            0).re) =
      (∫ σ : ℝ in Set.Ioi 1,
          deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ))
            0).re at hre
  rw [hre] at hor
  rw [logValueSum_eq_integrated_shiftedArithmeticSum, he, gammaLogRemainder, Complex.div_ofReal_re,
    Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sub_re, Complex.add_re]
  ring_nf at hor ⊢
  linarith only [hor]

end PseudoPrime.LLS.Extensions.GeneralLFunction
