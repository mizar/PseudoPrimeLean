/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperDefinitions
public import PseudoPrime.AnalyticNumberTheory.Gamma.UniformDigamma

/-!
# Gamma endpoints and analytic conductor logarithms

The logarithmic conductor and twice the gamma endpoint have the same arithmetic term.
Their difference is the finite sum of complex digamma errors. The uniform logarithmic
digamma estimate bounds its absolute value by degree times a universal constant.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible data, every gamma argument at one has positive norm.
Its real part is positive because the shift real part is nonnegative. Compare real part
with norm. This ensures that conductor products and their logarithms are well-defined. -/
theorem gammaArgument_one_norm_pos (f : GeneralLFunction) (hf : f.IsAdmissible) (j : Fin f.degree) :
    0 < ‖(1 + f.shift j) / 2‖ := by
  have hr : 0 < ((1 + f.shift j) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith only [hf.2.2.2.1 j]
  exact hr.trans_le (Complex.re_le_norm _)

/-- For admissible data, the analytic conductor is strictly positive.
The arithmetic conductor, pi power, and all gamma-argument norms are positive; multiply
the factors. This justifies logarithmic conductor identities in the remainder bounds. -/
theorem analyticConductor_pos (f : GeneralLFunction) (hf : f.IsAdmissible) :
    0 < f.analyticConductor := by
  unfold analyticConductor
  exact
    mul_pos (div_pos (Nat.cast_pos.mpr hf.2.1) (pow_pos Real.pi_pos f.degree))
      (Finset.prod_pos (fun j _ ↦ gammaArgument_one_norm_pos f hf j))

/-- For admissible data, the logarithmic analytic conductor splits into the logarithm
of the conductor divided by the pi power, plus the finite sum of gamma-argument logarithms.
Apply the logarithm product identities to nonzero factors. This permits comparison with
the gamma endpoint without changing the analytic conductor normalization. -/
theorem log_analyticConductor (f : GeneralLFunction) (hf : f.IsAdmissible) :
    Real.log f.analyticConductor =
      Real.log ((f.conductor : ℝ) / Real.pi ^ f.degree) +
        ∑ j : Fin f.degree, Real.log ‖(1 + f.shift j) / 2‖ := by
  have hn (j : Fin f.degree) : ‖(1 + f.shift j) / 2‖ ≠ 0 := (gammaArgument_one_norm_pos f hf j).ne'
  have hq : ((f.conductor : ℝ) / Real.pi ^ f.degree) ≠ 0 :=
    (div_pos (Nat.cast_pos.mpr hf.2.1) (pow_pos Real.pi_pos f.degree)).ne'
  rw [analyticConductor, Real.log_mul hq (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hn j)),
    Real.log_prod (fun j _ ↦ hn j)]

/-- For admissible data, twice the gamma endpoint minus the logarithmic analytic conductor
is the sum of real digamma values minus logarithms of gamma-argument norms. Expand the
endpoint and conductor logarithms and cancel the arithmetic term. This identifies the
precise complex digamma estimate needed for a degree-uniform endpoint bound. -/
theorem twice_gammaLogDerivativeAtOne_sub_log_conductor (f : GeneralLFunction)
    (hf : f.IsAdmissible) :
    2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor =
      ∑ j : Fin f.degree,
        ((logDeriv Complex.Gamma ((1 + f.shift j) / 2)).re - Real.log ‖(1 + f.shift j) / 2‖) := by
  rw [gammaLogDerivativeAtOne, log_analyticConductor f hf, Finset.sum_sub_distrib]
  ring

/-- For admissible data, the absolute difference between twice the gamma endpoint and
the logarithmic analytic conductor is at most the degree times a universal constant.
The gamma arguments have real part at least one half; sum their uniform digamma errors.
This removes dependence on individual shifts from the archimedean endpoint error. -/
theorem abs_twice_gammaLogDerivativeAtOne_sub_log_conductor_le (f : GeneralLFunction)
    (hf : f.IsAdmissible) :
    |2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor| ≤
      (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound := by
  rw [twice_gammaLogDerivativeAtOne_sub_log_conductor f hf]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb (j : Fin f.degree) :
    |(logDeriv Complex.Gamma ((1 + f.shift j) / 2)).re - Real.log ‖(1 + f.shift j) / 2‖| ≤
      AnalyticNumberTheory.Gamma.digammaLogErrorBound := by
    have hr : 1 / 2 ≤ ((1 + f.shift j) / 2).re := by
      rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
      linarith only [hf.2.2.2.1 j]
    simpa only [Complex.digamma_def, logDeriv_apply] using
      AnalyticNumberTheory.Gamma.abs_re_digamma_sub_log_norm_le hr
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hb j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

end PseudoPrime.LLS.Extensions.GeneralLFunction
