/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.GammaNodeRationalCertificate
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
public import PseudoPrime.Analysis.GammaResolventCertificate

/-! # Certified signed even Gamma resolvent correction -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- At a positive real node, the real logarithmic derivative of the even
Gamma factor is one half of digamma minus log pi. Positivity excludes all poles.
Taking real parts of the exact complex identity gives the scalar certificate interface. -/
theorem re_logDeriv_Gammaℝ_of_pos {σ : ℝ} (hσ : 0 < σ) :
    (logDeriv Complex.Gammaℝ (σ : ℂ)).re =
      ((Complex.digamma ((σ / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 := by
  have hh : 0 < (((σ : ℂ) / 2).re) := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re] using
      (div_pos hσ (by norm_num only : (0 : ℝ) < 2))
  rw [DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat (not_neg_nat_of_re_pos hh)]
  norm_num only [Complex.add_re, Complex.div_re, show (2 : ℂ).re = (2 : ℝ) from rfl,
    show (2 : ℂ).im = (0 : ℝ) from rfl, Complex.normSq_ofNat, mul_zero, add_zero, Complex.neg_re,
    Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) by rw [Complex.ofReal_div, Complex.ofReal_ofNat]]
  ring

/-- The actual signed even Gamma-factor correction is at most -159/100.
Apply the eight digamma intervals with the appropriate sign and the log pi
interval, then verify the final rational linear inequality. This removes
the fixed Gamma-factor numerical obligation from the analytic budget. -/
theorem gammaResolvent_even_correction_le :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      (-159 / 100 : ℝ) := by
  have h0 := gamma_digamma_node_0_bounds
  have h1 := gamma_digamma_node_1_bounds
  have h2 := gamma_digamma_node_2_bounds
  have h3 := gamma_digamma_node_3_bounds
  have h4 := gamma_digamma_node_4_bounds
  have h5 := gamma_digamma_node_5_bounds
  have h6 := gamma_digamma_node_6_bounds
  have h7 := gamma_digamma_node_7_bounds
  have hp := gamma_log_pi_bounds
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at h0 h1 h2 h3 h4 h5 h6 h7 hp
  norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero, zero_mul, zero_add,
    add_zero, ← Complex.ofReal_add]
  rw [re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 21 / 20),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 13 / 10),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 3 / 2),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 11 / 5),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 14 / 5),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 37 / 10),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 5),
    re_logDeriv_Gammaℝ_of_pos (by norm_num only : (0 : ℝ) < 15 / 2)]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [h0.2, h1.2, h2.2, h3.2, h4.1, h5.1, h6.2, h7.1, hp.1]

end PseudoPrime.AnalyticNumberTheory.Gamma
