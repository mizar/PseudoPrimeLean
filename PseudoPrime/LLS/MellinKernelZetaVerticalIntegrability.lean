/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelVerticalIntegrability
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.VerticalLogDerivGrowth

/-! # Absolute integrability of vertical xi Mellin contours

Full-line logarithmic xi bounds and quadratic kernel decay make both shifted
vertical integrands absolutely integrable at every positive scale.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- On an admissible right line in `(1/2,1]` and at positive scale, the negative
ξ logarithmic derivative times the kernel and Mellin power is integrable.
Apply the right-half-plane logarithmic majorant and continuity to the generic
weighted-line theorem. This removes the right integrability assumption. -/
theorem integrable_xi_right_line (K : MellinKernel) {c x : ℝ} (hc : 1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hc2 : c ≤ 1) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hσ : 1 < c + 1 / 2 := by linarith only [hc]
  obtain ⟨A, _, hb⟩ :=
    AnalyticNumberTheory.RiemannXi.exists_norm_logDeriv_vertical_right_le_log hσ
      (by linarith only [hc2])
  have hl : -1 / 2 - K.delta < c := by linarith only [hc, K.delta_pos]
  have he (t : ℝ) : ((c + 1 / 2 : ℝ) : ℂ) + Complex.I * t = ((c : ℂ) + Complex.I * t) + 1 / 2 := by
    rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hi :=
    integrable_logWeighted_power_line K hl hc' (by linarith only [hc]) hx
      (AnalyticNumberTheory.RiemannXi.continuous_logDeriv_vertical_right hσ).aestronglyMeasurable hb
  simpa only [he, Pi.neg_def, neg_mul, mul_assoc] using hi.neg

/-- On an admissible left line in `[-1,-1/2)` and at positive scale, the negative
ξ logarithmic derivative times the kernel and Mellin power is integrable.
The functional equation supplies logarithmic growth and continuity; apply the
generic weighted-line theorem. This removes the left integrability assumption. -/
theorem integrable_xi_left_line (K : MellinKernel) {c x : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c < -1 / 2) (hc2 : -1 ≤ c) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hσ : c + 1 / 2 < 0 := by linarith only [hc']
  obtain ⟨A, _, hb⟩ :=
    AnalyticNumberTheory.RiemannXi.exists_norm_logDeriv_vertical_left_le_log hσ
      (by linarith only [hc2])
  have hu : c ≤ 1 / 2 + K.delta := by linarith only [hc', K.delta_pos]
  have he (t : ℝ) : ((c + 1 / 2 : ℝ) : ℂ) + Complex.I * t = ((c : ℂ) + Complex.I * t) + 1 / 2 := by
    rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hi :=
    integrable_logWeighted_power_line K hc hu (ne_of_lt hc') hx
      (AnalyticNumberTheory.RiemannXi.continuous_logDeriv_vertical_left hσ).aestronglyMeasurable hb
  simpa only [he, Pi.neg_def, neg_mul, mul_assoc] using hi.neg

end PseudoPrime.LLS.PaperStatements.MellinKernel
