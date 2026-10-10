/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.OrdinaryEndpoint
public import PseudoPrime.LLS.Extensions.LogarithmicEndpoints
public import PseudoPrime.AnalyticNumberTheory.General.LSeriesDecay
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Real-axis integration for admissible RH L-functions

Dirichlet-series differentiation gives exponential tails. The entire completion provides
analyticity and nonvanishing on the real ray, discharging the origin integration hypotheses.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Admissibility makes the ordinary L-function analytic on the right half-plane.
Complex differentiability on a neighborhood follows from the nonzero completion factor. -/
theorem analyticAt_ordinary_of_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ f.L s := by
  have hd : DifferentiableOn ℂ f.L {z : ℂ | 0 < z.re} := fun z hz ↦
    (differentiableAt_ordinary_of_re_pos f hf hz).differentiableWithinAt
  exact hd.analyticAt (Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs))

/-- An admissible RH function has no ordinary zero to the right of the critical line.
The completion identity would otherwise produce a completed zero outside that line. -/
theorem ordinary_ne_zero_of_re_gt_half (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) : f.L s ≠ 0 := by
  intro hz
  have hc := completed_ne_zero_of_re_ne_half hRH (ne_of_gt hs)
  apply hc
  rw [hf.2.2.2.2.2.2.1 s (lt_trans (by norm_num only) hs), hz, mul_zero]

/-- The ordinary logarithmic derivative is analytic to the right of the critical line
under admissibility and RH. Analyticity and nonvanishing justify the quotient. -/
theorem analyticAt_logDeriv_ordinary_of_re_gt_half (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) : AnalyticAt ℂ (logDeriv f.L) s := by
  have hF := analyticAt_ordinary_of_re_pos f hf (lt_trans (by norm_num only) hs)
  exact hF.deriv.div hF (ordinary_ne_zero_of_re_gt_half f hf hRH hs)

/-- The admissible Dirichlet series has finite absolute convergence abscissa.
Absolute convergence at two supplies the bound used for real-axis decay. -/
theorem coefficient_abscissa_lt_top (f : GeneralLFunction) (hf : f.IsAdmissible) :
    LSeries.abscissaOfAbsConv f.coefficient < ⊤ := by
  have hab :=
    (hf.2.2.2.2.2.1 ((2 : ℝ) : ℂ) (by norm_num only [Complex.ofReal_re])).1.abscissaOfAbsConv_le
  exact hab.trans_lt (EReal.coe_lt_top _)

/-- For admissible data and Re s > 2, the ordinary derivative equals the negative
Dirichlet series with coefficients multiplied by log n. Identify L with its coefficient
series near s, bound the absolute convergence abscissa by two, and apply L-series
differentiation. This represents the first derivative for real-axis tail estimates. -/
theorem deriv_ordinary_eq_neg_logMul_series (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 2 < s.re) : deriv f.L s = -LSeries (LSeries.logMul f.coefficient) s := by
  have he : f.L =ᶠ[nhds s] LSeries f.coefficient := by
    filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds (lt_trans (show (1 : ℝ) < 2 by norm_num only) hs))] with
      z hz
    exact (hf.2.2.2.2.2.1 z hz).2.1
  rw [he.deriv_eq, LSeries_deriv]
  have hab :=
    (hf.2.2.2.2.2.1 ((2 : ℝ) : ℂ) (by norm_num only [Complex.ofReal_re])).1.abscissaOfAbsConv_le
  exact hab.trans_lt (by exact_mod_cast hs)

/-- For admissible data and Re s > 2, the second ordinary derivative equals the
Dirichlet series with coefficients multiplied by (log n)². Differentiate the local
first-derivative identity and use preservation of the absolute convergence abscissa
under logarithmic weighting. This supplies the second-derivative tail estimate. -/
theorem deriv_deriv_ordinary_eq_logMul_logMul_series (f : GeneralLFunction) (hf : f.IsAdmissible)
    {s : ℂ} (hs : 2 < s.re) :
    deriv (deriv f.L) s = LSeries (LSeries.logMul (LSeries.logMul f.coefficient)) s := by
  have he : deriv f.L =ᶠ[nhds s] -LSeries (LSeries.logMul f.coefficient) := by
    filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs)] with z
      hz
    exact deriv_ordinary_eq_neg_logMul_series f hf hz
  have ha : LSeries.abscissaOfAbsConv (LSeries.logMul f.coefficient) < s.re := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    have hab :=
      (hf.2.2.2.2.2.1 ((2 : ℝ) : ℂ) (by norm_num only [Complex.ofReal_re])).1.abscissaOfAbsConv_le
    exact hab.trans_lt (by exact_mod_cast hs)
  rw [he.deriv_eq, (LSeries_hasDerivAt ha).neg.deriv, neg_neg]

/-- Log-weighting preserves the finite absolute convergence abscissa of admissible
coefficients. This permits differentiation and exponential tail bounds. -/
theorem logMul_abscissa_lt_top (f : GeneralLFunction) (hf : f.IsAdmissible) :
    LSeries.abscissaOfAbsConv (LSeries.logMul f.coefficient) < ⊤ := by
  rw [LSeries.abscissaOfAbsConv_logMul]
  exact coefficient_abscissa_lt_top f hf

/-- The ordinary derivative tends to zero along the real axis for admissible functions.
The log-weighted coefficient at one vanishes, so its convergent L-series tends to zero. -/
theorem tendsto_deriv_ordinary_real_atTop (f : GeneralLFunction) (hf : f.IsAdmissible) :
    Filter.Tendsto (fun σ : ℝ ↦ deriv f.L (σ : ℂ)) Filter.atTop (nhds 0) := by
  have ht := (LSeries.tendsto_atTop (logMul_abscissa_lt_top f hf)).neg
  have ht0 :
    Filter.Tendsto (fun σ : ℝ ↦ -LSeries (LSeries.logMul f.coefficient) (σ : ℂ)) Filter.atTop
      (nhds 0) := by
    simpa only [LSeries.logMul, Nat.cast_one, Complex.log_one, zero_mul, neg_zero] using ht
  apply ht0.congr'
  filter_upwards [Filter.Ioi_mem_atTop (2 : ℝ)] with σ hσ
  exact
    (deriv_ordinary_eq_neg_logMul_series f hf
        (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).symm

/-- For admissible data, the ordinary logarithmic derivative tends to zero as real σ
tends to positive infinity. Its numerator tends to zero and the normalized ordinary
L-function tends to one, so take the quotient limit. This supplies the endpoint limit
for integrating the derivative of L'/L; no RH hypothesis is needed here. -/
theorem tendsto_logDeriv_ordinary_real_atTop (f : GeneralLFunction) (hf : f.IsAdmissible) :
    Filter.Tendsto (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ)) Filter.atTop (nhds 0) := by
  have ht :=
    (tendsto_deriv_ordinary_real_atTop f hf).div (tendsto_L_real_atTop hf)
      (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [logDeriv_apply, Pi.div_def, zero_div] using ht

/-- For admissible data, L'(σ) is O(2^(-σ)) as real σ tends to positive infinity.
The log-weighted coefficient series vanishes at indices zero and one and has finite
absolute convergence abscissa. Apply the Dirichlet-series tail bound and the local
derivative identity. This supplies an integrable exponential majorant at infinity. -/
theorem isBigO_deriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible) :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ deriv f.L (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
  have ho :=
    (AnalyticNumberTheory.General.isBigO_LSeries_of_zero_one (LSeries.logMul f.coefficient)
        (by simp only [LSeries.logMul, Nat.cast_zero, Complex.log_zero, zero_mul])
        (by simp only [LSeries.logMul, Nat.cast_one, Complex.log_one, zero_mul])
        (logMul_abscissa_lt_top f hf)).neg_left
  apply ho.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [Filter.Ioi_mem_atTop (2 : ℝ)] with σ hσ
  exact
    (deriv_ordinary_eq_neg_logMul_series f hf
        (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).symm

/-- For admissible data, L'(σ)/L(σ) is O(2^(-σ)) as real σ tends to positive infinity.
Multiply the first-derivative decay estimate by the bounded inverse L-value, which
tends to one. This bounds the tail used to prove real-axis integrability. -/
theorem isBigO_logDeriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible) :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
  have hi := ((tendsto_L_real_atTop hf).inv₀ (one_ne_zero : (1 : ℂ) ≠ 0)).isBigO_one ℂ
  simpa only [logDeriv_apply, div_eq_mul_inv, mul_one] using
    (isBigO_deriv_ordinary_real f hf).mul hi

/-- For admissible data, L''(σ) is O(2^(-σ)) as real σ tends to positive infinity.
The twice log-weighted coefficient series vanishes at zero and one and has finite
absolute convergence abscissa. Apply the series tail bound and the second-derivative
identity. This controls the first term in the derivative of L'/L. -/
theorem isBigO_deriv_deriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible) :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ deriv (deriv f.L) (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
  have ha : LSeries.abscissaOfAbsConv (LSeries.logMul (LSeries.logMul f.coefficient)) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact logMul_abscissa_lt_top f hf
  have ho :=
    AnalyticNumberTheory.General.isBigO_LSeries_of_zero_one
      (LSeries.logMul (LSeries.logMul f.coefficient))
      (by simp only [LSeries.logMul, Nat.cast_zero, Complex.log_zero, zero_mul])
      (by simp only [LSeries.logMul, Nat.cast_one, Complex.log_one, zero_mul]) ha
  apply ho.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [Filter.Ioi_mem_atTop (2 : ℝ)] with σ hσ
  exact
    (deriv_deriv_ordinary_eq_logMul_logMul_series f hf
        (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).symm

/-- For an admissible RH function right of the critical line, differentiating L'/L gives
L''/L minus its square. Analyticity and nonvanishing justify the quotient rule. -/
theorem deriv_logDeriv_ordinary_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    deriv (logDeriv f.L) s = deriv (deriv f.L) s / f.L s - logDeriv f.L s * logDeriv f.L s := by
  have hF := analyticAt_ordinary_of_re_pos f hf (lt_trans (by norm_num only) hs)
  have hn := ordinary_ne_zero_of_re_gt_half f hf hRH hs
  change deriv (deriv f.L / f.L) s = _
  rw [deriv_div hF.deriv.differentiableAt hF.differentiableAt hn, logDeriv_apply]
  field_simp [hn]

/-- For admissible data satisfying individual RH, the derivative of L'/L at real σ
is O(2^(-σ)) as σ tends to positive infinity. Use the quotient-rule identity on
the right of the critical line, the second-derivative decay estimate, and bounded
inverse L-values and L'/L. This provides the tail bound for the second endpoint integral. -/
theorem isBigO_deriv_logDeriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ deriv (logDeriv f.L) (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
  have hi := ((tendsto_L_real_atTop hf).inv₀ (one_ne_zero : (1 : ℂ) ≠ 0)).isBigO_one ℂ
  have hD := (tendsto_logDeriv_ordinary_real_atTop f hf).isBigO_one ℂ
  have ho1 :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ deriv (deriv f.L) (σ : ℂ) / f.L (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
    simpa only [div_eq_mul_inv, mul_one] using (isBigO_deriv_deriv_ordinary_real f hf).mul hi
  have ho2 :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ) * logDeriv f.L (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
    simpa only [mul_one] using (isBigO_logDeriv_ordinary_real f hf).mul hD
  apply (ho1.sub ho2).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with σ hσ
  exact
    (deriv_logDeriv_ordinary_eq f hf hRH
        (by
          simpa only [Complex.ofReal_re] using
            lt_trans (show (1 / 2 : ℝ) < 1 by norm_num only) hσ)).symm

/-- The logarithmic derivative of an admissible RH function is continuous on the closed
real ray starting at one. Restrict its analytic quotient to the real axis. -/
theorem continuousOn_logDeriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) : ContinuousOn (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ)) (Set.Ici 1) := by
  intro σ hσ
  have hs : 1 / 2 < (σ : ℂ).re := lt_of_lt_of_le (show (1 / 2 : ℝ) < 1 by norm_num only) hσ
  exact
    ((analyticAt_logDeriv_ordinary_of_re_gt_half f hf hRH hs).continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- The derivative of the logarithmic derivative is continuous on the closed real ray
for admissible RH functions. Restrict the analytic derivative to the real axis. -/
theorem continuousOn_deriv_logDeriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    ContinuousOn (fun σ : ℝ ↦ deriv (logDeriv f.L) (σ : ℂ)) (Set.Ici 1) := by
  intro σ hσ
  have hs : 1 / 2 < (σ : ℂ).re := lt_of_lt_of_le (show (1 / 2 : ℝ) < 1 by norm_num only) hσ
  exact
    ((analyticAt_logDeriv_ordinary_of_re_gt_half f hf hRH hs).deriv.continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- The ordinary logarithmic derivative is integrable over the real ray above one.
Under admissibility and RH, endpoint continuity and exponential decay prove integrability. -/
theorem integrableOn_logDeriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ)) (Set.Ioi 1) := by
  exact
    AnalyticNumberTheory.General.integrableOn_of_isBigO_two_neg_cpow
      (continuousOn_logDeriv_ordinary_real f hf hRH) (isBigO_logDeriv_ordinary_real f hf)

/-- For admissible data satisfying individual RH, the complex derivative of L'/L
restricted to the real ray σ > 1 is integrable. Combine continuity on σ ≥ 1 with
O(2^(-σ)) decay at infinity. This discharges the derivative integrability hypothesis
in the shifted-origin endpoint formula. -/
theorem integrableOn_deriv_logDeriv_ordinary_real (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ deriv (logDeriv f.L) (σ : ℂ)) (Set.Ioi 1) := by
  exact
    AnalyticNumberTheory.General.integrableOn_of_isBigO_two_neg_cpow
      (continuousOn_deriv_logDeriv_ordinary_real f hf hRH)
      (isBigO_deriv_logDeriv_ordinary_real f hf hRH)

/-- For an admissible RH function and x>1, the integrated Mellin-origin residue equals
the log L-value plus the normalized zero-mass and gamma endpoint terms.
All analyticity, nonvanishing, limit and integrability inputs follow from admissibility
and RH; no separate endpoint assumption remains. -/
theorem integral_origin_regularization_re_div_log_of_admissible (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1,
          (deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ))
              0).re) /
        Real.log x =
      Real.log ‖f.L 1‖ + (f.zeroMass / 2 - f.gammaLogDerivativeAtOne) / Real.log x := by
  rw [integral_origin_regularization_re_div_log hf hx
      (fun σ hσ ↦
        analyticAt_ordinary_of_re_pos f hf
          (by simpa only [Complex.ofReal_re] using lt_of_lt_of_le zero_lt_one hσ))
      (fun σ hσ ↦
        ordinary_ne_zero_of_re_gt_half f hf hRH
          (by
            simpa only [Complex.ofReal_re] using
              lt_of_lt_of_le (show (1 / 2 : ℝ) < 1 by norm_num only) hσ))
      (tendsto_logDeriv_ordinary_real_atTop f hf) (integrableOn_logDeriv_ordinary_real f hf hRH)
      (integrableOn_deriv_logDeriv_ordinary_real f hf hRH),
    re_logDeriv_ordinary_one_eq_half_zeroMass_sub_gamma f hf hRH]

end PseudoPrime.LLS.Extensions.GeneralLFunction
