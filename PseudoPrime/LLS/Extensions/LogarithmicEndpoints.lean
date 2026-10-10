/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicEndpoints
public import Mathlib.NumberTheory.LSeries.Injectivity
public import PseudoPrime.LLS.Extensions.PaperDefinitions

/-!
# Real-axis endpoints for admissible general L-functions.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- An admissible normalized L-function tends to one along the positive real axis.
The defining Dirichlet series converges absolutely at two and has coefficient one at one.
This supplies the L-value endpoint without an additional limit hypothesis. -/
theorem tendsto_L_real_atTop {f : GeneralLFunction} (hf : f.IsAdmissible) :
    Filter.Tendsto (fun σ : ℝ ↦ f.L (σ : ℂ)) Filter.atTop (nhds 1) := by
  have hseries := hf.2.2.2.2.2.1
  have hs := (hseries ((2 : ℝ) : ℂ) (by norm_num only [Complex.ofReal_re])).1
  have hab : LSeries.abscissaOfAbsConv f.coefficient < ⊤ :=
    hs.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have ht : Filter.Tendsto (fun σ : ℝ ↦ LSeries f.coefficient (σ : ℂ)) Filter.atTop (nhds 1) := by
    rw [← hf.2.2.1]
    exact LSeries.tendsto_atTop hab
  apply ht.congr'
  filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with σ hσ
  exact (hseries (σ : ℂ) (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).2.1.symm

/-- For admissible data and `x > 1`, assume analyticity and nonvanishing for real `σ ≥ 1`,
convergence of the logarithmic derivative to zero, and integrability of that derivative
and its complex derivative on `σ > 1`. The real integrated origin residue, divided by
`log x`, equals `log ‖L(1)‖ + Re(L'/L)(1)/log x`. The normalized Dirichlet series gives
`L(σ) → 1`; apply the logarithmic endpoint integral identity with the remaining explicit
hypotheses. This evaluates the origin term of the generalized explicit formula. -/
theorem integral_origin_regularization_re_div_log {f : GeneralLFunction} (hf : f.IsAdmissible)
    {x : ℝ} (hx : 1 < x) (hF : ∀ σ : ℝ, 1 ≤ σ → AnalyticAt ℂ f.L (σ : ℂ))
    (hne : ∀ σ : ℝ, 1 ≤ σ → f.L (σ : ℂ) ≠ 0)
    (hlimD : Filter.Tendsto (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ)) Filter.atTop (nhds 0))
    (hi : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ logDeriv f.L (σ : ℂ)) (Set.Ioi 1))
    (hiD : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ deriv (logDeriv f.L) (σ : ℂ)) (Set.Ioi 1)) :
    (∫ σ : ℝ in Set.Ioi 1,
          (deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ))
              0).re) /
        Real.log x =
      Real.log ‖f.L 1‖ + (logDeriv f.L 1).re / Real.log x := by
  exact
    AnalyticNumberTheory.General.integral_origin_regularization_re_div_log hx hF hne
      (tendsto_L_real_atTop hf) hlimD hi hiD

end PseudoPrime.LLS.Extensions.GeneralLFunction
