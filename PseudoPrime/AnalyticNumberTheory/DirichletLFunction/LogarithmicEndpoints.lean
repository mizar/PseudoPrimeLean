/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicEndpoints
public import PseudoPrime.AnalyticNumberTheory.General.LSeriesDecay
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Endpoint integration of Dirichlet logarithmic derivatives.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The coefficients χ(n)Λ(n) of the negative logarithmic derivative. They vanish at zero
and one and supply convergent L-series and decay estimates on the right half-plane. -/
noncomputable def twistedMangoldtCoefficient {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- For a Dirichlet character of nonzero modulus, χ(n)Λ(n) has absolute convergence
abscissa at most one. Apply convergence in every half-plane Re s>1. -/
theorem abscissa_twistedMangoldtCoefficient_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv (twistedMangoldtCoefficient χ) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  intro σ hσ
  have hσ' : 1 < ((σ : ℝ) : ℂ).re := by
    simpa only [← EReal.coe_one, EReal.coe_lt_coe_iff, Complex.ofReal_re] using hσ
  exact χ.LSeriesSummable_twist_vonMangoldt hσ'

/-- For Re s>1, the logarithmic derivative of L(s,χ) is the negative L-series with
coefficients χ(n)Λ(n). This supplies its real-axis decay and derivative formula. -/
theorem logDeriv_eq_neg_LSeries_twistedMangoldt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv χ.LFunction s = -LSeries (twistedMangoldtCoefficient χ) s := by
  have he := lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hs
  rw [neg_div, ← logDeriv_apply] at he
  change LSeries (twistedMangoldtCoefficient χ) s = -logDeriv χ.LFunction s at he
  have hn : -LSeries (twistedMangoldtCoefficient χ) s = -(-logDeriv χ.LFunction s) :=
    congrArg Neg.neg he
  rw [neg_neg] at hn
  exact hn.symm

/-- For Re s>1, the derivative of the logarithmic derivative is the L-series with
coefficients log(n)χ(n)Λ(n). Differentiate the locally equal absolutely convergent series. -/
theorem deriv_logDeriv_eq_LSeries_logMul_twistedMangoldt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (logDeriv χ.LFunction) s = LSeries (LSeries.logMul (twistedMangoldtCoefficient χ)) s := by
  have hlocal :
    Filter.EventuallyEq (nhds s) (logDeriv χ.LFunction)
      (fun z ↦ -LSeries (twistedMangoldtCoefficient χ) z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact logDeriv_eq_neg_LSeries_twistedMangoldt χ hz
  have hab : LSeries.abscissaOfAbsConv (twistedMangoldtCoefficient χ) < s.re :=
    (abscissa_twistedMangoldtCoefficient_le_one χ).trans_lt (by exact_mod_cast hs)
  rw [hlocal.deriv_eq]
  have hd := (LSeries_hasDerivAt hab).neg.deriv
  change
    deriv (fun z ↦ -LSeries (twistedMangoldtCoefficient χ) z) s =
      -(-LSeries (LSeries.logMul (twistedMangoldtCoefficient χ)) s) at hd
  rwa [neg_neg] at hd

/-- The twisted Mangoldt coefficient at zero vanishes, as required by the decay theorem. -/
theorem twistedMangoldtCoefficient_zero {N : ℕ} (χ : DirichletCharacter ℂ N) :
    twistedMangoldtCoefficient χ 0 = 0 := by
  rw [twistedMangoldtCoefficient, ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero]

/-- The twisted Mangoldt coefficient at one vanishes because Λ(1)=0. Thus the logarithmic
derivative has no constant Dirichlet-series term. -/
theorem twistedMangoldtCoefficient_one {N : ℕ} (χ : DirichletCharacter ℂ N) :
    twistedMangoldtCoefficient χ 1 = 0 := by
  rw [twistedMangoldtCoefficient, ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero,
    mul_zero]

/-- For nonzero modulus, L(σ,χ) tends to one as real σ tends to infinity. Use absolute
convergence and the coefficient χ(1)=1, with no primitivity or RH assumption. -/
theorem tendsto_LFunction_real_atTop {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Filter.Tendsto (fun σ : ℝ ↦ χ.LFunction (σ : ℂ)) Filter.atTop (nhds 1) := by
  have hs :=
    χ.LSeriesSummable_of_one_lt_re (s := ((2 : ℝ) : ℂ)) (by norm_num only [Complex.ofReal_re])
  have hab : LSeries.abscissaOfAbsConv (fun n : ℕ ↦ χ (n : ZMod N)) < ⊤ :=
    hs.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have ht := LSeries.tendsto_atTop hab
  have heq :
    Filter.EventuallyEq Filter.atTop (fun σ : ℝ ↦ LSeries (fun n : ℕ ↦ χ (n : ZMod N)) (σ : ℂ))
      (fun σ : ℝ ↦ χ.LFunction (σ : ℂ)) := by
    filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with σ hσ
    exact
      (dirichletLFunction_eq_LSeries_of_one_lt_re χ
          (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).symm
  have ht1 :
    Filter.Tendsto (fun σ : ℝ ↦ LSeries (fun n : ℕ ↦ χ (n : ZMod N)) (σ : ℂ)) Filter.atTop
      (nhds 1) := by
    simpa only [Nat.cast_one, map_one] using ht
  exact ht1.congr' heq

/-- The logarithmic derivative tends to zero along the positive real axis. Its convergent
Dirichlet series has zero coefficient at one, giving the endpoint for half-line integration. -/
theorem tendsto_logDeriv_LFunction_real_atTop {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Filter.Tendsto (fun σ : ℝ ↦ logDeriv χ.LFunction (σ : ℂ)) Filter.atTop (nhds 0) := by
  have hab : LSeries.abscissaOfAbsConv (twistedMangoldtCoefficient χ) < ⊤ :=
    (abscissa_twistedMangoldtCoefficient_le_one χ).trans_lt
      (by simpa only [EReal.coe_one] using EReal.coe_lt_top (1 : ℝ))
  have ht := (LSeries.tendsto_atTop hab).neg
  have ht0 :
    Filter.Tendsto (fun σ : ℝ ↦ -LSeries (twistedMangoldtCoefficient χ) (σ : ℂ)) Filter.atTop
      (nhds 0) := by
    simpa only [twistedMangoldtCoefficient_one, neg_zero] using ht
  apply ht0.congr'
  filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with σ hσ
  exact
    (logDeriv_eq_neg_LSeries_twistedMangoldt χ
        (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).symm

/-- For a nonprincipal character, the logarithmic derivative is analytic at Re s≥1.
Use the entire L-function and its nonvanishing on this closed half-plane. -/
theorem analyticAt_logDeriv_LFunction_of_one_le_re {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logDeriv χ.LFunction) s := by
  have hF := (χ.differentiable_LFunction hχ).analyticAt s
  exact hF.deriv.div hF (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs)

/-- For a nonprincipal character, the logarithmic derivative is continuous on the real ray
σ≥1. Restrict the complex analytic quotient to the real axis for local integrability. -/
theorem continuousOn_logDeriv_LFunction_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : ContinuousOn (fun σ : ℝ ↦ logDeriv χ.LFunction (σ : ℂ)) (Set.Ici 1) := by
  intro σ hσ
  have hs : 1 ≤ (σ : ℂ).re := by simpa only [Complex.ofReal_re, Set.mem_Ici] using hσ
  exact
    ((analyticAt_logDeriv_LFunction_of_one_le_re hχ hs).continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- For a nonprincipal character, the derivative of the logarithmic derivative is continuous
on σ≥1. Analyticity gives the continuity needed for half-line integrability. -/
theorem continuousOn_deriv_logDeriv_LFunction_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : ContinuousOn (fun σ : ℝ ↦ deriv (logDeriv χ.LFunction) (σ : ℂ)) (Set.Ici 1) := by
  intro σ hσ
  have hs : 1 ≤ (σ : ℂ).re := by simpa only [Complex.ofReal_re, Set.mem_Ici] using hσ
  exact
    ((analyticAt_logDeriv_LFunction_of_one_le_re hχ hs).deriv.continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- For a nonprincipal character, the logarithmic derivative is integrable over σ>1.
Combine continuity at the endpoint with exponential decay of its Dirichlet series. -/
theorem integrableOn_logDeriv_LFunction_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ logDeriv χ.LFunction (σ : ℂ)) (Set.Ioi 1) := by
  have hab : LSeries.abscissaOfAbsConv (twistedMangoldtCoefficient χ) < ⊤ :=
    (abscissa_twistedMangoldtCoefficient_le_one χ).trans_lt
      (by simpa only [EReal.coe_one] using EReal.coe_lt_top (1 : ℝ))
  have heq :
    Filter.EventuallyEq Filter.atTop (fun σ : ℝ ↦ LSeries (twistedMangoldtCoefficient χ) (σ : ℂ))
      (fun σ : ℝ ↦ -logDeriv χ.LFunction (σ : ℂ)) := by
    filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with σ hσ
    rw [logDeriv_eq_neg_LSeries_twistedMangoldt χ
        (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ),
      neg_neg]
  have hi :=
    General.integrableOn_of_eventuallyEq_LSeries_zero_one (twistedMangoldtCoefficient χ)
      (twistedMangoldtCoefficient_zero χ) (twistedMangoldtCoefficient_one χ) hab
      (continuousOn_logDeriv_LFunction_real hχ).neg heq
  simpa only [neg_neg] using hi.neg

/-- For a nonprincipal character, the derivative of the logarithmic derivative is integrable
over σ>1. The log-weighted coefficient series has finite convergence abscissa and decays
exponentially; endpoint continuity supplies local integrability. -/
theorem integrableOn_deriv_logDeriv_LFunction_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ deriv (logDeriv χ.LFunction) (σ : ℂ)) (Set.Ioi 1) := by
  have ha0 : LSeries.logMul (twistedMangoldtCoefficient χ) 0 = 0 := by
    rw [LSeries.logMul, twistedMangoldtCoefficient_zero, mul_zero]
  have ha1 : LSeries.logMul (twistedMangoldtCoefficient χ) 1 = 0 := by
    rw [LSeries.logMul, twistedMangoldtCoefficient_one, mul_zero]
  have hab : LSeries.abscissaOfAbsConv (LSeries.logMul (twistedMangoldtCoefficient χ)) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact
      (abscissa_twistedMangoldtCoefficient_le_one χ).trans_lt
        (by simpa only [EReal.coe_one] using EReal.coe_lt_top (1 : ℝ))
  apply
    General.integrableOn_of_eventuallyEq_LSeries_zero_one _ ha0 ha1 hab
      (continuousOn_deriv_logDeriv_LFunction_real hχ)
  filter_upwards [Filter.Ioi_mem_atTop (1 : ℝ)] with σ hσ
  exact
    (deriv_logDeriv_eq_LSeries_logMul_twistedMangoldt χ
        (by simpa only [Complex.ofReal_re, Set.mem_Ioi] using hσ)).symm

/-- For a nonprincipal character and x>1, the integrated real origin residue divided by
log x equals log|L(1,χ)| plus Re(L'/L)(1,χ)/log x. Prove the required limits and
integrability from Dirichlet series and apply the general endpoint identity. This identifies
the L-value term in the shifted explicit formula without an RH assumption. -/
theorem integral_origin_regularization_LFunction_re_div_log {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {x : ℝ} (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1,
          (deriv (General.shiftedLogarithmicRegularization χ.LFunction x (σ : ℂ)) 0).re) /
        Real.log x =
      Real.log ‖χ.LFunction 1‖ + (logDeriv χ.LFunction 1).re / Real.log x := by
  apply
    General.integral_origin_regularization_re_div_log hx
      (fun σ _ ↦ (χ.differentiable_LFunction hχ).analyticAt (σ : ℂ))
      (fun σ hσ ↦
        χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa only [Complex.ofReal_re] using hσ))
      (tendsto_LFunction_real_atTop χ) (tendsto_logDeriv_LFunction_real_atTop χ)
      (integrableOn_logDeriv_LFunction_real hχ) (integrableOn_deriv_logDeriv_LFunction_real hχ)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
