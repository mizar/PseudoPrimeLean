/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ExponentialPoleIntegral
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogarithmicEndpoints
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ShiftedMellin

/-!
# Evaluation of the combined zeta main integral

A real antiderivative combines the zeta pole and logarithmic-derivative terms.
Its singularities cancel at one, and its two endpoint limits give the main term
`log x (log log x + γ - 1) + γ`. RH is used for integrability of the combined
kernel; its derivative and endpoint calculations hold without RH.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The zeta function is real on the real axis. Its conjugation symmetry forces
its imaginary part to vanish, allowing real logarithms in the combined main integral. -/
theorem riemannZeta_real_eq_ofReal_re (σ : ℝ) :
    riemannZeta (σ : ℂ) = ((riemannZeta (σ : ℂ)).re : ℂ) := by
  have h := congrArg Complex.im (riemannZeta_conj (σ : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  apply Complex.ext
  · exact (Complex.ofReal_re _).symm
  · exact (eq_zero_of_neg_eq h.symm).trans (Complex.ofReal_im _).symm

/-- For sigma > 1, the norm of zeta(sigma) equals its positive real part.
Use reality and positivity to differentiate its real logarithm without a complex branch. -/
theorem norm_riemannZeta_real {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ = (riemannZeta (σ : ℂ)).re := by
  conv_lhs => rw [riemannZeta_real_eq_ofReal_re σ]
  rw [Complex.norm_real, Real.norm_of_nonneg (riemannZeta_re_pos_of_one_lt hσ).le]

/-- For sigma > 1, the real logarithm of zeta has derivative Re(zeta'/zeta).
The logarithmic norm derivative and positivity identify the derivative used at the endpoints. -/
theorem hasDerivAt_log_riemannZeta_re {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (fun t : ℝ ↦ Real.log (riemannZeta (t : ℂ)).re) (logDeriv riemannZeta (σ : ℂ)).re
      σ := by
  have hs : 1 < (σ : ℂ).re := hσ
  have hn : (σ : ℂ) ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hd :=
    General.hasDerivAt_log_norm_of_complex (differentiableAt_riemannZeta hn).hasDerivAt
      (riemannZeta_ne_zero_of_one_lt_re hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hσ] with t ht
  rw [norm_riemannZeta_real ht]

/-- For a real parameter a and sigma, combine the exponential pole primitive
with -a log zeta(sigma) and -Re(zeta'/zeta)(sigma). For a = log x and x,sigma > 1,
its derivative is the real zeta main kernel and its singular terms cancel at sigma = 1. -/
noncomputable def zetaMainPrimitive (a σ : ℝ) : ℝ :=
  General.exponentialPolePrimitive a (σ - 1) - a * Real.log (riemannZeta (σ : ℂ)).re -
    (logDeriv riemannZeta (σ : ℂ)).re

/-- For x > 1, the real part of the combined zeta main kernel is its real
exponential pole term minus the two real logarithmic derivative terms. Convert real complex
powers to exponentials; this connects the Mellin kernel to its real antiderivative. -/
theorem shiftedZetaMainKernel_re_eq {x σ : ℝ} (hx : 1 < x) :
    (shiftedZetaMainKernel x σ).re =
      Real.exp (-Real.log x * (σ - 1)) / (σ - 1) ^ 2 -
        Real.log x * (logDeriv riemannZeta (σ : ℂ)).re -
        (deriv (logDeriv riemannZeta) (σ : ℂ)).re := by
  rw [shiftedZetaMainKernel, ← Complex.ofReal_one, ← Complex.ofReal_sub, ←
    Complex.ofReal_cpow (le_of_lt (zero_lt_one.trans hx)), ← Complex.ofReal_sub, ←
    Complex.ofReal_pow, ← Complex.ofReal_div]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  congr 2
  · rw [show Real.log x * (1 - σ) = -Real.log x * (σ - 1) by ring]
  · ring

/-- For x,sigma > 1, the combined primitive with a = log x has derivative equal
to the real zeta main kernel. Differentiate the pole primitive and the two analytic zeta terms. -/
theorem hasDerivAt_zetaMainPrimitive {x σ : ℝ} (hx : 1 < x) (hσ : 1 < σ) :
    HasDerivAt (zetaMainPrimitive (Real.log x)) (shiftedZetaMainKernel x σ).re σ := by
  have ha := Real.log_pos hx
  have hs : 1 < (σ : ℂ).re := hσ
  have hn : (σ : ℂ) ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hζ := analyticOn_riemannZeta (σ : ℂ) hn
  have hD := hζ.deriv.div hζ (riemannZeta_ne_zero_of_one_lt_re hs)
  have hd :=
    ((General.hasDerivAt_exponentialPolePrimitive ha (sub_pos.mpr hσ)).comp σ
          ((hasDerivAt_id σ).sub_const 1)).sub
      ((hasDerivAt_log_riemannZeta_re hσ).const_mul (Real.log x))
  have hd' := hd.sub hD.differentiableAt.hasDerivAt.real_of_complex
  simp only [mul_one] at hd'
  rw [shiftedZetaMainKernel_re_eq hx]
  exact hd'

/-- As sigma tends to one from above, log zeta(sigma)+log(sigma-1) tends to zero.
Use the regularized zeta asymptotics; this cancels the logarithm in the exponential pole
primitive. -/
theorem tendsto_log_zeta_add_log_sub_one :
    Filter.Tendsto (fun σ : ℝ ↦ Real.log (riemannZeta (σ : ℂ)).re + Real.log (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  exact (Asymptotics.isLittleO_one_iff ℝ).mp log_riemannZeta_add_log_sub_isLittleO_ofReal

/-- As sigma tends to one from above, Re(zeta'/zeta)(sigma)+1/(sigma-1) tends
to gamma. Restrict the complex Laurent asymptotic to the real axis and take real parts. -/
theorem tendsto_logDeriv_zeta_add_inv_sub_one :
    Filter.Tendsto (fun σ : ℝ ↦ (logDeriv riemannZeta (σ : ℂ)).re + (σ - 1)⁻¹)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds Real.eulerMascheroniConstant) := by
  have hc :
    Filter.Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      rw [Set.mem_compl_singleton_iff, ← Complex.ofReal_one, ne_eq, Complex.ofReal_inj]
      exact ne_of_gt hσ
  have h :=
    ((Asymptotics.isLittleO_one_iff ℂ).mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO).comp hc
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  change
    Filter.Tendsto
      (fun σ : ℝ ↦
        (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹ -
            (Real.eulerMascheroniConstant : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) at hr
  simp only [Complex.sub_re, Complex.add_re, ← logDeriv_apply, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re] at hr
  have hf := hr.add_const Real.eulerMascheroniConstant
  simpa only [sub_add_cancel, zero_add] using hf

/-- For a > 0, the right limit of the combined zeta primitive at one is
a-a log a-gamma. Subtract the regularized zeta logarithm and logarithmic derivative from the
regularized exponential primitive; their pole and logarithmic singularities cancel exactly. -/
theorem tendsto_zetaMainPrimitive_one {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (zetaMainPrimitive a) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (a - a * Real.log a - Real.eulerMascheroniConstant)) := by
  have hs :
    Filter.Tendsto (fun σ : ℝ ↦ σ - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hid : Filter.Tendsto (fun σ : ℝ ↦ σ) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
        Filter.tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hid.sub_const (1 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_pos.mpr (show 1 < σ from hσ)
  have hP := (General.tendsto_exponentialPolePrimitive_regularized_zero ha).comp hs
  have h :=
    (hP.sub (tendsto_log_zeta_add_log_sub_one.const_mul a)).sub
      tendsto_logDeriv_zeta_add_inv_sub_one
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards with σ
  dsimp only [Function.comp_apply, zetaMainPrimitive]
  rw [one_div]
  ring

/-- For a > 0, the combined zeta primitive tends to a times the Euler--Mascheroni
constant at infinity.
Zeta tends to one and its logarithmic derivative to zero by their Dirichlet series, leaving
the Euler constant endpoint of the exponential primitive. -/
theorem tendsto_zetaMainPrimitive_atTop (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (zetaMainPrimitive a) Filter.atTop
      (nhds (a * Real.eulerMascheroniConstant)) := by
  change
    Filter.Tendsto
      (fun σ : ℝ ↦
        General.exponentialPolePrimitive a (σ - 1) - a * Real.log (riemannZeta (σ : ℂ)).re -
          (logDeriv riemannZeta (σ : ℂ)).re)
      Filter.atTop (nhds (a * Real.eulerMascheroniConstant))
  have hζ := DirichletLFunction.tendsto_LFunction_real_atTop (1 : DirichletCharacter ℂ 1)
  rw [DirichletCharacter.LFunction_modOne_eq] at hζ
  have hlog :=
    (Real.continuousAt_log (show (1 : ℝ) ≠ 0 from one_ne_zero)).tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp hζ)
  change
    Filter.Tendsto (fun σ : ℝ ↦ Real.log (riemannZeta (σ : ℂ)).re) Filter.atTop
      (nhds (Real.log (1 : ℂ).re)) at hlog
  simp only [Complex.one_re, Real.log_one] at hlog
  have hD := DirichletLFunction.tendsto_logDeriv_LFunction_real_atTop (1 : DirichletCharacter ℂ 1)
  rw [DirichletCharacter.LFunction_modOne_eq] at hD
  have hDr := Complex.continuous_re.continuousAt.tendsto.comp hD
  have hP :=
    (General.tendsto_exponentialPolePrimitive_atTop ha).comp
      (show Filter.Tendsto (fun σ : ℝ ↦ σ - 1) Filter.atTop Filter.atTop from by
        simpa only [id_eq, sub_eq_add_neg] using
          Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id)
  have h := (hP.sub (hlog.const_mul a)).sub hDr
  simpa only [Function.comp_apply, Complex.zero_re, mul_zero, sub_zero] using h

/-- Under RH and x > 1, the real combined zeta main integral equals
log x (log log x+gamma-1)+gamma. Its established integrability permits FTC with the two
finite endpoint limits, proving the main term of LLS Lemma 2.6. -/
theorem integral_shiftedZetaMainKernel_re (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1, (shiftedZetaMainKernel x σ).re) =
      Real.log x * (Real.log (Real.log x) + Real.eulerMascheroniConstant - 1) +
        Real.eulerMascheroniConstant := by
  have hi := Complex.reCLM.integrable_comp (integrableOn_shiftedZetaMainKernel hRH hx)
  change MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (shiftedZetaMainKernel x σ).re) (Set.Ioi 1) at hi
  have hint :
    MeasureTheory.IntegrableOn
      ((fun σ : ℝ ↦ (shiftedZetaMainKernel x σ).re) * (fun _ ↦ (1 : ℝ)) +
        zetaMainPrimitive (Real.log x) * (fun _ ↦ (0 : ℝ)))
      (Set.Ioi 1) := by
    simpa only [Pi.mul_def, Pi.add_def, mul_one, mul_zero, add_zero] using hi
  have hlo :
    Filter.Tendsto (zetaMainPrimitive (Real.log x) * (fun _ : ℝ ↦ (1 : ℝ)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.log x - Real.log x * Real.log (Real.log x) - Real.eulerMascheroniConstant)) := by
    simpa only [Pi.mul_def, mul_one] using tendsto_zetaMainPrimitive_one (Real.log_pos hx)
  have hhi :
    Filter.Tendsto (zetaMainPrimitive (Real.log x) * (fun _ : ℝ ↦ (1 : ℝ))) Filter.atTop
      (nhds (Real.log x * Real.eulerMascheroniConstant)) := by
    simpa only [Pi.mul_def, mul_one] using
      tendsto_zetaMainPrimitive_atTop (Real.log x) (Real.log_pos hx)
  have h :=
    MeasureTheory.integral_Ioi_deriv_mul_eq_sub (fun σ hσ ↦ hasDerivAt_zetaMainPrimitive hx hσ)
      (fun σ _ ↦ hasDerivAt_const σ (1 : ℝ)) hint hlo hhi
  simp only [mul_one, mul_zero, add_zero] at h
  rw [h]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
