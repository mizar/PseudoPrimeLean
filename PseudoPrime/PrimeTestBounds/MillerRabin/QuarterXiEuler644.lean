/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterXiPoisson644
import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivGammaFactor

/-! # The untwisted Euler contribution to the section 122 xi identity -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For analytic functions on the shifted real half-line, the section 122
operator splits over addition by the two real derivative sum identities. -/
theorem quarter_xi_operator_add (f g : ℂ → ℂ)
    (hf : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ f (((1 / 2 : ℝ) + u : ℝ) : ℂ))
    (hg : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ g (((1 / 2 : ℝ) + u : ℝ) : ℂ)) :
    quarterXiOperator (f + g) = quarterXiOperator f + quarterXiOperator g := by
  have hd := real_shift_sum_derivs f g (a := 107 / 100) (by norm_num only) hf hg
  dsimp only at hd
  unfold quarterXiOperator
  simp only [Pi.add_apply, Complex.add_re, hd.1, hd.2]
  ring

private theorem xi_operator_complex (f : ℂ → ℂ)
    (hf : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ f (((1 / 2 : ℝ) + u : ℝ) : ℂ)) :
    quarterXiOperator f =
      3 * (f (157 / 100)).re - (321 / 100 : ℝ) * (deriv f (157 / 100)).re +
        (11449 / 10000 : ℝ) * (deriv (deriv f) (157 / 100)).re := by
  have ha : (1 / 2 : ℝ) < 107 / 100 := by norm_num only
  have hc : (((1 / 2 : ℝ) + 107 / 100 : ℝ) : ℂ) = (157 / 100 : ℂ) := by
    norm_num only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hd := (hf _ ha).differentiableAt.hasDerivAt.real_of_complex
  have h₁ := (hd.comp (107 / 100 : ℝ) ((hasDerivAt_id _).const_add (1 / 2 : ℝ))).deriv
  have h₂ := real_shift_derivs f ha hf
  unfold quarterXiOperator
  dsimp only
  rw [show
      deriv (fun u : ℝ ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) (107 / 100) =
        (deriv f (157 / 100 : ℂ)).re
      by simpa only [mul_one, Function.comp_def, hc] using h₁,
    h₂, hc]

/-- Right of one, the zeta logarithmic derivative is analytic at each
real shift used in the section 122 operator, since zeta is nonvanishing there. -/
theorem quarter_zeta_log_analytic (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv riemannZeta) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
  have h : 1 < (((1 / 2 : ℝ) + u : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith only [hu]
  have hn : (((1 / 2 : ℝ) + u : ℝ) : ℂ) ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at h
    exact lt_irrefl _ h
  have hz := analyticOn_riemannZeta _ hn
  exact hz.deriv.div hz (riemannZeta_ne_zero_of_one_lt_re h)

/-- The section 122 operator on the zeta logarithmic derivative equals
minus eight times the universal Euler sum. The level-one character is one
at every index, so the signed character factor disappears. -/
theorem quarter_xi_euler_644 :
    quarterXiOperator (logDeriv riemannZeta) =
      -8 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n := by
  rw [xi_operator_complex _ quarter_zeta_log_analytic]
  simpa only [DirichletCharacter.LFunction_modOne_eq, MulChar.one_apply (isUnit_of_subsingleton _),
    Complex.one_re, one_mul] using quarter_euler_operator_644 (1 : DirichletCharacter ℂ 1)

private theorem xi_operator_congr {f g : ℂ → ℂ}
    (h : ∀ u : ℝ, 1 / 2 < u → f (((1 / 2 : ℝ) + u : ℝ) : ℂ) = g (((1 / 2 : ℝ) + u : ℝ) : ℂ)) :
    quarterXiOperator f = quarterXiOperator g := by
  let F : ℝ → ℝ := fun u ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  let G : ℝ → ℝ := fun u ↦ (g (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  have he {u : ℝ} (hu : 1 / 2 < u) : F =ᶠ[nhds u] G := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact congrArg Complex.re (h v hv)
  have ha : (1 / 2 : ℝ) < 107 / 100 := by norm_num only
  have hd : deriv F =ᶠ[nhds (107 / 100 : ℝ)] deriv G := by
    filter_upwards [Ioi_mem_nhds ha] with v hv
    exact (he hv).deriv_eq
  change
    3 * F (107 / 100) - _ * deriv F (107 / 100) + _ * deriv (deriv F) (107 / 100) =
      3 * G (107 / 100) - _ * deriv G (107 / 100) + _ * deriv (deriv G) (107 / 100)
  rw [(he ha).eq_of_nhds, (he ha).deriv_eq, hd.deriv_eq]

private theorem xi_pole_analytic (d : ℂ) (hd : -1 ≤ d.re) (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (fun s : ℂ ↦ (s + d)⁻¹) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
  have hz (h : -1 ≤ d.re) : (((1 / 2 : ℝ) + u : ℝ) : ℂ) + d ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [hr, h, hu]
  exact (analyticAt_id.add analyticAt_const).inv (hz hd)

private theorem xi_pole_operator (d : ℂ) (hd : -1 ≤ d.re) :
    quarterXiOperator (fun s : ℂ ↦ (s + d)⁻¹) =
      3 * (((157 / 100 : ℂ) + d)⁻¹).re - (321 / 100 : ℝ) * (-(((157 / 100 : ℂ) + d) ^ 2)⁻¹).re +
        (11449 / 10000 : ℝ) * (2 * ((157 / 100 : ℂ) + d) ^ (-3 : ℤ)).re := by
  rw [xi_operator_complex _ (xi_pole_analytic d hd)]
  have he : (deriv fun s : ℂ ↦ (s + d)⁻¹) = fun s ↦ -((s + d) ^ (-2 : ℤ)) := by
    funext s
    rw [deriv_comp_add_const, deriv_inv]
    norm_num only [zpow_neg, zpow_ofNat]
  rw [he]
  have hD := deriv_comp_add_const (fun s : ℂ ↦ -(s ^ (-2 : ℤ))) d (157 / 100)
  rw [hD,
    show (fun s : ℂ ↦ -(s ^ (-2 : ℤ))) = fun s ↦ (-1 : ℂ) * s ^ (-2 : ℤ) by
      funext s; rw [neg_one_mul],
    deriv_const_mul_field, deriv_zpow]
  norm_num only [zpow_neg, zpow_ofNat, Int.cast_neg, Int.cast_ofNat, Int.reduceSub, neg_mul,
    neg_neg, neg_one_mul, one_mul]

private theorem xi_poles_644 :
    quarterXiOperator (fun s : ℂ ↦ s⁻¹) + quarterXiOperator (fun s : ℂ ↦ (s + (-1))⁻¹) =
      16 * (107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3 := by
  have h₀ := xi_pole_operator 0 (by norm_num only [Complex.zero_re])
  have h₁ := xi_pole_operator (-1) (by norm_num only [Complex.neg_re, Complex.one_re])
  simp only [add_zero] at h₀
  rw [h₀, h₁]
  norm_num only [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div,
    ← Complex.ofReal_add, ← Complex.ofReal_neg, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_zpow, ← Complex.ofReal_mul, Complex.ofReal_re]
  norm_num only [Complex.div_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply, zero_mul, zero_pow, add_zero]

private theorem xi_gamma_analytic (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor)
      (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
  have h : 0 < (((1 / 2 : ℝ) + u : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith only [hu]
  have ha :=
    AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos
      (1 : DirichletCharacter ℂ 1) h
  exact ha.deriv.div ha (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos _ h)

/-- The even Gamma term in the section 122 operator equals the xi mass
correction, minus the two pole contributions, plus the universal Euler mass.
This is the single-character cancellation in the three-character mass identity. -/
theorem quarter_xi_gamma_644 (hRH : RiemannHypothesis) :
    quarterXiOperator (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor) / 8 -
        (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) =
      (∑' ρ, ‖quarterKernel644.zetaKernelZeroTerm ρ‖) -
        2 * (107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3 := by
  let P : ℂ → ℂ := fun s ↦ s⁻¹
  let Q : ℂ → ℂ := fun s ↦ (s + (-1))⁻¹
  let G := logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor
  let Z := logDeriv riemannZeta
  have hp : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ P (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    simpa only [P, add_zero] using xi_pole_analytic 0 (by norm_num only [Complex.zero_re])
  have hq := xi_pole_analytic (-1) (by norm_num only [Complex.neg_re, Complex.one_re])
  have he :
    quarterXiOperator (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi) =
      quarterXiOperator (P + Q + G + Z) := by
    apply xi_operator_congr
    intro u hu
    have hr : 1 < (((1 / 2 : ℝ) + u : ℝ) : ℂ).re := by
      rw [Complex.ofReal_re]
      linarith only [hu]
    simpa only [P, Q, G, Z, Pi.add_apply, sub_eq_add_neg, one_div] using
      AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hr
  rw [quarter_xi_operator_add _ _
      (fun u hu ↦ ((hp u hu).add (hq u hu)).add (xi_gamma_analytic u hu)) quarter_zeta_log_analytic,
    quarter_xi_operator_add _ _ (fun u hu ↦ (hp u hu).add (hq u hu)) xi_gamma_analytic,
    quarter_xi_operator_add _ _ hp hq] at he
  have hz := quarter_xi_poisson_644 hRH
  have hEuler := quarter_xi_euler_644
  change quarterXiOperator Z = _ at hEuler
  have hPole := xi_poles_644
  change quarterXiOperator P + quarterXiOperator Q = _ at hPole
  change quarterXiOperator G / 8 - _ = _
  linarith only [he, hz, hPole, hEuler]

end PseudoPrime.PrimeTestBounds.MillerRabin
