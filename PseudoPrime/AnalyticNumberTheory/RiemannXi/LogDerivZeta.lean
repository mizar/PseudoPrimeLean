/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMellin
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import PseudoPrime.AnalyticNumberTheory.Gamma.ShiftedPoleMellin
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-!
# Logarithmic derivative relation between xi and zeta

At regular zeta points with real part above minus two, xi separates the pole and
shifted gamma factor. In the right half-plane, subtracting and differentiating the
relation identify centered zero resolvents and inverse-square origin terms.
These identities provide the corrections in shifted Mellin contours without RH.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- For Re s > -2, the shifted half argument of the xi gamma factor has positive
real part. This excludes gamma poles and ensures nonvanishing. -/
private theorem gammaArgument_re_pos {s : ℂ} (hs : -2 < s.re) : 0 < (s / 2 + 1).re := by
  rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
  linarith only [hs]

/-- For Re s > -2 and s distinct from one, xi locally equals (s-1) times its pi power,
shifted gamma and zeta factors. Rewrite regularized zeta away from its pole.
The neighborhood equality permits differentiation of the factorization. -/
private theorem eventuallyEq_riemannXi_pole_gamma_zeta {s : ℂ} (hs : -2 < s.re) (hne : s ≠ 1) :
    riemannXi =ᶠ[nhds s]
      (fun z : ℂ ↦
        (z - 1) * ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)) * riemannZeta z) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
    isOpen_ne.mem_nhds hne] with z hz hn
  have he :=
    riemannXi_eq_gamma_mul_riemannZeta₁ hn
      (Complex.Gamma_ne_zero_of_re_pos (gammaArgument_re_pos hz))
  have hζ : riemannZeta₁ z = (z - 1) * riemannZeta z :=
    ((eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.mpr hn)).mp (riemannZeta_eq_inv_sub_mul hn)).symm
  rw [he, hζ]
  ring

/-- The pi power in the xi completion has constant logarithmic derivative
-log(pi)/2. Differentiate its affine exponent and cancel the nonzero complex power. -/
private theorem logDeriv_pi_cpow_neg_half (s : ℂ) :
    logDeriv (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) s = -Complex.log (Real.pi : ℂ) / 2 := by
  have hE : HasDerivAt (fun z : ℂ ↦ -z / 2) (-1 / 2 : ℂ) s := by
    have h1 : HasDerivAt (fun z : ℂ ↦ -z) (-1 : ℂ) s := (hasDerivAt_id s).neg
    simpa only [one_div, id_eq] using h1.div_const 2
  have hP := hE.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hn : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [logDeriv_apply, hP.deriv, mul_assoc, mul_div_cancel_left₀ _ hn]
  ring

/-- For Re s > -2, the xi gamma factor's logarithmic derivative is half its digamma
value. The affine chain rule and gamma nonvanishing give the quotient. -/
private theorem logDeriv_gamma_half_add_one {s : ℂ} (hs : -2 < s.re) :
    logDeriv (fun z : ℂ ↦ Complex.Gamma (z / 2 + 1)) s = Complex.digamma (s / 2 + 1) / 2 := by
  have hp : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hr
    linarith only [hr, hs, Nat.cast_nonneg (α := ℝ) m]
  have hn := Complex.Gamma_ne_zero_of_re_pos (gammaArgument_re_pos hs)
  rw [logDeriv_apply, (hasDerivAt_Gamma_affine_half hp).deriv, mul_assoc, mul_div_cancel_left₀ _ hn]
  ring

/-- For Re s > -2, s distinct from one, and nonzero zeta value, the xi logarithmic
derivative is the sum of the pole term, pi constant, shifted half-digamma and zeta
logarithmic derivative. Differentiate the local product; each factor is nonzero.
This separates the principal-character contour at regular horizontal and vertical
points, including those to the left of the critical line. -/
theorem logDeriv_eq_pole_gamma_zeta_of_regular {s : ℂ} (hs : -2 < s.re) (hn : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / (s - 1) - Complex.log (Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2 +
        logDeriv riemannZeta s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP : DifferentiableAt ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hpi)
  have hG : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.Gamma (z / 2 + 1)) s :=
    (analyticAt_Gamma_of_re_pos (gammaArgument_re_pos hs)).differentiableAt.comp s
      ((differentiableAt_id.div_const (2 : ℂ)).add_const 1)
  have hPne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hGne := Complex.Gamma_ne_zero_of_re_pos (gammaArgument_re_pos hs)
  have hS : HasDerivAt (fun z : ℂ ↦ z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have he := (logDeriv_congr_nhds (eventuallyEq_riemannXi_pole_gamma_zeta hs hn)).eq_of_nhds
  rw [he,
    logDeriv_fun_mul (f := fun z : ℂ ↦
      (z - 1) * ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1))) (g := riemannZeta) s
      (mul_ne_zero (sub_ne_zero.mpr hn) (mul_ne_zero hPne hGne)) hz
      (hS.differentiableAt.mul (hP.mul hG)) (differentiableAt_riemannZeta hn),
    logDeriv_fun_mul (f := fun z : ℂ ↦ z - 1) (g := fun z : ℂ ↦
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)) s (sub_ne_zero.mpr hn)
      (mul_ne_zero hPne hGne) hS.differentiableAt (hP.mul hG),
    logDeriv_fun_mul (f := fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) (g := fun z : ℂ ↦
      Complex.Gamma (z / 2 + 1)) s hPne hGne hP hG,
    logDeriv_pi_cpow_neg_half, logDeriv_gamma_half_add_one hs]
  rw [logDeriv_apply, hS.deriv]
  ring

/-- To the right of one, the xi logarithmic derivative separates the zeta pole,
pi constant, shifted digamma and zeta logarithmic derivative. The regular-point
formula applies because zeta is nonzero in this half-plane. This retains the
right-half-plane interface used in centered Mellin inversion. -/
theorem logDeriv_eq_pole_gamma_zeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / (s - 1) - Complex.log (Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2 +
        logDeriv riemannZeta s := by
  have hn : s ≠ 1 := fun he => by
    rw [he, Complex.one_re] at hs
    exact lt_irrefl _ hs
  exact
    logDeriv_eq_pole_gamma_zeta_of_regular (by linarith only [hs]) hn
      (riemannZeta_ne_zero_of_one_lt_re hs)

/-- For two points with real parts greater than one, the zeta logarithmic derivative
difference equals the xi difference minus the pole and shifted digamma differences.
Subtract the two completion identities; the pi constant cancels.
This is the decomposition used to evaluate the centered zeta Mellin contour. -/
theorem logDeriv_zeta_sub_eq_xi_sub_pole_sub_gamma {s t : ℂ} (hs : 1 < s.re) (ht : 1 < t.re) :
    logDeriv riemannZeta s - logDeriv riemannZeta t =
      (logDeriv riemannXi s - logDeriv riemannXi t) - (1 / (s - 1) - 1 / (t - 1)) -
        (Complex.digamma (s / 2 + 1) - Complex.digamma (t / 2 + 1)) / 2 := by
  have hS := logDeriv_eq_pole_gamma_zeta_of_one_lt_re hs
  have hT := logDeriv_eq_pole_gamma_zeta_of_one_lt_re ht
  linear_combination -hS + hT

/-- For Re s > 1 and Re t > 1, half the xi digamma difference equals the negative
reciprocal difference series at the shifted gamma poles. Use the digamma series
and remove the half-argument scaling. -/
private theorem digamma_half_sub_eq_poleSeries {s t : ℂ} (hs : 1 < s.re) (ht : 1 < t.re) :
    (Complex.digamma (s / 2 + 1) - Complex.digamma (t / 2 + 1)) / 2 =
      -(∑' n : ℕ, (1 / (s + 2 + 2 * (n : ℂ)) - 1 / (t + 2 + 2 * (n : ℂ)))) := by
  rw [Gamma.digamma_sub_eq_resolventSeries (gammaArgument_re_pos (by linarith only [hs]))
      (gammaArgument_re_pos (by linarith only [ht])),
    ← tsum_div_const, ← tsum_neg]
  apply tsum_congr
  intro n
  rw [sub_div, show s / 2 + 1 = (s + 2) / 2 by ring, show t / 2 + 1 = (t + 2) / 2 by ring,
    Gamma.halfArgument_resolvent_eq (zero_lt_one.trans hs)
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat]),
    Gamma.halfArgument_resolvent_eq (zero_lt_one.trans ht)
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat])]
  ring

/-- For sigma > 1, the centered shifted half-digamma function has derivative equal
to the inverse-square gamma-pole sum. Locally identify its reciprocal series with
the centered gamma resolvents and use their summable derivative. -/
private theorem hasDerivAt_digamma_half_centered_zero {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt
      (fun z : ℂ ↦
        (Complex.digamma (((σ : ℂ) + z) / 2 + 1) - Complex.digamma ((σ : ℂ) / 2 + 1)) / 2)
      (∑' n : ℕ, 1 / ((σ : ℂ) + 2 + 2 * (n : ℂ)) ^ 2) 0 := by
  have hd :=
    Gamma.hasDerivAt_gammaPole_centeredSum_zero
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat]) hσ.le
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds
      (show (0 : ℂ) ∈ Metric.ball 0 ((σ - 1) / 2) by
        rw [Metric.mem_ball, dist_self]; linarith only [hσ])] with
    z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hr := Complex.re_le_norm (-z)
  rw [Complex.neg_re, norm_neg] at hr
  have hs : 1 < ((σ : ℂ) + z).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    linarith only [hr, hz, hσ]
  rw [digamma_half_sub_eq_poleSeries hs (by simpa only [Complex.ofReal_re] using hσ)]
  congr 1
  apply tsum_congr
  intro n
  rw [sub_neg_eq_add]
  simp only [one_div, inv_neg]
  rw [show z + ((σ : ℂ) + 2 + 2 * (n : ℂ)) = (σ : ℂ) + z + 2 + 2 * (n : ℂ) by ring]
  ring

/-- For real sigma > 1, the derivative of zeta's logarithmic derivative equals the
xi derivative plus the inverse-square pole term minus the inverse-square gamma-pole
sum. Differentiate the local completion difference, whose three terms are analytic
and whose gamma series has a summable derivative. No RH assumption is needed.
This collects the origin terms in centered Mellin inversion. -/
theorem deriv_logDeriv_zeta_eq_xi_pole_gamma {σ : ℝ} (hσ : 1 < σ) :
    deriv (logDeriv riemannZeta) (σ : ℂ) =
      deriv (logDeriv riemannXi) (σ : ℂ) + 1 / ((σ : ℂ) - 1) ^ 2 -
        ∑' n : ℕ, 1 / ((σ : ℂ) + 2 + 2 * (n : ℂ)) ^ 2 := by
  have hs : 1 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  have hn : (σ : ℂ) ≠ 1 := fun he ↦ by
    rw [he, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hX := differentiable_riemannXi.analyticAt (σ : ℂ)
  have hDX : AnalyticAt ℂ (logDeriv riemannXi) (σ : ℂ) :=
    hX.deriv.div hX (riemannXi_ne_zero_of_one_lt_re hs)
  have hζ := analyticOn_riemannZeta (σ : ℂ) hn
  have hDζ : AnalyticAt ℂ (logDeriv riemannZeta) (σ : ℂ) :=
    hζ.deriv.div hζ (riemannZeta_ne_zero_of_one_lt_re hs)
  have ha : HasDerivAt (fun z : ℂ ↦ (σ : ℂ) + z) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add (σ : ℂ)
  have hdx' :
    HasDerivAt (logDeriv riemannXi) (deriv (logDeriv riemannXi) (σ : ℂ))
      ((fun z : ℂ ↦ (σ : ℂ) + z) 0) := by
    simpa only [add_zero] using hDX.differentiableAt.hasDerivAt
  have hdz' :
    HasDerivAt (logDeriv riemannZeta) (deriv (logDeriv riemannZeta) (σ : ℂ))
      ((fun z : ℂ ↦ (σ : ℂ) + z) 0) := by
    simpa only [add_zero] using hDζ.differentiableAt.hasDerivAt
  have hdx := (hdx'.comp 0 ha).sub_const (logDeriv riemannXi (σ : ℂ))
  have hdz := (hdz'.comp 0 ha).sub_const (logDeriv riemannZeta (σ : ℂ))
  simp only [Function.comp_def, mul_one] at hdx hdz
  have hb : HasDerivAt (fun z : ℂ ↦ (σ : ℂ) + z - 1) 1 0 := ha.sub_const 1
  have hp :=
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).div hb
          (show (σ : ℂ) + 0 - 1 ≠ 0 by
            rw [add_zero]; exact sub_ne_zero.mpr hn)).sub_const
      (1 / ((σ : ℂ) - 1))
  simp only [add_zero, zero_mul, one_mul, zero_sub] at hp
  have hd := (hdx.sub hp).sub (hasDerivAt_digamma_half_centered_zero hσ)
  have he :
    (fun z : ℂ ↦ logDeriv riemannZeta ((σ : ℂ) + z) - logDeriv riemannZeta (σ : ℂ)) =ᶠ[nhds 0]
      (fun z : ℂ ↦
        (logDeriv riemannXi ((σ : ℂ) + z) - logDeriv riemannXi (σ : ℂ)) -
          (1 / ((σ : ℂ) + z - 1) - 1 / ((σ : ℂ) - 1)) -
          (Complex.digamma (((σ : ℂ) + z) / 2 + 1) - Complex.digamma ((σ : ℂ) / 2 + 1)) / 2) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
        (show (0 : ℂ) ∈ Metric.ball 0 ((σ - 1) / 2) by
          rw [Metric.mem_ball, dist_self]; linarith only [hσ])] with
      z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hr := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg] at hr
    apply logDeriv_zeta_sub_eq_xi_sub_pole_sub_gamma
    · rw [Complex.add_re, Complex.ofReal_re]
      linarith only [hr, hz, hσ]
    · exact hs
  have hc := hdz.unique (hd.congr_of_eventuallyEq he)
  rw [hc]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannXi
