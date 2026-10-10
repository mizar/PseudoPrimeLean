/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CenteredHadamard
public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventDerivative
public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventInversion

/-!
# Mellin evaluation of the xi zero resolvents

The centered Hadamard series and its derivative identify the residue and origin terms.
Under RH, critical-line separation and summable power mass permit termwise
Mellin inversion and differentiation. The integrated zero sum has normalized
norm at most `2 B/(sqrt x (log x)²)` for `x > 1`, with `B` the Riemann zero mass.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Under RH and with both real parts above one half, the xi logarithmic derivative
difference is the zero-subtype reciprocal difference series. Restrict Hadamard's
all-point sum to zeros, because the analytic order vanishes elsewhere.
This uses the same indices as the shifted mass and Mellin estimates. -/
theorem logDeriv_sub_eq_zeroSubtypeSeries_of_riemannHypothesis (hRH : RiemannHypothesis) {s t : ℂ}
    (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv riemannXi s - logDeriv riemannXi t =
      ∑' ρ : Zero,
        (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) - 1 / (t - (ρ : ℂ))) := by
  rw [logDeriv_sub_eq_zeroSeries_of_riemannHypothesis hRH hs ht]
  symm
  apply
    tsum_subtype_eq_of_support_subset (s := {ρ : ℂ | riemannXi ρ = 0}) (f := fun ρ : ℂ ↦
      (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)))
  intro ρ hρ
  by_contra hn
  have ho : analyticOrderNatAt riemannXi ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  exact hρ (by simp only [ho, Nat.cast_zero, zero_mul])

/-- Under RH and sigma >= 1, the derivative of the xi logarithmic derivative is
the negative inverse-square shifted zero series. Differentiate the locally centered
Hadamard expansion using uniform pole separation and the summable square mass,
then identify the derivative by uniqueness. This is the Mellin origin term. -/
theorem deriv_logDeriv_real_eq_zeroSeries_of_riemannHypothesis (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 ≤ σ) :
    deriv (logDeriv riemannXi) (σ : ℂ) =
      ∑' ρ : Zero, -(analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) / ((ρ : ℂ) - (σ : ℂ)) ^ 2 := by
  have hm :
    Summable
      (fun ρ : Zero ↦ (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ 2) := by
    simpa only [Real.rpow_two, riemannXiZeroMultiplicity] using
      summable_shifted_power_mass_of_riemannHypothesis hRH hσ (show (1 : ℝ) < 2 by norm_num only)
  have hh :=
    General.hasDerivAt_centeredResolventSum_zero (fun ρ : Zero ↦ (ρ : ℂ) - (σ : ℂ))
      (fun ρ : Zero ↦ analyticOrderNatAt riemannXi (ρ : ℂ))
      (norm_zero_sub_real_ge_half_of_riemannHypothesis hRH hσ) hm
  have he :
    (fun z : ℂ ↦ logDeriv riemannXi ((σ : ℂ) + z) - logDeriv riemannXi (σ : ℂ)) =ᶠ[nhds 0]
      (fun z : ℂ ↦
        ∑' ρ : Zero,
          (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) *
            (1 / (z - ((ρ : ℂ) - (σ : ℂ))) + 1 / ((ρ : ℂ) - (σ : ℂ)))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
        (show (0 : ℂ) ∈ Metric.ball 0 (1 / 4) by
          rw [Metric.mem_ball, dist_self]; norm_num only)] with
      z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hr := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg] at hr
    have hs : 1 / 2 < ((σ : ℂ) + z).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith only [hr, hz, hσ]
    rw [logDeriv_sub_eq_zeroSubtypeSeries_of_riemannHypothesis hRH hs
        (by
          simpa only [Complex.ofReal_re] using
            (lt_of_lt_of_le (show (1 / 2 : ℝ) < 1 by norm_num only) hσ))]
    apply tsum_congr
    intro ρ
    have ha : (σ : ℂ) + z - (ρ : ℂ) = z - ((ρ : ℂ) - (σ : ℂ)) := by ring
    rw [ha, show (σ : ℂ) - (ρ : ℂ) = -((ρ : ℂ) - (σ : ℂ)) by ring]
    simp only [one_div, inv_neg, sub_neg_eq_add]
  have hd := hh.congr_of_eventuallyEq he
  have hF := differentiable_riemannXi.analyticAt (σ : ℂ)
  have hn : riemannXi (σ : ℂ) ≠ 0 := fun hz ↦
    (show (σ : ℂ).re ≠ 1 / 2 by
        rw [Complex.ofReal_re]; linarith only [hσ])
      (riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hz)
  have hDa : AnalyticAt ℂ (logDeriv riemannXi) (σ : ℂ) := hF.deriv.div hF hn
  have hD := hDa.differentiableAt.hasDerivAt
  have hD' :
    HasDerivAt (logDeriv riemannXi) (deriv (logDeriv riemannXi) (σ : ℂ))
      ((fun z : ℂ ↦ (σ : ℂ) + z) 0) := by
    simpa only [add_zero] using hD
  have ht :=
    (hD'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add (σ : ℂ))).sub_const (logDeriv riemannXi (σ : ℂ))
  simp only [Function.comp_def, mul_one] at ht
  exact ht.unique hd

/-- Under RH, sigma >= 1, tau > 0 and x > 1, the normalized vertical integral of
the centered xi zero resolvents equals the shifted residue sum, with a plus sign, and
the derivative of the xi logarithmic derivative. The three-halves mass justifies
termwise Mellin inversion; square mass splits the exponential and constant terms.
This evaluates the nontrivial-zero part of the shifted zeta formula. -/
theorem normalized_integral_zeroResolvent_eq_of_riemannHypothesis (hRH : RiemannHypothesis)
    {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          ∑' ρ : Zero,
            (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) *
              General.centeredResolventKernel ((ρ : ℂ) - (σ : ℂ)) x τ y) =
      (∑' ρ : Zero,
          (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2) +
        deriv (logDeriv riemannXi) (σ : ℂ) := by
  have hm :=
    summable_shifted_power_mass_of_riemannHypothesis hRH hσ (show (1 : ℝ) < 2 by norm_num only)
  have hi :
    Summable
      (fun ρ : Zero ↦ -(analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) / ((ρ : ℂ) - (σ : ℂ)) ^ 2) := by
    apply Summable.of_norm_bounded hm
    intro ρ
    rw [norm_div, norm_neg, Complex.norm_natCast, norm_pow, Real.rpow_two]
    rfl
  have hz :
    Summable
      (fun ρ : Zero ↦
        (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
          ((ρ : ℂ) - (σ : ℂ)) ^ 2) := by
    apply Summable.of_norm_bounded (hm.mul_left (x ^ (1 / 2 - σ)))
    intro ρ
    rw [norm_div, norm_mul, Complex.norm_natCast, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx), Complex.sub_re, Complex.ofReal_re,
      riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property, Real.rpow_two]
    unfold riemannXiZeroMultiplicity
    exact le_of_eq (by ring)
  have he :=
    General.normalized_integral_tsum_centeredResolventKernel (fun ρ : Zero ↦ (ρ : ℂ) - (σ : ℂ))
      (fun ρ : Zero ↦ analyticOrderNatAt riemannXi (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.ofReal_re,
          riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property]
        linarith only [hσ])
      hτ hx
      (by
        simpa only [riemannXiZeroMultiplicity] using
          (summable_shifted_power_mass_of_riemannHypothesis hRH hσ
            (show (1 : ℝ) < 3 / 2 by norm_num only)))
  rw [he, deriv_logDeriv_real_eq_zeroSeries_of_riemannHypothesis hRH hσ, ← hz.tsum_add hi]
  exact tsum_congr (fun ρ ↦ by ring)

/-- Under RH, sigma >= 1 and tau > 0, the xi zero kernel sum equals the centered
logarithmic derivative times x^z/z^2 on the vertical line. Rewrite the Hadamard
resolvents in shifted coordinates. This identifies the evaluated contour integrand. -/
theorem zeroResolventKernel_eq_logDeriv_difference (hRH : RiemannHypothesis) {σ τ x : ℝ}
    (hσ : 1 ≤ σ) (hτ : 0 < τ) (y : ℝ) :
    (∑' ρ : Zero,
        (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) *
          General.centeredResolventKernel ((ρ : ℂ) - (σ : ℂ)) x τ y) =
      (logDeriv riemannXi ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) - logDeriv riemannXi (σ : ℂ)) *
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  rw [General.tsum_centeredResolventKernel_eq_difference (fun ρ : Zero ↦ (ρ : ℂ) - (σ : ℂ))
      (fun ρ : Zero ↦ analyticOrderNatAt riemannXi (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.ofReal_re,
          riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property]
        linarith only [hσ])
      hτ]
  have hs : 1 / 2 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith only [hσ, hτ]
  rw [logDeriv_sub_eq_zeroSubtypeSeries_of_riemannHypothesis hRH hs
      (by
        simpa only [Complex.ofReal_re] using
          (lt_of_lt_of_le (show (1 / 2 : ℝ) < 1 by norm_num only) hσ))]
  congr 2
  apply tsum_congr
  intro ρ
  rw [show
      (σ : ℂ) + ((τ : ℂ) + y * Complex.I) - (ρ : ℂ) = (τ : ℂ) + y * Complex.I - ((ρ : ℂ) - (σ : ℂ))
      by ring,
    show (σ : ℂ) - (ρ : ℂ) = -((ρ : ℂ) - (σ : ℂ)) by ring]
  simp only [one_div, inv_neg, sub_neg_eq_add]

/-- Under RH, sigma >= 1, tau > 0 and x > 1, the centered xi logarithmic derivative's
normalized Mellin integral equals its shifted zero residues plus its derivative at sigma.
Replace the integrand by the summable zero kernels and apply termwise inversion.
This connects the zero calculation directly to the logarithmic derivative contour. -/
theorem normalized_integral_logDeriv_difference_eq (hRH : RiemannHypothesis) {σ τ x : ℝ}
    (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          (logDeriv riemannXi ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) - logDeriv riemannXi (σ : ℂ)) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2) =
      (∑' ρ : Zero,
          (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2) +
        deriv (logDeriv riemannXi) (σ : ℂ) := by
  simp_rw [← zeroResolventKernel_eq_logDeriv_difference hRH hσ hτ]
  exact normalized_integral_zeroResolvent_eq_of_riemannHypothesis hRH hσ hτ hx

/-- Under RH, the inverse-square xi mass on the zero subtype equals twice the
Riemann zero mass. Restrict the known all-point identity to actual zeros and
identify the complex norm square. This fixes the constant in integrated zero errors. -/
theorem tsum_inverse_square_mass_eq_two_mul_riemannZeroMass (hRH : RiemannHypothesis) :
    (∑' ρ : Zero, (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) =
      2 * riemannZeroMass := by
  have he :
    (∑' ρ : Zero, (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) =
      (∑' ρ : ℂ,
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) := by
    have ht :=
      tsum_subtype_eq_of_support_subset (s := {ρ : ℂ | riemannXi ρ = 0}) (f := fun ρ : ℂ ↦
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)
        (by
          intro ρ hρ
          by_contra hn
          change riemannXi ρ ≠ 0 at hn
          exact hρ (by simp only [ite_eq_right hn]))
    rw [← ht]
    apply tsum_congr
    intro ρ
    change _ = if riemannXi (ρ : ℂ) = 0 then _ else 0
    rw [ite_eq_left ρ.property, Complex.normSq_eq_norm_sq]
  rw [he,
    tsum_riemannXiZeroMultiplicity_invNormSq_eq_two_mul_riemannZeroMass_of_riemannHypothesis hRH]

/-- Under RH and x > 1, the integral over sigma > 1 of the shifted xi
zero residues has norm at most 2 B x^(-1/2)/log x, where B is the Riemann zero mass.
Apply the general critical-line majorant and substitute the exact inverse-square
mass. A further division by log x gives the zero-error scale in Lemma 2.6. -/
theorem norm_integral_shifted_zero_sum_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖∫ σ : ℝ in Set.Ioi 1,
          ∑' ρ : Zero,
            (riemannXiZeroMultiplicity (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
              ((ρ : ℂ) - (σ : ℂ)) ^ 2‖ ≤
      x ^ (-(1 / 2 : ℝ)) / Real.log x * (2 * riemannZeroMass) := by
  have h :=
    General.norm_integral_shifted_zero_residues_le (fun ρ : Zero ↦ (ρ : ℂ))
      (fun ρ : Zero ↦ riemannXiZeroMultiplicity (ρ : ℂ))
      (fun ρ ↦ riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property) hx
      (summable_inverse_square_mass_of_riemannHypothesis hRH)
  simp only [neg_mul, neg_div, tsum_neg, MeasureTheory.integral_neg, norm_neg] at h
  rwa [tsum_inverse_square_mass_eq_two_mul_riemannZeroMass hRH] at h

/-- Under RH and x > 1, the shifted xi zero residue sum is integrable
over sigma > 1. Negate the general critical-line residue sum and use its summable
inverse-square majorant. This permits separating the zero error in the integrated
shifted zeta formula. -/
theorem integrableOn_shifted_zero_sum (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦
        ∑' ρ : Zero,
          (riemannXiZeroMultiplicity (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2)
      (Set.Ioi 1) := by
  have h :=
    General.integrableOn_shifted_zero_sum (fun ρ : Zero ↦ (ρ : ℂ))
      (fun ρ : Zero ↦ riemannXiZeroMultiplicity (ρ : ℂ))
      (fun ρ ↦ riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property) hx
      (summable_inverse_square_mass_of_riemannHypothesis hRH)
  simpa only [neg_mul, neg_div, tsum_neg, Pi.neg_def, neg_neg] using h.neg

/-- Under RH and x > 1, the shifted xi zero integral divided by log x has norm
at most 2 B/(sqrt x (log x)^2), where B is the Riemann zero mass. Divide the
integrated majorant by the positive logarithm and rewrite the half power as a square
root. This is the exact nontrivial-zero error scale in Lemma 2.6. -/
theorem norm_integrated_shifted_zero_sum_div_log_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖(∫ σ : ℝ in Set.Ioi 1,
            ∑' ρ : Zero,
              (riemannXiZeroMultiplicity (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
                ((ρ : ℂ) - (σ : ℂ)) ^ 2) /
          (Real.log x : ℂ)‖ ≤
      2 * riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos hx)]
  have h :=
    div_le_div_of_nonneg_right (norm_integral_shifted_zero_sum_le hRH hx) (Real.log_pos hx).le
  apply h.trans_eq
  rw [Real.rpow_neg (zero_lt_one.trans hx).le, ← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannXi
