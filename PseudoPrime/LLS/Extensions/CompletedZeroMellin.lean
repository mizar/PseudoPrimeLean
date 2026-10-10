/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.CompletedHadamard
public import PseudoPrime.LLS.Extensions.CompletedPowerZeroMass
public import PseudoPrime.LLS.Extensions.ShiftedZeroContribution
public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventDerivative
public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventInversion

/-!
# Mellin evaluation of completed-zero resolvents

The admissible Hadamard expansion and power mass identify the zero residues and origin term.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- RH zeros stay at norm distance at least one half from every real σ ≥ 1.
Bound the reflected difference norm by its real part. This supplies the uniform pole
separation needed for differentiation of the centered zero series. -/
theorem norm_zero_sub_real_ge_half (f : GeneralLFunction) (hRH : f.RiemannHypothesis) {σ : ℝ}
    (hσ : 1 ≤ σ) (ρ : f.Zero) : (1 / 2 : ℝ) ≤ ‖(ρ : ℂ) - (σ : ℂ)‖ := by
  have h := Complex.re_le_norm ((σ : ℂ) - (ρ : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re, hRH ρ, norm_sub_rev] at h
  linarith only [h, hσ]

/-- For admissible RH data to the right of the critical line, the completed logarithmic
derivative difference equals the zero-subtype reciprocal difference series.
Restrict the Hadamard expansion to actual zeros, since other multiplicities vanish.
This aligns the expansion with the mass and residue APIs. -/
theorem logDeriv_completed_sub_eq_zeroSubtypeSeries (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv f.completed s - logDeriv f.completed t =
      ∑' ρ : f.Zero,
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) - 1 / (t - (ρ : ℂ))) := by
  rw [logDeriv_completed_sub_eq_zeroSeries f hf hRH hs ht]
  symm
  apply
    tsum_subtype_eq_of_support_subset (s := {ρ : ℂ | f.completed ρ = 0}) (f := fun ρ : ℂ ↦
      (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)))
  intro ρ hρ
  by_contra hn
  have ho : analyticOrderNatAt f.completed ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  exact hρ (by simp only [ho, Nat.cast_zero, zero_mul])

/-- For admissible RH data and σ ≥ 1, the completed logarithmic derivative's derivative
is the negative inverse-square zero series. Differentiate the locally centered resolvent
expansion using the uniform mass bound and identify derivatives by uniqueness.
This supplies the origin constant in the zero-side Mellin identity. -/
theorem deriv_logDeriv_completed_real_eq_zeroSeries (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ : ℝ} (hσ : 1 ≤ σ) :
    deriv (logDeriv f.completed) (σ : ℂ) =
      ∑' ρ : f.Zero, -(analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) / ((ρ : ℂ) - (σ : ℂ)) ^ 2 := by
  have hm :
    Summable
      (fun ρ : f.Zero ↦
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ 2) := by
    simpa only [Real.rpow_two] using
      summable_shifted_power_mass_of_admissible f hf hRH hσ (show (1 : ℝ) < 2 by norm_num only)
  have hh :=
    AnalyticNumberTheory.General.hasDerivAt_centeredResolventSum_zero
      (fun ρ : f.Zero ↦ (ρ : ℂ) - (σ : ℂ)) (fun ρ : f.Zero ↦ analyticOrderNatAt f.completed (ρ : ℂ))
      (norm_zero_sub_real_ge_half f hRH hσ) hm
  have he :
    (fun z : ℂ ↦ logDeriv f.completed ((σ : ℂ) + z) - logDeriv f.completed (σ : ℂ)) =ᶠ[nhds 0]
      (fun z : ℂ ↦
        ∑' ρ : f.Zero,
          (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
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
    rw [logDeriv_completed_sub_eq_zeroSubtypeSeries f hf hRH hs
        (by
          simpa only [Complex.ofReal_re] using
            (lt_of_lt_of_le (show (1 / 2 : ℝ) < 1 by norm_num only) hσ))]
    apply tsum_congr
    intro ρ
    have ha : (σ : ℂ) + z - (ρ : ℂ) = z - ((ρ : ℂ) - (σ : ℂ)) := by ring
    rw [ha, show (σ : ℂ) - (ρ : ℂ) = -((ρ : ℂ) - (σ : ℂ)) by ring, ]
    simp only [one_div, inv_neg, sub_neg_eq_add]
  have hd := hh.congr_of_eventuallyEq he
  have hF := (hf.2.2.2.2.2.2.2.1 : Differentiable ℂ f.completed).analyticAt (σ : ℂ)
  have hn :=
    completed_ne_zero_of_re_ne_half hRH
      (show (σ : ℂ).re ≠ 1 / 2 by
        rw [Complex.ofReal_re]; linarith only [hσ])
  have hDa : AnalyticAt ℂ (logDeriv f.completed) (σ : ℂ) := hF.deriv.div hF hn
  have hD := hDa.differentiableAt.hasDerivAt
  have hD' :
    HasDerivAt (logDeriv f.completed) (deriv (logDeriv f.completed) (σ : ℂ))
      ((fun z : ℂ ↦ (σ : ℂ) + z) 0) := by
    simpa only [add_zero] using hD
  have ht :=
    (hD'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add (σ : ℂ))).sub_const
      (logDeriv f.completed (σ : ℂ))
  simp only [Function.comp_def, mul_one] at ht
  exact ht.unique hd

/-- For admissible RH data, σ ≥ 1, τ > 0 and x > 1, the normalized zero-resolvent integral
is minus the shifted zero residue sum plus the completed logarithmic derivative's derivative.
Power-mass convergence justifies termwise Mellin evaluation; split each centered residue
into its exponential and constant parts. This completes the zero-side contour evaluation. -/
theorem normalized_integral_zeroResolvent_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          ∑' ρ : f.Zero,
            (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
              AnalyticNumberTheory.General.centeredResolventKernel ((ρ : ℂ) - (σ : ℂ)) x τ y) =
      -f.shiftedZeroSum x σ + deriv (logDeriv f.completed) (σ : ℂ) := by
  have hm := summable_zeroMassTerm_of_admissible f hf hRH
  have hi :
    Summable
      (fun ρ : f.Zero ↦
        -(analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) / ((ρ : ℂ) - (σ : ℂ)) ^ 2) := by
    have hs :=
      summable_shifted_power_mass_of_admissible f hf hRH hσ (show (1 : ℝ) < 2 by norm_num only)
    apply Summable.of_norm_bounded hs
    intro ρ
    rw [norm_div, norm_neg, Complex.norm_natCast, norm_pow, Real.rpow_two]
  have hz := summable_shiftedZeroSum f hRH hm (zero_lt_one.trans hx) hσ
  have he :=
    AnalyticNumberTheory.General.normalized_integral_tsum_centeredResolventKernel
      (fun ρ : f.Zero ↦ (ρ : ℂ) - (σ : ℂ)) (fun ρ : f.Zero ↦ analyticOrderNatAt f.completed (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.ofReal_re, hRH ρ]; linarith only [hσ])
      hτ hx
      (summable_shifted_power_mass_of_admissible f hf hRH hσ
        (show (1 : ℝ) < 3 / 2 by norm_num only))
  rw [he, deriv_logDeriv_completed_real_eq_zeroSeries f hf hRH hσ, shiftedZeroSum, ← tsum_neg, ←
    hz.neg.tsum_add hi]
  exact tsum_congr (fun ρ ↦ by ring)

end PseudoPrime.LLS.Extensions.GeneralLFunction
