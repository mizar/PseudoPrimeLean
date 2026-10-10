/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.CompletedHadamard
public import PseudoPrime.LLS.Extensions.ShiftedGammaContribution
public import PseudoPrime.AnalyticNumberTheory.Gamma.ShiftedPoleMellin

/-!
# Mellin evaluation of gamma-pole resolvents

The digamma series identifies both the shifted residues and the origin derivative.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible data and Re s > 0 and Re t > 0, the completion factor's logarithmic
derivative difference equals the finite sum over gamma shifts of the convergent series
`1/(t+κ_j+2n) - 1/(s+κ_j+2n)`. Rewrite the digamma resolvent formula at half arguments.
This gives the gamma pole expansion used in the centered Mellin integrand. -/
theorem logDeriv_completionFactor_sub_eq_gammaPoleSeries (f : GeneralLFunction)
    (hf : f.IsAdmissible) {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    logDeriv f.completionFactor s - logDeriv f.completionFactor t =
      ∑ j : Fin f.degree,
        ∑' n : ℕ, (1 / (t + f.shift j + 2 * (n : ℂ)) - 1 / (s + f.shift j + 2 * (n : ℂ))) := by
  rw [logDeriv_completionFactor_sub_eq_resolventSeries f hf hs ht, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  rw [sub_div, AnalyticNumberTheory.Gamma.halfArgument_resolvent_eq ht (hf.2.2.2.1 j),
    AnalyticNumberTheory.Gamma.halfArgument_resolvent_eq hs (hf.2.2.2.1 j)]

/-- For admissible data and real σ ≥ 1, the derivative of the completion factor's
logarithmic derivative equals the finite sum over gamma shifts of
`sum_n 1/(σ+κ_j+2n)²`. Differentiate the local centered pole expansion and translate
back from its center to σ. This evaluates the gamma part of the Mellin origin term. -/
theorem deriv_logDeriv_completionFactor_real_eq_gammaPoleSeries (f : GeneralLFunction)
    (hf : f.IsAdmissible) {σ : ℝ} (hσ : 1 ≤ σ) :
    deriv (logDeriv f.completionFactor) (σ : ℂ) =
      ∑ j : Fin f.degree, ∑' n : ℕ, 1 / ((σ : ℂ) + f.shift j + 2 * (n : ℂ)) ^ 2 := by
  have hsum :=
    HasDerivAt.sum (u := Finset.univ)
      (fun j _ ↦ AnalyticNumberTheory.Gamma.hasDerivAt_gammaPole_centeredSum_zero (hf.2.2.2.1 j) hσ)
  have he :
    (fun z : ℂ ↦
        logDeriv f.completionFactor ((σ : ℂ) + z) - logDeriv f.completionFactor (σ : ℂ)) =ᶠ[nhds 0]
      (fun z : ℂ ↦
        ∑ j : Fin f.degree,
          -(∑' n : ℕ,
              (1 / (z - (-((σ : ℂ) + f.shift j + 2 * (n : ℂ)))) +
                1 / (-((σ : ℂ) + f.shift j + 2 * (n : ℂ)))))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
        (show (0 : ℂ) ∈ Metric.ball 0 (1 / 4) by
          rw [Metric.mem_ball, dist_self]; norm_num only)] with
      z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hr := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg] at hr
    have hs : 0 < ((σ : ℂ) + z).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith only [hr, hz, hσ]
    rw [logDeriv_completionFactor_sub_eq_gammaPoleSeries f hf hs
        (by
          rw [Complex.ofReal_re]; linarith only [hσ])]
    apply Finset.sum_congr rfl
    intro j _
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    have ha : (σ : ℂ) + z + f.shift j + 2 * (n : ℂ) = z + ((σ : ℂ) + f.shift j + 2 * (n : ℂ)) := by
      ring
    rw [ha]
    simp only [sub_neg_eq_add, one_div, inv_neg]
    ring
  have hsum' :
    HasDerivAt
      (fun z : ℂ ↦
        ∑ j : Fin f.degree,
          -(∑' n : ℕ,
              (1 / (z - (-((σ : ℂ) + f.shift j + 2 * (n : ℂ)))) +
                1 / (-((σ : ℂ) + f.shift j + 2 * (n : ℂ))))))
      (∑ j : Fin f.degree, ∑' n : ℕ, 1 / ((σ : ℂ) + f.shift j + 2 * (n : ℂ)) ^ 2) 0 := by
    convert hsum using 1
    funext z
    rw [Finset.sum_apply]
  have hh := (hsum'.congr_of_eventuallyEq he).add_const (logDeriv f.completionFactor (σ : ℂ))
  have ht :
    HasDerivAt (fun z : ℂ ↦ logDeriv f.completionFactor ((σ : ℂ) + z))
      (∑ j : Fin f.degree, ∑' n : ℕ, 1 / ((σ : ℂ) + f.shift j + 2 * (n : ℂ)) ^ 2) 0 := by
    convert hh using 1
    funext z
    ring
  have ht' :
    HasDerivAt (fun z : ℂ ↦ logDeriv f.completionFactor ((σ : ℂ) + z))
      (∑ j : Fin f.degree, ∑' n : ℕ, 1 / ((σ : ℂ) + f.shift j + 2 * (n : ℂ)) ^ 2)
      ((fun w : ℂ ↦ w - (σ : ℂ)) (σ : ℂ)) := by
    simpa only [sub_self] using ht
  have hd :=
    ht'.comp (h := fun w : ℂ ↦ w - (σ : ℂ)) (σ : ℂ) ((hasDerivAt_id (σ : ℂ)).sub_const (σ : ℂ))
  have heq :
    (fun z : ℂ ↦ logDeriv f.completionFactor ((σ : ℂ) + z)) ∘ (fun w : ℂ ↦ w - (σ : ℂ)) =
      logDeriv f.completionFactor := by
    funext w
    dsimp only [Function.comp_def]
    congr 1
    ring
  rw [heq, mul_one] at hd
  exact hd.deriv

/-- For admissible data, real σ ≥ 1, τ > 0, and x > 1, the finite sum of normalized
gamma-pole resolvent integrals equals shiftedGammaSum minus the derivative of
the completion factor's logarithmic derivative at σ. Sum the individual Mellin
evaluations and substitute the inverse-square derivative series.
This identifies both the gamma residues and their centered origin correction. -/
theorem sum_normalized_integral_gammaPoleResolvent_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 1 < x) :
    (∑ j : Fin f.degree,
        (2 * Real.pi)⁻¹ •
          (∫ y : ℝ,
            ∑' n : ℕ,
              AnalyticNumberTheory.General.centeredResolventKernel
                (-((σ : ℂ) + f.shift j + 2 * (n : ℂ))) x τ y)) =
      f.shiftedGammaSum x σ - deriv (logDeriv f.completionFactor) (σ : ℂ) := by
  simp only [AnalyticNumberTheory.Gamma.normalized_integral_gammaPoleResolvent_eq (hf.2.2.2.1 _) hσ
        hτ hx]
  rw [Finset.sum_sub_distrib, shiftedGammaSum, AnalyticNumberTheory.General.gammaShiftFamilySum,
    deriv_logDeriv_completionFactor_real_eq_gammaPoleSeries f hf hσ]

end PseudoPrime.LLS.Extensions.GeneralLFunction
