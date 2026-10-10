/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntirePowerZeroMass
public import PseudoPrime.LLS.Extensions.CompletedZeroMass

/-!
# Power-weighted completed-zero mass

Admissible order-one growth gives every weight exponent strictly greater than one.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Admissibility and individual RH imply summability of regularized zero weights
for every exponent p > 1. Choose growth exponent (1+p)/2 and apply the dyadic Jensen bound.
For 1 < p < 2 this is stronger than inverse-square convergence and provides
the power-weighted majorants used in vertical integral estimates. -/
theorem summable_regularPowerZeroWeight_of_admissible (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {p : ℝ} (hp : 1 < p) :
    Summable (AnalyticNumberTheory.General.regularPowerZeroWeight f.completed p) := by
  have hF : Differentiable ℂ f.completed := hf.2.2.2.2.2.2.2.1
  have h0 : f.completed 0 ≠ 0 :=
    completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.zero_re])
  obtain ⟨C, hC, hg⟩ :=
    AnalyticNumberTheory.General.exists_global_exponential_bound_of_orderAtMostOne hF.continuous
      hf.2.2.2.2.2.2.2.2.1 (show (1 : ℝ) < (1 + p) / 2 by linarith only [hp])
  exact
    AnalyticNumberTheory.General.summable_regularPowerZeroWeight hF h0 hC (by linarith only [hp])
      (zero_lt_one.trans hp) (by linarith only [hp]) hg

/-- For admissible RH data, σ ≥ 1 and p > 1, the zero multiplicities divided by
norm(ρ-σ)^p form a summable series. Critical-line zeros stay at distance at least one half;
compare the shifted denominator to the regularized zero weights.
This provides the p=3/2 majorant needed to interchange zero sums and vertical integrals. -/
theorem summable_shifted_power_mass_of_admissible (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ : ℝ} (hσ : 1 ≤ σ) {p : ℝ} (hp : 1 < p) :
    Summable
      (fun ρ : f.Zero ↦
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ p) := by
  have hs :=
    (summable_regularPowerZeroWeight_of_admissible f hf hRH hp).subtype {z : ℂ | f.completed z = 0}
  change
    Summable
      (fun ρ : f.Zero ↦
        AnalyticNumberTheory.General.regularPowerZeroWeight f.completed p (ρ : ℂ)) at hs
  have hδ : ∀ ρ : f.Zero, (1 / 2 : ℝ) ≤ ‖(ρ : ℂ) - (σ : ℂ)‖ := by
    intro ρ
    have hh := Complex.re_le_norm ((σ : ℂ) - (ρ : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re, hRH ρ, norm_sub_rev] at hh
    linarith only [hh, hσ]
  have hc : ∀ ρ : f.Zero, 1 + ‖(ρ : ℂ)‖ ≤ (3 + 2 * σ) * ‖(ρ : ℂ) - (σ : ℂ)‖ := by
    intro ρ
    have ht := norm_add_le ((ρ : ℂ) - (σ : ℂ)) (σ : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hσ)] at ht
    have hm := mul_le_mul_of_nonneg_left (hδ ρ) (by linarith only [hσ] : 0 ≤ 2 * (1 + σ))
    nlinarith only [ht, hm]
  have hcp : ∀ ρ : f.Zero, (1 + ‖(ρ : ℂ)‖) ^ p ≤ (3 + 2 * σ) ^ p * ‖(ρ : ℂ) - (σ : ℂ)‖ ^ p := by
    intro ρ
    have h :=
      Real.rpow_le_rpow (by linarith only [norm_nonneg (ρ : ℂ)]) (hc ρ) (zero_lt_one.trans hp).le
    rwa [Real.mul_rpow (by linarith only [hσ]) (norm_nonneg _)] at h
  apply
    Summable.of_nonneg_of_le
      (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)) (fun ρ ↦ ?_)
      (hs.mul_left ((3 + 2 * σ) ^ p))
  change
    (analyticOrderNatAt f.completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ p ≤
      (3 + 2 * σ) ^ p * ((analyticOrderNatAt f.completed (ρ : ℂ) : ℝ) / (1 + ‖(ρ : ℂ)‖) ^ p)
  have hd := Real.rpow_pos_of_pos (by linarith only [hδ ρ]) p
  have he := Real.rpow_pos_of_pos (show 0 < 1 + ‖(ρ : ℂ)‖ by linarith only [norm_nonneg (ρ : ℂ)]) p
  rw [← mul_div_assoc, div_le_div_iff₀ hd he]
  convert
    mul_le_mul_of_nonneg_left (hcp ρ)
      (Nat.cast_nonneg (analyticOrderNatAt f.completed (ρ : ℂ)) : (0 : ℝ) ≤ _) using
    1
  ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
