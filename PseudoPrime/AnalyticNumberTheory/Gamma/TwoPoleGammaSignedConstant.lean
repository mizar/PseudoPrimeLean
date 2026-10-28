/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleGammaZeroMass
public import PseudoPrime.AnalyticNumberTheory.Gamma.SignedGammaIntervalBounds

/-! # Signed Gamma-factor corrections for the two-pole zero-mass bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For positive real sigma at most 9/4, the real logarithmic derivative of
GammaReal is at most -3/4. Move digamma to 9/8, retain eight positive reciprocal
differences up to the existing 7/5 node, and use the certified lower log-pi bound. -/
theorem re_logDeriv_GammaReal_le_neg_three_fourths {σ : ℝ} (hσ : 0 < σ) (hu : σ ≤ 9 / 4) :
    (logDeriv Complex.Gammaℝ (σ : ℂ)).re ≤ -(3 / 4 : ℝ) := by
  have hm :=
    re_digamma_mono_of_pos (div_pos hσ (by norm_num only : (0 : ℝ) < 2))
      (show σ / 2 ≤ (9 / 8 : ℝ) by linarith only [hu])
  have hp :=
    real_digamma_difference_ge_prefix (a := (9 / 8 : ℝ)) (r := 7 / 5) (by norm_num only)
      (by norm_num only) 8
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat] at hp
  have hd := gamma_digamma_node_4_bounds.2
  have hpi := gamma_log_pi_bounds.1
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hd hpi
  rw [re_logDeriv_Gammaℝ_of_pos hσ]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hm hp hd ⊢
  linarith only [hm, hp, hd, hpi]

/-- For positive sigma at most 5/4, the real logarithmic derivative of
GammaReal is at most -5/4. Digamma monotonicity compares sigma/2 with the existing
13/20 node. This sharper bound applies to every even character. -/
theorem re_logDeriv_GammaReal_le_neg_five_fourths {σ : ℝ} (hσ : 0 < σ) (hu : σ ≤ 5 / 4) :
    (logDeriv Complex.Gammaℝ (σ : ℂ)).re ≤ -(5 / 4 : ℝ) := by
  have hm :=
    re_digamma_mono_of_pos (div_pos hσ (by norm_num only : (0 : ℝ) < 2))
      (show σ / 2 ≤ (13 / 20 : ℝ) by linarith only [hu])
  have hd := gamma_digamma_node_1_bounds.2
  have hpi := gamma_log_pi_bounds.1
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hd hpi
  rw [re_logDeriv_Gammaℝ_of_pos hσ]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hm hd ⊢
  linarith only [hm, hd, hpi]

end PseudoPrime.AnalyticNumberTheory.Gamma
