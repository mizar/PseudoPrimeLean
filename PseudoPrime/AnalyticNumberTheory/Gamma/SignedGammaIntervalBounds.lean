/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.EvenResolventCertificate

/-! # Sign-sensitive rational bounds for even Gamma-factor nodes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The rational upper allowance for a signed even-Gamma node, from digamma
and log-pi intervals. Positive coefficients use the upper digamma and lower
log-pi endpoints; negative coefficients use the opposite endpoints. -/
def signedGammaNodeUpper (c dlo dhi plo phi : ℚ) : ℚ :=
  if 0 ≤ c then c * (dhi - plo) / 2 else c * (dlo - phi) / 2

/-- At a positive real node, certified rational digamma and log-pi intervals
bound the signed logarithmic derivative of the even Gamma factor. The exact
Gamma-factor identity and coefficient sign give the comparison. This generic
lemma supports new finite signed kernels without reusing old numerical sums. -/
theorem signed_gamma_node_upper {σ : ℝ} (hσ : 0 < σ) (c dlo dhi plo phi : ℚ)
    (hd :
      (dlo : ℝ) ≤ (Complex.digamma (((σ / 2 : ℝ)) : ℂ)).re ∧
        (Complex.digamma (((σ / 2 : ℝ)) : ℂ)).re ≤ (dhi : ℝ))
    (hp : (plo : ℝ) ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ (phi : ℝ)) :
    (c : ℝ) * (logDeriv Complex.Gammaℝ (σ : ℂ)).re ≤
      (signedGammaNodeUpper c dlo dhi plo phi : ℝ) := by
  rw [re_logDeriv_Gammaℝ_of_pos hσ]
  by_cases hc : 0 ≤ c
  · simp only [signedGammaNodeUpper, ite_eq_left hc, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_ofNat]
    have h := mul_le_mul_of_nonneg_left (sub_le_sub hd.2 hp.1) (by exact_mod_cast hc : (0 : ℝ) ≤ c)
    linarith only [h]
  · simp only [signedGammaNodeUpper, ite_eq_right hc, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_ofNat]
    have h :=
      mul_le_mul_of_nonpos_left (sub_le_sub hd.1 hp.2)
        (by exact_mod_cast le_of_not_ge hc : (c : ℝ) ≤ 0)
    linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Gamma
