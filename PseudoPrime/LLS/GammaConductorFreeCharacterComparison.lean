/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventCharacterComparison
public import PseudoPrime.LLS.GammaSignedConductorRemainder

/-! # Character comparison with a conductor-free left allowance -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal conductor 3≤m≤q, ambient q≥20000, GRH and x≥2,
the real Gamma arithmetic sum is bounded by its actual resolvent mass plus
the pole cost and conductor-free left allowance. Preserve the nonpositive
archimedean contribution; no positive 64/9 allowance is added. -/
theorem gamma_primitive_sum_re_le_resolvent_conductor_free {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hz :=
    norm_gamma_oscillatingZeroSum_le_resolvent (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      (hGRH m χ hp) hp hne hinv (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hr, hz, hn]

end PseudoPrime.LLS.PaperStatements
