/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaConductorFreeCharacterComparison

/-! # Variable-scale signed Jacobi comparison without a decimal input gate -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal data with 3 ≤ m ≤ q, q ≥ 20000, GRH and x ≥ 2,
bound the actual arithmetic sum by the resolvent zero mass, pole allowance,
exact nonpositive conductor integral and conductor-free remainder.
Combine the signed completed formula with the absolutely convergent zero majorant.
This retains the negative conductor gain for the Jacobi comparison. -/
theorem gamma_primitive_sum_re_le_resolvent_signed_conductor {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            AnalyticNumberTheory.Gamma.gammaResolventMajorant ρ.im) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm (Real.log m) x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hr := re_gamma_primitive_remainder_le_signed_conductor hq hm hmq hp hne hinv hGRH hx
  have hz :=
    norm_gamma_oscillatingZeroSum_le_resolvent (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      (hGRH m χ hp) hp hne hinv (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hr, hz, hn]

end PseudoPrime.LLS.PaperStatements
