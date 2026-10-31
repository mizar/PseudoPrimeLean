/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaSignedVariableScaleBounds
public import PseudoPrime.LLS.GammaNoNegativeRampSupport
public import PseudoPrime.Analysis.GammaResolventGridCertificate

/-! # Sharp character comparisons retaining the actual resolvent zero mass -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonprincipal character and positive scale, every oscillating Gamma
zero term is dominated by its nonnegative divisor times the certified rational
resolvent. The centered kernel and nonnegative multiplicity suffice; no RH
is needed for this pointwise estimate. It supplies the full-series majorant. -/
theorem norm_gamma_oscillatingZeroTerm_le_resolvent {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        AnalyticNumberTheory.Gamma.gammaResolventMajorant ρ.im := by
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  rw [MellinKernel.norm_oscillatingZeroTerm gammaMellinKernel χ hx]
  change
    ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          Complex.Gamma (Complex.I * ρ.im + 1 / 2)‖ ≤
      _
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hn]
  exact
    mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using Analysis.norm_Gamma_half_add_I_le_gammaResolvent ρ.im) hn

/-- Under individual RH for a primitive nonprincipal character with nonprincipal
inverse, the full oscillating Gamma zero sum is bounded by the actual signed
resolvent mass. Its convergent majorant proves absolute summability and allows
termwise comparison, retaining the prefix gain for later conductor budgets. -/
theorem norm_gamma_oscillatingZeroSum_le_resolvent {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          AnalyticNumberTheory.Gamma.gammaResolventMajorant ρ.im := by
  have hg :=
    AnalyticNumberTheory.DirichletLFunction.summable_completed_gammaResolvent_terms hm hRH hp hne
      hinv
  have hb := norm_gamma_oscillatingZeroTerm_le_resolvent hne hx
  have hs := hg.of_norm_bounded hb
  exact (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum hb hg)

/-- For primitive nonprincipal conductor 3≤m≤q, ambient q≥20000, GRH and x≥2,
the real Gamma arithmetic sum is bounded by its actual resolvent mass plus
the sharp pole and left-contour costs. Preserve the signed nonpositive
archimedean contribution; no positive 64/9 allowance is added. -/
theorem gamma_primitive_sum_re_le_resolvent_sharp {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            AnalyticNumberTheory.Gamma.gammaResolventMajorant ρ.im) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log m + 28) + 1) := by
  have hr := re_gamma_primitive_remainder_le_variable_scale_sharp hq hm hmq hp hne hinv hGRH hx
  have hz :=
    norm_gamma_oscillatingZeroSum_le_resolvent (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      (hGRH m χ hp) hp hne hinv (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hr, hz, hn]

end PseudoPrime.LLS.PaperStatements
