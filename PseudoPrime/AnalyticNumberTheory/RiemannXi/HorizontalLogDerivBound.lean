/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivGammaFactor
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth

/-! # Bounds for the logarithmic derivative of ξ on horizontal contour edges

Separate the pole, level-one gamma factor and zeta logarithmic derivative.
The fixed-strip gamma estimate leaves the zeta term available for good-height bounds.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- A fixed-strip gamma bound controls the ξ logarithmic derivative above height eight,
apart from the zeta term. The pole contributes at most one; the gamma contribution
is linear in the height. This estimate is used on horizontal contour edges. -/
theorem norm_logDeriv_le_pole_gamma_zeta (C : ℝ)
    (hg :
      ∀ (σ T : ℝ),
        -(3 : ℝ) - 1 / 2 ≤ σ →
          σ ≤ 3 + 3 / 2 →
          1 ≤ |T| →
          ‖logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor ((σ : ℂ) + T * Complex.I)‖ ≤
            C * (|T| + 1))
    (σ T : ℝ) (ha : -(1 : ℝ) / 2 ≤ σ) (hb : σ ≤ 2) (ht : 8 ≤ T)
    (hz : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0) :
    ‖logDeriv riemannXi ((σ : ℂ) + T * Complex.I)‖ ≤
      1 + C * (T + 1) + ‖logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
  have hre : -2 < ((σ : ℂ) + T * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith only [ha]
  have him : ((σ : ℂ) + T * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have hn : (σ : ℂ) + T * Complex.I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    rw [him, Complex.one_im] at hi
    linarith only [ht, hi]
  have hnorm : 1 ≤ ‖((σ : ℂ) + T * Complex.I) - 1‖ := by
    have hi := Complex.abs_im_le_norm (((σ : ℂ) + T * Complex.I) - 1)
    rw [Complex.sub_im, him, Complex.one_im, sub_zero, abs_of_nonneg (by linarith only [ht])] at hi
    linarith only [hi, ht]
  have hp : ‖1 / (((σ : ℂ) + T * Complex.I) - 1)‖ ≤ 1 := by
    rw [one_div, norm_inv]
    exact inv_le_one_of_one_le₀ hnorm
  have hg' :=
    hg (σ + 2) T
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [ha])
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [hb])
      (by
        rw [abs_of_nonneg (by linarith only [ht])]; linarith only [ht])
  rw [abs_of_nonneg (by linarith only [ht])] at hg'
  have he : ((σ : ℂ) + T * Complex.I) + 2 = ((σ + 2 : ℝ) : ℂ) + T * Complex.I := by
    rw [Complex.ofReal_add, Complex.ofReal_ofNat]
    ring
  rw [logDeriv_eq_pole_gammaFactor_zeta_of_regular hre hn hz]
  have htriangle :=
    norm_add_le
      (1 / (((σ : ℂ) + T * Complex.I) - 1) +
        logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (((σ : ℂ) + T * Complex.I) + 2))
      (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I))
  have htriangle' :=
    norm_add_le (1 / (((σ : ℂ) + T * Complex.I) - 1))
      (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (((σ : ℂ) + T * Complex.I) + 2))
  rw [he] at htriangle htriangle' ⊢
  linarith only [hp, hg', htriangle, htriangle']

/-- A single nonnegative constant controls the gamma contribution uniformly across
the central strip above height eight. Specialize the character-independent strip
bound and retain the zeta logarithmic derivative for later good-height estimates. -/
theorem exists_norm_logDeriv_le_pole_gamma_zeta :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ (σ T : ℝ),
          -(1 : ℝ) / 2 ≤ σ →
            σ ≤ 2 →
            8 ≤ T →
            riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0 →
            ‖logDeriv riemannXi ((σ : ℂ) + T * Complex.I)‖ ≤
              1 + C * (T + 1) + ‖logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
  obtain ⟨C, hC, hg⟩ := DirichletLFunction.exists_norm_logDeriv_gammaFactor_fixed_strip_le 3
  exact ⟨C, hC, norm_logDeriv_le_pole_gamma_zeta C (hg (1 : DirichletCharacter ℂ 1))⟩

/-- At zeta good heights, a uniform bound for ξ consists of a linear gamma term and
a squared-logarithmic zeta term. Combining the completion identity with the zero
separation estimate gives the majorant used to remove horizontal contour edges. -/
theorem exists_norm_logDeriv_good_height_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ (H T σ : ℝ),
          8 ≤ H →
            T ∈ Set.Icc H (H + 1) →
            (∀ ρ : ℂ,
              riemannZeta ρ = 0 →
                |ρ.im - H| ≤ 2 →
                1 / (4 * RiemannZeta.jensenLogConst * Real.log (H + 2)) ≤ |T - ρ.im|) →
            -(1 : ℝ) / 2 ≤ σ →
            σ ≤ 2 →
            ‖logDeriv riemannXi ((σ : ℂ) + T * Complex.I)‖ ≤
              1 + C * (T + 1) + RiemannZeta.qMinusOneZetaLogDerivConst * Real.log (T + 2) ^ 2 := by
  obtain ⟨C, hC, hg⟩ := exists_norm_logDeriv_le_pole_gamma_zeta
  refine ⟨C, hC, ?_⟩
  intro H T σ hH hT hgood ha hb
  have hz := RiemannZeta.riemannZeta_ne_zero_of_good_height hH hT hgood σ
  exact
    (hg σ T ha hb (hH.trans hT.1) hz).trans
      (add_le_add_right (RiemannZeta.forall_norm_logDeriv_riemannZeta_le hH hT hgood σ ha hb hz)
        (1 + C * (T + 1)))

/-- The same good-height majorant controls both horizontal ξ edges in the strip
`[-1/2,3/2]`. Reflect the lower edge through `s ↦ 1-s` and use the functional
equation; its image lies in the strip of the upper-edge estimate. -/
theorem exists_norm_logDeriv_signed_good_height_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ (H T σ e : ℝ),
          8 ≤ H →
            T ∈ Set.Icc H (H + 1) →
            (∀ ρ : ℂ,
              riemannZeta ρ = 0 →
                |ρ.im - H| ≤ 2 →
                1 / (4 * RiemannZeta.jensenLogConst * Real.log (H + 2)) ≤ |T - ρ.im|) →
            -(1 : ℝ) / 2 ≤ σ →
            σ ≤ 3 / 2 →
            (e = 1 ∨ e = -1) →
            ‖logDeriv riemannXi ((σ : ℂ) + ((e * T : ℝ) : ℂ) * Complex.I)‖ ≤
              1 + C * (T + 1) + RiemannZeta.qMinusOneZetaLogDerivConst * Real.log (T + 2) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_logDeriv_good_height_le
  refine ⟨C, hC, ?_⟩
  intro H T σ e hH hT hgood ha hb he
  rcases he with rfl | rfl
  · rw [one_mul]
    exact hbound H T σ hH hT hgood ha (by linarith only [hb])
  · have h := hbound H T (1 - σ) hH hT hgood (by linarith only [hb]) (by linarith only [ha])
    have hr :
      ((1 - σ : ℝ) : ℂ) + T * Complex.I = 1 - ((σ : ℂ) + ((-1 * T : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, neg_one_mul, Complex.ofReal_neg]
      ring
    rw [hr, logDeriv_one_sub, norm_neg] at h
    exact h

end PseudoPrime.AnalyticNumberTheory.RiemannXi
