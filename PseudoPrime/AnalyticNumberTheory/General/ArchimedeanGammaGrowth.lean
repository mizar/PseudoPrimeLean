/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ArchimedeanGammaPoles
public import PseudoPrime.AnalyticNumberTheory.Gamma.Conjugation

/-!
# Gamma logarithmic growth on positive strips

Positive gamma arguments admit a uniform linear-height bound. Nonnegative
shifts therefore supply the bounds needed for Mellin integration-line shifts.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- If all affine gamma arguments have positive real part, the gamma factor's
logarithmic derivative is the pi constant plus the half-weighted digamma sum.
Exclude gamma poles and differentiate the finite product. This extends the
right-half-plane formula to the critical line for nonnegative-real shifts. -/
theorem logDeriv_archimedeanGammaFactor_of_argument_re_pos {d : ℕ} {κ : Fin d → ℂ} {s : ℂ}
    (hp : ∀ j, 0 < ((s + κ j) / 2).re) :
    logDeriv (archimedeanGammaFactor κ) s =
      (-(d : ℂ) / 2) * Complex.log (Real.pi : ℂ) +
        ∑ j : Fin d, (1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2) := by
  have hn : ∀ j, ∀ n : ℕ, (s + κ j) / 2 ≠ -(n : ℂ) := by
    intro j n he
    have hh := hp j
    rw [he, Complex.neg_re, Complex.natCast_re] at hh
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hh
  have hprod : archimedeanGammaProduct κ s ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ ↦ Complex.Gamma_ne_zero_of_re_pos (hp j))
  have hdiff : DifferentiableAt ℂ (archimedeanGammaProduct κ) s := by
    apply DifferentiableAt.fun_finsetProd
    intro j _
    exact
      (Complex.differentiableAt_Gamma _ (hn j)).comp s
        (((hasDerivAt_id' s).add_const (κ j)).div_const 2).differentiableAt
  have hlog :
    logDeriv (archimedeanGammaProduct κ) s =
      ∑ j : Fin d, (1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2) := by
    change logDeriv (fun z ↦ ∏ j : Fin d, Complex.Gamma ((z + κ j) / 2)) s = _
    rw [logDeriv_fun_prod (f := fun j z ↦ Complex.Gamma ((z + κ j) / 2)) (x := s)
        (fun j _ ↦ Complex.Gamma_ne_zero_of_re_pos (hp j))
        (fun j _ ↦
          (Complex.differentiableAt_Gamma _ (hn j)).comp s
            (((hasDerivAt_id' s).add_const (κ j)).div_const 2).differentiableAt)]
    exact
      Finset.sum_congr rfl
        (fun j _ ↦ (((hasDerivAt_id' s).add_const (κ j)).div_const 2).logDeriv_Gamma (hn j))
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd :=
    ((hasDerivAt_id' s).const_mul (-(d : ℂ) / 2)).const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
  change logDeriv (fun z ↦ (Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * z) * archimedeanGammaProduct κ z) s = _
  rw [logDeriv_fun_mul (f := fun z ↦ (Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * z)) (g :=
      archimedeanGammaProduct κ) s (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)) hprod
      hd.differentiableAt hdiff,
    logDeriv_affinePower hpi, hlog]

/-- For positive-real gamma arguments, the gamma logarithmic derivative norm is
bounded by the pi contribution plus half the sum of digamma norms. Apply the
triangle inequality to the exact derivative formula. This reduces strip growth
to the individual gamma arguments. -/
theorem norm_logDeriv_archimedeanGammaFactor_of_argument_re_pos {d : ℕ} {κ : Fin d → ℂ} {s : ℂ}
    (hp : ∀ j, 0 < ((s + κ j) / 2).re) :
    ‖logDeriv (archimedeanGammaFactor κ) s‖ ≤
      (d : ℝ) / 2 * ‖Complex.log (Real.pi : ℂ)‖ +
        (1 / 2 : ℝ) * ∑ j : Fin d, ‖Complex.digamma ((s + κ j) / 2)‖ := by
  rw [logDeriv_archimedeanGammaFactor_of_argument_re_pos hp]
  calc
    _ ≤
        ‖(-(d : ℂ) / 2) * Complex.log (Real.pi : ℂ)‖ +
          ‖∑ j : Fin d, (1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2)‖ :=
      norm_add_le _ _
    _ ≤
        ‖(-(d : ℂ) / 2) * Complex.log (Real.pi : ℂ)‖ +
          ∑ j : Fin d, ‖(1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2)‖ :=
      add_le_add le_rfl (norm_sum_le _ _)
    _ = _ := by
      simp only [norm_mul, norm_div, norm_neg, norm_natCast, norm_one, Complex.norm_ofNat]
      rw [Finset.mul_sum]

/-- For nonnegative-real shifts and an ordered real strip with positive left
endpoint, the gamma logarithmic derivative has a uniform linear-height bound.
Use the left endpoint to control reciprocal arguments and the right endpoint
for their norms, then sum the digamma bounds. This discharges the growth inputs
of vertical Mellin integrability and horizontal contour decay. -/
theorem exists_archimedeanGamma_linear_bound_on_positive_strip {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ σ ∈ Set.Icc a b,
          ∀ T : ℝ,
            ‖logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|) := by
  let M : ℝ := b + Real.pi + |Gamma.digammaLogErrorBound| + (a / 2)⁻¹
  let C : ℝ := (d : ℝ) / 2 * ‖Complex.log (Real.pi : ℂ)‖ + (1 / 2 : ℝ) * ∑ j : Fin d, (‖κ j‖ + M)
  have hb : 0 < b := ha.trans_le hab
  have hδ : 0 < a / 2 := half_pos ha
  have hM : 0 ≤ M :=
    add_nonneg (add_nonneg (add_nonneg hb.le Real.pi_pos.le) (abs_nonneg _)) (inv_nonneg.mpr hδ.le)
  have hC : 0 ≤ C :=
    add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg d) (by norm_num only)) (norm_nonneg _))
      (mul_nonneg (by norm_num only) (Finset.sum_nonneg (fun j _ ↦ add_nonneg (norm_nonneg _) hM)))
  refine ⟨C + d / 2, add_nonneg hC (div_nonneg (Nat.cast_nonneg d) (by norm_num only)), ?_⟩
  intro σ hσ T
  have hp : ∀ j, a / 2 ≤ ((((σ : ℂ) + T * Complex.I) + κ j) / 2).re := by
    intro j
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    linarith only [hσ.1, hk j]
  have hnorm : ‖(σ : ℂ) + T * Complex.I‖ ≤ b + |T| := by
    have hh := norm_add_le (σ : ℂ) ((T : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_nonneg (ha.le.trans hσ.1)] at hh
    linarith only [hh, hσ.2]
  have hd : ∀ j, ‖Complex.digamma ((((σ : ℂ) + T * Complex.I) + κ j) / 2)‖ ≤ ‖κ j‖ + M + |T| := by
    intro j
    have hn : ‖(((σ : ℂ) + T * Complex.I) + κ j) / 2‖ ≤ b + |T| + ‖κ j‖ := by
      rw [norm_div, Complex.norm_ofNat]
      have hh := norm_add_le ((σ : ℂ) + T * Complex.I) (κ j)
      linarith only [hh, hnorm, norm_nonneg (((σ : ℂ) + T * Complex.I) + κ j)]
    have hh := Gamma.norm_digamma_le_linear_of_re_ge hδ (hp j)
    dsimp only [M]
    linarith only [hh, hn, le_abs_self Gamma.digammaLogErrorBound]
  have hs := norm_logDeriv_archimedeanGammaFactor_of_argument_re_pos (fun j ↦ hδ.trans_le (hp j))
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hd j)
  have hexpand : (∑ j : Fin d, (‖κ j‖ + M + |T|)) = (∑ j : Fin d, (‖κ j‖ + M)) + d * |T| := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hexpand] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (by norm_num only : (0 : ℝ) ≤ 1 / 2)
  have hh : ‖logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + T * Complex.I)‖ ≤ C + d / 2 * |T| := by
    dsimp only [C]
    linarith only [hs, hm]
  nlinarith only [hh, mul_nonneg hC (abs_nonneg T), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- For nonnegative-real shifts and a positive-real argument, the conjugate gamma
logarithmic derivative at the conjugate argument equals the factor with conjugate
shifts. Conjugate the digamma sum and the real pi constant. This identifies the
dual factor when shifting both gamma integrals to the critical line. -/
theorem star_logDeriv_archimedeanGammaFactor {d : ℕ} (κ : Fin d → ℂ) (hk : ∀ j, 0 ≤ (κ j).re)
    {s : ℂ} (hs : 0 < s.re) :
    star (logDeriv (archimedeanGammaFactor κ) (star s)) =
      logDeriv (archimedeanGammaFactor (fun j ↦ star (κ j))) s := by
  have hp : ∀ j, 0 < ((star s + κ j) / 2).re := by
    intro j
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.star_def, Complex.conj_re]
    linarith only [hs, hk j]
  have hq : ∀ j, 0 < ((s + star (κ j)) / 2).re := by
    intro j
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.star_def, Complex.conj_re]
    linarith only [hs, hk j]
  rw [logDeriv_archimedeanGammaFactor_of_argument_re_pos hp,
    logDeriv_archimedeanGammaFactor_of_argument_re_pos hq]
  simp only [Complex.star_def, map_add, map_mul, map_div₀, map_neg, map_natCast, map_ofNat, map_one,
    map_sum, ← Gamma.digamma_conj, Complex.conj_conj, ← Complex.ofReal_log Real.pi_pos.le,
    Complex.conj_ofReal]

end PseudoPrime.AnalyticNumberTheory.General
