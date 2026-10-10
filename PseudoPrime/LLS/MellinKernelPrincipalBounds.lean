/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelZetaBounds
public import PseudoPrime.LLS.MellinKernelPoleIntegrals
public import PseudoPrime.LLS.MellinKernelGammaBounds
public import PseudoPrime.LLS.MellinKernelPrimitiveComparison

/-! # Principal-character bounds for general Mellin kernels

Under RH, the modulus-one weighted Mangoldt sum has main term `K(1/2) sqrt x`
and a uniformly bounded error. The finite modulus correction supplies the
principal-character estimate required in Lemma 6.1 for every nonzero modulus.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Under RH and fixed admissible xi contour lines, the modulus-one principal
sum minus `K(1/2) sqrt x` is uniformly bounded for `x ≥ 1`. Split the zeta
logarithmic derivative into xi, two poles and gamma; all four weighted integrals
are absolutely integrable. The positive pole supplies the main term, and the
proved xi, negative-pole, central remainder and gamma bounds control the error. -/
private theorem exists_norm_level_one_summand_sub_main_le_of_lines (K : MellinKernel)
    (hRH : RiemannHypothesis) {a b : ℝ} (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta)
    (ha' : -1 ≤ a) (hb' : b ≤ 1) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          1 ≤ x →
            ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) -
                  K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
              C := by
  obtain ⟨A, hA, hbA⟩ := exists_norm_xi_rightIntegral_le K hRH ha hb ha' hb' haleft hbright
  obtain ⟨B, hB, hbB⟩ := exists_norm_poleIntegral_le_of_neg K (p := -1 / 2) (by norm_num only)
  obtain ⟨C, hC, hbC⟩ := exists_norm_poleIntegral_sub_residue_le K (p := 1 / 2) (by norm_num only)
  obtain ⟨D, hD, hbD⟩ := exists_norm_gammaIntegral_le K
  refine ⟨A + B + C + D, add_pos (add_pos (add_pos hA hB) hC) hD, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hb0 : 0 ≤ b := by linarith only [hbright]
  have hbl : -1 / 2 - K.delta < b := by linarith only [hbright, K.delta_pos]
  have hbn : b ≠ -1 / 2 := by linarith only [hbright]
  let s := fun t : ℝ => (b : ℂ) + Complex.I * t
  let W := fun t : ℝ => K.function (s t) * (x : ℂ) ^ (s t)
  let F := fun t : ℝ => -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t
  let P := fun t : ℝ => (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W t
  let Q := fun t : ℝ => (1 / (s t - ((1 / 2 : ℝ) : ℂ))) * W t
  let G := fun t : ℝ => logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (s t + 1 / 2) * W t
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hiF : MeasureTheory.Integrable F := integrable_xi_right_line K hbright hb hb' hxp
  have hiP : MeasureTheory.Integrable P := by
    simpa only [P, W, s, mul_assoc] using integrable_pole_power_line K hbl hb hbn hbn hxp
  have hiQ : MeasureTheory.Integrable Q := by
    simpa only [Q, W, s, mul_assoc] using integrable_pole_power_line K hbl hb hbn hbright.ne' hxp
  have hiG : MeasureTheory.Integrable G := by
    simpa only [G, W, s, mul_assoc] using
      integrable_gammaFactor_power_line K (1 : DirichletCharacter ℂ 1) (by linarith only [hbright])
        hb (by linarith only [hb']) hxp
  have he (t : ℝ) : -logDeriv riemannZeta (s t + 1 / 2) * W t = F t + P t + Q t + G t := by
    have hr : 1 < (s t + 1 / 2).re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
        Complex.one_re]
      linarith only [hbright]
    dsimp only [F, P, Q, G]
    rw [AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gammaFactor_zeta_of_one_lt_re hr]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hf :
    (fun t : ℝ => -logDeriv riemannZeta (s t + 1 / 2) * W t) = (fun t => F t + P t + Q t + G t) :=
    funext he
  have hsum := tsum_level_one_summand_eq_integral_zeta_logDeriv K hxp hbright hb
  change
    (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) =
      d * (∫ t : ℝ, -logDeriv riemannZeta (s t + 1 / 2) * W t) at hsum
  have hfp := MeasureTheory.integral_add hiF hiP
  have hfpq := MeasureTheory.integral_add (hiF.add hiP) hiQ
  have hfpqg := MeasureTheory.integral_add ((hiF.add hiP).add hiQ) hiG
  simp only [Pi.add_def] at hfp hfpq hfpqg
  rw [hf, hfpqg, hfpq, hfp] at hsum
  have hsqrt : (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (Real.sqrt x : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hxp.le]
  have hq := hbC hbright hb hx
  rw [hsqrt] at hq
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hq
  have hq' : ‖d * (∫ t : ℝ, Q t) - K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤ C := by
    simpa only [d, Q, W, s, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hq
  have hp := hbB hb0 hb hx
  have hg := hbD 1 (1 : DirichletCharacter ℂ 1) hx hb0 hb (by linarith only [hb'])
  have herr :
    (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) -
        K.function (1 / 2) * (Real.sqrt x : ℂ) =
      ((d * (∫ t : ℝ, F t) + d * (∫ t : ℝ, P t)) +
          (d * (∫ t : ℝ, Q t) - K.function (1 / 2) * (Real.sqrt x : ℂ))) +
        d * (∫ t : ℝ, G t) := by
    rw [hsum]
    ring
  rw [herr]
  exact
    (norm_add_le _ _).trans
      (add_le_add
        ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add (hbA hx) hp)) hq'))
        hg)

/-- Every positive-width kernel strip contains xi contour lines with
`-1 ≤ a < -1/2 < 1/2 < b ≤ 1`. Choose symmetric offsets given by
`min(delta/2,1/4)`; positivity and the two upper bounds prove all constraints.
This eliminates contour-line choices from the public principal estimate. -/
private theorem exists_principal_contour_lines (K : MellinKernel) :
    ∃ a b : ℝ,
      -1 / 2 - K.delta < a ∧ b ≤ 1 / 2 + K.delta ∧ -1 ≤ a ∧ b ≤ 1 ∧ a < -1 / 2 ∧ 1 / 2 < b := by
  let η := min (K.delta / 2) (1 / 4)
  have hη : 0 < η := lt_min (half_pos K.delta_pos) (by norm_num only)
  have hηK : η ≤ K.delta / 2 := min_le_left _ _
  have hηQ : η ≤ 1 / 4 := min_le_right _ _
  refine ⟨-1 / 2 - η, 1 / 2 + η, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hηK, K.delta_pos]
  · linarith only [hηK, K.delta_pos]
  · linarith only [hηQ]
  · linarith only [hηQ]
  · linarith only [hη]
  · linarith only [hη]

/-- Under RH, a positive kernel-dependent constant bounds the modulus-one
principal weighted sum minus `K(1/2) sqrt x` for every `x ≥ 1`.
Choose admissible contour lines and apply the proved four-part integral estimate.
This is the level-one analytic input to Lemma 6.1's principal-character branch. -/
theorem exists_norm_level_one_summand_sub_main_le (K : MellinKernel) (hRH : RiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          1 ≤ x →
            ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) -
                  K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
              C := by
  obtain ⟨a, b, ha, hb, ha', hb', haleft, hbright⟩ := exists_principal_contour_lines K
  exact exists_norm_level_one_summand_sub_main_le_of_lines K hRH ha hb ha' hb' haleft hbright

/-- Under RH, the principal-character weighted sum at every nonzero modulus has
main term `K(1/2) sqrt x` and error at most `C(1+log q log x/sqrt x)` for `x ≥ 2`.
Combine the proved modulus-one analytic estimate with the prime-power correction
for primes dividing the modulus. This completes the principal bound in Lemma 6.1. -/
theorem exists_principal_summand_remainder_le (K : MellinKernel) (hRH : RiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] {x : ℝ},
          2 ≤ x →
            ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n) -
                  K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
              C * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  obtain ⟨A, hA, hb⟩ := exists_norm_level_one_summand_sub_main_le K hRH
  apply exists_principal_summand_remainder_le_of_level_one K hA
  intro x hx
  exact hb (by linarith only [hx])

end PseudoPrime.LLS.PaperStatements.MellinKernel
