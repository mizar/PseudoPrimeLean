/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivZeta
public import PseudoPrime.AnalyticNumberTheory.Gamma.ShiftedPoleMellin
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedContourLimits
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedLogMellinInversion
public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicShiftIntegral

/-!
# Shifted zeta Mellin formula from xi and gamma resolvents

The entire xi contribution, zeta's pole at one and the shifted gamma poles give
the centered logarithmic-derivative contour under RH for `σ > 1`, `τ > 0`
and `x > 1`. Mellin inversion then expresses the finite shifted Mangoldt sum
through the pole, origin derivatives, and nontrivial and trivial zero residues.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For sigma >= 1 and tau > 0, the shifted gamma kernel sum equals minus half
the digamma difference times x^z/z^2. The reciprocal digamma series identifies the
poles at -(sigma+2+2n). This connects trivial zeros with the completion factor. -/
private theorem gammaPoleKernel_eq_digamma_difference {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ)
    (y : ℝ) :
    (∑' n : ℕ, General.centeredResolventKernel (-((σ : ℂ) + 2 + 2 * (n : ℂ))) x τ y) =
      -((Complex.digamma (((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) / 2 + 1) -
                Complex.digamma ((σ : ℂ) / 2 + 1)) /
              2) *
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have ha : ∀ n : ℕ, (-((σ : ℂ) + 2 + 2 * (n : ℂ))).re < 0 := by
    intro n
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
    linarith only [hσ, Nat.cast_nonneg (α := ℝ) n]
  have he :=
    General.tsum_centeredResolventKernel_eq_difference (fun n : ℕ ↦ -((σ : ℂ) + 2 + 2 * (n : ℂ)))
      (fun _ ↦ 1) ha hτ (x := x) y
  simp only [Nat.cast_one, one_mul] at he
  rw [he]
  have hsp : 0 < (((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) / 2 + 1).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self,
      add_zero]
    linarith only [hσ, hτ]
  have htp : 0 < ((σ : ℂ) / 2 + 1).re := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hσ]
  rw [Gamma.digamma_sub_eq_resolventSeries hsp htp, ← tsum_div_const, ← tsum_neg]
  congr 2
  apply tsum_congr
  intro n
  rw [sub_div,
    show
      ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) / 2 + 1 = ((σ : ℂ) + ((τ : ℂ) + y * Complex.I) + 2) / 2
      by ring,
    show (σ : ℂ) / 2 + 1 = ((σ : ℂ) + 2) / 2 by ring]
  have hs0 : 0 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith only [hσ, hτ]
  rw [Gamma.halfArgument_resolvent_eq hs0
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat]),
    Gamma.halfArgument_resolvent_eq
      (show (0 : ℝ) < (σ : ℂ).re by
        rw [Complex.ofReal_re]; linarith only [hσ])
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat])]
  simp only [sub_neg_eq_add, one_div, inv_neg]
  rw [show
      (τ : ℂ) + y * Complex.I + ((σ : ℂ) + 2 + 2 * (n : ℂ)) =
        (σ : ℂ) + ((τ : ℂ) + y * Complex.I) + 2 + 2 * (n : ℂ)
      by ring]
  ring

/-- Under RH, sigma > 1, tau > 0 and x > 1, the normalized centered zeta contour
is the pole residue minus the xi zero residues and origin derivative, minus the
shifted gamma residues with their inverse-square origin sum. Decompose the zeta
logarithmic derivative and combine three integrable centered resolvent families.
This is the shifted explicit formula before collecting the origin derivative. -/
theorem normalized_integral_centered_zeta_eq (hRH : RiemannHypothesis) {σ τ x : ℝ} (hσ : 1 < σ)
    (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          -(logDeriv riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) -
                  logDeriv riemannZeta (σ : ℂ)) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2) =
      ((x : ℂ) ^ (1 - (σ : ℂ)) - 1) / (1 - (σ : ℂ)) ^ 2 -
        ((∑' ρ : RiemannXi.Zero,
            (analyticOrderNatAt RiemannXi.riemannXi (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
              ((ρ : ℂ) - (σ : ℂ)) ^ 2) +
          deriv (logDeriv RiemannXi.riemannXi) (σ : ℂ)) -
        (General.gammaShiftSum x 2 σ - ∑' n : ℕ, 1 / ((σ : ℂ) + 2 + 2 * (n : ℂ)) ^ 2) := by
  let P := General.centeredResolventKernel (1 - (σ : ℂ)) x τ
  let Z := fun y : ℝ ↦
    ∑' ρ : RiemannXi.Zero,
      (analyticOrderNatAt RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
        General.centeredResolventKernel ((ρ : ℂ) - (σ : ℂ)) x τ y
  let G := fun y : ℝ ↦
    ∑' n : ℕ, General.centeredResolventKernel (-((σ : ℂ) + 2 + 2 * (n : ℂ))) x τ y
  have haP : (1 - (σ : ℂ)).re < 0 := by
    rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hσ]
  have haZ : ∀ ρ : RiemannXi.Zero, ((ρ : ℂ) - (σ : ℂ)).re < 0 := by
    intro ρ
    rw [Complex.sub_re, Complex.ofReal_re,
      RiemannXi.riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property]
    linarith only [hσ]
  have haG : ∀ n : ℕ, (-((σ : ℂ) + 2 + 2 * (n : ℂ))).re < 0 := by
    intro n
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
    linarith only [hσ, Nat.cast_nonneg (α := ℝ) n]
  have hP : MeasureTheory.Integrable P :=
    General.integrable_centeredResolventKernel haP hτ (zero_lt_one.trans hx)
  have hZ : MeasureTheory.Integrable Z :=
    General.integrable_tsum_centeredResolventKernel (fun ρ : RiemannXi.Zero ↦ (ρ : ℂ) - (σ : ℂ))
      (fun ρ : RiemannXi.Zero ↦ analyticOrderNatAt RiemannXi.riemannXi (ρ : ℂ)) haZ hτ
      (zero_lt_one.trans hx)
      (by
        simpa only [RiemannXi.riemannXiZeroMultiplicity] using
          RiemannXi.summable_shifted_power_mass_of_riemannHypothesis hRH hσ.le
            (show (1 : ℝ) < 3 / 2 by norm_num only))
  have hG : MeasureTheory.Integrable G := by
    have h :=
      General.integrable_tsum_centeredResolventKernel (fun n : ℕ ↦ -((σ : ℂ) + 2 + 2 * (n : ℂ)))
        (fun _ ↦ 1) haG hτ (zero_lt_one.trans hx)
        (by
          simpa only [Nat.cast_one] using
            Gamma.summable_gammaPole_power_mass
              (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat]) hσ.le
              (show (1 : ℝ) < 3 / 2 by norm_num only))
    simpa only [Nat.cast_one, one_mul] using h
  have he :
    ∀ y : ℝ,
      -(logDeriv riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) - logDeriv riemannZeta (σ : ℂ)) *
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
          ((τ : ℂ) + y * Complex.I) ^ 2 =
        P y - Z y - G y := by
    intro y
    have hs : 1 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
      linarith only [hσ, hτ]
    change
      _ =
        General.centeredResolventKernel (1 - (σ : ℂ)) x τ y -
          (∑' ρ : RiemannXi.Zero,
            (analyticOrderNatAt RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
              General.centeredResolventKernel ((ρ : ℂ) - (σ : ℂ)) x τ y) -
          (∑' n : ℕ, General.centeredResolventKernel (-((σ : ℂ) + 2 + 2 * (n : ℂ))) x τ y)
    rw [RiemannXi.logDeriv_zeta_sub_eq_xi_sub_pole_sub_gamma hs
        (by simpa only [Complex.ofReal_re] using hσ),
      RiemannXi.zeroResolventKernel_eq_logDeriv_difference hRH hσ.le hτ,
      gammaPoleKernel_eq_digamma_difference hσ.le hτ,
      General.centeredResolventKernel_eq_difference haP hτ]
    rw [show (τ : ℂ) + y * Complex.I - (1 - (σ : ℂ)) = (σ : ℂ) + ((τ : ℂ) + y * Complex.I) - 1 by
        ring,
      show 1 - (σ : ℂ) = -((σ : ℂ) - 1) by ring]
    simp only [one_div, inv_neg]
    ring
  simp_rw [he]
  rw [MeasureTheory.integral_sub (f := fun y ↦ P y - Z y) (g := G) (hP.sub hZ) hG,
    MeasureTheory.integral_sub (f := P) (g := Z) hP hZ, smul_sub, smul_sub]
  dsimp only [P, Z, G]
  rw [General.integral_centeredResolventKernel_eq haP hτ hx,
    RiemannXi.normalized_integral_zeroResolvent_eq_of_riemannHypothesis hRH hσ.le hτ hx,
    Gamma.normalized_integral_gammaPoleResolvent_eq
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat]) hσ.le hτ hx]

/-- Under RH, sigma > 1, tau > 0 and x > 1, the centered negative zeta
logarithmic derivative's Mellin integral is the pole residue minus its derivative,
nontrivial-zero residues and trivial-zero residues. Collect the xi, pole and gamma
origin terms using the differentiated completion identity. This gives the centered
shifted explicit formula used before integrating sigma in Lemma 2.6. -/
theorem normalized_integral_centered_zeta_eq_residues (hRH : RiemannHypothesis) {σ τ x : ℝ}
    (hσ : 1 < σ) (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          -(logDeriv riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) -
                  logDeriv riemannZeta (σ : ℂ)) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2) =
      (x : ℂ) ^ (1 - (σ : ℂ)) / ((σ : ℂ) - 1) ^ 2 - deriv (logDeriv riemannZeta) (σ : ℂ) -
        (∑' ρ : RiemannXi.Zero,
          (analyticOrderNatAt RiemannXi.riemannXi (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2) -
        General.gammaShiftSum x 2 σ := by
  have hM := normalized_integral_centered_zeta_eq hRH hσ hτ hx
  have hO := RiemannXi.deriv_logDeriv_zeta_eq_xi_pole_gamma hσ
  rw [show 1 - (σ : ℂ) = -((σ : ℂ) - 1) by ring, neg_sq] at hM
  rw [show 1 - (σ : ℂ) = -((σ : ℂ) - 1) by ring]
  linear_combination hM + hO

/-- Under RH, sigma > 1 and x > 1, the finite shifted Mangoldt sum
weighted by log(x/n) equals the pole residue minus the zeta logarithmic derivative
and its derivative, nontrivial-zero residues and trivial-zero residues. Specialize
character Mellin inversion to modulus one and evaluate the centered zeta contour;
the constant contour supplies the log x term. This is the shifted formula in Lemma 2.6. -/
theorem shifted_logarithmicWeightedSum_eq_residues (hRH : RiemannHypothesis) {σ x : ℝ} (hσ : 1 < σ)
    (hx : 1 < x) :
    General.logarithmicWeightedSum
        (General.shiftedLSeriesCoefficient (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) σ) x =
      (x : ℂ) ^ (1 - (σ : ℂ)) / ((σ : ℂ) - 1) ^ 2 -
        logDeriv riemannZeta (σ : ℂ) * (Real.log x : ℂ) -
        deriv (logDeriv riemannZeta) (σ : ℂ) -
        (∑' ρ : RiemannXi.Zero,
          (analyticOrderNatAt RiemannXi.riemannXi (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2) -
        General.gammaShiftSum x 2 σ := by
  let τ : ℝ := 1
  have hτ : 0 < τ := by norm_num only [τ]
  let U := fun y : ℝ ↦
    -logDeriv riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) *
        (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
      ((τ : ℂ) + y * Complex.I) ^ 2
  let K := fun y : ℝ ↦ (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I) ^ 2
  let V := fun y : ℝ ↦ logDeriv riemannZeta (σ : ℂ) * K y
  have hU : MeasureTheory.Integrable U := by
    have h :=
      DirichletLFunction.integrable_shiftedLogContourKernel_vertical (1 : DirichletCharacter ℂ 1)
        (zero_lt_one.trans hx) hσ.le hτ
    simpa only [U, DirichletLFunction.shiftedLogContourKernel,
      DirichletCharacter.LFunction_modOne_eq, logDeriv_apply, neg_div] using h
  obtain ⟨hK, hKI⟩ := General.logarithmicMellin_integrable_and_integral hτ hx
  have hV : MeasureTheory.Integrable V := hK.const_mul (logDeriv riemannZeta (σ : ℂ))
  have hVI :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, V y) = logDeriv riemannZeta (σ : ℂ) * (Real.log x : ℂ) := by
    dsimp only [V, K]
    rw [MeasureTheory.integral_const_mul, Complex.real_smul]
    rw [Complex.real_smul] at hKI
    rw [← mul_assoc, mul_comm _ (logDeriv riemannZeta (σ : ℂ)), mul_assoc, hKI]
  have hM := normalized_integral_centered_zeta_eq_residues hRH hσ hτ hx
  have he :
    ∀ y : ℝ,
      -(logDeriv riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) - logDeriv riemannZeta (σ : ℂ)) *
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
          ((τ : ℂ) + y * Complex.I) ^ 2 =
        U y + V y := by
    intro y
    dsimp only [U, V, K]
    ring
  simp_rw [he] at hM
  rw [MeasureTheory.integral_add hU hV, smul_add, hVI] at hM
  have hA :=
    DirichletLFunction.shifted_logarithmic_sum_eq_integral (1 : DirichletCharacter ℂ 1)
      (zero_lt_one.trans hx) hσ.le hτ
  have hcoef :
    (fun n : ℕ ↦
        (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one, one_mul]
  rw [hcoef] at hA
  have hA' :
    General.logarithmicWeightedSum
        (General.shiftedLSeriesCoefficient (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) σ) x =
      (2 * Real.pi)⁻¹ • (∫ y : ℝ, U y) := by
    simpa only [U, DirichletLFunction.shiftedLogContourKernel,
      DirichletCharacter.LFunction_modOne_eq, logDeriv_apply, neg_div] using hA
  linear_combination hA' + hM

/-- The main part of the shifted zeta formula, combining the residue at one with
the logarithmic derivative and its derivative at real sigma. For x > 1 and sigma > 1,
the pole and logarithmic singularities at `σ = 1` cancel in their combination.
Its sigma integral supplies the main term in Lemma 2.6. -/
noncomputable def shiftedZetaMainKernel (x σ : ℝ) : ℂ :=
  (x : ℂ) ^ (1 - (σ : ℂ)) / ((σ : ℂ) - 1) ^ 2 - logDeriv riemannZeta (σ : ℂ) * (Real.log x : ℂ) -
    deriv (logDeriv riemannZeta) (σ : ℂ)

/-- Under RH and x > 1, the combined zeta pole and origin terms are integrable
over sigma > 1. Express them as the finite shifted Mangoldt sum plus the two
integrable zero residue families. This establishes integrability without separating
the three singular main terms at sigma=1. -/
theorem integrableOn_shiftedZetaMainKernel (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    MeasureTheory.IntegrableOn (shiftedZetaMainKernel x) (Set.Ioi 1) := by
  have ha : (ArithmeticFunction.vonMangoldt 1 : ℂ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero]
  have hF :=
    General.integrableOn_logarithmicWeightedSum_shifted
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ha x
  have hZ := RiemannXi.integrableOn_shifted_zero_sum hRH hx
  have hG :=
    General.integrableOn_gammaShiftSum hx
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat])
  apply ((hF.add hZ).add hG).congr
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
  simp only [Pi.add_apply]
  rw [shifted_logarithmicWeightedSum_eq_residues hRH hσ hx, shiftedZetaMainKernel]
  unfold RiemannXi.riemannXiZeroMultiplicity
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
