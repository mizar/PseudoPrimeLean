/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.ReciprocalPoleMellin
public import PseudoPrime.AnalyticNumberTheory.Gamma.UniformReciprocalResidues
public import PseudoPrime.LLS.Extensions.ReciprocalArithmeticMellin
public import PseudoPrime.LLS.Extensions.ShiftedMellinFormula

/-!
# Reciprocal Mellin formula for the completion factor

The finite gamma family gives explicit residue sums, including the repeated pole at `-1`.
Its contribution to the ordinary reciprocal formula is the endpoint constant times
`1 - 1/x`, minus the residue sum. The latter is bounded by a fixed constant times
`(log x + 1)/x`.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Sum reciprocal resolvent kernels over all gamma shifts and poles `-1 - κ_j - 2n`.
Admissibility gives nonnegative shift real parts and summable pole mass. This integrand
represents the centered logarithmic derivative of the completion factor. -/
noncomputable def reciprocalGammaMellinIntegrand (f : GeneralLFunction) (x τ y : ℝ) : ℂ :=
  ∑ j : Fin f.degree,
    ∑' n : ℕ,
      AnalyticNumberTheory.General.reciprocalResolventKernel
        (AnalyticNumberTheory.Gamma.reciprocalGammaPole (f.shift j) n) x τ y

/-- The finite sum over gamma shifts of their reciprocal Mellin residue series.
The residue definition includes `-log x/x` at a repeated pole. Under admissibility and
`x > 1` these series converge absolutely and form the completion-factor remainder. -/
noncomputable def reciprocalGammaSum (f : GeneralLFunction) (x : ℝ) : ℂ :=
  ∑ j : Fin f.degree, ∑' n : ℕ, AnalyticNumberTheory.Gamma.reciprocalGammaResidue (f.shift j) n x

/-- A nonnegative bound for the fixed gamma family: sum each shift's reciprocal coefficient
series plus one for its possible repeated pole. Under admissibility this constant bounds
the residue sum by `(log x + 1)/x`; dependence on the fixed shifts is allowed. -/
noncomputable def reciprocalGammaBound (f : GeneralLFunction) : ℝ :=
  ∑ j : Fin f.degree,
    ((∑' n : ℕ, AnalyticNumberTheory.Gamma.reciprocalGammaCoefficient (f.shift j) n) + 1)

/-- For admissible data and positive `x,τ`, the reciprocal gamma-family integrand is integrable.
Sum the integrable individual gamma-pole series over the finite family. This permits
subtraction of the gamma contribution from the normalized vertical integral. -/
theorem integrable_reciprocalGammaMellinIntegrand (f : GeneralLFunction) (hf : f.IsAdmissible)
    {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x) :
    MeasureTheory.Integrable (f.reciprocalGammaMellinIntegrand x τ) := by
  exact
    MeasureTheory.integrable_finsetSum Finset.univ
      (fun j _ ↦
        AnalyticNumberTheory.Gamma.integrable_reciprocalGammaPoleSeries (hf.2.2.2.1 j) hτ hx)

/-- For admissible data, `τ > 0` and `x > 1`, the normalized gamma-family integral equals its
reciprocal residue sum. Integrate the finite family and evaluate each absolutely integrable
pole series. This includes the repeated-pole contribution at zero shifts. -/
theorem normalized_integral_reciprocalGamma_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, f.reciprocalGammaMellinIntegrand x τ y) =
      f.reciprocalGammaSum x := by
  unfold reciprocalGammaMellinIntegrand reciprocalGammaSum
  rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun j _ ↦
        AnalyticNumberTheory.Gamma.integrable_reciprocalGammaPoleSeries (hf.2.2.2.1 j) hτ
          (zero_lt_one.trans hx)),
    Finset.smul_sum]
  exact
    Finset.sum_congr rfl
      (fun j _ ↦
        AnalyticNumberTheory.Gamma.integral_tsum_reciprocalGammaPole_eq (hf.2.2.2.1 j) hτ hx)

/-- The reciprocal gamma-family integrand is the centered logarithmic gamma integrand at
center one multiplied by `z/(z + 1)`. Extract the common multiplier from the finite and
infinite sums. The identity is algebraic and identifies the existing digamma expansion. -/
theorem reciprocalGammaMellinIntegrand_eq_logarithmic_mul (f : GeneralLFunction) (x τ y : ℝ) :
    f.reciprocalGammaMellinIntegrand x τ y =
      f.gammaResolventMellinIntegrand x 1 τ y *
        (((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)) := by
  unfold reciprocalGammaMellinIntegrand gammaResolventMellinIntegrand
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  simp only [AnalyticNumberTheory.General.reciprocalResolventKernel,
    AnalyticNumberTheory.Gamma.reciprocalGammaPole, Complex.ofReal_one]

/-- For admissible data and `τ > 0`, the reciprocal gamma integrand equals the negative
completion-factor logarithmic-derivative difference from one, times `x^z/(z(z + 1))`.
Transfer the established centered digamma identity through the reciprocal multiplier.
This provides the pointwise decomposition before integration. -/
theorem reciprocalGammaMellinIntegrand_eq (f : GeneralLFunction) (hf : f.IsAdmissible) {τ x : ℝ}
    (hτ : 0 < τ) (y : ℝ) :
    f.reciprocalGammaMellinIntegrand x τ y =
      -(logDeriv f.completionFactor (1 + ((τ : ℂ) + y * Complex.I)) -
              logDeriv f.completionFactor 1) *
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) := by
  rw [reciprocalGammaMellinIntegrand_eq_logarithmic_mul,
    gammaResolventMellinIntegrand_eq f hf (σ := 1) le_rfl hτ]
  have hk :=
    AnalyticNumberTheory.General.reciprocalMellinTerm_eq_logarithmicMellinTerm_mul
      (fun _ ↦
        -(logDeriv f.completionFactor (1 + ((τ : ℂ) + y * Complex.I)) -
            logDeriv f.completionFactor 1))
      x hτ 1 y
  simpa only [AnalyticNumberTheory.General.reciprocalMellinTerm,
    AnalyticNumberTheory.General.logarithmicMellinTerm, Nat.cast_one, Complex.one_cpow, mul_one,
    Complex.ofReal_one] using hk.symm

/-- For admissible data and `x > 1`, the gamma residue sum has norm at most its fixed gamma
bound times `(log x + 1)/x`. Apply the individual absolutely convergent series bounds and
the finite triangle inequality. This gives the archimedean part of the reciprocal remainder. -/
theorem norm_reciprocalGammaSum_le (f : GeneralLFunction) (hf : f.IsAdmissible) {x : ℝ}
    (hx : 1 < x) : ‖f.reciprocalGammaSum x‖ ≤ f.reciprocalGammaBound * ((Real.log x + 1) / x) := by
  unfold reciprocalGammaSum reciprocalGammaBound
  apply (norm_sum_le Finset.univ _).trans
  rw [Finset.sum_mul]
  exact
    Finset.sum_le_sum
      (fun j _ ↦ AnalyticNumberTheory.Gamma.norm_tsum_reciprocalGammaResidue_le (hf.2.2.2.1 j) hx)

/-- The completion-factor logarithmic derivative at `1 + z`, multiplied by the reciprocal
Mellin kernel `x^z/(z(z + 1))`, with `z = τ + iy`. This is subtracted from the ordinary
logarithmic-derivative integral when recovering the completed-function formula. -/
noncomputable def completionReciprocalMellinIntegrand (f : GeneralLFunction) (x τ y : ℝ) : ℂ :=
  logDeriv f.completionFactor (1 + ((τ : ℂ) + y * Complex.I)) *
      (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
    (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))

/-- For admissible data and `τ > 0`, the completion-factor reciprocal integrand splits into
its endpoint derivative times the base kernel, minus the gamma-family integrand.
Use the centered gamma identity and distribute the common kernel. This isolates the
endpoint constant and the residue contribution. -/
theorem completionReciprocalMellinIntegrand_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    {τ x : ℝ} (hτ : 0 < τ) (y : ℝ) :
    f.completionReciprocalMellinIntegrand x τ y =
      logDeriv f.completionFactor 1 *
          ((x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) -
        f.reciprocalGammaMellinIntegrand x τ y := by
  rw [reciprocalGammaMellinIntegrand_eq f hf hτ]
  unfold completionReciprocalMellinIntegrand
  ring

/-- For admissible data, `τ > 0` and `x > 1`, the completion-factor reciprocal integrand is
integrable. Its endpoint part is a constant multiple of the integrable base kernel; its
remaining gamma-family part is integrable. This justifies the ordinary/completed integral split. -/
theorem integrable_completionReciprocalMellinIntegrand (f : GeneralLFunction) (hf : f.IsAdmissible)
    {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    MeasureTheory.Integrable (f.completionReciprocalMellinIntegrand x τ) := by
  rw [funext (completionReciprocalMellinIntegrand_eq f hf (x := x) hτ)]
  exact
    ((AnalyticNumberTheory.General.reciprocalMellin_integrable_and_integral hτ hx).1.const_mul
          (logDeriv f.completionFactor 1)).sub
      (integrable_reciprocalGammaMellinIntegrand f hf hτ (zero_lt_one.trans hx))

/-- For admissible data, `τ > 0` and `x > 1`, the normalized completion-factor integral equals
its logarithmic derivative at one times `1 - 1/x`, minus the gamma residue sum.
Integrate the endpoint/gamma decomposition using absolute integrability. This removes the
archimedean Mellin integral from the general reciprocal remainder. -/
theorem normalized_integral_completionReciprocalMellin_eq (f : GeneralLFunction)
    (hf : f.IsAdmissible) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, f.completionReciprocalMellinIntegrand x τ y) =
      logDeriv f.completionFactor 1 * (1 - (x : ℂ)⁻¹) - f.reciprocalGammaSum x := by
  obtain ⟨hG, hGI⟩ := AnalyticNumberTheory.General.reciprocalMellin_integrable_and_integral hτ hx
  rw [funext (completionReciprocalMellinIntegrand_eq f hf (x := x) hτ),
    MeasureTheory.integral_sub (hG.const_mul (logDeriv f.completionFactor 1))
      (integrable_reciprocalGammaMellinIntegrand f hf hτ (zero_lt_one.trans hx)),
    smul_sub, MeasureTheory.integral_const_mul, ← mul_smul_comm, hGI,
    normalized_integral_reciprocalGamma_eq f hf hτ hx]

/-- The fixed gamma bound is nonnegative for any L-function data. Its coefficients are
nonnegative real quotients, and each finite-family summand includes a unit term.
This supplies the sign condition needed when transferring the remainder estimate. -/
theorem reciprocalGammaBound_nonneg (f : GeneralLFunction) : 0 ≤ f.reciprocalGammaBound := by
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg _ zero_le_one
  apply tsum_nonneg
  intro n
  exact div_nonneg (by norm_num only) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- For admissible data and cutoff greater than one, the reciprocal gamma residue sum
has norm at most the degree times `(log x + reciprocalGammaTailBound) / x`, with a universal
tail constant. Sum the shift-independent bounds over the finite gamma family.
This controls the gamma remainder uniformly over all admissible data of a fixed degree. -/
theorem norm_reciprocalGammaSum_le_uniform (f : GeneralLFunction) (hf : f.IsAdmissible) {x : ℝ}
    (hx : 1 < x) :
    ‖f.reciprocalGammaSum x‖ ≤
      (f.degree : ℝ) *
        ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x) := by
  unfold reciprocalGammaSum
  apply (norm_sum_le Finset.univ _).trans
  have hb :=
    Finset.sum_le_sum
      (fun (j : Fin f.degree) (_ : j ∈ Finset.univ) ↦
        AnalyticNumberTheory.Gamma.norm_tsum_reciprocalGammaResidue_le_uniform (hf.2.2.2.1 j) hx)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hb

end PseudoPrime.LLS.Extensions.GeneralLFunction
