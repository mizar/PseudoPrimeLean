/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ReciprocalResolventMellin
public import PseudoPrime.LLS.Extensions.ShiftedMellinFormula
public import PseudoPrime.LLS.Extensions.CompletedEndpoint

/-!
# Completed reciprocal formula for general L-functions

Mellin inversion and zero-mass summability evaluate the completed-function integral.
The ordinary arithmetic sum and gamma-factor remainder are separate analytic contributions.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The completed-zero contribution to reciprocal smoothing,
Σρ mρ x^(ρ-1)/(ρ(1-ρ)), represented by its equivalent RH mass-weighted terms.
For positive x under individual RH and summable mass, it converges absolutely and has
norm at most zeroMass/sqrt x. It supplies the oscillatory error in the reciprocal formula. -/
noncomputable def reciprocalZeroSum (f : GeneralLFunction) (x : ℝ) : ℂ :=
  ∑' ρ : f.Zero, (f.zeroMassTerm ρ : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - 1)

/-- For individual RH and x > 0, each mass-weighted reciprocal zero term
has norm x^(-1/2) times its nonnegative mass. Evaluate the complex power norm on the
critical line. This gives the exact majorant used for absolute convergence. -/
theorem norm_reciprocalZeroTerm (f : GeneralLFunction) (hRH : f.RiemannHypothesis) (ρ : f.Zero)
    {x : ℝ} (hx : 0 < x) :
    ‖(f.zeroMassTerm ρ : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - 1)‖ = x ^ (-(1 / 2 : ℝ)) * f.zeroMassTerm ρ := by
  have hm : 0 ≤ f.zeroMassTerm ρ := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re, hRH ρ,
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num only]
  exact mul_comm _ _

/-- Individual RH, summable zero mass and x > 0 imply absolute convergence
of the reciprocal zero series. Dominate its terms by x^(-1/2) times their masses.
This permits summing the scalar Mellin residues. -/
theorem summable_reciprocalZeroTerms (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 0 < x) :
    Summable (fun ρ : f.Zero ↦ (f.zeroMassTerm ρ : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - 1)) := by
  exact
    (hm.mul_left (x ^ (-(1 / 2 : ℝ)))).of_norm_bounded
      (fun ρ ↦ (norm_reciprocalZeroTerm f hRH ρ hx).le)

/-- For individual RH, summable zero mass and x > 0, the reciprocal zero
sum has norm at most zeroMass/sqrt x. Sum the exact norm majorants and apply the
triangle inequality. This supplies the reciprocal formula's bounded real error. -/
theorem norm_reciprocalZeroSum_le (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 0 < x) :
    ‖f.reciprocalZeroSum x‖ ≤ f.zeroMass / Real.sqrt x := by
  have hn : Summable (fun ρ : f.Zero ↦ ‖(f.zeroMassTerm ρ : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - 1)‖) :=
    (hm.mul_left (x ^ (-(1 / 2 : ℝ)))).congr (fun ρ ↦ (norm_reciprocalZeroTerm f hRH ρ hx).symm)
  have hb := norm_tsum_le_tsum_norm hn
  rw [funext (fun ρ ↦ norm_reciprocalZeroTerm f hRH ρ hx), tsum_mul_left, Real.rpow_neg hx.le, ←
    Real.sqrt_eq_rpow] at hb
  simpa only [reciprocalZeroSum, zeroMass, div_eq_mul_inv, mul_comm] using hb

/-- For individual RH, summable zero mass and x > 0, the real reciprocal
zero sum equals θ*zeroMass/sqrt x with |θ| ≤ 1. Normalize the norm bound, treating zero
mass separately. This converts the complex zero sum into a real error coefficient. -/
theorem reciprocalZeroSum_eq_theta (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 0 < x) :
    ∃ θ : ℝ, |θ| ≤ 1 ∧ (f.reciprocalZeroSum x).re = θ / Real.sqrt x * f.zeroMass := by
  let Z := f.reciprocalZeroSum x
  let B := f.zeroMass / Real.sqrt x
  have hM : 0 ≤ f.zeroMass := tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hB : 0 ≤ B := div_nonneg hM (Real.sqrt_nonneg x)
  have hnorm : ‖Z‖ ≤ B := norm_reciprocalZeroSum_le f hRH hm hx
  have habs : |Z.re| ≤ B := (Complex.abs_re_le_norm Z).trans hnorm
  by_cases hB0 : B = 0
  · have hZ : Z = 0 := norm_eq_zero.mp (le_antisymm (hB0 ▸ hnorm) (norm_nonneg _))
    refine ⟨0, by norm_num only [abs_zero, zero_le_one], ?_⟩
    change Z.re = _
    rw [hZ, Complex.zero_re, zero_div, zero_mul]
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    refine ⟨Z.re / B, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hBp]
      exact (div_le_one hBp).mpr habs
    · change Z.re = (Z.re / B) / Real.sqrt x * f.zeroMass
      calc
        Z.re = (Z.re / B) * B := (div_mul_cancel₀ _ hB0).symm
        _ = _ := by
          dsimp only [B]; ring

/-- For an RH completed zero, its multiplicity-weighted reciprocal
resolvent residue equals zeroMassTerm times (1/x-x^(ρ-1)). The endpoint genus-one identity
and nonzero critical-line denominators give the algebra. This identifies the summed residues. -/
theorem reciprocalResolventResidue_eq_mass (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (ρ : f.Zero) (x : ℝ) :
    (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
        (((x : ℂ) ^ ((ρ : ℂ) - 1) - (x : ℂ)⁻¹) / (((ρ : ℂ) - 1) * (((ρ : ℂ) - 1) + 1))) =
      (f.zeroMassTerm ρ : ℂ) * ((x : ℂ)⁻¹ - (x : ℂ) ^ ((ρ : ℂ) - 1)) := by
  have hr := AnalyticNumberTheory.General.zero_ne_of_re_half (hRH ρ)
  have hs : 1 - (ρ : ℂ) ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re, hRH ρ] at he
    norm_num only at he
  have hd : (ρ : ℂ) - 1 ≠ 0 := fun hz ↦ hs (by rw [sub_eq_zero.mp hz, sub_self])
  rw [← genus_one_term_eq_zeroMassTerm f hRH ρ, sub_add_cancel]
  field_simp (disch := simp only [hr, hs, hd, ne_eq, not_false_eq_true])
  ring

/-- For admissible RH data, τ > 0 and x > 1, the normalized reciprocal
zero-resolvent integral is zeroMass/x minus reciprocalZeroSum. Power-mass convergence
justifies termwise Mellin inversion; sum the mass and oscillatory parts separately.
This evaluates the completed-zero contribution without a contour-shift assumption. -/
theorem normalized_integral_reciprocalZeroResolvent_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          ∑' ρ : f.Zero,
            (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
              AnalyticNumberTheory.General.reciprocalResolventKernel ((ρ : ℂ) - 1) x τ y) =
      (f.zeroMass : ℂ) / (x : ℂ) - f.reciprocalZeroSum x := by
  have hm := summable_zeroMassTerm_of_admissible f hf hRH
  have hs : Summable (fun ρ : f.Zero ↦ (f.zeroMassTerm ρ : ℂ)) :=
    (Complex.hasSum_ofReal.mpr hm.hasSum).summable
  have hz := summable_reciprocalZeroTerms f hRH hm (zero_lt_one.trans hx)
  have he :=
    AnalyticNumberTheory.General.normalized_integral_tsum_reciprocalResolventKernel
      (fun ρ : f.Zero ↦ (ρ : ℂ) - 1) (fun ρ ↦ analyticOrderNatAt f.completed (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.one_re, hRH ρ]; norm_num only)
      (fun ρ h ↦ by
        have hh := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, hRH ρ] at hh
        norm_num only at hh)
      hτ hx
      (by
        simpa only [Complex.ofReal_one] using
          (summable_shifted_power_mass_of_admissible f hf hRH (σ := 1) le_rfl
            (show (1 : ℝ) < 3 / 2 by norm_num only)))
  rw [he]
  calc
    _ =
        ∑' ρ : f.Zero,
          ((f.zeroMassTerm ρ : ℂ) * (x : ℂ)⁻¹ - (f.zeroMassTerm ρ : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - 1)) :=
      by
      apply tsum_congr
      intro ρ
      rw [reciprocalResolventResidue_eq_mass f hRH ρ x, mul_sub]
    _ = _ := by
      rw [(hs.mul_right (x : ℂ)⁻¹).tsum_sub hz, tsum_mul_right, ← Complex.ofReal_tsum]
      rfl

/-- The completed logarithmic derivative with reciprocal smoothing,
-ξ'/ξ(1+z)*x^z/(z(z+1)), where z=τ+i y. Under admissibility, RH, τ > 0 and x > 1,
its vertical integral is evaluated by the centered Hadamard expansion and scalar Mellin
inversion. It is the completed-function integral in the generalized reciprocal formula. -/
noncomputable def completedReciprocalMellinIntegrand (f : GeneralLFunction) (x τ y : ℝ) : ℂ :=
  -logDeriv f.completed (1 + ((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
    (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))

/-- For admissible RH data and τ > 0, the completed reciprocal integrand
splits into the endpoint constant and the negative reciprocal zero-resolvent series.
Multiply the centered Hadamard identity by the reciprocal smoothing factor.
This provides an integrable decomposition of the completed-function integral. -/
theorem completedReciprocalMellinIntegrand_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {τ x : ℝ} (hτ : 0 < τ) (y : ℝ) :
    f.completedReciprocalMellinIntegrand x τ y =
      -logDeriv f.completed 1 *
          ((x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) -
        ∑' ρ : f.Zero,
          (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
            AnalyticNumberTheory.General.reciprocalResolventKernel ((ρ : ℂ) - 1) x τ y := by
  have hZ :
    (∑' ρ : f.Zero,
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
          AnalyticNumberTheory.General.reciprocalResolventKernel ((ρ : ℂ) - 1) x τ y) =
      f.zeroResolventMellinIntegrand x 1 τ y *
        (((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)) := by
    simp only [AnalyticNumberTheory.General.reciprocalResolventKernel, ← mul_assoc, tsum_mul_right,
      zeroResolventMellinIntegrand, Complex.ofReal_one]
  have he := zeroResolventMellinIntegrand_eq f hf hRH (σ := 1) (x := x) le_rfl hτ y
  have hz := AnalyticNumberTheory.General.ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y
  have h1 : (τ : ℂ) + y * Complex.I + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re,
      Complex.zero_re] at hh
    linarith only [hh, hτ]
  rw [hZ, he, Complex.ofReal_one]
  unfold completedReciprocalMellinIntegrand
  field_simp (disch := simp only [hz, h1, ne_eq, not_false_eq_true])
  ring

/-- For admissible RH data, τ > 0 and x > 1, the completed reciprocal
Mellin integral equals -ξ'/ξ(1)*(1-1/x)-zeroMass/x+reciprocalZeroSum.
Integrate the endpoint and zero-series decomposition using absolute integrability.
This proves the exact completed-function side of the generalized reciprocal formula. -/
theorem normalized_integral_completedReciprocalMellin_eq (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, f.completedReciprocalMellinIntegrand x τ y) =
      -logDeriv f.completed 1 * (1 - (x : ℂ)⁻¹) -
        ((f.zeroMass : ℂ) / (x : ℂ) - f.reciprocalZeroSum x) := by
  obtain ⟨hG, hGI⟩ := AnalyticNumberTheory.General.reciprocalMellin_integrable_and_integral hτ hx
  have hZ :=
    AnalyticNumberTheory.General.integrable_tsum_reciprocalResolventKernel
      (fun ρ : f.Zero ↦ (ρ : ℂ) - 1) (fun ρ ↦ analyticOrderNatAt f.completed (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.one_re, hRH ρ]; norm_num only)
      hτ (zero_lt_one.trans hx)
      (by
        simpa only [Complex.ofReal_one] using
          (summable_shifted_power_mass_of_admissible f hf hRH (σ := 1) le_rfl
            (show (1 : ℝ) < 3 / 2 by norm_num only)))
  have he := funext (completedReciprocalMellinIntegrand_eq f hf hRH (τ := τ) (x := x) hτ)
  rw [he, MeasureTheory.integral_sub (hG.const_mul (-logDeriv f.completed 1)) hZ, smul_sub,
    MeasureTheory.integral_const_mul, ← mul_smul_comm, hGI,
    normalized_integral_reciprocalZeroResolvent_eq f hf hRH hτ hx]

/-- For admissible RH data, τ > 0 and x > 1, the real completed reciprocal
Mellin integral is -zeroMass/2+(θ/sqrt x-1/(2x))*zeroMass with |θ| ≤ 1.
Use the functional-equation endpoint identity and the reciprocal zero norm bound.
This is the zero-side estimate needed for the generalized smoothed logarithmic derivative. -/
theorem re_integral_completedReciprocalMellin_eq_theta (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        ((2 * Real.pi)⁻¹ • (∫ y : ℝ, f.completedReciprocalMellinIntegrand x τ y)).re =
          -f.zeroMass / 2 + (θ / Real.sqrt x - 1 / (2 * x)) * f.zeroMass := by
  obtain ⟨θ, hθ, hZ⟩ :=
    reciprocalZeroSum_eq_theta f hRH (summable_zeroMassTerm_of_admissible f hf hRH)
      (zero_lt_one.trans hx)
  refine ⟨θ, hθ, ?_⟩
  rw [normalized_integral_completedReciprocalMellin_eq f hf hRH hτ hx]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_div]
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re,
    Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, mul_zero]
  rw [re_logDeriv_completed_one_eq_half_zeroMass f hf hRH, hZ]
  ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
