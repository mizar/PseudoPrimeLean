/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.LLS.Extensions.CompletedReciprocalFormula
public import PseudoPrime.LLS.Extensions.OrdinaryEndpoint
public import PseudoPrime.LLS.Extensions.ReciprocalGammaFormula

/-!
# Deriving the general smoothed logarithmic derivative formula

The arithmetic and completed reciprocal integrals give the exact formula. Summable gamma
residues bound its remainder for each fixed admissible RH function, completing the hypotheses
used by the public reciprocal proposition.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The real remainder in the general reciprocal formula, defined as the completed
Mellin integral minus the arithmetic sum plus the gamma endpoint and zeroMass/x.
The last term reconciles the signs of the real zero coefficient after rearrangement.
For admissible RH data it equals the real gamma residue sum plus the endpoint and zero mass
divided by x. Its fixed-function Big-O bound supplies the error in the public formula. -/
noncomputable def reciprocalRemainder (f : GeneralLFunction) (x : ℝ) : ℝ :=
  ((2 * Real.pi)⁻¹ • (∫ y : ℝ, f.completedReciprocalMellinIntegrand x 1 y)).re -
      (f.reciprocalWeightedSum x).re +
    f.gammaLogDerivativeAtOne +
    f.zeroMass / x

/-- For admissible RH data and x > 1, the ordinary logarithmic derivative equals
the smoothed arithmetic sum, a bounded real zero coefficient, and reciprocalRemainder.
Combine the completed integral evaluation with the ordinary endpoint identity and reverse
the zero coefficient's sign. No asymptotic bound on the remainder is asserted here. -/
theorem reciprocalFormula_eq_theta (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        -(logDeriv f.L 1).re =
          (f.reciprocalWeightedSum x).re + (θ / Real.sqrt x - 1 / (2 * x)) * f.zeroMass +
            f.reciprocalRemainder x := by
  obtain ⟨θ, hθ, hI⟩ := re_integral_completedReciprocalMellin_eq_theta f hf hRH zero_lt_one hx
  refine ⟨-θ, ?_, ?_⟩
  · simpa only [abs_neg] using hθ
  · rw [re_logDeriv_ordinary_one_eq_half_zeroMass_sub_gamma f hf hRH]
    unfold reciprocalRemainder
    rw [hI]
    ring

/-- For admissible RH data and `τ > 0`, the completed reciprocal integrand is the ordinary
integrand minus the completion-factor integrand. Individual RH excludes completed zeros
on this vertical line, so the logarithmic product rule applies. This connects the
arithmetic Mellin formula with the completed zero expansion. -/
theorem completedReciprocalMellinIntegrand_eq_ordinary_sub (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    f.completedReciprocalMellinIntegrand x τ y =
      -logDeriv f.L (((1 + τ : ℝ) : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
          (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) -
        f.completionReciprocalMellinIntegrand x τ y := by
  have hr : (1 + ((τ : ℂ) + y * Complex.I)).re = 1 + τ := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hpos : 0 < (1 + ((τ : ℂ) + y * Complex.I)).re := by
    rw [hr]
    exact add_pos zero_lt_one hτ
  have hne : (1 + ((τ : ℂ) + y * Complex.I)).re ≠ 1 / 2 := by
    rw [hr]
    linarith only [hτ]
  unfold completedReciprocalMellinIntegrand completionReciprocalMellinIntegrand
  rw [logDeriv_completed_eq_completionFactor_add f hf hpos
      (completed_ne_zero_of_re_ne_half hRH hne)]
  simp only [Complex.ofReal_add, Complex.ofReal_one, add_assoc]
  ring

/-- For admissible RH data, `τ > 0` and `x > 1`, the completed reciprocal integral is the
smoothed arithmetic sum minus the completion endpoint contribution, plus the gamma residue
sum. Integrate the ordinary/completion decomposition using absolute integrability and the
two Mellin evaluations. This eliminates the remaining unevaluated vertical integral. -/
theorem normalized_integral_completedReciprocal_eq_arithmetic_sub (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x τ : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, f.completedReciprocalMellinIntegrand x τ y) =
      f.reciprocalWeightedSum x -
        (logDeriv f.completionFactor 1 * (1 - (x : ℂ)⁻¹) - f.reciprocalGammaSum x) := by
  rw [funext (completedReciprocalMellinIntegrand_eq_ordinary_sub f hf hRH (x := x) hτ),
    MeasureTheory.integral_sub (integrable_reciprocalMellin_logDeriv f hf (zero_lt_one.trans hx) hτ)
      (integrable_completionReciprocalMellinIntegrand f hf hτ hx),
    smul_sub, ← reciprocalWeightedSum_eq_integral_logDeriv f hf (zero_lt_one.trans hx) hτ,
    normalized_integral_completionReciprocalMellin_eq f hf hτ hx]

/-- For admissible RH data and `x > 1`, the reciprocal remainder is the gamma residue sum's
real part plus `(gamma endpoint + zero mass)/x`. Substitute the arithmetic/completion
integral formula and take real parts of the real inverse cutoff. This gives an explicit
remainder suitable for asymptotic estimation. -/
theorem reciprocalRemainder_eq_gammaResidues (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    f.reciprocalRemainder x =
      (f.gammaLogDerivativeAtOne + f.zeroMass) / x + (f.reciprocalGammaSum x).re := by
  unfold reciprocalRemainder
  rw [normalized_integral_completedReciprocal_eq_arithmetic_sub f hf hRH zero_lt_one hx]
  have hk : 1 - (x : ℂ)⁻¹ = ((1 - x⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  rw [hk]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, re_logDeriv_completionFactor_one f hf]
  ring

/-- For admissible RH data and `x > 1`, bound the reciprocal remainder norm by a fixed
constant times `(log x + 1)/x`. Combine the gamma residue bound with the endpoint and zero
mass divided by `x`, using `log x ≥ 0`. This supplies the estimate for the full proposition. -/
theorem norm_reciprocalRemainder_le (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.reciprocalRemainder x‖ ≤
      (|f.gammaLogDerivativeAtOne + f.zeroMass| + f.reciprocalGammaBound) *
        ((Real.log x + 1) / x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hw : (1 : ℝ) / x ≤ (Real.log x + 1) / x :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_left (Real.log_pos hx).le) hx0.le
  rw [reciprocalRemainder_eq_gammaResidues f hf hRH hx]
  have hg := (Complex.abs_re_le_norm (f.reciprocalGammaSum x)).trans
    (norm_reciprocalGammaSum_le f hf hx)
  have ha : ‖(f.gammaLogDerivativeAtOne + f.zeroMass) / x‖ ≤
      |f.gammaLogDerivativeAtOne + f.zeroMass| * ((Real.log x + 1) / x) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  have hb := norm_add_le ((f.gammaLogDerivativeAtOne + f.zeroMass) / x)
    (f.reciprocalGammaSum x).re
  have hgr : ‖(f.reciprocalGammaSum x).re‖ ≤
      f.reciprocalGammaBound * ((Real.log x + 1) / x) := by
    simpa only [Real.norm_eq_abs] using hg
  exact (hb.trans (add_le_add ha hgr)).trans_eq (by
    ring
    )

/-- For each fixed admissible RH function, the reciprocal remainder is Big-O of
`(log analyticConductor + degree * log x)/x` as `x` tends to infinity. The positive degree
and an explicit exponential cutoff let this scale dominate `(log x + 1)/x`; transfer the
fixed gamma bound. The Big-O constant may depend on the function, as in `lls_propL2`.
This discharges the last analytic hypothesis of the generalized reciprocal formula. -/
theorem isBigO_reciprocalRemainder (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) :
    Asymptotics.IsBigO Filter.atTop f.reciprocalRemainder
      (fun x : ℝ ↦ (Real.log f.analyticConductor + f.degree * Real.log x) / x) := by
  let A : ℝ := |f.gammaLogDerivativeAtOne + f.zeroMass| + f.reciprocalGammaBound
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (reciprocalGammaBound_nonneg f)
  have hd : (1 : ℝ) ≤ f.degree :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hf.1.ne')
  apply Asymptotics.IsBigO.of_bound (2 * A)
  filter_upwards [Filter.eventually_ge_atTop
    (Real.exp (2 * |Real.log f.analyticConductor| + 2))] with x hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl := Real.log_le_log (Real.exp_pos _) hx
  rw [Real.log_exp] at hl
  have hl0 : 0 < Real.log x := by
    linarith only [hl, abs_nonneg (Real.log f.analyticConductor)]
  have hx1 : 1 < x := (Real.log_pos_iff hx0.le).mp hl0
  have hn : Real.log x + 1 ≤
      2 * (Real.log f.analyticConductor + (f.degree : ℝ) * Real.log x) := by
    nlinarith only [hl, neg_abs_le (Real.log f.analyticConductor),
      mul_nonneg (sub_nonneg.mpr hd) hl0.le]
  have hnum : 0 ≤ Real.log f.analyticConductor + (f.degree : ℝ) * Real.log x := by
    linarith only [hn, hl0]
  have hnorm : ‖(Real.log f.analyticConductor + (f.degree : ℝ) * Real.log x) / x‖ =
      (Real.log f.analyticConductor + (f.degree : ℝ) * Real.log x) / x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hx0.le)]
  rw [hnorm]
  have ht := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hx0.le) hA
  exact (norm_reciprocalRemainder_le f hf hRH hx1).trans
    (ht.trans_eq (by
      dsimp only [A]
      ring
      ))

end PseudoPrime.LLS.Extensions.GeneralLFunction

namespace PseudoPrime.LLS.Extensions

/-- A bound on reciprocalRemainder of the stated Big-O size for every admissible
RH function implies the entire proposition lls_propL2. Zero-mass convergence and the
pointwise exact formula are proved; choose the bounded coefficient as a function of x.
This assembles the exact formula and remainder bound without adding either to admissibility. -/
theorem lls_propL2_of_reciprocalRemainder
    (hR :
      ∀ f : GeneralLFunction,
        f.IsAdmissible →
          f.RiemannHypothesis →
          Asymptotics.IsBigO Filter.atTop f.reciprocalRemainder
            (fun x : ℝ ↦ (Real.log f.analyticConductor + f.degree * Real.log x) / x)) :
    lls_propL2 := by
  intro f hf hRH
  have ht :
    ∀ x : ℝ,
      ∃ θ : ℝ,
        2 ≤ x →
          |θ| ≤ 1 ∧
            -(logDeriv f.L 1).re =
              (f.reciprocalWeightedSum x).re + (θ / Real.sqrt x - 1 / (2 * x)) * f.zeroMass +
                f.reciprocalRemainder x := by
    intro x
    by_cases hx : 2 ≤ x
    · obtain ⟨θ, hθ, he⟩ :=
        GeneralLFunction.reciprocalFormula_eq_theta f hf hRH
          (lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx)
      exact ⟨θ, fun _ ↦ ⟨hθ, he⟩⟩
    · exact ⟨0, fun h ↦ (hx h).elim⟩
  choose θ hθ using ht
  exact
    ⟨GeneralLFunction.summable_zeroMassTerm_of_admissible f hf hRH, θ, f.reciprocalRemainder, hθ,
      hR f hf hRH⟩

end PseudoPrime.LLS.Extensions
