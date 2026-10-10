/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedZeroBounds
public import PseudoPrime.LLS.Extensions.PaperDefinitions

/-!
# Integrated zero contribution for general L-functions

The completed-zero mass controls the shifted residue sum under individual RH.
This proves integrability, termwise integration, and the logarithmic zero-error bound;
it does not assume or establish the full explicit formula.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For general data and real `x, σ`, define the completed-zero sum with actual analytic
multiplicity and term `-m * x^(ρ - σ)/(ρ - σ)^2`. Complex powers, division and the sum
are totalized. Individual RH and summable zero mass imply absolute convergence when
`x > 0` and `σ ≥ 1`. The sum is the zero-side residue contribution before shift integration. -/
noncomputable def shiftedZeroSum (f : GeneralLFunction) (x σ : ℝ) : ℂ :=
  ∑' ρ : f.Zero,
    -(analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
      ((ρ : ℂ) - (σ : ℂ)) ^ 2

/-- For individual RH, summable zero mass, positive x and sigma>=1, the shifted zero series
converges absolutely. Apply the critical-line inverse-square mass majorant. -/
theorem summable_shiftedZeroSum (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x σ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) :
    Summable
      (fun ρ : f.Zero ↦
        -(analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
          ((ρ : ℂ) - (σ : ℂ)) ^ 2) := by
  exact
    AnalyticNumberTheory.General.summable_shifted_zero_residues (fun ρ : f.Zero ↦ (ρ : ℂ))
      (fun ρ ↦ analyticOrderNatAt f.completed (ρ : ℂ)) hRH hσ hx hm

/-- For individual RH, summable zero mass and x>1, the shifted zero sum is integrable over
sigma>1. The general measurable mass-majorant theorem proves integrability. -/
theorem integrableOn_shiftedZeroSum (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 1 < x) :
    MeasureTheory.IntegrableOn (f.shiftedZeroSum x) (Set.Ioi 1) := by
  exact
    AnalyticNumberTheory.General.integrableOn_shifted_zero_sum (fun ρ : f.Zero ↦ (ρ : ℂ))
      (fun ρ ↦ analyticOrderNatAt f.completed (ρ : ℂ)) hRH hx hm

/-- For individual RH, summable zero mass and x>1, the integrated zero sum divided by log x
has norm at most zeroMass/(sqrt x*(log x) ^ 2). Integrate the critical-line majorant and
normalize by log x. This is the zero-error estimate required by the generalized Lemma 2.5. -/
theorem norm_integrated_shiftedZeroSum_div_log_le (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 1 < x) :
    ‖(∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) / (Real.log x : ℂ)‖ ≤
      f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2) := by
  have hb :=
    AnalyticNumberTheory.General.norm_integral_shifted_zero_residues_le (fun ρ : f.Zero ↦ (ρ : ℂ))
      (fun ρ ↦ analyticOrderNatAt f.completed (ρ : ℂ)) hRH hx hm
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  calc
    _ ≤ (x ^ (-(1 / 2 : ℝ)) / Real.log x * f.zeroMass) / Real.log x :=
      div_le_div_of_nonneg_right hb hlog.le
    _ = _ := by
      rw [Real.rpow_neg (zero_lt_one.trans hx).le, ← Real.sqrt_eq_rpow]
      ring

/-- For individual RH, summable zero mass and x>1, shift integration commutes with the sum
over completed zeros. Absolute-integral bounds justify exchanging the two operations.
This supports evaluation of the generalized logarithmic explicit formula's zero term. -/
theorem integral_shiftedZeroSum_eq_tsum (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) =
      ∑' ρ : f.Zero,
        ∫ σ : ℝ in Set.Ioi 1,
          -(analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2 := by
  exact
    AnalyticNumberTheory.General.integral_tsum_shifted_zero_residues (fun ρ : f.Zero ↦ (ρ : ℂ))
      (fun ρ ↦ analyticOrderNatAt f.completed (ρ : ℂ)) hRH hx hm

/-- For individual RH, summable zero mass and `x > 1`, the real part of the integrated
zero sum divided by `log x` equals `θ * zeroMass / (sqrt x * (log x)^2)`, with `|θ| ≤ 1`.
Bound the complex norm and normalize its real part; if the bound is zero, the integral
vanishes. This supplies the real zero-error coefficient in generalized Lemma 2.5. -/
theorem integrated_shiftedZeroSum_eq_theta (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (hm : Summable f.zeroMassTerm) {x : ℝ} (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        ((∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) / (Real.log x : ℂ)).re =
          θ / (Real.sqrt x * (Real.log x) ^ 2) * f.zeroMass := by
  let Z : ℂ := (∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) / (Real.log x : ℂ)
  let B : ℝ := f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2)
  have hM : 0 ≤ f.zeroMass := tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hB : 0 ≤ B := div_nonneg hM (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))
  have hnorm : ‖Z‖ ≤ B := norm_integrated_shiftedZeroSum_div_log_le f hRH hm hx
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
    · change Z.re = (Z.re / B) / (Real.sqrt x * (Real.log x) ^ 2) * f.zeroMass
      calc
        Z.re = (Z.re / B) * B := (div_mul_cancel₀ _ hB0).symm
        _ = _ := by
          dsimp only [B]; ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
