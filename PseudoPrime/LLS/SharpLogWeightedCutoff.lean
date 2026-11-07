/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialAbsoluteVariation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.LLS.PaperStatements.GammaTruncatedBounds
public import PseudoPrime.LLS.JointRampPrincipalBounds
public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.LLS.LogShiftRampPrincipalBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2

/-! # Uniform sharp weighted Mangoldt error -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, the logarithmically weighted Mangoldt error is uniformly bounded
on the interval from zero to a cutoff at least one. The explicit formula, the
sharper zero-mass constant, and the trivial-zero tail give the stated budget.
This is the arithmetic input for finite double Abel summation. -/
theorem sharp_log_error_cutoff (hRH : RiemannHypothesis) {t X : ℝ} (ht : 0 ≤ t) (hX : 1 ≤ X)
    (htX : t ≤ X) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤
      (231 / 5000 : ℝ) * Real.sqrt X + (1839 / 1000 : ℝ) * Real.log X + 2 := by
  by_cases hlarge : 1 < t
  · have he := abs_le.mp (abs_logWeightedMangoldtSum_error_le hRH hlarge)
    have hm :=
      mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
        (add_nonneg (Real.sqrt_nonneg t) zero_le_one)
    have hz : 0 ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t := by
      apply tsum_nonneg
      intro k
      exact
        div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hlarge).le) _)
          (mul_nonneg (by norm_num only) (sq_nonneg _))
    have hb := AnalyticNumberTheory.RiemannZeta.logTrivialSeries_le_pi_sq_div_24 hlarge
    have hl := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le (Real.log_pos hlarge).le
    have hl0 : 0 ≤ Real.log (2 * Real.pi) * Real.log t :=
      mul_nonneg (le_trans (by norm_num only : (0 : ℝ) ≤ 1837 / 1000) Analysis.log_two_mul_pi_gt.le)
        (Real.log_pos hlarge).le
    have hs := Real.sqrt_le_sqrt htX
    have hlog := Real.log_le_log (zero_lt_one.trans hlarge) htX
    have hlogX := Real.log_nonneg hX
    rw [abs_le]
    constructor
    · nlinarith only [he.1, hm, hb, hl, hs, hlog, Real.pi_lt_four, Real.pi_pos,
        sq_nonneg (Real.pi - 4)]
    · nlinarith only [he.2, hm, hz, hl0, hs, hlogX, Real.pi_lt_four, Real.pi_pos,
        sq_nonneg (Real.pi - 4)]
  · have hsmall := le_of_not_gt hlarge
    rw [logWeightedMangoldtSum_eq_zero_of_le_one hsmall, zero_sub, abs_neg, abs_of_nonneg ht]
    have hl : 0 ≤ Real.log X := Real.log_nonneg hX
    have hs : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    nlinarith only [hsmall, hl, hs]

/-- The finite double-Abel error integral is bounded uniformly by twice the
cutoff error budget times `exp(-1)`. This retains the exact absolute variation
of the exponential kernel and prepares the Gaussian averaging step. -/
theorem sharp_log_error_variation (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxy : 1 ≤ x * y) :
    |∫ u in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            ((u - 1) * Real.exp (-u))| ≤
      2 * ((231 / 5000 : ℝ) * Real.sqrt (x * y) + (1839 / 1000 : ℝ) * Real.log (x * y) + 2) *
        Real.exp (-1) := by
  let E : ℝ := (231 / 5000 : ℝ) * Real.sqrt (x * y) + (1839 / 1000 : ℝ) * Real.log (x * y) + 2
  let f : ℝ → ℝ := fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u
  have hE : 0 ≤ E := by
    dsimp only [E]
    nlinarith only [Real.sqrt_nonneg (x * y), Real.log_nonneg hxy]
  have hf : ContinuousOn f (Set.uIcc 0 y) := by
    rw [Set.uIcc_of_le hy]
    exact
      (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y).sub
        (continuous_const.mul continuous_id).continuousOn
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hg : Continuous (fun u : ℝ ↦ (E + 0 * u) * |u - 1| * Real.exp (-u)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).mul
          (continuous_id.sub continuous_const).abs).mul
      (Real.continuous_exp.comp continuous_id.neg)
  have hn :=
    intervalIntegral.norm_integral_le_integral_norm (f := fun u ↦ f u * ((u - 1) * Real.exp (-u)))
      (μ := MeasureTheory.volume) hy
  simp only [Real.norm_eq_abs] at hn
  have hm :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy
      ((hf.mul hQ.continuousOn).abs.intervalIntegrable) (hg.intervalIntegrable 0 y)
      (fun u hu ↦
        show |f u * ((u - 1) * Real.exp (-u))| ≤ (E + 0 * u) * |u - 1| * Real.exp (-u) from by
          have hu0 : 0 ≤ x * u := mul_nonneg hx.le hu.1
          have huy : x * u ≤ x * y := mul_le_mul_of_nonneg_left hu.2 hx.le
          have h := sharp_log_error_cutoff hRH hu0 hxy huy
          change |f u| ≤ E at h
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          simpa only [zero_mul, add_zero, mul_assoc] using
            mul_le_mul_of_nonneg_right h (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
  have hv :=
    Analysis.integral_affine_abs_exponential_variation_le (a := E) (b := 0) hE (le_refl (0 : ℝ)) hy
  change |∫ u in (0 : ℝ)..y, f u * ((u - 1) * Real.exp (-u))| ≤ 2 * E * Real.exp (-1)
  exact hn.trans (hm.trans (by simpa only [mul_zero, add_zero, sub_zero] using hv))

/-- Under RH, finite exponential Mangoldt sums admit a lower bound with the
Chebyshev deficit only at the cutoff. Double Abel summation and the sharp
uniform error bound retain the exact exponential variation cost. -/
theorem exponential_mangoldt_lower_sharp (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x)
    (hy : 0 ≤ y) (hxy : 1 ≤ x * y) :
    x * (1 - Real.exp (-y)) - Real.exp (-y) * (x * y - Chebyshev.psi (x * y)) -
        ((231 / 5000 : ℝ) * Real.sqrt (x * y) + (1839 / 1000 : ℝ) * Real.log (x * y) + 2) *
          (y * Real.exp (-y) + 2 * Real.exp (-1)) ≤
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) := by
  have he := AnalyticNumberTheory.Arithmetic.expMangoldtSum_eq_logWeighted_integral hx hy
  rw [logWeighted_exp_integral_eq_main_error hx hy] at he
  have hi := (abs_le.mp (sharp_log_error_variation hRH hx hy hxy)).1
  have hw := (abs_le.mp (sharp_log_error_cutoff hRH (mul_nonneg hx.le hy) hxy le_rfl)).1
  have hp := mul_nonneg hy (Real.exp_pos (-y)).le
  have hm := mul_le_mul_of_nonneg_left hw hp
  nlinarith only [he, hi, hm]

/-- The sharp finite exponential estimate in the actual level-one Gamma
kernel normalization. The cutoff remains `x * y`, ready for Gaussian averaging
with a fixed arithmetic cutoff. -/
theorem gamma_level_one_lower_sharp (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxy : 1 ≤ x * y) :
    (x * (1 - Real.exp (-y)) - Real.exp (-y) * (x * y - Chebyshev.psi (x * y)) -
          ((231 / 5000 : ℝ) * Real.sqrt (x * y) + (1839 / 1000 : ℝ) * Real.log (x * y) + 2) *
            (y * Real.exp (-y) + 2 * Real.exp (-1))) /
        Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        (PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  rw [PaperStatements.gamma_level_one_sum_eq_exponential hx]
  exact
    div_le_div_of_nonneg_right (exponential_mangoldt_lower_sharp hRH hx hy hxy) (Real.sqrt_nonneg x)

end PseudoPrime.LLS
