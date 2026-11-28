/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnconditionalZeroSumBounds
import all PseudoPrime.AnalyticNumberTheory.RiemannXi.InversePowerZeroMass
import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2
import PseudoPrime.LLS.RiemannWeightedErrorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

/-! # Bounds for the centered logarithmic explicit formula -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Critical-line location gives the exact square-root scaling of the norm of each
nontrivial ζ term, even below one. -/
private theorem norm_log_zero_term_rh (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x ρ‖ =
      Real.sqrt x * AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2 ρ := by
  by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · have hz := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg h.1 h.2
    rw [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_left h,
      AnalyticNumberTheory.RiemannZeta.norm_logZeroContribution hx,
      AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hz,
      Real.sqrt_eq_rpow, mul_div_assoc,
      AnalyticNumberTheory.RiemannZeta.nontrivial_inverse_square_eq_weight h.1 h.2]
  · have hz : AnalyticNumberTheory.RiemannXi.riemannXi ρ ≠ 0 := by
      intro hz
      exact
        h
          ⟨AnalyticNumberTheory.RiemannXi.riemannZeta_zero_of_riemannXi_zero hz,
            AnalyticNumberTheory.RiemannXi.riemannXi_zero_re_nonneg hz⟩
    rw [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_right h, norm_zero,
      AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight, ite_eq_right hz, mul_zero]

/-- The logarithmic zero sum is absolutely convergent on the whole positive half-line. -/
public theorem gaussian_log_zero_summable (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    Summable (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x) := by
  apply
    Summable.of_norm_bounded
      ((AnalyticNumberTheory.RiemannXi.summable_inversePowerZeroWeight
            (by norm_num only : (1 : ℝ) < 2)).mul_left
        (Real.sqrt x))
  exact fun ρ ↦ (norm_log_zero_term_rh hRH hx ρ).le

/-- The real logarithmic zero sum is bounded by `231 sqrt(x) / 5000` on RH. -/
public theorem gaussian_log_zero_abs_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    |(∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x ρ).re| ≤
      231 / 5000 * Real.sqrt x := by
  have h := norm_tsum_le_tsum_norm (gaussian_log_zero_summable hRH hx).norm
  simp only [norm_log_zero_term_rh hRH hx, tsum_mul_left] at h
  have hm :
    (∑' ρ : ℂ, AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2 ρ) =
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass := by
    simpa only [AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight, Real.rpow_two,
      Complex.normSq_eq_norm_sq] using
      AnalyticNumberTheory.RiemannXi.tsum_multiplicityInvSq_eq_two_mass_RH hRH
  rw [hm] at h
  exact
    (Complex.abs_re_le_norm _).trans
      (h.trans
        (by
          have hm' :=
            mul_le_mul_of_nonneg_left
              AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000 (Real.sqrt_nonneg x)
          linarith only [hm']))

/-- The trivial zero series at one is the Basel sum scaled by one quarter. -/
private theorem trivial_log_series_one :
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries 1 = Real.pi ^ 2 / 24 := by
  unfold AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  simp only [inv_one, one_pow,
    show
        (fun k : ℕ ↦ (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2)) =
          (fun k : ℕ ↦ (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2))
        by
        funext k
        simp only [one_div, mul_inv_rev, mul_comm],
    tsum_mul_left, LLS.tsum_shifted_basel_eq]
  ring

/-- The trivial zero remainder is nonnegative and decays quadratically above one. -/
public theorem gaussian_trivial_log_bound {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x ∧
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x ≤
        (5 / 12 : ℝ) * x⁻¹ ^ 2 := by
  have hpi : Real.pi ^ 2 / 24 ≤ (5 / 12 : ℝ) := by
    nlinarith only [Real.pi_lt_d4,
      mul_nonneg (sub_nonneg.mpr Real.pi_lt_d4.le)
        (add_nonneg Real.pi_pos.le (by norm_num only : (0 : ℝ) ≤ 3.1416))]
  rcases hx.eq_or_lt with he | hlt
  · subst x
    rw [trivial_log_series_one, inv_one, one_pow, mul_one]
    exact ⟨div_nonneg (sq_nonneg _) (by norm_num only), hpi⟩
  · exact
      ⟨AnalyticNumberTheory.RiemannZeta.triv_nonneg hlt,
        (AnalyticNumberTheory.RiemannZeta.triv_decay hlt).trans
          ((mul_le_mul_of_nonneg_left hpi (sq_nonneg _)).trans_eq (mul_comm _ _))⟩

/-- The constant subtracted in the centered logarithmic explicit formula. -/
@[expose]
public noncomputable def gaussianLogZetaConstant : ℝ :=
  AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re

/-- The logarithmic explicit formula at one bounds its constant on RH. -/
public theorem gaussian_log_zeta_constant_bounds (hRH : RiemannHypothesis) :
    0 < gaussianLogZetaConstant ∧ gaussianLogZetaConstant < 16 / 25 := by
  have h := AnalyticNumberTheory.RiemannZeta.log_weighted_exact_one
  rw [LLS.logWeightedMangoldtSum_eq_zero_of_le_one le_rfl, Real.log_one, mul_zero, sub_zero,
    trivial_log_series_one] at h
  have hz := abs_le.mp (gaussian_log_zero_abs_le hRH zero_lt_one)
  rw [Real.sqrt_one, mul_one] at hz
  have hpi := Real.pi_gt_d2
  have hl : (49 / 5 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hpi.le)
        (add_nonneg Real.pi_pos.le (by norm_num only : (0 : ℝ) ≤ 3.14))]
  have hu : Real.pi ^ 2 / 24 ≤ (5 / 12 : ℝ) := by
    have hh := (gaussian_trivial_log_bound (x := 1) le_rfl).2
    simpa only [trivial_log_series_one, inv_one, one_pow, mul_one] using hh
  unfold gaussianLogZetaConstant
  exact ⟨by linarith only [h, hz.1, hu], by linarith only [h, hz.2, hl]⟩

/-- The centered remainder `G` after subtracting the full logarithmic zero sum. -/
@[expose]
public noncomputable def gaussianLogZetaRemainder (x : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x +
      Real.log (2 * Real.pi) * Real.log (max 1 x) +
      gaussianLogZetaConstant -
    (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x ρ).re

/-- Above and at one the centered remainder is exactly the negated trivial zero series. -/
public theorem gaussian_log_remainder_eq {x : ℝ} (hx : 1 ≤ x) :
    gaussianLogZetaRemainder x =
      -AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x := by
  have h :=
    hx.eq_or_lt.elim (fun e ↦ e ▸ AnalyticNumberTheory.RiemannZeta.log_weighted_exact_one)
      AnalyticNumberTheory.RiemannZeta.log_weighted_exact
  rw [gaussianLogZetaRemainder, max_eq_right hx, gaussianLogZetaConstant]
  linarith only [h]

/-- The small-argument bound of H22 uses only the mass bound and the logarithmic constant. -/
public theorem gaussian_log_remainder_small (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hx₁ : x ≤ 1) : |gaussianLogZetaRemainder x| < 17 / 10 := by
  rw [gaussianLogZetaRemainder, max_eq_left hx₁, Real.log_one, mul_zero, add_zero,
    LLS.logWeightedMangoldtSum_eq_zero_of_le_one hx₁, zero_sub]
  have hz := abs_le.mp (gaussian_log_zero_abs_le hRH hx)
  have hs : Real.sqrt x ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx₁
  have h0 := gaussian_log_zeta_constant_bounds hRH
  exact abs_lt.mpr ⟨by linarith only [hz.2, hs, h0.1, hx₁], by linarith only [hz.1, hs, h0.2, hx]⟩

/-- The large-argument bound of H22 is quadratic decay of the trivial-zero series. -/
public theorem gaussian_log_remainder_large {x : ℝ} (hx : 1 ≤ x) :
    |gaussianLogZetaRemainder x| ≤ (5 / 12 : ℝ) * x⁻¹ ^ 2 := by
  obtain ⟨hn, hu⟩ := gaussian_trivial_log_bound hx
  rw [gaussian_log_remainder_eq hx, abs_neg, abs_of_nonneg hn]
  exact hu

/-- Each nontrivial logarithmic zero term is continuous at zero on RH. -/
public theorem gaussian_log_term_continuous (hRH : RiemannHypothesis) (ρ : ℂ) :
    Continuous (fun t : ℝ ↦ AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ) := by
  by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · have hz := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg h.1 h.2
    have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hz
    rw [continuous_iff_continuousAt]
    intro t
    simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, h,
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution]
    exact
      ((Complex.continuousAt_ofReal_cpow_const t ρ
                (Or.inl (hr.symm ▸ (by norm_num only : (0 : ℝ) < 1 / 2)))).const_mul
            _).div_const
        _
  · simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, h, ↓reduceIte]
    exact continuous_const

/-- The RH norm formula extends to the endpoint zero, where the term vanishes. -/
public theorem gaussian_log_term_norm (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) (ρ : ℂ) :
    ‖AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ‖ =
      Real.sqrt t * AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2 ρ := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [Real.sqrt_zero, zero_mul]
    by_cases hρ : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
    · have hz := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hρ.1 hρ.2
      have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hz
      have hn : ρ ≠ 0 := by
        intro he
        rw [he, Complex.zero_re] at hr
        norm_num only at hr
      rw [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_left hρ]
      simp only [AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution,
        Complex.ofReal_zero, Complex.zero_cpow hn, mul_zero, zero_div, norm_zero]
    · rw [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_right hρ, norm_zero]
  · exact norm_log_zero_term_rh hRH h ρ

/-- The logarithmic zero sum extends continuously to zero on RH.
The uniform majorant on the closed interval uses the square root of its right endpoint. -/
public theorem gaussian_log_zero_continuous (hRH : RiemannHypothesis) {b : ℝ} :
    ContinuousOn
      (fun x : ℝ ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x ρ).re)
      (Set.Icc 0 b) := by
  apply Complex.continuous_re.comp_continuousOn
  have hs :=
    (AnalyticNumberTheory.RiemannXi.summable_inversePowerZeroWeight
          (by norm_num only : (1 : ℝ) < 2)).mul_left
      (Real.sqrt b)
  refine continuousOn_tsum (fun ρ ↦ (gaussian_log_term_continuous hRH ρ).continuousOn) hs ?_
  intro ρ t ht
  rw [gaussian_log_term_norm hRH ht.1]
  exact
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2)
      (AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight_nonneg 2 ρ)

/-- The clipped logarithmic Mangoldt discrepancy used in H21. -/
@[expose]
public noncomputable def gaussianLogZetaError (x : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x +
    Real.log (2 * Real.pi) * Real.log (max 1 x)

/-- The real sum of the nontrivial logarithmic ζ terms. -/
@[expose]
public noncomputable def gaussianLogZetaZeroSum (x : ℝ) : ℝ :=
  (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x ρ).re

/-- The centered remainder retains the zero sum and the constant exactly. -/
public theorem gaussian_log_error_split (x : ℝ) :
    gaussianLogZetaError x =
      gaussianLogZetaZeroSum x + gaussianLogZetaRemainder x - gaussianLogZetaConstant := by
  unfold gaussianLogZetaError gaussianLogZetaZeroSum gaussianLogZetaRemainder
  ring

/-- The clipped arithmetic discrepancy is continuous on each compact interval
with left endpoint zero, also after scaling by a positive cutoff. -/
public theorem gaussian_log_error_continuous {X : ℝ} (hX : 0 < X) (y : ℝ) :
    ContinuousOn (fun u ↦ gaussianLogZetaError (X * u)) (Set.Icc 0 y) := by
  have hx : Continuous (fun u : ℝ ↦ X * u) := continuous_const.mul continuous_id
  have hm : Continuous (fun u : ℝ ↦ max 1 (X * u)) := continuous_const.max hx
  have hl : Continuous (fun u : ℝ ↦ Real.log (max 1 (X * u))) :=
    hm.log (fun _ ↦ ne_of_gt (zero_lt_one.trans_le (le_max_left _ _)))
  exact
    ((AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hX y).sub
          hx.continuousOn).add
      (hl.const_mul _).continuousOn

/-- The scaled zero sum is continuous on any compact interval with left endpoint zero. -/
public theorem gaussian_log_zero_scaled_continuous (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (y : ℝ) : ContinuousOn (fun u ↦ gaussianLogZetaZeroSum (X * u)) (Set.Icc 0 y) := by
  have hx : Continuous (fun u : ℝ ↦ X * u) := continuous_const.mul continuous_id
  exact
    (gaussian_log_zero_continuous hRH (b := X * y)).comp hx.continuousOn
      (fun u hu ↦ ⟨mul_nonneg hX.le hu.1, mul_le_mul_of_nonneg_left hu.2 hX.le⟩)

/-- The scaled remainder is continuous down to the left endpoint of the principal integral. -/
public theorem gaussian_log_remainder_continuous (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (y : ℝ) : ContinuousOn (fun u ↦ gaussianLogZetaRemainder (X * u)) (Set.Icc 0 y) := by
  have hc : ContinuousOn (fun _ : ℝ ↦ gaussianLogZetaConstant) (Set.Icc 0 y) := continuousOn_const
  refine
    (((gaussian_log_error_continuous hX y).add hc).sub
          (gaussian_log_zero_scaled_continuous hRH hX y)).congr
      ?_
  intro u _
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
