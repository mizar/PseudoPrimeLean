/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnconditionalZeroSumBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePrincipalAbel

/-! # Pointwise bounds for the anchored log-weighted error -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH the absolute nontrivial log-weighted zero contributions are
bounded by the square root of the argument times the inverse-square mass. -/
private theorem log_zero_term_le_sqrt (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t) (ρ : ℂ) :
    ‖AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ‖ ≤
      Real.sqrt t * AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2 ρ := by
  rw [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm]
  split
  next h =>
    have hs := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg h.1 h.2
    rw [AnalyticNumberTheory.RiemannZeta.norm_logZeroContribution (zero_lt_one.trans_le ht),
      AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hs, ←
      Real.sqrt_eq_rpow, mul_div_assoc,
      AnalyticNumberTheory.RiemannZeta.nontrivial_inverse_square_eq_weight h.1 h.2]
  next h =>
    rw [norm_zero]
    exact
      mul_nonneg (Real.sqrt_nonneg _)
        (AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight_nonneg _ _)

/-- The global critical-line mass gives a bound of one twentieth times the
square root for the nontrivial part of the log-weighted explicit formula. -/
theorem log_zero_sum_le_sqrt (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t) :
    ‖∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ‖ ≤ Real.sqrt t / 20 := by
  let m := AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2
  have hm : Summable m :=
    AnalyticNumberTheory.RiemannXi.summable_inversePowerZeroWeight (by norm_num only)
  have hS := (AnalyticNumberTheory.RiemannZeta.summable_nontrivialLogZeroTerm ht).norm
  have h := hS.tsum_le_tsum (log_zero_term_le_sqrt hRH ht) (hm.mul_left (Real.sqrt t))
  rw [hm.tsum_mul_left] at h
  have hmass : (∑' ρ, m ρ) ≤ 1 / 20 := by
    have he : (∑' ρ, m ρ) = 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass := by
      simpa only [m, AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight, Real.rpow_two,
        Complex.normSq_eq_norm_sq] using
        AnalyticNumberTheory.RiemannXi.tsum_multiplicityInvSq_eq_two_mass_RH hRH
    rw [he]
    linarith only [AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth]
  exact
    ((norm_tsum_le_tsum_norm hS).trans h).trans
      ((mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg t)).trans_eq (by ring))

/-- The fixed trivial-zero endpoint is a quarter of the Basel sum. -/
private theorem log_trivial_at_one :
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries 1 = Real.pi ^ 2 / 24 := by
  have hsum : (∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two.summable.tsum_eq_zero_add
    simp only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), div_zero, zero_add, Nat.cast_add,
      Nat.cast_one] at h
    exact h.symm.trans hasSum_zeta_two.tsum_eq
  simp only [AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries, inv_one, one_pow]
  calc
    _ = ∑' k : ℕ, ((1 : ℝ) / ((k : ℝ) + 1) ^ 2) * (1 / 4) := by
      apply tsum_congr
      intro k
      simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    _ = _ := by
      rw [tsum_mul_right, hsum]; ring

/-- The anchored log-weighted Chebyshev error under RH has a square-root term
from the nontrivial zeros and a constant term from anchoring and trivial zeros. -/
theorem anchored_log_error_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t) +
          1| ≤
      Real.sqrt t / 20 + 43 / 60 := by
  rw [middle_anchored_explicit ht]
  rcases eq_or_lt_of_le ht with rfl | ht'
  · norm_num only [sub_self, abs_zero, Real.sqrt_one]
  have hZ := (Complex.abs_re_le_norm _).trans (log_zero_sum_le_sqrt hRH ht)
  have h1 := (Complex.abs_re_le_norm _).trans (log_zero_sum_le_sqrt hRH (le_refl (1 : ℝ)))
  rw [Real.sqrt_one] at h1
  have hT := AnalyticNumberTheory.RiemannZeta.logTrivialSeries_le_pi_sq_div_24 ht'
  have hT₀ := AnalyticNumberTheory.RiemannZeta.triv_nonneg ht'
  have hT₁ : Real.pi ^ 2 / 24 ≤ 2 / 3 := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
    linarith only [h]
  rw [log_trivial_at_one]
  have hA :=
    abs_sub_le ((∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) 0
      ((∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm 1 ρ).re)
  refine (abs_sub_le _ 0 _).trans ?_
  simp only [sub_zero, zero_sub, abs_neg] at hA ⊢
  rw [abs_of_nonpos (sub_nonpos.mpr hT)]
  linarith only [hA, hZ, h1, hT₀, hT₁]

/-- A coarser square-root bound applies even at the lower endpoint. -/
theorem anchored_log_error_le_sqrt (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t) +
          1| ≤
      Real.sqrt t := by
  have hs : 1 ≤ Real.sqrt t := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht
  linarith only [anchored_log_error_le hRH ht, hs]

/-- Above one million the fixed anchoring cost fits the difference between
the coefficients one twentieth and fifty-one thousandths. -/
theorem anchored_log_error_le_large (hRH : RiemannHypothesis) {t : ℝ} (ht : 10 ^ 6 ≤ t) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t) +
          1| ≤
      51 / 1000 * Real.sqrt t := by
  have h :=
    Real.sqrt_le_sqrt
      (show (1000 : ℝ) ^ 2 ≤ t from (by norm_num only : (1000 : ℝ) ^ 2 ≤ 10 ^ 6).trans ht)
  rw [Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 1000)] at h
  have ht₁ : 1 ≤ t := (by norm_num only : (1 : ℝ) ≤ 10 ^ 6).trans ht
  linarith only [anchored_log_error_le hRH ht₁, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
