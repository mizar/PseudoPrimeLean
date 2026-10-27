/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TruncatedDirichletBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds

/-! # Explicit von Mangoldt Euler bounds from finite Dirichlet prefixes and tails -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The truncated logarithmic numerator divided by the positive truncated power
denominator at real gap r and natural cutoff N. Operations are totalized.
For r>0,N>=3 this is an unconditional upper bound for the Mangoldt Dirichlet series
at exponent 1+r, preserving both finite prefixes and explicit integral tails. -/
noncomputable def truncatedEulerUpper (r : ℝ) (N : ℕ) : ℝ :=
  Analysis.truncatedLogDirichletUpper r N / Analysis.truncatedPowerDirichletLower r N

/-- For positive r and any natural cutoff, the explicit truncated Euler ratio is
nonnegative. Combine the nonnegative numerator and positive denominator.
This supplies a reusable scalar cap independently of character or GRH assumptions. -/
theorem truncatedEulerUpper_nonneg {r : ℝ} (hr : 0 < r) (N : ℕ) : 0 ≤ truncatedEulerUpper r N := by
  exact
    div_nonneg (Analysis.truncatedLogDirichletUpper_nonneg hr N)
      (Analysis.truncatedPowerDirichletLower_pos hr N).le

/-- For r>0 and cutoff N>=3, bound the full Mangoldt Dirichlet series at 1+r by
the explicit truncated Euler ratio. Use the exact logarithmic-to-power series ratio,
then substitute the finite-prefix numerator upper bound and denominator lower bound.
This certifies the previously exploratory arbitrary-cutoff analytic formula. -/
theorem tsum_vonMangoldt_le_truncatedEuler {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ truncatedEulerUpper r N := by
  have hs : 1 < 1 + r := by linarith only [hr]
  rw [tsum_vonMangoldt_eq_log_ratio hs]
  have hp : -(1 + r) = -r - 1 := by ring
  have hd : (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + r)) = ∑' n : ℕ, (n : ℝ) ^ (-r - 1) := by
    apply tsum_congr
    intro n
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n), hp]
  have hn :
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ (1 + r)) = ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-r - 1) := by
    apply tsum_congr
    intro n
    rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n), hp]
  rw [hd, hn]
  have hB := Analysis.truncatedPowerDirichletLower_pos hr N
  have hD := Analysis.truncatedPowerDirichletLower_le_tsum hr N
  have hA := Analysis.tsum_logPower_le_truncated hr hN
  exact
    (div_le_div_of_nonneg_right hA (hB.le.trans hD)).trans
      (div_le_div_of_nonneg_left (Analysis.truncatedLogDirichletUpper_nonneg hr N) hB hD)

/-- For 1<sigma<=tau, the Mangoldt Dirichlet series at tau is at most its value at sigma.
Compare positive real powers termwise and sum using absolute convergence.
This supports interval bounds without re-evaluating each real exponent. -/
theorem tsum_vonMangoldt_div_rpow_antitone {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ) ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  refine
    Summable.tsum_le_tsum (fun n ↦ ?_) (summable_vonMangoldt_div_rpow (hσ.trans_le hστ))
      (summable_vonMangoldt_div_rpow hσ)
  by_cases hn : n = 0
  · simp only [hn, ArithmeticFunction.map_zero, zero_div, le_refl]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact
      div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_pos_of_pos hn0 σ)
        (Real.rpow_le_rpow_of_exponent_le hn1 hστ)

/-- For r>0, exponent sigma>=1+r and cutoff N>=3, the truncated cap at 1+r also
bounds the Mangoldt series at sigma. Combine monotonicity with the explicit cutoff bound.
This permits one certified scalar Euler cap to cover a whole analytic interval. -/
theorem tsum_vonMangoldt_le_truncatedEuler_of_gap_le {r σ : ℝ} (hr : 0 < r) (hgap : 1 + r ≤ σ)
    {N : ℕ} (hN : 3 ≤ N) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) ≤ truncatedEulerUpper r N := by
  exact
    (tsum_vonMangoldt_div_rpow_antitone (by linarith only [hr]) hgap).trans
      (tsum_vonMangoldt_le_truncatedEuler hr hN)

/-- For r>0 and 3<=N<=M, the Euler cap at M is at most its value at N.
Combine decreasing numerators and increasing positive denominators.
This permits adaptive cutoffs. -/
theorem truncatedEulerUpper_antitone_cutoff {r : ℝ} (hr : 0 < r) {N M : ℕ} (hN : 3 ≤ N)
    (hNM : N ≤ M) : truncatedEulerUpper r M ≤ truncatedEulerUpper r N := by
  have hA := Analysis.truncatedLogDirichletUpper_antitone_cutoff hr hN hNM
  have hB := Analysis.truncatedPowerDirichletLower_monotone_cutoff hr hNM
  exact
    (div_le_div_of_nonneg_right hA (Analysis.truncatedPowerDirichletLower_pos hr M).le).trans
      (div_le_div_of_nonneg_left (Analysis.truncatedLogDirichletUpper_nonneg hr N)
        (Analysis.truncatedPowerDirichletLower_pos hr N) hB)

/-- For r>0 and N>=3, the truncated Euler cap is no larger than the coarse ratio cap.
Compare numerator caps and positive denominator floors. Thus refinement preserves the old bound. -/
theorem truncatedEulerUpper_le_euler_ratio {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    truncatedEulerUpper r N ≤ (r⁻¹ ^ 2 + (r + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r) / r) := by
  have hA := Analysis.truncatedLogDirichletUpper_le_euler_numerator hr hN
  have hB :=
    Analysis.euler_denominator_le_truncatedPowerDirichletLower hr
      ((by norm_num only : 1 ≤ 3).trans hN)
  have hB0 : 0 < 1 + (2 : ℝ) ^ (-r) / r :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _) hr.le)
  have hA0 : 0 ≤ r⁻¹ ^ 2 + (r + 1)⁻¹ :=
    add_nonneg (sq_nonneg r⁻¹) (inv_nonneg.mpr (by linarith only [hr] : 0 ≤ r + 1))
  exact
    (div_le_div_of_nonneg_right hA (Analysis.truncatedPowerDirichletLower_pos hr N).le).trans
      (div_le_div_of_nonneg_left hA0 hB0 hB)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
