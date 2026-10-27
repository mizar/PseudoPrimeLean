/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLocalSeries

/-! # Exponential ramp local bounds for every value in the complex unit disk -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a complex value in the closed unit disk, every power gives a paired real
coefficient between zero and two. Norm powers and bound the real part. This
replaces the three-value quadratic case split in local positivity estimates. -/
theorem one_add_pow_re_bounds_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (k : ℕ) :
    0 ≤ (1 + c ^ k).re ∧ (1 + c ^ k).re ≤ 2 := by
  have hp : ‖c ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg c) hc
  have hr := abs_le.mp ((Complex.abs_re_le_norm (c ^ k)).trans hp)
  rw [Complex.add_re, Complex.one_re]
  constructor
  · linarith only [hr.1]
  · linarith only [hr.2]

/-- For a local value of norm at most one, every signed ramp term has absolute value
at most twice its exponential envelope. Use the paired coefficient interval and
both ramp bounds. This supplies absolute convergence for nonquadratic characters. -/
theorem norm_exponentialRampLocalCorrection_le_exp_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (u : ℝ)
    (k : ℕ) : ‖exponentialRampLocalCorrection c u k‖ ≤ 2 * Real.exp (-u) := by
  have h := one_add_pow_re_bounds_of_norm_le_one hc k
  have h0 := mul_nonneg h.1 (Real.exp_pos (-u)).le
  have h2 := mul_le_mul_of_nonneg_right h.2 (Real.exp_pos (-u)).le
  have hW := exponentialRampWeight_bounds u
  rw [Real.norm_eq_abs, abs_le]
  dsimp only [exponentialRampLocalCorrection]
  constructor
  · linarith only [h2, hW.1]
  · linarith only [h0, hW.2]

/-- Above the ramp cutoff, every local term with coefficient in the unit disk is
nonpositive. The ramp vanishes and the paired real coefficient is nonnegative.
This allows general characters in the prime-triviality comparison. -/
theorem exponentialRampLocalCorrection_tail_nonpos_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) {u : ℝ}
    (hu : 99 / 40 ≤ u) (k : ℕ) : exponentialRampLocalCorrection c u k ≤ 0 := by
  rw [exponentialRampLocalCorrection, exponentialRampWeight_eq_zero hu, mul_zero, zero_sub]
  exact
    neg_nonpos.mpr (mul_nonneg (one_add_pow_re_bounds_of_norm_le_one hc k).1 (Real.exp_pos (-u)).le)

/-- For a unit-disk value, positive scale and heights growing at least linearly,
the local correction series converges absolutely. Dominate its norm by a geometric
exponential. No real-valued or quadratic hypothesis is required. -/
theorem summable_exponentialRampLocalCorrection_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) {x : ℝ}
    (hx : 0 < x) (u : ℕ → ℝ) (hu : ∀ k, ((k + 1 : ℕ) : ℝ) / x ≤ u k) :
    Summable (fun k ↦ exponentialRampLocalCorrection c (u k) (k + 1)) := by
  have hr : ‖Real.exp (-1 / x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num only) hx
  have hs := (summable_geometric_of_norm_lt_one hr).mul_right (Real.exp (-1 / x))
  have hmajor : Summable (fun k : ℕ ↦ 2 * Real.exp (-1 / x) ^ (k + 1)) := by
    simpa only [pow_succ] using hs.mul_left 2
  apply hmajor.of_norm_bounded
  intro k
  have he : Real.exp (-(u k)) ≤ Real.exp (-((k + 1 : ℕ) : ℝ) / x) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg (hu k)
  calc
    _ ≤ 2 * Real.exp (-(u k)) := norm_exponentialRampLocalCorrection_le_exp_of_norm_le_one hc _ _
    _ ≤ 2 * Real.exp (-((k + 1 : ℕ) : ℝ) / x) := mul_le_mul_of_nonneg_left he (by norm_num only)
    _ = _ := by rw [exp_neg_div_nat_eq_power]

end PseudoPrime.Analysis
