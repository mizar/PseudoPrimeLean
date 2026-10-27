/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.UniformPolynomialThetaSupply

/-! # Integer rounding for polynomial exceptional-conductor heights -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/-- For a nonnegative base and positive natural exponent, taking the reciprocal real
power and the natural power cancels in either order. -/
theorem rpow_nat_root_cancel {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    (x ^ (1 / (n : ℝ))) ^ n = x ∧ (x ^ n) ^ (1 / (n : ℝ)) = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel hn0, Real.rpow_one]
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_one_div_cancel hn0, Real.rpow_one]

/-- Rounding a polynomial root upward preserves a square modulus bound and controls
the corresponding height power by a fixed factor times the square of the scale.
These estimates select one exceptional-conductor height before the modulus is known. -/
theorem rounded_polynomial_height_bounds {Z : ℝ} (hZ : 1 ≤ Z) {n : ℕ} (hn : 0 < n) :
    let R := ⌈Z ^ (1 / (n : ℝ))⌉₊
    (R : ℝ) ^ (2 * n) ≤ (2 : ℝ) ^ (2 * n) * Z ^ 2 ∧
      ∀ q : ℕ, (q : ℝ) ^ (2 * n) ≤ Z → (q : ℝ) ^ 2 ≤ R := by
  dsimp only
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hα : 0 ≤ 1 / (n : ℝ) := (one_div_pos.mpr hnpos).le
  have hu : 1 ≤ Z ^ (1 / (n : ℝ)) := Real.one_le_rpow hZ hα
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hZ0 (1 / (n : ℝ)))
  have hR : (⌈Z ^ (1 / (n : ℝ))⌉₊ : ℝ) ≤ 2 * Z ^ (1 / (n : ℝ)) := by linarith only [hceil, hu]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hR (2 * n)
  rw [mul_pow] at hp
  have hpow : (Z ^ (1 / (n : ℝ))) ^ (2 * n) = Z ^ 2 := by
    rw [Nat.mul_comm 2 n, pow_mul, (rpow_nat_root_cancel hZ0 hn).1]
  rw [hpow] at hp
  refine ⟨hp, ?_⟩
  intro q hq
  have hqr := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg q) (2 * n)) hq hα
  have he : ((q : ℝ) ^ (2 * n)) ^ (1 / (n : ℝ)) = (q : ℝ) ^ 2 := by
    rw [pow_mul]
    exact (rpow_nat_root_cancel (sq_nonneg (q : ℝ)) hn).2
  rw [he] at hqr
  exact hqr.trans (Nat.le_ceil _)

end PseudoPrime.AnalyticNumberTheory.AGP
