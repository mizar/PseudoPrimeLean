/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPoleInversion
import Mathlib.Tactic.Ring

/-! # Real inverse Mellin profiles for shifted poles of arbitrary order -/

namespace PseudoPrime.Analysis

/-- The real inverse profile for a shifted pole of order `n + 1` at
`-ρ` with modulation `exp (b * z)`. The logarithmic factor vanishes
beyond the support endpoint when `n ≥ 1`. -/
@[expose]
public noncomputable def shiftedPoleProfile (n : ℕ) (ρ b u : ℝ) : ℝ :=
  let v := u * Real.exp (-b)
  v ^ ρ * (-Real.log (min v 1)) ^ n / n.factorial

/-- On every line to the right of the pole, the inverse Mellin transform
is the same real profile. The order may be odd or even. -/
public theorem inverseMellin_shiftedPole {n : ℕ} (hn : 1 ≤ n) {ρ σ u : ℝ} (hσ : 0 < σ + ρ)
    (hu : 0 < u) (b : ℝ) :
    inverseMellin (fun z : ℂ ↦ Complex.exp ((b : ℂ) * z) / (z + ρ) ^ (n + 1)) σ u =
      (shiftedPoleProfile n ρ b u : ℂ) := by
  have hb : (2 : ℝ) * (b / 2) = b := by ring
  have hc : (2 : ℂ) * ((b / 2 : ℝ) : ℂ) = (b : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, hb]
  have h := inverseMellin_shifted_power hn hσ hu (b / 2)
  rw [hc, hb] at h
  rw [h, ← Complex.ofReal_cpow (mul_pos hu (Real.exp_pos _)).le,
    logPowerWeight_eq_log_min hn (mul_pos hu (Real.exp_pos _))]
  simp only [shiftedPoleProfile, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast, mul_div_assoc]

/-- The inverse profile is nonnegative on the positive real axis. -/
public theorem shiftedPoleProfile_nonneg (n : ℕ) (ρ b : ℝ) {u : ℝ} (hu : 0 < u) :
    0 ≤ shiftedPoleProfile n ρ b u := by
  let v := u * Real.exp (-b)
  have hv : 0 < v := mul_pos hu (Real.exp_pos _)
  have hlog := Real.log_nonpos (le_min hv.le zero_le_one) (min_le_right v 1)
  exact
    div_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (pow_nonneg (neg_nonneg.mpr hlog) _))
      (Nat.cast_nonneg _)

/-- The inverse profile vanishes at and beyond the support endpoint for
poles of order at least two. -/
public theorem shiftedPoleProfile_support {n : ℕ} (hn : 1 ≤ n) (ρ : ℝ) {b u : ℝ}
    (hu : Real.exp b ≤ u) : shiftedPoleProfile n ρ b u = 0 := by
  have hv : 1 ≤ u * Real.exp (-b) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    exact hu
  simp only [shiftedPoleProfile, min_eq_right hv, Real.log_one, neg_zero,
    zero_pow (Nat.ne_of_gt (hn)), mul_zero, zero_div]

/-- Within the support the real profile is the shifted logarithmic
monomial, with no truncation in its logarithmic factor. -/
public theorem shiftedPoleProfile_eq (n : ℕ) (ρ : ℝ) {b u : ℝ} (hu : 0 < u) (hb : u ≤ Real.exp b) :
    shiftedPoleProfile n ρ b u = (u * Real.exp (-b)) ^ ρ * (b - Real.log u) ^ n / n.factorial := by
  have hv : u * Real.exp (-b) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact hb
  dsimp only [shiftedPoleProfile]
  rw [min_eq_left hv, Real.log_mul hu.ne' (Real.exp_pos _).ne', Real.log_exp, neg_add, neg_neg,
    sub_eq_add_neg, add_comm (b : ℝ)]

end PseudoPrime.Analysis
