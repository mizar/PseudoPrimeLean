/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularArithmeticCorrection
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CommonFactorPrimePowerReindex

/-! # Explicit logarithmic alpha-18 level corrections -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For natural powers, the square root commutes with exponentiation.
Induct using multiplicativity on nonnegative reals; used in the geometric correction. -/
theorem sqrt_nat_pow_for_correction {p k : ℕ} : Real.sqrt ((p : ℝ) ^ k) = (Real.sqrt p) ^ k := by
  induction k with
  | zero => rw [pow_zero, Real.sqrt_one, pow_zero]
  | succ k hk => rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) k), hk, pow_succ]

/-- For prime p, the positive prime-power series with square-root denominator
has sum log p divided by (sqrt p - 1). Evaluate the geometric series. -/
theorem hasSum_log_div_sqrt_prime_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ ↦ Real.log p / Real.sqrt ((p : ℝ) ^ (k + 1)))
      (Real.log p / (Real.sqrt p - 1)) := by
  have hr : 1 < Real.sqrt p := by
    have h := Real.sqrt_lt_sqrt (by norm_num only : (0 : ℝ) ≤ 1) (Nat.one_lt_cast.mpr hp.one_lt)
    simpa only [Real.sqrt_one] using h
  have hi := inv_lt_one_of_one_lt₀ hr
  have hgeo :=
    (hasSum_geometric_of_lt_one (inv_nonneg.mpr (Real.sqrt_nonneg p)) hi).mul_left
      (Real.log p / Real.sqrt p)
  have he : (Real.sqrt p)⁻¹ / (1 - (Real.sqrt p)⁻¹) = 1 / (Real.sqrt p - 1) := by
    rw [div_eq_div_iff (ne_of_gt (sub_pos.mpr hi)) (sub_ne_zero.mpr hr.ne')]
    rw [mul_sub, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans hr)), mul_one, one_mul]
  have hv (k : ℕ) :
    Real.log p / Real.sqrt ((p : ℝ) ^ (k + 1)) =
      (Real.log p / Real.sqrt p) * (Real.sqrt p)⁻¹ ^ k := by
    rw [sqrt_nat_pow_for_correction, pow_succ, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have hd :
    Real.log p / (Real.sqrt p - 1) = (Real.log p / Real.sqrt p) * (1 - (Real.sqrt p)⁻¹)⁻¹ := by
    have h := congrArg (fun z : ℝ ↦ Real.log p * z) he
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h.symm
  simpa only [hv, hd] using hgeo

/-- For a prime p, log p divided by (sqrt p - 1) is at most 3 log p.
The lower bound sqrt p >= 4/3 controls the positive denominator. -/
theorem log_div_sqrt_prime_sub_one_le_three_log {p : ℕ} (hp : p.Prime) :
    Real.log p / (Real.sqrt p - 1) ≤ 3 * Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := Nat.ofNat_le_cast.mpr hp.two_le
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  have hn := Real.sqrt_nonneg p
  have hlow : (4 / 3 : ℝ) ≤ Real.sqrt p := by nlinarith only [hp2, hs, hn]
  have hd : 0 < Real.sqrt p - 1 := by linarith only [hlow]
  apply (div_le_iff₀ hd).mpr
  have hl := Real.log_natCast_nonneg p
  nlinarith only [hlow, hl]

end PseudoPrime.Analysis
