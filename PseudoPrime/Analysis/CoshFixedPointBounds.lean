/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Outward rounded fixed-point lower bounds for hyperbolic cosine

The even Taylor recurrence rounds down using natural division. An explicit state
implementation is proved equal to the finite-sum specification.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Lower fixed-point even Taylor term at nonnegative rational a/b.
The initial term is scale; natural division rounds each recurrence down. -/
def coshFixedPointLowerTerm (a b scale : ℕ) : ℕ → ℕ
  | 0 => scale
  | k + 1 => coshFixedPointLowerTerm a b scale k * a * a / (b * b * ((2 * k + 1) * (2 * k + 2)))

/-- Every lower term is at most scale times the corresponding exact cosh term.
Use induction, downward division, and the two-step factorial recurrence. -/
theorem coshFixedPointLowerTerm_le (a b scale k : ℕ) :
    (coshFixedPointLowerTerm a b scale k : ℝ) ≤
      (scale : ℝ) * ((a : ℝ) / b) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction k with
  | zero =>
    simp only [coshFixedPointLowerTerm, mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, div_one, le_refl]
  | succ k
    ih =>
    have hstep :
      (coshFixedPointLowerTerm a b scale (k + 1) : ℝ) ≤
        (coshFixedPointLowerTerm a b scale k : ℝ) * a * a /
          ((b : ℝ) * b * ((2 * k + 1) * (2 * k + 2))) := by
      simpa only [coshFixedPointLowerTerm, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat] using
        (Nat.cast_div_le (m := coshFixedPointLowerTerm a b scale k * a * a) (n :=
            b * b * ((2 * k + 1) * (2 * k + 2))) :
          ((coshFixedPointLowerTerm a b scale k * a * a / (b * b * ((2 * k + 1) * (2 * k + 2))) :
                ℕ) :
              ℝ) ≤
            _)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ih (Nat.cast_nonneg a))
          (Nat.cast_nonneg a))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg b))
          (mul_nonneg (by nlinarith only [hk0] : (0 : ℝ) ≤ 2 * k + 1)
            (by nlinarith only [hk0] : (0 : ℝ) ≤ 2 * k + 2)))
    refine hstep.trans (hm.trans_eq ?_)
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      pow_succ, pow_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The sum of the first n lower fixed-point even Taylor terms.
This specification gives a natural-number lower bound for scale times cosh(a/b). -/
def coshFixedPointLowerSum (a b scale n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, coshFixedPointLowerTerm a b scale k

/-- For nonnegative x, every finite even Taylor sum is at most cosh x.
The convergent cosh series has nonnegative terms, so omitted terms increase the value. -/
theorem cosh_partialSum_le_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range n, x ^ (2 * k) / ((2 * k).factorial : ℝ)) ≤ Real.cosh x := by
  rw [Real.cosh_eq_tsum]
  exact
    Summable.sum_le_tsum (Finset.range n)
      (fun k _ ↦ div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)) (Real.hasSum_cosh x).summable

/-- The fixed-point lower sum is at most scale times cosh(a/b).
Sum the termwise bounds and apply the nonnegative even Taylor series estimate. -/
theorem coshFixedPointLowerSum_le_cosh (a b scale n : ℕ) :
    (coshFixedPointLowerSum a b scale n : ℝ) ≤ (scale : ℝ) * Real.cosh ((a : ℝ) / b) := by
  have h :=
    Finset.sum_le_sum (fun k (_hk : k ∈ Finset.range n) ↦ coshFixedPointLowerTerm_le a b scale k)
  simp only [mul_div_assoc] at h
  rw [← Finset.mul_sum] at h
  rw [coshFixedPointLowerSum, Nat.cast_sum]
  exact
    h.trans
      (mul_le_mul_of_nonneg_left
        (cosh_partialSum_le_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) n)
        (Nat.cast_nonneg scale))

/-- The current even Taylor term and the accumulated preceding terms.
Advance both in one recurrence to avoid recomputing prefixes during kernel evaluation. -/
def coshFixedPointLowerState (a b scale : ℕ) : ℕ → ℕ × ℕ
  | 0 => (scale, 0)
  | k + 1 =>
    let p := coshFixedPointLowerState a b scale k
    (p.1 * a * a / (b * b * ((2 * k + 1) * (2 * k + 2))), p.2 + p.1)

/-- The execution state equals the specification term and finite sum.
Induction proves the exact equality needed to transfer the analytic lower bound. -/
theorem coshFixedPointLowerState_eq (a b scale n : ℕ) :
    coshFixedPointLowerState a b scale n =
      (coshFixedPointLowerTerm a b scale n, coshFixedPointLowerSum a b scale n) := by
  induction n with
  | zero =>
    simp only [coshFixedPointLowerState, coshFixedPointLowerTerm, coshFixedPointLowerSum,
      Finset.sum_range_zero]
  | succ n ih =>
    simp only [coshFixedPointLowerState, ih, coshFixedPointLowerTerm, coshFixedPointLowerSum,
      Finset.sum_range_succ]

/-- The accumulated lower sum from the explicit execution state.
Its equality theorem connects this execution API to the finite-sum specification. -/
def coshFixedPointLowerSumFast (a b scale n : ℕ) : ℕ :=
  (coshFixedPointLowerState a b scale n).2

/-- The explicit execution API equals the lower-sum specification.
Project the state equality; no implicit compiler substitution is used. -/
theorem coshFixedPointLowerSumFast_eq (a b scale n : ℕ) :
    coshFixedPointLowerSumFast a b scale n = coshFixedPointLowerSum a b scale n := by
  rw [coshFixedPointLowerSumFast, coshFixedPointLowerState_eq]

end PseudoPrime.Analysis
