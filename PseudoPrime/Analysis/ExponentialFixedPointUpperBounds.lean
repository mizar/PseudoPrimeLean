/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import Mathlib.Algebra.Order.Floor.Div

/-! # Upper fixed-point exponential certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive natural denominator d, real division m/d is at most the
natural ceiling quotient. Cast its defining multiplicative inequality to the reals.
This justifies outward rounding in the exponential upper recurrence. -/
theorem div_le_cast_ceilDiv (m d : ℕ) (hd : 0 < d) : (m : ℝ) / d ≤ (((m + d - 1) / d : ℕ) : ℝ) := by
  have h : m ≤ d * ((m + d - 1) / d) := le_smul_ceilDiv (α := ℕ) (β := ℕ) hd
  have hc : (m : ℝ) ≤ (d : ℝ) * (((m + d - 1) / d : ℕ) : ℝ) := by exact_mod_cast h
  exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr (by simpa only [mul_comm] using hc)

/-- The outward rounded upper Taylor term at natural rational input a/b.
Start with scale and use (numerator+denominator-1)/denominator at each step.
For positive b, this overestimates the exact scaled Taylor term. -/
def expFixedPointUpperTerm (a b scale : ℕ) : ℕ → ℕ
  | 0 => scale
  | k + 1 => (expFixedPointUpperTerm a b scale k * a + b * (k + 1) - 1) / (b * (k + 1))

/-- For positive denominator b, each exact scaled Taylor term is at most
its upper fixed-point recurrence value. The ceiling inequality and factorial
recurrence prove the claim by induction. This validates executable upper terms. -/
theorem expFixedPointUpperTerm_ge (a b scale k : ℕ) (hb : 0 < b) :
    (scale : ℝ) * ((a : ℝ) / b) ^ k / (k.factorial : ℝ) ≤
      (expFixedPointUpperTerm a b scale k : ℝ) := by
  induction k with
  | zero =>
    simp only [expFixedPointUpperTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one,
      le_refl]
  | succ k
    ih =>
    have hm :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ih (Nat.cast_nonneg a))
        (mul_nonneg (Nat.cast_nonneg b)
          (add_nonneg (Nat.cast_nonneg k) (by norm_num only : (0 : ℝ) ≤ 1)))
    have heq :
      (scale : ℝ) * ((a : ℝ) / b) ^ k / (k.factorial : ℝ) * a / ((b : ℝ) * (k + 1)) =
        (scale : ℝ) * ((a : ℝ) / b) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq] at hm
    have hc :=
      div_le_cast_ceilDiv (expFixedPointUpperTerm a b scale k * a) (b * (k + 1))
        (Nat.mul_pos hb (Nat.succ_pos k))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
    exact hm.trans hc

/-- The first n upper fixed-point Taylor terms plus twice the next term.
Under a/b/(n+1)<=1/2 this is a scaled exponential upper bound.
The factor two comes from the proven analytic Taylor remainder. -/
def expFixedPointUpperSum (a b scale n : ℕ) : ℕ :=
  (∑ k ∈ Finset.range n, expFixedPointUpperTerm a b scale k) +
    2 * expFixedPointUpperTerm a b scale n

/-- With positive b and a/b/(n+1)<=1/2, scale exp(a/b) is at most the
upper fixed-point sum. Bound every polynomial term and the doubled remainder.
This provides a fully proved natural-number upper exponential certificate. -/
theorem expFixedPointUpperSum_ge_exp (a b scale n : ℕ) (hb : 0 < b)
    (hsize : ((a : ℝ) / b) / (n + 1 : ℕ) ≤ 1 / 2) :
    (scale : ℝ) * Real.exp ((a : ℝ) / b) ≤ (expFixedPointUpperSum a b scale n : ℝ) := by
  have hx : 0 ≤ (a : ℝ) / b := div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)
  have he := mul_le_mul_of_nonneg_left (exp_le_taylor_add_two_next hx hsize) (Nat.cast_nonneg scale)
  have hs :=
    Finset.sum_le_sum (fun k (_hk : k ∈ Finset.range n) ↦ expFixedPointUpperTerm_ge a b scale k hb)
  simp only [mul_div_assoc] at hs
  rw [← Finset.mul_sum] at hs
  have hn :=
    mul_le_mul_of_nonneg_left (expFixedPointUpperTerm_ge a b scale n hb)
      (by norm_num only : (0 : ℝ) ≤ 2)
  rw [expFixedPointUpperSum, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
  simp only [div_eq_mul_inv] at he hs hn ⊢
  nlinarith only [he, hs, hn]

end PseudoPrime.Analysis
