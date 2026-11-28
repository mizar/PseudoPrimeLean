/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic

/-! # Outward rounded fixed-point exponential certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The outward rounded lower Taylor term for nonnegative rational a/b and scale.
Start with scale; each recurrence multiplies by a and divides by b(k+1) using
natural-number division. The result underestimates the corresponding scaled real term. -/
def expFixedPointLowerTerm (a b scale : ℕ) : ℕ → ℕ
  | 0 => scale
  | k + 1 => expFixedPointLowerTerm a b scale k * a / (b * (k + 1))

/-- Every lower fixed-point term is at most scale times its exact Taylor term.
Natural division rounds down; induction and the factorial recurrence preserve the bound.
This justifies the integer arithmetic used for the positive exponential envelope. -/
theorem expFixedPointLowerTerm_le (a b scale k : ℕ) :
    (expFixedPointLowerTerm a b scale k : ℝ) ≤
      (scale : ℝ) * ((a : ℝ) / b) ^ k / (k.factorial : ℝ) := by
  induction k with
  | zero =>
    simp only [expFixedPointLowerTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one,
      le_refl]
  | succ k
    ih =>
    have hstep :
      (expFixedPointLowerTerm a b scale (k + 1) : ℝ) ≤
        (expFixedPointLowerTerm a b scale k : ℝ) * a / ((b : ℝ) * (k + 1)) := by
      simpa only [expFixedPointLowerTerm, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        (Nat.cast_div_le (m := expFixedPointLowerTerm a b scale k * a) (n := b * (k + 1)) :
          ((expFixedPointLowerTerm a b scale k * a / (b * (k + 1)) : ℕ) : ℝ) ≤ _)
    have hm :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ih (Nat.cast_nonneg a))
        (mul_nonneg (Nat.cast_nonneg b)
          (add_nonneg (Nat.cast_nonneg k) (by norm_num only : (0 : ℝ) ≤ 1)))
    refine hstep.trans (hm.trans_eq ?_)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The sum of the first n lower fixed-point Taylor terms at rational a/b.
All operations use natural numbers. This is the executable positive exponential lower bound. -/
def expFixedPointLowerSum (a b scale n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, expFixedPointLowerTerm a b scale k

/-- For any natural numerator, denominator, scale and term count, the lower
fixed-point sum is at most scale exp(a/b). Sum the termwise bounds and use the
nonnegative Taylor lower bound. No runtime certificate is assumed. -/
theorem expFixedPointLowerSum_le_exp (a b scale n : ℕ) :
    (expFixedPointLowerSum a b scale n : ℝ) ≤ (scale : ℝ) * Real.exp ((a : ℝ) / b) := by
  have h :=
    Finset.sum_le_sum (fun k (_hk : k ∈ Finset.range n) ↦ expFixedPointLowerTerm_le a b scale k)
  simp only [mul_div_assoc] at h
  rw [← Finset.mul_sum] at h
  rw [expFixedPointLowerSum, Nat.cast_sum]
  exact
    h.trans
      (mul_le_mul_of_nonneg_left
        (Real.sum_le_exp_of_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) n)
        (Nat.cast_nonneg scale))

/-- Integer multiplication comparisons certify lower Taylor terms supplied
by a generator, with no division in the certificate hypotheses. -/
theorem exp_mul_cert_term_le (a b Q : ℕ) (T : ℕ → ℕ) (hb : 0 < b) (hzero : T 0 = Q) {N : ℕ}
    (hstep : ∀ j < N, b * (j + 1) * T (j + 1) ≤ a * T j) :
    ∀ j ≤ N, (T j : ℝ) ≤ (Q : ℝ) * ((a : ℝ) / b) ^ j / j.factorial := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [hzero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one, le_refl]
  | succ j ih =>
    intro hj
    have hj' := Nat.lt_of_succ_le hj
    have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    have hd : 0 < (b : ℝ) * ((j : ℝ) + 1) := mul_pos hb' (by positivity)
    have hc : (b : ℝ) * ((j : ℝ) + 1) * T (j + 1) ≤ (a : ℝ) * T j := by exact_mod_cast hstep j hj'
    have ht : (T (j + 1) : ℝ) ≤ (T j : ℝ) * a / ((b : ℝ) * (j + 1)) :=
      (le_div_iff₀ hd).mpr (by simpa only [mul_comm, mul_left_comm] using hc)
    refine
      ht.trans
        ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (ih hj'.le) (Nat.cast_nonneg a))
              hd.le).trans_eq
          ?_)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- A prefix of terms certified by integer multiplication bounds the
positive exponential from below after division by the common scale. -/
theorem exp_mul_cert_sum_le (a b Q N : ℕ) (T : ℕ → ℕ) (hb : 0 < b) (hzero : T 0 = Q)
    (hstep : ∀ j < N, b * (j + 1) * T (j + 1) ≤ a * T j) :
    ((∑ j ∈ Finset.range (N + 1), T j : ℕ) : ℝ) ≤ Q * Real.exp ((a : ℝ) / b) := by
  rw [Nat.cast_sum]
  have ht :=
    Finset.sum_le_sum (s := Finset.range (N + 1)) fun j hj ↦
      exp_mul_cert_term_le a b Q T hb hzero hstep j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  simp only [mul_div_assoc, ← Finset.mul_sum] at ht
  exact
    ht.trans
      (mul_le_mul_of_nonneg_left
        (Real.sum_le_exp_of_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) (N + 1))
        (Nat.cast_nonneg Q))

/-- For nonnegative x with x/(n+1)<=1/2, exp(x) is at most the first n
Taylor terms plus twice the next term. Transfer the complex Taylor error bound
to the reals. This supplies an alternative rational upper envelope for x<=16. -/
theorem exp_le_taylor_add_two_next {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hsize : x / (n + 1 : ℕ) ≤ 1 / 2) :
    Real.exp x ≤
      (∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)) + x ^ n / (n.factorial : ℝ) * 2 := by
  have hc : ‖(x : ℂ)‖ / (n + 1 : ℕ) ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] using hsize
  have h := Complex.exp_bound' (n := n) hc
  have hr :
    |Real.exp x - ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)| ≤
      x ^ n / (n.factorial : ℝ) * 2 := by
    convert h using 1 <;> norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  have hl := le_abs_self (Real.exp x - ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ))
  linarith only [hl, hr]

/-- With at least one Taylor term, the lower fixed-point sum is at least scale.
The constant term is scale and all natural terms are nonnegative.
For positive scale this ensures the reciprocal cutoff denominator is nonzero. -/
theorem scale_le_expFixedPointLowerSum (a b scale n : ℕ) (hn : 0 < n) :
    scale ≤ expFixedPointLowerSum a b scale n := by
  have h :=
    Finset.single_le_sum
      (fun k (_hk : k ∈ Finset.range n) ↦ Nat.zero_le (expFixedPointLowerTerm a b scale k))
      (Finset.mem_range.mpr hn : 0 ∈ Finset.range n)
  simpa only [expFixedPointLowerSum, expFixedPointLowerTerm] using h

end PseudoPrime.Analysis
