/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.DyadicOddSums
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! # Dyadic sums of complex powers with positive integer bases -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For a positive real base, a critical-line negative complex power is a positive real amplitude
times a unit complex phase. Expanding the complex logarithm and exponential proves the identity.
This connects the phase checker to the actual terms of the finite Euler–Maclaurin sum. -/
theorem critical_power_phase (b t : ℝ) (hb : 0 < b) :
    (b : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) =
      (Real.exp (-Real.log b / 2) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * Complex.I) := by
  have hbn : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  rw [Complex.cpow_def_of_ne_zero hbn, ← Complex.ofReal_log hb.le, Complex.ofReal_exp, ←
    Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For a positive real base, the amplitude of its critical-line negative power is the reciprocal
of its positive square root. Squaring the exponential and using positivity identifies it with
the square root. This allows integer square-root and reciprocal certificates to bound amplitudes. -/
theorem critical_power_amplitude (b : ℝ) (hb : 0 < b) :
    Real.exp (-Real.log b / 2) = (Real.sqrt b)⁻¹ := by
  have hsq : Real.exp (Real.log b / 2) ^ 2 = b := by
    rw [pow_two, ← Real.exp_add]
    have h : Real.log b / 2 + Real.log b / 2 = Real.log b := by ring
    rw [h, Real.exp_log hb]
  have hp := Real.exp_pos (Real.log b / 2)
  have hs := Real.sq_sqrt hb.le
  have hn := Real.sqrt_nonneg b
  have he : Real.exp (Real.log b / 2) = Real.sqrt b := by nlinarith only [hsq, hp, hs, hn]
  rw [show -Real.log b / 2 = -(Real.log b / 2) by ring, Real.exp_neg, he]

/-- A critical-line negative power at a positive real base equals its reciprocal-square-root
amplitude times its logarithmic phase. This combines the phase decomposition with the amplitude
identity and provides the term formula for the computed odd-power sum. -/
theorem critical_power_sqrt_phase (b t : ℝ) (hb : 0 < b) :
    (b : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) =
      ((Real.sqrt b)⁻¹ : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * Complex.I) := by
  rw [critical_power_phase b t hb, critical_power_amplitude b hb, Complex.ofReal_inv]

/-- The summand `n ^ (-s)` at positive natural numbers, extended by zero at zero.
The zero extension allows sums over `Finset.range` to represent positive integer sums.
It is used in the compressed Euler–Maclaurin finite sum. -/
noncomputable def dyadicPowerTerm (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ (-s)

/-- A critical power term at a product of positive natural numbers is the product of the two
corresponding terms. The nonnegative-real-base complex power law gives the equality without
assuming multiplicativity for arbitrary complex bases. It supports factor-generated odd terms. -/
theorem dyadicPowerTerm_mul (s : ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    dyadicPowerTerm s (a * b) = dyadicPowerTerm s a * dyadicPowerTerm s b := by
  have hab : a * b ≠ 0 := Nat.ne_of_gt (Nat.mul_pos ha hb)
  simp only [dyadicPowerTerm, ite_eq_right (Nat.ne_of_gt ha), ite_eq_right (Nat.ne_of_gt hb),
    ite_eq_right hab, Nat.cast_mul]
  exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-s)

/-- Doubling a natural-number base multiplies the extended power term by `2 ^ (-s)`.
The zero case is handled separately; at positive bases the complex power product law applies
because both real bases are nonnegative. This supplies the even terms of the dyadic sum. -/
theorem dyadicPowerTerm_even (s : ℂ) (n : ℕ) :
    dyadicPowerTerm s (2 * n) = (2 : ℂ) ^ (-s) * dyadicPowerTerm s n := by
  by_cases hn : n = 0
  · simp only [hn, dyadicPowerTerm, ↓reduceIte, mul_zero]
  · have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by decide) hn
    simp only [dyadicPowerTerm, hn, h2n, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat]
    exact
      Complex.mul_cpow_ofReal_nonneg (show (0 : ℝ) ≤ (2 : ℕ) from Nat.cast_nonneg 2)
        (Nat.cast_nonneg n) (-s)

/-- A complex power at the positive base `2 ^ n` is the nth power of the value at two.
The argument of the positive real base is zero, so the complex power composition law applies.
This identity supplies the endpoint correction from the same base used in the Horner recurrence. -/
theorem dyadic_cpow (s : ℂ) (n : ℕ) : ((2 : ℂ) ^ n) ^ (-s) = ((2 : ℂ) ^ (-s)) ^ n := by
  have ha : Complex.arg (2 : ℂ) = 0 :=
    Complex.arg_ofReal_of_nonneg (show (0 : ℝ) ≤ (2 : ℕ) from Nat.cast_nonneg 2)
  have h1 : -Real.pi < (n : ℝ) * Complex.arg (2 : ℂ) := by
    rw [ha, mul_zero]
    exact neg_lt_zero.mpr Real.pi_pos
  have h2 : (n : ℝ) * Complex.arg (2 : ℂ) ≤ Real.pi := by
    rw [ha, mul_zero]
    exact Real.pi_pos.le
  rw [← Complex.cpow_nat_mul' h1 h2, Complex.cpow_nat_mul]

/-- The sum of positive integer powers below `2 ^ (m + 1)` is the sum of its odd terms plus
`2 ^ (-s)` times the corresponding sum below `2 ^ m`. The zero-extended term and the generic
even-odd split make this an exact identity, used to build the finite zeta sum by Horner steps. -/
theorem dyadicPowerTerm_sum (s : ℂ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 ^ (m + 1)), dyadicPowerTerm s k) =
      (∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s (2 * k + 1)) +
        (2 : ℂ) ^ (-s) * ∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s k := by
  exact Analysis.sum_range_pow_two_odd (dyadicPowerTerm s) _ (dyadicPowerTerm_even s) m

/-- Build a dyadic power sum from successive odd sums by Horner recurrence.
The input is the complex exponent and the dyadic depth; the initial sum is zero.
Each later level uses the odd powers at that level and the common power of two.
This representation avoids computing even powers separately in the finite zeta sum. -/
noncomputable def dyadicOddHorner (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 =>
    (∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s (2 * k + 1)) +
      (2 : ℂ) ^ (-s) * dyadicOddHorner s m

/-- The odd-sum Horner recurrence exactly equals the sum below `2 ^ m`.
Induction applies the dyadic even-odd identity at each level. The result permits finite
Euler–Maclaurin sums to be evaluated through odd terms without approximation. -/
theorem dyadicOddHorner_eq (s : ℂ) (m : ℕ) :
    dyadicOddHorner s m = ∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s k := by
  induction m with
  | zero => simp only [dyadicOddHorner, pow_zero, Finset.sum_range_one, dyadicPowerTerm, ↓reduceIte]
  | succ m ih => rw [dyadicOddHorner, ih, dyadicPowerTerm_sum]

/-- Compute a dyadic power sum and its current odd prefix together. At level zero both are the
term at one; each later level appends a disjoint block of odd terms and makes one Horner step.
The pair preserves the prefix for the next level, avoiding repeated evaluation of odd terms. -/
noncomputable def dyadicOddPair (s : ℂ) : ℕ → ℂ × ℂ
  | 0 => (dyadicPowerTerm s 1, dyadicPowerTerm s 1)
  | m + 1 =>
    let v := dyadicOddPair s m
    let odd := v.2 + ∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s (2 * (2 ^ m + k) + 1)
    (odd + (2 : ℂ) ^ (-s) * v.1, odd)

/-- The first component of the accumulated pair is the sum below `2 ^ (m + 1)` and the
second is its odd part. Induction combines the odd-prefix increment with the dyadic power-sum
recurrence. This invariant connects a one-pass odd-term evaluator to the finite zeta sum. -/
theorem dyadicOddPair_eq (s : ℂ) (m : ℕ) :
    dyadicOddPair s m =
      ((∑ k ∈ Finset.range (2 ^ (m + 1)), dyadicPowerTerm s k),
        (∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s (2 * k + 1))) := by
  induction m with
  | zero =>
    simp only [dyadicOddPair, pow_zero, pow_one, Finset.sum_range_one, zero_add, mul_zero,
      dyadicPowerTerm, Nat.cast_one, Complex.one_cpow]
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [↓reduceIte, Nat.cast_one, Complex.one_cpow, zero_add]
  | succ m ih =>
    simp only [dyadicOddPair, ih]
    rw [dyadicPowerTerm_sum s (m + 1), Analysis.odd_prefix_succ]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
