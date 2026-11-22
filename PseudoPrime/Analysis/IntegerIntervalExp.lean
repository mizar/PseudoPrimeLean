/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalExpressions
public import PseudoPrime.Analysis.RationalPhaseTaylor

/-! # Exponential Taylor error transport to integer intervals -/

public section

namespace PseudoPrime.Analysis

/-- For a real argument of absolute value at most one quarter, the 25-term
exponential Taylor sum has absolute error at most `2^-120`. This is the
analytic remainder used before sixteen interval squarings. -/
theorem exp_taylor24_error {x : ℝ} (hx : |x| ≤ 1 / 4) :
    |Real.exp x - ∑ m ∈ Finset.range 25, x ^ m / (m.factorial : ℝ)| ≤ (1 / 2 ^ 120 : ℝ) := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num only)
  have h := Real.exp_bound hx1 (n := 25) (by norm_num only)
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 25
  have hc : (0 : ℝ) ≤ (26 : ℝ) / ((25 : ℕ).factorial * 25) := by norm_num only
  have hm := mul_le_mul_of_nonneg_right hp hc
  have hn : (1 / 4 : ℝ) ^ 25 * (26 / ((25 : ℕ).factorial * 25)) ≤ 1 / 2 ^ 120 := by
    norm_num only [Nat.factorial]
  exact h.trans (hm.trans hn)

/-- If an integer interval encloses the exponential Taylor sum at a small
real argument, widening by the certified tick budget encloses the true exponential.
The finite polynomial containment can be supplied by checked arithmetic. -/
theorem exp_taylor24_contains {I : IntegerInterval} {G r : ℤ} {x : ℝ} (hx : |x| ≤ 1 / 4)
    (hI : I.Contains G (∑ m ∈ Finset.range 25, x ^ m / (m.factorial : ℝ)))
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) : (I.widen r).Contains G (Real.exp x) := by
  exact IntegerInterval.widen_contains hI ((exp_taylor24_error hx).trans hr)

/-- Recursively check every proposed squaring interval at common scale.
The next interval becomes the current one, avoiding indexed table access. -/
def intervalSquareCheck (G : ℤ) (I : IntegerInterval) : List IntegerInterval → Bool
  | [] => true
  | J :: rest =>
    integerProductCheck G I.lower I.upper I.lower I.upper J.lower J.upper &&
      intervalSquareCheck G J rest

/-- Return the final interval of a squaring certificate, or the initial interval
for an empty chain. The recursive traversal matches the checker. -/
def intervalSquareResult (I : IntegerInterval) : List IntegerInterval → IntegerInterval
  | [] => I
  | J :: rest => intervalSquareResult J rest

/-- Checked successive squarings transport an exponential enclosure from `x`
to `2^length * x`. Each step uses product soundness and the exponential addition law. -/
theorem intervalSquareCheck_exp_sound (chain : List IntegerInterval) (G : ℤ) (I : IntegerInterval)
    (x : ℝ) (h : intervalSquareCheck G I chain = true) (hx : I.Contains G (Real.exp x)) :
    (intervalSquareResult I chain).Contains G (Real.exp ((2 : ℝ) ^ chain.length * x)) := by
  induction chain generalizing I x with
  | nil => simpa only [intervalSquareResult, List.length_nil, pow_zero, one_mul] using hx
  | cons J rest ih =>
    have hc := Bool.and_eq_true_iff.mp h
    have hj := IntegerInterval.product_contains hc.1 hx hx
    rw [← Real.exp_add] at hj
    have hr := ih J (x + x) hc.2 hj
    have he : (2 : ℝ) ^ rest.length * (x + x) = 2 ^ (rest.length + 1) * x := by
      rw [pow_succ]
      ring
    simpa only [intervalSquareResult, List.length_cons, he] using hr

/-- A Taylor certificate at `x/2^n`, widened by its analytic error and followed
by `n` checked squarings, encloses `exp x`. This is the range-reduced endpoint API. -/
theorem exp_reduced_contains (chain : List IntegerInterval) (n : ℕ) (I : IntegerInterval) (G r : ℤ)
    (x : ℝ) (hlen : chain.length = n) (hx : |x / (2 : ℝ) ^ n| ≤ 1 / 4)
    (hp : I.Contains G (∑ m ∈ Finset.range 25, (x / (2 : ℝ) ^ n) ^ m / (m.factorial : ℝ)))
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) (hc : intervalSquareCheck G (I.widen r) chain = true) :
    (intervalSquareResult (I.widen r) chain).Contains G (Real.exp x) := by
  have hi := exp_taylor24_contains hx hp hr
  have hs := intervalSquareCheck_exp_sound chain G (I.widen r) (x / (2 : ℝ) ^ n) hc hi
  rw [hlen] at hs
  have he : (2 : ℝ) ^ n * (x / (2 : ℝ) ^ n) = x := by
    exact mul_div_cancel₀ x (pow_ne_zero n (by norm_num only : (2 : ℝ) ≠ 0))
  rwa [he] at hs

/-- Checked polynomial arithmetic feeds the range-reduced exponential theorem.
The equality identifies the arithmetic expression with the Taylor polynomial;
all rounded arithmetic witnesses and squarings are checked independently. -/
theorem exp_of_checked_taylor (e : IntegerIntervalExpr) (chain : List IntegerInterval) (n : ℕ)
    (G r : ℤ) (x : ℝ) (hlen : chain.length = n) (hx : |x / (2 : ℝ) ^ n| ≤ 1 / 4)
    (he : e.check G = true)
    (hv : e.value = ∑ m ∈ Finset.range 25, (x / (2 : ℝ) ^ n) ^ m / (m.factorial : ℝ))
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G)
    (hc : intervalSquareCheck G (e.interval.widen r) chain = true) :
    (intervalSquareResult (e.interval.widen r) chain).Contains G (Real.exp x) := by
  have hp := e.check_sound G he
  rw [hv] at hp
  exact exp_reduced_contains chain n e.interval G r x hlen hx hp hr hc

end PseudoPrime.Analysis
