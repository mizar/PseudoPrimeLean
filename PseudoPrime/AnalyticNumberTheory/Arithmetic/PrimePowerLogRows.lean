/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix

/-! # Checked logarithm rows for prime-power prefix increments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Rational data for the Mangoldt weight of one prime power. `p` is the prime
base, `k + 1` is the exponent, `j` and `terms` specify the logarithm checker,
and `lo`, `hi` are rational logarithm endpoints. The row checker verifies
primality and both endpoint inequalities before the data is used in a prefix. -/
structure PrimePowerLogRow where
  p : ℕ
  k : ℕ
  j : ℕ
  terms : ℕ
  lo : ℚ
  hi : ℚ

/-- Check that the base is prime and that the rational logarithm checker accepts
the proposed interval. The exponent is `k + 1`, so it is automatically positive. -/
def primePowerLogCheck (r : PrimePowerLogRow) : Bool :=
  @decide r.p.Prime (Nat.decidablePrime' r.p) &&
    Analysis.rationalLogIntervalCheck r.p r.j r.terms r.lo r.hi

/-- A checked row bounds the actual Mangoldt weight of its prime power by the
two rational endpoints. Primality and the logarithm bounds come from the checker. -/
theorem prime_power_log_row_bounds {r : PrimePowerLogRow} (h : primePowerLogCheck r = true) :
    (r.lo : ℝ) ≤ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) ∧
      ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) ≤ (r.hi : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp h
  let : Decidable r.p.Prime := Nat.decidablePrime' r.p
  have hp : r.p.Prime := of_decide_eq_true hc.1
  have hlog := Analysis.rationalLogIntervalCheck_sound hc.2
  simp only [Rat.cast_natCast] at hlog
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero r.k),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact hlog

/-- If every row passes its checker, the sum of their actual Mangoldt weights is
between the sums of their rational endpoints. This is independent of whether the
rows completely enumerate any specified interval. -/
theorem prime_power_log_rows_bounds (rows : List PrimePowerLogRow)
    (h : rows.all primePowerLogCheck = true) :
    (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤
        (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum ∧
      (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum ≤
        (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
  constructor
  · apply List.sum_le_sum
    intro r hr
    exact (prime_power_log_row_bounds (List.all_eq_true.mp h r hr)).1
  · apply List.sum_le_sum
    intro r hr
    exact (prime_power_log_row_bounds (List.all_eq_true.mp h r hr)).2

/-- A checked row list extends a bounded psi prefix from `a` to `b` when its
actual weights equal the Mangoldt increment on `(a, b]`. The equality is an
explicit coverage requirement; successful row checks alone do not imply it. -/
theorem psi_prefix_bounds_of_rows {a b : ℕ} {L U : ℝ} (hab : a ≤ b) (hL : L ≤ Chebyshev.psi a)
    (hU : Chebyshev.psi a ≤ U) (rows : List PrimePowerLogRow)
    (hrows : rows.all primePowerLogCheck = true)
    (hcover :
      (∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n) =
        (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum) :
    L + (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤ Chebyshev.psi b ∧
      Chebyshev.psi b ≤ U + (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
  have h := prime_power_log_rows_bounds rows hrows
  apply psi_prefix_bounds_of_interval hab hL hU
  · rw [hcover]
    exact h.1
  · rw [hcover]
    exact h.2

end PseudoPrime.AnalyticNumberTheory.Arithmetic
