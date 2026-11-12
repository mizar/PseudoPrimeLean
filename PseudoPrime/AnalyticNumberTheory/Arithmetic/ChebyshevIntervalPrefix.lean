/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals

/-! # Chebyshev prefixes from independently certified increments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For natural `a ≤ b`, the psi prefix through `b` is the psi prefix through `a`
plus the Mangoldt sum on `(a, b]`. This permits independently certified increments
to extend an already checked prefix. -/
theorem psi_prefix_add_interval {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.psi a + ∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n = Chebyshev.psi b := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  exact Finset.sum_Ioc_consecutive ArithmeticFunction.vonMangoldt (Nat.zero_le a) hab

/-- For natural `a ≤ b`, the theta prefix through `b` is the theta prefix through `a`
plus the logarithmic prime sum on `(a, b]`. This is the theta counterpart of the
incremental psi prefix identity. -/
theorem theta_prefix_add_interval {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta a + ∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n =
      Chebyshev.theta b := by
  classical
  simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
  exact Finset.sum_Ioc_consecutive (fun n ↦ if n.Prime then Real.log n else 0) (Nat.zero_le a) hab

/-- If `n + 1` is not a prime power, its Mangoldt increment vanishes, so the
psi prefixes through `n` and `n + 1` coincide. -/
theorem psi_succ_of_not_prime_power {n : ℕ} (hn : ¬IsPrimePow (n + 1)) :
    Chebyshev.psi (n + 1 : ℕ) = Chebyshev.psi n := by
  have h := psi_prefix_add_interval (a := n) (b := n + 1) (Nat.le_succ n)
  rw [Nat.Ioc_succ_singleton, Finset.sum_singleton,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, add_zero] at h
  exact h.symm

/-- If `(a, b]` contains no prime power, its Mangoldt sum vanishes and the two
psi prefixes agree. A single interval check can therefore reuse a prior prefix. -/
theorem psi_eq_of_no_prime_power {a b : ℕ} (hab : a ≤ b)
    (hn : ∀ n ∈ Finset.Ioc a b, ¬IsPrimePow n) : Chebyshev.psi b = Chebyshev.psi a := by
  simpa only [Finset.sum_eq_zero
        (fun n hn' ↦ ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (hn n hn')),
    add_zero] using (psi_prefix_add_interval hab).symm

/-- If `n + 1` is not prime, it contributes no logarithmic prime weight, so the
theta prefixes through `n` and `n + 1` coincide. -/
theorem theta_succ_of_not_prime {n : ℕ} (hn : ¬Nat.Prime (n + 1)) :
    Chebyshev.theta (n + 1 : ℕ) = Chebyshev.theta n := by
  classical
  have h := theta_prefix_add_interval (a := n) (b := n + 1) (Nat.le_succ n)
  rw [Nat.Ioc_succ_singleton] at h
  simp only [Finset.filter_singleton, hn, ite_false, Finset.sum_empty, add_zero] at h
  exact h.symm

/-- If `psi a` and its increment on `(a, b]` have explicit lower and upper bounds,
adding the bounds certifies `psi b`. No numerical certificate is built into this theorem. -/
theorem psi_prefix_bounds_of_interval {a b : ℕ} {L U l u : ℝ} (hab : a ≤ b)
    (hL : L ≤ Chebyshev.psi a) (hU : Chebyshev.psi a ≤ U)
    (hl : l ≤ ∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n)
    (hu : (∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n) ≤ u) :
    L + l ≤ Chebyshev.psi b ∧ Chebyshev.psi b ≤ U + u := by
  have h := psi_prefix_add_interval hab
  constructor <;> linarith only [h, hL, hU, hl, hu]

/-- If `theta a` and its prime-logarithm increment on `(a, b]` have explicit lower
and upper bounds, adding the bounds certifies `theta b`. -/
theorem theta_prefix_bounds_of_interval {a b : ℕ} {L U l u : ℝ} (hab : a ≤ b)
    (hL : L ≤ Chebyshev.theta a) (hU : Chebyshev.theta a ≤ U)
    (hl : l ≤ ∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n)
    (hu : (∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n) ≤ u) :
    L + l ≤ Chebyshev.theta b ∧ Chebyshev.theta b ≤ U + u := by
  have h := theta_prefix_add_interval hab
  constructor <;> linarith only [h, hL, hU, hl, hu]

/-- Pointwise lower and upper bounds for the Mangoldt weights on `(a, b]` extend
an already bounded psi prefix at `a` to a bounded prefix at `b`. This permits
row certificates to be reused without recomputing the earlier prefix. -/
theorem psi_prefix_bounds_of_terms {a b : ℕ} {L U : ℝ} (hab : a ≤ b) (hL : L ≤ Chebyshev.psi a)
    (hU : Chebyshev.psi a ≤ U) (lo hi : ℕ → ℝ)
    (hlo : ∀ n ∈ Finset.Ioc a b, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hhi : ∀ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n ≤ hi n) :
    L + (∑ n ∈ Finset.Ioc a b, lo n) ≤ Chebyshev.psi b ∧
      Chebyshev.psi b ≤ U + (∑ n ∈ Finset.Ioc a b, hi n) := by
  exact psi_prefix_bounds_of_interval hab hL hU (Finset.sum_le_sum hlo) (Finset.sum_le_sum hhi)

/-- Pointwise lower and upper bounds for prime logarithms on `(a, b]` extend an
already bounded theta prefix at `a` to a bounded prefix at `b`. -/
theorem theta_prefix_bounds_of_terms {a b : ℕ} {L U : ℝ} (hab : a ≤ b) (hL : L ≤ Chebyshev.theta a)
    (hU : Chebyshev.theta a ≤ U) (lo hi : ℕ → ℝ)
    (hlo : ∀ n ∈ (Finset.Ioc a b).filter Nat.Prime, lo n ≤ Real.log n)
    (hhi : ∀ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n ≤ hi n) :
    L + (∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, lo n) ≤ Chebyshev.theta b ∧
      Chebyshev.theta b ≤ U + (∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, hi n) := by
  exact theta_prefix_bounds_of_interval hab hL hU (Finset.sum_le_sum hlo) (Finset.sum_le_sum hhi)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
