/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearExtension
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # Consequences of a finite linear Chebyshev certificate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A `111/100` bound for `psi` through 11723 bounds `psi - theta` by `111/50` times the
square root at every argument at least one. The five-term estimate extends the prefix bound
and the Costa-Pereira inequality bounds the higher prime-power contribution. -/
theorem psi_sub_theta_le_111_fifty_of_prefix {x : ℝ} (hx : 1 ≤ x)
    (hprefix : ∀ t : ℝ, 0 ≤ t → t ≤ 11723 → Chebyshev.psi t ≤ (111 / 100 : ℝ) * t) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (111 / 50 : ℝ) * Real.sqrt x := by
  have h :=
    psi_sub_theta_le_twice_linear_sqrt hx (by norm_num only : (0 : ℝ) ≤ 111 / 100)
      (psi_le_111_of_prefix hprefix)
  norm_num only [show (2 : ℝ) * (111 / 100) = 111 / 50 by norm_num only] at h
  exact h

/-- If the finite `psi` bound holds, twice any nonprime Mangoldt mass with weights at most
`1/3` is at most `37/25` times the square root for `x ≥ 1`. The termwise comparison
uses the conditional `psi - theta` estimate. -/
theorem composite_weight_le_37_25_of_prefix {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n ≤ 1 / 3)
    (hprefix : ∀ t : ℝ, 0 ≤ t → t ≤ 11723 → Chebyshev.psi t ≤ (111 / 100 : ℝ) * t) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      (37 / 25 : ℝ) * Real.sqrt x := by
  have ht :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      (2 / 3 : ℝ) *
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime), ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h :=
      mul_le_mul_of_nonneg_left (hw n (Finset.mem_filter.mp hn).1)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
          (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
    nlinarith only [h]
  rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime] at ht
  linarith only [ht, psi_sub_theta_le_111_fifty_of_prefix hx hprefix]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
