/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.EvenCoprimeSingleSupport
public import PseudoPrime.Analysis.FiniteLinearBudget

/-! # Prime-factor logarithmic budgets retaining exceptional local costs -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- Sum the exact coupled local term over positive powers of the supplied
prime base, retaining the cutoff. Inputs are a character, root and base.
The function is defined for arbitrary bases; only prime divisors are used
by the budget theorem. This groups cancellation before bounding the tail. -/
noncomputable def evenCoprimePrimeCost {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊,
    if p ≤ ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ then evenCoprimeSupportTerm χ y (p ^ k) else 0

/-- For a nonzero level, the exact local cost is the sum of the grouped
prime costs over its distinct prime divisors. Extend each exponent's prime
support by zero and commute finite sums. This supplies the logarithmic budget. -/
theorem evenCoprimeLocalCost_eq_sum_primeFactors {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (y : ℝ) : evenCoprimeLocalCost χ y = ∑ p ∈ q.primeFactors, evenCoprimePrimeCost χ y p := by
  classical
  rw [evenCoprimeLocalCost_eq_prime_powers]
  symm
  unfold evenCoprimePrimeCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_filter]
  have hs :
    q.primeFactors.filter (fun p ↦ p ≤ ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊) =
      (Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊).filter (fun p ↦ p.Prime ∧ p ∣ q) := by
    ext p
    constructor
    · intro hp
      have h := Finset.mem_filter.mp hp
      have ht := (Nat.mem_primeFactors_of_ne_zero hq).mp h.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨ht.1.pos, h.2⟩, ht⟩
    · intro hp
      have h := Finset.mem_filter.mp hp
      exact
        Finset.mem_filter.mpr
          ⟨(Nat.mem_primeFactors_of_ne_zero hq).mpr h.2, (Finset.mem_Ioc.mp h.1).2⟩
  rw [hs]

/-- Given nonzero level, a>=0, and tail prime costs at most a*log p outside
finite T, the local cost is at most a*log q plus positive excesses on T.
Use the exact prime-factor decomposition and the finite linear-budget lemma.
This retains small-prime cancellations instead of counting all prime factors. -/
theorem evenCoprimeLocalCost_le_primeBudget {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (y : ℝ) (T : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (htail : ∀ p ∈ q.primeFactors, p ∉ T → evenCoprimePrimeCost χ y p ≤ a * Real.log p) :
    evenCoprimeLocalCost χ y ≤
      a * Real.log q + ∑ p ∈ T, max 0 (evenCoprimePrimeCost χ y p - a * Real.log p) := by
  rw [evenCoprimeLocalCost_eq_sum_primeFactors hq]
  exact
    Analysis.finite_sum_le_linear_budget_add_excess q.primeFactors T
      (fun p ↦ evenCoprimePrimeCost χ y p) (fun p ↦ Real.log p) ha
      (AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log hq) htail

end PseudoPrime.LLS.Extensions
