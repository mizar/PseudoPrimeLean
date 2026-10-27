/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPrimePowerCosts
public import Mathlib.Data.Nat.PrimeFin

/-! # Arithmetic conductor budget for the joint Gamma local costs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive integer conductor, the sum of logarithms of its distinct
prime factors is at most its logarithm. Their product divides the conductor;
take logarithms after proving positivity. This supplies the actual arithmetic
budget for the signed Euler and ramp costs. -/
theorem gamma_conductor_prime_log_budget {q : ℕ} (hq : 0 < q) :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  have hpos : 0 < ∏ p ∈ q.primeFactors, p :=
    Finset.prod_pos (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos)
  have hreal : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by exact_mod_cast hpos
  have hne (p : ℕ) (hp : p ∈ q.primeFactors) : (p : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Real.log_prod hne, ← Nat.cast_prod]
  exact Real.log_le_log hreal (by exact_mod_cast (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)))

/-- Any finite subset of the conductor's distinct prime factors obeys the
same logarithmic budget. Missing primes have nonnegative logarithms, so the
subset sum is bounded by the full prime-factor sum. This supports filtered
ramified sets, including the odd-prime set with the dyadic term separated. -/
theorem gamma_conductor_subset_log_budget {q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hS : S ⊆ q.primeFactors) : (∑ p ∈ S, Real.log p) ≤ Real.log q := by
  have h : (∑ p ∈ S, Real.log p) ≤ ∑ p ∈ q.primeFactors, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun p hp hnot ↦
        Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  exact h.trans (gamma_conductor_prime_log_budget hq)

/-- For positive conductor q and a subset of its prime factors, actual finite
Euler prime-power losses and ramp costs share the arithmetic budget log q.
The prime-factor subset supplies both primality and the budget, discharging
the abstract budget hypothesis of the joint local comparison. -/
theorem gamma_conductor_joint_cost_le_dual_cap {q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hS : S ⊆ q.primeFactors) (K : ℕ → Finset ℕ) (Ramp : ℕ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    (∑ p ∈ S, ((∑ k ∈ K p, gammaResolventMangoldtWeight (p ^ (k + 1))) + Real.log p * Ramp p)) ≤
      μ * Real.log q + ∑ p ∈ S, Real.log p * max (gammaPrimeEulerCost p + Ramp p - μ) 0 := by
  exact
    gamma_primePower_joint_cost_le_dual_cap S K Ramp hμ
      (fun p hp ↦ Nat.prime_of_mem_primeFactors (hS hp)) (gamma_conductor_subset_log_budget hq S hS)

end PseudoPrime.Analysis
