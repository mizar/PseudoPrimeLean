/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.QuadraticExcludedPrimeBudget
public import PseudoPrime.LLS.GammaQuadraticLocalCorrection
public import PseudoPrime.Analysis.AlternatingPrefixBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PairedEulerConductorBudget

/-! # Alternating prime-power cancellation and conductor-sensitive exclusion budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A level prime coprime to the conductor divides the conductor quotient. Factor the level
as conductor times quotient and use primality. This locates every unramified exclusion charge
inside the conductor logarithmic saving. -/
theorem coprime_level_prime_mem_quotientFactors {q p : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : p ∈ q.primeFactors) (hc : Nat.Coprime p χ.conductor) :
    p ∈ (q / χ.conductor).primeFactors := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  rw [← AnalyticNumberTheory.DirichletLFunction.conductor_mul_quotient χ] at hd
  have hquot := (hprime.dvd_mul.mp hd).resolve_left (hprime.coprime_iff_not_dvd.mp hc)
  exact
    Nat.mem_primeFactors.mpr
      ⟨hprime, hquot, (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ).ne'⟩

/-- For a character of nonzero level, the sum of logarithms of level primes coprime to the
conductor is at most the logarithm of the conductor quotient. Include these primes among the
quotient factors and apply the radical logarithm bound. No witness hypothesis is required. -/
theorem sum_log_unramified_level_primes_le_log_quotient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ q.primeFactors.filter (fun p ↦ Nat.Coprime p χ.conductor), Real.log p) ≤
      Real.log (q / χ.conductor : ℕ) := by
  have hsub :
    q.primeFactors.filter (fun p ↦ Nat.Coprime p χ.conductor) ⊆ (q / χ.conductor).primeFactors := by
    intro p hp
    exact
      coprime_level_prime_mem_quotientFactors χ (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p hp _ ↦
            Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_le))).trans
      (AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log
        (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ).ne')

/-- For nonnegative a and d, suppose each prime weight is at most a log p with the additional
allowance d only at two. Then the sum over unramified level primes is at most a times the
conductor-quotient logarithm plus d. Sum the scalar estimates and charge two at most once. This
separates a reusable conductor cost from a fixed exceptional-prime allowance. -/
theorem unramified_weight_sum_le_conductor_budget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (w : ℕ → ℝ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hw : ∀ p : ℕ, p.Prime → w p ≤ a * Real.log p + if p = 2 then d else 0) :
    (∑ p ∈ q.primeFactors, if Nat.Coprime p χ.conductor then w p else 0) ≤
      a * Real.log (q / χ.conductor : ℕ) + d := by
  classical
  rw [← Finset.sum_filter]
  let F := q.primeFactors.filter (fun p ↦ Nat.Coprime p χ.conductor)
  have hs : (∑ p ∈ F, w p) ≤ ∑ p ∈ F, (a * Real.log p + if p = 2 then d else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hw p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'] at hs
  have he : (if 2 ∈ F then d else 0) ≤ d := by
    split_ifs
    · exact le_refl _
    · exact hd
  have hl := mul_le_mul_of_nonneg_left (sum_log_unramified_level_primes_le_log_quotient χ) ha
  exact hs.trans (add_le_add hl he)

/-- For a nonzero character level and Y at least one, assume a nonnegative prime-power weight
decreasing on positive powers and bounded at primes by a log p plus a nonnegative allowance d
at two. The quadratic exclusion budget is at most the full prefix plus a log of the conductor
quotient and d. Combine alternating cancellation with the quotient prime-factor bound. This
is the conductor-sensitive interface for negative-witness comparisons. -/
theorem quadraticExcludedBudget_le_prefix_add_conductor_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hs : ∀ n : ℕ, ¬IsPrimePow n → w n = 0)
    (hdec : ∀ p : ℕ, p.Prime → Antitone (fun j : ℕ ↦ w (p ^ (j + 1)))) {a d : ℝ} (ha : 0 ≤ a)
    (hd : 0 ≤ d) (hprime : ∀ p : ℕ, p.Prime → w p ≤ a * Real.log p + if p = 2 then d else 0) :
    AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor q (Finset.Ioc 0 ⌊Y⌋₊) w ≤
      (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, w n) + a * Real.log (q / χ.conductor : ℕ) + d := by
  have hbase :=
    AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget_le_prefix_add_unramified (NeZero.ne q)
      χ.conductor hY w hw hs hdec
  have hquot := unramified_weight_sum_le_conductor_budget χ w ha hd hprime
  linarith only [hbase, hquot]

end PseudoPrime.LLS
