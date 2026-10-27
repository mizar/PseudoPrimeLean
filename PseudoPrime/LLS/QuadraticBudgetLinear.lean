/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticExcludedPrimeBudget

/-! # Linear structural exclusion budgets and a retained prime contribution -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For arbitrary real coefficients and weights, the structural quadratic
budget is linear in its weight. Distribute the finite sum. This retains a
finite taper subtraction before applying upper estimates. -/
theorem quadraticExcludedBudget_linear_weight (q N : ℕ) (S : Finset ℕ) (w v : ℕ → ℝ) (a b : ℝ) :
    quadraticExcludedBudget q N S (fun n ↦ a * w n + b * v n) =
      a * quadraticExcludedBudget q N S w + b * quadraticExcludedBudget q N S v := by
  unfold quadraticExcludedBudget
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- For a nonnegative weight on the support, the structural quadratic budget
is nonnegative. Every structural coefficient is zero, one or two. This supplies
positivity when preserving selected excluded prime contributions. -/
theorem quadraticExcludedBudget_nonneg (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) : 0 ≤ quadraticExcludedBudget q N S w := by
  apply Finset.sum_nonneg
  intro n hn
  have h := hw n (Finset.mem_filter.mp hn).1
  split_ifs
  · exact mul_nonneg (by norm_num only) h
  · exact mul_nonneg (by norm_num only) h
  · exact mul_nonneg (by norm_num only) h

/-- If a prime p divides N and belongs to S, the structural Mangoldt budget
is at least log p. Its coefficient is one at level nonunits and two otherwise,
because a prime is not square. Other contributions are nonnegative. This gives
a positive saving from any retained excluded prime, independently of the character. -/
theorem log_prime_le_quadraticExcludedBudget {p : ℕ} (hp : p.Prime) (q N : ℕ) (S : Finset ℕ)
    (hS : p ∈ S) (hpN : p ∣ N) :
    Real.log p ≤ quadraticExcludedBudget q N S ArithmeticFunction.vonMangoldt := by
  have hns : ¬IsSquare p := by
    intro hs
    have he : Even (1 : ℕ) := (isSquare_prime_pow_iff_even hp).mp (by simpa only [pow_one] using hs)
    exact (by decide : ¬Even (1 : ℕ)) he
  have hmem : p ∈ S.filter (fun n ↦ ¬Nat.Coprime n N) :=
    Finset.mem_filter.mpr ⟨hS, fun hc ↦ (hp.coprime_iff_not_dvd.mp hc) hpN⟩
  have hb :
    (if Nat.Coprime p q then if IsSquare p then 0 else 2 else 1) *
        ArithmeticFunction.vonMangoldt p ≤
      quadraticExcludedBudget q N S ArithmeticFunction.vonMangoldt := by
    apply Finset.single_le_sum _ hmem
    intro n _
    split_ifs
    · exact mul_nonneg (by norm_num only) ArithmeticFunction.vonMangoldt_nonneg
    · exact mul_nonneg (by norm_num only) ArithmeticFunction.vonMangoldt_nonneg
    · exact mul_nonneg (by norm_num only) ArithmeticFunction.vonMangoldt_nonneg
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at hb
  by_cases hc : Nat.Coprime p q
  · rw [ite_eq_left hc, ite_eq_right hns] at hb
    have hl : 0 ≤ Real.log p := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le)
    linarith only [hb, hl]
  · rw [ite_eq_right hc, one_mul] at hb
    exact hb

/-- For a finite set T of excluded primes lying in S, their logarithm sum is
at most the structural Mangoldt budget. Each prime has coefficient at least
one, and all remaining contributions are nonnegative. This supplies a reusable
lower bound retaining several excluded primes in the finite taper saving. -/
theorem sum_log_primes_le_quadraticExcludedBudget (q N : ℕ) (S T : Finset ℕ) (hTS : T ⊆ S)
    (hprime : ∀ p ∈ T, p.Prime) (hdiv : ∀ p ∈ T, p ∣ N) :
    (∑ p ∈ T, Real.log p) ≤ quadraticExcludedBudget q N S ArithmeticFunction.vonMangoldt := by
  let f := fun n : ℕ ↦
    (if Nat.Coprime n q then if IsSquare n then 0 else 2 else 1) * ArithmeticFunction.vonMangoldt n
  have hsub : T ⊆ S.filter (fun n ↦ ¬Nat.Coprime n N) := by
    intro p hp
    exact
      Finset.mem_filter.mpr ⟨hTS hp, fun hc ↦ ((hprime p hp).coprime_iff_not_dvd.mp hc) (hdiv p hp)⟩
  have hm : (∑ p ∈ T, f p) ≤ quadraticExcludedBudget q N S ArithmeticFunction.vonMangoldt := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n _ _
    dsimp only [f]
    split_ifs
    · exact mul_nonneg (by norm_num only) ArithmeticFunction.vonMangoldt_nonneg
    · exact mul_nonneg (by norm_num only) ArithmeticFunction.vonMangoldt_nonneg
    · exact mul_nonneg (by norm_num only) ArithmeticFunction.vonMangoldt_nonneg
  have hl : (∑ p ∈ T, Real.log p) ≤ ∑ p ∈ T, f p := by
    apply Finset.sum_le_sum
    intro p hp
    have hpr := hprime p hp
    have hns : ¬IsSquare p := by
      intro hs
      have he : Even (1 : ℕ) :=
        (isSquare_prime_pow_iff_even hpr).mp (by simpa only [pow_one] using hs)
      exact (by decide : ¬Even (1 : ℕ)) he
    dsimp only [f]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpr]
    by_cases hc : Nat.Coprime p q
    · rw [ite_eq_left hc, ite_eq_right hns]
      have hp0 : 0 ≤ Real.log p := Real.log_nonneg (Nat.one_le_cast.mpr hpr.one_le)
      linarith only [hp0]
    · rw [ite_eq_right hc, one_mul]
  exact hl.trans hm

end PseudoPrime.AnalyticNumberTheory.Arithmetic
