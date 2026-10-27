/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFullTriviality

/-! # Character sums trivial at odd primes with only even-index losses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If a character is one at odd primes through x, a nonnegative weighted
Mangoldt term has real character value at least the unsigned term minus twice
its even-index part. Odd supported terms have value one; even terms use Re chi>=-1.
This removes dependence on the ambient modulus when zero-valued witnesses are allowed. -/
theorem weighted_term_re_ge_of_odd_prime_trivial {q n : ℕ} (χ : DirichletCharacter ℂ q) {x w : ℝ}
    (hw : 0 ≤ w) (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ p = 1) (hn : (n : ℝ) ≤ x) :
    ArithmeticFunction.vonMangoldt n * w -
        2 * (if Nat.Coprime n 2 then 0 else ArithmeticFunction.vonMangoldt n * w) ≤
      (χ n).re * ArithmeticFunction.vonMangoldt n * w := by
  by_cases hz : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hz, zero_mul, mul_zero, ite_self, sub_zero, le_refl]
  · by_cases hc : Nat.Coprime n 2
    · have he :=
        character_apply_one_of_ambient_mangoldt_ne_zero (N := 2) χ
          (fun p hp hpx hpc ↦ ht p hp (Nat.coprime_two_right.mp hpc) hpx) hn hc hz
      rw [ite_eq_left hc, he, Complex.one_re, one_mul, mul_zero, sub_zero]
    · have hr := (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))).1
      have hm :=
        mul_nonneg (show 0 ≤ 1 + (χ n).re by linarith only [hr])
          (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) hw)
      rw [ite_eq_right hc]
      nlinarith only [hm]

/-- Under odd-prime triviality, nonnegative weights on a finite support through x
give a real character sum at least the unsigned sum minus twice the even-index sum.
Sum the pointwise comparison and rewrite the filter. No relation between the
character level and the excluded prime two is needed. -/
theorem weighted_sum_re_ge_of_odd_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ p = 1) (S : Finset ℕ)
    (hS : ∀ n ∈ S, (n : ℝ) ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) :
    (∑ n ∈ S, ArithmeticFunction.vonMangoldt n * w n) -
        2 * (∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n 2), ArithmeticFunction.vonMangoldt n * w n) ≤
      ∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n := by
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [ite_not]
  exact
    Finset.sum_le_sum (fun n hn ↦ weighted_term_re_ge_of_odd_prime_trivial χ (hw n hn) ht (hS n hn))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
