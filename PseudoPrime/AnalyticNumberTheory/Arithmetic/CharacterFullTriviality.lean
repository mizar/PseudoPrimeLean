/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality

/-! # Weighted sums when every small prime has character value one -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If a character is one at all primes through x, its real weighted Mangoldt
sum on any finite support through x equals the unsigned sum. Weights can have
either sign. Reduce nonzero Mangoldt terms to prime powers; zero terms vanish.
This removes nonunit losses when non-one witnesses are allowed at all primes. -/
theorem weighted_sum_re_eq_of_full_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ x)
    (w : ℕ → ℝ) :
    (∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n) =
      ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * w n := by
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hz, mul_zero, zero_mul]
  · have he :=
      character_apply_one_of_ambient_mangoldt_ne_zero (N := 1) χ (fun p hp hpx _ ↦ ht p hp hpx)
        (hS n hn) (Nat.coprime_one_right n) hz
    rw [he, Complex.one_re, one_mul]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
