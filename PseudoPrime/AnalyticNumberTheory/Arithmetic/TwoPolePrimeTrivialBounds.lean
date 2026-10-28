/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GeneralTwoPoleGammaWitness

/-! # Character-free two-pole bounds under full prime triviality -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If every prime through the cutoff has character value one, every weighted
Mangoldt defect below that cutoff vanishes, for any exclusion modulus. Reduce each
nonzero term to a prime power. This eliminates a character-dependent exclusion
budget under the universal-prime-pass contradiction used for Miller-Rabin. -/
theorem excludedCharacterDefect_eq_zero_of_all_prime_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) : excludedCharacterDefect χ N S w = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hmem := (Finset.mem_filter.mp hn).1
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · rw [hw n hmem hΛ, mul_zero]
  · have he :=
      character_apply_one_of_ambient_mangoldt_ne_zero (N := 1) χ (fun p hp hb _ ↦ ht p hp hb)
        (hS n hmem) (Nat.coprime_one_right n) hΛ
    rw [he, Complex.one_re, sub_self, zero_mul]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
