/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds

/-! # Untwisted Mangoldt prefixes under prime-character triviality -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If a character takes value one at each prime up to b, it takes value one at every
index n<=b with nonzero von Mangoldt value. Decompose n as a positive prime power.
This transfers prime witness nonexistence to arbitrary Mangoldt-weighted supports. -/
theorem character_apply_one_of_mangoldt_ne_zero {q n : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) (hn : (n : ℝ) ≤ b)
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
  obtain ⟨p, r, hp, hr, rfl⟩ :=
    (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hpb : (p : ℝ) ≤ b := (show (p : ℝ) ≤ (p ^ r : ℕ) by exact_mod_cast Nat.le_pow hr).trans hn
  simp only [Nat.cast_pow, map_pow, hsmall p hp hpb, one_pow]

/-- For any finite set of indices bounded by b and any real weights, prime triviality
through b makes the positive character prefix equal twice the untwisted prefix.
The Mangoldt-zero terms vanish and all other character values equal one.
No sign restriction on the weights, GRH, or primitivity is needed. -/
theorem character_positive_mangoldt_prefix_eq_twice {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    (∑ n ∈ S, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) =
      2 * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * w n := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, zero_mul]
  · rw [character_apply_one_of_mangoldt_ne_zero χ hsmall (hS n hn) hΛ, Complex.one_re]
    ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic
