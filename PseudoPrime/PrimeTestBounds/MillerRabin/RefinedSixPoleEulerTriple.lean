/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerDerivatives
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleMain

/-! # Three-character refined Euler prefix comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For three characters whose real values sum to at least minus one at every
index and to three on the nonzero Mangoldt support of a finite prefix, four
times that prefix is bounded by the total refined Euler mass plus the three
signed Euler series. Nonnegative complementary terms and absolute convergence
justify retaining the full signed prefix. -/
theorem refined_six_euler_three_prefix {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) ≤
      ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n))) := by
  have hsA := refined_six_euler_signed_summable a
  have hsB := refined_six_euler_signed_summable b
  have hsC := refined_six_euler_signed_summable c
  have h :=
    (refined_six_euler_weight_summable.add ((hsA.add hsB).add hsC)).sum_le_tsum s
      (fun n _ ↦ by
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n :=
          mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
            (refined_six_euler_weight_nonneg_all n)
        have hsign := mul_le_mul_of_nonneg_right (ht n) hw
        nlinarith only [hsign])
  have he :
    (∑ n ∈ s,
        (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n)))) =
      4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : ArithmeticFunction.vonMangoldt n = 0
    · simp only [hz, zero_mul, add_zero, mul_zero]
    · have hsign :=
        congrArg (fun z : ℝ ↦ z * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n))
          (hp n hn hz)
      nlinarith only [hsign]
  rw [he] at h
  exact h

/-- If three quadratic characters equal one at every prime through a cutoff,
the refined signed Euler series retains four times any finite prefix below
that cutoff, provided their real values sum to at least minus one. Prime-power
reduction supplies the prefix condition on the nonzero Mangoldt support. -/
theorem refined_six_euler_of_prime_one {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) ≤
      ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n))) := by
  apply refined_six_euler_three_prefix a b c s ht
  intro k hk hΛ
  have h1 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
      (fun l hl hlX _ ↦ hA l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
  have h2 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
      (fun l hl hlX _ ↦ hB l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
  have h3 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
      (fun l hl hlX _ ↦ hC l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
  rw [h1, h2, h3, Complex.one_re]
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
