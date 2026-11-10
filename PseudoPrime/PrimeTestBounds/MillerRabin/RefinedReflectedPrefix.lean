/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDualSigns
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerTriple

/-! # Reflected Euler prefix savings -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A finite prefix on which all three character values are one on the
Mangoldt support saves four times its weight in the reflected Euler bound.
Summability and the simultaneous sign estimate bound the complementary tail. -/
theorem refined_reflected_prefix {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {x : ℝ}
    (hx : 0 < x) (s : Finset ℕ) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    -(refinedReflectedEuler a x + refinedReflectedEuler b x + refinedReflectedEuler c x) ≤
      refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x -
        4 * ∑ n ∈ s, refinedDualWeight x n := by
  have hA := refined_dual_signed_summable a hx
  have hB := refined_dual_signed_summable b hx
  have hC := refined_dual_signed_summable c hx
  have hW := refined_dual_weight_summable hx
  have h :=
    (((hW.add hA).add hB).add hC).sum_le_tsum s
      (fun n _ ↦ by
        have hn := mul_le_mul_of_nonneg_right (ht n) (refined_dual_weight_nonneg x n)
        nlinarith only [hn])
  have he :
    (∑ n ∈ s,
        (refinedDualWeight x n + (a n).re * refinedDualWeight x n +
          (b n).re * refinedDualWeight x n +
          (c n).re * refinedDualWeight x n)) =
      4 * ∑ n ∈ s, refinedDualWeight x n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : ArithmeticFunction.vonMangoldt n = 0
    · simp only [refinedDualWeight, hz, zero_div, zero_mul, add_zero, mul_zero]
    · have hs := congrArg (fun z : ℝ ↦ z * refinedDualWeight x n) (hp n hn hz)
      nlinarith only [hs]
  rw [he, Summable.tsum_add ((hW.add hA).add hB) hC, Summable.tsum_add (hW.add hA) hB,
    Summable.tsum_add hW hA] at h
  rw [refined_reflected_principal_eq hx]
  unfold refinedReflectedEuler
  rw [refined_reflected_logDeriv_real a hx, refined_reflected_logDeriv_real b hx,
    refined_reflected_logDeriv_real c hx]
  linarith only [h]

/-- Prime-level triviality through a cutoff gives the reflected Euler saving
for every finite set below that cutoff. Reduction to prime powers supplies
character triviality on the nonzero Mangoldt support. -/
theorem refined_reflected_of_prime_one {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {x X : ℝ}
    (hx : 0 < x) (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    -(refinedReflectedEuler a x + refinedReflectedEuler b x + refinedReflectedEuler c x) ≤
      refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x -
        4 * ∑ n ∈ s, refinedDualWeight x n := by
  apply refined_reflected_prefix a b c hx s ht
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

/-- The three contour remainders retain the finite reflected Euler saving.
The inverse characters have the same real values, so their prefix condition
is inherited from the original characters. -/
theorem refined_contour_prefix {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (s : Finset ℕ) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
        (refinedContourRemainder c x).re ≤
      refinedContourNonEuler a x + refinedContourNonEuler b x + refinedContourNonEuler c x +
          refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x -
        4 * ∑ n ∈ s, refinedDualWeight x n := by
  have hA := refined_contour_split_real hpA hnA hiA hx
  have hB := refined_contour_split_real hpB hnB hiB hx
  have hC := refined_contour_split_real hpC hnC hiC hx
  have htInv : ∀ n : ℕ, -1 ≤ (a⁻¹ n).re + (b⁻¹ n).re + (c⁻¹ n).re := by
    intro n
    simpa only [refined_inv_char_re] using ht n
  have hpInv :
    ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a⁻¹ n).re + (b⁻¹ n).re + (c⁻¹ n).re = 3 := by
    intro n hn hΛ
    simpa only [refined_inv_char_re] using hp n hn hΛ
  have h := refined_reflected_prefix a⁻¹ b⁻¹ c⁻¹ hx s htInv hpInv
  linarith only [hA, hB, hC, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
