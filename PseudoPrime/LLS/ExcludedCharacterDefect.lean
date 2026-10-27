/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointTwoCostWitness

/-! # Exact excluded-support defects for endpoint witness budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a character, exclusion modulus N, finite support S and real weights w,
sum (1-Re chi(n))*w(n) only on indices noncoprime to N. No positivity is
assumed in the definition; exact values retain cancellation at character value one. -/
noncomputable def excludedCharacterDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n N), (1 - (χ n).re) * w n

/-- If all N-coprime primes through b have character value one, S lies below b
and w vanishes off Mangoldt support, the full weighted character defect equals
the excluded-support defect. Split coprimality and zero Mangoldt values exactly. -/
theorem weighted_defect_eq_excluded_of_ambient_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ S, w n) - (∑ n ∈ S, (χ n).re * w n) = excludedCharacterDefect χ N S w := by
  rw [← Finset.sum_sub_distrib, excludedCharacterDefect, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : Nat.Coprime n N
  · rw [ite_eq_right (not_not_intro hc)]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [hw n hn hΛ]
      ring
    · rw [character_apply_one_of_ambient_mangoldt_ne_zero χ ht (hS n hn) hc hΛ, Complex.one_re]
      ring
  · rw [ite_eq_left hc]
    ring

/-- At nonnegative Y under N-coprime prime triviality, the unsigned reciprocal
sum minus the real character sum equals the excluded reciprocal defect.
Apply the weighted identity; no conductor divisibility or quadraticity is needed. -/
theorem reciprocal_defect_eq_excluded_of_ambient_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {Y : ℝ} (hY : 0 ≤ Y) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → Nat.Coprime p N → χ p = 1) :
    reciprocalWeightedMangoldtSum Y - (characterReciprocalWeightedSum Y χ).re =
      excludedCharacterDefect χ N (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) := by
  have he :=
    weighted_defect_eq_excluded_of_ambient_trivial χ (Finset.Ioc 0 ⌊Y⌋₊)
      (reciprocalWeightedMangoldtTerm Y)
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hY))
      (fun n _ hΛ ↦ by simp only [reciprocalWeightedMangoldtTerm, hΛ, zero_div, zero_mul]) ht
  unfold reciprocalWeightedMangoldtSum characterReciprocalWeightedSum
    characterReciprocalWeightedTerm
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  simpa only [mul_comm] using he

/-- At nonnegative x under N-coprime prime triviality, the logarithmic character
defect equals the excluded logarithmic defect. This retains the exact character
values at excluded prime powers before applying any upper estimate. -/
theorem logarithmic_defect_eq_excluded_of_ambient_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 ≤ x) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) :
    logWeightedMangoldtSum x - (characterLogWeightedSum x χ).re =
      excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) := by
  have he :=
    weighted_defect_eq_excluded_of_ambient_trivial χ (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x)
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx))
      (fun n _ hΛ ↦ by simp only [logWeightedMangoldtTerm, hΛ, zero_mul]) ht
  unfold logWeightedMangoldtSum characterLogWeightedSum characterLogWeightedTerm
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  simpa only [mul_comm] using he

/-- For nonnegative weights on S, the excluded defect is nonnegative.
Character real parts are at most one; multiply nonnegative factors and sum. -/
theorem excludedCharacterDefect_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (S : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) : 0 ≤ excludedCharacterDefect χ N S w := by
  apply Finset.sum_nonneg
  intro n hn
  exact
    mul_nonneg (sub_nonneg.mpr ((Complex.re_le_norm (χ n)).trans (χ.norm_le_one n)))
      (hw n (Finset.mem_filter.mp hn).1)

/-- Increasing the real weight on S increases the excluded defect, because
1-Re chi(n) is nonnegative. This permits termwise arithmetic upper budgets. -/
theorem excludedCharacterDefect_mono_weight {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (S : Finset ℕ) (w v : ℕ → ℝ) (hw : ∀ n ∈ S, w n ≤ v n) :
    excludedCharacterDefect χ N S w ≤ excludedCharacterDefect χ N S v := by
  apply Finset.sum_le_sum
  intro n hn
  exact
    mul_le_mul_of_nonneg_left (hw n (Finset.mem_filter.mp hn).1)
      (sub_nonneg.mpr ((Complex.re_le_norm (χ n)).trans (χ.norm_le_one n)))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
