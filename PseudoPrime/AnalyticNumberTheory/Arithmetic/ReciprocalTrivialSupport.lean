/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalWeightedLowerBound

/-! # Reciprocal character sums under prime triviality at arbitrary cutoffs -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- At a positive cutoff, if the character is one on every prime within the cutoff
not dividing its level, a reciprocal summand equals the unsigned summand on
coprime inputs and is zero otherwise. Reduce nonzero Mangoldt terms to prime powers.
This identifies the exact support without a fixed LLS radius. -/
theorem characterReciprocalWeightedTerm_re_eq_ite_of_prime_trivial {q n : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    (characterReciprocalWeightedTerm x χ n).re =
      if Nat.Coprime n q then reciprocalWeightedMangoldtTerm x n else 0 := by
  by_cases hcop : Nat.Coprime n q
  · rw [ite_eq_left hcop]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [characterReciprocalWeightedTerm, reciprocalWeightedMangoldtTerm, hΛ, zero_div, zero_mul]
      norm_num only [Complex.ofReal_zero, zero_mul, Complex.zero_re]
    · obtain ⟨p, k, hp, hk, rfl⟩ :=
        (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpdiv : p ∣ p ^ k := dvd_pow_self p hk.ne'
      have hpcop : Nat.Coprime p q := hcop.of_dvd_left hpdiv
      have hpbound : (p : ℝ) ≤ x := by
        have hpowFloor := (Finset.mem_Ioc.mp hn).2
        have hpPow : p ≤ p ^ k := Nat.le_pow hk
        exact
          (show (p : ℝ) ≤ (p ^ k : ℕ) by exact_mod_cast hpPow).trans
            ((Nat.le_floor_iff hx.le).mp hpowFloor)
      have hpvalue : χ p = 1 := htrivial p hp (hp.coprime_iff_not_dvd.mp hpcop) hpbound
      rw [characterReciprocalWeightedTerm]
      simp only [Nat.cast_pow, map_pow, hpvalue, one_pow, mul_one, Complex.ofReal_re]
  · rw [ite_eq_right hcop]
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
    rw [characterReciprocalWeightedTerm, hχzero, mul_zero, Complex.zero_re]

/-- Under prime triviality up to a positive cutoff, the reciprocal character sum
has real part equal to the coprime unsigned sum. Sum the termwise support identity
and combine the conditional terms as a filtered sum. This supplies arbitrary-cutoff
level comparisons without imposing a conductor-prime-support condition. -/
theorem characterReciprocalWeightedSum_re_eq_coprime_of_prime_trivial {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    (characterReciprocalWeightedSum x χ).re =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.Coprime n q,
        reciprocalWeightedMangoldtTerm x n := by
  rw [characterReciprocalWeightedSum]
  simp only [Complex.re_sum]
  trans ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if Nat.Coprime n q then reciprocalWeightedMangoldtTerm x n else 0
  · apply Finset.sum_congr rfl
    intro n hn
    exact characterReciprocalWeightedTerm_re_eq_ite_of_prime_trivial x χ hx hn htrivial
  · rw [← Finset.sum_filter]

/-- Under prime triviality at a positive cutoff, the reciprocal character sum is
at least the unsigned sum minus the level prime-factor logarithmic cost.
Split off the common-factor terms and apply their uniform upper bound.
This preserves the level loss at any cutoff used in a no-witness argument. -/
theorem characterReciprocalWeightedSum_re_lower_level_of_prime_trivial {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    reciprocalWeightedMangoldtSum x - primeFactorLogSum q ≤
      (characterReciprocalWeightedSum x χ).re := by
  have horiginal := characterReciprocalWeightedSum_re_eq_coprime_of_prime_trivial x χ hx htrivial
  have hsplit := reciprocalWeightedMangoldtSum_eq_coprime_add_common x q
  have hcommon := commonFactorReciprocalWeightedSum_le (NeZero.ne q) hx
  linarith only [horiginal, hsplit, hcommon]

/-- Under prime triviality up to a positive cutoff, the reciprocal character sum
has nonnegative real part. Its coprime unsigned support consists of nonnegative terms.
This permits a maximum with zero in the lower input for character comparisons. -/
theorem characterReciprocalWeightedSum_re_nonneg_of_prime_trivial {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    0 ≤ (characterReciprocalWeightedSum x χ).re := by
  rw [characterReciprocalWeightedSum_re_eq_coprime_of_prime_trivial x χ hx htrivial]
  apply Finset.sum_nonneg
  intro n hn
  have hnIoc := (Finset.mem_filter.mp hn).1
  exact
    reciprocalWeightedMangoldtTerm_nonneg hx (Finset.mem_Ioc.mp hnIoc).1 (Finset.mem_Ioc.mp hnIoc).2

/-- Under RH and prime triviality up to x≥2, the reciprocal character sum is at
least max(0,log(x)-32873/20800-primeFactorLogSum(q)). Combine the refined unsigned
lower bound with the exact level support and nonnegativity.
This is the sharpened reciprocal input at a freely chosen no-witness cutoff. -/
theorem characterReciprocalWeightedSum_re_ge_refined_lower_bound {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hRH : RiemannHypothesis)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    max 0 (Real.log x - (32873 / 20800 : ℝ) - primeFactorLogSum q) ≤
      (characterReciprocalWeightedSum x χ).re := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  apply max_le
  · exact characterReciprocalWeightedSum_re_nonneg_of_prime_trivial x χ hx0 htrivial
  · have hlower := characterReciprocalWeightedSum_re_lower_level_of_prime_trivial x χ hx0 htrivial
    have hr := RiemannZeta.reciprocalWeightedMangoldtSum_lower_bound hRH hx
    linarith only [hlower, hr]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
