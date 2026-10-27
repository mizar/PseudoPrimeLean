/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.EvenCoprimeCoupledComparison

/-! # One-support local costs with exact primitive-character cancellation -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- For an arbitrary character, finite set and real weight, the primitive
sum on conductor-quotient support equals its sum on level support.
Outside the quotient support the two characters agree, and the level character
vanishes. This removes a second support set without a triangle inequality. -/
theorem primitive_quotient_support_sum_eq_level_support {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ s.filter (fun n ↦ ¬Nat.Coprime n (q / χ.conductor)), w n * (χ.primitiveCharacter n).re) =
      (∑ n ∈ s.filter (fun n ↦ ¬Nat.Coprime n q), w n * (χ.primitiveCharacter n).re) := by
  apply Finset.sum_subset
  · intro n hn
    have h := Finset.mem_filter.mp hn
    exact
      Finset.mem_filter.mpr
        ⟨h.1, fun hc ↦ h.2 (hc.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level))⟩
  · intro n hn hnot
    have h := Finset.mem_filter.mp hn
    have hquot : Nat.Coprime n (q / χ.conductor) := by
      by_contra hc
      exact hnot (Finset.mem_filter.mpr ⟨h.1, hc⟩)
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using h.2)
    have hp : χ.primitiveCharacter n = 0 :=
      (AnalyticNumberTheory.Arithmetic.apply_eq_primitiveCharacter_of_coprime_quotient χ
            hquot).symm.trans
        hχzero
    rw [hp, Complex.zero_re, mul_zero]

/-- For an arbitrary character and root, the coupled local cost is a single
sum on level support, with factor 1-Re(primitive character).
Move the correction to the same support and combine the weights.
This retains cancellation before any prime-power upper bound. -/
theorem evenCoprimeLocalCost_eq_single_support {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    evenCoprimeLocalCost χ y =
      ∑ n ∈ (Finset.Ioc 0 ⌊y ^ 2⌋₊).filter (fun n ↦ ¬Nat.Coprime n q),
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (y ^ 2) n +
            evenCoprimeReciprocalMultiplier y *
              AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm (y ^ 2) n) *
          (1 - (χ.primitiveCharacter n).re) := by
  rw [evenCoprimeLocalCost_eq_coupled_sums]
  have hc :=
    primitive_quotient_support_sum_eq_level_support χ (Finset.Ioc 0 ⌊y ^ 2⌋₊)
      (fun n ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (y ^ 2) n +
          evenCoprimeReciprocalMultiplier y *
            AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm (y ^ 2) n)
  simp only [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm,
    AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm, Complex.re_ofReal_mul]
  simp only [add_mul, mul_assoc] at hc
  rw [hc, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The logarithmic Mangoldt weight plus the reciprocal weight multiplied
by the even-comparison coefficient, at root y and natural index n.
This common real weight is nonnegative in the analytic range and vanishes
off prime powers. It is used to bound both local costs together. -/
noncomputable def evenCoprimeSupportWeight (y : ℝ) (n : ℕ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (y ^ 2) n +
    evenCoprimeReciprocalMultiplier y *
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm (y ^ 2) n

/-- The combined support weight times 1-Re(primitive character at n).
Inputs are a level character, root and natural index. This is the exact local
cost summand; primitive value one cancels instead of contributing a norm loss. -/
noncomputable def evenCoprimeSupportTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) (n : ℕ) : ℝ :=
  evenCoprimeSupportWeight y n * (1 - (χ.primitiveCharacter n).re)

/-- If the primitive character at n equals one, the combined support term
vanishes at every root. Substitute the character value.
This removes those indices from every local budget. -/
theorem evenCoprimeSupportTerm_of_one {q n : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (hn : χ.primitiveCharacter n = 1) : evenCoprimeSupportTerm χ y n = 0 := by
  rw [evenCoprimeSupportTerm, hn, Complex.one_re, sub_self, mul_zero]

/-- If the primitive value at p is minus one and k is even, its p^k support
cost vanishes. Use multiplicativity and even powers of minus one.
No primality assumption is needed. This retains even-power cancellation. -/
theorem evenCoprimeSupportTerm_even_power {q p k : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (hp : χ.primitiveCharacter p = -1) (hk : Even k) : evenCoprimeSupportTerm χ y (p ^ k) = 0 := by
  unfold evenCoprimeSupportTerm
  rw [Nat.cast_pow, map_pow, hp, hk.neg_one_pow, Complex.one_re, sub_self, mul_zero]

/-- If the primitive value at p is minus one and k is odd, its p^k support
cost is twice the common weight. Use multiplicativity and odd powers.
This identifies exactly the powers remaining after even-power cancellation. -/
theorem evenCoprimeSupportTerm_odd_power {q p k : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (hp : χ.primitiveCharacter p = -1) (hk : Odd k) :
    evenCoprimeSupportTerm χ y (p ^ k) = 2 * evenCoprimeSupportWeight y (p ^ k) := by
  unfold evenCoprimeSupportTerm
  rw [Nat.cast_pow, map_pow, hp, hk.neg_one_pow, Complex.neg_re, Complex.one_re]
  ring

/-- At y>=8 and 0<n<=floor(y^2), the common support weight is nonnegative.
Combine the two Mangoldt weight bounds and positive multiplier.
This allows termwise upper bounds while preserving the shared support. -/
theorem evenCoprimeSupportWeight_nonneg {y : ℝ} (hy : (8 : ℝ) ≤ y) {n : ℕ}
    (hn : n ∈ Finset.Ioc 0 ⌊y ^ 2⌋₊) : 0 ≤ evenCoprimeSupportWeight y n := by
  have hx : (0 : ℝ) < y ^ 2 := lt_of_lt_of_le (by norm_num only) (Analysis.sq_ge_64_of_ge_8 hy)
  have h := Finset.mem_Ioc.mp hn
  exact
    add_nonneg (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg hx h.1 h.2)
      (mul_nonneg (evenCoprimeReciprocalMultiplier_pos hy).le
        (AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_nonneg hx h.1 h.2))

/-- At y>=8 and a positive index through the cutoff, every support term
is nonnegative. Bound the primitive real part by its norm and then one.
This exposes the nonnegative prime-power cost of the coprime comparison. -/
theorem evenCoprimeSupportTerm_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) {y : ℝ}
    (hy : (8 : ℝ) ≤ y) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊y ^ 2⌋₊) :
    0 ≤ evenCoprimeSupportTerm χ y n := by
  have hc : (χ.primitiveCharacter n).re ≤ 1 :=
    (Complex.re_le_norm _).trans (DirichletCharacter.norm_le_one _ _)
  exact mul_nonneg (evenCoprimeSupportWeight_nonneg hy hn) (sub_nonneg.mpr hc)

/-- At arbitrary root and character, rewrite the coupled cost as the sum
of the new support terms. This is the definition-level interface used by
positivity and cancellation lemmas after the exact support transport. -/
theorem evenCoprimeLocalCost_eq_support_terms {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    evenCoprimeLocalCost χ y =
      ∑ n ∈ (Finset.Ioc 0 ⌊y ^ 2⌋₊).filter (fun n ↦ ¬Nat.Coprime n q),
        evenCoprimeSupportTerm χ y n := by
  exact evenCoprimeLocalCost_eq_single_support χ y

/-- For an arbitrary character and root y>=8, the exact coupled local cost
is nonnegative. Sum the nonnegative single-support terms.
No no-witness assumption or quadratic-character assumption is required. -/
theorem evenCoprimeLocalCost_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) {y : ℝ}
    (hy : (8 : ℝ) ≤ y) : 0 ≤ evenCoprimeLocalCost χ y := by
  rw [evenCoprimeLocalCost_eq_support_terms]
  apply Finset.sum_nonneg
  intro n hn
  exact evenCoprimeSupportTerm_nonneg χ hy (Finset.mem_filter.mp hn).1

/-- At arbitrary root, discard all indices whose primitive value is one
from the coupled local cost. Their support terms vanish identically.
This is the reduced finite ledger passed to quantitative witness budgets. -/
theorem evenCoprimeLocalCost_eq_filtered_support {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    evenCoprimeLocalCost χ y =
      ∑
        n ∈
          ((Finset.Ioc 0 ⌊y ^ 2⌋₊).filter (fun n ↦ ¬Nat.Coprime n q)).filter
            (fun n : ℕ ↦ χ.primitiveCharacter n ≠ 1),
        evenCoprimeSupportTerm χ y n := by
  rw [evenCoprimeLocalCost_eq_support_terms]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hval : χ.primitiveCharacter n = 1 := by
    by_contra hv
    exact hnot (Finset.mem_filter.mpr ⟨hn, hv⟩)
  exact evenCoprimeSupportTerm_of_one χ y hval

/-- If the primitive value at p is zero and k is nonzero, the support term
at p^k equals the common weight. Use multiplicativity and a positive power
of zero. This is the ramified case of the quadratic local-cost ledger. -/
theorem evenCoprimeSupportTerm_zero_power {q p k : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (hp : χ.primitiveCharacter p = 0) (hk : k ≠ 0) :
    evenCoprimeSupportTerm χ y (p ^ k) = evenCoprimeSupportWeight y (p ^ k) := by
  unfold evenCoprimeSupportTerm
  rw [Nat.cast_pow, map_pow, hp, zero_pow hk, Complex.zero_re, sub_zero, mul_one]

/-- At indices that are not prime powers, the support term is zero.
Both Mangoldt terms vanish. This removes all non-prime-power indices from
the single-support ledger without inspecting their character values. -/
theorem evenCoprimeSupportTerm_of_not_primePow {q n : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (hn : ¬IsPrimePow n) : evenCoprimeSupportTerm χ y n = 0 := by
  rw [evenCoprimeSupportTerm, evenCoprimeSupportWeight,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_eq_zero_of_not_primePow hn,
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow hn,
    mul_zero, zero_add, zero_mul]

/-- For arbitrary character and root, reindex the exact coupled local cost
by positive exponents and primes dividing the level. Only prime powers contribute.
Use the general Chebyshev reindexing and vanishing off prime powers.
This avoids enumerating all natural indices when constructing local budgets. -/
theorem evenCoprimeLocalCost_eq_prime_powers {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    evenCoprimeLocalCost χ y =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊).filter (fun p ↦ p.Prime ∧ p ∣ q),
          evenCoprimeSupportTerm χ y (p ^ k) := by
  rw [evenCoprimeLocalCost_eq_support_terms]
  exact
    AnalyticNumberTheory.Arithmetic.sum_not_coprime_eq_sum_prime_powers
      (fun n ↦ evenCoprimeSupportTerm χ y n) q (sq_nonneg y)
      (fun n hn ↦ evenCoprimeSupportTerm_of_not_primePow χ y hn)

end PseudoPrime.LLS.Extensions
