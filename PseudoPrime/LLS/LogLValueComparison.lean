/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimePowerFiniteComparison

/-!
# Logarithmic and reciprocal decomposition of the LLS comparison sum

The exact arithmetic identity in equation (5.3) connects Lemma 5.1 to the
logarithmic and reciprocal explicit formulas used in the lower bound of Theorem 1.5.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For `x > 1` and a positive natural index, split the comparison weight into
the logarithmic L-value weight and the reciprocal Mangoldt weight divided by `log x`.
The zero Mangoldt value at one handles the logarithmic denominator there. -/
theorem comparison_weight_split {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 0 < n) :
    ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) =
      ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) * (Real.log (x / n) / Real.log x) +
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm x n / Real.log x := by
  by_cases h1 : n = 1
  · subst n
    norm_num only [ArithmeticFunction.vonMangoldt_apply_one, zero_mul, zero_div,
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm, add_zero]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast lt_of_le_of_ne hn (Ne.symm h1)
    have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn1)
    have hx0 := ne_of_gt (zero_lt_one.trans hx)
    have hlx := ne_of_gt (Real.log_pos hx)
    rw [Real.log_div hx0 hn0]
    unfold AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm
    field_simp [hn0, hl, hx0, hlx]
    ring

/-- For `x > 1`, the unsigned prime-power comparison sum equals the logarithmic
L-value sum plus the reciprocal weighted Mangoldt sum divided by `log x`.
Reindex Mangoldt support and sum the pointwise weight identity. -/
theorem sum_comparison_weight_eq {x : ℝ} (hx : 1 < x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k) =
      logLValueSum x +
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x := by
  classical
  let f : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x))
  have hf : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n, f n) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n := by
    apply Finset.sum_filter_of_ne
    intro n _ hn
    by_contra hp
    exact
      hn
        (by
          dsimp only [f]
          rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, zero_mul])
  have he := AnalyticNumberTheory.Arithmetic.sum_primePow_eq_sum_primesLE f ⌊x⌋₊
  simp only [f, Nat.cast_pow] at he
  unfold primePowerComparisonWeight
  rw [← he, hf]
  have hi : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := Finset.Icc_add_one_left_eq_Ioc 0 ⌊x⌋₊
  rw [hi]
  unfold logLValueSum AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact comparison_weight_split hx (Finset.mem_Ioc.mp hn).1

/-- Split any finite alternating weight sum into the negative unsigned sum and
twice the even-index sum. The two parity cases prove the pointwise identity. -/
private theorem alternating_weight_decomposition (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ s, w k * (-1 : ℝ) ^ k) = -(∑ k ∈ s, w k) + 2 * ∑ k ∈ s with Even k, w k := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rcases Nat.even_or_odd k with he | ho
  · rw [ite_eq_left he, he.neg_one_pow]
    ring
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow]
    ring

/-- For `x > 1`, split the alternating prime-power sum into the two unsigned
logarithmic and reciprocal sums and twice the even-power correction.
This is the prime-power form of the paper's equation (5.3). -/
theorem alternatingPrimePowerSum_decomposition {x : ℝ} (hx : 1 < x) :
    alternatingPrimePowerSum x =
      -logLValueSum x -
          AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x +
        2 *
          ∑ p ∈ Nat.primesLE ⌊x⌋₊,
            ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊) with Even k, primePowerComparisonWeight x p k := by
  have he :
    alternatingPrimePowerSum x =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (-1 : ℝ) ^ k := by
    unfold alternatingPrimePowerSum primePowerComparisonWeight
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  simp only [alternating_weight_decomposition, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  rw [sum_comparison_weight_eq hx]
  ring

/-- For a prime and a positive integer cutoff, halve the even exponents.
The resulting positive exponent interval retains precisely the powers whose squares meet the cutoff.
An explicit bijection preserves every summand. -/
theorem even_exponent_sum_eq {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (p.log N) with Even k, f k) =
      ∑ j ∈ Finset.Icc 1 (p.log N) with p ^ (2 * j) ≤ N, f (2 * j) := by
  classical
  apply Finset.sum_bij (fun k _ ↦ k / 2)
  · intro k hk
    have h := Finset.mem_filter.mp hk
    have hi := Finset.mem_Icc.mp h.1
    have hr := Nat.mul_div_cancel' h.2.two_dvd
    have hd : 0 < k / 2 :=
      Nat.pos_of_ne_zero
        (by
          intro hz
          rw [hz, Nat.mul_zero] at hr
          exact (Nat.ne_of_gt hi.1) hr.symm)
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hd, (Nat.div_le_self k 2).trans hi.2⟩,
          Nat.pow_le_of_le_log hN
            (by
              rw [hr]; exact hi.2)⟩
  · intro a ha b hb hab
    have hra := Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2.two_dvd
    have hrb := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.two_dvd
    have h := congrArg (fun j ↦ 2 * j) hab
    simpa only [hra, hrb] using h
  · intro j hj
    have h := Finset.mem_filter.mp hj
    have hi := Finset.mem_Icc.mp h.1
    have he : Even (2 * j) := ⟨j, by ring⟩
    refine
      ⟨2 * j,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, Nat.le_log_of_pow_le hp.one_lt h.2⟩, he⟩,
        Nat.mul_div_cancel_left j (by decide)⟩
    exact hi.1.trans (Nat.le_mul_of_pos_left j (by decide))
  · intro k hk
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2.two_dvd]

/-- For `x > 1`, the even prime-power correction is the square-indexed Mangoldt sum.
Halve the exponents and reindex prime-power support; Mangoldt is unchanged under squaring.
The integer square cutoff is equivalent to the paper's real cutoff. -/
theorem even_primePower_sum_eq_squares {x : ℝ} (hx : 1 < x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊) with Even k, primePowerComparisonWeight x p k) =
      ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt m *
          (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) := by
  classical
  have hN : ⌊x⌋₊ ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hx.le)
  let f : ℕ → ℝ := fun m ↦
    if m ^ 2 ≤ ⌊x⌋₊ then
      ArithmeticFunction.vonMangoldt m *
        (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x))
    else 0
  have hf : (∑ m ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow m, f m) = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, f m := by
    apply Finset.sum_filter_of_ne
    intro m _ hm
    by_contra hp
    have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp
    exact hm (by simp only [f, hz, zero_mul, ite_self])
  have hi : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := Finset.Icc_add_one_left_eq_Ioc 0 ⌊x⌋₊
  rw [Finset.sum_filter, ← hi, ← hf, AnalyticNumberTheory.Arithmetic.sum_primePow_eq_sum_primesLE]
  apply Finset.sum_congr rfl
  intro p hp
  rw [even_exponent_sum_eq (Nat.mem_primesLE.mp hp).2 hN, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  have he : 2 * j = j * 2 := Nat.mul_comm _ _
  simp only [f, he, pow_mul, Nat.cast_pow, primePowerComparisonWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0)]

/-- Equation (5.3): for `x > 1`, the alternating sum is minus the logarithmic
L-value sum, minus the reciprocal sum divided by `log x`, plus twice the square correction.
Combine the parity decomposition with square-index reindexing. -/
theorem alternatingPrimePowerSum_eq_log_sums {x : ℝ} (hx : 1 < x) :
    alternatingPrimePowerSum x =
      -logLValueSum x -
          AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x +
        2 *
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt m *
              (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) := by
  rw [alternatingPrimePowerSum_decomposition hx, even_primePower_sum_eq_squares hx]

/-- Express a character comparison lower bound using the two unsigned sums and
the square correction. Assume the prime-power comparison inequality of Lemma 5.1;
equation (5.3) substitutes its arithmetic side without any analytic approximation. -/
theorem character_log_sum_lower_of_comparison {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 < x)
    (hc :
      alternatingPrimePowerSum x ≤
        (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            χ n *
              (ArithmeticFunction.vonMangoldt n *
                  (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
                ℝ)).re) :
    -logLValueSum x - AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x +
        2 *
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt m *
              (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) ≤
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          χ n *
            (ArithmeticFunction.vonMangoldt n *
                (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
              ℝ)).re := by
  rw [← alternatingPrimePowerSum_eq_log_sums hx]
  exact hc

/-- For any Dirichlet character and `x ≥ 100`, Lemma 5.1 and equation (5.3) give
the character comparison in terms of the logarithmic sum, reciprocal sum, and square correction.
This arithmetic lower bound is used before applying the analytic estimates of Theorem 1.5. -/
theorem character_log_sum_lower_decomposition {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 100 ≤ x) :
    -logLValueSum x - AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x +
        2 *
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt m *
              (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) ≤
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          χ n *
            (ArithmeticFunction.vonMangoldt n *
                (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
              ℝ)).re := by
  exact
    character_log_sum_lower_of_comparison χ (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx)
      (character_primePower_comparison_lower χ hx)

/-- For any complex Dirichlet character and x > 1, split its finite comparison sum
into the logarithmic sum and the reciprocal sum divided by log x.
Sum the pointwise real weight identity after multiplying by the character value.
This connects the comparison of Lemma 5.1 to the two character explicit formulas. -/
theorem character_comparison_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        χ n *
          (ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
            ℝ)) =
      characterLogLValueSum χ x +
        AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ / (Real.log x : ℂ) := by
  unfold characterLogLValueSum AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
    AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [comparison_weight_split hx (Finset.mem_Ioc.mp hn).1]
  simp only [Complex.ofReal_add, Complex.ofReal_div]
  ring

/-- For any complex Dirichlet character and x > 1, the real comparison sum splits
into the real logarithmic and reciprocal sums. Take real parts of the complex identity;
the reciprocal denominator is real. This form is used in real L-value bounds. -/
theorem character_comparison_sum_re_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          χ n *
            (ArithmeticFunction.vonMangoldt n *
                (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
              ℝ)).re =
      (characterLogLValueSum χ x).re +
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re / Real.log x := by
  rw [character_comparison_sum_eq χ hx]
  simp only [Complex.add_re, Complex.div_ofReal_re]

/-- For any complex Dirichlet character of nonzero modulus and x >= 100, bound the
real logarithmic sum below by the unsigned logarithmic and reciprocal sums, the square
correction, and the negative reciprocal character contribution divided by log x.
Apply Lemma 5.1 and equation (5.3), then split the character comparison weight.
This is the arithmetic input to the reciprocal L-value estimate of Theorem 1.5. -/
theorem character_log_sum_ge_unsigned {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 100 ≤ x) :
    -logLValueSum x - AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x +
          2 *
            ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
              ArithmeticFunction.vonMangoldt m *
                (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) -
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re / Real.log x ≤
      (characterLogLValueSum χ x).re := by
  have h := character_log_sum_lower_decomposition χ hx
  rw [character_comparison_sum_re_eq χ (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx)] at h
  linarith only [h]

end PseudoPrime.LLS.PaperStatements
