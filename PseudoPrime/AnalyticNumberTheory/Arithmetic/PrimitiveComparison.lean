/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.NumberTheory.MulCharParity

/-! Generic comparison lemmas for a character and its primitive character. -/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A nontrivial character has a nontrivial primitive inducing character.
Changing the trivial character back to the original level would otherwise make
the original character trivial. This transports nontriviality to analytic estimates. -/
theorem primitiveCharacter_ne_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  have hc := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h, DirichletCharacter.changeLevel_one] at hc
  exact hne hc.symm

/-- A reciprocal Mangoldt term in the finite summation range is nonnegative. -/
theorem reciprocalWeightedMangoldtTerm_nonneg {x : ℝ} {n : ℕ} (hx : 0 < x) (hn0 : 0 < n)
    (hnx : n ≤ ⌊x⌋₊) : 0 ≤ reciprocalWeightedMangoldtTerm x n := by
  have hncast : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hncastPos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [reciprocalWeightedMangoldtTerm]
  exact
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hncastPos.le)
      (sub_nonneg.mpr ((div_le_one₀ hx).mpr hncast))

/-- Coprimality with the conductor and complementary quotient implies coprimality with the level. -/
theorem coprime_level_of_coprime_conductor_quotient {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hconductor : Nat.Coprime n χ.conductor) (hquotient : Nat.Coprime n (q / χ.conductor)) :
    Nat.Coprime n q := by
  have hproduct : Nat.Coprime n (χ.conductor * (q / χ.conductor)) :=
    Nat.Coprime.mul_right hconductor hquotient
  rwa [Nat.mul_div_cancel' χ.conductor_dvd_level] at hproduct

/-- The original and primitive characters agree away from the complementary level quotient. -/
theorem apply_eq_primitiveCharacter_of_coprime_quotient {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hquotient : Nat.Coprime n (q / χ.conductor)) : χ n = χ.primitiveCharacter n := by
  by_cases hconductor : Nat.Coprime n χ.conductor
  · have hlevel := coprime_level_of_coprime_conductor_quotient χ hconductor hquotient
    simpa only [Int.cast_natCast] using
      (χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hlevel)).symm
  · have hlevel : ¬Nat.Coprime n q := by
      intro hnq
      exact hconductor (hnq.of_dvd_right χ.conductor_dvd_level)
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
    have hprimitiveZero : χ.primitiveCharacter n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ.primitiveCharacter (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hconductor)
    rw [hχzero, hprimitiveZero]

/-- On the coprime complement, the difference of weighted summands is zero. -/
theorem weightedTerm_sub_eq_zero_of_coprime_quotient {q n : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hquotient : Nat.Coprime n (q / χ.conductor)) :
    characterLogWeightedTerm x χ n - characterLogWeightedTerm x χ.primitiveCharacter n = 0 := by
  rw [characterLogWeightedTerm, characterLogWeightedTerm,
    apply_eq_primitiveCharacter_of_coprime_quotient χ hquotient, sub_self]

/-- A logarithmically weighted Mangoldt term indexed by `n ≤ x` is nonnegative. -/
theorem logWeightedMangoldtTerm_nonneg {x : ℝ} {n : ℕ} (hx : 0 < x) (hn0 : 0 < n) (hnx : n ≤ ⌊x⌋₊) :
    0 ≤ logWeightedMangoldtTerm x n := by
  have hncast : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hncastPos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [logWeightedMangoldtTerm]
  exact
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg ((one_le_div₀ hncastPos).mpr hncast))

/-- A character summand changes by at most its real weight on the quotient support. -/
theorem norm_weightedTerm_sub_primitive_le {q n : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 < x) (hn0 : 0 < n) (hnx : n ≤ ⌊x⌋₊) :
    ‖characterLogWeightedTerm x χ n - characterLogWeightedTerm x χ.primitiveCharacter n‖ ≤
      logWeightedMangoldtTerm x n := by
  have hweight := logWeightedMangoldtTerm_nonneg hx hn0 hnx
  by_cases hconductor : Nat.Coprime n χ.conductor
  · by_cases hquotient : Nat.Coprime n (q / χ.conductor)
    · rw [weightedTerm_sub_eq_zero_of_coprime_quotient x χ hquotient, norm_zero]
      exact hweight
    · have hlevel : ¬Nat.Coprime n q := by
        intro hnq
        exact hquotient (hnq.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
      have hχzero : χ n = 0 := by
        simpa only [Int.cast_natCast] using
          (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
            (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
      rw [characterLogWeightedTerm, characterLogWeightedTerm, hχzero, mul_zero, zero_sub, norm_neg,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hweight]
      exact mul_le_of_le_one_right hweight (DirichletCharacter.norm_le_one _ _)
  · have hlevel : ¬Nat.Coprime n q := by
      intro hnq
      exact hconductor (hnq.of_dvd_right χ.conductor_dvd_level)
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
    have hprimitiveZero : χ.primitiveCharacter n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ.primitiveCharacter (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hconductor)
    rw [characterLogWeightedTerm, characterLogWeightedTerm, hχzero, hprimitiveZero, mul_zero,
      sub_self, norm_zero]
    exact hweight

/-- The primitive character vanishes exactly off the coprime-to-conductor support. -/
theorem primitiveCharacter_apply_eq_zero_iff_not_coprime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : ℕ) : χ.primitiveCharacter p = 0 ↔ ¬Nat.Coprime p χ.conductor := by
  rw [← Nat.isCoprime_iff_coprime]
  simpa only [Int.cast_natCast] using
    DirichletCharacter.apply_eq_zero_iff χ.primitiveCharacter (p : ℤ)

/-- For a quadratic primitive character, the squared value has the coprimality indicator form. -/
theorem primitiveCharacter_sq_apply_re_eq_ite_of_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.primitiveCharacter.IsQuadratic) (p : ℕ) :
    (χ.primitiveCharacter p ^ 2).re = if Nat.Coprime p χ.conductor then 1 else 0 := by
  rcases hχ (p : ZMod χ.conductor) with h0 | h1 | hm1
  · rw [ite_eq_right ((primitiveCharacter_apply_eq_zero_iff_not_coprime χ p).mp h0), h0]
    simp only [zero_pow (show (2 : ℕ) ≠ 0 by decide), Complex.zero_re]
  · have hcop : Nat.Coprime p χ.conductor := by
      by_contra hncop
      have heq := (primitiveCharacter_apply_eq_zero_iff_not_coprime χ p).mpr hncop
      rw [h1] at heq
      exact one_ne_zero heq
    rw [ite_eq_left hcop, h1]
    simp only [one_pow, Complex.one_re]
  · have hcop : Nat.Coprime p χ.conductor := by
      by_contra hncop
      have heq := (primitiveCharacter_apply_eq_zero_iff_not_coprime χ p).mpr hncop
      rw [hm1] at heq
      exact (neg_ne_zero.mpr one_ne_zero) heq
    rw [ite_eq_left hcop, hm1]
    simp only [neg_one_sq, Complex.one_re]

/-- A character logarithmic summand vanishes on the complementary quotient support. -/
theorem characterLogWeightedTerm_eq_zero_of_not_coprime_quotient {q n : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hquotient : ¬Nat.Coprime n (q / χ.conductor)) :
    characterLogWeightedTerm x χ n = 0 := by
  have hlevel : ¬Nat.Coprime n q := by
    intro hcoprime
    exact hquotient (hcoprime.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
  have hχzero : χ n = 0 := by
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
        (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
  rw [characterLogWeightedTerm, hχzero, mul_zero]

/-- The finite logarithmic weighted-sum difference is supported on the quotient complement. -/
theorem characterLogWeightedSum_sub_primitive_eq {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) :
    characterLogWeightedSum x χ - characterLogWeightedSum x χ.primitiveCharacter =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
        (characterLogWeightedTerm x χ n - characterLogWeightedTerm x χ.primitiveCharacter n) := by
  rw [characterLogWeightedSum, characterLogWeightedSum, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnfilter
  have hquotient : Nat.Coprime n (q / χ.conductor) := by
    simpa only [Finset.mem_filter, hn, true_and, not_not] using hnfilter
  exact weightedTerm_sub_eq_zero_of_coprime_quotient x χ hquotient

/-- The logarithmic weighted summand at a prime power has an explicit closed form. -/
theorem characterLogWeightedTerm_primitive_re_prime_pow {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    {p k : ℕ} (hx : x ≠ 0) (hp : p.Prime) (hk : k ≠ 0) :
    (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
      Real.log p * (Real.log x - k * Real.log p) * (χ.primitiveCharacter p ^ k).re := by
  rw [characterLogWeightedTerm, logWeightedMangoldtTerm_prime_pow hx hp hk, Nat.cast_pow, map_pow,
    Complex.re_ofReal_mul]

/-- The quadratic specialization of the logarithmic prime-power closed form. -/
theorem characterLogWeightedTerm_primitive_re_prime_pow_of_isQuadratic {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) {p k : ℕ} (hx : x ≠ 0)
    (hp : p.Prime) (hk : k ≠ 0) :
    (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
      Real.log p * (Real.log x - k * Real.log p) *
        (if Odd k then (χ.primitiveCharacter p).re else (χ.primitiveCharacter p ^ 2).re) := by
  rw [characterLogWeightedTerm_primitive_re_prime_pow x χ hx hp hk,
    NumberTheory.isQuadratic_pow_apply hχ (p : ZMod χ.conductor) hk, apply_ite Complex.re]

/-- The finite logarithmic sum difference is bounded by the quotient common-factor sum. -/
theorem norm_characterLogWeightedSum_sub_primitive_le {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) :
    ‖characterLogWeightedSum x χ - characterLogWeightedSum x χ.primitiveCharacter‖ ≤
      (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2 := by
  rw [characterLogWeightedSum_sub_primitive_eq]
  calc
    ‖∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
            (characterLogWeightedTerm x χ n - characterLogWeightedTerm x χ.primitiveCharacter n)‖ ≤
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
          ‖characterLogWeightedTerm x χ n - characterLogWeightedTerm x χ.primitiveCharacter n‖ :=
      norm_sum_le _ _
    _ ≤ commonFactorLogWeightedSum x (q / χ.conductor) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIoc := (Finset.mem_filter.mp hn).1
      exact
        norm_weightedTerm_sub_primitive_le x χ hx (Finset.mem_Ioc.mp hnIoc).1
          (Finset.mem_Ioc.mp hnIoc).2
    _ ≤ (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2 := by
      apply commonFactorLogWeightedSum_le
      · exact
          (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
              χ.conductor_ne_zero.bot_lt).ne'
      · exact hx

/-- A reciprocal character summand vanishes on the complementary quotient support. -/
theorem characterReciprocalWeightedTerm_eq_zero_of_not_coprime_quotient {q n : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hquotient : ¬Nat.Coprime n (q / χ.conductor)) :
    characterReciprocalWeightedTerm x χ n = 0 := by
  have hlevel : ¬Nat.Coprime n q := by
    intro hcoprime
    exact hquotient (hcoprime.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
  have hχzero : χ n = 0 := by
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
        (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
  rw [characterReciprocalWeightedTerm, hχzero, mul_zero]

/-- A reciprocal summand changes by at most its nonnegative real weight. -/
theorem norm_reciprocalTerm_sub_primitive_le {q n : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 < x) (hn0 : 0 < n) (hnx : n ≤ ⌊x⌋₊) :
    ‖characterReciprocalWeightedTerm x χ n -
          characterReciprocalWeightedTerm x χ.primitiveCharacter n‖ ≤
      reciprocalWeightedMangoldtTerm x n := by
  have hweight := reciprocalWeightedMangoldtTerm_nonneg hx hn0 hnx
  by_cases hconductor : Nat.Coprime n χ.conductor
  · by_cases hquotient : Nat.Coprime n (q / χ.conductor)
    · have heq := apply_eq_primitiveCharacter_of_coprime_quotient χ hquotient
      rw [characterReciprocalWeightedTerm, characterReciprocalWeightedTerm, heq, sub_self,
        norm_zero]
      exact hweight
    · have hlevel : ¬Nat.Coprime n q := by
        intro hnq
        exact hquotient (hnq.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
      have hχzero : χ n = 0 := by
        simpa only [Int.cast_natCast] using
          (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
            (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
      rw [characterReciprocalWeightedTerm, characterReciprocalWeightedTerm, hχzero, mul_zero,
        zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hweight]
      exact mul_le_of_le_one_right hweight (DirichletCharacter.norm_le_one _ _)
  · have hlevel : ¬Nat.Coprime n q := by
      intro hnq
      exact hconductor (hnq.of_dvd_right χ.conductor_dvd_level)
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
    have hprimitiveZero : χ.primitiveCharacter n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ.primitiveCharacter (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hconductor)
    rw [characterReciprocalWeightedTerm, characterReciprocalWeightedTerm, hχzero, hprimitiveZero,
      mul_zero, sub_self, norm_zero]
    exact hweight

/-- The reciprocal finite-sum difference is bounded by the quotient common-factor sum. -/
theorem norm_characterReciprocalWeightedSum_sub_primitive_le {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) :
    ‖characterReciprocalWeightedSum x χ - characterReciprocalWeightedSum x χ.primitiveCharacter‖ ≤
      commonFactorReciprocalWeightedSum x (q / χ.conductor) := by
  rw [characterReciprocalWeightedSum, characterReciprocalWeightedSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            (characterReciprocalWeightedTerm x χ n -
              characterReciprocalWeightedTerm x χ.primitiveCharacter n)‖ ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          ‖characterReciprocalWeightedTerm x χ n -
              characterReciprocalWeightedTerm x χ.primitiveCharacter n‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          if ¬Nat.Coprime n (q / χ.conductor) then reciprocalWeightedMangoldtTerm x n else 0 :=
      by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hcop : Nat.Coprime n (q / χ.conductor)
      · rw [ite_eq_right (not_not.mpr hcop)]
        have heq := apply_eq_primitiveCharacter_of_coprime_quotient χ hcop
        rw [characterReciprocalWeightedTerm, characterReciprocalWeightedTerm, heq, sub_self,
          norm_zero]
      · rw [ite_eq_left hcop]
        exact
          norm_reciprocalTerm_sub_primitive_le x χ hx (Finset.mem_Ioc.mp hn).1
            (Finset.mem_Ioc.mp hn).2
    _ = commonFactorReciprocalWeightedSum x (q / χ.conductor) := by
      rw [commonFactorReciprocalWeightedSum, Finset.sum_filter]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
