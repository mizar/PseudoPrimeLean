/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Comparison with the primitive inducing character

The character values agree away from factors of the level-to-conductor quotient.
This support identity and nonnegative Mangoldt weights bound the change in finite
logarithmic and reciprocal sums. The estimates apply to general complex characters.
-/

@[expose] public section

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

/-- If `x > 0` and `0 < n ≤ floor x`, then the reciprocal Mangoldt weight at `n` is
nonnegative. Both `Λ(n)/n` and `1 - n/x` are nonnegative in this range.
This permits termwise norm bounds in the primitive-character comparison. -/
theorem reciprocalWeightedMangoldtTerm_nonneg {x : ℝ} {n : ℕ} (hx : 0 < x) (hn0 : 0 < n)
    (hnx : n ≤ ⌊x⌋₊) : 0 ≤ reciprocalWeightedMangoldtTerm x n := by
  have hncast : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hncastPos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [reciprocalWeightedMangoldtTerm]
  exact
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hncastPos.le)
      (sub_nonneg.mpr ((div_le_one₀ hx).mpr hncast))

/-- If the natural `n` is coprime to both `χ.conductor` and `q / χ.conductor`, it is
coprime to the level `q`. Multiply the coprimality statements and use the conductor's
divisibility into the level to identify the product with `q`.
This verifies the unit hypothesis of the primitive-character induction formula. -/
theorem coprime_level_of_coprime_conductor_quotient {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hconductor : Nat.Coprime n χ.conductor) (hquotient : Nat.Coprime n (q / χ.conductor)) :
    Nat.Coprime n q := by
  have hproduct : Nat.Coprime n (χ.conductor * (q / χ.conductor)) :=
    Nat.Coprime.mul_right hconductor hquotient
  rwa [Nat.mul_div_cancel' χ.conductor_dvd_level] at hproduct

/-- If `n` is coprime to `q / χ.conductor`, then `χ n = χ.primitiveCharacter n`.
When `n` is coprime to the conductor, it is coprime to the level and the induction formula
applies; otherwise both characters vanish. This confines level-change errors to the quotient
common-factor support. -/
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

/-- For any real cutoff `x`, if `n` is coprime to the level quotient, the logarithmic
weighted terms for the character and its primitive source have difference zero.
Their character values agree and the real weight is identical. This removes off-support
terms when restricting the finite logarithmic difference sum. -/
theorem weightedTerm_sub_eq_zero_of_coprime_quotient {q n : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hquotient : Nat.Coprime n (q / χ.conductor)) :
    characterLogWeightedTerm x χ n - characterLogWeightedTerm x χ.primitiveCharacter n = 0 := by
  rw [characterLogWeightedTerm, characterLogWeightedTerm,
    apply_eq_primitiveCharacter_of_coprime_quotient χ hquotient, sub_self]

/-- If `x > 0` and `0 < n ≤ floor x`, then `Λ(n) * log(x/n)` is nonnegative.
The quotient is at least one and the Mangoldt function is nonnegative.
This provides the sign needed to bound character terms by their real logarithmic weight. -/
theorem logWeightedMangoldtTerm_nonneg {x : ℝ} {n : ℕ} (hx : 0 < x) (hn0 : 0 < n) (hnx : n ≤ ⌊x⌋₊) :
    0 ≤ logWeightedMangoldtTerm x n := by
  have hncast : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hncastPos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [logWeightedMangoldtTerm]
  exact
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg ((one_le_div₀ hncastPos).mpr hncast))

/-- For `x > 0` and `0 < n ≤ floor x`, the norm of the logarithmic term's change from
`χ` to its primitive source is at most its nonnegative real Mangoldt weight.
Off quotient support the values agree; on it the level character vanishes and the primitive
value has norm at most one. This gives the termwise logarithmic level-change bound. -/
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

/-- For any real `x`, if `n` shares a factor with `q / χ.conductor`, its logarithmic term
for `χ` vanishes. The quotient divides the level, so `n` is not coprime to `q` and the
character value is zero. This identifies the correction as primitive contributions alone. -/
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

/-- For any real cutoff `x`, the logarithmic sum for `χ` minus that for its primitive
source is the sum of their term differences over `0 < n ≤ floor x` sharing a factor
with `q / χ.conductor`. All omitted terms have equal character values.
This exact support identity starts the logarithmic level-change ledger. -/
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

/-- For `x ≠ 0`, prime `p`, and nonzero natural exponent `k`, the real logarithmic term
at `p^k` for the primitive character is
`log p * (log x - k * log p) * Re (χ.primitiveCharacter p ^ k)`.
Use the Mangoldt prime-power formula and multiplicativity of the character.
This reduces prime-power corrections to affine logarithmic weights. -/
theorem characterLogWeightedTerm_primitive_re_prime_pow {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    {p k : ℕ} (hx : x ≠ 0) (hp : p.Prime) (hk : k ≠ 0) :
    (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
      Real.log p * (Real.log x - k * Real.log p) * (χ.primitiveCharacter p ^ k).re := by
  rw [characterLogWeightedTerm, logWeightedMangoldtTerm_prime_pow hx hp hk, Nat.cast_pow, map_pow,
    Complex.re_ofReal_mul]

/-- For a nonzero level `q` and positive cutoff `x`, the norm of the logarithmic weighted
sum's change to the primitive source is at most
`(1/2) * (q / χ.conductor).primeFactors.card * (log x)²`.
Restrict to quotient support, bound each term by its nonnegative weight, and apply the
common-factor sum bound. This is the coarse logarithmic comparison estimate. -/
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

/-- For any real cutoff `x`, if `n` is not coprime to the level quotient, the reciprocal
weighted term for `χ` is zero. Noncoprimality also holds at the level, forcing the character
value to vanish. This separates primitive contributions on the correction support. -/
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

/-- For `x > 0` and `0 < n ≤ floor x`, the norm of the reciprocal term's change to the
primitive source is at most its nonnegative real weight. Split on coprimality with the
conductor and level quotient: either the values agree, both vanish, or only the primitive
value remains with norm at most one. This gives the termwise reciprocal comparison. -/
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

/-- For nonzero level `q` and `x > 0`, the norm of the reciprocal weighted sum's change
to the primitive source is at most `commonFactorReciprocalWeightedSum x (q / χ.conductor)`.
The triangle inequality and termwise weight bound apply on quotient support, while all
other differences vanish. This is the finite-sum estimate before further arithmetic coarsening. -/
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

/-- For a complex Dirichlet character, x > 0 and 0 < n <= floor x, the reciprocal
term has norm at most its unsigned weight. The weight is nonnegative and the character
value has norm at most one. This is the termwise input to unsigned reciprocal comparison. -/
theorem norm_characterReciprocalWeightedTerm_le {q n : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (hn0 : 0 < n) (hnx : n ≤ ⌊x⌋₊) :
    ‖characterReciprocalWeightedTerm x χ n‖ ≤ reciprocalWeightedMangoldtTerm x n := by
  have hw := reciprocalWeightedMangoldtTerm_nonneg hx hn0 hnx
  rw [characterReciprocalWeightedTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw (DirichletCharacter.norm_le_one χ _)

/-- For any complex Dirichlet character and x > 0, the norm of the finite reciprocal
character sum is at most the unsigned reciprocal Mangoldt sum. Sum the nonnegative
termwise norm bounds and use the triangle inequality. No primitivity or RH is required;
the estimate removes character values from explicit logarithmic L-value bounds. -/
theorem norm_characterReciprocalWeightedSum_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) : ‖characterReciprocalWeightedSum x χ‖ ≤ reciprocalWeightedMangoldtSum x := by
  unfold characterReciprocalWeightedSum reciprocalWeightedMangoldtSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro n hn
  exact
    norm_characterReciprocalWeightedTerm_le χ hx (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2

end PseudoPrime.AnalyticNumberTheory.Arithmetic
