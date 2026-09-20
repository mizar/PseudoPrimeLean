/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
import PseudoPrime.AnalyticNumberTheory.Arithmetic.FejerConvexSums
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.NumberTheory.MulCharParity

/-!
# Comparing an imprimitive character with its primitive character

This file formalizes the logarithmic level-change identity.  It proves the arithmetic support
statement behind that identity:
the two character values can differ only at integers sharing a factor with the quotient of the
level by the conductor.  It then restricts the weighted-sum difference to exactly that support.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/--
Input/assumptions: a cutoff and a level-`q` character.
Conclusion: the original-to-primitive logarithmic level change is recorded as the finite sum of
primitive character contributions on the complementary quotient support.
Content: terms sharing the quotient are zero for the level character; terms away from it agree
with the primitive character.
Role: is the character-sensitive logarithmic correction, in the same shape as the reciprocal
correction, before it is converted to a prime-power form or combined with it in one ledger.
-/
noncomputable def primitiveLogLevelChangeCorrection {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) :
    ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
    (characterLogWeightedTerm x χ.primitiveCharacter n).re

/--
Input/assumptions: a cutoff and a level-`q` character.
Conclusion: the primitive logarithmic sum equals the level-character logarithmic sum plus the
character-sensitive complementary-quotient correction.
Content: take real parts of the exact `S(x, χ) - S(x, χ̃)` identity and use that the level
character vanishes on the quotient-complement support.
Role: gives the logarithmic ledger the same exact level-change identity already available on the
reciprocal side, so both quotient corrections can be assembled together.
-/
theorem characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    (characterLogWeightedSum x χ.primitiveCharacter).re =
      (characterLogWeightedSum x χ).re + primitiveLogLevelChangeCorrection x χ := by
  have hdiff := characterLogWeightedSum_sub_primitive_eq x χ
  have hre :
    (characterLogWeightedSum x χ).re - (characterLogWeightedSum x χ.primitiveCharacter).re =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
        ((characterLogWeightedTerm x χ n).re -
          (characterLogWeightedTerm x χ.primitiveCharacter n).re) := by
    have := congrArg Complex.re hdiff
    simpa only [Complex.sub_re, Complex.re_sum] using this
  have hzero :
    ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
        (characterLogWeightedTerm x χ n).re =
      0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [characterLogWeightedTerm_eq_zero_of_not_coprime_quotient x χ (Finset.mem_filter.mp hn).2]
    simp only [Complex.zero_re]
  rw [Finset.sum_sub_distrib, hzero] at hre
  rw [primitiveLogLevelChangeCorrection]
  linarith

/--
Input/assumptions: a cutoff `x ≥ 0` and a level-`q` character.
Conclusion: the character-sensitive logarithmic level-change correction is a double sum over
powers of primes dividing the complementary quotient, each retaining the real part of the
primitive character value at that prime power.
Content: reindex the correction support by exponent and prime, using that the logarithmic
weighted summand vanishes off prime powers.
Role: is the prime-power expansion of the logarithmic correction, matching the shape of
`PseudoPrime.AnalyticNumberTheory.Arithmetic.`
`primitiveReciprocalLevelChangeCorrection_eq_sum_prime_powers` so both ledgers share the same
`(k, p)` index.
-/
theorem primitiveLogLevelChangeCorrection_eq_sum_prime_powers {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) :
    primitiveLogLevelChangeCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ q / χ.conductor,
          (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  rw [primitiveLogLevelChangeCorrection]
  exact
    sum_not_coprime_eq_sum_prime_powers
      (fun n ↦ (characterLogWeightedTerm x χ.primitiveCharacter n).re) (q / χ.conductor) hx
      fun n hn ↦ by
      simp only [characterLogWeightedTerm, logWeightedMangoldtTerm_eq_zero_of_not_primePow hn,
        Complex.ofReal_zero, zero_mul, Complex.zero_re]

/--
Input/assumptions: a cutoff `x > 0` and a level-`q` character whose primitive inducing character is
quadratic.
Conclusion: the logarithmic level-change correction is the double sum over quotient prime powers
of the affine logarithmic weight times `χ̃(p)` on odd exponents, and times a coprime-to-conductor
indicator (no character value) on even exponents.
Content: combine the prime-power expansion with the quadratic closed form and the
coprime-to-conductor indicator for the squared value.
Role: is the fully reduced exact logarithmic ledger for the quadratic character class, matching
`PseudoPrime.AnalyticNumberTheory.Arithmetic.`
`primitiveReciprocalLevelChangeCorrection_eq_sum_of_isQuadratic`
in its prime/exponent indexing, for combining the logarithmic and reciprocal sums prime by prime.
-/
theorem primitiveLogLevelChangeCorrection_eq_sum_of_isQuadratic {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 0 < x) :
    primitiveLogLevelChangeCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ q / χ.conductor,
          Real.log p * (Real.log x - k * Real.log p) *
            (if Odd k then (χ.primitiveCharacter p).re
            else if Nat.Coprime p χ.conductor then 1 else 0) := by
  rw [primitiveLogLevelChangeCorrection_eq_sum_prime_powers x χ hx.le]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  have hkpos : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  rw [characterLogWeightedTerm_primitive_re_prime_pow_of_isQuadratic x χ hχ hx.ne' hpprime hkpos]
  by_cases hodd : Odd k
  · simp only [hodd, ↓reduceIte]
  · simp only [ite_eq_right hodd]
    rw [primitiveCharacter_sq_apply_re_eq_ite_of_isQuadratic χ hχ p]

/--
Input/assumptions: a level-`q` character with quadratic primitive part, a prime `p`, a cutoff
`x ≥ 2`, and `K` with `K \log p \le \log x < (K + 1) \log p` (i.e. `K` is the floor of
`log x / log p`; this exact-floor hypothesis is needed, not just `p ^ K ≤ x`).
Conclusion: the finite logarithmic prime-power sum over `k = 1..K` at `p` is at least
`-(1/2)(\log p)(\log x)`.
Content: case on the three possible values of `χ̃(p)`.  When `χ̃(p) = 0` every summand vanishes;
when `χ̃(p) = 1` every summand is nonnegative; when `χ̃(p) = -1` the sum telescopes exactly via
`PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_neg_one_pow_succ_mul_affine_even/odd`,
since consecutive terms of the affine weight differ
by the constant `log p` (unlike the geometric reciprocal weight, so an inequality-only bound is
not tight enough and an exact identity is used instead).
Role: is the local logarithmic alternating bound, the affine-weight analogue of the reciprocal
`PseudoPrime.AnalyticNumberTheory.Arithmetic.`
`quadraticReciprocalPrimePowerCorrection_neg_le_half_log`.
-/
theorem quadraticLogPrimePowerCorrection_neg_le_half_log_mul_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hx : 2 ≤ x) {K : ℕ} (hKle : (K : ℝ) * Real.log p ≤ Real.log x)
    (hKlt : Real.log x < (K + 1 : ℝ) * Real.log p) :
    -(1 / 2 * Real.log p * Real.log x) ≤
      ∑ k ∈ Finset.Icc 1 K, (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have heach :
    ∀ k ∈ Finset.Icc 1 K,
      (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
        Real.log p * (Real.log x - k * Real.log p) * (χ.primitiveCharacter p ^ k).re := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1; omega
    exact characterLogWeightedTerm_primitive_re_prime_pow x χ hxpos.ne' hp hk0
  rw [Finset.sum_congr rfl heach]
  rcases hχ (p : ZMod χ.conductor) with h0 | h1 | hm1
  · have hzero :
      ∀ k ∈ Finset.Icc 1 K,
        Real.log p * (Real.log x - k * Real.log p) * (χ.primitiveCharacter p ^ k).re = 0 := by
      intro k hk
      have hk0 : k ≠ 0 := by
        have := (Finset.mem_Icc.mp hk).1; omega
      rw [h0, zero_pow hk0]
      simp only [Complex.zero_re, mul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    nlinarith [mul_nonneg hlogp.le hlogx]
  · have hone :
      ∀ k ∈ Finset.Icc 1 K,
        Real.log p * (Real.log x - k * Real.log p) * (χ.primitiveCharacter p ^ k).re =
          Real.log p * (Real.log x - k * Real.log p) := by
      intro k hk
      rw [h1, one_pow]
      simp only [Complex.one_re, mul_one]
    rw [Finset.sum_congr rfl hone]
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 K, Real.log p * (Real.log x - k * Real.log p) := by
      apply Finset.sum_nonneg
      intro k hk
      have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
      have hkbound : (k : ℝ) * Real.log p ≤ (K : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkK) hlogp.le
      nlinarith [hKle]
    nlinarith [mul_nonneg hlogp.le hlogx]
  · have hcast : χ.primitiveCharacter p = ((-1 : ℝ) : ℂ) := by
      rw [hm1]
      simp only [Complex.ofReal_neg, Complex.ofReal_one]
    have hSeq :
      ∑ k ∈ Finset.Icc 1 K,
          Real.log p * (Real.log x - k * Real.log p) * (χ.primitiveCharacter p ^ k).re =
        -(Real.log p *
            ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * (Real.log x - k * Real.log p)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have hre : (χ.primitiveCharacter p ^ k).re = (-1 : ℝ) ^ k := by
        rw [hcast, ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hre, pow_succ]
      ring
    rw [hSeq]
    rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
    · obtain rfl : K = 2 * m := by omega
      rw [sum_neg_one_pow_succ_mul_affine_even]
      have hmb : (m : ℝ) * Real.log p ≤ 1 / 2 * Real.log x := by
        push_cast at hKle
        nlinarith [hKle]
      nlinarith [mul_le_mul_of_nonneg_left hmb hlogp.le]
    · obtain rfl : K = 2 * m + 1 := hm
      rw [sum_neg_one_pow_succ_mul_affine_odd]
      have hmb : 1 / 2 * Real.log x ≤ (m + 1 : ℝ) * Real.log p := by
        push_cast at hKlt
        nlinarith [hKlt]
      nlinarith [mul_le_mul_of_nonneg_left hmb hlogp.le]

/--
Input/assumptions: a cutoff `x ≥ 2`, a level-`q` character, a prime `p`
at which the primitive character has unit norm (in particular `p` is coprime to the conductor),
and `K` bracketing `log x` as
`K*log p ≤ log x < (K+1)*log p` (the exact floor of `log x/log p`, as in the quadratic version).
Conclusion: the finite logarithmic prime-power sum over `k = 1..K` at `p` is at least
`-(1/2)(log p)(log x)`, with no quadratic hypothesis on the character.
Content: rewrite each summand as `log p * (log x - k*log p) * Re(z^k)` with `z := χ̃(p)`,
`‖z‖ = 1`, then apply the generic Fejér log-weight bound
`PseudoPrime.AnalyticNumberTheory.Arithmetic.re_sum_logWeight_ge_neg_half`
with `logX := log x`, `logP := log p`, `θ := log x / log p - K ∈ [0, 1]`.
Role: is the `hquad`-free replacement for
`quadraticLogPrimePowerCorrection_neg_le_half_log_mul_log`.
-/
theorem re_sum_logPrimePowerCorrection_neg_le_half_log_mul_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) (hz : ‖χ.primitiveCharacter p‖ = 1)
    (hx : 2 ≤ x) {K : ℕ} (hKle : (K : ℝ) * Real.log p ≤ Real.log x)
    (hKlt : Real.log x < (K + 1 : ℝ) * Real.log p) :
    -(1 / 2 * Real.log p * Real.log x) ≤
      ∑ k ∈ Finset.Icc 1 K, (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  set z : ℂ := χ.primitiveCharacter p with hzdef
  set θ : ℝ := Real.log x / Real.log p - (K : ℝ) with hθdef
  have hlogX : Real.log x = ((K : ℝ) + θ) * Real.log p := by
    rw [hθdef]; field_simp; ring
  have hθ0 : 0 ≤ θ := by
    rw [hθdef, sub_nonneg, le_div_iff₀ hlogp]
    linarith [hKle]
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, sub_le_iff_le_add, div_le_iff₀ hlogp]
    linarith [hKlt]
  have heach :
    ∀ k ∈ Finset.Icc 1 K,
      (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
        Real.log p * ((Real.log x - (k : ℝ) * Real.log p) * (z ^ k).re) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1; omega
    rw [characterLogWeightedTerm_primitive_re_prime_pow x χ hxpos.ne' hp hk0, mul_assoc]
  have hfejer :=
    re_sum_logWeight_ge_neg_half (logX := Real.log x) (logP := Real.log p) (θ := θ) (K := K) (z :=
      z) hz hlogp hθ0 hθ1 hlogX
  have hstep2 :
    ∀ k ∈ Finset.Icc 1 K,
      (((Real.log x - (k : ℝ) * Real.log p : ℝ) : ℂ) * z ^ k).re =
        (Real.log x - (k : ℝ) * Real.log p) * (z ^ k).re :=
    fun k _ => Complex.re_ofReal_mul _ _
  have hsum_eq :
    (Finset.sum (Finset.Icc 1 K) fun k =>
          ((Real.log x - (k : ℝ) * Real.log p : ℝ) : ℂ) * z ^ k).re =
      Finset.sum (Finset.Icc 1 K) fun k => (Real.log x - (k : ℝ) * Real.log p) * (z ^ k).re := by
    rw [Complex.re_sum]; exact Finset.sum_congr rfl hstep2
  rw [hsum_eq] at hfejer
  rw [Finset.sum_congr rfl heach, ← Finset.mul_sum]
  have hlogp0 : 0 ≤ Real.log p := hlogp.le
  have := mul_le_mul_of_nonneg_left hfejer hlogp0
  nlinarith [this]

/--
Input/assumptions: a cutoff and a level-`q` character.
Conclusion: the logarithmic level-change correction is a double sum with the quotient-support
prime outermost and its admissible exponents `1..Nat.log p ⌊x⌋₊` innermost.
Content: reindex the prime-power expansion using
`PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_primePow_eq_sum_primesLE`,
the same reindexing already used for
`PseudoPrime.AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_eq_sum_prime_divisors`
in the weighted-sum module and for the reciprocal ledger.
Role: lets the per-prime bound be summed over `Nat.primesLE ⌊x⌋₊` directly.
-/
theorem primitiveLogLevelChangeCorrection_eq_sum_prime_divisors {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    primitiveLogLevelChangeCorrection x χ =
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  rw [primitiveLogLevelChangeCorrection, ← Finset.Icc_add_one_left_eq_Ioc]
  calc
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
          (characterLogWeightedTerm x χ.primitiveCharacter n).re =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n,
          if ¬Nat.Coprime n (q / χ.conductor) then
            (characterLogWeightedTerm x χ.primitiveCharacter n).re
          else 0 :=
      by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hpow : IsPrimePow n
      · simp only [hpow, ↓reduceIte]
      · rw [show (characterLogWeightedTerm x χ.primitiveCharacter n).re = 0 from by
            simp only [characterLogWeightedTerm,
              logWeightedMangoldtTerm_eq_zero_of_not_primePow hpow, Complex.ofReal_zero, zero_mul,
              Complex.zero_re]]
        simp only [ite_self]
    _ =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            if ¬Nat.Coprime (p ^ k) (q / χ.conductor) then
              (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re
            else 0 :=
      by
      exact
        sum_primePow_eq_sum_primesLE
          (fun n ↦
            if ¬Nat.Coprime n (q / χ.conductor) then
              (characterLogWeightedTerm x χ.primitiveCharacter n).re
            else 0)
          ⌊x⌋₊
    _ = _ := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
      by_cases hdvd : p ∣ q / χ.conductor
      · simp only [hdvd, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
        have hcop : ¬Nat.Coprime (p ^ k) (q / χ.conductor) := by
          rw [Nat.coprime_pow_left_iff hkpos, hpprime.coprime_iff_not_dvd]
          exact not_not_intro hdvd
        simp only [hcop, not_false_eq_true, ↓reduceIte]
      · simp only [hdvd, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro k hk
        have hkpos : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
        have hcop : Nat.Coprime (p ^ k) (q / χ.conductor) := by
          rw [Nat.coprime_pow_left_iff hkpos]
          exact hpprime.coprime_iff_not_dvd.mpr hdvd
        rw [ite_eq_right (not_not_intro hcop)]

/--
Input/assumptions: a level-`q` character with quadratic primitive part, `x ≥ 2`, and
`q / conductor ≠ 0`.
Conclusion: the logarithmic level-change correction is at least
`-(1/2) log(q / conductor) log x`.
Content: reindex to prime-outer form, bound each prime's inner sum via
`quadraticLogPrimePowerCorrection_neg_le_half_log_mul_log` (feeding it the exact-floor
hypotheses `Nat.pow_log_le_self`/`Nat.lt_pow_succ_log_self` cast to `ℝ` via monotone `Real.log`),
then bound the resulting `Σ log p` by `Real.log (q / conductor)` via
`PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log`.
Role: is the combined logarithmic bound, the affine-weight analogue of
`PseudoPrime.AnalyticNumberTheory.Arithmetic.`
`primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient_of_isQuadratic` in
the reciprocal comparison, replacing the coarse `primitiveLogLevelChangeCorrection_ge_neg`
route (via `(q / conductor).primeFactors.card`) with one whose quotient dependence is exactly
`log(q / conductor)`, ready for conductor absorption.
-/
theorem primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log_of_isQuadratic {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (hqd : q / χ.conductor ≠ 0) :
    -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) ≤
      primitiveLogLevelChangeCorrection x χ := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [primitiveLogLevelChangeCorrection_eq_sum_prime_divisors]
  set S := (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor with hSdef
  have hstep :
    ∀ p ∈ S,
      -(1 / 2 * Real.log p * Real.log x) ≤
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hple : p ≤ ⌊x⌋₊ := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hxfloor : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
    have hKnat : p ^ p.log ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hxfloor
    have hKlt' : ⌊x⌋₊ < p ^ (p.log ⌊x⌋₊).succ := Nat.lt_pow_succ_log_self hpprime.one_lt ⌊x⌋₊
    have hKle : (p.log ⌊x⌋₊ : ℝ) * Real.log p ≤ Real.log x := by
      have hpk_pos : (0 : ℝ) < (p : ℝ) ^ p.log ⌊x⌋₊ := pow_pos (by exact_mod_cast hpprime.pos) _
      have hKnatR : (p : ℝ) ^ p.log ⌊x⌋₊ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hKnat
      have hR : (p : ℝ) ^ p.log ⌊x⌋₊ ≤ x := hKnatR.trans (Nat.floor_le hxpos.le)
      have hlog := Real.log_le_log hpk_pos hR
      rwa [Real.log_pow] at hlog
    have hKlt : Real.log x < (p.log ⌊x⌋₊ + 1 : ℝ) * Real.log p := by
      have hpk_pos : (0 : ℝ) < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) :=
        pow_pos (by exact_mod_cast hpprime.pos) _
      have hstepNat : ⌊x⌋₊ + 1 ≤ p ^ (p.log ⌊x⌋₊ + 1) := by
        simp only [← Nat.succ_eq_add_one] at hKlt' ⊢
        omega
      have hstepR : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by exact_mod_cast hstepNat
      have hfloor := Nat.lt_floor_add_one x
      have hR : x < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by linarith
      have hlog := Real.log_lt_log hxpos hR
      rw [Real.log_pow] at hlog
      push_cast at hlog
      linarith [hlog]
    exact quadraticLogPrimePowerCorrection_neg_le_half_log_mul_log x χ hχ hpprime hx hKle hKlt
  have hbudget : ∑ p ∈ S, Real.log p ≤ Real.log ((q / χ.conductor : ℕ) : ℝ) := by
    apply le_trans _ (sum_log_primeFactors_le_log hqd)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpdata := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hpdata.1, hpdata.2, hqd⟩
    · intro p _ _
      exact
        Real.log_nonneg
          (by
            exact_mod_cast
              (Nat.prime_of_mem_primeFactors
                  (by assumption : p ∈ (q / χ.conductor).primeFactors)).one_le)
  calc
    -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) ≤
        -(1 / 2 * (∑ p ∈ S, Real.log p) * Real.log x) :=
      by nlinarith [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hlogx, hbudget]
    _ = ∑ p ∈ S, -(1 / 2 * Real.log p * Real.log x) := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    _ ≤
        ∑ p ∈ S,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re :=
      Finset.sum_le_sum hstep

/--
Input/assumptions: a level-`q` character (no quadratic hypothesis), a cutoff `x ≥ 2`, and
`q / conductor ≠ 0`.
Conclusion: the logarithmic level-change correction is at least
`-(1/2) log(q / conductor) log x`, matching
`primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log_of_isQuadratic` without
assuming `χ.primitiveCharacter.IsQuadratic`.
Content: reindex to prime-outer form; at each quotient-support prime `p`, split on whether `p`
divides `χ.conductor`. If it does, `χ.primitiveCharacter p = 0` so every summand vanishes;
otherwise `p` is coprime to the conductor, so `‖χ.primitiveCharacter p‖ = 1` and the generic
Fejér bound `re_sum_logPrimePowerCorrection_neg_le_half_log_mul_log` applies, with the
exact-floor brackets supplied by `Nat.pow_log_le_self`/`Nat.lt_pow_succ_log_self` exactly as in
the quadratic version. Bound the resulting `Σ log p` by `log(q / conductor)` as before.
Role: is the generic replacement for the quadratic-only logarithmic consumer, the
affine-weight analogue of
`PseudoPrime.AnalyticNumberTheory.Arithmetic.`
`primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient`.
-/
theorem primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) ≤
      primitiveLogLevelChangeCorrection x χ := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [primitiveLogLevelChangeCorrection_eq_sum_prime_divisors]
  set S := (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor with hSdef
  have hstep :
    ∀ p ∈ S,
      -(1 / 2 * Real.log p * Real.log x) ≤
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hple : p ≤ ⌊x⌋₊ := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    have hxfloor : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
    have hKnat : p ^ p.log ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hxfloor
    have hKlt' : ⌊x⌋₊ < p ^ (p.log ⌊x⌋₊).succ := Nat.lt_pow_succ_log_self hpprime.one_lt ⌊x⌋₊
    by_cases hdvd : p ∣ χ.conductor
    · have hnotunit : ¬IsUnit ((p : ℕ) : ZMod χ.conductor) := by
        rw [ZMod.isUnit_prime_iff_not_dvd hpprime]
        exact not_not_intro hdvd
      have hz0 : χ.primitiveCharacter p = 0 := χ.primitiveCharacter.map_nonunit hnotunit
      have heach :
        ∀ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re = 0 := by
        intro k hk
        have hk0 : k ≠ 0 := by
          have := (Finset.mem_Icc.mp hk).1; omega
        rw [characterLogWeightedTerm_primitive_re_prime_pow x χ hxpos.ne' hpprime hk0, hz0,
          zero_pow hk0]
        simp only [Complex.zero_re, mul_zero]
      rw [Finset.sum_congr rfl heach, Finset.sum_const_zero]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hlogp) hlogx]
    · have hunit : IsUnit ((p : ℕ) : ZMod χ.conductor) :=
        (ZMod.isUnit_prime_iff_not_dvd hpprime).mpr hdvd
      have hz : ‖χ.primitiveCharacter p‖ = 1 := by
        have hval := χ.primitiveCharacter.unit_norm_eq_one hunit.unit
        rwa [hunit.unit_spec] at hval
      have hKle : (p.log ⌊x⌋₊ : ℝ) * Real.log p ≤ Real.log x := by
        have hpk_pos : (0 : ℝ) < (p : ℝ) ^ p.log ⌊x⌋₊ := pow_pos (by exact_mod_cast hpprime.pos) _
        have hKnatR : (p : ℝ) ^ p.log ⌊x⌋₊ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hKnat
        have hR : (p : ℝ) ^ p.log ⌊x⌋₊ ≤ x := hKnatR.trans (Nat.floor_le hxpos.le)
        have hlog := Real.log_le_log hpk_pos hR
        rwa [Real.log_pow] at hlog
      have hKlt : Real.log x < (p.log ⌊x⌋₊ + 1 : ℝ) * Real.log p := by
        have hpk_pos : (0 : ℝ) < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) :=
          pow_pos (by exact_mod_cast hpprime.pos) _
        have hstepNat : ⌊x⌋₊ + 1 ≤ p ^ (p.log ⌊x⌋₊ + 1) := by
          simp only [← Nat.succ_eq_add_one] at hKlt' ⊢
          omega
        have hstepR : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by exact_mod_cast hstepNat
        have hfloor := Nat.lt_floor_add_one x
        have hR : x < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by linarith
        have hlog := Real.log_lt_log hxpos hR
        rw [Real.log_pow] at hlog
        push_cast at hlog
        linarith [hlog]
      exact re_sum_logPrimePowerCorrection_neg_le_half_log_mul_log x χ hpprime hz hx hKle hKlt
  have hbudget : ∑ p ∈ S, Real.log p ≤ Real.log ((q / χ.conductor : ℕ) : ℝ) := by
    apply le_trans _ (sum_log_primeFactors_le_log hqd)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpdata := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hpdata.1, hpdata.2, hqd⟩
    · intro p _ _
      exact
        Real.log_nonneg
          (by
            exact_mod_cast
              (Nat.prime_of_mem_primeFactors
                  (by assumption : p ∈ (q / χ.conductor).primeFactors)).one_le)
  calc
    -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) ≤
        -(1 / 2 * (∑ p ∈ S, Real.log p) * Real.log x) :=
      by nlinarith [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hlogx, hbudget]
    _ = ∑ p ∈ S, -(1 / 2 * Real.log p * Real.log x) := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    _ ≤
        ∑ p ∈ S,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re :=
      Finset.sum_le_sum hstep

/--
Input/assumptions: `q ≠ 0`, a level-`q` character with quadratic primitive part, a cutoff
`x ≥ 2`, and `q / conductor ≠ 0`.
Conclusion: subtracting the logarithmic level-change correction from the conductor-scaled term
`(1/2)(log conductor)(log x)` is at most the level-scaled term `(1/2)(log q)(log x)`.
Content: apply the lower bound on the correction, then use `log(conductor) + log(q/conductor)
= log q` (from `conductor ∣ q` and `conductor ≠ 0`, via `Real.log_mul`), the affine-weight
analogue of
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption_of_isQuadratic`.
Role: is the conductor absorption theorem: it moves the exact logarithmic correction from a
free-standing quotient term into `(log conductor)(log x)/2`, with no
positive residual left over and without ever coarsening to `(q / conductor).primeFactors.card`.
-/
theorem primitiveLogConductorAbsorption_of_isQuadratic {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (hqd : q / χ.conductor ≠ 0) :
    1 / 2 * Real.log (χ.conductor : ℝ) * Real.log x - primitiveLogLevelChangeCorrection x χ ≤
      1 / 2 * Real.log (q : ℝ) * Real.log x := by
  have hbound :=
    primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log_of_isQuadratic x χ hχ hx hqd
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hdpos : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  have hprod : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hdvd
  have hlogsum :
    Real.log (χ.conductor : ℝ) + Real.log ((q / χ.conductor : ℕ) : ℝ) = Real.log (q : ℝ) := by
    rw [← Real.log_mul hdpos (by exact_mod_cast hqd)]
    congr 1
    exact_mod_cast hprod
  have hgoal_equiv :
    1 / 2 * Real.log (χ.conductor : ℝ) * Real.log x - 1 / 2 * Real.log (q : ℝ) * Real.log x =
      -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) := by
    rw [← hlogsum]
    ring
  linarith [hbound, hgoal_equiv]

/--
Input/assumptions: `q ≠ 0`, a level-`q` character (no quadratic hypothesis), a cutoff `x ≥ 2`,
and `q / conductor ≠ 0`.
Conclusion: subtracting the logarithmic level-change correction from the conductor-scaled term
`(1/2)(log conductor)(log x)` is at most the level-scaled term `(1/2)(log q)(log x)`.
Content: same as `primitiveLogConductorAbsorption_of_isQuadratic`, but built on the generic
bound `primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log` instead of the
quadratic-only one.
Role: is the generic logarithmic conductor absorption theorem, the affine-weight analogue of
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption`.
-/
theorem primitiveLogConductorAbsorption {q : ℕ} [NeZero q] (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    1 / 2 * Real.log (χ.conductor : ℝ) * Real.log x - primitiveLogLevelChangeCorrection x χ ≤
      1 / 2 * Real.log (q : ℝ) * Real.log x := by
  have hbound := primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log x χ hx hqd
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hdpos : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  have hprod : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hdvd
  have hlogsum :
    Real.log (χ.conductor : ℝ) + Real.log ((q / χ.conductor : ℕ) : ℝ) = Real.log (q : ℝ) := by
    rw [← Real.log_mul hdpos (by exact_mod_cast hqd)]
    congr 1
    exact_mod_cast hprod
  have hgoal_equiv :
    1 / 2 * Real.log (χ.conductor : ℝ) * Real.log x - 1 / 2 * Real.log (q : ℝ) * Real.log x =
      -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) := by
    rw [← hlogsum]
    ring
  linarith [hbound, hgoal_equiv]

/--
Input/assumptions: a positive cutoff and a level-`q` character with `q ≠ 0`.
Conclusion: the logarithmic level-change correction is at least minus half the number of prime
factors of the complementary quotient times `(log x) ^ 2`.
Content: the exact level-change identity gives minus the correction as the real part of the
(level − primitive) difference; bound that real part by the norm, already bounded by the coarse
weighted-sum estimate.
Role: is the coarsening step turning the exact logarithmic correction into the same quantity
already consumed by the safe quotient route.
-/
theorem primitiveLogLevelChangeCorrection_ge_neg {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) :
    -((1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2) ≤
      primitiveLogLevelChangeCorrection x χ := by
  have hexact := characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection x χ
  have hnorm := norm_characterLogWeightedSum_sub_primitive_le x χ hx
  have hre :=
    Complex.re_le_norm
      (characterLogWeightedSum x χ - characterLogWeightedSum x χ.primitiveCharacter)
  rw [Complex.sub_re] at hre
  linarith

end PseudoPrime.AnalyticNumberTheory.Arithmetic
