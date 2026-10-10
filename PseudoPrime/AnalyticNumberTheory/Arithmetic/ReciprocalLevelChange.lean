/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.FejerConvexSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ConductorPrimeSupport
public import PseudoPrime.Analysis.RealLog

/-!
# Reciprocal level-change identities

This file records exact and bounded transformations of reciprocal character sums when the
conductor level changes.  The declarations separate the algebraic prime-power expansion from
the later comparison and majorization estimates.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/--
Input/assumptions: a level-`q` character and a real cutoff `x` (no positivity assumption).
Conclusion: the complementary conductor quotient contributes an explicit finite sum over its
prime powers, with the original reciprocal weight retained.
Content: this is the exact prime-power form of the quotient support before any geometric-tail or
prime-factor majorization.
Role: is the reciprocal ledger entry to be combined with the logarithmic level-change ledger
in the final combined inequality.
-/
noncomputable def primitiveReciprocalQuotientPrimePowerCorrection {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ q / χ.conductor,
      reciprocalWeightedMangoldtTerm x (p ^ k)

/--
Input/assumptions: a cutoff `x ≥ 0` and a level-`q` character.
Conclusion: the exact quotient prime-power correction equals the common-factor reciprocal sum of
`q / conductor`.
Content: specialize the finite prime-power decomposition of the common-factor support.
Role: identifies the prime-power sum with `commonFactorReciprocalWeightedSum x (q / conductor)`
before replacing it by a geometric upper bound.
-/
theorem primitiveReciprocalQuotientPrimePowerCorrection_eq_commonFactor {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) :
    primitiveReciprocalQuotientPrimePowerCorrection x χ =
      commonFactorReciprocalWeightedSum x (q / χ.conductor) := by
  rw [primitiveReciprocalQuotientPrimePowerCorrection,
    commonFactorReciprocalWeightedSum_eq_sum_prime_powers (q / χ.conductor) hx]

/--
Input/assumptions: a cutoff and a level-`q` character.
Conclusion: the original-to-primitive reciprocal level change is recorded as the finite sum of
primitive character contributions on the complementary quotient support.
Content: terms sharing the quotient are zero for the level character; terms away from it agree
with the primitive character.
Role: retains the signed reciprocal correction
`Σ_{0<n≤x, (n,q/conductor)>1} Λ(n)/n * (1-n/x) * Re χ̃(n)` before prime-power reindexing.
-/
noncomputable def primitiveReciprocalLevelChangeCorrection {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
    (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re

/--
Input/assumptions: a cutoff, a level-`q` character, a prime `p`, and a nonzero exponent `k`.
Conclusion: the level-change correction's prime-power summand has the explicit closed form
carrying the geometric reciprocal weight times the real part of `χ̃(p) ^ k`.
Content: specialize the reciprocal weighted Mangoldt term at a prime power and separate the real
scalar factor from the primitive character value.
Role: supplies the reciprocal weight `log p / p^k * (1-p^k/x)` explicitly for each prime
and positive exponent, so logarithmic and reciprocal corrections can be compared termwise.
-/
theorem characterReciprocalWeightedTerm_primitive_re_prime_pow {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
      Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) * (χ.primitiveCharacter p ^ k).re := by
  rw [characterReciprocalWeightedTerm, reciprocalWeightedMangoldtTerm_prime_pow hp hk, Nat.cast_pow,
    map_pow, Complex.re_ofReal_mul]

/--
For a prime `p` with unit primitive-character value and endpoints
`p^K ≤ x ≤ p^(K+1)`, `x ≥ 2`, the reciprocal prime-power correction is at least
`-(1-1/x) * log p / 2`. Rewrite the summands as reciprocal weights times
real parts of character powers and apply the Fejér bound for level corrections.
-/
theorem re_sum_reciprocalPrimePowerCorrection_neg_le_half_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) (hz : ‖χ.primitiveCharacter p‖ = 1)
    (hx : 2 ≤ x) {K : ℕ} (_hK : 1 ≤ K) (hKle : (p : ℝ) ^ K ≤ x) (hKup : x ≤ (p : ℝ) ^ (K + 1)) :
    -(1 / 2 * (1 - 1 / x) * Real.log p) ≤
      ∑ k ∈ Finset.Icc 1 K,
        (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set z : ℂ := χ.primitiveCharacter p with hzdef
  set r : ℝ := 1 / (p : ℝ) with hrdef
  set c : ℝ := 1 / x with hcdef
  have hr0 : 0 < r := by
    rw [hrdef]
    exact one_div_pos.mpr hppos
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hppos]
    exact hp1
  have hc1 : r ^ (K + 1) ≤ c := by
    rw [hrdef, hcdef, one_div_pow]
    exact one_div_le_one_div_of_le hxpos hKup
  have hc2 : c ≤ r ^ K := by
    rw [hrdef, hcdef, one_div_pow]
    exact one_div_le_one_div_of_le (pow_pos hppos K) hKle
  have hpk0 : ∀ k : ℕ, ((p : ℝ) ^ k) ≠ 0 := fun k => pow_ne_zero k hppos.ne'
  have heach :
    ∀ k ∈ Finset.Icc 1 K,
      (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
        Real.log p * (r ^ k - c) * (z ^ k).re := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1
      exact Nat.ne_of_gt this
    rw [characterReciprocalWeightedTerm_primitive_re_prime_pow x χ hp hk0]
    have hcoef : Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) = Real.log p * (r ^ k - c) := by
      rw [hrdef, hcdef, one_div_pow]
      field_simp [hpk0 k, hxpos.ne']
    rw [hcoef]
  have hfejer :=
    re_sum_reciprocalWeight_ge_neg_half (r := r) (c := c) (K := K) (z := z) hz hr0 hr1 hc1 hc2
  have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hstep2 :
    ∀ k ∈ Finset.Icc 1 K, (((r ^ k - c : ℝ) : ℂ) * z ^ k).re = (r ^ k - c) * (z ^ k).re := by
    intro k _
    rw [Complex.re_ofReal_mul]
  have hsum_eq :
    (Finset.sum (Finset.Icc 1 K) fun k => ((r ^ k - c : ℝ) : ℂ) * z ^ k).re =
      Finset.sum (Finset.Icc 1 K) fun k => (r ^ k - c) * (z ^ k).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl hstep2
  rw [hsum_eq] at hfejer
  rw [Finset.sum_congr rfl heach]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  have := mul_le_mul_of_nonneg_left hfejer hlogp0
  nlinarith only [this]

/--
Input/assumptions: a cutoff and a level-`q` character.
Conclusion: the reciprocal level-change correction is a double sum with the quotient-support
prime outermost and its admissible exponents `1..Nat.log p ⌊x⌋₊` innermost.
Content: reindex the prime-power expansion using
`PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_primePow_eq_sum_primesLE`, mirroring
`PseudoPrime.AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_eq_sum_prime_divisors`.
Role: lets the per-prime lower bound be summed over `Nat.primesLE ⌊x⌋₊` directly.
-/
theorem primitiveReciprocalLevelChangeCorrection_eq_sum_prime_divisors {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    primitiveReciprocalLevelChangeCorrection x χ =
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  rw [primitiveReciprocalLevelChangeCorrection, ← Finset.Icc_add_one_left_eq_Ioc]
  calc
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n,
          if ¬Nat.Coprime n (q / χ.conductor) then
            (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re
          else 0 :=
      by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hpow : IsPrimePow n
      · simp only [hpow, ↓reduceIte]
      · rw [show (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re = 0 from by
            simp only [characterReciprocalWeightedTerm,
              reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow hpow, Complex.ofReal_zero,
              zero_mul, Complex.zero_re]]
        simp only [ite_self]
    _ =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            if ¬Nat.Coprime (p ^ k) (q / χ.conductor) then
              (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re
            else 0 :=
      by
      exact
        sum_primePow_eq_sum_primesLE
          (fun n ↦
            if ¬Nat.Coprime n (q / χ.conductor) then
              (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re
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
For `x ≥ 2` and nonzero conductor quotient, the reciprocal level correction
is at least `-(1-1/x) * log(q / χ.conductor) / 2`. Reindex by quotient primes,
use vanishing at conductor primes and the Fejér bound elsewhere, then bound
the prime logarithm sum. This supplies reciprocal conductor absorption.
-/
theorem primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    -(1 / 2 * (1 - 1 / x) * Real.log ((q / χ.conductor : ℕ) : ℝ)) ≤
      primitiveReciprocalLevelChangeCorrection x χ := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hxfrac : 0 ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hxpos]
    exact le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  rw [primitiveReciprocalLevelChangeCorrection_eq_sum_prime_divisors]
  set S := (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor with hSdef
  have hstep :
    ∀ p ∈ S,
      -(1 / 2 * (1 - 1 / x) * Real.log p) ≤
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hple : p ≤ ⌊x⌋₊ := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hK1 : 1 ≤ p.log ⌊x⌋₊ := Nat.log_pos hpprime.one_lt hple
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    by_cases hdvd : p ∣ χ.conductor
    · have hnotunit : ¬IsUnit ((p : ℕ) : ZMod χ.conductor) := by
        rw [ZMod.isUnit_prime_iff_not_dvd hpprime]
        exact not_not_intro hdvd
      have hz0 : χ.primitiveCharacter p = 0 := χ.primitiveCharacter.map_nonunit hnotunit
      have heach :
        ∀ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re = 0 := by
        intro k hk
        have hk0 : k ≠ 0 := by
          have := (Finset.mem_Icc.mp hk).1
          exact Nat.ne_of_gt this
        rw [characterReciprocalWeightedTerm_primitive_re_prime_pow x χ hpprime hk0, hz0,
          zero_pow hk0]
        simp only [Complex.zero_re, mul_zero]
      rw [Finset.sum_congr rfl heach, Finset.sum_const_zero]
      nlinarith only [mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac) hlogp]
    · have hunit : IsUnit ((p : ℕ) : ZMod χ.conductor) :=
        (ZMod.isUnit_prime_iff_not_dvd hpprime).mpr hdvd
      have hxfloor : ⌊x⌋₊ ≠ 0 :=
        (Nat.floor_pos.mpr (le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx)).ne'
      have hz : ‖χ.primitiveCharacter p‖ = 1 := by
        have hval := χ.primitiveCharacter.unit_norm_eq_one hunit.unit
        rwa [hunit.unit_spec] at hval
      have hKnat : p ^ p.log ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hxfloor
      have hKnatR : (p : ℝ) ^ (p.log ⌊x⌋₊) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hKnat
      have hKle : (p : ℝ) ^ (p.log ⌊x⌋₊) ≤ x := hKnatR.trans (Nat.floor_le hxpos.le)
      have hKup : x ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by
        have hlt : ⌊x⌋₊ < p ^ (p.log ⌊x⌋₊).succ := Nat.lt_pow_succ_log_self hpprime.one_lt ⌊x⌋₊
        have hltR : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have hcast : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by
          have : ⌊x⌋₊ + 1 ≤ p ^ (p.log ⌊x⌋₊ + 1) := hlt
          exact_mod_cast this
        exact le_of_lt (lt_of_lt_of_le hltR hcast)
      exact re_sum_reciprocalPrimePowerCorrection_neg_le_half_log x χ hpprime hz hx hK1 hKle hKup
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
    -(1 / 2 * (1 - 1 / x) * Real.log ((q / χ.conductor : ℕ) : ℝ)) ≤
        -(1 / 2 * (1 - 1 / x) * ∑ p ∈ S, Real.log p) :=
      by nlinarith only [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac, hbudget]
    _ = ∑ p ∈ S, -(1 / 2 * (1 - 1 / x) * Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤
        ∑ p ∈ S,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            (characterReciprocalWeightedTerm x χ.primitiveCharacter (p ^ k)).re :=
      Finset.sum_le_sum hstep

/--
For nonzero level `q`, `x ≥ 2`, and nonzero conductor quotient, subtracting
the reciprocal level correction from `(1-1/x) * log(χ.conductor) / 2` is at most
`(1-1/x) * log q / 2`. Combine the correction lower bound with the logarithm
of the conductor quotient to obtain a level-based weighted estimate.
-/
theorem primitiveReciprocalConductorAbsorption {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    1 / 2 * (1 - 1 / x) * Real.log (χ.conductor : ℝ) -
        primitiveReciprocalLevelChangeCorrection x χ ≤
      1 / 2 * (1 - 1 / x) * Real.log (q : ℝ) := by
  have hbound := primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient x χ hx hqd
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hdpos : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  have hprod : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hdvd
  have hlogsum :
    Real.log (χ.conductor : ℝ) + Real.log ((q / χ.conductor : ℕ) : ℝ) = Real.log (q : ℝ) := by
    rw [← Real.log_mul hdpos (by exact_mod_cast hqd)]
    congr 1
    exact_mod_cast hprod
  have hgoal_equiv :
    1 / 2 * (1 - 1 / x) * Real.log (χ.conductor : ℝ) - 1 / 2 * (1 - 1 / x) * Real.log (q : ℝ) =
      -(1 / 2 * (1 - 1 / x) * Real.log ((q / χ.conductor : ℕ) : ℝ)) := by
    rw [← hlogsum]
    ring
  linarith only [hbound, hgoal_equiv]

/--
Input/assumptions: a cutoff and a level-`q` character.
Conclusion: the primitive reciprocal sum equals the level-character reciprocal sum plus the
character-sensitive complementary-quotient correction.
Content: partition the finite cutoff into the coprime quotient support, where the characters
agree, and its complement, where the level character vanishes.
Role: gives the reciprocal sum its exact level-change identity before any norm or prime-factor
majorization.
-/
theorem characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    (characterReciprocalWeightedSum x χ.primitiveCharacter).re =
      (characterReciprocalWeightedSum x χ).re + primitiveReciprocalLevelChangeCorrection x χ := by
  rw [characterReciprocalWeightedSum, characterReciprocalWeightedSum,
    primitiveReciprocalLevelChangeCorrection]
  simp only [Complex.re_sum]
  let S := Finset.Ioc 0 ⌊x⌋₊
  let p : ℕ → Prop := fun n ↦ Nat.Coprime n (q / χ.conductor)
  have hprimitive :
    ∑ n ∈ S, (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re =
      (∑ n ∈ S.filter p, (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re) +
        ∑ n ∈ S.filter fun n ↦ ¬p n,
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re := by
    exact
      (Finset.sum_filter_add_sum_filter_not (s := S) (f := fun n ↦
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re) (p := p)).symm
  have hlevel :
    ∑ n ∈ S, (characterReciprocalWeightedTerm x χ n).re =
      ∑ n ∈ S.filter p, (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re := by
    have hin :
      ∑ n ∈ S.filter p, (characterReciprocalWeightedTerm x χ n).re =
        ∑ n ∈ S.filter p, (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re := by
      apply Finset.sum_congr rfl
      intro n hn
      have hcop : Nat.Coprime n (q / χ.conductor) := Finset.mem_filter.mp hn |>.2
      rw [characterReciprocalWeightedTerm, characterReciprocalWeightedTerm,
        apply_eq_primitiveCharacter_of_coprime_quotient χ hcop]
    have houtside :
      ∑ n ∈ S.filter fun n ↦ ¬p n, (characterReciprocalWeightedTerm x χ n).re = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hquotient : ¬Nat.Coprime n (q / χ.conductor) := Finset.mem_filter.mp hn |>.2
      rw [characterReciprocalWeightedTerm_eq_zero_of_not_coprime_quotient x χ hquotient]
      simp only [Complex.zero_re]
    calc
      ∑ n ∈ S, (characterReciprocalWeightedTerm x χ n).re =
          (∑ n ∈ S.filter p, (characterReciprocalWeightedTerm x χ n).re) +
            ∑ n ∈ S.filter fun n ↦ ¬p n, (characterReciprocalWeightedTerm x χ n).re :=
        (Finset.sum_filter_add_sum_filter_not (s := S) (f := fun n ↦
            (characterReciprocalWeightedTerm x χ n).re) (p := p)).symm
      _ = ∑ n ∈ S.filter p, (characterReciprocalWeightedTerm x χ n).re := by rw [houtside, add_zero]
      _ = _ := hin
  rw [hprimitive]
  rw [hlevel]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
