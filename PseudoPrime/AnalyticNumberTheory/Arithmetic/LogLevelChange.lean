/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.FejerConvexSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Comparing an imprimitive character with its primitive character

This file formalizes the logarithmic level-change identity.  It proves the arithmetic support
statement behind that identity:
the two character values can differ only at integers sharing a factor with the quotient of the
level by the conductor.  It then restricts the weighted-sum difference to exactly that support.
-/

@[expose] public section

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
  linarith only [hre, hzero]

/--
For a prime `p` with `‖χ.primitiveCharacter p‖ = 1`, `x ≥ 2`, and `K` bracketing
`log x / log p`, the logarithmic prime-power correction is at least
`-(log p * log x)/2`. Rewrite the terms using powers of the unit character value
and apply the Fejér affine-weight bound. This controls each prime in the level correction.
-/
theorem re_sum_logPrimePowerCorrection_neg_le_half_log_mul_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) (hz : ‖χ.primitiveCharacter p‖ = 1)
    (hx : 2 ≤ x) {K : ℕ} (hKle : (K : ℝ) * Real.log p ≤ Real.log x)
    (hKlt : Real.log x < (K + 1 : ℝ) * Real.log p) :
    -(1 / 2 * Real.log p * Real.log x) ≤
      ∑ k ∈ Finset.Icc 1 K, (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re := by
  have hxpos : (0 : ℝ) < x := by exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  set z : ℂ := χ.primitiveCharacter p with hzdef
  set θ : ℝ := Real.log x / Real.log p - (K : ℝ) with hθdef
  have hlogX : Real.log x = ((K : ℝ) + θ) * Real.log p := by
    rw [hθdef]
    field_simp [hlogp.ne']
    ring
  have hθ0 : 0 ≤ θ := by
    rw [hθdef, sub_nonneg, le_div_iff₀ hlogp]
    linarith only [hKle]
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, sub_le_iff_le_add, div_le_iff₀ hlogp]
    linarith only [hKlt]
  have heach :
    ∀ k ∈ Finset.Icc 1 K,
      (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re =
        Real.log p * ((Real.log x - (k : ℝ) * Real.log p) * (z ^ k).re) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one this)
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
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl hstep2
  rw [hsum_eq] at hfejer
  rw [Finset.sum_congr rfl heach, ← Finset.mul_sum]
  have hlogp0 : 0 ≤ Real.log p := hlogp.le
  have := mul_le_mul_of_nonneg_left hfejer hlogp0
  nlinarith only [this]

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
For `x ≥ 2` and `q / χ.conductor ≠ 0`, the logarithmic level-change correction
is at least `-log(q / χ.conductor) * log x / 2`. Reindex by quotient primes,
discard primes dividing the conductor, and apply the unit-circle Fejér bound
to the remaining primes. The prime logarithm sum gives the conductor absorption bound.
-/
theorem primitiveLogLevelChangeCorrection_ge_neg_half_log_quotient_mul_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    -(1 / 2 * Real.log ((q / χ.conductor : ℕ) : ℝ) * Real.log x) ≤
      primitiveLogLevelChangeCorrection x χ := by
  have hxpos : (0 : ℝ) < x := by exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hlogx : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx)
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
    have hxfloor : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr ((Real.log_nonneg_iff hxpos).mp hlogx)).ne'
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
          have := (Finset.mem_Icc.mp hk).1
          exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one this)
        rw [characterLogWeightedTerm_primitive_re_prime_pow x χ hxpos.ne' hpprime hk0, hz0,
          zero_pow hk0]
        simp only [Complex.zero_re, mul_zero]
      rw [Finset.sum_congr rfl heach, Finset.sum_const_zero]
      nlinarith only [mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hlogp) hlogx]
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
          exact Nat.succ_le_of_lt hKlt'
        have hstepR : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by exact_mod_cast hstepNat
        have hfloor := Nat.lt_floor_add_one x
        have hR : x < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by exact lt_of_lt_of_le hfloor hstepR
        have hlog := Real.log_lt_log hxpos hR
        rw [Real.log_pow] at hlog
        push_cast at hlog
        exact hlog
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
      by nlinarith only [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hlogx, hbudget]
    _ = ∑ p ∈ S, -(1 / 2 * Real.log p * Real.log x) := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    _ ≤
        ∑ p ∈ S,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            (characterLogWeightedTerm x χ.primitiveCharacter (p ^ k)).re :=
      Finset.sum_le_sum hstep

/--
For nonzero level `q`, `x ≥ 2`, and nonzero conductor quotient, subtracting the
logarithmic level correction from `log(χ.conductor) * log x / 2` is at most
`log q * log x / 2`. Combine the correction lower bound with the logarithm
of the conductor quotient. This expresses the weighted estimate in terms of the level.
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
  linarith only [hbound, hgoal_equiv]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
