/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
import PseudoPrime.AnalyticNumberTheory.Arithmetic.FejerConvexSums
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ConductorPrimeSupport
import PseudoPrime.Analysis.RealLog

/-!
# Reciprocal level-change identities

This file records exact and bounded transformations of reciprocal character sums when the
conductor level changes.  The declarations separate the algebraic prime-power expansion from
the later comparison and majorization estimates.
-/

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
    primitiveReciprocalQuotientPrimePowerCorrection x
        χ =
      commonFactorReciprocalWeightedSum x
        (q / χ.conductor) := by
  rw [primitiveReciprocalQuotientPrimePowerCorrection,
    commonFactorReciprocalWeightedSum_eq_sum_prime_powers
      (q / χ.conductor) hx]

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
    (characterReciprocalWeightedTerm x
        χ.primitiveCharacter n).re

/--
Input/assumptions: a cutoff `x ≥ 0` and a level-`q` character.
Conclusion: the character-sensitive level-change correction is a double sum over powers of
primes dividing the complementary quotient, each retaining the real part of the primitive
character value at that prime power.
Content: reindex the level-change correction support by exponent and prime, using that the
reciprocal weighted summand vanishes off prime powers.
Role: exposes the terms `log p / p^k * (1-p^k/x) * Re(χ̃(p)^k)` on the same `(k,p)`
index set as the logarithmic terms `log p * (log x-k*log p) * Re(χ̃(p)^k)`.
-/
theorem primitiveReciprocalLevelChangeCorrection_eq_sum_prime_powers {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) :
    primitiveReciprocalLevelChangeCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ q / χ.conductor,
          (characterReciprocalWeightedTerm x
              χ.primitiveCharacter (p ^ k)).re := by
  rw [primitiveReciprocalLevelChangeCorrection]
  exact
    sum_not_coprime_eq_sum_prime_powers
      (fun n ↦
        (characterReciprocalWeightedTerm x
            χ.primitiveCharacter n).re)
      (q / χ.conductor) hx fun n hn ↦ by
      simp only [characterReciprocalWeightedTerm,
        reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow
            hn,
        Complex.ofReal_zero, zero_mul, Complex.zero_re]

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
    (characterReciprocalWeightedTerm x
          χ.primitiveCharacter (p ^ k)).re =
      Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) * (χ.primitiveCharacter p ^ k).re := by
  rw [characterReciprocalWeightedTerm,
    reciprocalWeightedMangoldtTerm_prime_pow hp hk,
    Nat.cast_pow, map_pow, Complex.re_ofReal_mul]

/--
Input/assumptions: a cutoff, a level-`q` character whose primitive inducing character is
quadratic, a prime `p`, and a nonzero exponent `k`.
Conclusion: the reciprocal level-change correction's prime-power summand has the explicit closed
form carrying the geometric reciprocal weight times `χ̃(p)` when `k` is odd, and times `χ̃(p) ^ 2`
when `k` is even.
Content: apply the quadratic parity expansion `isQuadratic_pow_apply` to the closed form already
established for a general character.
Role: is the quadratic closed form for the reciprocal quotient correction, matching
`PseudoPrime.AnalyticNumberTheory.Arithmetic.`
`characterLogWeightedTerm_primitive_re_prime_pow_of_isQuadratic` in shape, so the reciprocal
and logarithmic sums can be combined term by term for quadratic primitive characters.
-/
theorem characterReciprocalWeightedTerm_primitive_re_prime_pow_of_isQuadratic {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) :
    (characterReciprocalWeightedTerm x
          χ.primitiveCharacter (p ^ k)).re =
      Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) *
        (if Odd k then (χ.primitiveCharacter p).re else (χ.primitiveCharacter p ^ 2).re) := by
  rw [characterReciprocalWeightedTerm_primitive_re_prime_pow
      x χ hp hk,
    NumberTheory.isQuadratic_pow_apply hχ (p : ZMod χ.conductor) hk,
    apply_ite Complex.re]

/--
Input/assumptions: a cutoff `x ≥ 0` and a level-`q` character whose primitive inducing character is
quadratic.
Conclusion: the reciprocal level-change correction is the double sum over quotient prime powers
of the geometric weight times `χ̃(p)` on odd exponents, and times a coprime-to-conductor
indicator (no character value) on even exponents.
Content: combine the prime-power expansion with the quadratic closed form and the
coprime-to-conductor indicator for the squared value.
Role: reduces the even-exponent character factor to `1` when `p` is coprime to the conductor
and `0` otherwise, leaving only the odd-exponent factor `Re χ̃(p)` to control.
-/
theorem primitiveReciprocalLevelChangeCorrection_eq_sum_of_isQuadratic {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 0 ≤ x) :
    primitiveReciprocalLevelChangeCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ q / χ.conductor,
          Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) *
            (if Odd k then (χ.primitiveCharacter p).re
            else if Nat.Coprime p χ.conductor then 1 else 0) := by
  rw [primitiveReciprocalLevelChangeCorrection_eq_sum_prime_powers
      x χ hx]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  have hkpos : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  rw [characterReciprocalWeightedTerm_primitive_re_prime_pow_of_isQuadratic
      x χ hχ hpprime hkpos]
  by_cases hodd : Odd k
  · simp only [hodd, ↓reduceIte]
  · simp only [ite_eq_right hodd]
    rw [primitiveCharacter_sq_apply_re_eq_ite_of_isQuadratic
        χ hχ p]

/--
Input/assumptions: a level-`q` character with quadratic primitive part, a prime `p`, a cutoff
`x ≥ 2`, and `K ≥ 1` with `p ^ K ≤ x`.
Conclusion: the finite reciprocal prime-power sum over `k = 1..K` at `p` is at least
`-(1/2)(1 - 1/x) log p`.
Content: case on the three possible values of `χ̃(p)`.  When `χ̃(p) = 0` every summand vanishes;
when `χ̃(p) = 1` every summand is nonnegative; when `χ̃(p) = -1` the sum is `-log p` times the
alternating geometric partial sum bounded above by `1/p - 1/x ≤ (1/2)(1 - 1/x)` (using `p ≥ 2`)
in `PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_neg_one_pow_succ_mul_inv_pow_bounds`.
Role: is the local reciprocal alternating bound: the worst-case loss from any single
quotient-support prime is controlled by half its log, independently of the character's sign at
that prime.
-/
theorem quadraticReciprocalPrimePowerCorrection_neg_le_half_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hx : 2 ≤ x) {K : ℕ} (hK : 1 ≤ K) (hKle : (p : ℝ) ^ K ≤ x) :
    -(1 / 2 * (1 - 1 / x) * Real.log p) ≤
      ∑ k ∈ Finset.Icc 1 K,
        (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re := by
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hxfrac : 0 ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hxpos]; linarith only [hx]
  have heach :
    ∀ k ∈ Finset.Icc 1 K,
      (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re =
        Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) * (χ.primitiveCharacter p ^ k).re := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1; omega
    exact
      characterReciprocalWeightedTerm_primitive_re_prime_pow
        x χ hp hk0
  rw [Finset.sum_congr rfl heach]
  rcases hχ (p : ZMod χ.conductor) with h0 | h1 | hm1
  · have hzero :
      ∀ k ∈ Finset.Icc 1 K,
        Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) * (χ.primitiveCharacter p ^ k).re = 0 := by
      intro k hk
      have hk0 : k ≠ 0 := by
        have := (Finset.mem_Icc.mp hk).1; omega
      rw [h0, zero_pow hk0]
      simp only [Complex.zero_re, mul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    nlinarith only [mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac) hlogp]
  · have hone :
      ∀ k ∈ Finset.Icc 1 K,
        Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) * (χ.primitiveCharacter p ^ k).re =
          Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) := by
      intro k hk
      rw [h1, one_pow]
      simp only [Complex.one_re, mul_one]
    rw [Finset.sum_congr rfl hone]
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 K, Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) := by
      apply Finset.sum_nonneg
      intro k hk
      have hpk : (p : ℝ) ^ k ≤ x :=
        (pow_le_pow_right₀ (by exact_mod_cast hp.one_le) (Finset.mem_Icc.mp hk).2).trans hKle
      have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.pos) k
      apply mul_nonneg (div_nonneg hlogp hpkpos.le)
      rw [sub_nonneg, div_le_one hxpos]
      exact hpk
    nlinarith only [hnonneg,
      mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac) hlogp]
  · have hSeq :
      ∑ k ∈ Finset.Icc 1 K,
          Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) * (χ.primitiveCharacter p ^ k).re =
        Real.log p * (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ k * (1 / (p : ℝ) ^ k - 1 / x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hcast : χ.primitiveCharacter p = ((-1 : ℝ) : ℂ) := by
        rw [hm1]
        norm_num only [Complex.ofReal_neg, Complex.ofReal_one]
      have hre : (χ.primitiveCharacter p ^ k).re = (-1 : ℝ) ^ k := by
        rw [hcast, ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hre]
      have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.pos) k
      field_simp
    have hSflip :
      ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ k * (1 / (p : ℝ) ^ k - 1 / x) =
        -(∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * (1 / (p : ℝ) ^ k - 1 / x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring
    rw [hSeq, hSflip]
    have hgeom :=
      sum_neg_one_pow_succ_mul_inv_pow_bounds hp hxpos
        hK hKle
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hnum : 1 / (p : ℝ) - 1 / x ≤ 1 / 2 * (1 - 1 / x) := by
      have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num only) hp2
      have h2 : 1 / (2 * x) ≤ 1 / x := one_div_le_one_div_of_le hxpos (by linarith only [hxpos])
      have h3 : 1 / (2 * x) = 1 / 2 * (1 / x) := by ring
      nlinarith only [h1, h2, h3]
    nlinarith only [hgeom.2, hlogp, mul_le_mul_of_nonneg_left hnum hlogp]

/--
Input/assumptions: a cutoff `x ≥ 2`, a level-`q` character,
  a prime `p` at which the primitive character
  has unit norm (in particular `p` is coprime to the conductor), and `K ≥ 1` whose
  endpoints bracket `x` as `p ^ K ≤ x ≤ p ^ (K + 1)`.
Conclusion: the finite reciprocal prime-power sum over `k = 1..K` at `p` is at least
  `-(1/2)(1 - 1/x) log p`, with no quadratic hypothesis on the character.
Content: rewrite each summand as `log p * ((1/p)^k - 1/x) * Re(z^k)` with `z := χ̃(p)`, `‖z‖ = 1`,
  then apply the generic Fejér reciprocal-weight bound
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.re_sum_reciprocalWeight_ge_neg_half`
  with `r := 1/p`, `c := 1/x`.
Role: is the `hquad`-free replacement for
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.`
  `quadraticReciprocalPrimePowerCorrection_neg_le_half_log`.
For `K = p.log ⌊x⌋₊` and `p ≤ ⌊x⌋₊`, the integer logarithm provides the required brackets.
-/
theorem re_sum_reciprocalPrimePowerCorrection_neg_le_half_log {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) (hz : ‖χ.primitiveCharacter p‖ = 1)
    (hx : 2 ≤ x) {K : ℕ} (_hK : 1 ≤ K) (hKle : (p : ℝ) ^ K ≤ x) (hKup : x ≤ (p : ℝ) ^ (K + 1)) :
    -(1 / 2 * (1 - 1 / x) * Real.log p) ≤
      ∑ k ∈ Finset.Icc 1 K,
        (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re := by
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set z : ℂ := χ.primitiveCharacter p with hzdef
  set r : ℝ := 1 / (p : ℝ) with hrdef
  set c : ℝ := 1 / x with hcdef
  have hr0 : 0 < r := by
    rw [hrdef]; positivity
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hppos]; exact hp1
  have hc1 : r ^ (K + 1) ≤ c := by
    rw [hrdef, hcdef, one_div_pow]
    exact one_div_le_one_div_of_le hxpos hKup
  have hc2 : c ≤ r ^ K := by
    rw [hrdef, hcdef, one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) hKle
  have hpk0 : ∀ k : ℕ, ((p : ℝ) ^ k) ≠ 0 := fun k => by positivity
  have heach :
    ∀ k ∈ Finset.Icc 1 K,
      (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re =
        Real.log p * (r ^ k - c) * (z ^ k).re := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1; omega
    rw [characterReciprocalWeightedTerm_primitive_re_prime_pow
        x χ hp hk0]
    have hcoef : Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) = Real.log p * (r ^ k - c) := by
      rw [hrdef, hcdef, one_div_pow]
      field_simp
    rw [hcoef]
  have hfejer :=
    re_sum_reciprocalWeight_ge_neg_half (r := r) (c :=
      c) (K := K) (z := z) hz hr0 hr1 hc1 hc2
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
          (characterReciprocalWeightedTerm x
              χ.primitiveCharacter (p ^ k)).re := by
  rw [primitiveReciprocalLevelChangeCorrection, ←
    Finset.Icc_add_one_left_eq_Ioc]
  calc
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n (q / χ.conductor),
          (characterReciprocalWeightedTerm x
              χ.primitiveCharacter n).re =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n,
          if ¬Nat.Coprime n (q / χ.conductor) then
            (characterReciprocalWeightedTerm x
                χ.primitiveCharacter n).re
          else 0 :=
      by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hpow : IsPrimePow n
      · simp only [hpow, ↓reduceIte]
      · rw [show
            (characterReciprocalWeightedTerm x
                  χ.primitiveCharacter n).re =
              0
            from by
            simp only [characterReciprocalWeightedTerm,
              reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow
                  hpow,
              Complex.ofReal_zero, zero_mul, Complex.zero_re]]
        simp only [ite_self]
    _ =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            if ¬Nat.Coprime (p ^ k) (q / χ.conductor) then
              (characterReciprocalWeightedTerm x
                  χ.primitiveCharacter (p ^ k)).re
            else 0 :=
      by
      exact
        sum_primePow_eq_sum_primesLE
          (fun n ↦
            if ¬Nat.Coprime n (q / χ.conductor) then
              (characterReciprocalWeightedTerm x
                  χ.primitiveCharacter n).re
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
Input/assumptions: a level-`q` character with quadratic primitive part and a cutoff `x ≥ 2`, with
  `q / conductor ≠ 0`.
Conclusion: the reciprocal level-change correction is at least
  `-(1/2)(1 - 1/x) log(q / conductor)`.
Content: reindex to prime-outer form, bound each prime's inner sum via
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.`
  `quadraticReciprocalPrimePowerCorrection_neg_le_half_log` (feeding it
  `p ^ (Nat.log p ⌊x⌋₊) ≤ x` from `Nat.pow_log_le_self` and `Nat.floor_le`), then bound the
  resulting `Σ log p` by `Real.log (q / conductor)` via
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log`,
  using that the quotient-support filter set is a subset of `(q / conductor).primeFactors`.
Role: supplies the lower bound with quotient dependence `log(q / conductor)` consumed by
  `primitiveReciprocalConductorAbsorption_of_isQuadratic`.
-/
theorem primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient_of_isQuadratic {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (hqd : q / χ.conductor ≠ 0) :
    -(1 / 2 * (1 - 1 / x) * Real.log ((q / χ.conductor : ℕ) : ℝ)) ≤
      primitiveReciprocalLevelChangeCorrection x χ := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxfrac : 0 ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hxpos]; linarith
  rw [primitiveReciprocalLevelChangeCorrection_eq_sum_prime_divisors]
  set S := (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor with hSdef
  have hstep :
    ∀ p ∈ S,
      -(1 / 2 * (1 - 1 / x) * Real.log p) ≤
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterReciprocalWeightedTerm x
              χ.primitiveCharacter (p ^ k)).re := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hple : p ≤ ⌊x⌋₊ := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hK1 : 1 ≤ p.log ⌊x⌋₊ := Nat.log_pos hpprime.one_lt hple
    have hxfloor : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
    have hKnat : p ^ p.log ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hxfloor
    have hKnatR : (p : ℝ) ^ (p.log ⌊x⌋₊) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hKnat
    have hKle : (p : ℝ) ^ (p.log ⌊x⌋₊) ≤ x := hKnatR.trans (Nat.floor_le hxpos.le)
    exact
      quadraticReciprocalPrimePowerCorrection_neg_le_half_log
        x χ hχ hpprime hx hK1 hKle
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
      by nlinarith [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac, hbudget]
    _ = ∑ p ∈ S, -(1 / 2 * (1 - 1 / x) * Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤
        ∑ p ∈ S,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            (characterReciprocalWeightedTerm x
                χ.primitiveCharacter (p ^ k)).re :=
      Finset.sum_le_sum hstep

/--
Input/assumptions: `q ≠ 0`, a level-`q` character with quadratic primitive part, a cutoff
`x ≥ 2`, and `q / conductor ≠ 0`.
Conclusion: subtracting the reciprocal level-change correction from the conductor-scaled term
`(1/2)(1-1/x) log(conductor)` is at most the level-scaled term `(1/2)(1-1/x) log q`.
Content: apply the preceding lower bound on the correction,
then use `log(conductor) + log(q/conductor) = log q`
(from `conductor ∣ q` and `conductor ≠ 0`, via `Real.log_mul`).
Role: moves the exact reciprocal correction from a
free-standing quotient term into `(1-1/x) * log(conductor)/2`,
with no positive residual left over and without ever coarsening to
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primeFactorLogSum` or
`ω(q / conductor)`.
-/
theorem primitiveReciprocalConductorAbsorption_of_isQuadratic {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (hqd : q / χ.conductor ≠ 0) :
    1 / 2 * (1 - 1 / x) * Real.log (χ.conductor : ℝ) -
        primitiveReciprocalLevelChangeCorrection x χ ≤
      1 / 2 * (1 - 1 / x) * Real.log (q : ℝ) := by
  have hbound :=
    primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient_of_isQuadratic
      x χ hχ hx hqd
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
  linarith [hbound, hgoal_equiv]

/--
Input/assumptions: a level-`q` character (no quadratic hypothesis) and a cutoff `x ≥ 2`, with
  `q / conductor ≠ 0`.
Conclusion: the reciprocal level-change correction is at least
  `-(1/2)(1 - 1/x) log(q / conductor)`, matching
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.`
  `primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient_of_isQuadratic` without
  assuming `χ.primitiveCharacter.IsQuadratic`.
Content: reindex to prime-outer form; at each quotient-support prime `p`, split on whether `p`
  divides `χ.conductor`. If it does, `χ.primitiveCharacter p = 0` (a nonunit maps to `0`) so every
  summand vanishes; otherwise `p` is coprime to the conductor, so `‖χ.primitiveCharacter p‖ = 1`
  and the generic Fejér bound `PseudoPrime.AnalyticNumberTheory.Arithmetic.`
  `re_sum_reciprocalPrimePowerCorrection_neg_le_half_log` applies,
  with the tight bracket `x ≤ p ^ (K+1)` supplied by `Nat.lt_pow_succ_log_self`. Bound the resulting
  `Σ log p` by `log(q / conductor)` exactly as in the quadratic version.
Role: supplies the lower bound used by
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption`.
-/
theorem primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    -(1 / 2 * (1 - 1 / x) * Real.log ((q / χ.conductor : ℕ) : ℝ)) ≤
      primitiveReciprocalLevelChangeCorrection x χ := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxfrac : 0 ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hxpos]; linarith
  rw [primitiveReciprocalLevelChangeCorrection_eq_sum_prime_divisors]
  set S := (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ q / χ.conductor with hSdef
  have hstep :
    ∀ p ∈ S,
      -(1 / 2 * (1 - 1 / x) * Real.log p) ≤
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          (characterReciprocalWeightedTerm x
              χ.primitiveCharacter (p ^ k)).re := by
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
          (characterReciprocalWeightedTerm x
                χ.primitiveCharacter (p ^ k)).re =
            0 := by
        intro k hk
        have hk0 : k ≠ 0 := by
          have := (Finset.mem_Icc.mp hk).1; omega
        rw [characterReciprocalWeightedTerm_primitive_re_prime_pow
            x χ hpprime hk0,
          hz0, zero_pow hk0]
        simp only [Complex.zero_re, mul_zero]
      rw [Finset.sum_congr rfl heach, Finset.sum_const_zero]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac) hlogp]
    · have hunit : IsUnit ((p : ℕ) : ZMod χ.conductor) :=
        (ZMod.isUnit_prime_iff_not_dvd hpprime).mpr hdvd
      have hz : ‖χ.primitiveCharacter p‖ = 1 := by
        have hval := χ.primitiveCharacter.unit_norm_eq_one hunit.unit
        rwa [hunit.unit_spec] at hval
      have hxfloor : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
      have hKnat : p ^ p.log ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hxfloor
      have hKnatR : (p : ℝ) ^ (p.log ⌊x⌋₊) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hKnat
      have hKle : (p : ℝ) ^ (p.log ⌊x⌋₊) ≤ x := hKnatR.trans (Nat.floor_le hxpos.le)
      have hKup : x ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by
        have hlt : ⌊x⌋₊ < p ^ (p.log ⌊x⌋₊).succ := Nat.lt_pow_succ_log_self hpprime.one_lt ⌊x⌋₊
        have hltR : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have hcast : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by
          have : ⌊x⌋₊ + 1 ≤ p ^ (p.log ⌊x⌋₊ + 1) := hlt
          exact_mod_cast this
        linarith
      exact
        re_sum_reciprocalPrimePowerCorrection_neg_le_half_log
          x χ hpprime hz hx hK1 hKle hKup
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
      by nlinarith [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hxfrac, hbudget]
    _ = ∑ p ∈ S, -(1 / 2 * (1 - 1 / x) * Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤
        ∑ p ∈ S,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            (characterReciprocalWeightedTerm x
                χ.primitiveCharacter (p ^ k)).re :=
      Finset.sum_le_sum hstep

/--
Input/assumptions: `q ≠ 0`, a level-`q` character (no quadratic hypothesis), a cutoff `x ≥ 2`,
  and `q / conductor ≠ 0`.
Conclusion: subtracting the reciprocal level-change correction from the conductor-scaled term
  `(1/2)(1-1/x) log(conductor)` is at most the level-scaled term `(1/2)(1-1/x) log q`.
Content: same as `PseudoPrime.AnalyticNumberTheory.`
  `Arithmetic.primitiveReciprocalConductorAbsorption_of_isQuadratic`, but built on the
  generic bound `PseudoPrime.AnalyticNumberTheory.Arithmetic.`
  `primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient` instead
  of the quadratic-only one.
Role: replaces the conductor logarithm and reciprocal correction by a single level logarithm.
-/
theorem primitiveReciprocalConductorAbsorption {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x) (hqd : q / χ.conductor ≠ 0) :
    1 / 2 * (1 - 1 / x) * Real.log (χ.conductor : ℝ) -
        primitiveReciprocalLevelChangeCorrection x χ ≤
      1 / 2 * (1 - 1 / x) * Real.log (q : ℝ) := by
  have hbound :=
    primitiveReciprocalLevelChangeCorrection_ge_neg_half_log_quotient
      x χ hx hqd
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
  linarith [hbound, hgoal_equiv]

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
      (characterReciprocalWeightedSum x χ).re +
        primitiveReciprocalLevelChangeCorrection x χ := by
  rw [characterReciprocalWeightedSum,
    characterReciprocalWeightedSum,
    primitiveReciprocalLevelChangeCorrection]
  simp only [Complex.re_sum]
  let S := Finset.Ioc 0 ⌊x⌋₊
  let p : ℕ → Prop := fun n ↦ Nat.Coprime n (q / χ.conductor)
  have hprimitive :
    ∑ n ∈ S,
        (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re =
      (∑ n ∈ S.filter p,
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re) +
        ∑ n ∈ S.filter fun n ↦ ¬p n,
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re := by
    exact
      (Finset.sum_filter_add_sum_filter_not (s := S) (f := fun n ↦
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re)
          (p := p)).symm
  have hlevel :
    ∑ n ∈ S,
        (characterReciprocalWeightedTerm x χ n).re =
      ∑ n ∈ S.filter p,
        (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re := by
    have hin :
      ∑ n ∈ S.filter p,
          (characterReciprocalWeightedTerm x χ n).re =
        ∑ n ∈ S.filter p,
          (characterReciprocalWeightedTerm x χ.primitiveCharacter n).re := by
      apply Finset.sum_congr rfl
      intro n hn
      have hcop : Nat.Coprime n (q / χ.conductor) := Finset.mem_filter.mp hn |>.2
      rw [characterReciprocalWeightedTerm,
        characterReciprocalWeightedTerm,
        apply_eq_primitiveCharacter_of_coprime_quotient χ hcop]
    have houtside :
      ∑ n ∈ S.filter fun n ↦ ¬p n,
          (characterReciprocalWeightedTerm x χ n).re =
        0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hquotient : ¬Nat.Coprime n (q / χ.conductor) := Finset.mem_filter.mp hn |>.2
      rw [characterReciprocalWeightedTerm_eq_zero_of_not_coprime_quotient
          x χ hquotient]
      simp only [Complex.zero_re]
    calc
      ∑ n ∈ S,
            (characterReciprocalWeightedTerm x χ n).re =
          (∑ n ∈ S.filter p,
              (characterReciprocalWeightedTerm x χ n).re) +
            ∑ n ∈ S.filter fun n ↦ ¬p n,
              (characterReciprocalWeightedTerm x χ n).re :=
        (Finset.sum_filter_add_sum_filter_not (s := S) (f := fun n ↦
            (characterReciprocalWeightedTerm x χ n).re)
            (p := p)).symm
      _ =
          ∑ n ∈ S.filter p,
            (characterReciprocalWeightedTerm x χ n).re :=
        by rw [houtside, add_zero]
      _ = _ := hin
  rw [hprimitive]
  rw [hlevel]

/--
Input/assumptions: a positive cutoff and a level-`q` character with `q ≠ 0`.
Conclusion: the reciprocal level-change correction is at most the character-free reciprocal
  weighted sum on the complementary quotient.
Content: the exact level-change identity gives the correction as the real part of the (level −
  primitive) difference up to sign; bound that real part by the norm, already bounded by the
  common-factor sum.
Role: bounds the signed correction by a nonnegative common-factor sum, to which geometric
  prime-power bounds apply.
-/
theorem primitiveReciprocalLevelChangeCorrection_le {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) :
    primitiveReciprocalLevelChangeCorrection x χ ≤
      commonFactorReciprocalWeightedSum x
        (q / χ.conductor) := by
  have hexact :=
    characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection x χ
  have hnorm :=
    norm_characterReciprocalWeightedSum_sub_primitive_le x χ hx
  have hre :=
    Complex.re_le_norm
      (characterReciprocalWeightedSum x χ.primitiveCharacter -
        characterReciprocalWeightedSum x χ)
  rw [Complex.sub_re, norm_sub_rev] at hre
  linarith

end PseudoPrime.AnalyticNumberTheory.Arithmetic
