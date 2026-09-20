/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalLevelChange
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
import PseudoPrime.AnalyticNumberTheory.Arithmetic.FejerConvexSums
import PseudoPrime.LLS.Lemma22
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ConductorPrimeSupport
import PseudoPrime.Analysis.RealLog

/-!
# Reciprocal weighted sums and the LLS Lemma 2.3 interface

This file uses the foundation's reciprocal character sum and separates three responsibilities: the
primitive reciprocal lower bound, Lemma 2.3's raw zero-mass estimate, and its elementary numerical
simplification.  In particular, no equality between the original and primitive characters at the
extra level primes is assumed silently.
-/

namespace PseudoPrime.LLS

/-- The Riemann reciprocal lower estimate used from LLS Lemma 2.4. -/
def LLSRiemannReciprocalLowerBound : Prop :=
  ∀ x : ℝ,
    2 ≤ x → Real.log x - 8 / 5 ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x

/-- The Part 1 consequence of Lemma 2.4 and the finite reciprocal character comparison. -/
def LLSPart1PrimitiveReciprocalLowerAt {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  llsAuxiliaryTerm q ≤
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
        ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re

/--
The conductor-safe reciprocal lower input before the finite Euler-factor correction is absorbed.

For an arbitrary level-`q` character, passage to `primitiveCharacter` costs the reciprocal
prime-factor term of `q / conductor`. Unlike `LLSPart1PrimitiveReciprocalLowerAt`, this form
makes that cost explicit and therefore needs no prime-support hypothesis.
-/
def LLSPart1PrimitiveReciprocalLowerAtWithQuotient {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  2 * Real.log (Real.log q) - 8 / 5 - AnalyticNumberTheory.Arithmetic.primeFactorLogSum q -
      AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) ≤
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
        ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re

/--
Input/assumptions: a Part 1 character.
Conclusion: its reciprocal lower input retains both the level common-factor sum and the exact
complementary-conductor prime-power correction.
Content: the quotient common-factor sum is kept as its exact finite prime-power expansion
at the prescribed cutoff; this is a loss bound, not the signed level-change identity.
Role: supplies the conductor algebra before either reciprocal or logarithmic quotient data is
majorized separately.
-/
noncomputable def LLSPart1PrimitiveReciprocalLowerAtWithExactQuotient {q : ℕ}
    (χ : DirichletCharacter ℂ q) : Prop :=
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  2 * Real.log (Real.log q) - 8 / 5 -
      AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x q -
      AnalyticNumberTheory.Arithmetic.primitiveReciprocalQuotientPrimePowerCorrection x χ ≤
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ.primitiveCharacter).re

/-- Under the Part 1 no-small-prime hypothesis and within its positive cutoff, a reciprocal
summand equals the Riemann summand on coprime inputs and vanishes on the remaining inputs. -/
theorem characterReciprocalWeightedTerm_re_eq_ite {q n : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊)
    (hsmall : llsTheorem11S1NoSmallPrime χ) (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm x χ n).re =
      if Nat.Coprime n q then AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm x n
      else 0 := by
  by_cases hcop : Nat.Coprime n q
  · rw [ite_eq_left hcop]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm,
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm, hΛ, zero_div, zero_mul]
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
      have hpvalue : χ p = 1 := hsmall p hp (hp.coprime_iff_not_dvd.mp hpcop) (hpbound.trans hlimit)
      rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm]
      simp only [Nat.cast_pow, map_pow, hpvalue, one_pow, mul_one, Complex.ofReal_re]
  · rw [ite_eq_right hcop]
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
    rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm, hχzero, mul_zero,
      Complex.zero_re]

/-- Under the Part 1 no-small-prime hypothesis and within its positive cutoff, the reciprocal
character sum has real part equal to the coprime part of the Riemann sum. -/
theorem characterReciprocalWeightedSum_re_eq_coprime {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.Coprime n q,
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm x n := by
  rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum]
  simp only [Complex.re_sum]
  trans
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      if Nat.Coprime n q then AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm x n
      else 0
  · apply Finset.sum_congr rfl
    intro n hn
    exact characterReciprocalWeightedTerm_re_eq_ite x χ hx hn hsmall hlimit
  · rw [← Finset.sum_filter]

/--
The safe finite reciprocal lower bound, retaining the correction from primes in the level divided
by the conductor.  This avoids identifying the original and primitive characters at those primes.
-/
theorem llsPrimitiveReciprocalWeightedSum_re_lower_safe {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x -
        AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x q -
        AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x (q / χ.conductor) ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          χ.primitiveCharacter).re := by
  have horiginal := characterReciprocalWeightedSum_re_eq_coprime x χ hx hsmall hlimit
  have hsplit :=
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum_eq_coprime_add_common x q
  have hnorm :=
    AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_sub_primitive_le x χ hx
  have hre :=
    Complex.re_le_norm
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
        AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ.primitiveCharacter)
  rw [Complex.sub_re, horiginal] at hre
  linarith

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/--
Input/assumptions: a positive cutoff, a no-small-prime level character, and the Part 1 cutoff
comparison.
Conclusion: the primitive reciprocal sum has a lower bound retaining the quotient as its exact
finite prime-power correction.
Content: rewrite the safe reciprocal comparison by the prime-power correction identity.
Role: avoids prematurely replacing the quotient correction by
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primeFactorLogSum`.
-/
theorem llsPrimitiveReciprocalWeightedSum_re_lower_exactQuotientPrimePowers {q : ℕ} [NeZero q]
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    reciprocalWeightedMangoldtSum x - commonFactorReciprocalWeightedSum x q -
        primitiveReciprocalQuotientPrimePowerCorrection x χ ≤
      (characterReciprocalWeightedSum x χ.primitiveCharacter).re := by
  rw [primitiveReciprocalQuotientPrimePowerCorrection_eq_commonFactor x χ hx.le]
  exact llsPrimitiveReciprocalWeightedSum_re_lower_safe x χ hx hsmall hlimit

/--
The safe finite lower bound after applying Lemma 3.1's reciprocal estimate to both corrections.

The second prime-factor sum is the explicit cost of passing from the original character at level
`q` to its primitive character.  It cannot be dropped for an arbitrary imprimitive character.
-/
theorem llsPrimitiveReciprocalWeightedSum_re_lower_primeFactorSums {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum q -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          χ.primitiveCharacter).re := by
  have hsafe := llsPrimitiveReciprocalWeightedSum_re_lower_safe x χ hx hsmall hlimit
  have hlevel :=
    AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le (NeZero.ne q) hx
  have hquotientPos : 0 < q / χ.conductor :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) χ.conductor_ne_zero.bot_lt
  have hquotient :=
    AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le hquotientPos.ne' hx
  linarith

/--
LLS Lemma 2.4 and the safe primitive-character comparison give a reciprocal lower bound with
the complementary conductor quotient retained explicitly.

For `q ≥ 3000` and a character satisfying `llsTheorem11S1NoSmallPrime`, this gives the input
for numerical absorption of the quotient correction. Nontriviality is not required here.
-/
theorem llsPart1PrimitiveReciprocalLowerAtWithQuotient_of_riemann
    (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hsmall : llsTheorem11S1NoSmallPrime χ) :
    LLSPart1PrimitiveReciprocalLowerAtWithQuotient χ := by
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  have hy : 0 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hx : 0 < x := sq_pos_of_pos hy
  have hxTwo : (2 : ℝ) ≤ x := by
    dsimp only [x]
    nlinarith [eight_lt_llsTheorem11S1RadiusRoot hq]
  have hlower := llsPrimitiveReciprocalWeightedSum_re_lower_primeFactorSums x χ hx hsmall le_rfl
  have hriemann := h24 x hxTwo
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hroot : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hlogRoot : Real.log (Real.log q) ≤ Real.log (llsTheorem11S1RadiusRoot q) :=
    Real.log_le_log hlogq hroot
  have hlogX : 2 * Real.log (Real.log q) ≤ Real.log x := by
    rw [show Real.log x = 2 * Real.log (llsTheorem11S1RadiusRoot q) by
        exact Analysis.log_sq_eq_two_mul_log hy]
    linarith
  rw [LLSPart1PrimitiveReciprocalLowerAtWithQuotient]
  linarith

/--
Input/assumptions: a positive cutoff within the Part 1 range and a no-small-prime character.
Conclusion: the level character's own reciprocal sum is at least the Riemann reciprocal sum
minus the level's prime-factor log-sum.
Content: identify the level-character sum with the coprime Riemann support (exact equality via
`characterReciprocalWeightedSum_re_eq_coprime`), then bound the discarded common-factor part
by `PseudoPrime.AnalyticNumberTheory.Arithmetic.primeFactorLogSum q`
(`PseudoPrime.AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le`).
Role: supplies the level-character reciprocal lower input: unlike the primitive
version, no `PseudoPrime.AnalyticNumberTheory.Arithmetic.ConductorPrimeSupport` hypothesis is
needed since no comparison to
`χ.primitiveCharacter` is made at all.
-/
theorem characterReciprocalWeightedSum_re_lower_level {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum q ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re := by
  have horiginal := characterReciprocalWeightedSum_re_eq_coprime x χ hx hsmall hlimit
  have hsplit :=
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum_eq_coprime_add_common x q
  have hcommon :=
    AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le (NeZero.ne q) hx
  linarith [horiginal, hsplit, hcommon]

/-- Under the no-small-prime hypothesis and within the Part 1 cutoff, the reciprocal sum has
nonnegative real part. -/
theorem characterReciprocalWeightedSum_re_nonneg_level {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    0 ≤ (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re := by
  rw [characterReciprocalWeightedSum_re_eq_coprime x χ hx hsmall hlimit]
  apply Finset.sum_nonneg
  intro n hn
  have hnIoc := (Finset.mem_filter.mp hn).1
  exact
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_nonneg hx
      (Finset.mem_Ioc.mp hnIoc).1 (Finset.mem_Ioc.mp hnIoc).2

/--
Input/assumptions: a level-`q` character.
Conclusion: the level character's reciprocal weighted sum satisfies the same `A(q)` lower bound
that LLS Lemma 2.3 needs from the primitive character, but stated directly for `χ` (not
`χ.primitiveCharacter`), so no conductor-prime-support hypothesis is needed.
Role: supplies the level-character lower bound for the exact level-change adapter below.
The separate `LLSPart1PrimitiveRawCoreBounds` interface still retains a primitive lower input.
-/
def LLSPart1LevelReciprocalLowerAt {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  llsAuxiliaryTerm q ≤
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
        ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re

/--
Input/assumptions: LLS Lemma 2.4's Riemann reciprocal lower bound and a Part 1 no-small-prime
level character.
Conclusion: `LLSPart1LevelReciprocalLowerAt χ` holds.
Content: mirrors `llsPart1PrimitiveReciprocalLowerAt_of_riemann_of_conductorPrimeSupport`'s proof,
but works with `χ` throughout instead of rewriting to `χ.primitiveCharacter`, so the
`PseudoPrime.AnalyticNumberTheory.Arithmetic.ConductorPrimeSupport` hypothesis and its rewrite
lemma are not needed.
Role: supplies the level-character entry point, valid without any
imprimitivity restriction.
-/
theorem llsPart1LevelReciprocalLowerAt_of_riemann (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q)
    (hsmall : llsTheorem11S1NoSmallPrime χ) : LLSPart1LevelReciprocalLowerAt χ := by
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  have hy : 0 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hx : 0 < x := sq_pos_of_pos hy
  have hxTwo : (2 : ℝ) ≤ x := by
    dsimp only [x]
    nlinarith [eight_lt_llsTheorem11S1RadiusRoot hq]
  have hlower := characterReciprocalWeightedSum_re_lower_level x χ hx hsmall le_rfl
  have hriemann := h24 x hxTwo
  have hsumNonneg := characterReciprocalWeightedSum_re_nonneg_level x χ hx hsmall le_rfl
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hroot : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hlogRoot : Real.log (Real.log q) ≤ Real.log (llsTheorem11S1RadiusRoot q) :=
    Real.log_le_log hlogq hroot
  have hlogX : 2 * Real.log (Real.log q) ≤ Real.log x := by
    rw [show Real.log x = 2 * Real.log (llsTheorem11S1RadiusRoot q) by
        exact Analysis.log_sq_eq_two_mul_log hy]
    linarith
  rw [LLSPart1LevelReciprocalLowerAt, llsAuxiliaryTerm]
  apply max_le hsumNonneg
  linarith

/--
Input/assumptions: a level-`q` character.
Conclusion: `A(q)` plus the exact reciprocal level-change correction is at most the primitive
reciprocal sum's real part.
Content: immediate from `llsPart1LevelReciprocalLowerAt_of_riemann` and the exact identity
`Arithmetic.characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection`.
Role: states the lower input with the signed level-change term available for conductor absorption.
-/
def LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  llsAuxiliaryTerm q +
      AnalyticNumberTheory.Arithmetic.primitiveReciprocalLevelChangeCorrection x χ ≤
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ.primitiveCharacter).re

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/--
Input/assumptions: LLS Lemma 2.4's Riemann reciprocal lower bound and a Part 1 no-small-prime
level character.
Conclusion: `LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt χ` holds.
Content: combine `llsPart1LevelReciprocalLowerAt_of_riemann` with the exact level-change identity.
Role: supplies the analytic input for
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption_of_isQuadratic`.
-/
theorem llsPart1PrimitiveReciprocalLowerWithLevelChangeAt_of_riemann
    (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hsmall : llsTheorem11S1NoSmallPrime χ) :
    LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt χ := by
  have hlevel := llsPart1LevelReciprocalLowerAt_of_riemann h24 χ hq hsmall
  have hidentity :=
    characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ
  rw [LLSPart1LevelReciprocalLowerAt] at hlevel
  rw [LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt]
  linarith [hlevel, hidentity]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Under equal prime support, the finite reciprocal lower bound has only the level correction. -/
theorem llsPrimitiveReciprocalWeightedSum_re_lower_of_conductorPrimeSupport {q : ℕ} [NeZero q]
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) (hsupport : ConductorPrimeSupport χ) :
    reciprocalWeightedMangoldtSum x - primeFactorLogSum q ≤
      (characterReciprocalWeightedSum x χ.primitiveCharacter).re := by
  have horiginal := characterReciprocalWeightedSum_re_eq_coprime x χ hx hsmall hlimit
  have hsplit := reciprocalWeightedMangoldtSum_eq_coprime_add_common x q
  have hcommon := commonFactorReciprocalWeightedSum_le (NeZero.ne q) hx
  rw [← characterReciprocalWeightedSum_eq_primitive_of_conductorPrimeSupport x χ hsupport]
  linarith

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/--
LLS Lemma 2.4 and equal prime support give the reciprocal lower input used by Lemma 2.3.
-/
theorem llsPart1PrimitiveReciprocalLowerAt_of_riemann_of_conductorPrimeSupport
    (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hsmall : llsTheorem11S1NoSmallPrime χ) (hsupport : ConductorPrimeSupport χ) :
    LLSPart1PrimitiveReciprocalLowerAt χ := by
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  have hy : 0 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hx : 0 < x := sq_pos_of_pos hy
  have hxTwo : (2 : ℝ) ≤ x := by
    dsimp only [x]
    nlinarith [eight_lt_llsTheorem11S1RadiusRoot hq]
  have hlower :=
    llsPrimitiveReciprocalWeightedSum_re_lower_of_conductorPrimeSupport x χ hx hsmall le_rfl
      hsupport
  have hriemann := h24 x hxTwo
  have hsumNonneg : 0 ≤ (characterReciprocalWeightedSum x χ.primitiveCharacter).re := by
    rw [← characterReciprocalWeightedSum_eq_primitive_of_conductorPrimeSupport x χ hsupport,
      characterReciprocalWeightedSum_re_eq_coprime x χ hx hsmall le_rfl]
    apply Finset.sum_nonneg
    intro n hn
    have hnIoc := (Finset.mem_filter.mp hn).1
    exact
      reciprocalWeightedMangoldtTerm_nonneg hx (Finset.mem_Ioc.mp hnIoc).1
        (Finset.mem_Ioc.mp hnIoc).2
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hroot : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hlogRoot : Real.log (Real.log q) ≤ Real.log (llsTheorem11S1RadiusRoot q) :=
    Real.log_le_log hlogq hroot
  have hlogX : 2 * Real.log (Real.log q) ≤ Real.log x := by
    rw [show Real.log x = 2 * Real.log (llsTheorem11S1RadiusRoot q) by
        exact Analysis.log_sq_eq_two_mul_log hy]
    linarith
  rw [LLSPart1PrimitiveReciprocalLowerAt, llsAuxiliaryTerm]
  apply max_le hsumNonneg
  linarith

/-- Lemma 2.3's raw upper-bound shape at the Part 1 radius for a real candidate `b` representing
`|Re B(χ̃)|`; the proposition itself imposes no equality with the zero mass. -/
def LLSPart1PrimitiveZeroMassRawUpperAt {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) : Prop :=
  let y := llsTheorem11S1RadiusRoot q
  b ≤ (1 - 1 / y)⁻¹ ^ 2 * (Real.log ((χ.conductor : ℝ) / Real.pi) / 2) - llsAuxiliaryTerm q - 1 / 4

/--
Definition: the reciprocal quotient loss used in the Lemma 2.3 zero-mass estimate.
Input: a level-`q` character.
Output: `(1 - 1 / y)⁻² P(q / conductor)`, where `y` is the Part 1 radius root.
Role: records the conductor-quotient correction before its joint absorption with the `(3.2)` term.
-/
noncomputable def llsPart1PrimitiveReciprocalQuotientCorrection {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ℝ :=
  (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 *
    AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)

/--
Definition: Lemma 2.3's raw zero-mass upper bound with the reciprocal quotient correction.
Input: a character and a real zero-mass witness candidate; nonnegativity is imposed by the core.
Output: the exact raw bound with `llsPart1PrimitiveReciprocalQuotientCorrection` retained.
Role: supplies the corrected raw inequality to
`llsPart1PrimitiveZeroMassSimplificationWithQuotient`.
-/
def LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) :
    Prop :=
  let y := llsTheorem11S1RadiusRoot q
  b ≤
    (1 - 1 / y)⁻¹ ^ 2 * (Real.log ((χ.conductor : ℝ) / Real.pi) / 2) - llsAuxiliaryTerm q - 1 / 4 +
      llsPart1PrimitiveReciprocalQuotientCorrection χ

/-- The reciprocal quotient correction is nonnegative. -/
theorem llsPart1PrimitiveReciprocalQuotientCorrection_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) :
    0 ≤ llsPart1PrimitiveReciprocalQuotientCorrection χ := by
  unfold llsPart1PrimitiveReciprocalQuotientCorrection
    AnalyticNumberTheory.Arithmetic.primeFactorLogSum
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  exact
    div_nonneg (Real.log_nonneg (by exact_mod_cast hpprime.one_le))
      (sub_nonneg.mpr (by exact_mod_cast hpprime.one_le))

/--
Definition: the Section 3.1 zero-mass upper interface with its quotient correction retained.
Input: a character and zero-mass witness.
Output: the existing public zero-mass bound plus the exact reciprocal correction.
Role: supplies the finite real inequality to combine with the logarithmic `(3.2)` correction.
-/
def LLSPart1PrimitiveZeroMassUpperWithQuotientAt {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) :
    Prop :=
  b ≤
    Real.log χ.conductor / 2 + 2 / 5 - llsAuxiliaryTerm q +
      llsPart1PrimitiveReciprocalQuotientCorrection χ

/--
Definition: the analytic shared-witness core with reciprocal quotient data retained.
Input: every nontrivial Part 1 character satisfying the no-small-prime hypothesis.
Output: one witness serving the logarithmic bound, safe reciprocal lower bound, and corrected
zero-mass raw bound.
Role: isolates the analytic deliverable before the combined estimate absorbs the common quotient
terms.
-/
def LLSPart1PrimitiveRawCoreBoundsWithQuotient : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      ∃ b : ℝ,
        0 ≤ b ∧
          LLSPart1PrimitiveWeightedUpperAt χ b ∧
          LLSPart1PrimitiveReciprocalLowerAtWithQuotient χ ∧
          LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt χ b

/-- The analytic shared witness before the final elementary zero-mass simplification. -/
def LLSPart1PrimitiveRawCoreBounds : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      ∃ b : ℝ,
        0 ≤ b ∧
          LLSPart1PrimitiveWeightedUpperAt χ b ∧
          LLSPart1PrimitiveReciprocalLowerAt χ ∧ LLSPart1PrimitiveZeroMassRawUpperAt χ b

/-- The elementary implication from Lemma 2.3's raw estimate to the bound used in Section 3.1. -/
def LLSPart1PrimitiveZeroMassSimplification : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ),
    3000 ≤ q →
      0 ≤ b → LLSPart1PrimitiveZeroMassRawUpperAt χ b → LLSPart1PrimitiveZeroMassUpperAt χ b

/-- The raw Lemma 2.3 estimate implies the zero-mass bound used in Section 3.1. -/
theorem llsPart1PrimitiveZeroMassSimplification : LLSPart1PrimitiveZeroMassSimplification := by
  intro q _ χ b hq _ hraw
  have hy : (8 : ℝ) ≤ llsTheorem11S1RadiusRoot q := (eight_lt_llsTheorem11S1RadiusRoot hq).le
  have hconductor := AnalyticNumberTheory.DirichletLFunction.log_conductor_le_log_level χ
  have hlevel : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hlogPi : (1 : ℝ) ≤ Real.log Real.pi := by
    have hlogThreePi : Real.log 3 < Real.log Real.pi :=
      Real.strictMonoOn_log (by norm_num only [Set.mem_Ioi]) Real.pi_pos Real.pi_gt_three
    linarith [Real.log_three_gt_d9]
  have hlogConductor : 0 ≤ Real.log χ.conductor :=
    Real.log_nonneg (by exact_mod_cast AnalyticNumberTheory.DirichletLFunction.conductor_pos χ)
  have hproduct :
    (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * (Real.log ((χ.conductor : ℝ) / Real.pi) / 2) ≤
      Real.log χ.conductor / 2 + 13 / 20 := by
    rw [Real.log_div
        (by exact_mod_cast (AnalyticNumberTheory.DirichletLFunction.conductor_pos χ).ne')
        Real.pi_ne_zero]
    by_cases hdiff : 0 ≤ Real.log χ.conductor - Real.log Real.pi
    · exact
        AnalyticNumberTheory.Arithmetic.inverseSquareLogTradeoff hy (hconductor.trans hlevel) hlogPi
          hdiff
    · have hinverse : 0 ≤ (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 := sq_nonneg _
      nlinarith
  rw [LLSPart1PrimitiveZeroMassRawUpperAt] at hraw
  rw [LLSPart1PrimitiveZeroMassUpperAt]
  nlinarith

/--
Input/assumptions: the quotient-corrected raw Lemma 2.3 estimate, `q ≥ 3000`, and `0 ≤ b`.
Conclusion: its Section 3.1 form retains exactly the reciprocal quotient correction.
Content: apply the existing inverse-square logarithmic tradeoff without altering the added term.
Role: preserves the same additive correction in the simplified zero-mass upper bound.
-/
theorem llsPart1PrimitiveZeroMassSimplificationWithQuotient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (b : ℝ) (hq : 3000 ≤ q) (_hb : 0 ≤ b)
    (hraw : LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt χ b) :
    LLSPart1PrimitiveZeroMassUpperWithQuotientAt χ b := by
  have hy : (8 : ℝ) ≤ llsTheorem11S1RadiusRoot q := (eight_lt_llsTheorem11S1RadiusRoot hq).le
  have hconductor := AnalyticNumberTheory.DirichletLFunction.log_conductor_le_log_level χ
  have hlevel : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hlogPi : (1 : ℝ) ≤ Real.log Real.pi := by
    have hlogThreePi : Real.log 3 < Real.log Real.pi :=
      Real.strictMonoOn_log (by norm_num only [Set.mem_Ioi]) Real.pi_pos Real.pi_gt_three
    linarith [Real.log_three_gt_d9]
  have hlogConductor : 0 ≤ Real.log χ.conductor :=
    Real.log_nonneg (by exact_mod_cast AnalyticNumberTheory.DirichletLFunction.conductor_pos χ)
  have hproduct :
    (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * (Real.log ((χ.conductor : ℝ) / Real.pi) / 2) ≤
      Real.log χ.conductor / 2 + 13 / 20 := by
    rw [Real.log_div
        (by exact_mod_cast (AnalyticNumberTheory.DirichletLFunction.conductor_pos χ).ne')
        Real.pi_ne_zero]
    by_cases hdiff : 0 ≤ Real.log χ.conductor - Real.log Real.pi
    · exact
        AnalyticNumberTheory.Arithmetic.inverseSquareLogTradeoff hy (hconductor.trans hlevel) hlogPi
          hdiff
    · have hinverse : 0 ≤ (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 := sq_nonneg _
      nlinarith
  rw [LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt] at hraw
  rw [LLSPart1PrimitiveZeroMassUpperWithQuotientAt]
  nlinarith

/--
Definition: the simplified shared-witness core with the reciprocal quotient correction retained.
Input: every nontrivial Part 1 character under the no-small-prime hypothesis.
Output: the logarithmic upper and corrected zero-mass upper for one shared witness.
Role: supplies the shared witness to `characterLogWeightedSum_re_le_comparisonUpperWithQuotient`.
-/
def LLSPart1PrimitiveCoreBoundsWithQuotient : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      ∃ b : ℝ,
        0 ≤ b ∧
          LLSPart1PrimitiveWeightedUpperAt χ b ∧ LLSPart1PrimitiveZeroMassUpperWithQuotientAt χ b

/--
Definition: the full Section 3.1 comparison upper bound with both quotient corrections retained.
Input: a level-`q` character.
Output: the `(3.2)` comparison upper plus the propagated reciprocal correction.
Role: records both losses before conductor absorption.
-/
noncomputable def llsTheorem11S1ComparisonUpperBoundWithQuotient {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ℝ :=
  llsTheorem11S1ComparisonUpperBound χ +
    (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
      llsPart1PrimitiveReciprocalQuotientCorrection χ

/--
Input/assumptions: the corrected primitive shared-witness core at one Part 1 character.
Conclusion: the primitive logarithmic sum obeys the primitive upper bound plus the propagated
reciprocal correction; the logarithmic comparison error is added only in the next theorem.
Content: substitute the corrected zero-mass witness into Lemma 2.2's weighted inequality.
Role: supplies the primitive input to the original-character comparison below.
-/
theorem llsPrimitiveLogWeightedSum_re_le_comparisonUpperWithQuotient {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {b : ℝ} (hq : 3000 ≤ q)
    (hweighted : LLSPart1PrimitiveWeightedUpperAt χ b)
    (hzero : LLSPart1PrimitiveZeroMassUpperWithQuotientAt χ b) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ.primitiveCharacter).re ≤
      llsTheorem11S1PrimitiveUpperBound χ +
        (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
          llsPart1PrimitiveReciprocalQuotientCorrection χ := by
  rw [LLSPart1PrimitiveWeightedUpperAt] at hweighted
  rw [LLSPart1PrimitiveZeroMassUpperWithQuotientAt] at hzero
  rw [llsTheorem11S1PrimitiveUpperBound]
  have hcoefficient :
    0 ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    have hroot : 1 ≤ llsTheorem11S1RadiusRoot q := by
      linarith [eight_lt_llsTheorem11S1RadiusRoot hq]
    have hlog : 0 ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
      apply Real.log_nonneg
      nlinarith
    linarith
  have hmul := mul_le_mul_of_nonneg_left hzero hcoefficient
  have hcomparison :
    0 ≤
      (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card *
        (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 := by
    positivity
  linarith

/--
Input/assumptions: the corrected primitive shared-witness core for one Part 1 character.
Conclusion: the original logarithmic weighted sum is bounded by the combined corrected comparison
upper bound.
Content: add the existing `(3.2)` primitive-comparison error to the corrected primitive bound.
Role: connects the corrected shared-witness core to the original-character finite sum.
-/
theorem characterLogWeightedSum_re_le_comparisonUpperWithQuotient
    (hcore : LLSPart1PrimitiveCoreBoundsWithQuotient) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hχ : χ ≠ 1)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ).re ≤
      llsTheorem11S1ComparisonUpperBoundWithQuotient χ := by
  obtain ⟨b, _, hweighted, hzero⟩ := hcore q χ hq hχ hsmall
  have hprimitive := llsPrimitiveLogWeightedSum_re_le_comparisonUpperWithQuotient hq hweighted hzero
  have hy : 0 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hcomparison :=
    AnalyticNumberTheory.Arithmetic.norm_characterLogWeightedSum_sub_primitive_le
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ (sq_pos_of_pos hy)
  have hre :=
    Complex.re_le_norm
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ -
        AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ.primitiveCharacter)
  rw [llsTheorem11S1ComparisonUpperBoundWithQuotient, llsTheorem11S1ComparisonUpperBound] at ⊢
  calc
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
            χ).re =
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
                χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re +
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
              ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re :=
      by
      rw [Complex.sub_re]
      ring
    _ ≤
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
                χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter‖ +
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
              ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re :=
      add_le_add hre le_rfl
    _ ≤
        (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card *
            (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 +
          (llsTheorem11S1PrimitiveUpperBound χ +
            (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
              llsPart1PrimitiveReciprocalQuotientCorrection χ) :=
      add_le_add hcomparison hprimitive
    _ =
        llsTheorem11S1ComparisonUpperBound χ +
          (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
            llsPart1PrimitiveReciprocalQuotientCorrection χ :=
      by
      unfold llsTheorem11S1ComparisonUpperBound
      ring

/-!
### Abstract reciprocal correction transport

The `WithQuotient` theorems above fix the reciprocal correction to the coarse
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)`.  The theorems
below keep the same `(1 - 1/y)⁻²`
transport coefficient
but leave the reciprocal correction itself as an abstract real parameter `δrec`, so that the
exact quadratic `(k, p)` ledger
(`Arithmetic.primitiveReciprocalLevelChangeCorrection_eq_sum_of_isQuadratic`)
can be substituted for it
once the analytic estimate supplies a concrete lower bound for the primitive reciprocal sum,
without redoing this
algebra.  On the logarithmic side, the exact identity
`Arithmetic.characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection`
is used directly in place
of the coarse `(3.2)` norm bound, so the logarithmic correction never needs to be abstracted or
coarsened at all: it enters the final bound as an exact subtracted term.
-/

/--
Input/assumptions: a level-`q` character, an abstract reciprocal correction `δrec`, and a
zero-mass witness candidate `b`.
Conclusion: Lemma 2.3's raw upper bound for `b`, with `δrec` in place of the coarse
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)`.
Content: the same expression as `LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt`, with the
quotient correction factored out as a free parameter instead of fixed to its coarse source.
Role: the prime-local estimate interface can be discharged by an analytic proof with any exact or
coarse reciprocal correction, without committing in advance to which one.
-/
def LLSPart1PrimitiveZeroMassRawUpperWithCorrectionAt {q : ℕ} (χ : DirichletCharacter ℂ q)
    (δrec b : ℝ) : Prop :=
  let y := llsTheorem11S1RadiusRoot q
  b ≤
    (1 - 1 / y)⁻¹ ^ 2 * (Real.log ((χ.conductor : ℝ) / Real.pi) / 2 + δrec) - llsAuxiliaryTerm q -
      1 / 4

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/--
Input/assumptions: a level-`q` character, an abstract reciprocal correction `δrec`, and a
zero-mass witness `b` satisfying Lemma 2.2's weighted upper bound and the zero-mass upper bound
at `δrec`.
Conclusion: the *original* character's logarithmic weighted sum (not the primitive one) is
bounded using `δrec` through Lemma 2.2's coefficient `A(X) = 2y + 2 + log X`, and the *exact*
logarithmic level-change correction, subtracted with no coarsening at all.
Content: chain Lemma 2.2's inequality for `χ̃` through the exact primitive/level logarithmic
identity, instead of the coarse `(3.2)` norm bound used by
`characterLogWeightedSum_re_le_comparisonUpperWithQuotient`.
Role: transports a concrete reciprocal correction to an upper bound for the original weighted
sum, retaining the signed logarithmic level-change correction exactly.
-/
theorem characterLogWeightedSum_re_le_upperBound_of_corrections {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δrec b : ℝ) (hq : 3000 ≤ q)
    (hweighted : LLSPart1PrimitiveWeightedUpperAt χ b)
    (hzero :
      b ≤
        Real.log χ.conductor / 2 + 2 / 5 - llsAuxiliaryTerm q +
          (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * δrec) :
    (characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re ≤
      llsTheorem11S1PrimitiveUpperBound χ +
          (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
            ((1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * δrec) -
        primitiveLogLevelChangeCorrection ((llsTheorem11S1RadiusRoot q) ^ 2) χ := by
  have hexact :=
    characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ
  rw [LLSPart1PrimitiveWeightedUpperAt] at hweighted
  rw [llsTheorem11S1PrimitiveUpperBound]
  have hcoefficient :
    0 ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    have hroot : 1 ≤ llsTheorem11S1RadiusRoot q := by
      linarith [eight_lt_llsTheorem11S1RadiusRoot hq]
    have hlog : 0 ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
      apply Real.log_nonneg
      nlinarith
    linarith
  have hmul := mul_le_mul_of_nonneg_left hzero hcoefficient
  nlinarith [hexact, hweighted, hmul]

/-- Raw analytic core bounds and their numerical simplification give the shared-witness core. -/
theorem llsPart1PrimitiveCoreBounds_of_raw (hraw : LLSPart1PrimitiveRawCoreBounds)
    (hsimplify : LLSPart1PrimitiveZeroMassSimplification) : LLSPart1PrimitiveCoreBounds := by
  intro q _ χ hq hχ hsmall
  obtain ⟨b, hb, hweighted, _, hzero⟩ := hraw q χ hq hχ hsmall
  exact ⟨b, hb, hweighted, hsimplify q χ b hq hb hzero⟩

/-- The raw primitive analytic core implies the final shared-witness core. -/
theorem llsPart1PrimitiveCoreBounds_of_raw_analytic (hraw : LLSPart1PrimitiveRawCoreBounds) :
    LLSPart1PrimitiveCoreBounds :=
  llsPart1PrimitiveCoreBounds_of_raw hraw llsPart1PrimitiveZeroMassSimplification

/-- The Riemann lower bound and raw primitive analytic core imply LLS Part 1. -/
theorem llsTheorem11S1Character_of_riemann_and_primitive_raw (h21 : LLSRiemannWeightedLowerBound)
    (hraw : LLSPart1PrimitiveRawCoreBounds) : llsTheorem11S1Character :=
  llsTheorem11S1Character_of_riemann_and_primitive_core h21
    (llsPart1PrimitiveCoreBounds_of_raw_analytic hraw)

end PseudoPrime.LLS
