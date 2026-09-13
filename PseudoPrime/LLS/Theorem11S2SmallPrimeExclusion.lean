/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NoSmallPrimeFactor
import PseudoPrime.LLS.WeightedComparison

/-!
# Vanishing weighted defects for Theorem 1.1 S2

This file supplies the logarithmic and reciprocal defect bounds for
`LLSWeightedComparisonCore`: under the counterexample hypothesis that a level-`q` character `χ` is
trivial on every prime residue below the cutoff `X` (`LLSCharacterTrivialBelow`), both weighted
defects vanish exactly, giving `dS = dR = 0`.

The counterexample hypothesis alone forces `q`'s prime factors below `X` to be absent
(`noSmallPrimeFactor_of_characterTrivialBelow`): a Dirichlet character vanishes at any input not
coprime to its modulus, so `χ p = 1 ≠ 0` already rules out `p ∣ q`. At the endpoint `n = X`,
both weights vanish. Thus the strict prime cutoff suffices for the closed finite sums.
-/

namespace PseudoPrime.LLS

/-- The counterexample hypothesis for Theorem 1.1 S2: `χ` is trivial on every prime residue
strictly below the cutoff `X`. -/
def LLSCharacterTrivialBelow {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℝ) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) < X → χ ℓ = 1

/--
Input/assumptions: a level-`q` character trivial on every prime residue below `X`.
Conclusion: `q` has no prime factor strictly below `X`.
Content: a Dirichlet character vanishes at any input sharing a factor with its modulus, so
`χ p = 1 ≠ 0` already forces `p` coprime to `q`.
Role: recovers `NoSmallPrimeFactor` from the counterexample hypothesis, so the arithmetic
small-prime-exclusion input to `LLSWeightedComparisonCore` need not be supplied separately once
`LLSCharacterTrivialBelow` is available.
-/
theorem noSmallPrimeFactor_of_characterTrivialBelow {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {X : ℝ} (htrivial : LLSCharacterTrivialBelow χ X) :
    AnalyticNumberTheory.Arithmetic.NoSmallPrimeFactor q X := by
  intro p hp hpX hpdvd
  have hcop : ¬Nat.Coprime p q := fun hc ↦ (hp.coprime_iff_not_dvd.mp hc) hpdvd
  have hzero : χ p = 0 := by
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff χ (p : ℤ)).mpr
        (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
  rw [htrivial p hp hpX] at hzero
  exact one_ne_zero hzero

/-- Every log-weighted term below the cutoff agrees with the Riemann term: it is either forced
equal by the counterexample hypothesis, or it sits exactly at the boundary `n = X`, where the
log weight vanishes regardless of the character value. -/
theorem re_characterLogWeightedTerm_eq_of_trivialBelow {q n : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {X : ℝ} (hX : 0 < X) (hn : n ∈ Finset.Ioc 0 ⌊X⌋₊)
    (htrivial : LLSCharacterTrivialBelow χ X) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm X χ n).re =
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm X n := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm, hΛ, zero_mul]
    change ((0 : ℂ) * χ n).re = 0
    rw [zero_mul, Complex.zero_re]
  · obtain ⟨p, k, hp, hk, rfl⟩ :=
      (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpbound : (p : ℝ) ≤ X := by
      have hpowFloor := (Finset.mem_Ioc.mp hn).2
      have hpPow : p ≤ p ^ k := Nat.le_pow hk
      exact
        (show (p : ℝ) ≤ (p ^ k : ℕ) by exact_mod_cast hpPow).trans
          ((Nat.le_floor_iff hX.le).mp hpowFloor)
    rcases lt_or_eq_of_le hpbound with hplt | hpeq
    · have hpvalue : χ p = 1 := htrivial p hp hplt
      rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm]
      simp only [Nat.cast_pow, map_pow, hpvalue, one_pow, mul_one, Complex.ofReal_re]
    · have hpk_le_nat : p ^ k ≤ ⌊X⌋₊ := (Finset.mem_Ioc.mp hn).2
      have hpk_le : ((p ^ k : ℕ) : ℝ) ≤ X := (Nat.cast_le.mpr hpk_le_nat).trans (Nat.floor_le hX.le)
      have hpk_ge : (p : ℝ) ≤ (p : ℝ) ^ k := le_self_pow₀ (by exact_mod_cast hp.one_lt.le) hk.ne'
      have hpk_eq : (p : ℝ) ^ k = X := le_antisymm (by exact_mod_cast hpk_le) (hpeq ▸ hpk_ge)
      have hzeroterm : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm X (p ^ k) = 0 := by
        rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm,
          show ((p ^ k : ℕ) : ℝ) = X from by
            push_cast; exact hpk_eq,
          div_self hX.ne', Real.log_one, mul_zero]
      rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm, hzeroterm]
      simp

/--
Input/assumptions: a level-`q` character trivial on every prime residue below `X > 0`.
Conclusion: the log-weighted defect vanishes exactly.
Content: every term of `characterLogWeightedSum X χ` has the same real part as the corresponding
Riemann term, by `re_characterLogWeightedTerm_eq_of_trivialBelow`.
Role: supplies `dS = 0` in `LLSWeightedComparisonCore` for Theorem 1.1 S2.
-/
theorem weightedLogDefect_eq_zero_of_trivialBelow {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {X : ℝ} (hX : 0 < X) (htrivial : LLSCharacterTrivialBelow χ X) : weightedLogDefect χ X = 0 := by
  unfold weightedLogDefect
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
    AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
  rw [sub_eq_zero, Complex.re_sum]
  exact
    Finset.sum_congr rfl fun n hn ↦
      (re_characterLogWeightedTerm_eq_of_trivialBelow hX hn htrivial).symm

/-- Every reciprocal-weighted term below the cutoff agrees with the Riemann term: forced equal by
the counterexample hypothesis, or sitting exactly at the boundary `n = X`, where the reciprocal
weight vanishes regardless of the character value. -/
theorem re_characterReciprocalWeightedTerm_eq_of_trivialBelow {q n : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {X : ℝ} (hX : 0 < X) (hn : n ∈ Finset.Ioc 0 ⌊X⌋₊)
    (htrivial : LLSCharacterTrivialBelow χ X) :
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm X χ n).re =
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm X n := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm,
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm, hΛ, zero_div, zero_mul]
    norm_num only [Complex.ofReal_zero, zero_mul, Complex.zero_re]
  · obtain ⟨p, k, hp, hk, rfl⟩ :=
      (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpbound : (p : ℝ) ≤ X := by
      have hpowFloor := (Finset.mem_Ioc.mp hn).2
      have hpPow : p ≤ p ^ k := Nat.le_pow hk
      exact
        (show (p : ℝ) ≤ (p ^ k : ℕ) by exact_mod_cast hpPow).trans
          ((Nat.le_floor_iff hX.le).mp hpowFloor)
    rcases lt_or_eq_of_le hpbound with hplt | hpeq
    · have hpvalue : χ p = 1 := htrivial p hp hplt
      rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm]
      simp only [Nat.cast_pow, map_pow, hpvalue, one_pow, mul_one, Complex.ofReal_re]
    · have hpk_le_nat : p ^ k ≤ ⌊X⌋₊ := (Finset.mem_Ioc.mp hn).2
      have hpk_le : ((p ^ k : ℕ) : ℝ) ≤ X := (Nat.cast_le.mpr hpk_le_nat).trans (Nat.floor_le hX.le)
      have hpk_ge : (p : ℝ) ≤ (p : ℝ) ^ k := le_self_pow₀ (by exact_mod_cast hp.one_lt.le) hk.ne'
      have hpk_eq : (p : ℝ) ^ k = X := le_antisymm (by exact_mod_cast hpk_le) (hpeq ▸ hpk_ge)
      have hnX : ((p ^ k : ℕ) : ℝ) = X := by
        push_cast; exact hpk_eq
      have hzeroterm : AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm
        X (p ^ k) = 0 := by
        rw [AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm,
        hnX, div_self hX.ne', sub_self, mul_zero]
      rw [AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm, hzeroterm]
      simp

/--
Input/assumptions: a level-`q` character trivial on every prime residue below `X > 0`.
Conclusion: the reciprocal-weighted defect vanishes exactly.
Content: every term of `characterReciprocalWeightedSum X χ` has the same real part as the
corresponding Riemann term, by `re_characterReciprocalWeightedTerm_eq_of_trivialBelow`.
Role: supplies `dR = 0` in `LLSWeightedComparisonCore` for Theorem 1.1 S2.
-/
theorem weightedReciprocalDefect_eq_zero_of_trivialBelow {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {X : ℝ} (hX : 0 < X) (htrivial : LLSCharacterTrivialBelow χ X) :
    weightedReciprocalDefect χ X = 0 := by
  unfold weightedReciprocalDefect
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum
    AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
  rw [sub_eq_zero, Complex.re_sum]
  exact
    Finset.sum_congr rfl fun n hn ↦
      (re_characterReciprocalWeightedTerm_eq_of_trivialBelow hX hn htrivial).symm

/-- `LLSWeightedComparisonS2Defects` follows from the counterexample hypothesis alone: no
separate arithmetic small-prime-factor input on `q` is needed once `χ` is trivial below `X`. -/
theorem llsWeightedComparisonS2Defects_of_trivialBelow {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq1 : 0 < (Real.log q) ^ 2)
    (htrivial : LLSCharacterTrivialBelow χ ((Real.log q) ^ 2)) :
    LLSWeightedComparisonS2Defects q χ :=
  ⟨(weightedLogDefect_eq_zero_of_trivialBelow hq1 htrivial).le,
    (weightedReciprocalDefect_eq_zero_of_trivialBelow hq1 htrivial).le⟩

/-- Triviality at every prime strictly below `X` passes to the primitive character.
The counterexample assumption excludes those primes from the original modulus;
the inducing character therefore has the same value. The strict cutoff is preserved. -/
theorem characterTrivialBelow_primitiveCharacter {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {X : ℝ} (htrivial : LLSCharacterTrivialBelow χ X) :
    LLSCharacterTrivialBelow χ.primitiveCharacter X := by
  intro p hp hpx
  have hc := hp.coprime_iff_not_dvd.mpr
    (noSmallPrimeFactor_of_characterTrivialBelow htrivial p hp hpx)
  have heq := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hc)
  simp only [Int.cast_natCast] at heq
  exact heq.trans (htrivial p hp hpx)

end PseudoPrime.LLS
