/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTestBounds.MillerRabin.SmallLogBound
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTest.MillerRabin.WitnessBound
import PseudoPrime.LLS.Theorem11S2
import PseudoPrime.PrimeTest.MillerRabin.Composite
import PseudoPrime.PrimeTest.MillerRabin.Prime
import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Large-input and GRH assembly for the Miller–Rabin witness bound
-/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithmic-square cutoff is strictly below every odd prime modulus. -/
private theorem log_sq_lt_of_odd_prime {n : ℕ} (hnPrime : Nat.Prime n) (hnOdd : Odd n) :
    (Real.log (n : ℝ)) ^ 2 < (n : ℝ) := by
  have hn3 : 3 ≤ n := by
    rcases hnPrime.two_le.eq_or_lt with h | h
    · subst n
      norm_num only at hnOdd
    · exact h
  by_cases hn9 : n < 9
  · interval_cases n
    · have hlog : Real.log (3 : ℝ) < 11 / 10 := Real.log_three_lt_d9.trans (by norm_num only)
      have hsq :=
        mul_self_lt_mul_self
          ((Real.log_nonneg_iff (by norm_num only : (0 : ℝ) < 3)).2 (by norm_num only)) hlog
      change (Real.log (3 : ℝ)) ^ 2 < 3
      nlinarith only [hsq]
    · norm_num only at hnPrime
    · have hlog : Real.log (5 : ℝ) < 161 / 100 := Real.log_five_lt_d9.trans (by norm_num only)
      have hsq :=
        mul_self_lt_mul_self
          ((Real.log_nonneg_iff (by norm_num only : (0 : ℝ) < 5)).2 (by norm_num only)) hlog
      change (Real.log (5 : ℝ)) ^ 2 < 5
      nlinarith only [hsq]
    · norm_num only at hnPrime
    · have hlog7 : Real.log 7 < 21 / 10 := by
        calc
          Real.log 7 < Real.log 8 := Real.log_lt_log (by norm_num only) (by norm_num only)
          _ = 3 * Real.log 2 := by
            rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
            norm_num only
          _ < 21 / 10 := by nlinarith only [Real.log_two_lt_d9]
      have hsq :=
        mul_self_lt_mul_self
          ((Real.log_nonneg_iff (by norm_num only : (0 : ℝ) < 7)).2 (by norm_num only)) hlog7
      change (Real.log (7 : ℝ)) ^ 2 < 7
      nlinarith only [hsq]
    · norm_num only at hnPrime
  · have hn9' : 9 ≤ n := Nat.le_of_not_lt hn9
    have he2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num only, Real.exp_add]
      have hpos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have hsq : Real.exp 1 * Real.exp 1 < 3 * 3 := mul_self_lt_mul_self hpos Real.exp_one_lt_three
      nlinarith only [hsq]
    have hn9cast : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9'
    have hexp : Real.exp 2 ≤ (n : ℝ) := le_trans he2.le hn9cast
    have hratio := Real.log_div_sqrt_antitoneOn (le_rfl : Real.exp 2 ≤ Real.exp 2) hexp hexp
    have hsqrt : Real.sqrt (Real.exp 2) = Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num only, Real.exp_add]
      exact Real.sqrt_mul_self (Real.exp_nonneg 1)
    have hbase : Real.log (Real.exp 2) / Real.sqrt (Real.exp 2) < 1 := by
      rw [Real.log_exp, hsqrt]
      exact (div_lt_one (Real.exp_pos 1)).2 Real.exp_one_gt_two
    have hratio' : Real.log (n : ℝ) / Real.sqrt (n : ℝ) < 1 := lt_of_le_of_lt hratio hbase
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hloglt : Real.log (n : ℝ) < Real.sqrt (n : ℝ) := by
      rwa [div_lt_iff₀ hsqrtpos, one_mul] at hratio'
    have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
      (Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 1 < 3) hn3))).le
    have hsquare := (sq_lt_sq₀ hlognonneg (Real.sqrt_nonneg (n : ℝ))).mpr hloglt
    rw [Real.sq_sqrt (by positivity)] at hsquare
    exact hsquare

/-- Assuming the S2 interface, every odd composite `n ≥ 3000` has a prime witness at most
`(log n)^2` for the canonical strong test. A small prime divisor is rejected directly;
otherwise S2 supplies a prime outside the proper subgroup containing all passing residues.
This is the large-input branch of the GRH witness theorem. -/
theorem exists_prime_millerRabin_witness_le_log_sq_of_s2 (hS2 : LLS.llsTheorem11S2) {n : ℕ}
    (hn : 1 < n) (hnOdd : Odd n) (hnNotPrime : ¬Nat.Prime n) (hlarge : 3000 ≤ n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    ∃ p : ℕ,
      Nat.Prime p ∧
        (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  have hNeZero : NeZero n := ⟨Nat.ne_of_gt (lt_trans (by decide : 0 < 1) hn)⟩
  by_cases hsmallFactor : ∃ p : ℕ, Nat.Prime p ∧ (p : ℝ) < (Real.log (n : ℝ)) ^ 2 ∧ p ∣ n
  · obtain ⟨p, hp, hpBound, hpDiv⟩ := hsmallFactor
    refine ⟨p, hp, hpBound.le, ?_⟩
    exact
      PrimeTest.not_strongMillerRabinPass_iff.mp
        (PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp hpDiv)
  · have hnoSmallFactor : ∀ p : ℕ, Nat.Prime p → (p : ℝ) < (Real.log (n : ℝ)) ^ 2 → ¬p ∣ n := by
      intro p hp hpBound hpDiv
      exact hsmallFactor ⟨p, hp, hpBound, hpDiv⟩
    obtain ⟨H, hHproper, hpassImage⟩ :=
      PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnNotPrime
    obtain ⟨p, hp, hpBound, hpOutside⟩ := hS2 n hlarge hnoSmallFactor H hHproper
    refine ⟨p, hp, hpBound, ?_⟩
    apply PrimeTest.not_strongMillerRabinPass_iff.mp
    exact PrimeTest.not_pass_of_outside_subgroup hpassImage hpOutside

/-- Under GRH, every odd composite `n > 1` has a prime witness at most `(log n)^2`
for the canonical strong test. The finite certificate handles `n < 3000`, and the S2
subgroup argument handles `n ≥ 3000`. -/
theorem exists_prime_millerRabin_witness_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) (hnNotPrime : ¬Nat.Prime n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    ∃ p : ℕ,
      Nat.Prime p ∧
        (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  have hS2 : LLS.llsTheorem11S2 := LLS.llsTheorem11S2_of_grh hGRH
  by_cases hsmall : n < 3000
  · exact exists_prime_millerRabin_witness_le_log_sq_of_lt_3000 hn hnOdd hnNotPrime hsmall
  · have hlarge : 3000 ≤ n := Nat.le_of_not_lt hsmall
    exact exists_prime_millerRabin_witness_le_log_sq_of_s2 hS2 hn hnOdd hnNotPrime hlarge

/-- An odd prime has no prime witness at most `(log n)^2` that fails the canonical strong
test. The logarithmic estimate puts each candidate base below `n`, hence coprime to the
prime modulus; prime-base acceptance then contradicts the witness inequalities. -/
theorem no_prime_millerRabin_witness_le_log_sq_of_prime {n : ℕ} (hnOdd : Odd n)
    (hnPrime : Nat.Prime n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    ¬∃ p : ℕ,
        Nat.Prime p ∧
          (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
          (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  dsimp only
  rintro ⟨p, hp, hpBound, hreject⟩
  have hpLt : p < n := by
    have hcast : (p : ℝ) < (n : ℝ) := lt_of_le_of_lt hpBound (log_sq_lt_of_odd_prime hnPrime hnOdd)
    exact_mod_cast hcast
  have hcop : Nat.Coprime p n :=
    Nat.coprime_comm.mpr <|
      hnPrime.coprime_iff_not_dvd.mpr
        (by
          intro hdiv
          have hle : n ≤ p := Nat.le_of_dvd hp.pos hdiv
          exact (Nat.not_lt.mpr hle) hpLt)
  have hpass : PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    PrimeTest.isStrongMillerRabinProbablePrime_iff_pass.mp
      (PrimeTest.strongMillerRabinWithBase_eq_true_iff.mp
        (PrimeTest.strongMillerRabinWithBase_of_prime hnPrime hcop))
  exact (PrimeTest.not_strongMillerRabinPass_iff.mpr hreject) hpass

/-- Under GRH, odd `n > 1` is prime exactly when every prime base at most `(log n)^2`
has `p^d = 1` or `p^(2^j d) = -1` for some `j < s`, where `s` and `d` are computed from
`n - 1`. A bounded rejected witness rules out composite `n`; for prime `n`, each bounded
prime base is coprime to `n` and passes the prime-modulus test. -/
theorem prime_iff_millerRabin_for_all_primes_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_contra hnNotPrime
    obtain ⟨p, hp, hpBound, hreject⟩ :=
      exists_prime_millerRabin_witness_le_log_sq hGRH hn hnOdd hnNotPrime
    have hstrong : PrimeTest.StrongMillerRabinPass n (p : ZMod n) := hpass p hp hpBound
    exact (PrimeTest.not_strongMillerRabinPass_iff.mpr hreject) hstrong
  · intro hnPrime p hp hpBound
    have hpLt : p < n := by
      have hcast : (p : ℝ) < (n : ℝ) :=
        lt_of_le_of_lt hpBound (log_sq_lt_of_odd_prime hnPrime hnOdd)
      exact_mod_cast hcast
    have hcop : Nat.Coprime p n :=
      Nat.coprime_comm.mpr <|
        hnPrime.coprime_iff_not_dvd.mpr
          (by
            intro hdiv
            have hle : n ≤ p := Nat.le_of_dvd hp.pos hdiv
            exact (Nat.not_lt.mpr hle) hpLt)
    exact
      PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass.mp
        (PrimeTest.strongMillerRabinWithBase_of_prime hnPrime hcop)

/-- Under GRH, every odd composite `n > 1` has a prime base at most `(log n)^2` whose
canonical odd-part power differs from `1` and whose every repeated-square power differs
from `-1`. This records the former Boolean rejection result with its power conditions
visible in the declaration; the witness theorem supplies the same conditions. -/
theorem exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) (hnNotPrime : ¬Nat.Prime n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    ∃ p : ℕ,
      Nat.Prime p ∧
        (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  exact exists_prime_millerRabin_witness_le_log_sq hGRH hn hnOdd hnNotPrime

end PseudoPrime.PrimeTestBounds.MillerRabin
