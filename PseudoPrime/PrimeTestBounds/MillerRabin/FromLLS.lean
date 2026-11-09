/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallLogBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeLogSquareBounds
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.PrimeTest.MillerRabin.WitnessBound
public import PseudoPrime.LLS.Theorem11S2
public import PseudoPrime.PrimeTest.MillerRabin.Composite
public import PseudoPrime.PrimeTest.MillerRabin.Prime
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Large-input and GRH assembly for the Miller–Rabin witness bound
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Assuming the S2 interface, every odd composite `n ≥ 3000` has a prime witness at most
`(log n)^2` for the canonical strong test. A small prime divisor is rejected directly;
otherwise S2 supplies a prime outside the proper subgroup containing all passing residues.
This is the large-input branch of the GRH witness theorem. -/
theorem exists_prime_millerRabin_witness_le_log_sq_of_s2 (hS2 : LLS.llsTheorem11S2) {n : ℕ}
    (hn : 1 < n) (hnOdd : Odd n) (hnNotPrime : ¬Nat.Prime n) (hlarge : 3000 ≤ n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
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
      PrimeTest.exists_proper_subgroup_strongMR hn hnOdd hnNotPrime
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
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    ∃ p : ℕ,
      Nat.Prime p ∧
        (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  have hS2 : LLS.llsTheorem11S2 := LLS.llsTheorem11S2_of_grh hGRH
  by_cases hsmall : n < 3000
  · exact exists_primeWitness_lt_3000 hn hnOdd hnNotPrime hsmall
  · have hlarge : 3000 ≤ n := Nat.le_of_not_lt hsmall
    exact exists_prime_millerRabin_witness_le_log_sq_of_s2 hS2 hn hnOdd hnNotPrime hlarge

/-- Under GRH, odd `n > 1` is prime exactly when every prime base at most `(log n)^2`
has `p^d = 1` or `p^(2^j d) = -1` for some `j < s`, where `s` and `d` are computed from
`n - 1`. A bounded rejected witness rules out composite `n`; for prime `n`, each bounded
prime base is coprime to `n` and passes the prime-modulus test. -/
theorem prime_iff_millerRabin_for_all_primes_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
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
from `-1`. The canonical witness theorem supplies these power conditions directly; this entry
exposes the rejection certificate in the naming used by strong-test consumers. -/
theorem exists_rejectPowers_logSq_GRH (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) (hnNotPrime : ¬Nat.Prime n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    ∃ p : ℕ,
      Nat.Prime p ∧
        (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  exact exists_prime_millerRabin_witness_le_log_sq hGRH hn hnOdd hnNotPrime

end PseudoPrime.PrimeTestBounds.MillerRabin
