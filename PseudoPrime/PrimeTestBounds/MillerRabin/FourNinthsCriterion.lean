/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Strong Miller--Rabin primality criterion with the four-ninths cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every prime base within the four-ninths cutoff passes at an odd prime.
This direction is unconditional: the cutoff is below the previously established
log-square cutoff, for which prime-modulus acceptance is already known. -/
theorem prime_passes_four_ninths {n : ℕ} (ho : Odd n) (hnp : n.Prime) {p : ℕ} (hp : p.Prime)
    (hb : (p : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnot
  have hbound : (p : ℝ) ≤ (Real.log n) ^ 2 := by
    have hsq := sq_nonneg (Real.log n)
    nlinarith only [hb, hsq]
  exact
    no_prime_millerRabin_witness_le_log_sq_of_prime ho hnp
      ⟨p, hp, hbound, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

/-- Under GRH, an odd integer greater than one is prime exactly when every prime
base up to four ninths of its squared logarithm passes the canonical strong test.
The composite direction uses the global rejecting-prime bound; prime acceptance
is unconditional and follows from the preceding theorem. -/
theorem prime_iff_mr_le_four_ninths_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_four_ninths hn ho hc hGRH
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    exact prime_passes_four_ninths ho hp hprime hb

end PseudoPrime.PrimeTestBounds.MillerRabin
