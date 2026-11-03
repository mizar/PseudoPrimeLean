/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientBounds

/-! # High-range strong Miller–Rabin primality criterion -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd integer `n > 1` with `log n ≥ 70000` is prime exactly
when it passes the strong Miller–Rabin test at every prime base at most
`(7 / 16) * log n ^ 2`. A composite has a rejecting prime in that range;
prime acceptance follows from the existing log-square criterion. -/
theorem prime_iff_mr_highCoeff (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hL : (70000 : ℝ) ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf⟩ := highCoeff_prime_witness hn ho hc hGRH hL
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    by_contra hnot
    have hbound : (p : ℝ) ≤ (Real.log n) ^ 2 := by
      have hsq := sq_nonneg (Real.log n)
      nlinarith only [hb, hsq]
    exact
      no_prime_millerRabin_witness_le_log_sq_of_prime ho hp
        ⟨p, hprime, hbound, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
