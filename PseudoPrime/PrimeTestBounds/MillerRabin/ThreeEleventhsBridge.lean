/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeLogSquareBounds
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsGRH

/-! # Three-elevenths Miller–Rabin criterion -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd natural number `n > 1` is prime if and only if it passes
the strong Miller–Rabin test for every prime base at most
`max 2 ((3 / 11) * (log n)^2)`. The least rejecting-prime bound proves the
composite direction; base-two acceptance and the log-square bound prove the
prime direction. -/
theorem prime_millerRabin_027_criterion
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf, _⟩ := three_eleven_least_of_grh hn ho hc hGRH
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    rcases (le_max_iff.mp hb) with htwo | hlarge
    · have hp2 : p = 2 := Nat.le_antisymm (by exact_mod_cast htwo) hprime.two_le
      subst p
      exact
        PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass.mp
          (PrimeTest.strongMillerRabinBase2_of_prime_of_ne_two hp (ho.ne_two_of_dvd_nat dvd_rfl))
    · by_contra hnot
      have hbound : (p : ℝ) ≤ Real.log n ^ 2 := by nlinarith only [hlarge, sq_nonneg (Real.log n)]
      exact
        no_prime_millerRabin_witness_le_log_sq_of_prime ho hp
          ⟨p, hprime, hbound, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
