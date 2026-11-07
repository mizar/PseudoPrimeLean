/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrimeSupport
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerHigherData

/-! # Actual Euler prefix from separated prime and higher-power payloads -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked prime payload uses the positive closed cutoff convention.
Prime positivity removes zero, while the successor endpoint gives 50000.
This matches the actual Euler-center finite sum. -/
theorem centerPrimes50000_Ioc :
    centerPrimes50000.toFinset = (Finset.Ioc 0 50000).filter Nat.Prime := by
  rw [centerPrimes50000_finset]
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc, Nat.zero_le, true_and,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨hb, hp⟩
    exact ⟨⟨hp.pos, hb⟩, hp⟩
  · rintro ⟨⟨_, hb⟩, hp⟩
    exact ⟨hb, hp⟩

/-- The actual Euler prefix through 50000 is the sum of its checked prime
payload and its 84 higher-power entries. Combine the support split with
the two exact payload identities. Numerical bounds for these two pieces
therefore bound the full finite prefix without an unverified support input. -/
theorem center50000_prefix_split :
    (∑ m ∈ Finset.Ioc 0 50000, Analysis.gammaResolventMangoldtWeight m) =
      (∑ p ∈ centerPrimes50000.toFinset, Analysis.gammaResolventMangoldtWeight p) +
        ∑ pk ∈ centerHigherPowers.toFinset,
          Analysis.gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)) := by
  rw [gamma_prefix_split_primes, ← centerPrimes50000_Ioc,
    higher_payload_sum Analysis.gammaResolventMangoldtWeight]

end PseudoPrime.PrimeTestBounds.MillerRabin
