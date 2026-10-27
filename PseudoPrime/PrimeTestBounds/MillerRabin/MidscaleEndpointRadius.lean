/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MidscaleEndpointRadius
public import PseudoPrime.PrimeTestBounds.MillerRabin.FullEndpointEightyOneRange

/-! # Prime MR witnesses through the continuous midscale endpoint radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite N>1 under GRH in the midscale logarithmic interval,
a prime through the squared piecewise affine radius rejects the strong test.
Use a nonprincipal character trivial on all passing residues. The rejecting
prime may be 2, and square composites are included. -/
theorem exists_prime_reject_le_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : 1339 / 50 ≤ Real.log N) (hhi : Real.log N ≤ 26269 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (LLS.PaperStatements.midscaleEndpointRadius (Real.log N)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) := by
  obtain ⟨χ, hχ, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_le_midscale_radius_sq χ hχ hGRH hlo hhi
  refine ⟨p, hp, hb, ?_⟩
  intro ha
  exact hv (hpass p ha)

/-- Under the midscale hypotheses, the least rejecting prime satisfies the
squared affine-radius bound. Minimize the full prime rejection predicate, so
minimality holds among all rejecting primes, including prime 2. -/
theorem exists_least_prime_reject_le_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : 1339 / 50 ≤ Real.log N) (hhi : Real.log N ≤ 26269 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        (p : ℝ) ≤ (LLS.PaperStatements.midscaleEndpointRadius (Real.log N)) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_le_midscale_radius_sq hn ho hc hGRH hlo hhi
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
