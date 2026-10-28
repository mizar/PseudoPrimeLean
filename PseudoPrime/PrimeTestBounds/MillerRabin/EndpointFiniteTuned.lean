/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointFiniteTunedProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFinitePrincipal

/-! # Actual rejecting primes and least primes from the tuned thirteen profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Each of thirteen finite-principal profiles gives an actual rejecting prime through its cap. -/
theorem exists_prime_finiteTuned (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.tunedCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ f.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_finitePrincipal_gap hn ho hc hGRH (Analysis.finitePrincipal_radius_bounds f).1
      f.tunedR f.tunedS (Analysis.finiteTuned_reciprocal f) (Analysis.finiteTuned_smoothed f)
      (LLS.PaperStatements.finiteTuned_profile_gap f hL)
  have hq : (p : ℝ) < f.nextPrime := hb.trans_lt (Analysis.finitePrincipal_radius_bounds f).2
  exact ⟨p, hp, Nat.cast_le.mpr (finitePrincipal_round f hp (by exact_mod_cast hq)), hr⟩

/-- The least rejecting prime also satisfies each of the thirteen strengthened fixed cutoffs. -/
theorem exists_least_finiteTuned (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.tunedCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_finiteTuned f hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
