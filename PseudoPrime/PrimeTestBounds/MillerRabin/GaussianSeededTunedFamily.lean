/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSeededTunedOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedBounds

/-! # Actual witnesses under the tuned seeded minimum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH a single least rejecting prime is bounded by both tuned seeded profiles.
Transfer the second independently certified cutoff by minimality of the first witness. -/
theorem exists_least_seededTunedFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededTunedFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hl⟩ := exists_least_seededTuned false ho hc hGRH hL
  obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_seededTuned true ho hc hGRH hL
  have ht : (p : ℝ) ≤ Analysis.gaussianSeededTunedBound true (Real.log n) :=
    (Nat.cast_le.mpr (hl q hq hqr)).trans hqb
  exact ⟨p, hp, le_min hb ht, hr, hl⟩

/-- Under GRH the tuned seeded minimum is an actual rejecting-prime bound
for every odd composite at logarithmic scale at least 63. -/
theorem exists_prime_seededTunedFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededTunedFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (exists_least_seededTunedFamily ho hc hGRH hL).imp fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
