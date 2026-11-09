/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileBounds

/-! # Actual prime and least witnesses for the seven tuned triangular certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a chosen tuned profile and an odd composite n>1, GRH and its unchanged
entrance imply an actual rejecting prime below its smaller quadratic cutoff.
The generic theorem closes the local, large-index, and uniform triple branches. -/
theorem exists_prime_triangularTunedProfile (i : Fin 7) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (triangularTunedProfile i).T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (triangularTunedProfile i).C * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile (triangularTunedProfile i) hn ho hc hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
