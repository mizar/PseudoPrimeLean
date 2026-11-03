/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientCumulative

/-! # History-preserving high-window bounds for cumulative MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing and high-window profiles in reverse order of their entrances. Each candidate
retains the preceding bound at its entrance, so all earlier inputs remain covered. -/
noncomputable def highWindowHistoryProfiles : List TriangularProfile :=
  [triangularP02823622, triangularP028289, triangularP028399, highWindowP0288, triangularP02891,
    highWindowP0296, triangularP02992, highWindowP0323, triangularP03315, highWindowP0346,
    highWindowP0369, highWindowP040, triangularP04145, highWindowP0423, triangularP04603]

/-- Cumulative high-window bound at a natural endpoint. The recursive history keeps
the previous bound at each new entrance and intersects it with the new quadratic candidate. -/
noncomputable def highWindowCumulative (N : ℕ) : ℝ :=
  min (highCoeffCumulative N)
    (baseHistory TriangularProfile.T TriangularProfile.C highCoeffHistoryBase
      highWindowHistoryProfiles (Real.log N))

/-- Under GRH, the cumulative maximum of least rejecting primes is bounded by the
high-window history at every natural endpoint. The general history theorem supplies the
entrance coverage and the certified triangular witness for each profile. -/
theorem cumulativeLeastPrime_le_highWindow
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ highWindowCumulative N :=
  le_min (cumulativeLeastPrime_le_highCoeff hGRH N)
    (cumulativeLeastPrime_le_base highCoeffHistoryBase highCoeffHistoryBase_nonneg
      (fun hn ho hc L hlog ↦ leastPrime_le_highCoeffScale hGRH hn ho hc L hlog)
      highWindowHistoryProfiles hGRH N)

/-- The new cumulative envelope never exceeds the previous one: each new history
step retains its predecessor as a candidate in a minimum. -/
theorem highWindowCumulative_le_previous (N : ℕ) :
    highWindowCumulative N ≤ highCoeffCumulative N := by exact min_le_left _ _

end PseudoPrime.PrimeTestBounds.MillerRabin
