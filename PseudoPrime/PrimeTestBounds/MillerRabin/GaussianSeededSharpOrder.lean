/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

public import PseudoPrime.Analysis.GaussianSeededSharpComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededSharpBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededCurrentOrder

/-! # Selected recovered seeded Gaussian witnesses and strict baseline comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On L>=63 the actual two-profile witness envelope equals the exact selected
numerical candidate, including the short entrance interval before 63+delta. -/
theorem seededSharpEnvelope_eq {L : ℝ} (hL : 63 ≤ L) :
    gaussianSeededSharpEnvelope L = Analysis.gaussianSeededSharp L := by
  exact (Analysis.gaussianSeededSharp_eq_min hL).symm

/-- Under GRH each odd composite with log n>=63 has an actual prime witness
below the selected recovered seeded cutoff. Apply the actual-prefix minimum theorem
and the independently proved numerical selection identity. -/
theorem exists_prime_seededSharpSelected {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededSharp (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← seededSharpEnvelope_eq hL]
  exact exists_prime_gaussianSeededSharp ho hc hGRH hL

/-- Under the same all-input assumptions, the least rejecting prime lies below
the selected recovered seeded cutoff. Preserve the least-prime conclusion under selection. -/
theorem exists_least_seededSharpSelected {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededSharp (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← seededSharpEnvelope_eq hL]
  exact exists_least_gaussianSeededSharp ho hc hGRH hL

/-- On either full strict seeded band before the current triangular entrance, the new
selected cutoff is strictly below the current refined public selection. -/
theorem seededSharp_lt_refinedSelected {n : ℕ} (hn : 1 < n) (hU : Real.log n < 1100000000000)
    (hstrict :
      (Analysis.gaussianRecoveredSeededSwitch false 35000 < Real.log n ∧
          Real.log n <
            Analysis.gaussianRecoveredSeededSwitch false 50000 +
              Analysis.gaussianSeededSharpShift) ∨
        Analysis.gaussianRecoveredSeededSwitch true 50000 < Real.log n) :
    Analysis.gaussianSeededSharp (Real.log n) < refinedSelectedEnvelope n := by
  have h240 : (240 : ℝ) ≤ Real.log n := by
    rcases hstrict with h | h
    · linarith only [h.1, Analysis.gaussianRecoveredSeeded_switch35_bounds.1]
    · linarith only [h, (Analysis.gaussianRecoveredSeeded_switch50_bounds true).1]
  rw [refinedSelected_eq_currentSeeded hn h240 hU]
  rcases hstrict with h | h
  · exact Analysis.gaussianSeededSharp_strict_first_full (by linarith only [h240]) h.1 h.2
  · exact Analysis.gaussianSeededSharp_strict_last (by linarith only [h240]) h

end PseudoPrime.PrimeTestBounds.MillerRabin
