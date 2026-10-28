/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianRecoveredSeededComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRecoveredSeededBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextIntervalSelection

/-! # Selected recovered seeded Gaussian witnesses and strict baseline comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On L>=63 the actual two-profile witness envelope equals the exact selected
numerical candidate, including the short entrance interval before 63+delta. -/
theorem recoveredSeededEnvelope_eq {L : ℝ} (hL : 63 ≤ L) :
    gaussianRecoveredSeededEnvelope L = Analysis.gaussianRecoveredSeeded L := by
  exact (Analysis.gaussianRecoveredSeeded_eq_min hL).symm

/-- Under GRH each odd composite with log n>=63 has an actual prime witness
below the selected recovered seeded cutoff. Apply the actual-prefix minimum theorem
and the independently proved numerical selection identity. -/
theorem exists_prime_recoveredSeededSelected {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianRecoveredSeeded (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← recoveredSeededEnvelope_eq hL]
  exact exists_prime_gaussianRecoveredSeeded ho hc hGRH hL

/-- Under the same all-input assumptions, the least rejecting prime lies below
the selected recovered seeded cutoff. Preserve the least-prime conclusion under selection. -/
theorem exists_least_recoveredSeededSelected {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianRecoveredSeeded (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← recoveredSeededEnvelope_eq hL]
  exact exists_least_gaussianRecoveredSeeded ho hc hGRH hL

/-- Below the old triangular entrance, the two varying baseline seeded ranges
strictly improve the baseline next-selected envelope. Plateaus are deliberately excluded;
all interval boundaries use the existing exact switches. -/
theorem recoveredSeeded_lt_nextSelected {n : ℕ} (hn : 1 < n) (hU : Real.log n < 1500000000000)
    (hstrict :
      (Analysis.gaussianSeededSwitch false 35000 < Real.log n ∧
          Real.log n < Analysis.gaussianSeededSwitch false 50000) ∨
        Analysis.gaussianSeededSwitch true 50000 < Real.log n) :
    Analysis.gaussianRecoveredSeeded (Real.log n) < nextSelectedEnvelope n := by
  have h240 : (240 : ℝ) ≤ Real.log n := by
    rcases hstrict with h | h
    · linarith only [h.1, Analysis.gaussianSeeded_switch35_bounds.1]
    · linarith only [h, (Analysis.gaussianSeeded_switch50_bounds true).1]
  rw [← next_eq_selected hn, next_eq_seeded hn h240 hU]
  rcases hstrict with h | h
  · exact Analysis.gaussianRecoveredSeeded_strict_first (by linarith only [h240]) h.1 h.2
  · exact Analysis.gaussianRecoveredSeeded_strict_last (by linarith only [h240]) h

end PseudoPrime.PrimeTestBounds.MillerRabin
