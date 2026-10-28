/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointPointwiseWindow
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextIntervalSelection

/-! # Prime rounding on a continuous pointwise window -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On [29/2,15], rounding the pointwise cutoff gives exactly 113, strictly below
the real cutoff. Verify only the finite prime gap from 113 to 127. -/
theorem pointwise_primeRound113 {L : ℝ} (hL : 29 / 2 ≤ L) (hU : L ≤ 15) :
    primeRound (LLS.PaperStatements.pointwiseCutoff L) = 113 ∧
      (113 : ℝ) < LLS.PaperStatements.pointwiseCutoff L := by
  have hw := LLS.PaperStatements.pointwiseCutoff_window113 hL hU
  have hp : Nat.Prime 113 := by decide +kernel
  have ho : Odd (113 : ℕ) := by decide +kernel
  exact
    ⟨primeRound_eq_odd_of_gap hp ho hw.1.le hw.2
        (by decide +kernel : ∀ k ∈ Finset.Ioo 113 127, ¬Nat.Prime k),
      hw.1⟩

/-- The current selected envelope rounds to 113 on the full logarithmic interval
[29/2,15]. Use its proved equality with the pointwise candidate on that interval. -/
theorem nextSelected_primeRound113 {n : ℕ} (hn : 1 < n) (hL : 29 / 2 ≤ Real.log n)
    (hU : Real.log n ≤ 15) :
    primeRound (nextSelectedEnvelope n) = 113 ∧ (113 : ℝ) < nextSelectedEnvelope n := by
  rw [← next_eq_selected hn, next_eq_pointwise hn (by linarith only [hL]) (by linarith only [hU])]
  exact pointwise_primeRound113 hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
