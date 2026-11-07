/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Log8
public import PseudoPrime.PrimeTestBounds.MillerRabin.CumulativeHighBounds

/-! # Least rejecting prime at logarithmic scale at least 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the least rejecting prime for an odd composite with logarithm at
least 8 is bounded by three tenths of its squared logarithm. Transfer the
actual witness bound using the minimality of the canonical least prime. -/
theorem compositeLeastPrime_le_03_log8
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hL : (8 : ℝ) ≤ Real.log n) :
    (compositeLeastPrime n : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_reject_03_log8 hn ho hc hGRH hL
  have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
  exact (Nat.cast_le.mpr hm).trans hb

end PseudoPrime.PrimeTestBounds.MillerRabin
