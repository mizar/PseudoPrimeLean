/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Log8

/-! # Coefficient 0.28 on the bounded logarithmic range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm between 8 and 1000 has a
rejecting prime within `7 / 25` times its squared logarithm. The global
logarithmic-scale witness proves the stronger assertion without the upper bound. -/
theorem exists_reject_028_analytic1000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (_hU : Real.log n ≤ (1000 : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact exists_prime_reject_028_log8 hn ho hc hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
