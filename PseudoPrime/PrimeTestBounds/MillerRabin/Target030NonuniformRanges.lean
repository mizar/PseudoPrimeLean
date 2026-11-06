/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Nonuniform5551
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030High

/-! # Covered nonuniform ranges for the 0.30 bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a nonuniform odd composite with logarithm in `[8, 55.51]`
or at least 100 has a 0.30 rejecting prime. The count-based low range and
the fixed-index high range supply the two cases. -/
theorem exists_prime_reject_03_nonuniform_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hcover : Real.log n ≤ 5551 / 100 ∨ 100 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  rcases hcover with hlow | hhigh
  · exact exists_prime_reject_03_nonuniform_5551 hn ho hc hu hGRH hL hlow
  · exact exists_prime_reject_03_nonuniform100 hn ho hc hGRH hhigh hu

end PseudoPrime.PrimeTestBounds.MillerRabin
