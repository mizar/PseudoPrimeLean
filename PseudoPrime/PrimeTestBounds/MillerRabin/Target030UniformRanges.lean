/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformLow
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformGaussian

/-! # Covered 0.30 ranges for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd uniform Korselt triple has a 0.30 rejecting prime when
its logarithm is in `[8, 39.4]` or at least 5250. The finite classification
and local corrections cover the first range, and the Gaussian bound the second. -/
theorem uniformKorselt_reject_03_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hcover : Real.log n ≤ 197 / 5 ∨ 5250 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  rcases hcover with hlow | hhigh
  · exact uniformKorselt_reject_03_low hn ho hu hGRH hL hlow
  · let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
    have h100 : (100 : ℝ) ≤ Real.log n := by linarith only [hhigh]
    have hlarge : 20000 ≤ n :=
      (by norm_num only : (20000 : ℕ) ≤ 10 ^ 27).trans (ten_pow_27_le_of_log100 h100)
    exact uniformKorselt_reject_03_high ho hlarge hu hGRH hhigh

end PseudoPrime.PrimeTestBounds.MillerRabin
