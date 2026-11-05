/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalRatioCover

/-! # Three-factor coefficient from even-anchor coverage -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Seven even-anchor cells covering local scales from `25/3` through `3461/15`.
The rational boundaries overlap exactly and each anchor is certified in the local table. -/
def threeFactorRatioCells : List LocalRatioCell :=
  [⟨8, 324969 / 100000, 3, 25 / 3, 324969 / 3533⟩,
    ⟨64, 310121 / 50000, 6, 324969 / 3533, 620242 / 3533⟩,
    ⟨160, 76157 / 10000, 8, 620242 / 3533, 761570 / 3533⟩,
    ⟨192, 158329 / 20000, 8, 761570 / 3533, 791645 / 3533⟩,
    ⟨216, 811399 / 100000, 8, 791645 / 3533, 811399 / 3533⟩,
    ⟨220, 814499 / 100000, 8, 811399 / 3533, 814499 / 3533⟩,
    ⟨222, 81603 / 10000, 8, 814499 / 3533, 3461 / 15⟩]

/-- The seven anchor cells cover the required local interval and satisfy the ratio budget.
The finite rational check verifies each anchor and every adjacent endpoint. -/
theorem threeFactorRatioCells_checked :
    localRatioCoverCheck (25 / 3) (3461 / 15) threeFactorRatioCells = true := by decide +kernel

/-- Under GRH, an odd input with at least three prime factors and logarithm between
`25/2` and `3461/10` has a rejecting prime at most `(517/1250) * (log n)²`. The two-factor
logarithmic mean gives a local scale of `2 log n / 3`, and seven even-anchor cells bound
its radius by `96467/100000` times that scale. -/
theorem exists_prime_reject_three_factors_4136 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hlo : (25 / 2 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3461 / 10 : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (517 / 1250 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_three_factors_local hn ho hGRH hk
  have hslo : (25 / 3 : ℝ) ≤ 2 * Real.log n / 3 := by linarith only [hlo]
  have hshi : 2 * Real.log n / 3 ≤ (3461 / 15 : ℝ) := by linarith only [hhi]
  have hslo' : ((25 / 3 : ℚ) : ℝ) ≤ 2 * Real.log n / 3 := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact hslo
  have hshi' : 2 * Real.log n / 3 ≤ ((3461 / 15 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact hshi
  have hlocal :=
    localRatioCoverCheck_sound threeFactorRatioCells (25 / 3) (3461 / 15)
      threeFactorRatioCells_checked hslo' hshi'
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlocal
  have hcoeff :
    ((96467 / 100000 : ℝ) * (2 * Real.log n / 3)) ^ 2 ≤ (517 / 1250 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [sq_nonneg (Real.log n)]
  exact ⟨r, hr, hb.trans (hlocal.trans hcoeff), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
