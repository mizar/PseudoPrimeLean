/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformTo663
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow76
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven465to700
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven700to1000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven1000to1500
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven1500to2000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven2000to3000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven3000to4000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven4000to5000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven5000to6000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven6000to7000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven7000to8000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven8000to9000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven9000to10000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven10000to10300

/-! # Uniform three-elevenths bound through logarithmic scale 10300 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every uniform Korselt triple with logarithm at most 10300 has
  a rejecting prime within the three-elevenths cutoff. The quarter bound covers
  the low range and independent uniform interval bounds cover the rest. -/
theorem uniform_three_eleven_to10300 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 10300) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
  by_cases h8 : 8 ≤ Real.log n
  swap
  · obtain ⟨p, hp, hb, hf⟩ :=
      quarter_uniform_low76 hn ho hu hGRH (by linarith only [le_of_not_ge h8])
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h663 : Real.log n ≤ 663
  · obtain ⟨p, hp, hb, hf⟩ := uniform_witness_8_to663 hn ho hu hGRH ⟨h8, h663⟩
    rw [show (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2 by ring] at hb
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h700 : Real.log n ≤ 700
  · exact uniform_three_eleven_465_700 hn ho hu hGRH (by linarith only [le_of_not_ge h663]) h700
  by_cases h1000 : Real.log n ≤ 1000
  · exact uniform_three_eleven_700_1000 hn ho hu hGRH (le_of_not_ge h700) h1000
  by_cases h1500 : Real.log n ≤ 1500
  · exact uniform_three_eleven_1000_1500 hn ho hu hGRH (le_of_not_ge h1000) h1500
  by_cases h2000 : Real.log n ≤ 2000
  · exact uniform_three_eleven_1500_2000 hn ho hu hGRH (le_of_not_ge h1500) h2000
  by_cases h3000 : Real.log n ≤ 3000
  · exact uniform_three_eleven_2000_3000 hn ho hu hGRH (le_of_not_ge h2000) h3000
  by_cases h4000 : Real.log n ≤ 4000
  · exact uniform_three_eleven_3000_4000 hn ho hu hGRH (le_of_not_ge h3000) h4000
  by_cases h5000 : Real.log n ≤ 5000
  · exact uniform_three_eleven_4000_5000 hn ho hu hGRH (le_of_not_ge h4000) h5000
  by_cases h6000 : Real.log n ≤ 6000
  · exact uniform_three_eleven_5000_6000 hn ho hu hGRH (le_of_not_ge h5000) h6000
  by_cases h7000 : Real.log n ≤ 7000
  · exact uniform_three_eleven_6000_7000 hn ho hu hGRH (le_of_not_ge h6000) h7000
  by_cases h8000 : Real.log n ≤ 8000
  · exact uniform_three_eleven_7000_8000 hn ho hu hGRH (le_of_not_ge h7000) h8000
  by_cases h9000 : Real.log n ≤ 9000
  · exact uniform_three_eleven_8000_9000 hn ho hu hGRH (le_of_not_ge h8000) h9000
  by_cases h10000 : Real.log n ≤ 10000
  · exact uniform_three_eleven_9000_10000 hn ho hu hGRH (le_of_not_ge h9000) h10000
  exact uniform_three_eleven_10000_10300 hn ho hu hGRH (le_of_not_ge h10000) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
