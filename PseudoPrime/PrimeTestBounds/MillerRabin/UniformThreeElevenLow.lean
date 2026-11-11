/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosed398375
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval3985
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval39875
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval3988
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite3988400
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite400410
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite410420
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite420430
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite430440
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite440450
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite450460
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite460465
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
  by_cases h398375 : Real.log n ≤ (3187 / 8 : ℝ)
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_8_398375 hn ho hu hGRH h398375
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h3985 : Real.log n ≤ (797 / 2 : ℝ)
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_398375_3985 hn ho hu hGRH (le_of_not_ge h398375) h3985
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h39875 : Real.log n ≤ (1595 / 4 : ℝ)
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_3985_39875 hn ho hu hGRH (le_of_not_ge h3985) h39875
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h3988 : Real.log n ≤ (1994 / 5 : ℝ)
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_39875_3988 hn ho hu hGRH (le_of_not_ge h39875) h3988
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h400 : Real.log n ≤ 400
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_3988_400 hn ho hu hGRH (le_of_not_ge h3988) h400
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h410 : Real.log n ≤ 410
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_400_410 hn ho hu hGRH (le_of_not_ge h400) h410
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h420 : Real.log n ≤ 420
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_410_420 hn ho hu hGRH (le_of_not_ge h410) h420
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h430 : Real.log n ≤ 430
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_420_430 hn ho hu hGRH (le_of_not_ge h420) h430
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h440 : Real.log n ≤ 440
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_430_440 hn ho hu hGRH (le_of_not_ge h430) h440
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h450 : Real.log n ≤ 450
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_440_450 hn ho hu hGRH (le_of_not_ge h440) h450
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h460 : Real.log n ≤ 460
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_450_460 hn ho hu hGRH (le_of_not_ge h450) h460
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h465 : Real.log n ≤ 465
  · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_460_465 hn ho hu hGRH (le_of_not_ge h460) h465
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  by_cases h700 : Real.log n ≤ 700
  · exact uniform_three_eleven_465_700 hn ho hu hGRH (le_of_not_ge h465) h700
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
