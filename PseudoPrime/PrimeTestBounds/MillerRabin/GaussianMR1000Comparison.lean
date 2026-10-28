/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR1000WitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedIntervalSelection
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaReflectedComparison
public import PseudoPrime.Analysis.GaussianMR1000Comparison

/-! # Continuous comparisons for the sharp 1000-prefix Gaussian bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For L>=100, the existing sharper Gamma root exceeds 67L/125+13/2.
Complete the square in its negative test polynomial and use gap monotonicity.
This supplies a continuous separation from the new Gaussian radius cap. -/
theorem gammaSharpRoot_lower_affine {L : ℝ} (hL : 100 ≤ L) :
    (67 / 125 : ℝ) * L + 13 / 2 < gammaSharpRoot L := by
  let y := (67 / 125 : ℝ) * L + 13 / 2
  have hy : 0 < y := by
    dsimp only [y]; linarith only [hL]
  have hf :
    (86733 / 98800 : ℝ) * y ^ 2 - ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) * y -
        ((7 / 6 : ℝ) * L + 20475759 / 494000) <
      0 := by
    dsimp only [y]
    nlinarith only [sq_nonneg (L - 377063391625 / 1989892362)]
  have hid :
    gammaSharpGap L y * y =
      (86733 / 98800 : ℝ) * y ^ 2 - ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) * y -
        ((7 / 6 : ℝ) * L + 20475759 / 494000) := by
    dsimp only [gammaSharpGap]
    field_simp [hy.ne']
    ring
  by_contra hn
  have hg := gammaSharpGap_nonneg_of_root_le hL (le_of_not_gt hn)
  have hp := mul_nonneg hg hy.le
  nlinarith only [hid, hf, hp]

/-- For L>=132, the 1000-prefix Gaussian bound is strictly below G1.
Compare its affine radius cap with the certified affine Gamma-root lower bound;
the cutoff difference is positive throughout the real half-line. -/
theorem gaussian1000_lt_gammaSharp {L : ℝ} (hL : 132 ≤ L) :
    Analysis.gaussian1000Bound L < gammaSharpBound L := by
  have hu := Analysis.gaussian1000_cutoff_upper hL
  have hr := gammaSharpRoot_lower_affine (by linarith only [hL] : (100 : ℝ) ≤ L)
  have hp : (0 : ℝ) ≤ (67 / 125) * L + 13 / 2 := by linarith only [hL]
  have hs := (sq_lt_sq₀ hp (gammaSharpRoot_pos (by linarith only [hL])).le).mpr hr
  have hdiff :
    (6 / 5 : ℝ) * ((69 / 100) * L + 39 / 2) ^ 2 <
      (99 / 40 : ℝ) * ((67 / 125) * L + 13 / 2) ^ 2 := by
    nlinarith only [sq_nonneg (L - 132), hL]
  dsimp only [gammaSharpBound]
  nlinarith only [hu, hs, hdiff]

/-- For every n>1 with 132<=log n<=235, the 1000-prefix Gaussian candidate
is strictly below the existing public envelope. Use its exact Gamma/fixed
selection and the continuous comparisons, without sampled crossings. -/
theorem gaussian1000_lt_improved {n : ℕ} (hn : 1 < n) (hL : 132 ≤ Real.log n)
    (hU : Real.log n ≤ 235) :
    Analysis.gaussian1000Bound (Real.log n) < improvedSelectedEnvelope n := by
  rw [← improved_eq_selected hn]
  by_cases hS : Real.log n ≤ gammaSharpFixedSwitch
  · rw [improved_eq_sharp hn (by linarith only [hL]) hS]
    exact gaussian1000_lt_gammaSharp hL
  · rw [improved_eq_fixed35000 hn (le_of_not_ge hS) (by linarith only [hU])]
    exact Analysis.gaussian1000_lt_fixed (by linarith only [hL]) hU

/-- For L>=100, the reflected Gamma root exceeds 67L/125+63/10. Complete
the square in its negative test polynomial. This is an independent lower
bound for G2, not an inference from both candidates being below G1. -/
theorem gammaReflectedRoot_lower_affine {L : ℝ} (hL : 100 ≤ L) :
    (67 / 125 : ℝ) * L + 63 / 10 < gammaReflectedRoot L := by
  let y := (67 / 125 : ℝ) * L + 63 / 10
  have hy : 0 < y := by
    dsimp only [y]; linarith only [hL]
  have hf :
    (86733 / 98800 : ℝ) * y ^ 2 - ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) * y -
        ((7 / 6 : ℝ) * L + 58129633 / 2223000) <
      0 := by
    dsimp only [y]
    nlinarith only [sq_nonneg (L - 79758988850 / 994946181)]
  have hid :
    gammaReflectedGap L y * y =
      (86733 / 98800 : ℝ) * y ^ 2 - ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) * y -
        ((7 / 6 : ℝ) * L + 58129633 / 2223000) := by
    dsimp only [gammaReflectedGap]
    field_simp [hy.ne']
    ring
  by_contra hn
  have hg := gammaReflectedGap_nonneg_of_root_le hL (le_of_not_gt hn)
  have hp := mul_nonneg hg hy.le
  nlinarith only [hid, hf, hp]

/-- For L>=132, the 1000-prefix Gaussian bound is strictly below G2.
Compare the Gaussian affine radius cap with the independent reflected-root
lower bound; the rational cutoff difference is positive on the full half-line. -/
theorem gaussian1000_lt_gammaReflected {L : ℝ} (hL : 132 ≤ L) :
    Analysis.gaussian1000Bound L < gammaReflectedBound L := by
  have hu := Analysis.gaussian1000_cutoff_upper hL
  have hr := gammaReflectedRoot_lower_affine (by linarith only [hL] : (100 : ℝ) ≤ L)
  have hp : (0 : ℝ) ≤ (67 / 125) * L + 63 / 10 := by linarith only [hL]
  have hs := (sq_lt_sq₀ hp (gammaReflectedRoot_pos (by linarith only [hL])).le).mpr hr
  have hdiff :
    (6 / 5 : ℝ) * ((69 / 100) * L + 39 / 2) ^ 2 <
      (99 / 40 : ℝ) * ((67 / 125) * L + 63 / 10) ^ 2 := by
    nlinarith only [sq_nonneg (L - 132), hL]
  dsimp only [gammaReflectedBound]
  nlinarith only [hu, hs, hdiff]

end PseudoPrime.PrimeTestBounds.MillerRabin
