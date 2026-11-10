/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell164
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell170
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell174
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix26896

/-! # Uniform triples through logarithm 350 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with logarithm between 328 and 350
has a quarter-square rejecting prime. The Euler-prefix increment is obtained
analytically, and three independent endpoint checks cover the radius interval. -/
theorem quarter_uniform_328_350 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (328 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 350) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (164 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 175 := by
    dsimp only [r]; linarith only [hhi]
  have hr34 : (34 : ℝ) ≤ r := by linarith only [hr]
  have hr2 : (26896 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hP := quarter_euler_prefix_26896 hGRH.riemann hr2
  have hgap :
    quarterCenteredResidual r - 4 * ((2869 / 1000 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
    by_cases h1 : r ≤ 170
    · exact quarter_centered_gap_164_170 hr h1
    by_cases h2 : r ≤ 174
    · exact quarter_centered_gap_170_174 (le_of_not_ge h1) h2
    · exact quarter_centered_gap_174_175 (le_of_not_ge h2) hrU
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact quarter_uniform_of_residual_prefix hn ho hu hGRH hr34 hU hcut hP hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
