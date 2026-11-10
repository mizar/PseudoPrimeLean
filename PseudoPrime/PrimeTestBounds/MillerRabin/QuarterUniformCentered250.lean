/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell34
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell70
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell110

/-! # Uniform triples through logarithm 250 by centered Abel comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with logarithm between 68 and 250
has a rejecting prime below one quarter of the squared logarithm. The three
independent endpoint certificates cover the entire radius interval. -/
theorem quarter_uniform_68_250 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (68 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 250) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (34 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 125 := by
    dsimp only [r]; linarith only [hhi]
  have hgap :
    quarterCenteredResidual r ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
    by_cases h1 : r ≤ 70
    · exact quarter_centered_gap_34_70 hr h1
    by_cases h2 : r ≤ 110
    · exact quarter_centered_gap_70_110 (le_of_not_ge h1) h2
    · exact quarter_centered_gap_110_125 (le_of_not_ge h2) hrU
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact quarter_uniform_of_residual hn ho hu hGRH hr hU hcut hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
