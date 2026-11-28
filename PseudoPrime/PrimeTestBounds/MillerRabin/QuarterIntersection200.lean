/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeRange200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareRange200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformTo663
import Mathlib.Tactic.Ring
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFactorDispatch

/-! # Common quarter-bound range for all factor types -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm between 8 and 200 has a
quarter-square rejecting prime. The factor classification combines the type ranges. -/
theorem quarter_all_8_200 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 200) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply quarter_of_factor_cases hn ho hc hGRH
  · intro hu
    obtain ⟨p, hp, hb, hf⟩ := uniform_witness_8_to663 hn ho hu hGRH ⟨hL, by linarith only [hU]⟩
    rw [show (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2 by ring] at hb
    exact ⟨p, hp, hb, hf⟩
  · intro p hp hd
    exact quarter_square_8_200 hn ho hp hd hGRH hL hU
  · intro p q hp hq hpq hprod
    exact quarter_semiprime_8_200 hn ho hp hq hpq hprod hGRH hL hU
  · exact le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
