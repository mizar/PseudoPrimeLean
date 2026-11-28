/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointPrimitive
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformTo663
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Quarter-bound witness between logarithmic scales 200 and 398.75 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with logarithm between 200 and 398.75 has a
prime Miller–Rabin witness bounded by one quarter of its squared logarithm.
The uniform Korselt and nonuniform cases are supplied by their independent
witness bounds. -/
theorem quarter_from200_to39875 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (200 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (1595 / 4 : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · obtain ⟨p, hp, hb, hf⟩ :=
      uniform_witness_8_to663 hn ho hu hGRH ⟨by linarith only [hL], by linarith only [hU]⟩
    rw [show (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2 by ring] at hb
    exact ⟨p, hp, hb, hf⟩
  · exact quarter_nonuniform_high hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
