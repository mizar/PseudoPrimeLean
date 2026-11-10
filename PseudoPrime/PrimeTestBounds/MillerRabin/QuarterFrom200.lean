/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointPrimitive
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosed398375
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval3985
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval39875

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
  · by_cases h375 : Real.log n ≤ (3187 / 8 : ℝ)
    · exact quarter_uniform_8_398375 hn ho hu hGRH h375
    by_cases h5 : Real.log n ≤ (797 / 2 : ℝ)
    · exact quarter_uniform_398375_3985 hn ho hu hGRH (le_of_not_ge h375) h5
    exact quarter_uniform_3985_39875 hn ho hu hGRH (le_of_not_ge h5) hU
  · exact quarter_nonuniform_high hn ho hc hu hGRH hL

/-- Under GRH, an odd composite with logarithm between 68 and 398.75 and
Fermat subgroup index at most 33000 has a prime witness below one quarter of
its squared logarithm. The uniform case uses its interval bound; the other
case uses the small-index local subgroup bound. -/
theorem quarter_small_index_to39875 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (68 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (1595 / 4 : ℝ)) (hi : (PrimeTest.fermatSubgroup n).index ≤ 33000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hu : UniformKorseltTriple n
  · by_cases h375 : Real.log n ≤ (3187 / 8 : ℝ)
    · exact quarter_uniform_8_398375 hn ho hu hGRH h375
    by_cases h5 : Real.log n ≤ (797 / 2 : ℝ)
    · exact quarter_uniform_398375_3985 hn ho hu hGRH (le_of_not_ge h375) h5
    exact quarter_uniform_3985_39875 hn ho hu hGRH (le_of_not_ge h5) hU
  · exact quarter_common_index_le hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hi hu hGRH hL le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
