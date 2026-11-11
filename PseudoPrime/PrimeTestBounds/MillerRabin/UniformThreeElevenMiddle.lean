/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional10125to15188
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional15188to22782
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional22782to34173
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional34173to51260
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional51260to76890
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional76890to115335
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional115335to173003
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional173003to259505
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional259505to389258
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional389258to583887
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional583887to875831
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional875831to1313747
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional1313747to1970621
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional1970621to2955932
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenConditional2955932to4433898

/-! # Conditional uniform witness on the middle logarithmic range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the displayed Chebyshev lower bound at the selected radius,
any uniform Korselt triple with logarithm in `[10300, 4000000]` has a rejecting
prime within the three-elevenths cutoff. Independent interval certificates
cover the range. -/
theorem uniform_three_eleven_middle_at {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp :
      let r := (52223 / 100000 : ℝ) * Real.log n
      r ^ 2 - (1 / 12 : ℝ) * r * Real.log (r ^ 2) ^ 2 ≤ Chebyshev.psi (r ^ 2))
    (hL : (10300 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h15188 : Real.log n ≤ 15188
  · exact uniform_10125_15188_at hn ho hu hGRH hp (by linarith only [hL]) h15188
  by_cases h22782 : Real.log n ≤ 22782
  · exact uniform_15188_22782_at hn ho hu hGRH hp (le_of_not_ge h15188) h22782
  by_cases h34173 : Real.log n ≤ 34173
  · exact uniform_22782_34173_at hn ho hu hGRH hp (le_of_not_ge h22782) h34173
  by_cases h51260 : Real.log n ≤ 51260
  · exact uniform_34173_51260_at hn ho hu hGRH hp (le_of_not_ge h34173) h51260
  by_cases h76890 : Real.log n ≤ 76890
  · exact uniform_51260_76890_at hn ho hu hGRH hp (le_of_not_ge h51260) h76890
  by_cases h115335 : Real.log n ≤ 115335
  · exact uniform_76890_115335_at hn ho hu hGRH hp (le_of_not_ge h76890) h115335
  by_cases h173003 : Real.log n ≤ 173003
  · exact uniform_115335_173003_at hn ho hu hGRH hp (le_of_not_ge h115335) h173003
  by_cases h259505 : Real.log n ≤ 259505
  · exact uniform_173003_259505_at hn ho hu hGRH hp (le_of_not_ge h173003) h259505
  by_cases h389258 : Real.log n ≤ 389258
  · exact uniform_259505_389258_at hn ho hu hGRH hp (le_of_not_ge h259505) h389258
  by_cases h583887 : Real.log n ≤ 583887
  · exact uniform_389258_583887_at hn ho hu hGRH hp (le_of_not_ge h389258) h583887
  by_cases h875831 : Real.log n ≤ 875831
  · exact uniform_583887_875831_at hn ho hu hGRH hp (le_of_not_ge h583887) h875831
  by_cases h1313747 : Real.log n ≤ 1313747
  · exact uniform_875831_1313747_at hn ho hu hGRH hp (le_of_not_ge h875831) h1313747
  by_cases h1970621 : Real.log n ≤ 1970621
  · exact uniform_1313747_1970621_at hn ho hu hGRH hp (le_of_not_ge h1313747) h1970621
  by_cases h2955932 : Real.log n ≤ 2955932
  · exact uniform_1970621_2955932_at hn ho hu hGRH hp (le_of_not_ge h1970621) h2955932
  exact uniform_2955932_4433898_at hn ho hu hGRH hp (le_of_not_ge h2955932) (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin
