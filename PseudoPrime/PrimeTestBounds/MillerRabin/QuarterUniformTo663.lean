/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLowRange
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniform556
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniform532
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness574
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness576
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness584
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness600
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness626
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness628
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeWitness663

/-! # Quarter-square witness bound for uniform triples through logarithm 663 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, odd uniform Korselt triples in the closed log interval [533,556]
have a prime witness bounded by the squared half-logarithm. The existing square
recovery results meet at log 540. -/
private theorem uniform_witness_533_to556 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 533 556) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [show (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2 by ring]
  by_cases h : Real.log n ≤ 540
  · exact quarter_uniform_532_540 hn ho hu hGRH ((by norm_num only : (532 : ℝ) ≤ 533).trans hL.1) h
  exact quarter_uniform_540_556 hn ho hu hGRH (le_of_not_ge h) hL.2

/-- Under GRH an odd uniform Korselt triple with logarithm in [8, 663] has
a prime rejecting Miller–Rabin base at most the square of its half-logarithm.
The consecutive interval bounds share endpoints and apply only to uniform triples. -/
theorem uniform_witness_8_to663 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 8 663) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h533 : Real.log n ≤ 533
  · exact uniform_witness_through533 hn ho hu hGRH h533
  by_cases h556 : Real.log n ≤ 556
  · exact uniform_witness_533_to556 hn ho hu hGRH ⟨le_of_not_ge h533, h556⟩
  by_cases h570 : Real.log n ≤ 570
  · exact uniform_witness_570 hn ho hu hGRH (le_of_not_ge h556) h570
  by_cases h574 : Real.log n ≤ 574
  · exact uniform_witness_574 hn ho hu hGRH (le_of_not_ge h570) h574
  by_cases h576 : Real.log n ≤ 576
  · exact uniform_witness_576 hn ho hu hGRH (le_of_not_ge h574) h576
  by_cases h584 : Real.log n ≤ 584
  · exact uniform_witness_584 hn ho hu hGRH (le_of_not_ge h576) h584
  by_cases h600 : Real.log n ≤ 600
  · exact uniform_witness_600 hn ho hu hGRH (le_of_not_ge h584) h600
  by_cases h626 : Real.log n ≤ 626
  · exact uniform_witness_626 hn ho hu hGRH (le_of_not_ge h600) h626
  by_cases h628 : Real.log n ≤ 628
  · exact uniform_witness_628 hn ho hu hGRH (le_of_not_ge h626) h628
  by_cases h632 : Real.log n ≤ 632
  · exact uniform_witness_632 hn ho hu hGRH (le_of_not_ge h628) h632
  by_cases h644 : Real.log n ≤ 644
  · exact uniform_witness_644 hn ho hu hGRH (le_of_not_ge h632) h644
  by_cases h656 : Real.log n ≤ 656
  · exact uniform_witness_656 hn ho hu hGRH (le_of_not_ge h644) h656
  exact uniform_witness_656_to663 hn ho hu hGRH (le_of_not_ge h656) hL.2

end PseudoPrime.PrimeTestBounds.MillerRabin
