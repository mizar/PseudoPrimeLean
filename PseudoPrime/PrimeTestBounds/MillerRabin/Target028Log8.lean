/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Through1133
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028From106
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square115
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028UniformFirst
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square13
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square25
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square425
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square100
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square63
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square813
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine31Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine37Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine43Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine47Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine59Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine61Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028AnchorInput
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupInput
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SummedInput
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SummedHighInput
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two569Input
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoFinalInput
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028UniformCells

/-! # Logarithmic-scale witness for the 0.28 cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite of logarithmic scale at least eight has a
rejecting prime below the 0.28 cutoff. The proof combines the finite low and
intermediate ranges, the uniform Korselt cells, and the high-scale bound. -/
theorem exists_prime_reject_028_log8 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : Real.log n ≤ 1133 / 100
  · exact exists_prime_reject_028_through1133 hn ho hc hGRH hL hsmall
  by_cases hlarge : (106 : ℝ) ≤ Real.log n
  · exact exists_prime_reject_028_from106 hn ho hc hGRH hlarge
  by_cases hu : UniformKorseltTriple n
  · by_cases hlarge : (100 : ℝ) ≤ Real.log n
    · exact target028_uniform_high_witness hn ho hu hGRH hlarge
    by_cases hlocal : Real.log n ≤ 30
    · exact uniformKorselt_reject_028_8_30 hn ho hu hGRH hL hlocal
    by_cases hfirst : Real.log n ≤ 30461 / 1000
    · exact target028_uniform_first_witness hn ho hu hGRH (le_of_not_ge hlocal) hfirst
    exact
      target028_uniform_cells_30461_100 hn ho hu hGRH (le_of_not_ge hfirst)
        (by linarith only [hlarge])
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · exact exists_prime_reject_028_four_factors hn ho hc h4 hGRH
  by_cases hsf : Squarefree n
  · by_cases h3 : n.primeFactors.card = 3
    · exact exists_prime_reject_028_nonuniform_three hn ho hsf h3 hu hGRH
    by_cases hU : Real.log n ≤ 119 / 10
    · exact target028_squarefree_fine31 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hsmall) hU
    by_cases hU37 : Real.log n ≤ 12451 / 1000
    · exact target028_squarefree_fine37 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU) hU37
    by_cases hU43 : Real.log n ≤ 13324 / 1000
    · exact target028_squarefree_fine43 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU37) hU43
    by_cases hU47 : Real.log n ≤ 13777 / 1000
    · exact target028_squarefree_fine47 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU43) hU47
    by_cases hU53 : Real.log n ≤ 14518 / 1000
    · exact target028_squarefree_fine53 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU47) hU53
    by_cases hU59 : Real.log n ≤ 14800 / 1000
    · exact target028_squarefree_fine59 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU53) hU59
    by_cases hU61 : Real.log n ≤ 15153 / 1000
    · exact target028_squarefree_fine61 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU59) hU61
    by_cases hUa : Real.log n ≤ 71609 / 1000
    · exact target028_squarefree_anchor hn ho hc hsf h4 h3 hGRH (le_of_not_ge hU61) hUa
    by_cases hUg : Real.log n ≤ 85926 / 1000
    · exact target028_squarefree_group hn ho hc hsf h4 h3 hGRH (le_of_not_ge hUa) hUg
    by_cases hUs : Real.log n ≤ 88181 / 1000
    · exact target028_squarefree_summed hn ho hc hsf h4 h3 hGRH (le_of_not_ge hUg) hUs
    by_cases hUsh : Real.log n ≤ 96708 / 1000
    · exact target028_squarefree_summed_high hn ho hc hsf h4 h3 hGRH (le_of_not_ge hUs) hUsh
    by_cases hUt : Real.log n ≤ 99677 / 1000
    · exact target028_squarefree_two569 hn ho hc hsf h4 h3 hGRH (le_of_not_ge hUsh) hUt
    exact
      target028_squarefree_final hn ho hc hsf h4 h3 hGRH (le_of_not_ge hUt) (le_of_not_ge hlarge)
  have hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n := by
    by_contra h
    apply hsf
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hd
    exact h ⟨p, hp, (pow_two p).symm ▸ hd⟩
  obtain ⟨p, hp, hd⟩ := hsq
  by_cases hU : Real.log n ≤ 13
  · exact exists_prime_reject_028_square_1133_13 hn ho hp hd hGRH.riemann (le_of_not_ge hsmall) hU
  by_cases hU25 : Real.log n ≤ 25
  · exact exists_prime_reject_028_square_13_25 hn ho hp hd (le_of_not_ge hU) hU25
  by_cases hU28 : Real.log n ≤ 28
  · exact exists_prime_reject_028_square_25_28 hn ho hp hd (le_of_not_ge hU25) hU28
  by_cases hU425 : Real.log n ≤ 85 / 2
  · exact exists_prime_reject_028_square_28_425 hn ho hp hd (le_of_not_ge hU28) hU425
  by_cases hU63 : Real.log n ≤ 63
  · exact exists_prime_reject_028_square_425_63 hn ho hp hd (le_of_not_ge hU425) hU63
  by_cases hU805 : Real.log n ≤ 161 / 2
  · exact exists_prime_reject_028_square_63_805 hn ho hp hd hGRH.riemann (le_of_not_ge hU63) hU805
  by_cases h813 : (813 / 10 : ℝ) ≤ Real.log n
  · exact exists_prime_reject_028_square_813_106 hn ho hp hd h813 (le_of_not_ge hlarge)
  exact exists_prime_reject_028_square_805_813 hn ho hp hd (le_of_not_ge hU805) (le_of_not_ge h813)

end PseudoPrime.PrimeTestBounds.MillerRabin
