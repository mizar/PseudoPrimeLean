/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedGaussianBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeProfileBounds

/-! # First all-factor reduced-contour MR witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm at least `2 * 10 ^ 8` has a
rejecting prime at most `(39 / 100) * log n ^ 2`. The reduced contour core
covers the local and large-index branches; the Gaussian certificate covers triples. -/
theorem prime_witness_reduced039 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (200000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (39 / 100 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reducedCore reducedProfile039 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness reducedGaussian039 ho hsf ht hK hU hGRH hL

/-- Under GRH, every odd composite above logarithmic scale `5 * 10 ^ 8` has a
rejecting prime below coefficient `161 / 500` times the squared logarithm.
The reduced triangular and Gaussian certificates cover the full classification. -/
theorem prime_witness_reduced0322 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (500000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (161 / 500 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reducedCore reducedProfile0322 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness reducedGaussian0322 ho hsf ht hK hU hGRH hL

/-- Under GRH, every odd composite above logarithmic scale `10 ^ 9` has a
rejecting prime below coefficient `3 / 10` times the squared logarithm.
The reduced triangular and Gaussian certificates cover the full classification. -/
theorem prime_witness_reduced030 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reducedCore reducedProfile030 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness reducedGaussian030 ho hsf ht hK hU hGRH hL

/-- Under GRH, every odd composite above logarithmic scale `5 * 10 ^ 9` has a
rejecting prime below coefficient `71 / 250` times the squared logarithm.
The reduced triangular and Gaussian certificates cover the full classification. -/
theorem prime_witness_reduced0284 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (71 / 250 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reducedCore reducedProfile0284 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness reducedGaussian0284 ho hsf ht hK hU hGRH hL
/-- Under GRH, every odd composite above logarithmic scale `3 * 10 ^ 10` has a
rejecting prime below coefficient `28237 / 100000` times the squared logarithm.
The reduced triangular and Gaussian certificates cover the full classification. -/
theorem prime_witness_reduced028237 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (30000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (28237 / 100000 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reducedCore reducedProfile028237 hn ho hc hGRH hL
  intro hsf ht hK hU
  have h36 : 10 ^ 36 ≤ n := decimal_le_of_log_upper (Nat.zero_lt_of_lt hn) (by
    norm_num only [Nat.cast_ofNat]
    linarith only [hL])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  exact gaussianProfile_witness_card gaussianRelativeCommon ho hsf ht hK hU hnlarge hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
