/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaLinearCutoffBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianIndexClassification

/-! # Complete all-input Gamma index-100 witness bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm at least 330 has a prime
strong-MR witness below the Gamma index-100 cutoff. The subgroup-index split
and its residual uniform Korselt triple are discharged internally. -/
theorem exists_prime_witness_le_gammaIndex100 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  let : NeZero n := ⟨hn0⟩
  have hn142 := gammaIndex100_log_ge_decimal142 hL
  have hnlarge : 20000 ≤ n := by
    have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
    exact h20000.trans hn142
  rcases gamma100_witness_or_Korselt_oddComposite_GRH hnOdd hcomp hGRH hL with hw | htriple
  · exact hw
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    exact exists_prime_gamma100_korseltCard_GRH hnOdd hsf hc hK hU hnlarge hGRH hL

/-- The least prime rejecting strong MR inherits the Gamma index-100 cutoff
for every odd composite at logarithmic scale at least 330. -/
theorem exists_least_prime_witness_le_gammaIndex100 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ := exists_prime_witness_le_gammaIndex100 hnOdd hcomp hGRH hL
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, (Nat.find_spec hex).2,
      fun q hq hqReject ↦ Nat.find_min' hex ⟨hq, hqReject⟩⟩

/-- The least prime rejecting strong MR is bounded by the two-prefix `U₁₀₀`
envelope for every odd composite with logarithm at least 240. -/
theorem exists_leastWitness_le_gammaIndex100PrefixUpper {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_le_gammaIndex100PrefixUpper hnOdd hcomp hGRH hL
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, (Nat.find_spec hex).2,
      fun q hq hqReject ↦ Nat.find_min' hex ⟨hq, hqReject⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
