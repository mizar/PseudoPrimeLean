/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoFactorUniform409
public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeFactorLow4136
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHigh4136
public import PseudoPrime.PrimeTestBounds.MillerRabin.Small4136

/-! # Global Miller–Rabin max witness bound with coefficient 0.4136 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite `n > 1` has a rejecting prime at most
`max 2 ((517/1250) * (log n)²)`. The proof joins the small-input classification, the
certified two-factor and three-factor middle ranges, and the high Gaussian bound. -/
theorem exists_prime_reject_max_4136 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ max 2 ((517 / 1250 : ℝ) * (Real.log n) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hhigh : (3461 / 10 : ℝ) ≤ Real.log n
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_high_4136 hn ho hc hGRH hhigh
    exact ⟨r, hr, hb.trans (le_max_right _ _), hf⟩
  by_cases hsmall : Real.log n < 8
  · exact exists_prime_reject_small_4136 hn ho hc hsmall
  have hlo : (8 : ℝ) ≤ Real.log n := le_of_not_gt hsmall
  have hhi : Real.log n ≤ (3461 / 10 : ℝ) := le_of_not_ge hhigh
  by_cases hthree : 3 ≤ ArithmeticFunction.cardFactors n
  · by_cases hmid : Real.log n ≤ (25 / 2 : ℝ)
    · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_three_factors_low hn ho hthree hlo hmid
      exact ⟨r, hr, hb.trans (le_max_right _ _), hf⟩
    · obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_three_factors_4136 hn ho hGRH hthree (le_of_not_ge hmid) hhi
      exact ⟨r, hr, hb.trans (le_max_right _ _), hf⟩
  · have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
    have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
      hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
    have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
      Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
    have hkeq : ArithmeticFunction.cardFactors n = 2 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hthree)) hk2
    have hhi350 : Real.log n ≤ (350 : ℝ) := by linarith only [hhi]
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_two_factors_409 hn ho hGRH hkeq hlo hhi350
    have hcoeff : (409 / 1000 : ℝ) * (Real.log n) ^ 2 ≤ (517 / 1250 : ℝ) * (Real.log n) ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
    exact ⟨r, hr, (hb.trans hcoeff).trans (le_max_right _ _), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
