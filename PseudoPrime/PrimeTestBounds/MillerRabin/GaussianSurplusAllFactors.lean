/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusReduction

/-! # Surplus Gaussian all-factor reductions -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH from scale 280, reduce the 35000-prefix cutoff to the large-index
branch. The local and uniform three-factor cases use actual witness theorems. -/
theorem jointSurplus_reduce35000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (280 : ℝ) ≤ Real.log n)
    (hlarge :
      1000000000000 ≤ (PrimeTest.fermatSubgroup n).index →
        ∃ p : ℕ,
          p.Prime ∧
            (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 130 30 (Real.log n)) ^ 2 ∧
            ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 130 30 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    jointSurplus_reduce_branches hn ho hc hGRH hL (rho := 130) (R := 30) (by norm_num only)
      (by norm_num only) hlarge
  intro hsf ht hK hU
  have h36 : 10 ^ 36 ≤ n :=
    decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [hL])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  exact jointSurplus_three35000 hn ho hsf ht hK hU hnlarge hGRH

/-- The 50000-prefix cutoff has the same all-factor reduction; its large-index
hypothesis is discharged separately on the certified range. -/
theorem jointSurplus_reduce50000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (280 : ℝ) ≤ Real.log n)
    (hlarge :
      1000000000000 ≤ (PrimeTest.fermatSubgroup n).index →
        ∃ p : ℕ,
          p.Prime ∧
            (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 155 29 (Real.log n)) ^ 2 ∧
            ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 155 29 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    jointSurplus_reduce_branches hn ho hc hGRH hL (rho := 155) (R := 29) (by norm_num only)
      (by norm_num only) hlarge
  intro hsf ht hK hU
  have h36 : 10 ^ 36 ≤ n :=
    decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [hL])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  exact jointSurplus_three50000 hn ho hsf ht hK hU hnlarge hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
