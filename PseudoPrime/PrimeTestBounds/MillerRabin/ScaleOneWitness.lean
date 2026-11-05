/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneGaussian
public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneReduction

/-! # Adaptive Gaussian all-factor reduction at scale 25000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive Gaussian coefficient exceeds the square-radius floor required by
the local and large-index reductions. Its positive correction terms preserve this bound. -/
theorem scaleOne_gaussian_floor (L : ℝ) (hL : 25000 ≤ L) :
    (5313 / 10000 : ℝ) ^ 2 ≤ (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1 : 0 ≤ (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  have ha : (3666849 / 10000000 : ℝ) ≤ adaptiveGaussianA L := by
    dsimp only [adaptiveGaussianA]
    apply (le_div_iff₀ (by norm_num only)).2
    linarith only [h1, h2]
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3666849 / 10000000) ha 2
  nlinarith only [hs]

/-- Under GRH above scale 25000, the adaptive Gaussian cutoff has a rejecting prime
for every odd composite once the large-index branch is supplied. The local and uniform
three-factor branches follow from their actual witness theorems. -/
theorem scaleOne_reduce_large {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (25000 : ℝ) ≤ Real.log n)
    (hlarge :
      1000000000000 ≤ (PrimeTest.fermatSubgroup n).index →
        ∃ p : ℕ,
          p.Prime ∧
            (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
            ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply scaleOne_reduce_branches hn ho hc hGRH hL (scaleOne_gaussian_floor _ hL) hlarge
  intro hsf ht hK hU
  have h36 : 10 ^ 36 ≤ n :=
    decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [hL])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  exact scaleOne_gaussian_card ho hsf ht hK hU hnlarge hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
