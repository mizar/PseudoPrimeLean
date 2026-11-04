/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTriangularCore
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveProfile

/-! # Adaptive Gaussian witness for all odd composites -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite above logarithmic scale two trillion has a
rejecting prime below the adaptive Gaussian cutoff. The triangular core handles
local and large-index cases, and the relative Gaussian profile handles triples. -/
theorem gaussianAdaptive_prime_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hC :
    gaussianTriangularRadius (Real.log n) ^ 2 =
      (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 := by
    exact Real.sq_sqrt (mul_nonneg (by norm_num only) (sq_nonneg _))
  have hlarge : 20000 ≤ n := by
    have h36 : 10 ^ 36 ≤ n :=
      decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
        (by
          norm_num only [Nat.cast_ofNat]
          linarith only [hL])
    exact (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  have hw :=
    exists_prime_triangularCore (gaussianTriangularCore (Real.log n) hL) hn ho hc hGRH le_rfl
      (fun hsf ht hK hU ↦ by
        obtain ⟨p, hp, hb, hr⟩ := adaptiveGaussian_witness_card ho hsf ht hK hU hlarge hGRH hL
        exact ⟨p, hp, by simpa only [gaussianTriangularCore, hC] using hb, hr⟩)
  simpa only [gaussianTriangularCore, hC] using hw

end PseudoPrime.PrimeTestBounds.MillerRabin
