/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
import Mathlib.Tactic.Linarith

/-! # Tail-free K196 zero upper bound from its coefficient check -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The K196 coefficient check removes the signed Euler tail from the
three-pair zero upper bound. The rational pole certificate supplies the
explicit saving of `543 / 40`. -/
public theorem k196_zero_upper {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ}
    (hX : 0 < X) (hlog : 75 / 2 ≤ Real.log X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑' ρ : ℂ, HighGaussianKernel.k196.zeroTerm a X ρ).re -
        (∑' ρ : ℂ, HighGaussianKernel.k196.zeroTerm b X ρ).re -
        (∑' ρ : ℂ, HighGaussianKernel.k196.zeroTerm c X ρ).re ≤
      3 / 8 * Real.log n - 543 / 40 + 3 * HighGaussianKernel.k196.xiMass.re := by
  intro a b c
  have h := high_gaussian_zero_upper_of_pass .k196 hn ho hu hprod hp hq hr hg hX hpass
  dsimp only at h
  have ht :=
    high_k196_euler_tail_nonpos a b c hX hlog (k196_coeff_nonpos_of_check k196_mass_sign_check)
  have hw : ((22625 / 10000 : ℚ) : ℝ) < (HighGaussianKernel.k196.massPole : ℝ) :=
    Rat.cast_lt.mpr gaussian_k196_mass_pole_bounds.1
  simp only [Rat.cast_div, Rat.cast_ofNat] at hw
  linarith only [h, ht, hw]

end PseudoPrime.PrimeTestBounds.MillerRabin
