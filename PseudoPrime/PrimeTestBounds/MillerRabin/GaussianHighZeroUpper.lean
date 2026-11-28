/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighThreeMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPairCharacterData
import PseudoPrime.AnalyticNumberTheory.GRH.QuasiRiemannConsequences
import Mathlib.Tactic.Linarith

/-! # Signed zero upper bound under uniform Korselt Miller–Rabin passage -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed zero contribution of the three Jacobi pair characters is
bounded by (H17) when every prime below the tested cutoff passes Miller–Rabin. -/
public theorem high_gaussian_zero_upper_of_pass (K : HighGaussianKernel) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑' ρ : ℂ, K.zeroTerm a X ρ).re - (∑' ρ : ℂ, K.zeroTerm b X ρ).re -
        (∑' ρ : ℂ, K.zeroTerm c X ρ).re ≤
      3 / 8 * Real.log n - 6 * (K.massPole : ℝ) + 3 * K.xiMass.re +
        (∑' m : { m : ℕ // ⌊X⌋₊ < m },
          ArithmeticFunction.vonMangoldt m.val *
            (3 - ((a m.val).re + (b m.val).re + (c m.val).re)) *
            (m.val : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
            (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) (Real.log m.val)) := by
  intro a b c
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  have hm := high_gaussian_three_mass K hprod a b c hpq hpr hqr ha hb hc hg hg.riemann hX hsmall
  have hterm {d : ℕ} [NeZero d] (hd : 2 ≤ d) {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) : -(∑' ρ : ℂ, K.zeroTerm χ X ρ).re ≤ ∑' ρ : ℂ, ‖K.zeroTerm χ X ρ‖ :=
    (neg_le_abs _).trans
      ((Complex.abs_re_le_norm _).trans
        (norm_tsum_le_tsum_norm (high_gaussian_zero_summable K hd hg hprim hne hX).norm))
  linarith only [hm, hterm hpq ha.1 ha.2.1, hterm hpr hb.1 hb.2.1, hterm hqr hc.1 hc.2.1]

end PseudoPrime.PrimeTestBounds.MillerRabin
