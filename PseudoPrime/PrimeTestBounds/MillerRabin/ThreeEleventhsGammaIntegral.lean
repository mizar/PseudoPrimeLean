/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaRemainder
public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsRemainder
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaIntegral

/-! # Three-elevenths bound from the Gamma-remainder integral -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the Euler-normalized Riemann–von Mangoldt identity and the
Gamma-remainder integral identity imply the least-prime `3/11` witness
bound for every odd composite. The integral bound, Backlund phase estimate,
coarse zero count and classification are discharged internally. -/
theorem three_eleven_least_of_gamma_integral {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hV : AnalyticNumberTheory.RiemannZeta.EulerRiemannVonMangoldt)
    (hI : AnalyticNumberTheory.RiemannZeta.BacklundGammaRemainderIdentity) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_gamma_remainder hn ho hc hGRH hV
      (AnalyticNumberTheory.RiemannZeta.gamma_remainder_bounds_of_integral hI)

end PseudoPrime.PrimeTestBounds.MillerRabin
