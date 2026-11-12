/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsGammaIntegral
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaFiniteLimit
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaCellIntegral

/-! # Three-elevenths witnesses from Gamma integral identities -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the Euler-normalized zero-count identity, the complex
Gamma integral representation yields the least-prime `3/11` witness bound
for every odd composite. The integral estimates and classification are
discharged by the preceding bridge. -/
theorem three_eleven_least_of_gamma_complex {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hV : AnalyticNumberTheory.RiemannZeta.EulerRiemannVonMangoldt)
    (hI : AnalyticNumberTheory.RiemannZeta.BacklundGammaComplexIdentity) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_gamma_integral hn ho hc hGRH hV
      (AnalyticNumberTheory.RiemannZeta.gamma_remainder_identity_of_complex hI)

/-- Under GRH, the Euler-normalized zero-count identity and the imaginary
cell limit imply the least-prime `3/11` witness bound for odd composites.
The real Stirling constant is unnecessary for this conditional conclusion. -/
theorem three_eleven_least_of_gamma_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hV : AnalyticNumberTheory.RiemannZeta.EulerRiemannVonMangoldt)
    (hI : AnalyticNumberTheory.RiemannZeta.BacklundGammaCellImaginaryLimit) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_gamma_integral hn ho hc hGRH hV
      (AnalyticNumberTheory.RiemannZeta.gamma_remainder_identity_of_cells hI)

/-- Under GRH, the normalized zero-count identity and the finite Gamma
identity imply the least-prime `3/11` witness bound for odd composites.
The limiting and real-constant steps are discharged internally. -/
theorem three_eleven_least_of_gamma_finite {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hV : AnalyticNumberTheory.RiemannZeta.EulerRiemannVonMangoldt)
    (hI : AnalyticNumberTheory.RiemannZeta.BacklundGammaFiniteIdentity) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_gamma_complex hn ho hc hGRH hV
      (AnalyticNumberTheory.RiemannZeta.gamma_complex_identity_of_finite hI)

end PseudoPrime.PrimeTestBounds.MillerRabin
