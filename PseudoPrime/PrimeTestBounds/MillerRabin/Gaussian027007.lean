/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEndpointCert

/-! # The Gaussian and quadratic 027007 prime-base criteria -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked finite interval closes the K186 budget used in the
uniform Korselt triple case. -/
private theorem k186_finite_budget : K186FiniteBudget := by
  exact k186_budget_of_gap_cells k186_gap_left_checked k186_gap_right_checked k186_gap_curv_checked

/-- Under GRH, an odd input greater than one is prime exactly when all
prime bases at most the Gaussian cutoff pass. Join the uniform ranges
before applying the existing nonuniform and low-range criteria. -/
theorem prime_millerRabin_027007_gaussian_criterion
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact gaussian_criterion_of_finite_budget k186_finite_budget hn ho hGRH

/-- Under GRH, the same criterion holds with the larger quadratic
cutoff ( max(2,(9090/33659)(log n)^2) ). -/
theorem prime_millerRabin_027007_criterion
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ max 2 ((9090 / 33659 : ℝ) * Real.log n ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact criterion_027007_of_finite_budget k186_finite_budget hn ho hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
