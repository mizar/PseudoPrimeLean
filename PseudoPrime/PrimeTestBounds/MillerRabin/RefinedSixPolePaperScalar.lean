/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperConstants

/-! # Explicit residual in the refined three-prime scalar inequality -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized residual at logarithmic size `L` and root scale `R`. It combines
the conductor, dual Euler, Gamma, zero-mass, principal variation and endpoint costs;
the linear and square-root leading terms are kept outside for the scalar certificate. -/
noncomputable def refinedPaperResidual (L R : ℝ) : ℝ :=
  (2 * L) *
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
            (R ^ 2) ^ (-(27 / 25 : ℝ)) *
            ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
        5 * (27 / 25 : ℝ) ^ 5 +
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
          (R ^ 2) ^ (-(27 / 25 : ℝ)) *
          (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
            (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) -
      (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    5 *
      ((231 / 5000 : ℝ) * (6889 / 2700) +
        ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
            ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
          R) +
    4 * |refinedWeightDeriv 1| * ((231 / 5000 : ℝ) * R + (1839 / 1000 : ℝ) * (2 * Real.log R) + 2) /
      R +
    4 * refinedWeight 1 * ((231 / 2500 : ℝ) * (7 / 3) / Real.sqrt R + (1839 / 1000 : ℝ) / R)

/-- For `R ≥ 522`, the explicit character-gap inequality implies the paper scalar
inequality with its exact rational leading coefficients. Compare the kernel main mass
and square-root boundary coefficient with their certified strict bounds. -/
theorem refined_scalar_from_gap {L R : ℝ} (hR : 522 ≤ R)
    (hgap :
      R *
            (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
              (refinedSixPoleKernel.function (1 / 2)).re) -
          5 *
            ((231 / 5000 : ℝ) * (6889 / 2700) +
              ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
                  ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
                R) -
          4 * |refinedWeightDeriv 1| *
              ((231 / 5000 : ℝ) * R + (1839 / 1000 : ℝ) * (2 * Real.log R) + 2) /
            R -
          4 * refinedWeight 1 *
            (((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt R +
              (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt R +
              (1839 / 1000 : ℝ) / R) <
        (2 * L) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                (R ^ 2) ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
            5 * (27 / 25 : ℝ) ^ 5 +
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
              (R ^ 2) ^ (-(27 / 25 : ℝ)) *
              (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
                (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
            (3 / 8 : ℝ) * L -
          (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) :
    (27 / 25 : ℝ) ^ 5 * (24439 / 50000) * R <
      (3 / 8 : ℝ) * L + (27 / 25 : ℝ) ^ 5 * (53 / 500) * Real.sqrt R +
        refinedPaperResidual L R := by
  have hR0 : 0 < R := (by norm_num only : (0 : ℝ) < 522).trans_le hR
  have hd := mul_lt_mul_of_pos_right refined_paper_delta_lower hR0
  have hv := mul_le_mul_of_nonneg_right refined_paper_sqrt_cost.le (Real.sqrt_nonneg R)
  dsimp only [refinedPaperResidual]
  ring_nf at hd hv hgap ⊢
  linarith only [hd, hv, hgap]

/-- Under GRH, a uniform three-prime Korselt product for which all prime bases at
most `R²` pass must satisfy the explicit scalar inequality. Combine the paper-width
principal comparison with the certified leading constants. -/
theorem refined_pair_scalar_necessary {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {R : ℝ} (hR : 522 ≤ R)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    (27 / 25 : ℝ) ^ 5 * (24439 / 50000) * R <
      (3 / 8 : ℝ) * Real.log n + (27 / 25 : ℝ) ^ 5 * (53 / 500) * Real.sqrt R +
        refinedPaperResidual (Real.log n) R := by
  apply refined_scalar_from_gap hR
  exact
    refined_pair_paper_necessary hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
      hrK hvq hvr hR hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
