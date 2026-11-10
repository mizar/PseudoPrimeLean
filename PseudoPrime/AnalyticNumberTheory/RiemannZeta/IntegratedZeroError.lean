/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroSplitBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound

/-! # Integrated Chebyshev error from zero sums

Combine the finite-ledger zero split with the explicit-formula limit.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, for `1 < a < b` and `T ≥ 0`, bound the centered integrated
Chebyshev difference using the low reciprocal zero sum and a uniform bound
`C` for the high inverse-square sums in every finite contour ledger. The
trivial-zero correction contributes at most one. The high-tail bound remains
an explicit hypothesis. -/
theorem psi1_error_of_zero_split (hRH : RiemannHypothesis) {T a b C : ℝ} (hT : 0 ≤ T) (ha : 1 < a)
    (hab : a < b)
    (hC :
      ∀ m : ℕ,
        (∑
            ρ ∈
              ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                        (unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0)).filter
                (fun ρ ↦ ¬|ρ.im| ≤ T),
            (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
          C) :
    |Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a - (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a)| ≤
      (b - a) *
          (Real.sqrt b * zeroReciprocalSum T + (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C) +
        1 := by
  classical
  let S : ℕ → Finset ℂ := fun m ↦
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let f : ℂ → ℂ := fun ρ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
  let B := Real.sqrt b * zeroReciprocalSum T + (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C
  have hw : 0 < b - a := sub_pos.mpr hab
  have hbound (m : ℕ) : ‖∑ ρ ∈ S m, f ρ‖ ≤ (b - a) * B := by
    have hh :=
      split_zero_sum_bound hRH (S m)
        (fun ρ hρ ↦ (mem_riemannZetaZerosInAnyRectangle_iff.mp (Finset.mem_filter.mp hρ).1).2)
        (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2) hT (zero_lt_one.trans ha) hab (hC m)
    simpa only [f, B, mul_comm] using (div_le_iff₀ hw).mp hh
  obtain ⟨r, hr, hlim⟩ := psi1_finite_zero_remainder ha hab.le
  have hlim' :=
    ((hlim.sub_const ((b ^ 2 - a ^ 2) / 2)).add_const (Real.log (2 * Real.pi) * (b - a))).abs
  apply le_of_tendsto hlim'
  filter_upwards with m
  have hneg :
    (∑ ρ ∈ S m,
        -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
          (ρ * (ρ + 1))) =
      -(∑ ρ ∈ S m, f ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp only [f]
    ring
  change
    |((b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) +
              (∑ ρ ∈ S m,
                  -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                    (ρ * (ρ + 1))).re +
              r) -
            (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a)| ≤
      (b - a) * B + 1
  rw [hneg, Complex.neg_re]
  have hs : |-(∑ ρ ∈ S m, f ρ).re| ≤ (b - a) * B := by
    rw [abs_neg]
    exact (Complex.abs_re_le_norm (∑ ρ ∈ S m, f ρ)).trans (hbound m)
  have htri := abs_add_le (-(∑ ρ ∈ S m, f ρ).re) r
  have heq :
    (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) + -(∑ ρ ∈ S m, f ρ).re + r -
          (b ^ 2 - a ^ 2) / 2 +
        Real.log (2 * Real.pi) * (b - a) =
      -(∑ ρ ∈ S m, f ρ).re + r := by
    ring
  rw [heq]
  linarith only [htri, hs, hr]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
