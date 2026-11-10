/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevZeroSplit
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalPositiveCount

/-! # Chebyshev error from explicit zero-count inputs

Combine the conditional reciprocal-height and inverse-square-tail bounds.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a Rosser-type positive-height count estimate through `T` and a
uniform inverse-square tail estimate beyond `T` imply the displayed explicit
bound for `|ψ(x) - x|`. Use the reciprocal-sum estimate in the symmetric
zero-split bound. Both zero-count inputs remain explicit hypotheses. -/
theorem psi_error_of_zero_count (hRH : RiemannHypothesis) {T x h : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hh : 0 < h) (hx : 1 < x - h)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) T,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t))
    (hC :
      ∀ m : ℕ,
        (∑
            ρ ∈
              ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                        (unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0)).filter
                (fun ρ ↦ ¬|ρ.im| ≤ T),
            (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
          Real.log T / (Real.pi * T)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  have hT0 : 0 ≤ T :=
    (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos) (Real.exp_pos 1)).le.trans hT
  have hlo := reciprocal_of_rosser hRH hT hQ
  have hh' := psi_error_of_zero_split hRH hT0 hh hx hC
  have hm := mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg (x + h))
  linarith only [hh', hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
