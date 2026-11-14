/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroError
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroHeadSplit
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedZeroExhaustion

/-! # Integrated ψ error retaining the signed low-zero head -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, retain the real signed contribution of zeros through `A` in
the integrated ψ error on `1 < a < b`. The range `(A,T]` uses a reciprocal
sum difference and the tail above `T` uses the supplied bound `C`. -/
theorem psi1_error_retain_head (hRH : RiemannHypothesis) {A T a b C : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (ha : 1 < a) (hab : a < b)
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
    let f : ℂ → ℂ := fun ρ ↦
      (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    |Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a - (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a)| ≤
      |(∑ ρ ∈ zerosUpTo A, f ρ).re| +
        (b - a) *
          (Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A) +
            (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C) +
        1 := by
  classical
  dsimp only
  let S : ℕ → Finset ℂ := fun m ↦
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let f : ℂ → ℂ := fun ρ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
  let B :=
    Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A) +
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C
  obtain ⟨r, hr, hlim⟩ := psi1_finite_zero_remainder ha hab.le
  have hlim' :=
    ((hlim.sub_const ((b ^ 2 - a ^ 2) / 2)).add_const (Real.log (2 * Real.pi) * (b - a))).abs
  apply le_of_tendsto hlim'
  filter_upwards [unified_head_eventually_eq hA] with m hhead
  have hbound :=
    split_zero_sum_retain_head hRH (S m)
      (fun ρ hρ ↦ (mem_riemannZetaZerosInAnyRectangle_iff.mp (Finset.mem_filter.mp hρ).1).2)
      (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2) hA hAT (zero_lt_one.trans ha) hab (hC m)
  change
    |(∑ ρ ∈ S m, f ρ).re| ≤
      |(∑ ρ ∈ (S m).filter (fun ρ ↦ |ρ.im| ≤ A), f ρ).re| + (b - a) * B at hbound
  rw [hhead] at hbound
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
      |(∑ ρ ∈ zerosUpTo A, f ρ).re| + (b - a) * B + 1
  rw [hneg, Complex.neg_re]
  have htri := abs_add_le (-(∑ ρ ∈ S m, f ρ).re) r
  have heq :
    (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) + -(∑ ρ ∈ S m, f ρ).re + r -
          (b ^ 2 - a ^ 2) / 2 +
        Real.log (2 * Real.pi) * (b - a) =
      -(∑ ρ ∈ S m, f ρ).re + r := by
    ring
  rw [heq]
  rw [abs_neg] at htri
  linarith only [htri, hbound, hr]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
