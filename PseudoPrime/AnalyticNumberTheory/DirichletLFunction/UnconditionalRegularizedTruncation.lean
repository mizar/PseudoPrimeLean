/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogBelowThreshold
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalRegularizedZeroTail

/-! # Finite real-part and height truncation of the regularized zero norm sum -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A completed zero with real part between a threshold and one, and absolute
ordinate below a natural height, belongs to the corresponding closed rectangle.
Construct the real and imaginary coordinate bounds. This supplies finite-ledger
membership without a boundary-zero avoidance hypothesis. -/
theorem completed_zero_mem_rectangle_of_bounds {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {ρ : ℂ} (hz : χ.completedLFunction ρ = 0) {σ : ℝ} (hlo : σ ≤ ρ.re)
    (hhi : ρ.re ≤ 1) (H : ℕ) (hh : |ρ.im| ≤ H) :
    ρ ∈
      completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I)
        ((1 : ℂ) + (H : ℝ) * Complex.I) := by
  apply mem_completedZerosInRectangle_iff.mpr
  refine ⟨?_, hz⟩
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    mul_zero, sub_zero, Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im, Complex.I_im,
    mul_one, zero_sub, Complex.add_im, zero_add, Complex.one_re, Complex.one_im]
  exact ⟨Set.Icc_subset_uIcc ⟨hlo, hhi⟩, Set.Icc_subset_uIcc (abs_le.mp hh)⟩

/-- For a primitive nonprincipal character with nonprincipal inverse, modulus
and scale at least two, split the full regularized zero norm sum into a finite
part below any real threshold, a finite rectangle above it, and a high-ordinate
tail. These sets cover every actual divisor occurrence; overlaps on boundaries
are harmless for nonnegative norms. Use absolute summability and finite indicators.
This gives the truncation needed to combine local counting, weighted family
density, and the unconditional tail bound without leaving an uncounted height gap. -/
theorem tsum_norm_regularizedLogHalfZeroTerm_le_truncated_parts {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) (σ : ℝ) (H : ℕ) :
    (∑' ρ : ℂ, ‖regularizedLogHalfZeroTerm χ x ρ‖) ≤
      (∑
          ρ ∈
            (completedZerosInRectangle χ hne ((0 : ℂ) - (H : ℝ) * Complex.I)
                  ((1 : ℂ) + (H : ℝ) * Complex.I)).filter
              (fun ρ ↦ ρ.re ≤ σ),
          ‖regularizedLogHalfZeroTerm χ x ρ‖) +
        (∑
          ρ ∈
            completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I)
              ((1 : ℂ) + (H : ℝ) * Complex.I),
          ‖regularizedLogHalfZeroTerm χ x ρ‖) +
        ∑' ρ : ℂ, if (H : ℝ) ≤ |ρ.im| then ‖regularizedLogHalfZeroTerm χ x ρ‖ else 0 := by
  classical
  let f : ℂ → ℝ := fun ρ ↦ ‖regularizedLogHalfZeroTerm χ x ρ‖
  let S :=
    (completedZerosInRectangle χ hne ((0 : ℂ) - (H : ℝ) * Complex.I)
          ((1 : ℂ) + (H : ℝ) * Complex.I)).filter
      (fun ρ ↦ ρ.re ≤ σ)
  let T :=
    completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I) ((1 : ℂ) + (H : ℝ) * Complex.I)
  let U : Set ℂ := {ρ | (H : ℝ) ≤ |ρ.im|}
  have hs : Summable f :=
    (summable_regularizedLogHalfZeroTerm_unconditionally hq hp hne hinv hx).norm
  have hpoint (ρ : ℂ) :
    f ρ ≤ (S : Set ℂ).indicator f ρ + (T : Set ℂ).indicator f ρ + U.indicator f ρ := by
    have hn : 0 ≤ f ρ := norm_nonneg _
    have hsn : 0 ≤ (S : Set ℂ).indicator f ρ := Set.indicator_nonneg (fun _ _ ↦ norm_nonneg _) ρ
    have htn : 0 ≤ (T : Set ℂ).indicator f ρ := Set.indicator_nonneg (fun _ _ ↦ norm_nonneg _) ρ
    have hun : 0 ≤ U.indicator f ρ := Set.indicator_nonneg (fun _ _ ↦ norm_nonneg _) ρ
    by_cases hh : ρ ∈ U
    · rw [Set.indicator_of_mem hh]
      linarith only [hsn, htn]
    · have hheight : |ρ.im| ≤ H := (lt_of_not_ge hh).le
      by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
      · have hz : f ρ = 0 := by
          simp only [f, regularizedLogHalfZeroTerm, completedLogHalfZeroTerm, hD, Int.cast_zero,
            zero_mul, zero_div, mul_zero, sub_self, norm_zero]
        rw [hz]
        exact add_nonneg (add_nonneg hsn htn) hun
      · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
        have hlo := (completedLFunction_zero_re_pos hp hinv hz).le
        have hhi := (completedLFunction_zero_re_lt_one hne hz).le
        by_cases hr : ρ.re ≤ σ
        · have hS : ρ ∈ S :=
            Finset.mem_filter.mpr
              ⟨completed_zero_mem_rectangle_of_bounds hne hz hlo hhi H hheight, hr⟩
          rw [Set.indicator_of_mem hS]
          linarith only [htn, hun]
        · have hT : ρ ∈ T :=
            completed_zero_mem_rectangle_of_bounds hne hz (lt_of_not_ge hr).le hhi H hheight
          rw [Set.indicator_of_mem hT]
          linarith only [hsn, hun]
  have hb :=
    hs.tsum_le_tsum hpoint
      (((hs.indicator (S : Set ℂ)).add (hs.indicator (T : Set ℂ))).add (hs.indicator U))
  rw [((hs.indicator (S : Set ℂ)).add (hs.indicator (T : Set ℂ))).tsum_add (hs.indicator U),
    (hs.indicator (S : Set ℂ)).tsum_add (hs.indicator (T : Set ℂ)), ← sum_eq_tsum_indicator f S, ←
    sum_eq_tsum_indicator f T] at hb
  exact hb

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
