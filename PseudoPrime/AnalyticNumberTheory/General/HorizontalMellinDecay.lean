/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.QuadraticGoodHeights
public import PseudoPrime.AnalyticNumberTheory.General.MellinTestStripDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Vanishing horizontal integrals for smooth compact logarithmic tests

Fourth-power uniform Mellin decay dominates the quadratic logarithmic-derivative
bound on good heights. Both horizontal integrals tend to zero along the upper
and lower sequences. The statements retain the nonvanishing information needed
to assemble expanding residue contours.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- If the logarithmic-derivative factor has a quadratic bound and the test
factor has fourth-power height decay, their product is bounded by a constant
times (n+2) to the inverse second power at heights of magnitude at least n+2.
Use (n+5)^2 <= 9(n+2)^2 and the norm product formula. This scalar estimate
controls the horizontal integrand on both good-height sequences. -/
theorem norm_product_le_of_quadratic_growth_and_quartic_decay (L W : ℂ) (C D T : ℝ) (n : ℕ)
    (hC : 0 ≤ C) (hL : ‖L‖ ≤ C * ((n : ℝ) + 5) ^ 2) (hW : |T| ^ 4 * ‖W‖ ≤ D)
    (hT : (n : ℝ) + 2 ≤ |T|) : ‖L * W‖ ≤ 9 * C * D / ((n : ℝ) + 2) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hu : 0 < (n : ℝ) + 2 := by linarith only [hn]
  have hs : ((n : ℝ) + 5) ^ 2 ≤ 9 * ((n : ℝ) + 2) ^ 2 := by
    have hb : (n : ℝ) + 5 ≤ 3 * ((n : ℝ) + 2) := by linarith only [hn]
    have hp := pow_le_pow_left₀ (by linarith only [hn] : 0 ≤ (n : ℝ) + 5) hb 2
    nlinarith only [hp]
  have hl : ‖L‖ ≤ 9 * C * ((n : ℝ) + 2) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hs hC
    nlinarith only [hL, hh]
  have hw : ((n : ℝ) + 2) ^ 4 * ‖W‖ ≤ D :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.le hT 4) (norm_nonneg W)).trans hW
  apply (le_div_iff₀ (pow_pos hu 2)).mpr
  rw [norm_mul]
  calc
    ‖L‖ * ‖W‖ * ((n : ℝ) + 2) ^ 2 ≤ (9 * C * ((n : ℝ) + 2) ^ 2) * ‖W‖ * ((n : ℝ) + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (norm_nonneg W)) (sq_nonneg _)
    _ = 9 * C * (((n : ℝ) + 2) ^ 4 * ‖W‖) := by ring
    _ ≤ 9 * C * D := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num only) hC)

/-- For an even compactly supported smooth logarithmic test, a horizontal
integral of the entire regularization's logarithmic derivative times its
Mellin transform tends to zero along a sequence of heights of magnitude
at least n+2, provided the logarithmic derivative has a uniform quadratic
bound on the segment. Bound the integral by segment length times the
inverse-square product majorant and squeeze its norm to zero.
This supplies the horizontal-edge limit in the Mellin explicit formula. -/
theorem tendsto_horizontal_logDeriv_mellin_integral_zero (F : ℂ → ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C) (T : ℕ → ℝ) (hT : ∀ n : ℕ, (n : ℝ) + 2 ≤ |T n|)
    (hL :
      ∀ n : ℕ,
        ∀ σ ∈ Set.Icc a b, ‖logDeriv F ((σ : ℂ) + T n * Complex.I)‖ ≤ C * ((n : ℝ) + 5) ^ 2) :
    Filter.Tendsto
      (fun n ↦
        ∫ σ in a..b,
          logDeriv F ((σ : ℂ) + T n * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T n * Complex.I))
      Filter.atTop (nhds 0) := by
  obtain ⟨D, _, hD⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg a b 4
  have hb :
    ∀ n : ℕ,
      ‖∫ σ in a..b,
            logDeriv F ((σ : ℂ) + T n * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T n * Complex.I)‖ ≤
        9 * C * D / ((n : ℝ) + 2) ^ 2 * |b - a| := by
    intro n
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hs : σ ∈ Set.Icc a b := by
      rw [← Set.uIcc_of_le hab]
      exact Set.uIoc_subset_uIcc hσ
    exact
      norm_product_le_of_quadratic_growth_and_quartic_decay _ _ C D (T n) n hC (hL n σ hs)
        (hD σ hs (T n)) (hT n)
  apply squeeze_zero_norm hb
  have hi : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)⁻¹) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul] using
      (tendsto_mul_add_inv_atTop_nhds_zero 1 2 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hp := ((hi.pow 2).const_mul (9 * C * D)).mul_const |b - a|
  simpa only [inv_pow, div_eq_mul_inv, zero_pow (by norm_num only : 2 ≠ 0), mul_zero,
    zero_mul] using hp

/-- A quadratic good-height bound in every real unit interval supplies upper
and lower sequences escaping to infinity on which both horizontal weighted
logarithmic-derivative integrals vanish for an even compactly supported smooth
test. Select the existing good-height sequences, retain nonvanishing on
the segments, and apply uniform Mellin decay to each sequence.
This connects height selection to the horizontal limits needed to pass from
finite residue rectangles to an infinite-zero explicit formula. -/
theorem exists_goodHeight_sequences_with_horizontal_integrals_zero {F : ℂ → ℂ} {C : ℝ} (hC : 0 < C)
    (hb :
      ∀ H : ℝ,
        ∃ T ∈ Set.Icc H (H + 1),
          ∀ s : ℂ, s.im = T → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2)
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    ∃ U B : ℕ → ℝ,
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
        Filter.Tendsto B Filter.atTop Filter.atBot ∧
        (∀ n : ℕ,
          (n : ℝ) + 2 ≤ U n ∧
            B n ≤ -(n : ℝ) - 2 ∧
            ∀ s : ℂ,
              (s.im = U n ∨ s.im = B n) →
                -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * ((n : ℝ) + 5) ^ 2) ∧
        Filter.Tendsto
          (fun n ↦
            ∫ σ in (-1 : ℝ)..2,
              logDeriv F ((σ : ℂ) + U n * Complex.I) *
                mellin (logarithmicTestWeight g) ((σ : ℂ) + U n * Complex.I))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n ↦
            ∫ σ in (-1 : ℝ)..2,
              logDeriv F ((σ : ℂ) + B n * Complex.I) *
                mellin (logarithmicTestWeight g) ((σ : ℂ) + B n * Complex.I))
          Filter.atTop (nhds 0) := by
  obtain ⟨U, B, hu, hb', hseq⟩ := exists_goodHeight_sequences hC hb
  have hcoord :
    ∀ σ T : ℝ, (((σ : ℂ) + T * Complex.I).im = T) ∧ (((σ : ℂ) + T * Complex.I).re = σ) := by
    intro σ T
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, zero_add, add_zero, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      sub_zero]
    exact ⟨True.intro, True.intro⟩
  refine ⟨U, B, hu, hb', hseq, ?_, ?_⟩
  · apply
      tendsto_horizontal_logDeriv_mellin_integral_zero F g he hc hg (-1) 2 C (by norm_num only)
        hC.le U
    · intro n
      exact (hseq n).1.trans (le_abs_self _)
    · intro n σ hσ
      exact
        ((hseq n).2.2 _ (Or.inl (hcoord σ (U n)).1)
            (by
              rw [(hcoord σ (U n)).2]; exact hσ.1)
            (by
              rw [(hcoord σ (U n)).2]; exact hσ.2)).2
  · apply
      tendsto_horizontal_logDeriv_mellin_integral_zero F g he hc hg (-1) 2 C (by norm_num only)
        hC.le B
    · intro n
      have hn := (hseq n).2.1
      exact (by linarith only [hn] : (n : ℝ) + 2 ≤ -B n).trans (neg_le_abs _)
    · intro n σ hσ
      exact
        ((hseq n).2.2 _ (Or.inr (hcoord σ (B n)).1)
            (by
              rw [(hcoord σ (B n)).2]; exact hσ.1)
            (by
              rw [(hcoord σ (B n)).2]; exact hσ.2)).2

end PseudoPrime.AnalyticNumberTheory.General
