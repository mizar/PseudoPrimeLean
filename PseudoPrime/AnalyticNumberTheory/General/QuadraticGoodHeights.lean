/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.HorizontalLogDerivative
public import PseudoPrime.AnalyticNumberTheory.General.ConductorGrowth

/-!
# Quadratic horizontal bounds from general completion data

The fixed-parameter conductor profile removes local zero sums from the
good-height bound in both directions on the imaginary axis.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The reflected local zero-count estimate is bounded by ten times the
reference logarithmic derivative norm for entire order-one completion data.
Use the real-part norm bound. This controls all local counts by the same
reference-line growth profile. -/
theorem localZeroCount_le_referenceNorm {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (T : ℝ) :
    (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
      10 * ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ := by
  exact
    (localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder T).2.trans
      (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num only))

/-- A linear reference-line growth bound for an entire order-one completion
supplies in every positive or negative unit height interval a nonvanishing
horizontal segment with uniform quadratic logarithmic derivative bound.
Estimate the two counts used for height separation and the count at the
selected height by the reference profile. This removes the remaining local
zero sums from the good-height contour estimate. -/
theorem exists_height_with_quadratic_bound {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {A : ℝ} (hA : 0 < A)
    (href : ∀ T : ℝ, ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|)) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ H : ℝ,
          ∃ T ∈ Set.Icc H (H + 1),
            ∀ s : ℂ,
              s.im = T → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2 := by
  refine ⟨1 + 86 * A + 800 * A ^ 2, ?_, ?_⟩
  · nlinarith only [hA, sq_nonneg A]
  · intro H
    obtain ⟨T, hT, hbound⟩ := exists_height_with_horizontalStrip_bound hε hfe hright hF h0 horder H
    have hprofile :
      ∀ t : ℝ, |t| ≤ |H| + 1 → ‖logDeriv F (((3 : ℝ) : ℂ) + t * Complex.I)‖ ≤ A * (|H| + 2) := by
      intro t ht
      have hb := href t
      have hh := mul_le_mul_of_nonneg_left ht hA.le
      linarith only [hb, hh]
    have hmH : |H - 1| ≤ |H| + 1 := by
      simpa only [Real.norm_eq_abs, abs_one] using norm_sub_le H (1 : ℝ)
    have hpH : |H + 1| ≤ |H| + 1 := by
      simpa only [Real.norm_eq_abs, abs_one] using norm_add_le H (1 : ℝ)
    have hTH : |T| ≤ |H| + 1 :=
      abs_le.mpr ⟨by linarith only [hT.1, neg_le_abs H], by linarith only [hT.2, le_abs_self H]⟩
    have hm :=
      (localZeroCount_le_referenceNorm hε hfe hright hF h0 horder (H - 1)).trans
        (mul_le_mul_of_nonneg_left (hprofile (H - 1) hmH) (by norm_num only : (0 : ℝ) ≤ 10))
    have hp :=
      (localZeroCount_le_referenceNorm hε hfe hright hF h0 horder (H + 1)).trans
        (mul_le_mul_of_nonneg_left (hprofile (H + 1) hpH) (by norm_num only : (0 : ℝ) ≤ 10))
    have hr := hprofile T hTH
    have hn :=
      (localZeroCount_le_referenceNorm hε hfe hright hF h0 horder T).trans
        (mul_le_mul_of_nonneg_left hr (by norm_num only : (0 : ℝ) ≤ 10))
    have hmn :
      0 ≤
        (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) +
          ∑' z : ℂ, localZeroMultiplicity F (H + 1) z :=
      add_nonneg (tsum_nonneg (localZeroMultiplicity_nonneg F (H - 1)))
        (tsum_nonneg (localZeroMultiplicity_nonneg F (H + 1)))
    refine ⟨T, hT, ?_⟩
    intro s hs hlo hhi
    obtain ⟨hs0, hb⟩ := hbound s hs hlo hhi
    rw [div_div_eq_mul_div, div_one] at hb
    have hn' :=
      mul_le_mul_of_nonneg_right hn
        (by linarith only [hmn] :
          0 ≤
            4 *
              (1 + (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) +
                ∑' z : ℂ, localZeroMultiplicity F (H + 1) z))
    have hM :
      (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) + ∑' z : ℂ, localZeroMultiplicity F (H + 1) z ≤
        20 * A * (|H| + 2) := by
      linarith only [hm, hp]
    have hM' :=
      mul_le_mul_of_nonneg_left hM (by nlinarith only [hA, abs_nonneg H] : 0 ≤ 40 * A * (|H| + 2))
    have hlin : A * (|H| + 2) ≤ A * (|H| + 2) ^ 2 := by
      have hh : |H| + 2 ≤ (|H| + 2) ^ 2 := by nlinarith only [abs_nonneg H]
      exact mul_le_mul_of_nonneg_left hh hA.le
    refine ⟨hs0, ?_⟩
    nlinarith only [hb, hn', hM', hr, hlin, sq_nonneg (|H| + 2)]

/-- Regularized completion data with general complex gamma parameters and
an arithmetic logarithmic derivative series imply quadratic horizontal-edge
bounds at selected heights in every unit interval. Derive the linear
reference profile from the conductor and gamma estimates, then apply the
zero-avoiding height construction. No separate horizontal growth premise
or Riemann hypothesis is required. This is a fixed-completion estimate for
the general explicit formula. -/
theorem exists_height_with_quadratic_bound_of_completion {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ H : ℝ,
          ∃ T ∈ Set.Icc H (H + 1),
            ∀ s : ℂ,
              s.im = T → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2 := by
  obtain ⟨A, hA, href⟩ :=
    exists_norm_logDeriv_at_three_le_linear_height hq k κ hκ hreg ha hL hdL hlog
  exact exists_height_with_quadratic_bound hε hfe hright hF h0 horder hA href

/-- A quadratic good-height bound in every real unit interval yields an
upper height sequence tending to positive infinity and a lower sequence
tending to negative infinity. Both horizontal segments are nonvanishing and
share the bound C times (n+5)^2. Select the heights by classical choice at
shifted positive and negative integers; their interval inequalities imply
the limits. These sequences are used to pass finite contour formulas to the
infinite-height explicit formula. -/
theorem exists_goodHeight_sequences {F : ℂ → ℂ} {C : ℝ} (hC : 0 < C)
    (hb :
      ∀ H : ℝ,
        ∃ T ∈ Set.Icc H (H + 1),
          ∀ s : ℂ, s.im = T → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2) :
    ∃ U B : ℕ → ℝ,
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
        Filter.Tendsto B Filter.atTop Filter.atBot ∧
        ∀ n : ℕ,
          (n : ℝ) + 2 ≤ U n ∧
            B n ≤ -(n : ℝ) - 2 ∧
            ∀ s : ℂ,
              (s.im = U n ∨ s.im = B n) →
                -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * ((n : ℝ) + 5) ^ 2 := by
  classical
  let τ : ℝ → ℝ := fun H ↦ Classical.choose (hb H)
  have hτ :
    ∀ H : ℝ,
      τ H ∈ Set.Icc H (H + 1) ∧
        ∀ s : ℂ, s.im = τ H → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2 :=
    fun H ↦ Classical.choose_spec (hb H)
  let U : ℕ → ℝ := fun n ↦ τ ((n : ℝ) + 2)
  let B : ℕ → ℝ := fun n ↦ τ (-(n : ℝ) - 3)
  have hu : ∀ n : ℕ, (n : ℝ) + 2 ≤ U n := fun n ↦ (hτ _).1.1
  have hb' : ∀ n : ℕ, B n ≤ -(n : ℝ) - 2 := by
    intro n
    have hh := (hτ (-(n : ℝ) - 3)).1.2
    change B n ≤ (-(n : ℝ) - 3) + 1 at hh
    linarith only [hh]
  have htop : Filter.Tendsto U Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ by linarith only [hu n]) tendsto_natCast_atTop_atTop
  have hneg : Filter.Tendsto (fun n ↦ -B n) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ by linarith only [hb' n]) tendsto_natCast_atTop_atTop
  have hbot : Filter.Tendsto B Filter.atTop Filter.atBot := by
    simpa only [Function.comp_def, neg_neg] using Filter.tendsto_neg_atTop_atBot.comp hneg
  refine ⟨U, B, htop, hbot, ?_⟩
  intro n
  refine ⟨hu n, hb' n, ?_⟩
  intro s hs hlo hhi
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases hs with hs | hs
  · have hh := (hτ ((n : ℝ) + 2)).2 s hs hlo hhi
    rw [abs_of_nonneg (by linarith only [hnn] : 0 ≤ (n : ℝ) + 2)] at hh
    have hp : ((n : ℝ) + 2 + 2) ^ 2 ≤ ((n : ℝ) + 5) ^ 2 := by nlinarith only [hnn]
    exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_left hp hC.le)⟩
  · have hh := (hτ (-(n : ℝ) - 3)).2 s hs hlo hhi
    rw [abs_of_nonpos (by linarith only [hnn] : -(n : ℝ) - 3 ≤ 0)] at hh
    refine ⟨hh.1, ?_⟩
    convert hh.2 using 1
    ring

end PseudoPrime.AnalyticNumberTheory.General
