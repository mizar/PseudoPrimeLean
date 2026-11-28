/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCertificate644
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedGeometry

/-! # Phase lower bounds on the four section 122 intervals -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real section 122 phase sum, with multiplicities, over the zeta zeros
up to height `T` at positive radius `r`. This is the spectral term in the
principal comparison before passing to the limit. -/
noncomputable def quarterPhaseSum644 (r T : ℝ) : ℝ :=
  ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
      (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im).re

private theorem phase_width {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (2 * Real.log b - 2 * Real.log a) ^ 2 ≤ (2 * (b / a - 1)) ^ 2 := by
  have hb := ha.trans hab
  have hl := Real.log_lt_log ha hab
  have hu := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hu
  exact pow_le_pow_left₀ (by linarith only [hl]) (by linarith only [hu]) 2

/-- Under RH every height truncation at `T ≥ 100` satisfies a phase lower bound
on each of the four section 122 radius intervals. The bounds combine the
certified endpoint phases, a curvature loss, and the high-zero tail. -/
theorem quarter_phase_rows_644 (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    (∀ r ∈ Set.Icc 316 320, -0.006631 ≤ quarterPhaseSum644 r T) ∧
      (∀ r ∈ Set.Icc 320 (1287 / 4), -0.003250 ≤ quarterPhaseSum644 r T) ∧
      (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), -0.002063 ≤ quarterPhaseSum644 r T) ∧
      (∀ r ∈ Set.Icc (1609 / 5) 322, -0.002049 ≤ quarterPhaseSum644 r T) := by
  obtain ⟨g, hlo, hhi, h⟩ := quarter_phase_radius_interval_644 hRH
  have h₀ := quarter_phase_endpoint_644_316 hlo hhi
  have h₁ := quarter_phase_endpoint_644_320 hlo hhi
  have h₂ := quarter_phase_endpoint_644_32175 hlo hhi
  have h₃ := quarter_phase_endpoint_644_3218 hlo hhi
  have h₄ := quarter_phase_endpoint_644_322 hlo hhi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    have hw := phase_width (a := 316) (b := 320) (by norm_num only) (by norm_num only)
    have hs :=
      h (by norm_num only) (by norm_num only) hr hT h₀
        ((by norm_num only : (1842 / 1000000 : ℝ) ≤ 3371 / 1000000).trans h₁)
    unfold quarterPhaseSum644
    linarith only [hw, hs]
  · intro r hr
    have hw := phase_width (a := 320) (b := 1287 / 4) (by norm_num only) (by norm_num only)
    have hs :=
      h (by norm_num only) (by norm_num only) hr hT h₁
        ((by norm_num only : (3371 / 1000000 : ℝ) ≤ 4133 / 1000000).trans h₂)
    unfold quarterPhaseSum644
    linarith only [hw, hs]
  · intro r hr
    have hw := phase_width (a := 1287 / 4) (b := 1609 / 5) (by norm_num only) (by norm_num only)
    have hs :=
      h (by norm_num only) (by norm_num only) hr hT h₂
        ((by norm_num only : (4133 / 1000000 : ℝ) ≤ 4152 / 1000000).trans h₃)
    unfold quarterPhaseSum644
    linarith only [hw, hs]
  · intro r hr
    have hw := phase_width (a := 1609 / 5) (b := 322) (by norm_num only) (by norm_num only)
    have hs :=
      h (by norm_num only) (by norm_num only) hr hT h₃
        ((by norm_num only : (4152 / 1000000 : ℝ) ≤ 4227 / 1000000).trans h₄)
    unfold quarterPhaseSum644
    linarith only [hw, hs]

private theorem unified_ledger_eq (k : ℕ)
    (hk : 0 ≤ AnalyticNumberTheory.RiemannZeta.unifiedContourHeightSeq k) :
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
            (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
            (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
        (fun ρ ↦ ¬ρ.re < 0) =
      AnalyticNumberTheory.RiemannZeta.zerosUpTo
        (AnalyticNumberTheory.RiemannZeta.unifiedContourHeightSeq k) := by
  ext ρ
  rw [Finset.mem_filter, AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff,
    AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo hk]
  constructor
  · rintro ⟨⟨hb, hz⟩, hr⟩
    simp only [AnalyticNumberTheory.Rectangle.rectangleClosedBox, Complex.mem_reProdIm,
      Set.mem_uIcc, AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower,
      AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper] at hb
    refine ⟨hz, not_lt.mp hr, abs_le.mpr ?_⟩
    rcases hb.2 with h | h
    · exact h
    · exact ⟨(neg_nonpos.mpr hk).trans (hk.trans h.1), h.2.trans ((neg_nonpos.mpr hk).trans hk)⟩
  · rintro ⟨hz, hr, hi⟩
    have hre := AnalyticNumberTheory.RiemannZeta.riemannZeta_zero_re_le_one hz
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact
      ⟨⟨AnalyticNumberTheory.RiemannZeta.mem_unifiedTauRectangle 2 k (by linarith only [hr, hk0])
            (hre.trans (by norm_num only)) (abs_le.mp hi).1 (abs_le.mp hi).2,
          hz⟩,
        not_lt.mpr hr⟩

/-- The four certified phase bounds apply along the sequence of rectangular
truncations used by the logarithmic explicit formula. -/
theorem quarter_phase_rect_rows_644 (hRH : RiemannHypothesis) :
    ∀ᶠ k : ℕ in Filter.atTop,
      let S :=
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
              (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
              (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
          (fun ρ ↦ ¬ρ.re < 0)
      let F := fun r : ℝ ↦
        ∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                quarterPhaseKernel644 ρ.im).re
      (∀ r ∈ Set.Icc 316 320, -0.006631 ≤ F r) ∧
        (∀ r ∈ Set.Icc 320 (1287 / 4), -0.003250 ≤ F r) ∧
        (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), -0.002063 ≤ F r) ∧
        (∀ r ∈ Set.Icc (1609 / 5) 322, -0.002049 ≤ F r) := by
  filter_upwards [Filter.tendsto_atTop.mp
      AnalyticNumberTheory.RiemannZeta.tendsto_unifiedContourHeightSeq_atTop 100] with
    k hk
  dsimp only
  rw [unified_ledger_eq k ((by norm_num only : (0 : ℝ) ≤ 100).trans hk)]
  exact quarter_phase_rows_644 hRH hk

end PseudoPrime.PrimeTestBounds.MillerRabin
