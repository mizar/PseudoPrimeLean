/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestAnalytic
public import PseudoPrime.AnalyticNumberTheory.General.MellinTestZeroSum
public import PseudoPrime.AnalyticNumberTheory.General.RectangleZeroSums
public import PseudoPrime.AnalyticNumberTheory.General.HorizontalMellinDecay
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.BoundaryLimits

/-!
# Mellin contour limits for the infinite zero side

Finite weighted residues converge along good-height rectangles. Horizontal
integrals vanish simultaneously; vertical-edge evaluation remains separate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an entire function nonzero at zero of order at most one, with conjugate
functional equation and no zeros right of the critical strip, the finite Mellin
zero sums converge along any heights tending to opposite infinities.
An even smooth compactly supported logarithmic test supplies absolute convergence,
and reflection locates the zeros. This specializes finite exhaustion to the
test functions used by the explicit formula. -/
theorem tendsto_rectangle_mellin_zero_sum {F : ℂ → ℂ} {ε : ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (hε : ε ≠ 0)
    (hfe : ∀ s, F s = ε * star (F (1 - star s))) (hright : ∀ s, 1 < s.re → F s ≠ 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (U B : ℕ → ℝ) (hU : Filter.Tendsto U Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atBot) :
    Filter.Tendsto
      (fun n ↦
        ∑
          ρ ∈
            entireZerosInRectangle hF h0 (((-1 : ℝ) : ℂ) + B n * Complex.I)
              (((2 : ℝ) : ℂ) + U n * Complex.I),
          (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)
      Filter.atTop
      (nhds (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)) := by
  exact
    tendsto_rectangle_zero_sum hF h0
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) _
      (summable_mellin_zero_terms_of_orderAtMostOne hF h0 horder hε hfe hright g he hc hg) U B hU hB

/-- For an entire function nonzero at zero of order at most one, with conjugate
functional equation and right-half-plane nonvanishing, good-height rectangles
have logarithmic Mellin boundary integrals tending to -2*pi*i times the
multiplicity-weighted infinite zero sum. The logarithmic test is even, smooth
and compactly supported. Its Mellin transform is entire and its zero values
are summable; horizontal nonvanishing puts the finite ledger inside each contour.
No residue identity or zero-sum convergence is assumed. -/
theorem tendsto_mellin_boundary {F : ℂ → ℂ} {ε : ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (horder : HasOrderAtMostOne F) (hε : ε ≠ 0) (hfe : ∀ s, F s = ε * star (F (1 - star s)))
    (hright : ∀ s, 1 < s.re → F s ≠ 0) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (U B : ℕ → ℝ)
    (hU : Filter.Tendsto U Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atBot) (hBU : ∀ n, B n < U n)
    (hboundary : ∀ n s, (s.im = U n ∨ s.im = B n) → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0) :
    Filter.Tendsto
      (fun n ↦
        RectangleGeometry.rectangleBoundaryIntegral
          (fun s ↦ -logDeriv F s * mellin (logarithmicTestWeight g) s)
          (((-1 : ℝ) : ℂ) + B n * Complex.I) (((2 : ℝ) : ℂ) + U n * Complex.I))
      Filter.atTop
      (nhds
        (-(2 * Real.pi * Complex.I) *
          ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)) := by
  have hs : ∀ ρ : ℂ, F ρ = 0 → ρ.re ∈ Set.Icc (0 : ℝ) 1 := fun ρ hz ↦
    zero_re_mem_Icc_of_functionalEquation hε hfe hright hz
  exact
    tendsto_weighted_entire_boundary hF h0
      (differentiable_mellin_logarithmicTestWeight g hc hg.continuous) hs
      (summable_mellin_zero_terms_of_orderAtMostOne hF h0 horder hε hfe hright g he hc hg) U B hU hB
      hBU (fun n ↦ entireZerosInRectangle_subset_open hF h0 hs (U n) (B n) (hBU n) (hboundary n))

/-- For an entire order-one function with conjugate functional equation,
right-half-plane nonvanishing and a quadratic good-height logarithmic-derivative
bound, an even smooth compactly supported test admits simultaneous upper and
lower contour heights. Both horizontal integrals tend to zero, while the full
boundary integral tends to the weighted infinite zero sum with factor -2*pi*i.
Select the existing good-height sequences and apply the proved finite-residue
limit. This gives the zero-side contour limits for the Mellin explicit formula. -/
theorem exists_goodHeight_mellin_boundary_limit {F : ℂ → ℂ} {ε : ℂ} {C : ℝ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (hε : ε ≠ 0)
    (hfe : ∀ s, F s = ε * star (F (1 - star s))) (hright : ∀ s, 1 < s.re → F s ≠ 0) (hC : 0 < C)
    (hb :
      ∀ H : ℝ,
        ∃ T ∈ Set.Icc H (H + 1),
          ∀ s : ℂ, s.im = T → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2)
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    ∃ U B : ℕ → ℝ,
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
        Filter.Tendsto B Filter.atTop Filter.atBot ∧
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
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n ↦
            RectangleGeometry.rectangleBoundaryIntegral
              (fun s ↦ -logDeriv F s * mellin (logarithmicTestWeight g) s)
              (((-1 : ℝ) : ℂ) + B n * Complex.I) (((2 : ℝ) : ℂ) + U n * Complex.I))
          Filter.atTop
          (nhds
            (-(2 * Real.pi * Complex.I) *
              ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)) := by
  obtain ⟨U, B, hu, hb', hseq, htop, hbot⟩ :=
    exists_goodHeight_sequences_with_horizontal_integrals_zero hC hb g he hc hg
  refine ⟨U, B, hu, hb', htop, hbot, ?_⟩
  apply tendsto_mellin_boundary hF h0 horder hε hfe hright g he hc hg U B hu hb'
  · intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    have hupper := (hseq n).1
    have hlower := (hseq n).2.1
    linarith only [hn, hupper, hlower]
  · intro n s hheight hlo hhi
    exact ((hseq n).2.2 s hheight hlo hhi).1

/-- If the two horizontal logarithmic Mellin integrals vanish and the full
negative-logarithmic boundary integral has its proved zero-sum limit, the
right vertical integral minus the left one tends to 2*pi times that zero sum.
Extract the oriented vertical difference and multiply by i; i squared fixes
the sign. This normalization prepares evaluation of the vertical edges. -/
theorem tendsto_mellin_vertical_difference {F : ℂ → ℂ} (g : ℝ → ℂ) (U B : ℕ → ℝ)
    (hupper :
      Filter.Tendsto
        (fun n ↦
          ∫ σ in (-1 : ℝ)..2,
            logDeriv F ((σ : ℂ) + U n * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + U n * Complex.I))
        Filter.atTop (nhds 0))
    (hlower :
      Filter.Tendsto
        (fun n ↦
          ∫ σ in (-1 : ℝ)..2,
            logDeriv F ((σ : ℂ) + B n * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + B n * Complex.I))
        Filter.atTop (nhds 0))
    (hboundary :
      Filter.Tendsto
        (fun n ↦
          RectangleGeometry.rectangleBoundaryIntegral
            (fun s ↦ -logDeriv F s * mellin (logarithmicTestWeight g) s)
            (((-1 : ℝ) : ℂ) + B n * Complex.I) (((2 : ℝ) : ℂ) + U n * Complex.I))
        Filter.atTop
        (nhds
          (-(2 * Real.pi * Complex.I) *
            ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ))) :
    Filter.Tendsto
      (fun n ↦
        (∫ y in B n..U n,
            logDeriv F (((2 : ℝ) : ℂ) + y * Complex.I) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + y * Complex.I)) -
          (∫ y in B n..U n,
            logDeriv F (((-1 : ℝ) : ℂ) + y * Complex.I) *
              mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + y * Complex.I)))
      Filter.atTop
      (nhds
        ((2 * Real.pi : ℂ) *
          ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)) := by
  have hu :
    Filter.Tendsto
      (fun n ↦
        ∫ σ in (-1 : ℝ)..2,
          -logDeriv F ((σ : ℂ) + U n * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + U n * Complex.I))
      Filter.atTop (nhds 0) := by
    simpa only [neg_mul, intervalIntegral.integral_neg, neg_zero] using hupper.neg
  have hb :
    Filter.Tendsto
      (fun n ↦
        ∫ σ in (-1 : ℝ)..2,
          -logDeriv F ((σ : ℂ) + B n * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + B n * Complex.I))
      Filter.atTop (nhds 0) := by
    simpa only [neg_mul, intervalIntegral.integral_neg, neg_zero] using hlower.neg
  have ht :=
    (RectangleGeometry.tendsto_vertical_difference_of_boundary_limit _ (-1) 2 U B _ hu hb
          hboundary).const_mul
      Complex.I
  have heq (n : ℕ) :
    Complex.I *
        (Complex.I *
            (∫ y in B n..U n,
              -logDeriv F (((2 : ℝ) : ℂ) + y * Complex.I) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + y * Complex.I)) -
          Complex.I *
            (∫ y in B n..U n,
              -logDeriv F (((-1 : ℝ) : ℂ) + y * Complex.I) *
                mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + y * Complex.I))) =
      (∫ y in B n..U n,
          logDeriv F (((2 : ℝ) : ℂ) + y * Complex.I) *
            mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + y * Complex.I)) -
        (∫ y in B n..U n,
          logDeriv F (((-1 : ℝ) : ℂ) + y * Complex.I) *
            mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + y * Complex.I)) := by
    rw [← mul_sub, ← mul_assoc, Complex.I_mul_I]
    simp only [neg_mul, intervalIntegral.integral_neg]
    ring
  have htarget :
    Complex.I *
        (-(2 * Real.pi * Complex.I) *
          ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) =
      (2 * Real.pi : ℂ) *
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ := by
    calc
      _ =
          -(2 * Real.pi : ℂ) * (Complex.I * Complex.I) *
            ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ :=
        by ring
      _ = _ := by
        rw [Complex.I_mul_I]; ring
  rw [htarget] at ht
  exact ht.congr heq

/-- For an entire order-one function nonzero at zero, with conjugate functional
equation, right-half-plane nonvanishing and quadratic good-height bounds, an
even smooth compact test has height sequences tending to opposite infinities
on which the right-minus-left logarithmic Mellin integral tends to 2*pi times
the multiplicity-weighted zero sum. Combine the actual finite-residue limit
and horizontal vanishing; neither limit is an independent input.
This is the zero-side identity before evaluating the two vertical lines. -/
theorem exists_goodHeight_mellin_vertical_difference {F : ℂ → ℂ} {ε : ℂ} {C : ℝ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (hε : ε ≠ 0)
    (hfe : ∀ s, F s = ε * star (F (1 - star s))) (hright : ∀ s, 1 < s.re → F s ≠ 0) (hC : 0 < C)
    (hb :
      ∀ H : ℝ,
        ∃ T ∈ Set.Icc H (H + 1),
          ∀ s : ℂ, s.im = T → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ C * (|H| + 2) ^ 2)
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    ∃ U B : ℕ → ℝ,
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
        Filter.Tendsto B Filter.atTop Filter.atBot ∧
        Filter.Tendsto
          (fun n ↦
            (∫ y in B n..U n,
                logDeriv F (((2 : ℝ) : ℂ) + y * Complex.I) *
                  mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + y * Complex.I)) -
              (∫ y in B n..U n,
                logDeriv F (((-1 : ℝ) : ℂ) + y * Complex.I) *
                  mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + y * Complex.I)))
          Filter.atTop
          (nhds
            ((2 * Real.pi : ℂ) *
              ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)) := by
  obtain ⟨U, B, hu, hb', htop, hbot, hboundary⟩ :=
    exists_goodHeight_mellin_boundary_limit hF h0 horder hε hfe hright hC hb g he hc hg
  exact ⟨U, B, hu, hb', tendsto_mellin_vertical_difference g U B htop hbot hboundary⟩

/-- General completion data with complex gamma shifts of real part greater
than -1, entire order-one regularization nonzero at zero, conjugate functional
equation and right-half-plane nonvanishing supply the zero-side contour limit
for an even smooth compact logarithmic test. Arithmetic coefficient bounds
and the logarithmic derivative series on the reference line give the required
good-height bounds. The right-minus-left Mellin integral tends to 2*pi times
the weighted zero sum without an independent height-selection, residue-limit
or zero-sum convergence premise. Vertical-line evaluation is the next step. -/
theorem exists_mellin_vertical_difference_of_completion {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q)
    (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
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
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    ∃ U B : ℕ → ℝ,
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
        Filter.Tendsto B Filter.atTop Filter.atBot ∧
        Filter.Tendsto
          (fun n ↦
            (∫ y in B n..U n,
                logDeriv F (((2 : ℝ) : ℂ) + y * Complex.I) *
                  mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + y * Complex.I)) -
              (∫ y in B n..U n,
                logDeriv F (((-1 : ℝ) : ℂ) + y * Complex.I) *
                  mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + y * Complex.I)))
          Filter.atTop
          (nhds
            ((2 * Real.pi : ℂ) *
              ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ)) := by
  obtain ⟨C, hC, hb⟩ :=
    exists_height_with_quadratic_bound_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog
  exact exists_goodHeight_mellin_vertical_difference hF h0 horder hε hfe hright hC hb g he hc hg

end PseudoPrime.AnalyticNumberTheory.General
