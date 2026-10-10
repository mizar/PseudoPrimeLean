/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ArchimedeanGammaPoles
public import PseudoPrime.AnalyticNumberTheory.General.ArchimedeanGammaGrowth
public import PseudoPrime.AnalyticNumberTheory.General.HorizontalMellinDecay
public import PseudoPrime.AnalyticNumberTheory.General.MellinVerticalIntegrals
public import PseudoPrime.AnalyticNumberTheory.General.MellinTestAnalytic
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.BoundaryLimits

/-!
# Mellin-weighted gamma contours

Apply the finite gamma pole formula to compactly supported logarithmic tests.
For nonnegative-real shifts, pass to full vertical integrals once their
integrability and vanishing horizontal contributions are supplied.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For shifts with real part greater than -1, a continuous compactly supported test,
an ordered positive-real rectangle, and interior gamma poles, the Mellin-weighted
gamma contour equals its negative multiplicity-weighted pole sum. Apply the entire
Mellin weight to the finite gamma residue formula. This retains poles during line shifts. -/
theorem mellin_archimedeanGamma_finite_contour {d : ℕ} (κ : Fin d → ℂ) (hk : ∀ j, -1 < (κ j).re)
    (g : ℝ → ℂ) (hc : HasCompactSupport g) (hg : Continuous g) {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re < w.re) (him : z.im < w.im)
    (hop :
      ∀ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s ↦ logDeriv (archimedeanGammaFactor κ) s * mellin (logarithmicTestWeight g) s) z w =
      ∑ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        2 * Real.pi * Complex.I *
          (-(analyticOrderNatAt (inverseArchimedeanGammaFactor κ) s : ℂ) *
            mellin (logarithmicTestWeight g) s) := by
  exact
    archimedeanGamma_weighted_finite_contour κ hk hz hre him
      (differentiable_mellin_logarithmicTestWeight g hc hg) hop

/-- Under the finite gamma contour hypotheses, the oriented vertical difference is
the pole residue sum minus the lower horizontal edge plus the upper edge. Expand
the four-edge definition. This prepares the infinite-height Mellin contour limit. -/
theorem mellin_archimedeanGamma_finite_vertical_difference {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, -1 < (κ j).re) (g : ℝ → ℂ) (hc : HasCompactSupport g) (hg : Continuous g) {z w : ℂ}
    (hz : 0 < z.re) (hre : z.re < w.re) (him : z.im < w.im)
    (hop :
      ∀ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    Complex.I *
          (∫ T in z.im..w.im,
            logDeriv (archimedeanGammaFactor κ) ((w.re : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) ((w.re : ℂ) + T * Complex.I)) -
        Complex.I *
          (∫ T in z.im..w.im,
            logDeriv (archimedeanGammaFactor κ) ((z.re : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) ((z.re : ℂ) + T * Complex.I)) =
      (∑ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
            2 * Real.pi * Complex.I *
              (-(analyticOrderNatAt (inverseArchimedeanGammaFactor κ) s : ℂ) *
                mellin (logarithmicTestWeight g) s)) -
          (∫ σ in z.re..w.re,
            logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + z.im * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + z.im * Complex.I)) +
        (∫ σ in z.re..w.re,
          logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + w.im * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + w.im * Complex.I)) := by
  rw [← mellin_archimedeanGamma_finite_contour κ hk g hc hg hz hre him hop]
  simp only [RectangleGeometry.rectangleBoundaryIntegral, smul_eq_mul]
  ring

/-- For nonnegative-real shifts and a continuous compactly supported test, the
Mellin-weighted gamma contour on an ordered positive-real rectangle vanishes.
The gamma pole ledger is empty there. This is the finite residue-free case for LLS. -/
theorem mellin_archimedeanGamma_finite_contour_eq_zero_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) (g : ℝ → ℂ) (hc : HasCompactSupport g) (hg : Continuous g) {z w : ℂ}
    (hz : 0 < z.re) (hre : z.re < w.re) (him : z.im < w.im) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s ↦ logDeriv (archimedeanGammaFactor κ) s * mellin (logarithmicTestWeight g) s) z w =
      0 := by
  exact
    archimedeanGamma_weighted_finite_contour_eq_zero_of_nonneg κ hk hz hre him
      (differentiable_mellin_logarithmicTestWeight g hc hg)

/-- For nonnegative-real shifts and a continuous compactly supported test, two positive
vertical Mellin-gamma integrals agree if they are integrable and the horizontal edges
vanish along ordered heights tending to both infinities. Pass the zero finite contour
to the limit and cancel i. The analytic decay and integrability remain explicit inputs;
this supplies the limiting interface for the central-line gamma term. -/
theorem mellin_archimedeanGamma_vertical_integral_eq_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) (g : ℝ → ℂ) (hc : HasCompactSupport g) (hg : Continuous g) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (U B : ℕ → ℝ) (hBU : ∀ n, B n < U n)
    (hU : Filter.Tendsto U Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atBot)
    (hupper :
      Filter.Tendsto
        (fun n ↦
          ∫ x in a..b,
            logDeriv (archimedeanGammaFactor κ) ((x : ℂ) + U n * Complex.I) *
              mellin (logarithmicTestWeight g) ((x : ℂ) + U n * Complex.I))
        Filter.atTop (nhds 0))
    (hlower :
      Filter.Tendsto
        (fun n ↦
          ∫ x in a..b,
            logDeriv (archimedeanGammaFactor κ) ((x : ℂ) + B n * Complex.I) *
              mellin (logarithmicTestWeight g) ((x : ℂ) + B n * Complex.I))
        Filter.atTop (nhds 0))
    (hia :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          logDeriv (archimedeanGammaFactor κ) ((a : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((a : ℂ) + T * Complex.I)))
    (hib :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          logDeriv (archimedeanGammaFactor κ) ((b : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((b : ℂ) + T * Complex.I))) :
    (∫ T : ℝ,
        logDeriv (archimedeanGammaFactor κ) ((b : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((b : ℂ) + T * Complex.I)) =
      ∫ T : ℝ,
        logDeriv (archimedeanGammaFactor κ) ((a : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((a : ℂ) + T * Complex.I) := by
  let f : ℂ → ℂ := fun s ↦
    logDeriv (archimedeanGammaFactor κ) s * mellin (logarithmicTestWeight g) s
  have hz :
    ∀ n,
      RectangleGeometry.rectangleBoundaryIntegral f ((a : ℂ) + B n * Complex.I)
          ((b : ℂ) + U n * Complex.I) =
        0 := by
    intro n
    apply mellin_archimedeanGamma_finite_contour_eq_zero_of_nonneg κ hk g hc hg
    all_goals
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
        add_zero, zero_add]
    · exact ha
    · exact hab
    · exact hBU n
  have hbdy :
    Filter.Tendsto
      (fun n ↦
        RectangleGeometry.rectangleBoundaryIntegral f ((a : ℂ) + B n * Complex.I)
          ((b : ℂ) + U n * Complex.I))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr (fun n ↦ (hz n).symm) tendsto_const_nhds
  have hv :=
    RectangleGeometry.tendsto_vertical_difference_of_boundary_limit f a b U B 0 hupper hlower hbdy
  have hi :=
    ((MeasureTheory.intervalIntegral_tendsto_integral hib hB hU).const_mul Complex.I).sub
      ((MeasureTheory.intervalIntegral_tendsto_integral hia hB hU).const_mul Complex.I)
  exact mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp (tendsto_nhds_unique hi hv))

/-- For nonnegative-real shifts, a positive vertical line and an even smooth compact
test, the gamma logarithmic derivative times the Mellin weight is integrable.
Use linear growth and cubic Mellin decay on the entire reciprocal factor, then
transfer its negative logarithmic derivative to gamma. No integrability input is needed. -/
theorem integrable_archimedeanGamma_mellin_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) (σ : ℝ) (hσ : 0 < σ) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  obtain ⟨A, hA, hb⟩ := exists_archimedeanGamma_linear_bound_on_positive_strip κ hk σ σ hσ le_rfl
  have hn : ∀ T : ℝ, inverseArchimedeanGammaFactor κ ((σ : ℂ) + T * Complex.I) ≠ 0 := by
    intro T
    apply inverseArchimedeanGammaFactor_ne_zero_of_nonneg κ hk
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσ
  have hi :=
    integrable_vertical_logDeriv_mellin (differentiable_inverseArchimedeanGammaFactor κ) σ A hA hn
      (fun T ↦ by
        rw [← norm_neg, neg_logDeriv_inverseArchimedeanGammaFactor κ (hn T)]
        exact hb σ ⟨le_rfl, le_rfl⟩ T)
      g he hc hg
  apply hi.neg.congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      simp only [Pi.neg_apply]
      rw [← neg_mul, neg_logDeriv_inverseArchimedeanGammaFactor κ (hn T)]

/-- For nonnegative-real shifts, a positive strip and an even smooth compact test,
the horizontal Mellin-gamma integrals tend to zero at heights of magnitude n+2.
Combine the uniform linear growth with quartic Mellin decay on the reciprocal
factor and transfer back to gamma. This removes the horizontal-limit premise. -/
theorem tendsto_horizontal_archimedeanGamma_mellin_zero_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (T : ℕ → ℝ) (hT : ∀ n, |T n| = (n : ℝ) + 2) :
    Filter.Tendsto
      (fun n ↦
        ∫ σ in a..b,
          logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + T n * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T n * Complex.I))
      Filter.atTop (nhds 0) := by
  obtain ⟨A, hA, hb⟩ := exists_archimedeanGamma_linear_bound_on_positive_strip κ hk a b ha hab
  have hn :
    ∀ n, ∀ σ ∈ Set.Icc a b, inverseArchimedeanGammaFactor κ ((σ : ℂ) + T n * Complex.I) ≠ 0 := by
    intro n σ hσ
    apply inverseArchimedeanGammaFactor_ne_zero_of_nonneg κ hk
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using ha.trans_le hσ.1
  have ht :=
    tendsto_horizontal_logDeriv_mellin_integral_zero (inverseArchimedeanGammaFactor κ) g he hc hg a
      b A hab hA T (fun n ↦ (hT n).ge)
      (fun n σ hσ ↦ by
        rw [← norm_neg, neg_logDeriv_inverseArchimedeanGammaFactor κ (hn n σ hσ)]
        have hh := hb σ hσ (T n)
        rw [hT n] at hh
        have hp : 1 + ((n : ℝ) + 2) ≤ ((n : ℝ) + 5) ^ 2 := by
          nlinarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        exact hh.trans (mul_le_mul_of_nonneg_left hp hA))
  have hh := ht.neg
  simp only [neg_zero] at hh
  apply hh.congr
  intro n
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro σ hσ
  have hs : σ ∈ Set.Icc a b := by
    rw [← Set.uIcc_of_le hab]
    exact hσ
  dsimp only
  rw [← neg_mul, neg_logDeriv_inverseArchimedeanGammaFactor κ (hn n σ hs)]

/-- For nonnegative-real shifts, two ordered positive vertical lines and an even
smooth compact test, the Mellin-gamma integrals agree. Choose symmetric heights,
derive integrability and horizontal decay, and pass the finite residue-free
contour to the limit. This permits moving the gamma term to the critical line
without assuming convergence or vanishing horizontal edges. -/
theorem mellin_archimedeanGamma_vertical_integral_eq_of_smooth_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) (a b : ℝ) (ha : 0 < a) (hab : a < b) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    (∫ T : ℝ,
        logDeriv (archimedeanGammaFactor κ) ((b : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((b : ℂ) + T * Complex.I)) =
      ∫ T : ℝ,
        logDeriv (archimedeanGammaFactor κ) ((a : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((a : ℂ) + T * Complex.I) := by
  let U : ℕ → ℝ := fun n ↦ (n : ℝ) + 2
  let B : ℕ → ℝ := fun n ↦ -((n : ℝ) + 2)
  have hu : Filter.Tendsto U Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun n ↦ by
        dsimp only [U]; linarith only)
      tendsto_natCast_atTop_atTop
  have hb : Filter.Tendsto B Filter.atTop Filter.atBot := Filter.tendsto_neg_atTop_atBot.comp hu
  have hpos : ∀ n : ℕ, 0 ≤ (n : ℝ) + 2 := fun n ↦ add_nonneg (Nat.cast_nonneg n) (by norm_num only)
  apply
    mellin_archimedeanGamma_vertical_integral_eq_of_nonneg κ hk g hc hg.continuous a b ha hab U B
      (fun n ↦ by
        dsimp only [B, U]
        linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      hu hb
  · exact
      tendsto_horizontal_archimedeanGamma_mellin_zero_of_nonneg κ hk a b ha hab.le g he hc hg U
        (fun n ↦ abs_of_nonneg (hpos n))
  · exact
      tendsto_horizontal_archimedeanGamma_mellin_zero_of_nonneg κ hk a b ha hab.le g he hc hg B
        (fun n ↦ by
          dsimp only [B]
          rw [abs_neg, abs_of_nonneg (hpos n)])
  · exact integrable_archimedeanGamma_mellin_of_nonneg κ hk a ha g he hc hg
  · exact integrable_archimedeanGamma_mellin_of_nonneg κ hk b (ha.trans hab) g he hc hg

/-- On a positive vertical line with nonnegative-real shifts, the conjugated gamma
derivative at negative height is the conjugate-shift factor at positive height.
Apply conjugation of the factor derivative and the line-coordinate identity.
This rewrites the dual gamma integrand without conjugating the test function. -/
theorem star_reflected_archimedeanGamma_logDeriv {d : ℕ} (κ : Fin d → ℂ) (hk : ∀ j, 0 ≤ (κ j).re)
    (σ T : ℝ) (hσ : 0 < σ) :
    star (logDeriv (archimedeanGammaFactor κ) ((σ : ℂ) + (-T) * Complex.I)) =
      logDeriv (archimedeanGammaFactor (fun j ↦ star (κ j))) ((σ : ℂ) + T * Complex.I) := by
  have hs : 0 < ((σ : ℂ) + T * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσ
  have hcoord : star ((σ : ℂ) + T * Complex.I) = (σ : ℂ) + (-T) * Complex.I := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      neg_mul]
  simpa only [hcoord] using star_logDeriv_archimedeanGammaFactor κ hk hs

/-- For nonnegative-real shifts, two ordered positive lines and an even smooth
compact test, the reflected dual Mellin-gamma integrals agree. Rewrite the dual
derivative using conjugate shifts and apply the residue-free line shift.
This moves the dual term with the same complex test weight as the original. -/
theorem mellin_reflected_archimedeanGamma_vertical_integral_eq_of_smooth_nonneg {d : ℕ}
    (κ : Fin d → ℂ) (hk : ∀ j, 0 ≤ (κ j).re) (a b : ℝ) (ha : 0 < a) (hab : a < b) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    (∫ T : ℝ,
        star (logDeriv (archimedeanGammaFactor κ) ((b : ℂ) + (-T) * Complex.I)) *
          mellin (logarithmicTestWeight g) ((b : ℂ) + T * Complex.I)) =
      ∫ T : ℝ,
        star (logDeriv (archimedeanGammaFactor κ) ((a : ℂ) + (-T) * Complex.I)) *
          mellin (logarithmicTestWeight g) ((a : ℂ) + T * Complex.I) := by
  simp_rw [star_reflected_archimedeanGamma_logDeriv κ hk b _ (ha.trans hab),
    star_reflected_archimedeanGamma_logDeriv κ hk a _ ha]
  exact
    mellin_archimedeanGamma_vertical_integral_eq_of_smooth_nonneg (fun j ↦ star (κ j))
      (fun j ↦ by simpa only [Complex.star_def, Complex.conj_re] using hk j) a b ha hab g he hc hg

end PseudoPrime.AnalyticNumberTheory.General
