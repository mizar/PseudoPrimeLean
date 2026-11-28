/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseInterpolation644
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds

/-! # Curvature bound on the 29 certified ordinate brackets -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem ordinate_lower_pos (i : Fin 29) :
    0 < (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ) := by
  have h : ∀ j : Fin 29, 0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower j := by decide +kernel
  exact Rat.cast_pos.mpr (h i)

private theorem phase_budget_sum :
    2 * (∑ i : Fin 29, quarterPhaseBudget644 (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i)) ≤
      28.424 := by
  norm_num only [quarterPhaseBudget644, Fin.sum_univ_succ, Fin.sum_univ_zero,
    AnalyticNumberTheory.RiemannZeta.lowZero100Lower, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Rat.cast_div, Rat.cast_ofNat,
    Finset.sum_range_succ, Finset.sum_range_zero, quarterPhaseCoeff644, Nat.factorial,
    Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, ite_true, ite_false]

/-- The low-zero phase curvature is at most 28.424 for every choice of
ordinates in the certified brackets. The sum uses the separate lower
endpoint of each bracket and the phase kernel's rational norm envelope. -/
theorem quarter_phase_curvature_644 {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) :
    2 * (∑ i : Fin 29, (g i) ^ 2 * ‖quarterPhaseKernel644 (g i)‖) ≤ 28.424 := by
  apply le_trans _ phase_budget_sum
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ ?_)) (by norm_num only)
  have hp := ordinate_lower_pos i
  have he :=
    quarter_phase_norm_budget_644 hp
      (show (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ) ≤ |g i|
        by
        rw [abs_of_pos (hp.trans_le (hg i))]
        exact hg i)
  rw [abs_of_pos (hp.trans_le (hg i)), mul_comm] at he
  exact he

/-- On a positive radius interval, the certified curvature bound carries
endpoint phase bounds to every complete height truncation. The interpolation
width is measured in the coordinate twice the logarithm of the radius. -/
theorem quarter_phase_radius_interval_644 (hRH : RiemannHypothesis) :
    ∃ g : Fin 29 → ℝ,
      AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g ∧
        AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g ∧
        ∀ {a b r B T : ℝ},
          0 < a →
            a < b →
            r ∈ Set.Icc a b →
            100 ≤ T →
            B ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log a) →
            B ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log b) →
            B - 28.424 * (2 * Real.log b - 2 * Real.log a) ^ 2 / 8 - 0.0061952 ≤
              ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
                (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
                  (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                      quarterPhaseKernel644 ρ.im).re := by
  obtain ⟨g, hlo, hhi, hinterp⟩ := quarter_phase_interval_644 hRH
  refine ⟨g, hlo, hhi, ?_⟩
  intro a b r B T ha hab hr hT hleft hright
  have hlog := Real.log_lt_log ha hab
  exact
    hinterp (by linarith only [hlog])
      ⟨by linarith only [Real.log_le_log ha hr.1], by
        linarith only [Real.log_le_log (ha.trans_le hr.1) hr.2]⟩
      (by norm_num only) hT (quarter_phase_curvature_644 hlo) hleft hright

end PseudoPrime.PrimeTestBounds.MillerRabin
