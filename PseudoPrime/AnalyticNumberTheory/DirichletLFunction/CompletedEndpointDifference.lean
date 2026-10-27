/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedEndpointPoissonComparison
public import PseudoPrime.Analysis.PoissonEndpointDifference

/-! # Completed real-axis difference quotients controlled by endpoint zero mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal individual-RH data at q>=2 and h>0, the real
completed logarithmic-derivative difference from 1 to 1+h divided by h is at most
2/(1+2h) times the centered endpoint value. Rearrange the positive Poisson comparison
before dividing. This avoids separate inverse-gap bounds for the two derivatives. -/
theorem completedLogDeriv_endpoint_difference_div_gap_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {h : ℝ} (hh : 0 < h) :
    ((logDeriv χ.completedLFunction 1).re - (logDeriv χ.completedLFunction ((1 + h : ℝ) : ℂ)).re) /
        h ≤
      (2 / (1 + 2 * h)) * ((logDeriv χ.completedLFunction 1).re + Real.log q / 2) := by
  have hd : 0 < 1 + 2 * h := by linarith only [hh]
  have he := completedLogDeriv_endpoint_le_shifted hq hRH hp hne hinv hh.le
  have hr :
    ((logDeriv χ.completedLFunction 1).re - (logDeriv χ.completedLFunction ((1 + h : ℝ) : ℂ)).re) *
        (1 + 2 * h) ≤
      2 * h * ((logDeriv χ.completedLFunction 1).re + Real.log q / 2) := by
    nlinarith only [he]
  have hv := (le_div_iff₀ hd).mpr hr
  have ha (v : ℝ) : 2 * h * v / (1 + 2 * h) = (2 / (1 + 2 * h) * v) * h := by ring
  rw [ha] at hv
  exact (div_le_iff₀ hh).mpr hv

/-- Under primitive nonprincipal individual RH and positive h, any nonnegative
weight z gives a normalized bound for the coupled conductor and two real derivatives.
Apply the scalar signed-difference inequality to the Poisson endpoint comparison.
At z=x^(-h), this controls the pole and left contour without Euler bounds at 1+h. -/
theorem completedLogDeriv_endpoint_weighted_gap_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {h : ℝ} (hh : 0 < h) (z : ℝ) (hz : 0 ≤ z) :
    ((1 - z) * Real.log q + (logDeriv χ.completedLFunction 1).re -
          z * (logDeriv χ.completedLFunction ((1 + h : ℝ) : ℂ)).re) /
        h ≤
      ((1 - z) / h) * Real.log q / 2 +
        (((1 - z) / h + 2) / (1 + 2 * h)) *
          ((logDeriv χ.completedLFunction 1).re + Real.log q / 2) := by
  exact
    Analysis.poisson_endpoint_weighted_gap_le hh _ _ _ z hz
      (completedLogDeriv_endpoint_le_shifted hq hRH hp hne hinv hh.le)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
