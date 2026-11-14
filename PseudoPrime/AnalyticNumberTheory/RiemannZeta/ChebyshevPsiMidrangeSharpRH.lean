/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeScaleRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiFirstTwoSharpRH

/-! # Sharper canonical smoothing on the initial midrange -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A small relative smoothing width places both midpoint logarithms in the
first two phase blocks when `13.815 ≤ log x ≤ 13.86`. -/
theorem midrange_midpoints_sharp {x δ : ℝ} (hx : 0 < x) (hd : 0 ≤ δ) (hu : δ ≤ 1 / 200)
    (hl : (13815 / 1000 : ℝ) ≤ Real.log x) (hh : Real.log x ≤ (1386 / 100 : ℝ)) :
    Real.log ((x - x * δ + x) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (6933 / 500 : ℝ) ∧
      Real.log ((x + (x + x * δ)) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (6933 / 500 : ℝ) := by
  have hlog := midpoint_log_bounds hd hu
  have hm : 0 < 1 - δ / 2 := by linarith only [hu]
  have hp : 0 < 1 + δ / 2 := by linarith only [hd]
  have hm0 : Real.log (1 - δ / 2) ≤ 0 := Real.log_nonpos hm.le (by linarith only [hd])
  have hp0 : 0 ≤ Real.log (1 + δ / 2) := Real.log_nonneg (by linarith only [hd])
  have he1 : (x - x * δ + x) / 2 = x * (1 - δ / 2) := by ring
  have he2 : (x + (x + x * δ)) / 2 = x * (1 + δ / 2) := by ring
  rw [he1, he2, Real.log_mul hx.ne' hm.ne', Real.log_mul hx.ne' hp.ne']
  constructor <;> constructor <;> linarith only [hl, hh, hlog.1, hlog.2, hm0, hp0]

/-- Under RH and the stated height-100 zero hypotheses, the sharper first two
phase blocks apply to canonical smoothing when `10^6 ≤ x` and `log x ≤ 13.86`.
The smoothing cutoff and midpoint hypotheses follow from these bounds. -/
theorem psi_midrange_canonical_sharp (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1386 / 100 : ℝ)) :
    let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * (127 / 250) + 3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * Real.sqrt x) := by
  dsimp only
  let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hc := midrange_scale_conditions ha (show Real.log x ≤ (1423 / 100 : ℝ) by linarith only [hL])
  change 0 < δ ∧ δ ≤ 1 / 200 ∧ 1 < x - x * δ ∧ 100 ≤ 2 / δ at hc
  have hm := midrange_midpoints_sharp hx hc.1.le hc.2.1 (log_million_lower ha) hL
  exact
    psi_error_first_two_sharp_scale hRH g hmono hpos hheight hzero hcount hl hu hx hc.1
      (by linarith only [hc.2.1]) hc.2.2.1 hc.2.2.2 hm.1 hm.2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
