/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLog235Numerics
import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Lee–Nosal logarithmic gap from 23.5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The dimensionless gap between the Lee–Nosal envelope and the main term
for the smoothing width `5L/(6π)`. Its positivity is propagated from `47/2`
using its derivative. -/
noncomputable def leeNosalGap235 (L : ℝ) : ℝ :=
  4 * L * Real.log (5 * L / 6) - L * Real.log L - (22 / 3 : ℝ) * L - 4 * Real.log (5 * L / 6) ^ 2 +
      8 * Real.log (5 * L / 6) -
    8

/-- At a positive scale, the logarithmic gap has the displayed derivative.
Differentiate both logarithms and simplify using the nonzero scale. -/
theorem leeNosalGap235_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt leeNosalGap235
      (4 * Real.log (5 * x / 6) - Real.log x - 13 / 3 + 8 * (1 - Real.log (5 * x / 6)) / x) x := by
  have hx' : (5 : ℝ) * x / 6 ≠ 0 :=
    ne_of_gt (div_pos (mul_pos (by norm_num only) hx) (by norm_num only))
  have harg := (((hasDerivAt_id x).const_mul 5).div_const 6).log hx'
  have hl := Real.hasDerivAt_log hx.ne'
  have h :=
    ((((((((hasDerivAt_id x).const_mul 4).mul harg).sub ((hasDerivAt_id x).mul hl)).sub
                  ((hasDerivAt_id x).const_mul (22 / 3))).sub
              ((harg.pow 2).const_mul 4)).add
          (harg.const_mul 8)).sub_const
      8)
  convert h using 1
  · funext y
    rfl
  · dsimp only [id_eq]
    have hc := mul_inv_cancel₀ hx.ne'
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination (-3 : ℝ) * hc

/-- The gap derivative is positive from `47/2` onward. Bounds on `log x / x`
and `log(6/5)` make the comparison uniform on the entire half-line. -/
private theorem gap_deriv_pos {x : ℝ} (hx : (47 / 2 : ℝ) ≤ x) :
    0 < 4 * Real.log (5 * x / 6) - Real.log x - 13 / 3 + 8 * (1 - Real.log (5 * x / 6)) / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hlow :=
    log_47_div_two_bounds.1.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 47 / 2) hx)
  have hs := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  have hlog := Analysis.log_le_sqrt_of_pos hx0
  have hupper : Real.log x ≤ x / 4 := by
    have h : Real.sqrt x ≤ x / 4 := by nlinarith only [hx, hs, hs0]
    exact hlog.trans h
  have hdiv : Real.log x / x ≤ 1 / 4 := by
    apply (div_le_iff₀ hx0).2
    linarith only [hupper]
  have hd0 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num only)
  have hd1 : Real.log (6 / 5 : ℝ) ≤ 1 / 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 6 / 5)
    linarith only [h]
  have heq : Real.log (5 * x / 6) = Real.log x - Real.log (6 / 5 : ℝ) := by
    have h : 5 * x / 6 = x / (6 / 5 : ℝ) := by ring
    rw [h, Real.log_div hx0.ne' (by norm_num only)]
  rw [heq]
  have hi : 0 ≤ 1 / x := div_nonneg (by norm_num only) hx0.le
  have hdi : 0 ≤ Real.log (6 / 5 : ℝ) / x := div_nonneg hd0 hx0.le
  have hform :
    8 * (1 - (Real.log x - Real.log (6 / 5 : ℝ))) / x =
      8 * (1 / x) - 8 * (Real.log x / x) + 8 * (Real.log (6 / 5 : ℝ) / x) := by
    ring
  rw [hform]
  linarith only [hlow, hdiv, hd1, hi, hdi]

/-- The logarithmic gap is nondecreasing from `47/2` onward, since its
explicit derivative is positive on the interior of that half-line. -/
theorem leeNosalGap235_monotone : MonotoneOn leeNosalGap235 (Set.Ici (47 / 2 : ℝ)) := by
  have hc : ContinuousOn leeNosalGap235 (Set.Ici (47 / 2 : ℝ)) := by
    intro x hx
    change (47 / 2 : ℝ) ≤ x at hx
    exact (leeNosalGap235_deriv (by linarith only [hx])).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ interior (Set.Ici (47 / 2 : ℝ)), 0 < deriv leeNosalGap235 x := by
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(leeNosalGap235_deriv (by linarith only [hx])).deriv]
    exact gap_deriv_pos hx.le
  exact (strictMonoOn_of_deriv_pos (convex_Ici (47 / 2 : ℝ)) hc hd).monotoneOn

/-- At the first scale the gap exceeds `13499/1000`. This is a rational
consequence of the two checked logarithm enclosures. -/
private theorem gap_start : (13499 / 1000 : ℝ) ≤ leeNosalGap235 (47 / 2 : ℝ) := by
  have h := log_47_div_two_bounds
  have hb := log_235_div_twelve_bounds
  have hs : Real.log (235 / 12 : ℝ) ^ 2 ≤ (2974679 / 1000000 : ℝ) ^ 2 := by
    nlinarith only [hb.1, hb.2]
  unfold leeNosalGap235
  norm_num only at ⊢
  nlinarith only [h.2, hb.1, hs]

/-- On the half-line `L ≥ 47/2`, the selected main term plus `537/1000`
is below the Lee–Nosal envelope. The margin leaves `7/1000` above the
reciprocal-sum constant `53/100`. -/
theorem chebyshev_main_le_envelope235 {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    ((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2 + 5 * L / 6) /
          (2 * Real.pi) +
        537 / 1000 ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hg :=
    gap_start.trans (leeNosalGap235_monotone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hL) hL)
  have hp : Real.pi < (314160 / 100000 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hdiv : (537 / 1000 : ℝ) ≤ leeNosalGap235 L / (8 * Real.pi) := by
    apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [hg, hp]
  have heq :
    ((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2 + 5 * L / 6) /
          (2 * Real.pi) +
        leeNosalGap235 L / (8 * Real.pi) =
      L * (L - Real.log L) / (8 * Real.pi) := by
    unfold leeNosalGap235
    ring
  linarith only [hdiv, heq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
