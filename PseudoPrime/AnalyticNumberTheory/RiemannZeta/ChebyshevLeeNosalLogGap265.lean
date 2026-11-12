/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevGap43
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Lee–Nosal envelope comparison from logarithmic height twenty-six and one half -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A rational logarithm certificate bounds `log (2π)` by `37/20`. -/
private theorem log_two_pi_le_thirty_seven_twentieths : Real.log (2 * Real.pi) ≤ (37 / 20 : ℝ) := by
  have hc :=
    Analysis.preciseLogCheck_sound (N := (44 / 7 : ℚ)) (j := 3) (n := 32) (lo := 183 / 100) (hi :=
      37 / 20) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  have hp : 2 * Real.pi ≤ (44 / 7 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h
    linarith only [h]
  exact (Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hp).trans hc.2

/-- A rational logarithm certificate encloses log 53/2 between 3277/1000 and 3278/1000.
This is used to bound the gap at the beginning of the range. -/
private theorem log265_bounds :
    (3277 / 1000 : ℝ) ≤ Real.log (53 / 2 : ℝ) ∧ Real.log (53 / 2 : ℝ) ≤ 3278 / 1000 := by
  have h :=
    Analysis.preciseLogCheck_sound (N := (53 / 2 : ℚ)) (j := 5) (n := 32) (lo := 3277 / 1000) (hi :=
      3278 / 1000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  constructor <;> linarith only [h.1, h.2]

/-- Above 53/2, the logarithm is bounded by one fifth of the scale. -/
private theorem log_le_scale_fifth265 {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) : Real.log L ≤ L / 5 := by
  have hp : 0 < L := by linarith only [hL]
  have hs := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg L
  have hlog := Analysis.log_le_sqrt_of_pos hp
  have ht : Real.sqrt L ≤ L / 5 := by nlinarith only [hL, hs, hs0]
  exact hlog.trans ht

/-- The derivative of the logarithmic gap is positive from 53/2 onward. -/
private theorem chebyshevGap_deriv_pos265 {x : ℝ} (hx : (53 / 2 : ℝ) ≤ x) :
    0 < 3 * Real.log x - 5 + 8 * (1 - Real.log x) / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hlow :=
    log265_bounds.1.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < (53 / 2 : ℝ)) hx)
  have hupper := log_le_scale_fifth265 hx
  have hd : Real.log x / x ≤ 1 / 5 := by
    apply (div_le_iff₀ hx0).2
    linarith only [hupper]
  have hi : 0 ≤ 1 / x := div_nonneg (by norm_num only) hx0.le
  have heq : 8 * (1 - Real.log x) / x = 8 * (1 / x) - 8 * (Real.log x / x) := by ring
  rw [heq]
  linarith only [hd, hi, hlow]

/-- At the starting scale 53/2, the explicit logarithmic gap is at least
`167/10`. Apply the certified logarithm interval and `log (2π) ≤ 37/20`. -/
private theorem chebyshevGap_start265 : (167 / 10 : ℝ) ≤ chebyshevGap (53 / 2 : ℝ) := by
  have h := log265_bounds
  have hc := log_two_pi_le_thirty_seven_twentieths
  have hs : Real.log (53 / 2 : ℝ) ^ 2 ≤ (3278 / 1000 : ℝ) ^ 2 := by nlinarith only [h.1, h.2]
  unfold chebyshevGap
  norm_num only at hc hs ⊢
  linarith only [h.1, hc, hs]

/-- The logarithmic gap is nondecreasing from 53/2 onward. Its derivative is
positive on the interior, so later envelope comparisons can share this fact. -/
theorem chebyshevGap_monotone265 : MonotoneOn chebyshevGap (Set.Ici (53 / 2 : ℝ)) := by
  have hc : ContinuousOn chebyshevGap (Set.Ici (53 / 2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := by
      change (53 / 2 : ℝ) ≤ x at hx
      linarith only [hx]
    exact (chebyshevGap_deriv hx0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ interior (Set.Ici (53 / 2 : ℝ)), 0 < deriv chebyshevGap x := by
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : 0 < x := by linarith only [hx]
    rw [(chebyshevGap_deriv hx0).deriv]
    exact chebyshevGap_deriv_pos265 hx.le
  exact (strictMonoOn_of_deriv_pos (convex_Ici (53 / 2 : ℝ)) hc hd).monotoneOn

/-- The logarithmic gap is at least `167/10` at every scale `L ≥ 53/2`.
Monotonicity propagates the certified starting bound. -/
private theorem chebyshevGap_lower265 {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    (167 / 10 : ℝ) ≤ chebyshevGap L := by
  exact
    chebyshevGap_start265.trans
      (chebyshevGap_monotone265 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hL) hL)

/-- Above 53/2, the Chebyshev main bound plus `33/50` is at most the target
logarithmic envelope. The certified positive gap supplies the
margin after division by `8π`. -/
theorem chebyshev_main_le_envelope265 {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        33 / 50 ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hg := chebyshevGap_lower265 hL
  have hp : Real.pi < (22 / 7 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h ⊢
    linarith only [h]
  have hdiv : (33 / 50 : ℝ) ≤ chebyshevGap L / (8 * Real.pi) := by
    apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [hg, hp]
  have heq :
    ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        chebyshevGap L / (8 * Real.pi) =
      L * (L - Real.log L) / (8 * Real.pi) := by
    unfold chebyshevGap
    ring
  linarith only [hdiv, heq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
