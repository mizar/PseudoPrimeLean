/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevRemainder43
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
import PseudoPrime.Analysis.NumericalLogBounds

/-! # The logarithmic gap above the Chebyshev main term -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The logarithmic numerator of the difference between the target envelope
and the normalized Chebyshev main term, evaluated at logarithmic scale `L`. -/
noncomputable def chebyshevGap (L : ℝ) : ℝ :=
  3 * L * Real.log L - 8 * L - 4 * (Real.log L) ^ 2 + 8 * Real.log L - 8 * Real.log (2 * Real.pi)

/-- The logarithm of 43 lies between `15/4` and `19/5`. A rational Taylor
certificate supplies both bounds without introducing a zero-count table. -/
theorem log43_bounds : (15 / 4 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ 19 / 5 := by
  have h :=
    Analysis.preciseLogCheck_sound (N := 43) (j := 5) (n := 32) (lo := 15 / 4) (hi := 19 / 5)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- For positive scales above 43, the logarithm is at most one fifth of the
scale. Compare the logarithm with the square root, then square the bound. -/
theorem log_le_scale_fifth {L : ℝ} (hL : 43 ≤ L) : Real.log L ≤ L / 5 := by
  have hp : 0 < L := by linarith only [hL]
  have hs := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg L
  have hlog := Analysis.log_le_sqrt_of_pos hp
  have ht : Real.sqrt L ≤ L / 5 := by nlinarith only [hL, hs, hs0]
  exact hlog.trans ht

/-- At every positive scale, differentiate the logarithmic gap term by term.
The displayed derivative is used to show monotonicity beyond 43. -/
theorem chebyshevGap_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt chebyshevGap (3 * Real.log x - 5 + 8 * (1 - Real.log x) / x) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hi := hasDerivAt_id x
  have h1 := ((hi.const_mul 3).mul hl).sub (hi.const_mul 8)
  have h2 := (h1.sub ((hl.pow 2).const_mul 4)).add (hl.const_mul 8)
  have h := h2.sub_const (8 * Real.log (2 * Real.pi))
  convert h using 1
  · funext t
    rfl
  · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
    ring

/-- The logarithmic gap has a positive derivative from 43 onward. The lower
bound on `log x` and the upper bound on `log x / x` leave a positive margin. -/
theorem chebyshevGap_deriv_pos {x : ℝ} (hx : 43 ≤ x) :
    0 < 3 * Real.log x - 5 + 8 * (1 - Real.log x) / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hlow := log43_bounds.1.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 43) hx)
  have hupper := log_le_scale_fifth hx
  have hd : Real.log x / x ≤ 1 / 5 := by
    apply (div_le_iff₀ hx0).2
    linarith only [hupper]
  have hi : 0 ≤ 1 / x := div_nonneg (by norm_num only) hx0.le
  have heq : 8 * (1 - Real.log x) / x = 8 * (1 / x) - 8 * (Real.log x / x) := by ring
  rw [heq]
  linarith only [hd, hi, hlow]

/-- At the starting scale 43, the explicit logarithmic gap is at least
`9599/100`. Apply the certified logarithm interval and `log (2π) < 2`. -/
theorem chebyshevGap_start : (9599 / 100 : ℝ) ≤ chebyshevGap 43 := by
  have h := log43_bounds
  have hc := Analysis.log_two_mul_pi_lt
  have hs : Real.log 43 ^ 2 ≤ (19 / 5 : ℝ) ^ 2 := by nlinarith only [h.1, h.2]
  unfold chebyshevGap
  norm_num only at hc hs ⊢
  linarith only [h.1, hc, hs]

/-- The logarithmic gap is at least `9599/100` at every scale `L ≥ 43`.
The positive derivative makes the gap increasing from its certified start. -/
theorem chebyshevGap_lower {L : ℝ} (hL : 43 ≤ L) : (9599 / 100 : ℝ) ≤ chebyshevGap L := by
  have hc : ContinuousOn chebyshevGap (Set.Ici 43) := by
    intro x hx
    have hx0 : 0 < x := by
      change 43 ≤ x at hx
      linarith only [hx]
    exact (chebyshevGap_deriv hx0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ interior (Set.Ici (43 : ℝ)), 0 < deriv chebyshevGap x := by
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : 0 < x := by linarith only [hx]
    rw [(chebyshevGap_deriv hx0).deriv]
    exact chebyshevGap_deriv_pos hx.le
  have hm := (strictMonoOn_of_deriv_pos (convex_Ici (43 : ℝ)) hc hd).monotoneOn
  exact chebyshevGap_start.trans (hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hL) hL)

/-- Above 43, the Chebyshev main bound plus `101/100` is at most the target
logarithmic envelope minus `11/4`. The certified positive gap supplies the
margin after division by `8π`. -/
theorem chebyshev_main_le_envelope {L : ℝ} (hL : 43 ≤ L) :
    ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        101 / 100 ≤
      L * (L - Real.log L) / (8 * Real.pi) - 11 / 4 := by
  have hg := chebyshevGap_lower hL
  have hp : Real.pi < (22 / 7 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h ⊢
    linarith only [h]
  have hdiv : (94 / 25 : ℝ) ≤ chebyshevGap L / (8 * Real.pi) := by
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

/-- Under RH and the stated Rosser-type positive-height zero-count bound,
the Chebyshev error at `exp L`, for `L ≥ 43`, lies below the target envelope
with an additional `11/4` times the square-root scale of margin. The count
estimate remains an explicit hypothesis. -/
theorem psi_error_envelope43 (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.exp (L / 2) * (L * (L - Real.log L) / (8 * Real.pi) - 11 / 4) := by
  have h := (psi_error_main_43 hRH hL hQ).trans (chebyshev_main_le_envelope hL)
  have hp := Real.exp_pos (L / 2)
  have hm := (div_le_iff₀ hp).1 h
  nlinarith only [hm]

/-- Under RH and the stated Rosser-type zero-count hypothesis, for positive
`x` with `log x ≥ 43`, the Chebyshev error lies below the target envelope
minus `11/4` times `sqrt x`. Substitute `L = log x` in the scale theorem. -/
theorem psi_error_envelope_of_log (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : 43 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 11 / 4) := by
  have h := psi_error_envelope43 hRH hL hQ
  have hs : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Real.exp_log hx, hs] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
