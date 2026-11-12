/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogGap265
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Lee–Nosal envelope margin from logarithmic height thirty-six -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A certified logarithm bound sharpens the numerical constant in the gap. -/
private theorem log_two_pi_le_nineteen_tenths : Real.log (2 * Real.pi) ≤ (19 / 10 : ℝ) := by
  have h13 :=
    Analysis.preciseLogCheck_sound (N := 13) (j := 4) (n := 32) (lo := 256 / 100) (hi := 257 / 100)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h13
  have hp : 2 * Real.pi ≤ (13 / 2 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h
    linarith only [h]
  have hlog := Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hp
  have hsplit : Real.log (13 / 2 : ℝ) = Real.log 13 - Real.log 2 := by
    rw [Real.log_div (by norm_num only) (by norm_num only)]
  rw [hsplit] at hlog
  have h2 := Real.log_two_gt_d9
  norm_num only at h2
  linarith only [hlog, h13.2, h2]

/-- Rational bounds for log 36 provide the initial gap certificate. -/
private theorem log36_bounds : (358 / 100 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ 359 / 100 := by
  have h :=
    Analysis.preciseLogCheck_sound (N := 36) (j := 6) (n := 32) (lo := 358 / 100) (hi := 359 / 100)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  constructor
  · linarith only [h.1]
  · exact h.2

/-- At the starting scale 36, the explicit logarithmic gap is at least
`60`. Apply the certified logarithm interval and `log (2π) ≤ 19/10`. -/
private theorem chebyshevGap_start36 : (60 : ℝ) ≤ chebyshevGap 36 := by
  have h := log36_bounds
  have hc := log_two_pi_le_nineteen_tenths
  have hs : Real.log 36 ^ 2 ≤ (359 / 100 : ℝ) ^ 2 := by nlinarith only [h.1, h.2]
  unfold chebyshevGap
  norm_num only at hc hs ⊢
  linarith only [h.1, hc, hs]

/-- The logarithmic gap is at least `60` at every scale `L ≥ 36`.
The positive derivative makes the gap increasing from its certified start. -/
private theorem chebyshevGap_lower36 {L : ℝ} (hL : 36 ≤ L) : (60 : ℝ) ≤ chebyshevGap L := by
  have h265 : (53 / 2 : ℝ) ≤ L := by linarith only [hL]
  exact
    chebyshevGap_start36.trans
      (chebyshevGap_monotone265 (Set.mem_Ici.mpr (by norm_num only)) (Set.mem_Ici.mpr h265) hL)

/-- Above 36, the Chebyshev main bound plus `33/50` is at most the target
logarithmic envelope minus `8/5`. The certified positive gap supplies the
margin after division by `8π`. -/
theorem chebyshev_main_le_envelope36 {L : ℝ} (hL : 36 ≤ L) :
    ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        33 / 50 ≤
      L * (L - Real.log L) / (8 * Real.pi) - 8 / 5 := by
  have hg := chebyshevGap_lower36 hL
  have hp : Real.pi < (22 / 7 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h ⊢
    linarith only [h]
  have hdiv : (113 / 50 : ℝ) ≤ chebyshevGap L / (8 * Real.pi) := by
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
