/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
public import PseudoPrime.Analysis.LogTaylorBounds

import Mathlib.Analysis.Real.Pi.Bounds

/-! # Lower Lee–Nosal bound on a certified restart cell -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem log24_upper : Real.log 24 ≤ 317806 / 100000 := by
  have h :=
    PseudoPrime.Analysis.rationalLogIntervalCheck_sound
      (show
        PseudoPrime.Analysis.rationalLogIntervalCheck 24 5 20 (317804 / 100000) (317806 / 100000) =
          true
        from by decide +kernel)
  simpa only [Rat.cast_ofNat, Rat.cast_div] using h.2

private theorem coefficient24 {x l c : ℝ} (hl : l ≤ Real.log x) (hpos : 4 ≤ l) (hc : 0 ≤ c)
    (hnum : 8 * (31416 / 10000) * c ≤ l * (23 / 24 * l - 217806 / 100000)) :
    c ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hL : 0 < Real.log x := by linarith only [hl, hpos]
  have ht := Real.log_le_sub_one_of_pos (show 0 < Real.log x / 24 by linarith only [hL])
  rw [Real.log_div hL.ne' (by norm_num only : (24 : ℝ) ≠ 0)] at ht
  have hg : 23 / 24 * l - 217806 / 100000 ≤ Real.log x - Real.log (Real.log x) := by
    linarith only [hl, ht, log24_upper]
  have hm := mul_le_mul hl hg (by linarith only [hpos]) hL.le
  apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
  have hp :=
    mul_le_mul_of_nonneg_right (show Real.pi ≤ 31416 / 10000 by linarith only [Real.pi_lt_d4]) hc
  linarith only [hp, hnum, hm]

/-- A rational tangent coefficient covers a whole real cell from its entrance bound.
The supplied endpoint transfer propagates the bound to the following cell. -/
theorem theta_restart_cell (a b r : ℕ) (e f q c : ℚ) (ha : 0 < a) (hr : r ^ 2 ≤ a)
    (hq : (q : ℝ) ≤ Real.log a) (hpos : 4 ≤ q) (hc : 0 ≤ c)
    (hn : 8 * (31416 / 10000) * c ≤ q * (23 / 24 * q - 217806 / 100000)) (hw : (b : ℚ) ≤ e + c * r)
    (gain : (e : ℝ) ≤ Chebyshev.theta a → (f : ℝ) ≤ Chebyshev.theta b) :
    ThetaLowerSegment a b e f := by
  intro entry
  refine ⟨gain entry, fun x hax hxb => ?_⟩
  have hap := Nat.cast_pos (α := ℝ).mpr ha
  have hp := hap.trans_le hax
  have hs := Real.le_sqrt_of_sq_le ((show (r : ℝ) ^ 2 ≤ a by exact_mod_cast hr).trans hax)
  have hc' := (Rat.cast_nonneg (K := ℝ)).2 hc
  apply
    le_trans _
      (coefficient24 (hq.trans (Real.log_le_log hap hax)) (by exact_mod_cast hpos) hc'
        (by
          simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat] using
            (Rat.cast_le (K := ℝ)).2 hn))
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).2
  have hw' := (Rat.cast_le (K := ℝ)).2 hw
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at hw'
  linarith only [hw', mul_le_mul_of_nonneg_left hs hc', entry, hxb, Chebyshev.theta_mono hax]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
