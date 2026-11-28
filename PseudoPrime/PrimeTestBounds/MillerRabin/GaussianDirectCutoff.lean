/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessCutoff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Common rational scale for the direct Gaussian comparison -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common rational scale used by the direct middle and high witnesses. -/
@[expose]
public noncomputable def gaussianDirectScale : ℝ :=
  519674416 / 10 ^ 9

/-- The common squared scale fits the final Gaussian cutoff from log 42410.
The entrance exponential bound is propagated by normalized-cutoff monotonicity. -/
public theorem gaussian_direct_cutoff {L : ℝ} (hL : 42410 ≤ L) :
    (gaussianDirectScale * L) ^ 2 ≤ gaussianWitnessCutoff L := by
  have h₂ : (2 : ℝ) ≤ Real.exp (7 / 10) := by
    rw [← Real.exp_log (by norm_num only : (0 : ℝ) < 2), Real.exp_le_exp]
    exact Real.log_two_lt_d9.le.trans (by norm_num only)
  have hp : (2 : ℝ) ^ 21 ≤ Real.exp (((42410 : ℝ) / 11000) ^ 2) := by
    calc
      _ ≤ Real.exp (7 / 10) ^ (21 : ℕ) := pow_le_pow_left₀ (by norm_num only) h₂ _
      _ = Real.exp ((21 : ℕ) * (7 / 10)) := (Real.exp_natCast_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num only)
  have he : Real.exp (-(((42410 : ℝ) / 11000) ^ 2)) ≤ 1 / 2 ^ 21 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).2 hp
  have hc :=
    gaussianCell_cutoff_le (a := 42410) (c := (270061499 / 10 ^ 9 : ℝ)) (scale :=
      2 * gaussianDirectScale) (by norm_num only) hL he (by norm_num only)
      (by norm_num only [gaussianDirectScale])
  convert hc using 1
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
