/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEnvelopeBounds
public import PseudoPrime.Analysis.HighPrecisionLogBounds

/-! # Rational local envelope checks -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check that the common local envelope at rational scale `s` is at most `U`.
Below 25 the checker uses the plain square and moderate guard; above 25 it checks a
logarithm lower bound `lo` at binary scale `j` and uses the finer logarithmic radius. -/
def localEnvelopeUpperCheck (s lo U : ℚ) (j : ℕ) : Bool :=
  if s ≤ 25 then decide (min (s ^ 2) (max 61 ((81 / 100) * s ^ 2)) ≤ U)
  else
    decide
      (Analysis.fineLogCheck s j 64 lo (lo + 1) = true ∧
        min (s ^ 2) ((s - 2 * lo + 45571 / 10000) ^ 2) ≤ U)

/-- A successful rational local upper check bounds the real local envelope by `U`.
The low-scale case casts the checked quadratic budget; the high-scale case combines
the certified logarithm lower bound with the nonnegative finer radius. -/
theorem localEnvelopeUpperCheck_sound {s lo U : ℚ} {j : ℕ}
    (h : localEnvelopeUpperCheck s lo U j = true) : localFullEnvelope (s : ℝ) ≤ (U : ℝ) := by
  by_cases hs : s ≤ 25
  · have hc : min (s ^ 2) (max 61 ((81 / 100) * s ^ 2)) ≤ U := by
      apply of_decide_eq_true
      simpa only [localEnvelopeUpperCheck, ite_eq_left hs] using h
    have hsR : (s : ℝ) ≤ 25 := by exact_mod_cast hs
    have hb := (Rat.cast_le (K := ℝ)).mpr hc
    simp only [Rat.cast_min, Rat.cast_max, Rat.cast_pow, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat] at hb
    exact (local_full_le_low hsR).trans hb
  · have hc :
      Analysis.fineLogCheck s j 64 lo (lo + 1) = true ∧
        min (s ^ 2) ((s - 2 * lo + 45571 / 10000) ^ 2) ≤ U := by
      apply of_decide_eq_true
      simpa only [localEnvelopeUpperCheck, ite_eq_right hs] using h
    have hsR : (25 : ℝ) ≤ s := by exact_mod_cast (le_of_not_ge hs)
    have hlog := (Analysis.fineLogCheck_sound hc.1).1
    have hf : (0 : ℝ) ≤ Analysis.finerPart2CutoffRoot s := by
      have hfr :=
        Analysis.finerPart2Root_ge_36_5_of_639_100_le (L := (s : ℝ)) (by linarith only [hsR])
      linarith only [hfr]
    have hupper : Analysis.finerPart2CutoffRoot s ≤ (s : ℝ) - 2 * (lo : ℝ) + 45571 / 10000 := by
      dsimp only [Analysis.finerPart2CutoffRoot]
      linarith only [hlog]
    have hsq := pow_le_pow_left₀ hf hupper 2
    have hb := (Rat.cast_le (K := ℝ)).mpr hc.2
    simp only [Rat.cast_min, Rat.cast_pow, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat] at hb
    exact (le_min (local_full_le_sq s) ((local_full_le_finer hsR).trans hsq)).trans hb

end PseudoPrime.PrimeTestBounds.MillerRabin
