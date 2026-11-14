/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeCurvature
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Retaining the negative cutoff contribution in the initial midrange -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- In the first two phase blocks, canonical smoothing has relative width at
least 7/2000. A rational logarithm check bounds `sqrt x` above by 1025. -/
theorem midrange_delta_lower {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1386 / 100 : ℝ)) :
    (7 / 2000 : ℝ) ≤ (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 1025 10 64 (6932 / 1000) (6933 / 1000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((1025 : ℝ) ^ 2) = 2 * Real.log 1025 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxupper : x ≤ (1025 : ℝ) ^ 2 := by
    apply (Real.log_le_log_iff hx (by norm_num only : (0 : ℝ) < (1025 : ℝ) ^ 2)).mp
    linarith only [hL, hc.1, he]
  have hsupper : s ≤ 1025 := by nlinarith only [hs, hs2, hxupper]
  have hq : (18 / 5 : ℝ) ≤ q := by
    dsimp only [q]
    apply (le_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    have hll := log_million_lower ha
    nlinarith only [hll, Real.pi_lt_d4]
  change _ ≤ q / s
  apply (le_div_iff₀ hs).2
  linarith only [hq, hsupper]

/-- The signed cutoff contribution supplies at least 21/32000 when the
relative width is at least 7/2000. -/
theorem midrange_cutoff_gain {δ : ℝ} (hd : (7 / 2000 : ℝ) ≤ δ) :
    (21 / 32000 : ℝ) ≤ (1 + δ) * ((3 / 8 : ℝ) / (2 / δ)) := by
  have he : (1 + δ) * ((3 / 8 : ℝ) / (2 / δ)) = (1 + δ) * (3 * δ / 16) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he]
  nlinarith only [hd, sq_nonneg δ]

/-- Under RH and the stated height-100 zero hypotheses, the initial midrange
ψ bound retains an explicit negative cutoff gain and a rational curvature bound. -/
theorem psi_midrange_signed (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1386 / 100 : ℝ)) :
    let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
            ((1 + δ / 4) * (127 / 250) + 527 / 250000) +
            (1 + δ) *
              (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) +
                      2) /
                    (2 * Real.pi) -
                  143 / 125 +
                1 / (15 * (2 / δ) ^ 2)) -
          21 / 32000 +
        1 / (x * δ * Real.sqrt x) := by
  dsimp only
  let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
  have hd : (7 / 2000 : ℝ) ≤ δ := midrange_delta_lower ha hL
  have hg := midrange_cutoff_gain hd
  have hp := psi_midrange_curvature hRH g hmono hpos hheight hzero hcount hl hu ha hL
  dsimp only at hp
  dsimp only [δ] at hg
  nlinarith only [hp, hg]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
