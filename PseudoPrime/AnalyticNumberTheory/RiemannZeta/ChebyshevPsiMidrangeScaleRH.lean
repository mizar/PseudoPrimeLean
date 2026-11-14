/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiFirstFiveBlocksRH
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Canonical smoothing on the first midrange phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `x ≥ 10^6`, the logarithm of `x` is at least 13.815. A rational
Taylor certificate for `log 10` supplies the endpoint bound. -/
theorem log_million_lower {x : ℝ} (hx : 1000000 ≤ x) : (13815 / 1000 : ℝ) ≤ Real.log x := by
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 10 3 64 (23025 / 10000) (23027 / 10000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hlog : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
    have he : (1000000 : ℝ) = 10 ^ 6 := by norm_num only
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 1000000) hx
  linarith only [hc.1, hlog, hm]

/-- For `0 ≤ δ ≤ 1/200`, the logarithms of the two midpoint factors are
bounded by explicit small rational constants. -/
theorem midpoint_log_bounds {δ : ℝ} (hd : 0 ≤ δ) (hu : δ ≤ 1 / 200) :
    -(31 / 10000 : ℝ) ≤ Real.log (1 - δ / 2) ∧ Real.log (1 + δ / 2) ≤ (3 / 1000 : ℝ) := by
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (997 / 1000) 0 12 (-31 / 10000) 0 = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Rat.cast_zero] at hc
  have h1 : (997 / 1000 : ℝ) ≤ 1 - δ / 2 := by linarith only [hu]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 997 / 1000) h1
  have hp : 0 < 1 + δ / 2 := by linarith only [hd]
  have ht := Real.log_le_sub_one_of_pos hp
  constructor
  · linarith only [hc.1, hl]
  · linarith only [ht, hu]

/-- For the first five phase blocks, the hypotheses on both midpoint logarithms
follow from the stated bounds on `log x` and the relative width. -/
theorem midrange_midpoints {x δ : ℝ} (hx : 0 < x) (hd : 0 ≤ δ) (hu : δ ≤ 1 / 200)
    (hl : (13815 / 1000 : ℝ) ≤ Real.log x) (hh : Real.log x ≤ (1423 / 100 : ℝ)) :
    Real.log ((x - x * δ + x) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7119 / 500 : ℝ) ∧
      Real.log ((x + (x + x * δ)) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7119 / 500 : ℝ) := by
  have hlog := midpoint_log_bounds hd hu
  have hm : 0 < 1 - δ / 2 := by linarith only [hu]
  have hp : 0 < 1 + δ / 2 := by linarith only [hd]
  have hm0 : Real.log (1 - δ / 2) ≤ 0 := Real.log_nonpos hm.le (by linarith only [hd])
  have hp0 : 0 ≤ Real.log (1 + δ / 2) := Real.log_nonneg (by linarith only [hd])
  have he1 : (x - x * δ + x) / 2 = x * (1 - δ / 2) := by ring
  have he2 : (x + (x + x * δ)) / 2 = x * (1 + δ / 2) := by ring
  rw [he1, he2, Real.log_mul hx.ne' hm.ne', Real.log_mul hx.ne' hp.ne']
  constructor <;> constructor <;> linarith only [hl, hh, hlog.1, hlog.2, hm0, hp0]

/-- The canonical relative width `5 log x / (6π sqrt x)` is positive and at
most `1/200` in the stated range; the smoothing cutoff conditions also hold. -/
theorem midrange_scale_conditions {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1423 / 100 : ℝ)) :
    let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
    0 < δ ∧ δ ≤ 1 / 200 ∧ 1 < x - x * δ ∧ 100 ≤ 2 / δ := by
  dsimp only
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hll := log_million_lower ha
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs1000 : 1000 ≤ s := by nlinarith only [hs, hs2, ha]
  have hq : 0 < q := by
    dsimp only [q]
    exact div_pos (by linarith only [hll]) (by nlinarith only [Real.pi_pos])
  have hq4 : q ≤ 4 := by
    dsimp only [q]
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    nlinarith only [hL, Real.pi_gt_three]
  have hd : 0 < q / s := div_pos hq hs
  have hd200 : q / s ≤ 1 / 200 := by
    apply (div_le_iff₀ hs).2
    linarith only [hq4, hs1000]
  have hmul := mul_le_mul_of_nonneg_left hd200 hx.le
  have hleft : 1 < x - x * (q / s) := by nlinarith only [hmul, ha]
  have hcut : 100 ≤ 2 / (q / s) := by
    apply (le_div_iff₀ hd).2
    linarith only [hd200]
  exact ⟨hd, hd200, hleft, hcut⟩

/-- Under RH and the stated height-100 zero hypotheses, canonical smoothing
applies the first five phase blocks whenever `10^6 ≤ x` and `log x ≤ 14.23`.
No separate midpoint or cutoff assumptions are needed. -/
theorem psi_midrange_canonical (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1423 / 100 : ℝ)) :
    let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * (51 / 100) + 3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24) +
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
  have hc := midrange_scale_conditions ha hL
  change 0 < δ ∧ δ ≤ 1 / 200 ∧ 1 < x - x * δ ∧ 100 ≤ 2 / δ at hc
  have hm := midrange_midpoints hx hc.1.le hc.2.1 (log_million_lower ha) hL
  exact
    psi_error_first_five_blocks_scale hRH g hmono hpos hheight hzero hcount hl hu hx hc.1
      (by linarith only [hc.2.1]) hc.2.2.1 hc.2.2.2 hm.1 hm.2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
