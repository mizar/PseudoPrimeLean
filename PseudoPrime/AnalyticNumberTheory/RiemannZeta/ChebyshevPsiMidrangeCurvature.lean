/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeSharpRH
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Rational control of the midrange curvature remainder -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- In the initial midrange, the canonical relative width is at most 1/250.
The proof uses the elementary bounds `sqrt x ≥ 1000` and `5 log x/(6π) ≤ 4`. -/
theorem midrange_delta_le {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1423 / 100 : ℝ)) :
    (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x ≤ (1 / 250 : ℝ) := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs1000 : 1000 ≤ s := by nlinarith only [hs, hs2, ha]
  have hq4 : q ≤ 4 := by
    dsimp only [q]
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    nlinarith only [hL, Real.pi_gt_three]
  change q / s ≤ _
  apply (div_le_iff₀ hs).2
  linarith only [hq4, hs1000]

/-- For `0 ≤ δ ≤ 1/250`, the negative three-halves power of `1-δ` is
at most 101/100. Monotonicity in the exponent reduces it to a reciprocal square. -/
theorem midrange_curvature_power {δ : ℝ} (hd : 0 ≤ δ) (hu : δ ≤ 1 / 250) :
    (1 - δ) ^ (-(3 / 2 : ℝ)) ≤ (101 / 100 : ℝ) := by
  have hb : 0 < 1 - δ := by linarith only [hu]
  have hb1 : 1 - δ ≤ 1 := by linarith only [hd]
  have h := Real.rpow_le_rpow_of_exponent_ge hb hb1 (show (-2 : ℝ) ≤ -(3 / 2 : ℝ) by norm_num only)
  have he : (1 - δ) ^ (-2 : ℝ) = 1 / (1 - δ) ^ 2 := by
    rw [Real.rpow_neg (by linarith only [hu] : 0 ≤ 1 - δ)]
    norm_num only [Real.rpow_ofNat, one_div]
  rw [he] at h
  have hp : 0 < (1 - δ) ^ 2 := sq_pos_of_pos hb
  have hbound : (1 : ℝ) / (1 - δ) ^ 2 ≤ 101 / 100 := by
    apply (div_le_iff₀ hp).2
    nlinarith only [hu, hd, sq_nonneg (δ - 1 / 250)]
  exact h.trans hbound

/-- The normalized curvature remainder is at most 613/250000 whenever the
relative smoothing width is between zero and 1/250. -/
theorem midrange_curvature_le {δ : ℝ} (hd : 0 ≤ δ) (hu : δ ≤ 1 / 250) :
    3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24 ≤ (613 / 250000 : ℝ) := by
  have hp := midrange_curvature_power hd hu
  have hs : δ ^ 2 ≤ (1 / 250 : ℝ) ^ 2 := by nlinarith only [hd, hu]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg δ)
  have hn : 0 ≤ (101 / 100 : ℝ) := by norm_num only
  have hm2 := mul_le_mul_of_nonneg_left hs hn
  nlinarith only [hm, hm2]

/-- In the first two phase blocks, canonical smoothing has relative width at
most 37/10000. The lower bound for π tightens the general 1/250 estimate. -/
theorem midrange_delta_sharp {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1386 / 100 : ℝ)) :
    (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x ≤ (37 / 10000 : ℝ) := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs1000 : 1000 ≤ s := by nlinarith only [hs, hs2, ha]
  have hq : q ≤ 37 / 10 := by
    dsimp only [q]
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    nlinarith only [hL, Real.pi_gt_d4]
  change q / s ≤ _
  apply (div_le_iff₀ hs).2
  linarith only [hq, hs1000]

/-- The sharper width bound makes the normalized curvature remainder at most
527/250000. This rational bound is used in the initial margin comparison. -/
theorem midrange_curvature_sharp {δ : ℝ} (hd : 0 ≤ δ) (hu : δ ≤ 37 / 10000) :
    3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24 ≤ (527 / 250000 : ℝ) := by
  have hu' : δ ≤ 1 / 250 := by linarith only [hu]
  have hp := midrange_curvature_power hd hu'
  have hs : δ ^ 2 ≤ (37 / 10000 : ℝ) ^ 2 := by nlinarith only [hd, hu]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg δ)
  have hn : 0 ≤ (101 / 100 : ℝ) := by norm_num only
  have hm2 := mul_le_mul_of_nonneg_left hs hn
  nlinarith only [hm, hm2]

/-- Under RH and the stated height-100 zero hypotheses, canonical smoothing in
the initial midrange admits a rational upper bound for its curvature term. -/
theorem psi_midrange_curvature (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1386 / 100 : ℝ)) :
    let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * (127 / 250) + 527 / 250000) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * Real.sqrt x) := by
  dsimp only
  let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
  have hc := midrange_scale_conditions ha (show Real.log x ≤ (1423 / 100 : ℝ) by linarith only [hL])
  change 0 < δ ∧ δ ≤ 1 / 200 ∧ 1 < x - x * δ ∧ 100 ≤ 2 / δ at hc
  have huδ : δ ≤ 37 / 10000 := midrange_delta_sharp ha hL
  have hcurv := midrange_curvature_sharp hc.1.le huδ
  have hp := psi_midrange_canonical_sharp hRH g hmono hpos hheight hzero hcount hl hu ha hL
  change
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * (127 / 250) + 3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * Real.sqrt x) at hp
  dsimp only [δ] at hp hcurv
  linarith only [hp, hcurv]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
