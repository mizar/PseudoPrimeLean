/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEightNinthsRange
public import PseudoPrime.Analysis.BernsteinQuartic

/-! # Generic logarithmic-chord certificates for full endpoint polynomials -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For y>=1, L<=3y/2, P>=0 and z>=0, the full endpoint logarithmic slope
is nonnegative. Retain the nonnegative pi and logarithmic terms and the level
slack. This permits arbitrary lower chords on the radius interval. -/
theorem fullEndpointLogSlope_nonneg {L P y z : ℝ} (hy : 1 ≤ y) (hL : L ≤ (3 / 2 : ℝ) * y)
    (hP : 0 ≤ P) (hz : 0 ≤ z) : 0 ≤ fullEndpointLogSlope L P y z := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hys : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy]
  have hlevel :=
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 * y by linarith only [hy]) (sub_nonneg.mpr hy))
      (sub_nonneg.mpr hL)
  have hpi := mul_nonneg hP hys
  have hlog := mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) (sq_nonneg y)) hz
  dsimp only [fullEndpointLogSlope]
  nlinarith only [hlevel, hpi, hlog, pow_nonneg hy0 3, sq_nonneg y, hy]

/-- For y>=1, L<=3y/2, P>=0 and 0<=z<=Z, increasing the logarithmic
argument increases the full endpoint polynomial. Apply the nonnegative slope
and the exact quadratic shift identity. This lifts any certified lower chord. -/
theorem fullEndpointPolynomial_mono_log_of_level_bound {L P y z Z : ℝ} (hy : 1 ≤ y)
    (hL : L ≤ (3 / 2 : ℝ) * y) (hP : 0 ≤ P) (hz : 0 ≤ z) (hzZ : z ≤ Z) :
    fullEndpointPolynomial L P y z ≤ fullEndpointPolynomial L P y Z := by
  have hm := mul_nonneg (sub_nonneg.mpr hzZ) (fullEndpointLogSlope_nonneg hy hL hP hz)
  have hs :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg y)) (sq_nonneg (Z - z))
  have he := fullEndpointPolynomial_log_shift L P y z (Z - z)
  rw [add_sub_cancel] at he
  linarith only [hm, hs, he]

/-- On a positive real interval [a,b], an affine line lying below log at both
endpoints lies below log everywhere. Use logarithmic concavity and exact
barycentric weights. This provides reusable chord bounds from two scalar inputs. -/
theorem log_chord_le_of_endpoints {a b m c y : ℝ} (ha : 0 < a) (hab : a < b) (hlo : a ≤ y)
    (hhi : y ≤ b) (hloglo : m * a + c ≤ Real.log a) (hloghi : m * b + c ≤ Real.log b) :
    m * y + c ≤ Real.log y := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hwa : 0 ≤ (b - y) / (b - a) := div_nonneg (sub_nonneg.mpr hhi) hd.le
  have hwb : 0 ≤ (y - a) / (b - a) := div_nonneg (sub_nonneg.mpr hlo) hd.le
  have hs : (b - y) / (b - a) + (y - a) / (b - a) = 1 := by
    have hn : (b - y) + (y - a) = b - a := by ring
    rw [← add_div, hn, div_self hd.ne']
  have hc :=
    strictConcaveOn_log_Ioi.concaveOn.2 (show a ∈ Set.Ioi 0 from ha)
      (show b ∈ Set.Ioi 0 from ha.trans hab) hwa hwb hs
  simp only [smul_eq_mul] at hc
  have he : (b - y) / (b - a) * a + (y - a) / (b - a) * b = y := by
    have hm := congrArg (fun w : ℝ ↦ a * w) hs
    have ht := div_mul_cancel₀ (y - a) hd.ne'
    nlinarith only [hm, ht]
  rw [he] at hc
  have hA := mul_le_mul_of_nonneg_left hloglo hwa
  have hB := mul_le_mul_of_nonneg_left hloghi hwb
  have hm := congrArg (fun w : ℝ ↦ m * w) he
  have ht := congrArg (fun w : ℝ ↦ c * w) hs
  nlinarith only [hc, hA, hB, hm, ht]

end PseudoPrime.LLS.PaperStatements
