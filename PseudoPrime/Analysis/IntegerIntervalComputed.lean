/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervals

/-! # Computed outward integer interval arithmetic -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Round scaled integer endpoints outwards by Euclidean division at scale `G`.
Positive scale is required by the soundness lemmas; the result supports computed arithmetic. -/
def roundInterval (G l u : ℤ) : IntegerInterval :=
  ⟨l / G, -((-u) / G)⟩

/-- Compute a product enclosure from the minimum and maximum of the four corner products.
The endpoints are rounded outwards, avoiding externally supplied intermediate witnesses. -/
def roundedProduct (G : ℤ) (I J : IntegerInterval) : IntegerInterval :=
  roundInterval G
    (min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)))
    (max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper)))

/-- At positive scale, outward rounding encloses every integer between the source bounds.
Euclidean division supplies both inequalities, including negative source endpoints. -/
theorem round_corner {G l u x : ℤ} (hg : 0 < G) (hl : l ≤ x) (hu : x ≤ u) :
    (roundInterval G l u).lower * G ≤ x ∧ x ≤ (roundInterval G l u).upper * G := by
  exact
    ⟨(Int.ediv_mul_le l (ne_of_gt hg)).trans hl,
      hu.trans
        (by
          simpa only [roundInterval, neg_mul, neg_neg] using
            (neg_le_neg (Int.ediv_mul_le (-u) (ne_of_gt hg))))⟩

/-- At positive scale, the computed product passes the existing four-corner checker.
Each corner lies between the minimum and maximum used by outward rounding. -/
theorem roundedProduct_check (G : ℤ) (I J : IntegerInterval) (hg : 0 < G) :
    integerProductCheck G I.lower I.upper J.lower J.upper (roundedProduct G I J).lower
        (roundedProduct G I J).upper =
      true := by
  apply decide_eq_true
  refine ⟨hg, ?_, ?_, ?_, ?_⟩
  · exact
      round_corner hg ((min_le_left _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_left _ _))
  · exact
      round_corner hg ((min_le_left _ _).trans (min_le_right _ _))
        ((le_max_right _ _).trans (le_max_left _ _))
  · exact
      round_corner hg ((min_le_right _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _))
  · exact
      round_corner hg ((min_le_right _ _).trans (min_le_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _))

/-- Computed multiplication preserves real containment at a positive common scale.
Reuse checker soundness so Horner evaluation needs no intermediate witness table. -/
theorem roundedProduct_contains {G : ℤ} {I J : IntegerInterval} {x y : ℝ} (hg : 0 < G)
    (hx : I.Contains G x) (hy : J.Contains G y) : (roundedProduct G I J).Contains G (x * y) := by
  exact IntegerInterval.product_contains (roundedProduct_check G I J hg) hx hy

/-- Compute outward bounds for the rational `p/d` at scale `G`.
Positive denominator and scale are imposed by the containment theorem. -/
def roundedConstant (G p d : ℤ) : IntegerInterval :=
  roundInterval d (p * G) (p * G)

/-- Positive scale and denominator make the computed constant contain `p/d`.
Cross-product bounds from integer rounding feed the existing rational soundness theorem. -/
theorem roundedConstant_contains {G p d : ℤ} (hg : 0 < G) (hd : 0 < d) :
    (roundedConstant G p d).Contains G ((p : ℝ) / d) := by
  have hc := round_corner (G := d) (l := p * G) (u := p * G) hd le_rfl le_rfl
  exact integer_constant_bounds hg hd hc.1 hc.2

/-- Containment survives enlargement of integer endpoints at positive scale.
Cast the endpoint inequalities and divide by the common scale. -/
theorem interval_contains_of_bounds {G : ℤ} {R S : IntegerInterval} {x : ℝ} (hg : 0 < G)
    (hl : S.lower ≤ R.lower) (hu : R.upper ≤ S.upper) (hx : R.Contains G x) : S.Contains G x := by
  have h : (0 : ℝ) ≤ G := le_of_lt ((Int.cast_pos (R := ℝ)).mpr hg)
  have lo := div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hl) h
  have up := div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hu) h
  exact ⟨lo.trans hx.1, hx.2.trans up⟩

end PseudoPrime.Analysis
