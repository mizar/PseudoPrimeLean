/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedRationalIntervals

/-! # Integer witnesses for outward interval arithmetic -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Check whether integer endpoints at positive scale enclose the rational `p/d`.
The denominator is positive and cross-products certify both bounds. This is the
constant-leaf checker for real interval certificates. -/
def integerConstantCheck (G p d l u : ℤ) : Bool :=
  decide (0 < G ∧ 0 < d ∧ l * d ≤ p * G ∧ p * G ≤ u * d)

/-- Positive scale and denominator turn the checked integer cross-products into
real division bounds. Cast the witnesses and use the ordered-field division laws. -/
theorem integer_constant_bounds {G p d l u : ℤ} (hG : 0 < G) (hd : 0 < d) (hl : l * d ≤ p * G)
    (hu : p * G ≤ u * d) : (l : ℝ) / G ≤ (p : ℝ) / d ∧ (p : ℝ) / d ≤ (u : ℝ) / G := by
  have hg : (0 : ℝ) < G := by exact_mod_cast hG
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl' : (l : ℝ) * d ≤ (p : ℝ) * G := by exact_mod_cast hl
  have hu' : (p : ℝ) * G ≤ (u : ℝ) * d := by exact_mod_cast hu
  exact ⟨(div_le_div_iff₀ hg hd').2 hl', (div_le_div_iff₀ hd' hg).2 hu'⟩

/-- Successful constant checking supplies real interval containment, with no
assumption about the algorithm that generated the integer endpoints. -/
theorem integerConstantCheck_sound {G p d l u : ℤ} (h : integerConstantCheck G p d l u = true) :
    (l : ℝ) / G ≤ (p : ℝ) / d ∧ (p : ℝ) / d ≤ (u : ℝ) / G := by
  have hc := of_decide_eq_true h
  exact integer_constant_bounds hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- Check reciprocal containment at a positive integer scale. The input lower
endpoint is positive and the cross-products bound both reciprocal endpoints. -/
def integerReciprocalCheck (G a b l u : ℤ) : Bool :=
  decide (0 < G ∧ 0 < a ∧ a ≤ b ∧ l ≤ u ∧ l * b ≤ G * G ∧ G * G ≤ u * a)

/-- Positive input bounds and checked cross-products enclose the reciprocal.
Cast the integer inequalities, then apply the order reversal of inversion. -/
theorem integer_reciprocal_bounds {G a b l u : ℤ} {x : ℝ} (hg : 0 < G) (ha : 0 < a)
    (hl : l * b ≤ G * G) (hu : G * G ≤ u * a) (hx : (a : ℝ) / G ≤ x ∧ x ≤ (b : ℝ) / G) :
    (l : ℝ) / G ≤ x⁻¹ ∧ x⁻¹ ≤ (u : ℝ) / G := by
  have g : (0 : ℝ) < G := by exact_mod_cast hg
  have aa : (0 : ℝ) < a := by exact_mod_cast ha
  have ab : (a : ℝ) ≤ b := (div_le_div_iff_of_pos_right g).1 (hx.1.trans hx.2)
  have bb : (0 : ℝ) < b := aa.trans_le ab
  have hll : (l : ℝ) * b ≤ (G : ℝ) * G := by exact_mod_cast hl
  have huu : (G : ℝ) * G ≤ (u : ℝ) * a := by exact_mod_cast hu
  have lo : (l : ℝ) / G ≤ (G : ℝ) / b := (div_le_div_iff₀ g bb).2 hll
  have up : (G : ℝ) / a ≤ (u : ℝ) / G := (div_le_div_iff₀ aa g).2 huu
  have low := inv_le_inv₀ (div_pos bb g) (lt_of_lt_of_le (div_pos aa g) hx.1)
  have high := inv_le_inv₀ (lt_of_lt_of_le (div_pos aa g) hx.1) (div_pos aa g)
  have lx : (G : ℝ) / b ≤ x⁻¹ := by simpa only [inv_div] using low.2 hx.2
  have ux : x⁻¹ ≤ (G : ℝ) / a := by simpa only [inv_div] using high.2 hx.1
  exact ⟨lo.trans lx, ux.trans up⟩

/-- A successful reciprocal check transports any real input in the positive
source interval into the certified output interval. -/
theorem integerReciprocalCheck_sound {G a b l u : ℤ} {x : ℝ}
    (h : integerReciprocalCheck G a b l u = true) (hx : (a : ℝ) / G ≤ x ∧ x ≤ (b : ℝ) / G) :
    (l : ℝ) / G ≤ x⁻¹ ∧ x⁻¹ ≤ (u : ℝ) / G := by
  have hc := of_decide_eq_true h
  exact integer_reciprocal_bounds hc.1 hc.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2 hx

/-- Reflect a negative input and its output through zero and check the
positive reciprocal. This avoids a separate signed division implementation. -/
def integerNegReciprocalCheck (G a b l u : ℤ) : Bool :=
  integerReciprocalCheck G (-b) (-a) (-u) (-l)

/-- A successful reflected check encloses the reciprocal of a negative input.
Negate the source interval, apply positive reciprocal soundness, and negate back. -/
theorem integerNegReciprocalCheck_sound {G a b l u : ℤ} {x : ℝ}
    (h : integerNegReciprocalCheck G a b l u = true) (hx : (a : ℝ) / G ≤ x ∧ x ≤ (b : ℝ) / G) :
    (l : ℝ) / G ≤ x⁻¹ ∧ x⁻¹ ≤ (u : ℝ) / G := by
  have hn : ((-b : ℤ) : ℝ) / G ≤ -x ∧ -x ≤ ((-a : ℤ) : ℝ) / G := by
    simpa only [Int.cast_neg, neg_div] using ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hr := integerReciprocalCheck_sound h hn
  simpa only [Int.cast_neg, neg_div, inv_neg, neg_neg] using
    And.intro (neg_le_neg hr.2) (neg_le_neg hr.1)

/-- Multiplication by any signed scalar preserves bounds verified at both
endpoints. Split on the scalar sign to account for order reversal. -/
theorem interval_scalar_bounds {r s z k L U : ℝ} (hz : r ≤ z ∧ z ≤ s) (hL : L ≤ r * k ∧ L ≤ s * k)
    (hU : r * k ≤ U ∧ s * k ≤ U) : L ≤ z * k ∧ z * k ≤ U := by
  rcases le_total 0 k with hk | hk
  · exact
      ⟨hL.1.trans (mul_le_mul_of_nonneg_right hz.1 hk),
        (mul_le_mul_of_nonneg_right hz.2 hk).trans hU.2⟩
  · exact
      ⟨hL.2.trans (mul_le_mul_of_nonpos_right hz.2 hk),
        (mul_le_mul_of_nonpos_right hz.1 hk).trans hU.1⟩

/-- Four corner products enclose the product of two real interval values.
Apply signed scalar bounds successively to the two input intervals. -/
theorem interval_four_corner_bounds {a b c d l u x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : l ≤ a * c ∧ l ≤ a * d ∧ l ≤ b * c ∧ l ≤ b * d)
    (hu : a * c ≤ u ∧ a * d ≤ u ∧ b * c ≤ u ∧ b * d ≤ u) : l ≤ x * y ∧ x * y ≤ u := by
  have ac :=
    interval_scalar_bounds hy (k := a) (by simpa only [mul_comm] using And.intro hl.1 hl.2.1)
      (by simpa only [mul_comm] using And.intro hu.1 hu.2.1)
  have bc :=
    interval_scalar_bounds hy (k := b) (by simpa only [mul_comm] using And.intro hl.2.2.1 hl.2.2.2)
      (by simpa only [mul_comm] using And.intro hu.2.2.1 hu.2.2.2)
  apply interval_scalar_bounds hx
  · exact ⟨by simpa only [mul_comm] using ac.1, by simpa only [mul_comm] using bc.1⟩
  · exact ⟨by simpa only [mul_comm] using ac.2, by simpa only [mul_comm] using bc.2⟩

/-- Integer cross-product bounds at positive scale enclose one scaled corner
product. Cast the witnesses and divide by the square of the scale. -/
theorem integer_corner_bounds {G a b l u : ℤ} (hg : 0 < G) (hl : l * G ≤ a * b)
    (hu : a * b ≤ u * G) :
    (l : ℝ) / G ≤ ((a : ℝ) / G) * ((b : ℝ) / G) ∧ ((a : ℝ) / G) * ((b : ℝ) / G) ≤ (u : ℝ) / G := by
  have g : (0 : ℝ) < G := by exact_mod_cast hg
  have g2 := mul_pos g g
  have hl' : (l : ℝ) * G ≤ (a : ℝ) * b := by exact_mod_cast hl
  have hu' : (a : ℝ) * b ≤ (u : ℝ) * G := by exact_mod_cast hu
  rw [div_mul_div_comm]
  constructor
  · apply (div_le_div_iff₀ g g2).2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hl' g.le
  · apply (div_le_div_iff₀ g2 g).2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hu' g.le

/-- Check that four integer corner products fit inside the proposed output
interval at positive scale. Signed inputs require all four comparisons. -/
def integerProductCheck (G a b c d l u : ℤ) : Bool :=
  decide
    (0 < G ∧
      (l * G ≤ a * c ∧ a * c ≤ u * G) ∧
      (l * G ≤ a * d ∧ a * d ≤ u * G) ∧
      (l * G ≤ b * c ∧ b * c ≤ u * G) ∧ (l * G ≤ b * d ∧ b * d ≤ u * G))

/-- Successful product checking encloses products of arbitrary real values
in the two source intervals. Transport the four corners and apply signed bounds. -/
theorem integerProductCheck_sound {G a b c d l u : ℤ} {x y : ℝ}
    (h : integerProductCheck G a b c d l u = true) (hx : (a : ℝ) / G ≤ x ∧ x ≤ (b : ℝ) / G)
    (hy : (c : ℝ) / G ≤ y ∧ y ≤ (d : ℝ) / G) : (l : ℝ) / G ≤ x * y ∧ x * y ≤ (u : ℝ) / G := by
  have hc := of_decide_eq_true h
  have ac := integer_corner_bounds hc.1 hc.2.1.1 hc.2.1.2
  have ad := integer_corner_bounds hc.1 hc.2.2.1.1 hc.2.2.1.2
  have bc := integer_corner_bounds hc.1 hc.2.2.2.1.1 hc.2.2.2.1.2
  have bd := integer_corner_bounds hc.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  exact interval_four_corner_bounds hx hy ⟨ac.1, ad.1, bc.1, bd.1⟩ ⟨ac.2, ad.2, bc.2, bd.2⟩

end PseudoPrime.Analysis
