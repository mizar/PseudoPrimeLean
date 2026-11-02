/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Endpoint deficits for small cyclic character families

The variables are the effective character costs and actual principal prefix/tail used by
the LLS comparison. The finite quotient penalties and their endpoint reductions belong to
this application layer; no numerical kernel choices are added to the general foundations.
These scalar statements require their trace and conductor-order hypotheses. They are not
closed prime bounds without the character and analytic interfaces supplied by consumers.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The minimum of two real costs is below a nonnegative normalized two-point mixture.
Input: the two weights and their total. Proof: multiply the minimum inequalities.
Role: justify the cyclic-four endpoint interpolation. -/
private theorem min_two_mix {a b r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (h : r + s = 1) :
    min a b ≤ r * a + s * b := by
  have ha := mul_le_mul_of_nonneg_left (min_le_left a b) hr
  have hb := mul_le_mul_of_nonneg_left (min_le_right a b) hs
  nlinarith only [ha, hb, congrArg (fun v : ℝ ↦ v * min a b) h]

/-- A cyclic-four weighted deficit is dominated by the quadratic or uniform endpoint.
Input: a normalized conjugate-pair weight, nonnegative principal tail, ordered conductor
costs and a trace penalty bounding both unit-value patterns. Claim: the two endpoint
minimum is no larger. Proof: split the affine trace penalty at one third.
Role: avoid continuous weight search for cyclic-four LLS character families. -/
theorem cyclic_four_endpoint {c₂ c₄ P T t m : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hT : 0 ≤ T)
    (hc : c₂ ≤ c₄) (hm₁ : t ≤ m) (hm₂ : 1 - 2 * t ≤ m) :
    min (c₂ - P + T) ((2 * c₄ + c₂) / 3 - P + T / 3) ≤ (1 - t) * c₄ + t * c₂ - P + m * T := by
  by_cases h : t ≤ 1 / 3
  · have hb :=
      min_two_mix (a := c₂ - P + T) (b := (2 * c₄ + c₂) / 3 - P + T / 3) (r := 1 - 3 * t) (s :=
        3 * t) (by linarith only [h]) (by linarith only [ht]) (by ring)
    have hcost := mul_nonneg (show 0 ≤ 1 - 3 * t by linarith only [h]) (sub_nonneg.mpr hc)
    have hpen := mul_nonneg (sub_nonneg.mpr hm₂) hT
    nlinarith only [hb, hcost, hpen]
  · have hb :=
      min_two_mix (a := c₂ - P + T) (b := (2 * c₄ + c₂) / 3 - P + T / 3) (r := (3 * t - 1) / 2)
        (s := 3 * (1 - t) / 2) (by linarith only [h]) (by linarith only [ht1]) (by ring)
    have hpen := mul_nonneg (sub_nonneg.mpr hm₁) hT
    nlinarith only [hb, hpen]

/-- A common-conductor cyclic-five deficit is minimized by its uniform trace penalty.
Input: a nonnegative principal tail and penalty at least one quarter.
Claim: the equal-weight endpoint is no worse. Proof: monotonicity in the tail coefficient.
Role: the scalar comparison after the finite character trace certificate is supplied. -/
theorem cyclic_five_endpoint {c P T m : ℝ} (hT : 0 ≤ T) (hm : 1 / 4 ≤ m) :
    c - P + T / 4 ≤ c - P + m * T := by nlinarith only [mul_nonneg (sub_nonneg.mpr hm) hT]

/-- The minimum of three real costs is below a normalized nonnegative three-point mixture.
Input: three weights summing to one. Proof: sum the weighted minimum inequalities.
Role: certify the cyclic-six faces without a linear-programming oracle. -/
private theorem min_three_mix {a b c r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : r + s + t = 1) : min a (min b c) ≤ r * a + s * b + t * c := by
  have ha := mul_le_mul_of_nonneg_left (min_le_left a (min b c)) hr
  have hb := mul_le_mul_of_nonneg_left ((min_le_right a (min b c)).trans (min_le_left b c)) hs
  have hc := mul_le_mul_of_nonneg_left ((min_le_right a (min b c)).trans (min_le_right b c)) ht
  nlinarith only [ha, hb, hc, congrArg (fun v : ℝ ↦ v * min a (min b c)) h]

/-- The first cyclic-six trace face interpolates quadratic, cubic and uniform endpoints.
Input: the face inequalities and nonnegative tail. Claim: the endpoint minimum is valid.
Proof: explicit nonnegative barycentric weights. Role: one face of the finite reduction. -/
private theorem six_face_one {y z c₂ c₃ c₆ P T m : ℝ} (hxyz : 0 ≤ 1 - y - z) (hT : 0 ≤ T)
    (hr : 1 ≤ 2 * y + z) (hs : 1 ≤ y + 3 * z) (hm : -(1 / 2 : ℝ) + y + 3 / 2 * z ≤ m) :
    min (c₂ - P + T) (min (c₃ - P + T / 2) ((2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5)) ≤
      (1 - y - z) * c₆ + y * c₃ + z * c₂ - P + m * T := by
  have hb :=
    min_three_mix (a := c₂ - P + T) (b := c₃ - P + T / 2) (c :=
      (2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5) (r := (y + 3 * z - 1) / 2) (s := 2 * y + z - 1) (t :=
      5 / 2 * (1 - y - z)) (by linarith only [hs]) (by linarith only [hr])
      (by nlinarith only [hxyz]) (by ring)
  have hpen := mul_nonneg (sub_nonneg.mpr hm) hT
  nlinarith only [hb, hpen]

/-- The second cyclic-six trace face uses cubic and uniform endpoints.
Input: ordered cubic/full conductor costs, face inequalities and a nonnegative tail.
Proof: explicit interpolation and the conductor order. Role: remove its dominated vertex. -/
private theorem six_face_two {y z c₂ c₃ c₆ P T m : ℝ} (hz : 0 ≤ z) (hT : 0 ≤ T) (hc : c₃ ≤ c₆)
    (hr : 1 + 3 * z ≤ 4 * y) (hs : y + 3 * z ≤ 1) (hm : 1 / 2 - 3 / 2 * z ≤ m) :
    min (c₂ - P + T) (min (c₃ - P + T / 2) ((2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5)) ≤
      (1 - y - z) * c₆ + y * c₃ + z * c₂ - P + m * T := by
  have hb :=
    min_three_mix (a := c₂ - P + T) (b := c₃ - P + T / 2) (c :=
      (2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5) (r := 0) (s := 1 - 5 * z) (t := 5 * z) (le_refl 0)
      (by linarith only [hr, hs]) (by linarith only [hz]) (by ring)
  have hcost := mul_nonneg (show 0 ≤ 1 - y - 3 * z by linarith only [hs]) (sub_nonneg.mpr hc)
  have hpen := mul_nonneg (sub_nonneg.mpr hm) hT
  nlinarith only [hb, hcost, hpen]

/-- One half of the third cyclic-six face uses quadratic and uniform endpoints.
Input: ordered quadratic/full conductor costs, face inequalities and a nonnegative tail.
Proof: explicit interpolation and the conductor order. Role: remove the full-order vertex. -/
private theorem six_face_three_a {y z c₂ c₃ c₆ P T m : ℝ} (hy : 0 ≤ y) (hT : 0 ≤ T) (hc : c₂ ≤ c₆)
    (hr : 2 * y + z ≤ 1) (hs : y ≤ 2 * z) (hm : 1 - 2 * y ≤ m) :
    min (c₂ - P + T) (min (c₃ - P + T / 2) ((2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5)) ≤
      (1 - y - z) * c₆ + y * c₃ + z * c₂ - P + m * T := by
  have hb :=
    min_three_mix (a := c₂ - P + T) (b := c₃ - P + T / 2) (c :=
      (2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5) (r := 1 - 5 / 2 * y) (s := 0) (t := 5 / 2 * y)
      (by linarith only [hr, hs]) (le_refl 0) (by linarith only [hy]) (by ring)
  have hcost := mul_nonneg (show 0 ≤ 1 - 2 * y - z by linarith only [hr]) (sub_nonneg.mpr hc)
  have hpen := mul_nonneg (sub_nonneg.mpr hm) hT
  nlinarith only [hb, hcost, hpen]

/-- The other half of the third cyclic-six face uses the three retained endpoints.
Input: ordered conductor costs, face inequalities and a nonnegative principal tail.
Proof: nonnegative barycentric weights and the two conductor orders.
Role: retain only the quadratic, cubic and full-average candidates. -/
private theorem six_face_three_b {y z c₂ c₃ c₆ P T m : ℝ} (hz : 0 ≤ z) (hT : 0 ≤ T) (hc₂ : c₂ ≤ c₆)
    (hc₃ : c₃ ≤ c₆) (hr : 4 * y ≤ 1 + 3 * z) (hs : 2 * z ≤ y) (hm : 1 - 2 * y ≤ m) :
    min (c₂ - P + T) (min (c₃ - P + T / 2) ((2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5)) ≤
      (1 - y - z) * c₆ + y * c₃ + z * c₂ - P + m * T := by
  have hb :=
    min_three_mix (a := c₂ - P + T) (b := c₃ - P + T / 2) (c :=
      (2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5) (r := 1 - 4 * y + 3 * z) (s := 4 * y - 8 * z) (t :=
      5 * z) (by linarith only [hr]) (by linarith only [hs]) (by linarith only [hz]) (by ring)
  have hcost₂ := mul_nonneg (show 0 ≤ 1 - 4 * y + 3 * z by linarith only [hr]) (sub_nonneg.mpr hc₂)
  have hcost₃ := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hc₃)
  have hpen := mul_nonneg (sub_nonneg.mpr hm) hT
  nlinarith only [hb, hcost₂, hcost₃, hpen]

/-- Every normalized cyclic-six weighted deficit is dominated by three retained endpoints.
Input: nonnegative weights totaling one, nonnegative principal tail, ordered conductor
costs and the three explicit trace-penalty inequalities. Claim: the quadratic, cubic or
uniform endpoint is no worse. Proof: cover the weight simplex by four rational triangles.
Role: replace continuous LLS weight optimization by a finite candidate family. -/
theorem cyclic_six_endpoint {x y z c₂ c₃ c₆ P T m : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hw : x + y + z = 1) (hT : 0 ≤ T) (hc₂ : c₂ ≤ c₆) (hc₃ : c₃ ≤ c₆)
    (hm₁ : -(1 / 2 : ℝ) + y + 3 / 2 * z ≤ m) (hm₂ : 1 / 2 - 3 / 2 * z ≤ m) (hm₃ : 1 - 2 * y ≤ m) :
    min (c₂ - P + T) (min (c₃ - P + T / 2) ((2 * c₆ + 2 * c₃ + c₂) / 5 - P + T / 5)) ≤
      x * c₆ + y * c₃ + z * c₂ - P + m * T := by
  have hxv : x = 1 - y - z := by linarith only [hw]
  rw [hxv]
  by_cases h₁ : 1 ≤ 2 * y + z
  · by_cases h₂ : 1 ≤ y + 3 * z
    · exact six_face_one (hxv ▸ hx) hT h₁ h₂ hm₁
    · exact six_face_two hz hT hc₃ (by linarith only [h₁, h₂]) (le_of_not_ge h₂) hm₂
  · by_cases h₂ : 1 + 3 * z ≤ 4 * y
    · exact six_face_two hz hT hc₃ h₂ (by linarith only [h₁, h₂]) hm₂
    · by_cases h₃ : y ≤ 2 * z
      · exact six_face_three_a hy hT hc₂ (le_of_not_ge h₁) h₃ hm₃
      · exact six_face_three_b hz hT hc₂ hc₃ (le_of_not_ge h₂) (le_of_not_ge h₃) hm₃

end PseudoPrime.LLS.PaperStatements
