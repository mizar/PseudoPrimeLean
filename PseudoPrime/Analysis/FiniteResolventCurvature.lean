/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CosineMomentInterpolation
public import PseudoPrime.Analysis.SignedResolventEulerBounds

/-! # Unscaled signed resolvent curvature for arbitrary rational node lists -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real node and ordinate. Output: a/(a^2+t^2).
Role: isolate the unscaled rational factor in signed spectral majorants. -/
noncomputable def plainResolvent (a t : ℝ) : ℝ :=
  a / (a ^ 2 + t ^ 2)

/-- Input: a real node and ordinate. Output: the first rational derivative of plainResolvent.
Role: supply explicit derivatives without an implicit differentiation oracle. -/
noncomputable def plainResolventDeriv (a t : ℝ) : ℝ :=
  -2 * a * t / (a ^ 2 + t ^ 2) ^ 2

/-- Input: a real node and ordinate. Output: 2*a*(3*t^2-a^2)/(a^2+t^2)^3.
Role: bound the unscaled rational curvature uniformly in the ordinate. -/
noncomputable def plainResolventSecondDeriv (a t : ℝ) : ℝ :=
  2 * a * (3 * t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 3

/-- Input: a positive node and any ordinate.
Claim: the plain resolvent has the stated first derivative.
Proof: differentiate the inverse denominator and clear its positive power.
Role: certify a rational majorant's analytic curvature. -/
theorem hasDerivAt_plainResolvent {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (plainResolvent a) (plainResolventDeriv a t) t := by
  have hz : a ^ 2 + t ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)).ne'
  have hd := (hasDerivAt_const t (a ^ 2)).add ((hasDerivAt_id t).pow 2)
  have h := (hd.inv hz).const_mul a
  convert h using 1
  · rfl
  · dsimp only [plainResolventDeriv, Pi.add_apply, Pi.pow_apply, id_eq]
    field_simp (discharger := exact hz)
    ring

/-- Input: a positive node and any ordinate.
Claim: the first derivative has the stated second derivative.
Proof: quotient rule and polynomial normalization.
Role: retain exact signed derivatives before applying a uniform bound. -/
theorem hasDerivAt_plainResolventDeriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (plainResolventDeriv a) (plainResolventSecondDeriv a t) t := by
  have hz : a ^ 2 + t ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)).ne'
  have hd := (hasDerivAt_const t (a ^ 2)).add ((hasDerivAt_id t).pow 2)
  have hn := (hasDerivAt_id t).const_mul (-2 * a)
  have h := hn.div (hd.pow 2) (pow_ne_zero 2 hz)
  convert h using 1
  · rfl
  · dsimp only [plainResolventSecondDeriv, Pi.add_apply, Pi.pow_apply, id_eq]
    field_simp (discharger :=
      first
      | exact hz
      | exact pow_ne_zero 2 hz)
    ring

/-- Input: a positive node and any ordinate.
Claim: the second derivative has absolute value at most 6/a^3.
Proof: bound |3*t^2-a^2| by 3*(a^2+t^2) and compare positive denominators.
Role: produce a finite coefficient cost for arbitrary signed node lists. -/
theorem abs_plainResolventSecondDeriv_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |plainResolventSecondDeriv a t| ≤ 6 / a ^ 3 := by
  have hD : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have habs : |3 * t ^ 2 - a ^ 2| ≤ 3 * (a ^ 2 + t ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg a, sq_nonneg t]
  rw [plainResolventSecondDeriv, abs_div, abs_mul,
    abs_of_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) ha), abs_of_pos (pow_pos hD 3)]
  apply (div_le_div_iff₀ (pow_pos hD 3) (pow_pos ha 3)).mpr
  have h1 :=
    mul_le_mul_of_nonneg_left habs
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) ha.le) (pow_nonneg ha.le 3))
  have hsq := pow_le_pow_left₀ (sq_nonneg a) (le_add_of_nonneg_right (sq_nonneg t)) 2
  have h2 := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6) hD.le)
  nlinarith only [h1, h2]

/-- Input: a positive node, any signed weight and any interval.
Claim: subtracting |c|*(6/a^3)*t^2/2 makes the weighted resolvent concave.
Proof: multiply the exact derivatives by c and use their absolute bound.
Role: support signed coefficients while keeping a positive interpolation cost. -/
theorem concaveOn_weighted_plainResolvent {a : ℝ} (ha : 0 < a) (c lo hi : ℝ) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t ↦ c * plainResolvent a t - (|c| * (6 / a ^ 3)) / 2 * t ^ 2) := by
  apply
    concaveOn_quadratic_correction_of_second_deriv_le
      (fun t _ ↦ (hasDerivAt_plainResolvent ha t).const_mul c)
      (fun t _ ↦ (hasDerivAt_plainResolventDeriv ha t).const_mul c)
  intro t _
  exact
    ((le_abs_self (c * plainResolventSecondDeriv a t)).trans_eq (abs_mul _ _)).trans
      (mul_le_mul_of_nonneg_left (abs_plainResolventSecondDeriv_le ha t) (abs_nonneg c))

/-- Input: a finite rational node-coefficient list.
Output: the sum of |c|*(6/a^3) over that list.
Role: provide an explicit uniform curvature budget independent of the ordinate. -/
noncomputable def finiteResolventCurvatureCost (l : List (ℚ × ℚ)) : ℝ :=
  (l.map (fun ab ↦ |(ab.2 : ℝ)| * (6 / (ab.1 : ℝ) ^ 3))).sum

/-- Input: a finite list with positive nodes.
Claim: its curvature cost is nonnegative.
Proof: each absolute weight times reciprocal positive cube is nonnegative.
Role: satisfy the interpolation theorem's sign premise. -/
theorem finiteResolventCurvatureCost_nonneg (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, 0 < (ab.1 : ℝ)) :
    0 ≤ finiteResolventCurvatureCost l := by
  dsimp only [finiteResolventCurvatureCost]
  apply List.sum_nonneg
  intro v hv
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hv
  exact mul_nonneg (abs_nonneg _) (div_nonneg (by norm_num only) (pow_nonneg (ha ab hab).le 3))

/-- Input: a finite list with positive nodes and any interval.
Claim: the signed resolvent minus its curvature cost times t^2/2 is concave.
Proof: add the single-node concavity inequalities by list induction.
Role: supply the actual rational majorant input for Gamma phase interpolation. -/
theorem concaveOn_finiteSignedResolvent_quadratic (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, 0 < (ab.1 : ℝ))
    (lo hi : ℝ) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t ↦ finiteSignedResolvent l t - finiteResolventCurvatureCost l / 2 * t ^ 2) := by
  induction l with
  | nil =>
    simpa only [finiteSignedResolvent, finiteResolventCurvatureCost, List.map_nil, List.sum_nil,
      zero_div, zero_mul, sub_zero] using (concaveOn_const (c := (0 : ℝ)) (convex_Icc lo hi))
  | cons ab l
    ih =>
    have h :=
      (concaveOn_weighted_plainResolvent (ha ab List.mem_cons_self) (ab.2 : ℝ) lo hi).add
        (ih (fun cd hcd ↦ ha cd (List.mem_cons_of_mem ab hcd)))
    convert h using 1
    funext t
    simp only [Pi.add_apply, finiteSignedResolvent, finiteResolventCurvatureCost, plainResolvent,
      List.map_cons, List.sum_cons]
    ring

end PseudoPrime.Analysis
