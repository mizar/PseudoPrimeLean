/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveRoots

/-! # Scale-dependent coefficients for a triangular profile

The root and the existing three-factor floors define an adaptive coefficient. The estimates
below hold on the whole intended high-scale range and use no table of scale samples.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing three-factor coefficient floor at logarithmic scale `L`. It switches to
the sharper certified floor at `1820000000000). The adaptive profile takes its radius
at least as large as the square root of this floor. -/
noncomputable def triangularAdaptiveFloor (L : ℝ) : ℝ :=
  if (1820000000000 : ℝ) ≤ L then 1411811 / 5000000 else 28237 / 100000

/-- The positive linear coefficient in the adaptive triangular quadratic at scale `L).
It combines the main term, square-root loss and fixed margin. It is used to define the
positive root that closes the profile's scalar budget. -/
noncomputable def triangularAdaptiveA (L : ℝ) : ℝ :=
  36 + (1456 + 13 / 10000000) / Real.sqrt L + 165102 / L

/-- The nonnegative inverse-root cost in the adaptive triangular quadratic at scale `L).
It is the existing conductor cost divided by the eighth-root floor and `L).
This is the constant term in the positive-root equation. -/
noncomputable def triangularAdaptiveD (L : ℝ) : ℝ :=
  (4000000000000 * (1001 / 1000) : ℝ) / (triangularEighthRoot L * L)

/-- The adaptive triangular radius coefficient at scale `L) is the maximum of the
positive budget root and the square root of the applicable three-factor floor.
Its square is the proposed pointwise coefficient. -/
noncomputable def triangularAdaptiveRadius (L : ℝ) : ℝ :=
  max (Real.sqrt (triangularAdaptiveFloor L))
    (triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA L) (triangularAdaptiveD L))

/-- On `L ≥ 3 * 10 ^ 10`, the adaptive linear term is positive, its inverse-root cost
is nonnegative, and their sum is at most `68 - 3 / 10000`. Bound the eighth root,
square root and scale by their entrance values. This proves the quadratic root is at most one. -/
theorem triangularAdaptive_budget {L : ℝ} (hL : 30000000000 ≤ L) :
    0 < triangularAdaptiveA L ∧
      0 ≤ triangularAdaptiveD L ∧
      triangularAdaptiveA L + triangularAdaptiveD L ≤ 68 - 3 / 10000 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hm := triangularEighthRoot_ge_18 hL
  have hv : (170000 : ℝ) ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by nlinarith only [hL])
  have hm0 : 0 < triangularEighthRoot L := by linarith only [hm]
  have hv0 : 0 < Real.sqrt L := by linarith only [hv]
  have hden : (18 : ℝ) * 30000000000 ≤ triangularEighthRoot L * L :=
    mul_le_mul hm hL (by norm_num only) (by linarith only [hm])
  have ha : (1456 + 13 / 10000000 : ℝ) / Real.sqrt L ≤ (1456 + 13 / 10000000) / 170000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hv
  have hb : (165102 : ℝ) / L ≤ 165102 / 30000000000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  have hc : triangularAdaptiveD L ≤ (4000000000000 * (1001 / 1000) : ℝ) / (18 * 30000000000) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hden
  have hapos : 0 ≤ (1456 + 13 / 10000000 : ℝ) / Real.sqrt L := div_nonneg (by norm_num only) hv0.le
  have hbpos : 0 ≤ (165102 : ℝ) / L := div_nonneg (by norm_num only) hL0.le
  have hcpos : 0 ≤ triangularAdaptiveD L := div_nonneg (by norm_num only) (mul_nonneg hm0.le hL0.le)
  dsimp only [triangularAdaptiveA]
  constructor
  · linarith only [hapos, hbpos]
  exact
    ⟨hcpos, by
      norm_num only at ha hb hc ⊢; linarith only [ha, hb, hc]⟩

/-- At every scale, the existing three-factor floor lies strictly above
`(5313 / 10000) ^ 2` and at most one. Check both rational branches.
This supplies the local and sixteenth-root conditions of the adaptive profile. -/
theorem triangularAdaptiveFloor_bounds (L : ℝ) :
    (5313 / 10000 : ℝ) ^ 2 < triangularAdaptiveFloor L ∧ triangularAdaptiveFloor L ≤ 1 := by
  by_cases h : (1820000000000 : ℝ) ≤ L
  · rw [triangularAdaptiveFloor, ite_eq_left h]
    norm_num only [and_self]
  · rw [triangularAdaptiveFloor, ite_eq_right h]
    norm_num only [and_self]

/-- For `L ≥ 3 * 10 ^ 10`, the adaptive radius lies strictly above `5313 / 10000`
and at most one. The floor supplies the lower bound and the quadratic budget bounds
the positive root by one. These inequalities establish the profile's radius range. -/
theorem triangularAdaptiveRadius_bounds {L : ℝ} (hL : 30000000000 ≤ L) :
    (5313 / 10000 : ℝ) < triangularAdaptiveRadius L ∧ triangularAdaptiveRadius L ≤ 1 := by
  have hg := triangularAdaptiveFloor_bounds L
  have hroot : (5313 / 10000 : ℝ) < Real.sqrt (triangularAdaptiveFloor L) :=
    (Real.lt_sqrt (by norm_num only)).mpr hg.1
  have hsqrt : Real.sqrt (triangularAdaptiveFloor L) ≤ 1 := Real.sqrt_le_one.mpr hg.2
  have hb := triangularAdaptive_budget hL
  have hr := triangularPositiveRoot_spec (K := 68 - 3 / 10000) (by norm_num only) hb.1 hb.2.1
  have hr1 :=
    triangular_root_le_one (by norm_num only : (0 : ℝ) < 68 - 3 / 10000) hb.2.1 hr.2 hb.2.2
  constructor
  · exact hroot.trans_le (le_max_left _ _)
  · exact max_le hsqrt hr1

/-- For `L ≥ 3 * 10 ^ 10`, the adaptive radius satisfies the displayed quadratic
budget after division by the positive radius. The radius is at least the positive
root, so the root budget transfers to it. This is the core of the profile margin. -/
theorem triangularAdaptive_root_budget {L : ℝ} (hL : 30000000000 ≤ L) :
    triangularAdaptiveA L + triangularAdaptiveD L / triangularAdaptiveRadius L ≤
      (68 - 3 / 10000) * triangularAdaptiveRadius L := by
  have hb := triangularAdaptive_budget hL
  have hr := triangularPositiveRoot_spec (K := 68 - 3 / 10000) (by norm_num only) hb.1 hb.2.1
  have ha : 0 < triangularAdaptiveRadius L := by
    have hh := (triangularAdaptiveRadius_bounds hL).1
    linarith only [hh]
  exact triangular_root_budget (by norm_num only) hb.2.1 hr.1 hr.2 (le_max_right _ _) ha

/-- For `L ≥ 3 * 10 ^ 10`, the eighth root is positive and its sixteenth power is
at most `triangularAdaptiveRadius L ^ 2 * L ^ 2`. Square the exact eighth-power
identity and use the radius lower bound. This supplies the profile's root condition. -/
theorem triangularAdaptive_root16 {L : ℝ} (hL : 30000000000 ≤ L) :
    0 < triangularEighthRoot L ∧
      (triangularEighthRoot L) ^ 16 ≤ (triangularAdaptiveRadius L) ^ 2 * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hm := triangularEighthRoot_pow hL0
  have hm0 : 0 < triangularEighthRoot L := by
    have hh := triangularEighthRoot_ge_18 hL
    linarith only [hh]
  have ha := (triangularAdaptiveRadius_bounds hL).1
  have hasq : (5313 / 10000 : ℝ) ^ 2 ≤ (triangularAdaptiveRadius L) ^ 2 :=
    pow_le_pow_left₀ (by norm_num only) ha.le 2
  have hmul := mul_le_mul_of_nonneg_right hasq (sq_nonneg L)
  have he : (triangularEighthRoot L) ^ 16 = (5313 / 10000 : ℝ) ^ 2 * L ^ 2 := by
    calc
      _ = ((triangularEighthRoot L) ^ 8) ^ 2 := by ring
      _ = ((5313 / 10000 : ℝ) * L) ^ 2 := by rw [hm.2]
      _ = _ := by ring
  exact ⟨hm0, he.le.trans hmul⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
