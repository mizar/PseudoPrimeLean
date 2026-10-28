/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRClippedNumerics

/-! # Exact comparisons for clipped Gaussian profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The raw cutoff (6/5)t_D(L)^4 before inserting a prefix floor.
It supplies the varying pieces between the exact clipped-envelope switches. -/
noncomputable def gaussianFloorRawBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2

/-- The exact scale sigma_N(D) at which the raw cutoff reaches N.
Use the fixed floor radius and the quadratic root equation.
No rounded decimal appears in this boundary definition. -/
noncomputable def gaussianFloorSwitch (f : Bool) (N : ℝ) : ℝ :=
  (gaussianMRRefinedD * Real.sqrt ((5 / 6) * N) -
      gaussianMRRefinedBeta * Real.sqrt (Real.sqrt ((5 / 6) * N)) -
      gaussianFloorConstant f) /
    gaussianMRRefinedConductor

/-- For N>=35000, the fourth-root floor sqrt(sqrt(5N/6)) is at least thirteen.
Square twice using the rational lower bound on N. -/
theorem gaussianFloor_floor_thirteen {N : ℝ} (hN : 35000 ≤ N) :
    (13 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6) * N)) := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * N := by linarith only [hN]
  have h4 : (13 : ℝ) ^ 4 ≤ (5 / 6) * N := by linarith only [hN]
  have h2 : (13 : ℝ) ^ 2 ≤ Real.sqrt ((5 / 6) * N) :=
    (Real.le_sqrt (by norm_num only) h0).mpr (by nlinarith only [h4])
  exact (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg _)).mpr h2

/-- For L>=0 and N>=35000, comparing the raw root with the N-floor is equivalent
to comparing L with sigma_N(D), in both directions. Factor the quadratic
difference and use its positive radius factor and conductor coefficient. -/
theorem gaussianFloor_raw_root_compare {f : Bool} {L N : ℝ} (hL : 0 ≤ L) (hN : 35000 ≤ N) :
    (gaussianFloorRawRoot f L ≤ Real.sqrt (Real.sqrt ((5 / 6) * N)) ↔ L ≤ gaussianFloorSwitch f N) ∧
      (Real.sqrt (Real.sqrt ((5 / 6) * N)) ≤ gaussianFloorRawRoot f L ↔
        gaussianFloorSwitch f N ≤ L) := by
  let y := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * N))
  let t := gaussianFloorRawRoot f L
  have hy : (13 : ℝ) ≤ y := gaussianFloor_floor_thirteen hN
  have ht : 0 < t := gaussianFloor_raw_pos f L
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hb : gaussianMRRefinedBeta < 13 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have hdy := mul_le_mul_of_nonneg_left hy hd.le
  have hdt := mul_pos hd ht
  have hfac : 0 < gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta := by
    linarith only [hdy, hdt, hb]
  have he := gaussianFloor_raw_equation f hL
  change
    gaussianMRRefinedD * t ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * t + gaussianFloorConstant f at he
  have hsq : y ^ 2 = Real.sqrt ((5 / 6) * N) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hid :
    (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
      gaussianMRRefinedConductor * (gaussianFloorSwitch f N - L) := by
    rw [gaussianFloorSwitch]
    conv_rhs =>
      rw [mul_sub, mul_div_cancel₀ _ hc.ne', ← hsq,
        Real.sqrt_sq (by linarith only [hy] : (0 : ℝ) ≤ y)]
    change
      (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
        gaussianMRRefinedD * y ^ 2 - gaussianMRRefinedBeta * y - gaussianFloorConstant f -
          gaussianMRRefinedConductor * L
    nlinarith only [he]
  have hneg :
    (t - y) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
      gaussianMRRefinedConductor * (L - gaussianFloorSwitch f N) := by
    linarith only [hid]
  constructor
  · have hi : (t ≤ y) ↔ 0 ≤ (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) := by
      rw [mul_nonneg_iff_of_pos_right hfac, sub_nonneg]
    rw [hid, mul_nonneg_iff_of_pos_left hc, sub_nonneg] at hi
    exact hi
  · have hi : (y ≤ t) ↔ 0 ≤ (t - y) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) := by
      rw [mul_nonneg_iff_of_pos_right hfac, sub_nonneg]
    rw [hneg, mul_nonneg_iff_of_pos_left hc, sub_nonneg] at hi
    exact hi

/-- For L>=0 and N>=35000, the raw cutoff is below N exactly when L<=sigma_N(D),
and above N exactly when sigma_N(D)<=L. Square nonnegative radii twice and
apply the exact root comparison. This certifies all piecewise boundaries. -/
theorem gaussianFloor_raw_bound_compare {f : Bool} {L N : ℝ} (hL : 0 ≤ L) (hN : 35000 ≤ N) :
    (gaussianFloorRawBound f L ≤ N ↔ L ≤ gaussianFloorSwitch f N) ∧
      (N ≤ gaussianFloorRawBound f L ↔ gaussianFloorSwitch f N ≤ L) := by
  let y := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * N))
  have hy := (Real.sqrt_nonneg (Real.sqrt ((5 / 6 : ℝ) * N)))
  have ht := (gaussianFloor_raw_pos f L).le
  have h0 : 0 ≤ (5 / 6 : ℝ) * N := by linarith only [hN]
  have hid : (6 / 5 : ℝ) * (y ^ 2) ^ 2 = N := by
    dsimp only [y]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h0]
    ring
  have hroot := gaussianFloor_raw_root_compare (f := f) hL hN
  constructor
  · apply Iff.trans _ hroot.1
    constructor
    · intro hb
      have h4 : (gaussianFloorRawRoot f L ^ 2) ^ 2 ≤ (y ^ 2) ^ 2 := by
        change (6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2 ≤ N at hb
        linarith only [hb, hid]
      exact (sq_le_sq₀ ht hy).mp ((sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp h4)
    · intro hr
      have h2 := (sq_le_sq₀ ht hy).mpr hr
      have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
      change (6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2 ≤ N
      linarith only [h4, hid]
  · apply Iff.trans _ hroot.2
    constructor
    · intro hb
      have h4 : (y ^ 2) ^ 2 ≤ (gaussianFloorRawRoot f L ^ 2) ^ 2 := by
        change N ≤ (6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2 at hb
        linarith only [hb, hid]
      exact (sq_le_sq₀ hy ht).mp ((sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp h4)
    · intro hr
      have h2 := (sq_le_sq₀ hy ht).mpr hr
      have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
      change N ≤ (6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2
      linarith only [h4, hid]

/-- For L>=0, the raw 50000-profile root is strictly below the raw 35000-profile root.
The coefficients agree and the residual allowance 111/20 is below 29/5.
Strict square-root monotonicity gives the comparison. -/
theorem gaussianFloor_raw_profiles_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianFloorRawRoot true L < gaussianFloorRawRoot false L := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hdisc :
    0 ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianFloorConstant true) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc hL) (gaussianFloor_constant_pos true).le))
  have hconst : gaussianFloorConstant true < gaussianFloorConstant false := by
    norm_num only [gaussianFloorConstant, ite_true, ite_false, Bool.false_eq_true]
  have hmul := mul_lt_mul_of_pos_left hconst (mul_pos (by norm_num only : (0 : ℝ) < 4) hd)
  have hrad :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianFloorConstant true) <
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianFloorConstant false) := by
    linarith only [hmul]
  have hs := Real.sqrt_lt_sqrt hdisc hrad
  change
    (gaussianMRRefinedBeta + _) / (2 * gaussianMRRefinedD) <
      (gaussianMRRefinedBeta + _) / (2 * gaussianMRRefinedD)
  apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num only) hd)).mpr
  linarith only [hs]

/-- For L>=0, the raw 50000-profile cutoff is below the raw 35000-profile cutoff.
Square the positive root comparison twice and multiply by six fifths. -/
theorem gaussianFloor_raw_bounds_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianFloorRawBound true L < gaussianFloorRawBound false L := by
  have h2 :=
    (sq_lt_sq₀ (gaussianFloor_raw_pos true L).le (gaussianFloor_raw_pos false L).le).mpr
      (gaussianFloor_raw_profiles_lt hL)
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- The first switch sigma_35000(29/5) lies strictly between 240 and 242.
Rational square-root enclosures prove this interval, without sampled crossing values. -/
theorem gaussianFloor_switch35_bounds :
    (240 : ℝ) < gaussianFloorSwitch false 35000 ∧ gaussianFloorSwitch false 35000 < 242 := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hRlo : (8539 / 50 : ℝ) ≤ Real.sqrt ((5 / 6 : ℝ) * 35000) :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hRhi : Real.sqrt ((5 / 6 : ℝ) * 35000) ≤ (17079 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hSlo : (13 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 35000)) :=
    gaussianFloor_floor_thirteen (by norm_num only)
  have hShi : Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 35000)) ≤ (131 / 10 : ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by norm_num only, ?_⟩
    exact Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  dsimp only [gaussianFloorSwitch]
  constructor
  · apply (lt_div_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex, gaussianFloorConstant, Bool.false_eq_true, ite_false,
      ite_true] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRlo, hShi]
  · apply (div_lt_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex, gaussianFloorConstant, Bool.false_eq_true, ite_false,
      ite_true] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRhi, hSlo]

/-- Both switches at floor 50000 lie strictly between 293 and 294.
Rational enclosures for the radius and root, together with the two allowed
residual constants, certify the complete parameter cases. -/
theorem gaussianFloor_switch50_bounds (f : Bool) :
    (293 : ℝ) < gaussianFloorSwitch f 50000 ∧ gaussianFloorSwitch f 50000 < 294 := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hDlo : (111 / 20 : ℝ) ≤ gaussianFloorConstant f := by
    cases f <;> norm_num only [gaussianFloorConstant, Bool.false_eq_true, ite_false, ite_true]
  have hDhi : gaussianFloorConstant f ≤ (29 / 5 : ℝ) := by
    cases f <;> norm_num only [gaussianFloorConstant, Bool.false_eq_true, ite_false, ite_true]
  have hRlo : (5103 / 25 : ℝ) ≤ Real.sqrt ((5 / 6 : ℝ) * 50000) :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hRhi : Real.sqrt ((5 / 6 : ℝ) * 50000) ≤ (20413 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hSlo : (357 / 25 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 50000)) := by
    apply (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg _)).mpr
    exact (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hShi : Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 50000)) ≤ (1429 / 100 : ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by norm_num only, ?_⟩
    exact Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  dsimp only [gaussianFloorSwitch]
  constructor
  · apply (lt_div_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRlo, hShi, hDhi]
  · apply (div_lt_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRhi, hSlo, hDlo]

/-- The three switching scales are strictly ordered.
Separate the first two by their rational intervals, then compare the last two
using the exact residual-constant difference and positive conductor coefficient. -/
theorem gaussianFloor_switch_order :
    gaussianFloorSwitch false 35000 < gaussianFloorSwitch false 50000 ∧
      gaussianFloorSwitch false 50000 < gaussianFloorSwitch true 50000 := by
  constructor
  · linarith only [gaussianFloor_switch35_bounds.2, (gaussianFloor_switch50_bounds false).1]
  · dsimp only [gaussianFloorSwitch]
    apply
      (div_lt_div_iff_of_pos_right
          (by norm_num only [gaussianMRRefinedConductor] : 0 < gaussianMRRefinedConductor)).mpr
    norm_num only [gaussianFloorConstant, Bool.false_eq_true, ite_false, ite_true]
    linarith only

/-- At every certified nonnegative switching scale, the raw cutoff equals N.
Apply both directions of the cutoff comparison and antisymmetry.
This proves equality of the adjacent formulas at each boundary. -/
theorem gaussianFloor_raw_at_switch {f : Bool} {N : ℝ} (hN : 35000 ≤ N)
    (hS : 0 ≤ gaussianFloorSwitch f N) : gaussianFloorRawBound f (gaussianFloorSwitch f N) = N := by
  have h := gaussianFloor_raw_bound_compare (f := f) hS hN
  exact le_antisymm (h.1.mpr le_rfl) (h.2.mpr le_rfl)

/-- The four explicit pieces of the clipped Gaussian envelope: 35000, raw35,50000,raw50.
The boundaries are sigma_35000(29/5),sigma_50000(29/5),sigma_50000(111/20). -/
noncomputable def gaussianFloorSelected (L : ℝ) : ℝ :=
  if L ≤ gaussianFloorSwitch false 35000 then 35000
  else
    if L < gaussianFloorSwitch false 50000 then gaussianFloorRawBound false L
    else if L ≤ gaussianFloorSwitch true 50000 then 50000 else gaussianFloorRawBound true L

/-- Each clipped profile is exactly the maximum of its prefix floor and raw cutoff.
This restates the clipping identity using the named raw bound. -/
theorem gaussianFloor_eq_max (f : Bool) (L : ℝ) :
    gaussianFloorBound f L = max (gaussianFloorCutoff f : ℝ) (gaussianFloorRawBound f L) :=
  gaussianFloor_bound_eq_max f L

/-- For L>=63, the two-profile minimum equals the four-piece selected function.
Apply the exact cutoff comparisons and strict ordering of the raw profiles
in each interval. No unresolved minimum remains in the Gaussian interval table. -/
theorem gaussianFloor_min_eq_selected {L : ℝ} (hL : 63 ≤ L) :
    min (gaussianFloorBound false L) (gaussianFloorBound true L) = gaussianFloorSelected L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hprof := (gaussianFloor_raw_bounds_lt h0).le
  rw [gaussianFloor_eq_max false L, gaussianFloor_eq_max true L]
  norm_num only [gaussianFloorCutoff, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  by_cases h35 : L ≤ gaussianFloorSwitch false 35000
  · have ha :=
      (gaussianFloor_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 35000)).1.mpr
        h35
    have hb : gaussianFloorRawBound true L ≤ (50000 : ℝ) := by linarith only [hprof, ha]
    simp only [gaussianFloorSelected, ite_eq_left h35, max_eq_left ha, max_eq_left hb,
      min_eq_left (by norm_num only : (35000 : ℝ) ≤ 50000)]
  · have ha :=
      (gaussianFloor_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 35000)).2.mpr
        (le_of_not_ge h35)
    by_cases h50 : L < gaussianFloorSwitch false 50000
    · have hb :=
        (gaussianFloor_raw_bound_compare (f := false) h0
              (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
          h50.le
      have hc : gaussianFloorRawBound true L ≤ (50000 : ℝ) := hprof.trans hb
      simp only [gaussianFloorSelected, ite_eq_right h35, ite_eq_left h50, max_eq_right ha,
        max_eq_left hc, min_eq_left hb]
    · have hb :=
        (gaussianFloor_raw_bound_compare (f := false) h0
              (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
          (le_of_not_gt h50)
      by_cases hlast : L ≤ gaussianFloorSwitch true 50000
      · have hc :=
          (gaussianFloor_raw_bound_compare (f := true) h0
                (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
            hlast
        simp only [gaussianFloorSelected, ite_eq_right h35, ite_eq_right h50, ite_eq_left hlast,
          max_eq_right ha, max_eq_left hc, min_eq_right hb]
      · have hc :=
          (gaussianFloor_raw_bound_compare (f := true) h0
                (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
            (le_of_not_ge hlast)
        simp only [gaussianFloorSelected, ite_eq_right h35, ite_eq_right h50, ite_eq_right hlast,
          max_eq_right ha, max_eq_right hc, min_eq_right hprof]

/-- For L>=240, raw35 is strictly below the existing B6 cutoff.
Compare their positive-root equations using the improved mass, conductor, width
and allowance, then square twice. This is a continuous half-line comparison. -/
theorem gaussianFloor35_raw_lt_six {L : ℝ} (hL : 240 ≤ L) :
    gaussianFloorRawBound false L < gaussianMR6Bound L := by
  let s := gaussianFloorRawRoot false L
  let t := gaussianMR6Root L
  have hs : 0 < s := gaussianFloor_raw_pos false L
  have ht : (13 : ℝ) ≤ t := by linarith only [gaussianMR6_root_lower hL]
  have he := gaussianFloor_raw_equation false (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hf := gaussianMR6_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  dsimp only [gaussianMR6Radius] at hf
  have hst : s < t := by
    by_contra h
    have hts : t ≤ s := le_of_not_gt h
    have hp := mul_nonneg (sub_nonneg.mpr hts) (by linarith only [hs, ht] : (0 : ℝ) ≤ s + t - 13)
    change
      gaussianMRRefinedD * s ^ 2 =
        gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s +
          gaussianFloorConstant false at he
    change
      gaussianMR6FifthsD * t ^ 2 =
        gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * t + 6 at hf
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsD, gaussianMR6FifthsBeta,
      gaussianMR6FifthsConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianFloorConstant, Bool.false_eq_true, ite_false] at he hf
    nlinarith only [he, hf, hp, hts, hL, hs, ht, sq_nonneg t]
  have h2 := (sq_lt_sq₀ hs.le (by linarith only [ht] : (0 : ℝ) ≤ t)).mpr hst
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- For L>=300, raw50 is strictly below the existing refined Gaussian cutoff.
The coefficients agree and 111/20<28/5. Compare the root equations and square twice. -/
theorem gaussianFloor50_raw_lt_refined {L : ℝ} (hL : 300 ≤ L) :
    gaussianFloorRawBound true L < gaussianMRRefinedBound L := by
  let s := gaussianFloorRawRoot true L
  let t := gaussianMRRefinedRoot L
  have hs : 0 < s := gaussianFloor_raw_pos true L
  have ht : (14 : ℝ) ≤ t := gaussianMRRefined_root_lower hL
  have he := gaussianFloor_raw_equation true (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hf := gaussianMRRefined_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  dsimp only [gaussianMRRefinedRadius] at hf
  have hst : s < t := by
    by_contra h
    have hts : t ≤ s := le_of_not_gt h
    have hp := mul_nonneg (sub_nonneg.mpr hts) (by linarith only [hs, ht] : (0 : ℝ) ≤ s + t - 13)
    change
      gaussianMRRefinedD * s ^ 2 =
        gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s +
          gaussianFloorConstant true at he
    change
      gaussianMRRefinedD * t ^ 2 =
        gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * t + 28 / 5 at hf
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, gaussianFloorConstant, ite_true] at he hf
    nlinarith only [he, hf, hp, hts, hL, hs, ht]
  have h2 := (sq_lt_sq₀ hs.le (by linarith only [ht] : (0 : ℝ) ≤ t)).mpr hst
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- For L>=240, the clipped 35000 profile is below B6.
Both its floor and raw cutoff are strictly below B6, so their maximum is too. -/
theorem gaussianFloor35_lt_six {L : ℝ} (hL : 240 ≤ L) :
    gaussianFloorBound false L < gaussianMR6Bound L := by
  rw [gaussianFloor_eq_max]
  norm_num only [gaussianFloorCutoff, Bool.false_eq_true, ite_false, Nat.cast_ofNat]
  exact max_lt (gaussianMR6_prefix35000 hL) (gaussianFloor35_raw_lt_six hL)

/-- For L>=300, the clipped 50000 profile is below the existing refined cutoff.
Both its floor and raw cutoff are strictly below that cutoff. -/
theorem gaussianFloor50_lt_refined {L : ℝ} (hL : 300 ≤ L) :
    gaussianFloorBound true L < gaussianMRRefinedBound L := by
  rw [gaussianFloor_eq_max]
  norm_num only [gaussianFloorCutoff, ite_true, Nat.cast_ofNat]
  exact max_lt (gaussianMRRefined_prefix50000 hL) (gaussianFloor50_raw_lt_refined hL)

/-- At scales at or below the first exact Gaussian switch, the selected value is 35000.
This is the first branch of the explicit piecewise definition. -/
theorem gaussianFloorSelected_eq_fixed {L : ℝ} (hL : L ≤ gaussianFloorSwitch false 35000) :
    gaussianFloorSelected L = 35000 := by exact ite_eq_left hL

/-- For L>=63, the selected Gaussian envelope exceeds (15/32)L^2.
Both profiles satisfy the strict lower comparison, so their minimum does too. -/
theorem gaussianFloorSelected_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianFloorSelected L := by
  rw [← gaussianFloor_min_eq_selected hL]
  exact
    lt_min (gaussianFloor_bound_lower (f := false) hL) (gaussianFloor_bound_lower (f := true) hL)

end PseudoPrime.Analysis
