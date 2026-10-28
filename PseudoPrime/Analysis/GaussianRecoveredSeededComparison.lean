/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianRecoveredSeededNumerics
public import PseudoPrime.Analysis.GaussianMRClippedComparison
public import PseudoPrime.Analysis.GaussianBudgetRoots
public import PseudoPrime.Analysis.GaussianMRSeededComparison

/-! # Exact comparisons for seeded Gaussian profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The raw cutoff (6/5)t_D(L)^4 before inserting a prefix floor.
It supplies the varying pieces between the exact clipped-envelope switches. -/
noncomputable def gaussianRecoveredSeededRawBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2

/-- The exact scale sigma_N(D) at which the raw cutoff reaches N.
Use the fixed floor radius and the quadratic root equation.
No rounded decimal appears in this boundary definition. -/
noncomputable def gaussianRecoveredSeededSwitch (f : Bool) (N : ℝ) : ℝ :=
  (gaussianMRRefinedD * Real.sqrt ((5 / 6) * N) -
      gaussianMRRefinedBeta * Real.sqrt (Real.sqrt ((5 / 6) * N)) -
      gaussianRecoveredSeededConstant f) /
    gaussianMRRefinedConductor

/-- For N>=35000, the fourth-root floor sqrt(sqrt(5N/6)) is at least thirteen.
Square twice using the rational lower bound on N. -/
theorem gaussianRecoveredSeeded_floor_thirteen {N : ℝ} (hN : 35000 ≤ N) :
    (13 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6) * N)) := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * N := by linarith only [hN]
  have h4 : (13 : ℝ) ^ 4 ≤ (5 / 6) * N := by linarith only [hN]
  have h2 : (13 : ℝ) ^ 2 ≤ Real.sqrt ((5 / 6) * N) :=
    (Real.le_sqrt (by norm_num only) h0).mpr (by nlinarith only [h4])
  exact (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg _)).mpr h2

/-- For L>=0 and N>=35000, comparing the raw root with the N-floor is equivalent
to comparing L with sigma_N(D), in both directions. Factor the quadratic
difference and use its positive radius factor and conductor coefficient. -/
theorem gaussianRecoveredSeeded_raw_root_compare {f : Bool} {L N : ℝ} (hL : 0 ≤ L)
    (hN : 35000 ≤ N) :
    (gaussianRecoveredSeededRawRoot f L ≤ Real.sqrt (Real.sqrt ((5 / 6) * N)) ↔
        L ≤ gaussianRecoveredSeededSwitch f N) ∧
      (Real.sqrt (Real.sqrt ((5 / 6) * N)) ≤ gaussianRecoveredSeededRawRoot f L ↔
        gaussianRecoveredSeededSwitch f N ≤ L) := by
  let y := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * N))
  let t := gaussianRecoveredSeededRawRoot f L
  have hy : (13 : ℝ) ≤ y := gaussianRecoveredSeeded_floor_thirteen hN
  have ht : 0 < t := gaussianRecoveredSeeded_raw_pos f L
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hb : gaussianMRRefinedBeta < 13 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have hdy := mul_le_mul_of_nonneg_left hy hd.le
  have hdt := mul_pos hd ht
  have hfac : 0 < gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta := by
    linarith only [hdy, hdt, hb]
  have he := gaussianRecoveredSeeded_raw_equation f hL
  change
    gaussianMRRefinedD * t ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * t +
        gaussianRecoveredSeededConstant f at he
  have hsq : y ^ 2 = Real.sqrt ((5 / 6) * N) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hid :
    (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
      gaussianMRRefinedConductor * (gaussianRecoveredSeededSwitch f N - L) := by
    rw [gaussianRecoveredSeededSwitch]
    conv_rhs =>
      rw [mul_sub, mul_div_cancel₀ _ hc.ne', ← hsq,
        Real.sqrt_sq (by linarith only [hy] : (0 : ℝ) ≤ y)]
    change
      (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
        gaussianMRRefinedD * y ^ 2 - gaussianMRRefinedBeta * y - gaussianRecoveredSeededConstant f -
          gaussianMRRefinedConductor * L
    nlinarith only [he]
  have hneg :
    (t - y) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
      gaussianMRRefinedConductor * (L - gaussianRecoveredSeededSwitch f N) := by
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
theorem gaussianRecoveredSeeded_raw_bound_compare {f : Bool} {L N : ℝ} (hL : 0 ≤ L)
    (hN : 35000 ≤ N) :
    (gaussianRecoveredSeededRawBound f L ≤ N ↔ L ≤ gaussianRecoveredSeededSwitch f N) ∧
      (N ≤ gaussianRecoveredSeededRawBound f L ↔ gaussianRecoveredSeededSwitch f N ≤ L) := by
  let y := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * N))
  have hy := (Real.sqrt_nonneg (Real.sqrt ((5 / 6 : ℝ) * N)))
  have ht := (gaussianRecoveredSeeded_raw_pos f L).le
  have h0 : 0 ≤ (5 / 6 : ℝ) * N := by linarith only [hN]
  have hid : (6 / 5 : ℝ) * (y ^ 2) ^ 2 = N := by
    dsimp only [y]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h0]
    ring
  have hroot := gaussianRecoveredSeeded_raw_root_compare (f := f) hL hN
  constructor
  · apply Iff.trans _ hroot.1
    constructor
    · intro hb
      have h4 : (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2 ≤ (y ^ 2) ^ 2 := by
        change (6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2 ≤ N at hb
        linarith only [hb, hid]
      exact (sq_le_sq₀ ht hy).mp ((sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp h4)
    · intro hr
      have h2 := (sq_le_sq₀ ht hy).mpr hr
      have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
      change (6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2 ≤ N
      linarith only [h4, hid]
  · apply Iff.trans _ hroot.2
    constructor
    · intro hb
      have h4 : (y ^ 2) ^ 2 ≤ (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2 := by
        change N ≤ (6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2 at hb
        linarith only [hb, hid]
      exact (sq_le_sq₀ hy ht).mp ((sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp h4)
    · intro hr
      have h2 := (sq_le_sq₀ hy ht).mpr hr
      have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
      change N ≤ (6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2
      linarith only [h4, hid]

/-- For L>=0, the raw 50000-profile root is strictly below the raw 35000-profile root.
The coefficients agree and the residual allowance 136/25 is below 283/50.
Strict square-root monotonicity gives the comparison. -/
theorem gaussianRecoveredSeeded_raw_profiles_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianRecoveredSeededRawRoot true L < gaussianRecoveredSeededRawRoot false L := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hdisc :
    0 ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant true) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc hL) (gaussianRecoveredSeeded_constant_pos true).le))
  have hconst : gaussianRecoveredSeededConstant true < gaussianRecoveredSeededConstant false := by
    norm_num only [gaussianRecoveredSeededConstant, ite_true, ite_false, Bool.false_eq_true]
  have hmul := mul_lt_mul_of_pos_left hconst (mul_pos (by norm_num only : (0 : ℝ) < 4) hd)
  have hrad :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant true) <
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant false) := by
    linarith only [hmul]
  have hs := Real.sqrt_lt_sqrt hdisc hrad
  change
    (gaussianMRRefinedBeta + _) / (2 * gaussianMRRefinedD) <
      (gaussianMRRefinedBeta + _) / (2 * gaussianMRRefinedD)
  apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num only) hd)).mpr
  linarith only [hs]

/-- For L>=0, the raw 50000-profile cutoff is below the raw 35000-profile cutoff.
Square the positive root comparison twice and multiply by six fifths. -/
theorem gaussianRecoveredSeeded_raw_bounds_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianRecoveredSeededRawBound true L < gaussianRecoveredSeededRawBound false L := by
  have h2 :=
    (sq_lt_sq₀ (gaussianRecoveredSeeded_raw_pos true L).le
          (gaussianRecoveredSeeded_raw_pos false L).le).mpr
      (gaussianRecoveredSeeded_raw_profiles_lt hL)
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- The first switch sigma_35000(283/50) lies strictly between 240 and 242.
Rational square-root enclosures prove this interval, without sampled crossing values. -/
theorem gaussianRecoveredSeeded_switch35_bounds :
    (240 : ℝ) < gaussianRecoveredSeededSwitch false 35000 ∧
      gaussianRecoveredSeededSwitch false 35000 < 242 := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hRlo : (8539 / 50 : ℝ) ≤ Real.sqrt ((5 / 6 : ℝ) * 35000) :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hRhi : Real.sqrt ((5 / 6 : ℝ) * 35000) ≤ (17079 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hSlo : (13 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 35000)) :=
    gaussianRecoveredSeeded_floor_thirteen (by norm_num only)
  have hShi : Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 35000)) ≤ (131 / 10 : ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by norm_num only, ?_⟩
    exact Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  dsimp only [gaussianRecoveredSeededSwitch]
  constructor
  · apply (lt_div_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex, gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false,
      ite_true] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRlo, hShi]
  · apply (div_lt_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex, gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false,
      ite_true] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRhi, hSlo]

/-- Both switches at floor 50000 lie strictly between 293 and 295.
Rational enclosures for the radius and root, together with the two allowed
residual constants, certify the complete parameter cases. -/
theorem gaussianRecoveredSeeded_switch50_bounds (f : Bool) :
    (293 : ℝ) < gaussianRecoveredSeededSwitch f 50000 ∧
      gaussianRecoveredSeededSwitch f 50000 < 295 := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hDlo : (136 / 25 : ℝ) ≤ gaussianRecoveredSeededConstant f := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false, ite_true]
  have hDhi : gaussianRecoveredSeededConstant f ≤ (283 / 50 : ℝ) := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false, ite_true]
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
  dsimp only [gaussianRecoveredSeededSwitch]
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
theorem gaussianRecoveredSeeded_switch_order :
    gaussianRecoveredSeededSwitch false 35000 < gaussianRecoveredSeededSwitch false 50000 ∧
      gaussianRecoveredSeededSwitch false 50000 < gaussianRecoveredSeededSwitch true 50000 := by
  constructor
  · linarith only [gaussianRecoveredSeeded_switch35_bounds.2,
      (gaussianRecoveredSeeded_switch50_bounds false).1]
  · dsimp only [gaussianRecoveredSeededSwitch]
    apply
      (div_lt_div_iff_of_pos_right
          (by norm_num only [gaussianMRRefinedConductor] : 0 < gaussianMRRefinedConductor)).mpr
    norm_num only [gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false, ite_true]
    linarith only

/-- At every certified nonnegative switching scale, the raw cutoff equals N.
Apply both directions of the cutoff comparison and antisymmetry.
This proves equality of the adjacent formulas at each boundary. -/
theorem gaussianRecoveredSeeded_raw_at_switch {f : Bool} {N : ℝ} (hN : 35000 ≤ N)
    (hS : 0 ≤ gaussianRecoveredSeededSwitch f N) :
    gaussianRecoveredSeededRawBound f (gaussianRecoveredSeededSwitch f N) = N := by
  have h := gaussianRecoveredSeeded_raw_bound_compare (f := f) hS hN
  exact le_antisymm (h.1.mpr le_rfl) (h.2.mpr le_rfl)

/-- The four explicit pieces of the clipped Gaussian envelope: 35000, raw35,50000,raw50.
The boundaries are sigma_35000(283/50),sigma_50000(283/50),sigma_50000(136/25). -/
noncomputable def gaussianRecoveredSeededSelected (L : ℝ) : ℝ :=
  if L ≤ gaussianRecoveredSeededSwitch false 35000 then 35000
  else
    if L < gaussianRecoveredSeededSwitch false 50000 then gaussianRecoveredSeededRawBound false L
    else
      if L ≤ gaussianRecoveredSeededSwitch true 50000 then 50000
      else gaussianRecoveredSeededRawBound true L

/-- Each clipped profile is exactly the maximum of its prefix floor and raw cutoff.
This restates the clipping identity using the named raw bound. -/
theorem gaussianRecoveredSeeded_eq_max (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededBound f L =
      max (gaussianRecoveredSeededCutoff f : ℝ) (gaussianRecoveredSeededRawBound f L) :=
  gaussianRecoveredSeeded_bound_eq_max f L

/-- For L>=63, the two-profile minimum equals the four-piece selected function.
Apply the exact cutoff comparisons and strict ordering of the raw profiles
in each interval. No unresolved minimum remains in the Gaussian interval table. -/
theorem gaussianRecoveredSeeded_min_eq_selected {L : ℝ} (hL : 63 ≤ L) :
    min (gaussianRecoveredSeededBound false L) (gaussianRecoveredSeededBound true L) =
      gaussianRecoveredSeededSelected L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hprof := (gaussianRecoveredSeeded_raw_bounds_lt h0).le
  rw [gaussianRecoveredSeeded_eq_max false L, gaussianRecoveredSeeded_eq_max true L]
  norm_num only [gaussianRecoveredSeededCutoff, Bool.false_eq_true, ite_false, ite_true,
    Nat.cast_ofNat]
  by_cases h35 : L ≤ gaussianRecoveredSeededSwitch false 35000
  · have ha :=
      (gaussianRecoveredSeeded_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 35000)).1.mpr
        h35
    have hb : gaussianRecoveredSeededRawBound true L ≤ (50000 : ℝ) := by linarith only [hprof, ha]
    simp only [gaussianRecoveredSeededSelected, ite_eq_left h35, max_eq_left ha, max_eq_left hb,
      min_eq_left (by norm_num only : (35000 : ℝ) ≤ 50000)]
  · have ha :=
      (gaussianRecoveredSeeded_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 35000)).2.mpr
        (le_of_not_ge h35)
    by_cases h50 : L < gaussianRecoveredSeededSwitch false 50000
    · have hb :=
        (gaussianRecoveredSeeded_raw_bound_compare (f := false) h0
              (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
          h50.le
      have hc : gaussianRecoveredSeededRawBound true L ≤ (50000 : ℝ) := hprof.trans hb
      simp only [gaussianRecoveredSeededSelected, ite_eq_right h35, ite_eq_left h50,
        max_eq_right ha, max_eq_left hc, min_eq_left hb]
    · have hb :=
        (gaussianRecoveredSeeded_raw_bound_compare (f := false) h0
              (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
          (le_of_not_gt h50)
      by_cases hlast : L ≤ gaussianRecoveredSeededSwitch true 50000
      · have hc :=
          (gaussianRecoveredSeeded_raw_bound_compare (f := true) h0
                (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
            hlast
        simp only [gaussianRecoveredSeededSelected, ite_eq_right h35, ite_eq_right h50,
          ite_eq_left hlast, max_eq_right ha, max_eq_left hc, min_eq_right hb]
      · have hc :=
          (gaussianRecoveredSeeded_raw_bound_compare (f := true) h0
                (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
            (le_of_not_ge hlast)
        simp only [gaussianRecoveredSeededSelected, ite_eq_right h35, ite_eq_right h50,
          ite_eq_right hlast, max_eq_right ha, max_eq_right hc, min_eq_right hprof]

/-- The exact horizontal shift induced by decreasing each seeded residual
allowance by 1/100. Only numerical function comparisons use this shift. -/
noncomputable def gaussianRecoveredSeededShift : ℝ :=
  500000 / 20115621

/-- Both recovered constants differ from their baseline counterparts by 1/100.
This algebraic identity does not change the input of an actual witness theorem. -/
theorem gaussianRecoveredSeeded_constant_shift (f : Bool) :
    gaussianRecoveredSeededConstant f = gaussianSeededConstant f - 1 / 100 := by
  cases f <;>
    norm_num only [gaussianRecoveredSeededConstant, gaussianSeededConstant, Bool.false_eq_true,
      ite_false, ite_true]

/-- Each recovered raw root equals the baseline raw root at L-delta.
Expand the common discriminant and compare its affine constant terms. -/
theorem gaussianRecoveredSeeded_raw_shift (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededRawRoot f L =
      gaussianSeededRawRoot f (L - gaussianRecoveredSeededShift) := by
  have he :
    gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f =
      gaussianMRRefinedConductor * (L - gaussianRecoveredSeededShift) +
        gaussianSeededConstant f := by
    rw [gaussianRecoveredSeeded_constant_shift]
    norm_num only [gaussianMRRefinedConductor, gaussianRecoveredSeededShift]
    ring
  rw [gaussianRecoveredSeededRawRoot, gaussianSeededRawRoot, he]

/-- The clipped recovered root has the same exact horizontal shift.
The prefix floor is unchanged in both profiles. -/
theorem gaussianRecoveredSeeded_root_shift (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededRoot f L = gaussianSeededRoot f (L - gaussianRecoveredSeededShift) := by
  rw [gaussianRecoveredSeededRoot, gaussianSeededRoot, gaussianRecoveredSeeded_raw_shift]
  rfl

/-- The full clipped bound inherits the exact shift, including its constant floor. -/
theorem gaussianRecoveredSeeded_bound_shift (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededBound f L =
      gaussianSeededBound f (L - gaussianRecoveredSeededShift) := by
  simp only [gaussianRecoveredSeededBound, gaussianSeededBound, gaussianRecoveredSeededRadius,
    gaussianSeededRadius, gaussianRecoveredSeeded_root_shift]

/-- The raw cutoff before clipping inherits the same exact shift. -/
theorem gaussianRecoveredSeeded_rawBound_shift (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededRawBound f L =
      gaussianSeededRawBound f (L - gaussianRecoveredSeededShift) := by
  simp only [gaussianRecoveredSeededRawBound, gaussianSeededRawBound,
    gaussianRecoveredSeeded_raw_shift]

/-- Every exact floor crossing increases by delta under the recovered prefix.
No decimal approximation is used as a switching guard. -/
theorem gaussianRecoveredSeeded_switch_shift (f : Bool) (N : ℝ) :
    gaussianRecoveredSeededSwitch f N =
      gaussianSeededSwitch f N + gaussianRecoveredSeededShift := by
  rw [gaussianRecoveredSeededSwitch, gaussianSeededSwitch, gaussianRecoveredSeeded_constant_shift]
  norm_num only [gaussianMRRefinedConductor, gaussianRecoveredSeededShift]
  ring

/-- The recovered four-piece selected function is the horizontally shifted baseline
selected function at every real level, without a domain assumption. -/
theorem gaussianRecoveredSeeded_selected_shift (L : ℝ) :
    gaussianRecoveredSeededSelected L =
      gaussianSeededSelected (L - gaussianRecoveredSeededShift) := by
  simp only [gaussianRecoveredSeededSelected, gaussianSeededSelected,
    gaussianRecoveredSeeded_switch_shift, gaussianRecoveredSeeded_rawBound_shift, sub_le_iff_le_add,
    sub_lt_iff_lt_add]

/-- At every real level each recovered raw root is no larger than its baseline
root. Apply global square-root monotonicity to the smaller residual constant. -/
theorem gaussianRecoveredSeeded_raw_le_old (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededRawRoot f L ≤ gaussianSeededRawRoot f L := by
  have hconst : gaussianRecoveredSeededConstant f ≤ gaussianSeededConstant f := by
    rw [gaussianRecoveredSeeded_constant_shift]
    linarith only
  have hd := gaussianMRRefined_coefficients.1
  have hrad := mul_le_mul_of_nonneg_left hconst (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd.le)
  have hrad' :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianSeededConstant f) := by
    linarith only [hrad]
  have hroot := add_le_add_left (Real.sqrt_le_sqrt hrad') gaussianMRRefinedBeta
  exact
    div_le_div_of_nonneg_right (by linarith only [hroot])
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hd.le)

/-- Each recovered clipped cutoff preserves the baseline upper bound globally.
Use the unchanged floor, then square nonnegative roots twice. -/
theorem gaussianRecoveredSeeded_le_old (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededBound f L ≤ gaussianSeededBound f L := by
  have hr : gaussianRecoveredSeededRoot f L ≤ gaussianSeededRoot f L := by
    apply max_le_max
    · rfl
    · exact gaussianRecoveredSeeded_raw_le_old f L
  have h2 :=
    (sq_le_sq₀ (gaussianRecoveredSeeded_root_pos f L).le (gaussianSeeded_root_pos f L).le).mpr hr
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- At nonnegative levels the raw recovered cutoff is strictly smaller than
its baseline counterpart. The discriminants differ by the positive residual decrease. -/
theorem gaussianRecoveredSeeded_raw_lt_old (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianRecoveredSeededRawBound f L < gaussianSeededRawBound f L := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hdisc :
    0 ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc hL) (gaussianRecoveredSeeded_constant_pos f).le))
  have hconst : gaussianRecoveredSeededConstant f < gaussianSeededConstant f := by
    rw [gaussianRecoveredSeeded_constant_shift]
    linarith only
  have hmul := mul_lt_mul_of_pos_left hconst (mul_pos (by norm_num only : (0 : ℝ) < 4) hd)
  have hdisc' :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) <
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianSeededConstant f) := by
    linarith only [hmul]
  have hs := add_lt_add_left (Real.sqrt_lt_sqrt hdisc hdisc') gaussianMRRefinedBeta
  have hr : gaussianRecoveredSeededRawRoot f L < gaussianSeededRawRoot f L :=
    (div_lt_div_iff_of_pos_right (mul_pos (by norm_num only) hd)).mpr (by linarith only [hs])
  have h2 :=
    (sq_lt_sq₀ (gaussianRecoveredSeeded_raw_pos f L).le (gaussianSeeded_raw_pos f L).le).mpr hr
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- If the baseline profile has left its floor, the recovered full profile
strictly improves it. Both the unchanged floor and smaller raw curve lie below the old raw curve. -/
theorem gaussianRecoveredSeeded_lt_old (f : Bool) {L : ℝ} (hL : 0 ≤ L)
    (hfloor : (gaussianSeededCutoff f : ℝ) < gaussianSeededRawBound f L) :
    gaussianRecoveredSeededBound f L < gaussianSeededBound f L := by
  rw [gaussianRecoveredSeeded_eq_max, gaussianSeeded_eq_max]
  have hnew :
    max (gaussianRecoveredSeededCutoff f : ℝ) (gaussianRecoveredSeededRawBound f L) <
      gaussianSeededRawBound f L :=
    max_lt hfloor (gaussianRecoveredSeeded_raw_lt_old f hL)
  exact hnew.trans_le (le_max_right _ _)

/-- The recovered selected candidate used by the public witness envelope. -/
noncomputable def gaussianRecoveredSeeded (L : ℝ) : ℝ :=
  gaussianRecoveredSeededSelected L

/-- On the certified half-line, the recovered selected function is exactly the
minimum of its two actual-prefix profiles, including the entrance strip [63,63+delta). -/
theorem gaussianRecoveredSeeded_eq_min {L : ℝ} (hL : 63 ≤ L) :
    gaussianRecoveredSeeded L =
      min (gaussianRecoveredSeededBound false L) (gaussianRecoveredSeededBound true L) := by
  exact (gaussianRecoveredSeeded_min_eq_selected hL).symm

/-- On the certified half-line, the selected recovered envelope never exceeds
the baseline selected envelope. Both profile inequalities are pointwise and global. -/
theorem gaussianRecoveredSeeded_le_seeded {L : ℝ} (hL : 63 ≤ L) :
    gaussianRecoveredSeeded L ≤ gaussianSeededSelected L := by
  rw [gaussianRecoveredSeeded_eq_min hL, ← gaussianSeeded_min_eq_selected hL]
  exact min_le_min (gaussianRecoveredSeeded_le_old false L) (gaussianRecoveredSeeded_le_old true L)

/-- The minimum of the two clipped profiles inherits the exact horizontal shift
at every real input, with no entrance-domain assumption. -/
theorem gaussianRecoveredSeeded_min_shift (L : ℝ) :
    min (gaussianRecoveredSeededBound false L) (gaussianRecoveredSeededBound true L) =
      min (gaussianSeededBound false (L - gaussianRecoveredSeededShift))
        (gaussianSeededBound true (L - gaussianRecoveredSeededShift)) := by
  rw [gaussianRecoveredSeeded_bound_shift, gaussianRecoveredSeeded_bound_shift]

/-- A baseline profile lies strictly above its floor beyond the exact switch.
Use the reverse implication of the non-strict raw-bound comparison to rule out equality. -/
theorem gaussianSeeded_raw_gt_floor (f : Bool) {L : ℝ} (hL : 0 ≤ L)
    (hS : gaussianSeededSwitch f (gaussianSeededCutoff f : ℝ) < L) :
    (gaussianSeededCutoff f : ℝ) < gaussianSeededRawBound f L := by
  have hN : (35000 : ℝ) ≤ (gaussianSeededCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianSeededCutoff, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  by_contra h
  exact (not_le.mpr hS) ((gaussianSeeded_raw_bound_compare (f := f) hL hN).1.mp (le_of_not_gt h))

/-- On the first varying baseline segment, the recovered selected envelope is
strictly smaller. Its false profile improves the baseline raw35 curve, even if
its own floor is still active immediately after the old switch. -/
theorem gaussianRecoveredSeeded_strict_first {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianSeededSwitch false 35000 < L) (hU : L < gaussianSeededSwitch false 50000) :
    gaussianRecoveredSeeded L < gaussianSeededSelected L := by
  have hfloor := gaussianSeeded_raw_gt_floor false (by linarith only [hL]) hS
  have hnew := gaussianRecoveredSeeded_lt_old false (by linarith only [hL]) hfloor
  rw [gaussianSeeded_eq_max false L, max_eq_right hfloor.le] at hnew
  have hs :=
    (min_le_left (gaussianRecoveredSeededBound false L)
          (gaussianRecoveredSeededBound true L)).trans_lt
      hnew
  rw [gaussianRecoveredSeeded_eq_min hL]
  simpa only [gaussianSeededSelected, ite_eq_right (not_le.mpr hS), ite_eq_left hU] using hs

/-- Beyond the final baseline switch, the recovered true profile strictly
improves its raw50 curve, hence so does the two-profile selected minimum. -/
theorem gaussianRecoveredSeeded_strict_last {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianSeededSwitch true 50000 < L) :
    gaussianRecoveredSeeded L < gaussianSeededSelected L := by
  have hfloor := gaussianSeeded_raw_gt_floor true (by linarith only [hL]) hS
  have hnew := gaussianRecoveredSeeded_lt_old true (by linarith only [hL]) hfloor
  rw [gaussianSeeded_eq_max true L, max_eq_right hfloor.le] at hnew
  have hs :=
    (min_le_right (gaussianRecoveredSeededBound false L)
          (gaussianRecoveredSeededBound true L)).trans_lt
      hnew
  have h35 : ¬L ≤ gaussianSeededSwitch false 35000 := by
    linarith only [gaussianSeeded_switch_order.1, gaussianSeeded_switch_order.2, hS]
  have h50 : ¬L < gaussianSeededSwitch false 50000 := by
    linarith only [gaussianSeeded_switch_order.2, hS]
  rw [gaussianRecoveredSeeded_eq_min hL]
  simpa only [gaussianSeededSelected, ite_eq_right h35, ite_eq_right h50,
    ite_eq_right (not_le.mpr hS)] using hs

end PseudoPrime.Analysis
