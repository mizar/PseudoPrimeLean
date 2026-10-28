/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

public import PseudoPrime.Analysis.GaussianSeededSharp
public import PseudoPrime.Analysis.GaussianRecoveredSeededComparison
public import PseudoPrime.Analysis.GaussianMRClippedComparison
public import PseudoPrime.Analysis.GaussianBudgetRoots
public import PseudoPrime.Analysis.GaussianMRSeededComparison

/-! # Exact comparisons for seeded Gaussian profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The raw cutoff (6/5)t_D(L)^4 before inserting a prefix floor.
It supplies the varying pieces between the exact clipped-envelope switches. -/
noncomputable def gaussianSeededSharpRawBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * (gaussianSeededSharpRawRoot f L ^ 2) ^ 2

/-- The exact scale sigma_N(D) at which the raw cutoff reaches N.
Use the fixed floor radius and the quadratic root equation.
No rounded decimal appears in this boundary definition. -/
noncomputable def gaussianSeededSharpSwitch (f : Bool) (N : ℝ) : ℝ :=
  (gaussianMRRefinedD * Real.sqrt ((5 / 6) * N) -
      gaussianMRRefinedBeta * Real.sqrt (Real.sqrt ((5 / 6) * N)) -
      gaussianSeededSharpConstant f) /
    gaussianMRRefinedConductor

/-- For N>=35000, the fourth-root floor sqrt(sqrt(5N/6)) is at least thirteen.
Square twice using the rational lower bound on N. -/
theorem gaussianSeededSharp_floor_thirteen {N : ℝ} (hN : 35000 ≤ N) :
    (13 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6) * N)) := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * N := by linarith only [hN]
  have h4 : (13 : ℝ) ^ 4 ≤ (5 / 6) * N := by linarith only [hN]
  have h2 : (13 : ℝ) ^ 2 ≤ Real.sqrt ((5 / 6) * N) :=
    (Real.le_sqrt (by norm_num only) h0).mpr (by nlinarith only [h4])
  exact (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg _)).mpr h2

/-- For L>=0 and N>=35000, comparing the raw root with the N-floor is equivalent
to comparing L with sigma_N(D), in both directions. Factor the quadratic
difference and use its positive radius factor and conductor coefficient. -/
theorem gaussianSeededSharp_raw_root_compare {f : Bool} {L N : ℝ} (hL : 0 ≤ L) (hN : 35000 ≤ N) :
    (gaussianSeededSharpRawRoot f L ≤ Real.sqrt (Real.sqrt ((5 / 6) * N)) ↔
        L ≤ gaussianSeededSharpSwitch f N) ∧
      (Real.sqrt (Real.sqrt ((5 / 6) * N)) ≤ gaussianSeededSharpRawRoot f L ↔
        gaussianSeededSharpSwitch f N ≤ L) := by
  let y := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * N))
  let t := gaussianSeededSharpRawRoot f L
  have hy : (13 : ℝ) ≤ y := gaussianSeededSharp_floor_thirteen hN
  have ht : 0 < t := gaussianSeededSharp_raw_pos f L
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hb : gaussianMRRefinedBeta < 13 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have hdy := mul_le_mul_of_nonneg_left hy hd.le
  have hdt := mul_pos hd ht
  have hfac : 0 < gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta := by
    linarith only [hdy, hdt, hb]
  have he := gaussianSeededSharp_raw_equation f hL
  change
    gaussianMRRefinedD * t ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * t +
        gaussianSeededSharpConstant f at he
  have hsq : y ^ 2 = Real.sqrt ((5 / 6) * N) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hid :
    (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
      gaussianMRRefinedConductor * (gaussianSeededSharpSwitch f N - L) := by
    rw [gaussianSeededSharpSwitch]
    conv_rhs =>
      rw [mul_sub, mul_div_cancel₀ _ hc.ne', ← hsq,
        Real.sqrt_sq (by linarith only [hy] : (0 : ℝ) ≤ y)]
    change
      (y - t) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
        gaussianMRRefinedD * y ^ 2 - gaussianMRRefinedBeta * y - gaussianSeededSharpConstant f -
          gaussianMRRefinedConductor * L
    nlinarith only [he]
  have hneg :
    (t - y) * (gaussianMRRefinedD * (y + t) - gaussianMRRefinedBeta) =
      gaussianMRRefinedConductor * (L - gaussianSeededSharpSwitch f N) := by
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
theorem gaussianSeededSharp_raw_bound_compare {f : Bool} {L N : ℝ} (hL : 0 ≤ L) (hN : 35000 ≤ N) :
    (gaussianSeededSharpRawBound f L ≤ N ↔ L ≤ gaussianSeededSharpSwitch f N) ∧
      (N ≤ gaussianSeededSharpRawBound f L ↔ gaussianSeededSharpSwitch f N ≤ L) := by
  let y := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * N))
  have hy := (Real.sqrt_nonneg (Real.sqrt ((5 / 6 : ℝ) * N)))
  have ht := (gaussianSeededSharp_raw_pos f L).le
  have h0 : 0 ≤ (5 / 6 : ℝ) * N := by linarith only [hN]
  have hid : (6 / 5 : ℝ) * (y ^ 2) ^ 2 = N := by
    dsimp only [y]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h0]
    ring
  have hroot := gaussianSeededSharp_raw_root_compare (f := f) hL hN
  constructor
  · apply Iff.trans _ hroot.1
    constructor
    · intro hb
      have h4 : (gaussianSeededSharpRawRoot f L ^ 2) ^ 2 ≤ (y ^ 2) ^ 2 := by
        change (6 / 5 : ℝ) * (gaussianSeededSharpRawRoot f L ^ 2) ^ 2 ≤ N at hb
        linarith only [hb, hid]
      exact (sq_le_sq₀ ht hy).mp ((sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp h4)
    · intro hr
      have h2 := (sq_le_sq₀ ht hy).mpr hr
      have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
      change (6 / 5 : ℝ) * (gaussianSeededSharpRawRoot f L ^ 2) ^ 2 ≤ N
      linarith only [h4, hid]
  · apply Iff.trans _ hroot.2
    constructor
    · intro hb
      have h4 : (y ^ 2) ^ 2 ≤ (gaussianSeededSharpRawRoot f L ^ 2) ^ 2 := by
        change N ≤ (6 / 5 : ℝ) * (gaussianSeededSharpRawRoot f L ^ 2) ^ 2 at hb
        linarith only [hb, hid]
      exact (sq_le_sq₀ hy ht).mp ((sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp h4)
    · intro hr
      have h2 := (sq_le_sq₀ hy ht).mpr hr
      have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
      change N ≤ (6 / 5 : ℝ) * (gaussianSeededSharpRawRoot f L ^ 2) ^ 2
      linarith only [h4, hid]

/-- For L>=0, the raw 50000-profile root is strictly below the raw 35000-profile root.
The coefficients agree and the residual allowance 541/100 is below 563/100.
Strict square-root monotonicity gives the comparison. -/
theorem gaussianSeededSharp_raw_profiles_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianSeededSharpRawRoot true L < gaussianSeededSharpRawRoot false L := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hdisc :
    0 ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianSeededSharpConstant true) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc hL) (gaussianSeededSharp_constant_pos true).le))
  have hconst : gaussianSeededSharpConstant true < gaussianSeededSharpConstant false := by
    norm_num only [gaussianSeededSharpConstant, ite_true, ite_false, Bool.false_eq_true]
  have hmul := mul_lt_mul_of_pos_left hconst (mul_pos (by norm_num only : (0 : ℝ) < 4) hd)
  have hrad :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianSeededSharpConstant true) <
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianSeededSharpConstant false) := by
    linarith only [hmul]
  have hs := Real.sqrt_lt_sqrt hdisc hrad
  change
    (gaussianMRRefinedBeta + _) / (2 * gaussianMRRefinedD) <
      (gaussianMRRefinedBeta + _) / (2 * gaussianMRRefinedD)
  apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num only) hd)).mpr
  linarith only [hs]

/-- For L>=0, the raw 50000-profile cutoff is below the raw 35000-profile cutoff.
Square the positive root comparison twice and multiply by six fifths. -/
theorem gaussianSeededSharp_raw_bounds_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianSeededSharpRawBound true L < gaussianSeededSharpRawBound false L := by
  have h2 :=
    (sq_lt_sq₀ (gaussianSeededSharp_raw_pos true L).le (gaussianSeededSharp_raw_pos false L).le).mpr
      (gaussianSeededSharp_raw_profiles_lt hL)
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- The first switch sigma_35000(563/100) lies strictly between 240 and 243.
Rational square-root enclosures prove this interval, without sampled crossing values. -/
theorem gaussianSeededSharp_switch35_bounds :
    (240 : ℝ) < gaussianSeededSharpSwitch false 35000 ∧
      gaussianSeededSharpSwitch false 35000 < 243 := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hRlo : (8539 / 50 : ℝ) ≤ Real.sqrt ((5 / 6 : ℝ) * 35000) :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hRhi : Real.sqrt ((5 / 6 : ℝ) * 35000) ≤ (17079 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hSlo : (13 : ℝ) ≤ Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 35000)) :=
    gaussianSeededSharp_floor_thirteen (by norm_num only)
  have hShi : Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * 35000)) ≤ (131 / 10 : ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by norm_num only, ?_⟩
    exact Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  dsimp only [gaussianSeededSharpSwitch]
  constructor
  · apply (lt_div_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex, gaussianSeededSharpConstant, Bool.false_eq_true, ite_false,
      ite_true] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRlo, hShi]
  · apply (div_lt_iff₀ hc).mpr
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsIndex, gaussianSeededSharpConstant, Bool.false_eq_true, ite_false,
      ite_true] at hRlo hRhi hSlo hShi ⊢
    linarith only [hRhi, hSlo]

/-- Both switches at floor 50000 lie strictly between 293 and 295.
Rational enclosures for the radius and root, together with the two allowed
residual constants, certify the complete parameter cases. -/
theorem gaussianSeededSharp_switch50_bounds (f : Bool) :
    (293 : ℝ) < gaussianSeededSharpSwitch f 50000 ∧ gaussianSeededSharpSwitch f 50000 < 295 := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hDlo : (541 / 100 : ℝ) ≤ gaussianSeededSharpConstant f := by
    cases f <;> norm_num only [gaussianSeededSharpConstant, Bool.false_eq_true, ite_false, ite_true]
  have hDhi : gaussianSeededSharpConstant f ≤ (563 / 100 : ℝ) := by
    cases f <;> norm_num only [gaussianSeededSharpConstant, Bool.false_eq_true, ite_false, ite_true]
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
  dsimp only [gaussianSeededSharpSwitch]
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
theorem gaussianSeededSharp_switch_order :
    gaussianSeededSharpSwitch false 35000 < gaussianSeededSharpSwitch false 50000 ∧
      gaussianSeededSharpSwitch false 50000 < gaussianSeededSharpSwitch true 50000 := by
  constructor
  · linarith only [gaussianSeededSharp_switch35_bounds.2,
      (gaussianSeededSharp_switch50_bounds false).1]
  · dsimp only [gaussianSeededSharpSwitch]
    apply
      (div_lt_div_iff_of_pos_right
          (by norm_num only [gaussianMRRefinedConductor] : 0 < gaussianMRRefinedConductor)).mpr
    norm_num only [gaussianSeededSharpConstant, Bool.false_eq_true, ite_false, ite_true]
    linarith only

/-- At every certified nonnegative switching scale, the raw cutoff equals N.
Apply both directions of the cutoff comparison and antisymmetry.
This proves equality of the adjacent formulas at each boundary. -/
theorem gaussianSeededSharp_raw_at_switch {f : Bool} {N : ℝ} (hN : 35000 ≤ N)
    (hS : 0 ≤ gaussianSeededSharpSwitch f N) :
    gaussianSeededSharpRawBound f (gaussianSeededSharpSwitch f N) = N := by
  have h := gaussianSeededSharp_raw_bound_compare (f := f) hS hN
  exact le_antisymm (h.1.mpr le_rfl) (h.2.mpr le_rfl)

/-- The four explicit pieces of the clipped Gaussian envelope: 35000, raw35,50000,raw50.
The boundaries are sigma_35000(563/100),sigma_50000(563/100),sigma_50000(541/100). -/
noncomputable def gaussianSeededSharpSelected (L : ℝ) : ℝ :=
  if L ≤ gaussianSeededSharpSwitch false 35000 then 35000
  else
    if L < gaussianSeededSharpSwitch false 50000 then gaussianSeededSharpRawBound false L
    else
      if L ≤ gaussianSeededSharpSwitch true 50000 then 50000 else gaussianSeededSharpRawBound true L

/-- Each clipped profile is exactly the maximum of its prefix floor and raw cutoff.
This restates the clipping identity using the named raw bound. -/
theorem gaussianSeededSharp_eq_max (f : Bool) (L : ℝ) :
    gaussianSeededSharpBound f L =
      max (gaussianSeededSharpCutoff f : ℝ) (gaussianSeededSharpRawBound f L) :=
  gaussianSeededSharp_bound_eq_max f L

/-- For L>=63, the two-profile minimum equals the four-piece selected function.
Apply the exact cutoff comparisons and strict ordering of the raw profiles
in each interval. No unresolved minimum remains in the Gaussian interval table. -/
theorem gaussianSeededSharp_min_eq_selected {L : ℝ} (hL : 63 ≤ L) :
    min (gaussianSeededSharpBound false L) (gaussianSeededSharpBound true L) =
      gaussianSeededSharpSelected L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hprof := (gaussianSeededSharp_raw_bounds_lt h0).le
  rw [gaussianSeededSharp_eq_max false L, gaussianSeededSharp_eq_max true L]
  norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  by_cases h35 : L ≤ gaussianSeededSharpSwitch false 35000
  · have ha :=
      (gaussianSeededSharp_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 35000)).1.mpr
        h35
    have hb : gaussianSeededSharpRawBound true L ≤ (50000 : ℝ) := by linarith only [hprof, ha]
    simp only [gaussianSeededSharpSelected, ite_eq_left h35, max_eq_left ha, max_eq_left hb,
      min_eq_left (by norm_num only : (35000 : ℝ) ≤ 50000)]
  · have ha :=
      (gaussianSeededSharp_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 35000)).2.mpr
        (le_of_not_ge h35)
    by_cases h50 : L < gaussianSeededSharpSwitch false 50000
    · have hb :=
        (gaussianSeededSharp_raw_bound_compare (f := false) h0
              (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
          h50.le
      have hc : gaussianSeededSharpRawBound true L ≤ (50000 : ℝ) := hprof.trans hb
      simp only [gaussianSeededSharpSelected, ite_eq_right h35, ite_eq_left h50, max_eq_right ha,
        max_eq_left hc, min_eq_left hb]
    · have hb :=
        (gaussianSeededSharp_raw_bound_compare (f := false) h0
              (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
          (le_of_not_gt h50)
      by_cases hlast : L ≤ gaussianSeededSharpSwitch true 50000
      · have hc :=
          (gaussianSeededSharp_raw_bound_compare (f := true) h0
                (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
            hlast
        simp only [gaussianSeededSharpSelected, ite_eq_right h35, ite_eq_right h50,
          ite_eq_left hlast, max_eq_right ha, max_eq_left hc, min_eq_right hb]
      · have hc :=
          (gaussianSeededSharp_raw_bound_compare (f := true) h0
                (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
            (le_of_not_ge hlast)
        simp only [gaussianSeededSharpSelected, ite_eq_right h35, ite_eq_right h50,
          ite_eq_right hlast, max_eq_right ha, max_eq_right hc, min_eq_right hprof]

/-- The exact horizontal shift induced by decreasing each seeded residual
allowance by 3/100. Only numerical function comparisons use this shift. -/
noncomputable def gaussianSeededSharpShift : ℝ :=
  500000 / 6705207

/-- Both recovered constants differ from their baseline counterparts by 3/100.
This algebraic identity does not change the input of an actual witness theorem. -/
theorem gaussianSeededSharp_constant_shift (f : Bool) :
    gaussianSeededSharpConstant f = gaussianRecoveredSeededConstant f - 3 / 100 := by
  cases f <;>
    norm_num only [gaussianSeededSharpConstant, gaussianRecoveredSeededConstant, Bool.false_eq_true,
      ite_false, ite_true]

/-- Each recovered raw root equals the baseline raw root at L-delta.
Expand the common discriminant and compare its affine constant terms. -/
theorem gaussianSeededSharp_raw_shift (f : Bool) (L : ℝ) :
    gaussianSeededSharpRawRoot f L =
      gaussianRecoveredSeededRawRoot f (L - gaussianSeededSharpShift) := by
  have he :
    gaussianMRRefinedConductor * L + gaussianSeededSharpConstant f =
      gaussianMRRefinedConductor * (L - gaussianSeededSharpShift) +
        gaussianRecoveredSeededConstant f := by
    rw [gaussianSeededSharp_constant_shift]
    norm_num only [gaussianMRRefinedConductor, gaussianSeededSharpShift]
    ring
  rw [gaussianSeededSharpRawRoot, gaussianRecoveredSeededRawRoot, he]

/-- The clipped recovered root has the same exact horizontal shift.
The prefix floor is unchanged in both profiles. -/
theorem gaussianSeededSharp_root_shift (f : Bool) (L : ℝ) :
    gaussianSeededSharpRoot f L = gaussianRecoveredSeededRoot f (L - gaussianSeededSharpShift) := by
  rw [gaussianSeededSharpRoot, gaussianRecoveredSeededRoot, gaussianSeededSharp_raw_shift]
  rfl

/-- The full clipped bound inherits the exact shift, including its constant floor. -/
theorem gaussianSeededSharp_bound_shift (f : Bool) (L : ℝ) :
    gaussianSeededSharpBound f L =
      gaussianRecoveredSeededBound f (L - gaussianSeededSharpShift) := by
  simp only [gaussianSeededSharpBound, gaussianRecoveredSeededBound, gaussianSeededSharpRadius,
    gaussianRecoveredSeededRadius, gaussianSeededSharp_root_shift]

/-- The raw cutoff before clipping inherits the same exact shift. -/
theorem gaussianSeededSharp_rawBound_shift (f : Bool) (L : ℝ) :
    gaussianSeededSharpRawBound f L =
      gaussianRecoveredSeededRawBound f (L - gaussianSeededSharpShift) := by
  simp only [gaussianSeededSharpRawBound, gaussianRecoveredSeededRawBound,
    gaussianSeededSharp_raw_shift]

/-- Every exact floor crossing increases by delta under the recovered prefix.
No decimal approximation is used as a switching guard. -/
theorem gaussianSeededSharp_switch_shift (f : Bool) (N : ℝ) :
    gaussianSeededSharpSwitch f N =
      gaussianRecoveredSeededSwitch f N + gaussianSeededSharpShift := by
  rw [gaussianSeededSharpSwitch, gaussianRecoveredSeededSwitch, gaussianSeededSharp_constant_shift]
  norm_num only [gaussianMRRefinedConductor, gaussianSeededSharpShift]
  ring

/-- The recovered four-piece selected function is the horizontally shifted baseline
selected function at every real level, without a domain assumption. -/
theorem gaussianSeededSharp_selected_shift (L : ℝ) :
    gaussianSeededSharpSelected L =
      gaussianRecoveredSeededSelected (L - gaussianSeededSharpShift) := by
  simp only [gaussianSeededSharpSelected, gaussianRecoveredSeededSelected,
    gaussianSeededSharp_switch_shift, gaussianSeededSharp_rawBound_shift, sub_le_iff_le_add,
    sub_lt_iff_lt_add]

/-- At every real level each recovered raw root is no larger than its baseline
root. Apply global square-root monotonicity to the smaller residual constant. -/
theorem gaussianSeededSharp_raw_le_old (f : Bool) (L : ℝ) :
    gaussianSeededSharpRawRoot f L ≤ gaussianRecoveredSeededRawRoot f L := by
  have hconst : gaussianSeededSharpConstant f ≤ gaussianRecoveredSeededConstant f := by
    rw [gaussianSeededSharp_constant_shift]
    linarith only
  have hd := gaussianMRRefined_coefficients.1
  have hrad := mul_le_mul_of_nonneg_left hconst (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd.le)
  have hrad' :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianSeededSharpConstant f) ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) := by
    linarith only [hrad]
  have hroot := add_le_add_left (Real.sqrt_le_sqrt hrad') gaussianMRRefinedBeta
  exact
    div_le_div_of_nonneg_right (by linarith only [hroot])
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hd.le)

/-- Each recovered clipped cutoff preserves the baseline upper bound globally.
Use the unchanged floor, then square nonnegative roots twice. -/
theorem gaussianSeededSharp_le_old (f : Bool) (L : ℝ) :
    gaussianSeededSharpBound f L ≤ gaussianRecoveredSeededBound f L := by
  have hr : gaussianSeededSharpRoot f L ≤ gaussianRecoveredSeededRoot f L := by
    apply max_le_max
    · rfl
    · exact gaussianSeededSharp_raw_le_old f L
  have h2 :=
    (sq_le_sq₀ (gaussianSeededSharp_root_pos f L).le (gaussianRecoveredSeeded_root_pos f L).le).mpr
      hr
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- At nonnegative levels the raw recovered cutoff is strictly smaller than
its baseline counterpart. The discriminants differ by the positive residual decrease. -/
theorem gaussianSeededSharp_raw_lt_old (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianSeededSharpRawBound f L < gaussianRecoveredSeededRawBound f L := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hdisc :
    0 ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianSeededSharpConstant f) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc hL) (gaussianSeededSharp_constant_pos f).le))
  have hconst : gaussianSeededSharpConstant f < gaussianRecoveredSeededConstant f := by
    rw [gaussianSeededSharp_constant_shift]
    linarith only
  have hmul := mul_lt_mul_of_pos_left hconst (mul_pos (by norm_num only : (0 : ℝ) < 4) hd)
  have hdisc' :
    gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianSeededSharpConstant f) <
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) := by
    linarith only [hmul]
  have hs := add_lt_add_left (Real.sqrt_lt_sqrt hdisc hdisc') gaussianMRRefinedBeta
  have hr : gaussianSeededSharpRawRoot f L < gaussianRecoveredSeededRawRoot f L :=
    (div_lt_div_iff_of_pos_right (mul_pos (by norm_num only) hd)).mpr (by linarith only [hs])
  have h2 :=
    (sq_lt_sq₀ (gaussianSeededSharp_raw_pos f L).le (gaussianRecoveredSeeded_raw_pos f L).le).mpr hr
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- If the baseline profile has left its floor, the recovered full profile
strictly improves it. Both the unchanged floor and smaller raw curve lie below the old raw curve. -/
theorem gaussianSeededSharp_lt_old (f : Bool) {L : ℝ} (hL : 0 ≤ L)
    (hfloor : (gaussianRecoveredSeededCutoff f : ℝ) < gaussianRecoveredSeededRawBound f L) :
    gaussianSeededSharpBound f L < gaussianRecoveredSeededBound f L := by
  rw [gaussianSeededSharp_eq_max, gaussianRecoveredSeeded_eq_max]
  have hnew :
    max (gaussianSeededSharpCutoff f : ℝ) (gaussianSeededSharpRawBound f L) <
      gaussianRecoveredSeededRawBound f L :=
    max_lt hfloor (gaussianSeededSharp_raw_lt_old f hL)
  exact hnew.trans_le (le_max_right _ _)

/-- The recovered selected candidate used by the public witness envelope. -/
noncomputable def gaussianSeededSharp (L : ℝ) : ℝ :=
  gaussianSeededSharpSelected L

/-- On the certified half-line, the recovered selected function is exactly the
minimum of its two actual-prefix profiles, including the entrance strip [63,63+delta). -/
theorem gaussianSeededSharp_eq_min {L : ℝ} (hL : 63 ≤ L) :
    gaussianSeededSharp L =
      min (gaussianSeededSharpBound false L) (gaussianSeededSharpBound true L) := by
  exact (gaussianSeededSharp_min_eq_selected hL).symm

/-- On the certified half-line, the selected recovered envelope never exceeds
the baseline selected envelope. Both profile inequalities are pointwise and global. -/
theorem gaussianSeededSharp_le_seeded {L : ℝ} (hL : 63 ≤ L) :
    gaussianSeededSharp L ≤ gaussianRecoveredSeededSelected L := by
  rw [gaussianSeededSharp_eq_min hL, ← gaussianRecoveredSeeded_min_eq_selected hL]
  exact min_le_min (gaussianSeededSharp_le_old false L) (gaussianSeededSharp_le_old true L)

/-- The minimum of the two clipped profiles inherits the exact horizontal shift
at every real input, with no entrance-domain assumption. -/
theorem gaussianSeededSharp_min_shift (L : ℝ) :
    min (gaussianSeededSharpBound false L) (gaussianSeededSharpBound true L) =
      min (gaussianRecoveredSeededBound false (L - gaussianSeededSharpShift))
        (gaussianRecoveredSeededBound true (L - gaussianSeededSharpShift)) := by
  rw [gaussianSeededSharp_bound_shift, gaussianSeededSharp_bound_shift]

/-- A baseline profile lies strictly above its floor beyond the exact switch.
Use the reverse implication of the non-strict raw-bound comparison to rule out equality. -/
theorem gaussianRecoveredSeeded_raw_gt_floor (f : Bool) {L : ℝ} (hL : 0 ≤ L)
    (hS : gaussianRecoveredSeededSwitch f (gaussianRecoveredSeededCutoff f : ℝ) < L) :
    (gaussianRecoveredSeededCutoff f : ℝ) < gaussianRecoveredSeededRawBound f L := by
  have hN : (35000 : ℝ) ≤ (gaussianRecoveredSeededCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededCutoff, Bool.false_eq_true, ite_false, ite_true,
        Nat.cast_ofNat]
  by_contra h
  exact
    (not_le.mpr hS)
      ((gaussianRecoveredSeeded_raw_bound_compare (f := f) hL hN).1.mp (le_of_not_gt h))

/-- On the first varying baseline segment, the recovered selected envelope is
strictly smaller. Its false profile improves the baseline raw35 curve, even if
its own floor is still active immediately after the old switch. -/
theorem gaussianSeededSharp_strict_first {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianRecoveredSeededSwitch false 35000 < L)
    (hU : L < gaussianRecoveredSeededSwitch false 50000) :
    gaussianSeededSharp L < gaussianRecoveredSeededSelected L := by
  have hfloor := gaussianRecoveredSeeded_raw_gt_floor false (by linarith only [hL]) hS
  have hnew := gaussianSeededSharp_lt_old false (by linarith only [hL]) hfloor
  rw [gaussianRecoveredSeeded_eq_max false L, max_eq_right hfloor.le] at hnew
  have hs :=
    (min_le_left (gaussianSeededSharpBound false L) (gaussianSeededSharpBound true L)).trans_lt hnew
  rw [gaussianSeededSharp_eq_min hL]
  simpa only [gaussianRecoveredSeededSelected, ite_eq_right (not_le.mpr hS), ite_eq_left hU] using
    hs

/-- Beyond the final baseline switch, the recovered true profile strictly
improves its raw50 curve, hence so does the two-profile selected minimum. -/
theorem gaussianSeededSharp_strict_last {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianRecoveredSeededSwitch true 50000 < L) :
    gaussianSeededSharp L < gaussianRecoveredSeededSelected L := by
  have hfloor := gaussianRecoveredSeeded_raw_gt_floor true (by linarith only [hL]) hS
  have hnew := gaussianSeededSharp_lt_old true (by linarith only [hL]) hfloor
  rw [gaussianRecoveredSeeded_eq_max true L, max_eq_right hfloor.le] at hnew
  have hs :=
    (min_le_right (gaussianSeededSharpBound false L) (gaussianSeededSharpBound true L)).trans_lt
      hnew
  have h35 : ¬L ≤ gaussianRecoveredSeededSwitch false 35000 := by
    linarith only [gaussianRecoveredSeeded_switch_order.1, gaussianRecoveredSeeded_switch_order.2,
      hS]
  have h50 : ¬L < gaussianRecoveredSeededSwitch false 50000 := by
    linarith only [gaussianRecoveredSeeded_switch_order.2, hS]
  rw [gaussianSeededSharp_eq_min hL]
  simpa only [gaussianRecoveredSeededSelected, ite_eq_right h35, ite_eq_right h50,
    ite_eq_right (not_le.mpr hS)] using hs

/-- The first strict improvement band includes the initial part of the old 50000 plateau.
The new raw35 curve remains below 50000 until the exact shifted second switch. -/
theorem gaussianSeededSharp_strict_first_full {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianRecoveredSeededSwitch false 35000 < L)
    (hU : L < gaussianRecoveredSeededSwitch false 50000 + gaussianSeededSharpShift) :
    gaussianSeededSharp L < gaussianRecoveredSeeded L := by
  by_cases hOld : L < gaussianRecoveredSeededSwitch false 50000
  · exact gaussianSeededSharp_strict_first hL hS hOld
  · have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
    have hN : (35000 : ℝ) ≤ 50000 := by norm_num only
    have hNew : L < gaussianSeededSharpSwitch false 50000 := by
      rw [gaussianSeededSharp_switch_shift]
      exact hU
    have hraw : gaussianSeededSharpRawBound false L < (50000 : ℝ) := by
      by_contra hn
      exact
        (not_le.mpr hNew)
          ((gaussianSeededSharp_raw_bound_compare (f := false) h0 hN).2.mp (le_of_not_gt hn))
    have hnewBound : gaussianSeededSharpBound false L < (50000 : ℝ) := by
      rw [gaussianSeededSharp_eq_max]
      apply max_lt
      · norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, Nat.cast_ofNat]
      · exact hraw
    have holdRaw : (50000 : ℝ) ≤ gaussianRecoveredSeededRawBound false L :=
      (gaussianRecoveredSeeded_raw_bound_compare (f := false) h0 hN).2.mpr (le_of_not_gt hOld)
    have hold35 : (50000 : ℝ) ≤ gaussianRecoveredSeededBound false L := by
      rw [gaussianRecoveredSeeded_eq_max]
      exact holdRaw.trans (le_max_right _ _)
    have hold50 : (50000 : ℝ) ≤ gaussianRecoveredSeededBound true L := by
      simpa only [gaussianRecoveredSeededCutoff, ite_true, Nat.cast_ofNat] using
        gaussianRecoveredSeeded_cutoff_le true L
    rw [gaussianSeededSharp_eq_min hL, gaussianRecoveredSeeded_eq_min hL]
    exact ((min_le_left _ _).trans_lt hnewBound).trans_le (le_min hold35 hold50)

end PseudoPrime.Analysis
