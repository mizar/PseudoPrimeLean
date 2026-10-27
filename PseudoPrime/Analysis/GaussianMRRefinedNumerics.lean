/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMR6FifthsNumerics
public import PseudoPrime.Analysis.GaussianMRWidthNumerics
public import PseudoPrime.LLS.GaussianPrefixComparison

/-! # Refined constant-width Gaussian MR numerical budgets from scale 300 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The stronger rational cutoff mass extracted from the unchanged 128-node certificate.
It replaces the old 16/25 mass only in the separate refined witness bound. -/
noncomputable def gaussianMRRefinedMass : ℝ :=
  64167 / 100000

/-- The exact conductor coefficient from the Gaussian zero-mass estimate.
The refined comparison retains this value through primitive character averaging. -/
noncomputable def gaussianMRRefinedConductor : ℝ :=
  20115621 / 50000000

/-- The positive relative-width factor: h=(2/5)/s for root s.
This balances the main-term loss against the principal smoothing error. -/
noncomputable def gaussianMRRefinedWidth : ℝ :=
  2 / 5

/-- The leading radius coefficient after eliminating every index at least 10^9.
The existing endpoint and index constants are reused. This defines the refined quadratic budget. -/
noncomputable def gaussianMRRefinedD : ℝ :=
  (gaussianMR6FifthsIndex * gaussianMRRefinedMass - gaussianMR6FifthsEndpoint) /
    (gaussianMR6FifthsIndex - 1)

/-- The root coefficient for relative width h=(2/5)/s after index normalization.
Its two terms are the retained-mass loss and principal smoothing cost. -/
noncomputable def gaussianMRRefinedBeta : ℝ :=
  (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
    (gaussianMRRefinedWidth * gaussianMRRefinedMass + 1 / (10 * gaussianMRRefinedWidth))

/-- The positive root of d*s^2=c*L+beta*s+28/5 with the refined constants.
Input L is the conductor logarithmic scale. The witness theorem uses only L>=300. -/
noncomputable def gaussianMRRefinedRoot (L : ℝ) : ℝ :=
  (gaussianMRRefinedBeta + Real.sqrt (gaussianMRRefinedBeta ^ 2 +
    4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + 28 / 5))) /
    (2 * gaussianMRRefinedD)

/-- The squared refined root, which is the square root of the Mellin scale x.
This radius feeds the signed subgroup comparison and the final witness cutoff. -/
noncomputable def gaussianMRRefinedRadius (L : ℝ) : ℝ :=
  gaussianMRRefinedRoot L ^ 2

/-- The separate refined prime-witness bound: six fifths of the squared refined radius.
The original gaussianMR6Bound is unchanged. The new all-composite theorem starts at L>=300. -/
noncomputable def gaussianMRRefinedBound (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianMRRefinedRadius L ^ 2

/-- The refined quadratic and root coefficients are positive. Exact rational arithmetic
checks their definitions. Later square-root and comparison arguments use these signs. -/
theorem gaussianMRRefined_coefficients :
    0 < gaussianMRRefinedD ∧ 0 < gaussianMRRefinedBeta := by
  constructor <;>
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]

/-- The actual Gaussian transform retains mass above the refined rational target.
Transfer the original 128-node certificate through the Mellin cutoff identity.
No quadrature nodes or certified payload values are changed. -/
theorem gaussianMRRefined_mass :
    gaussianMRRefinedMass <
      ∫ u in (0 : ℝ)..(6 / 5),
        (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u := by
  rw [LLS.PaperStatements.gaussianGamma_cutoff_integral (by norm_num only), ←
    integral_gaussianGammaProfile_div_sqrt (by norm_num only)]
  exact gaussianGammaCutoffSixFifths_refined

/-- The refined root is positive at every real scale, since its beta term is positive.
This algebraic fact supplies sign conditions for the separate scale-300 witness proof. -/
theorem gaussianMRRefined_root_pos (L : ℝ) : 0 < gaussianMRRefinedRoot L := by
  have hd := gaussianMRRefined_coefficients.1
  have hb := gaussianMRRefined_coefficients.2
  exact div_pos (add_pos_of_pos_of_nonneg hb (Real.sqrt_nonneg _))
    (mul_pos (by norm_num only : (0 : ℝ) < 2) hd)

/-- At every nonnegative scale the refined radius satisfies d*r=c*L+beta*s+28/5.
Square the defining root identity with its nonnegative discriminant. This exact relation
is used before rounding the pole cost in the refined residual estimate. -/
theorem gaussianMRRefined_equation {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedD * gaussianMRRefinedRadius L =
      gaussianMRRefinedConductor * L +
        gaussianMRRefinedBeta * gaussianMRRefinedRoot L + 28 / 5 := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 < gaussianMRRefinedConductor := by
    norm_num only [gaussianMRRefinedConductor]
  let z := Real.sqrt (gaussianMRRefinedBeta ^ 2 +
    4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + 28 / 5))
  have ha : 0 ≤ gaussianMRRefinedBeta ^ 2 +
      4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + 28 / 5) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
      (add_nonneg (mul_nonneg hc.le hL) (by norm_num only)))
  have hz : z ^ 2 = gaussianMRRefinedBeta ^ 2 +
      4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + 28 / 5) := Real.sq_sqrt ha
  have hlin := div_mul_cancel₀ (gaussianMRRefinedBeta + z)
    (ne_of_gt (mul_pos (by norm_num only : (0 : ℝ) < 2) hd))
  change gaussianMRRefinedRoot L * (2 * gaussianMRRefinedD) = gaussianMRRefinedBeta + z at hlin
  have hsq := congrArg (fun u : ℝ ↦ u ^ 2) hlin
  dsimp only [gaussianMRRefinedRadius]
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta,
    gaussianMRRefinedConductor,
    gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsEndpoint] at hz hlin hsq ⊢
  nlinarith only [hz, hlin, hsq]

/-- For L>=300 the refined root is at least fourteen. Evaluate the quadratic at this
rational anchor and use the root equation. This controls the inverse-root error uniformly. -/
theorem gaussianMRRefined_root_lower {L : ℝ} (hL : 300 ≤ L) :
    (14 : ℝ) ≤ gaussianMRRefinedRoot L := by
  have hp := gaussianMRRefined_root_pos L
  have he := gaussianMRRefined_equation (by linarith only [hL] : 0 ≤ L)
  dsimp only [gaussianMRRefinedRadius] at he
  by_contra hn
  have ht := lt_of_not_ge hn
  have hs : gaussianMRRefinedRoot L ^ 2 ≤ (14 : ℝ) * gaussianMRRefinedRoot L := by
    nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr ht.le)]
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
    gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hs, ht, hL]

/-- For L>=300 the refined radius is at least 5L/8+20. Use the root anchor in its exact
budget equation. The result reaches the existing stronger 50000 prefix. -/
theorem gaussianMRRefined_radius_lower {L : ℝ} (hL : 300 ≤ L) :
    (5 / 8 : ℝ) * L + 20 ≤ gaussianMRRefinedRadius L := by
  have he := gaussianMRRefined_equation (by linarith only [hL] : 0 ≤ L)
  have hs := gaussianMRRefined_root_lower hL
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
    gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hs, hL]

/-- For L>=300 the refined witness cutoff exceeds 50000. The radius lower bound is
at least 415/2, whose squared cutoff exceeds 50000. This permits the existing prefix proof. -/
theorem gaussianMRRefined_prefix50000 {L : ℝ} (hL : 300 ≤ L) :
    (50000 : ℝ) < gaussianMRRefinedBound L := by
  have he := gaussianMRRefined_equation (by linarith only [hL] : 0 ≤ L)
  have hs := gaussianMRRefined_root_lower hL
  have hr : (415 / 2 : ℝ) ≤ gaussianMRRefinedRadius L := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsEndpoint] at he
    nlinarith only [he, hs, hL]
  dsimp only [gaussianMRRefinedBound]
  nlinarith only [hr, sq_nonneg (gaussianMRRefinedRadius L - 415 / 2)]
/-- For L>=300 the separate refined bound is strictly smaller than the unchanged old bound.
Compare their positive-root equations using the improved mass, conductor coefficient,
width and constant. The continuous half-line comparison does not use sampled values. -/
theorem gaussianMRRefined_lt_gaussianMR6 {L : ℝ} (hL : 300 ≤ L) :
    gaussianMRRefinedBound L < gaussianMR6Bound L := by
  let s := gaussianMRRefinedRoot L
  let t := gaussianMR6Root L
  have hs : 14 ≤ s := gaussianMRRefined_root_lower hL
  have ht : 14 ≤ t := gaussianMR6Root_lower_14 hL
  have he := gaussianMRRefined_equation (by linarith only [hL] : 0 ≤ L)
  have hf := gaussianMR6Radius_equation hL
  dsimp only [gaussianMRRefinedRadius] at he
  dsimp only [gaussianMR6Radius] at hf
  have hst : s < t := by
    by_contra hn
    have hts : t ≤ s := le_of_not_gt hn
    have hp := mul_nonneg (sub_nonneg.mpr hts)
      (by linarith only [hs, ht] : (0 : ℝ) ≤ s + t - 14)
    change gaussianMRRefinedD * s ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 28 / 5 at he
    change gaussianMR6FifthsD * t ^ 2 =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * t + 6 at hf
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsD, gaussianMR6FifthsBeta,
      gaussianMR6FifthsConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint] at he hf
    nlinarith only [he, hf, hp, hts, hL, hs, ht, sq_nonneg t]
  have hrad : gaussianMRRefinedRadius L < gaussianMR6Radius L := by
    change s ^ 2 < t ^ 2
    nlinarith only [hst, hs, ht, mul_pos (sub_pos.mpr hst)
      (by linarith only [hs, ht] : (0 : ℝ) < t + s)]
  have hpos : 0 ≤ gaussianMRRefinedRadius L := sq_nonneg _
  have hsq := (sq_lt_sq₀ hpos (hpos.trans hrad.le)).mpr hrad
  exact mul_lt_mul_of_pos_left hsq (by norm_num only : (0 : ℝ) < 6 / 5)

/-- The normalized radius coefficient in the index-four refined budget.
It is used in both the subgroup scalar comparison and the root-gap contradiction. -/
noncomputable def gaussianMRRefinedTripleD : ℝ :=
  (4 * gaussianMRRefinedMass - gaussianMR6FifthsEndpoint) / 3

/-- The root coefficient for index four and relative width (2/5)/s.
It combines the mass loss with the principal smoothing cost in the three-prime branch. -/
noncomputable def gaussianMRRefinedTripleBeta : ℝ :=
  (4 / 3 : ℝ) * (gaussianMRRefinedMass * gaussianMRRefinedWidth +
    1 / (10 * gaussianMRRefinedWidth))

/-- For r>=415/2, the left-contour and archimedean tails are at most 3/25 and 1/1000.
Use the existing real-power decay lemma and exact rational anchors.
These caps serve both branches. -/
theorem gaussianMRRefined_tail {r : ℝ} (hr : 415 / 2 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 3 / 25 ∧
      (512 / 27 : ℝ) / r ^ 2 ≤ 1 / 1000 := by
  have hp : 0 < r := by linarith only [hr]
  have hx : (19 / 10 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only
    nlinarith only [hr]
  have hdec := LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt
    (a := 19 / 10) (by norm_num only) hx
  rw [Real.sqrt_sq hp.le] at hdec
  have hl := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
  constructor
  · have hc : (473 / 10 : ℝ) / ((19 / 10 : ℝ) * r) ≤ 3 / 25 := by
      rw [div_le_iff₀ (mul_pos (by norm_num only) hp)]
      nlinarith only [hr]
    have he : (473 / 10 : ℝ) * (1 / ((19 / 10 : ℝ) * r)) =
        (473 / 10 : ℝ) / ((19 / 10 : ℝ) * r) := by ring
    exact (hl.trans_eq he).trans hc
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    nlinarith only [hr]

/-- For L>=300 and log q<=L, the signed 50000-prefix ambient error is at most 265219/50000.
Combine the refined radius anchor with the common tail caps.
The index-four branch uses this bound. -/
theorem gaussianMRRefined_ambient {q : ℕ} {L : ℝ} (hL : 300 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianPrefixError (484381 / 100000) q (gaussianMRRefinedRadius L ^ 2) ≤
      265219 / 50000 := by
  have hr := gaussianMRRefined_radius_lower hL
  have h207 : 415 / 2 ≤ gaussianMRRefinedRadius L := by nlinarith only [hr, hL]
  have hp : 0 < gaussianMRRefinedRadius L := by linarith only [h207]
  have ht := gaussianMRRefined_tail h207
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / gaussianMRRefinedRadius L) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith only [hr, hq, hL]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hp.le]
  linarith only [ht.1, ht.2, hP]

/-- For L>=300, the normalized residual of the refined root is strictly below 28/5.
Substitute its exact equation into the pole cost before rounding,
  and keep the beneficial signed term.
This provides the strict large-index margin with the original 50000-prefix mass. -/
theorem gaussianMRRefined_budget {L : ℝ} (hL : 300 ≤ L) :
    let r := gaussianMRRefinedRadius L
    let s := gaussianMRRefinedRoot L
    let g := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
    g * (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
      1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
      13 / (gaussianMR6FifthsIndex - 1) +
      LLS.PaperStatements.gaussianPrefixError (484381 / 100000) 1 (r ^ 2) +
      gaussianMR6FifthsEndpoint * ((7 / 6) * L / r) < 28 / 5 := by
  let r := gaussianMRRefinedRadius L
  let s := gaussianMRRefinedRoot L
  let g := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
  let e := gaussianMR6FifthsEndpoint
  let d := gaussianMRRefinedD
  let b := gaussianMRRefinedBeta
  let c := gaussianMRRefinedConductor
  let a := g * (21 * e / (10 * gaussianMRRefinedWidth)) - 7 * e * b / (6 * c)
  let v := g * (1839 * e / 1000) + e * (4 - 7 * (28 / 5) / (6 * c))
  have hs : 14 ≤ s := le_trans (by norm_num only) (gaussianMRRefined_root_lower hL)
  have hr : 415 / 2 ≤ r := by
    have h := gaussianMRRefined_radius_lower hL
    change (5 / 8 : ℝ) * L + 20 ≤ r at h
    nlinarith only [h, hL]
  have hs0 : 0 < s := by linarith only [hs]
  have hr0 : 0 < r := by linarith only [hr]
  have hroot : d * r = c * L + b * s + 28 / 5 := gaussianMRRefined_equation (by linarith only [hL])
  have heq : s ^ 2 = r := rfl
  have hid :
      g * (21 * e / (10 * gaussianMRRefinedWidth * s) + 1839 * e / (1000 * r)) +
        e * (((7 / 6) * L + 4) / r) =
      7 * e * d / (6 * c) + a / s + v / r := by
    dsimp only [a, v]
    have hc : c ≠ 0 := by norm_num only [c, gaussianMRRefinedConductor]
    have hk : gaussianMRRefinedWidth ≠ 0 := by norm_num only [gaussianMRRefinedWidth]
    have hLsolve : L = (d * r - b * s - 28 / 5) / c :=
      (eq_div_iff hc).mpr (by linarith only [hroot])
    rw [hLsolve, ← heq]
    field_simp (disch := first
      | exact hs0.ne'
      | exact hc
      | exact hk
      | norm_num only)
    ring
  have ha : 0 ≤ a := by
    norm_num only [a, g, e, b, c, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedWidth, gaussianMRRefinedConductor]
  have hv : v ≤ 0 := by
    norm_num only [v, g, e, c, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
      gaussianMRRefinedConductor]
  have ha' : a / s ≤ a / 14 := div_le_div_of_nonneg_left ha (by norm_num only) hs
  have hv' : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv hr0.le
  have ht := gaussianMRRefined_tail hr
  have hrat : (159169 / 50000 : ℝ) + 7 * e * d / (6 * c) + a / 14 +
      3 / 25 + 1 / 1000 + 13 / (gaussianMR6FifthsIndex - 1) < 28 / 5 := by
    norm_num only [a, g, e, b, c, d, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedWidth, gaussianMRRefinedConductor,
      gaussianMRRefinedD]
  change g * (21 * e / (10 * gaussianMRRefinedWidth * s) + 1839 * e / (1000 * r)) +
    13 / (gaussianMR6FifthsIndex - 1) +
    LLS.PaperStatements.gaussianPrefixError (484381 / 100000) 1 (r ^ 2) + e * ((7 / 6) * L /
      r) < 28 / 5
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hr0.le]
  norm_num only [Nat.cast_one, Real.log_one, mul_zero, zero_add]
  dsimp only [e, gaussianMR6FifthsEndpoint] at hid hrat ⊢
  simp only [div_eq_mul_inv] at hid ha' hv' ht hrat ⊢
  nlinarith only [hid, ha', hv', ht.1, ht.2, hrat]




/-- At L>=300 and every index m>=10^9, the full signed refined residual is below 28/5.
Bound the index ratio and principal constant, then use log q<=L in the coupled root budget.
The large-index MR witness proof uses this strict inequality. -/
theorem gaussianMRRefined_residual {q : ℕ} {L m : ℝ}
    (hL : 300 ≤ L) (hq : Real.log q ≤ L) (hm : gaussianMR6FifthsIndex ≤ m) :
    let r := gaussianMRRefinedRadius L
    let s := gaussianMRRefinedRoot L
    (m / (m - 1)) * (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
      1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
      13 / (m - 1) + LLS.PaperStatements.gaussianPrefixError (484381 /
        100000) q (r ^ 2) < 28 / 5 := by
  let r := gaussianMRRefinedRadius L
  let s := gaussianMRRefinedRoot L
  let g := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
  let T := 21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
    1839 * gaussianMR6FifthsEndpoint / (1000 * r)
  have hr : 0 < r := by
    have h := gaussianMRRefined_radius_lower hL
    change (5 / 8 : ℝ) * L + 20 ≤ r at h
    linarith only [h, hL]
  have hs : 0 < s := gaussianMRRefined_root_pos L
  have hm1 : 0 < m - 1 := by
    norm_num only [gaussianMR6FifthsIndex] at hm
    linarith only [hm]
  have hJ : 0 < gaussianMR6FifthsIndex - 1 := by
    norm_num only [gaussianMR6FifthsIndex]
  have hT : 0 ≤ T := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num only) (by norm_num only [gaussianMR6FifthsEndpoint]))
      (mul_nonneg (mul_nonneg (by norm_num only)
        (by norm_num only [gaussianMRRefinedWidth])) hs.le))
    (div_nonneg (mul_nonneg (by norm_num only) (by norm_num only [gaussianMR6FifthsEndpoint]))
      (mul_nonneg (by norm_num only) hr.le))
  have hmT := mul_le_mul_of_nonneg_right (gaussianMR6Fifths_index_coefficients hm).2.1 hT
  have h13 : (13 : ℝ) / (m - 1) ≤ 13 / (gaussianMR6FifthsIndex - 1) :=
    div_le_div_of_nonneg_left (by norm_num only) hJ (sub_le_sub_right hm 1)
  have hlog := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (by norm_num only : (0 : ℝ) ≤ (2129 / 2000) * (7 / 6)) (inv_nonneg.mpr hr.le))
  have hA : LLS.PaperStatements.gaussianPrefixError (484381 / 100000) q (r ^ 2) ≤
      LLS.PaperStatements.gaussianPrefixError (484381 / 100000) 1 (r ^ 2) +
        gaussianMR6FifthsEndpoint * ((7 / 6) * L / r) := by
    dsimp only [LLS.PaperStatements.gaussianPrefixError, gaussianMR6FifthsEndpoint]
    rw [Real.sqrt_sq hr.le]
    norm_num only [Nat.cast_one, Real.log_one, mul_zero, zero_add]
    simp only [div_eq_mul_inv]
    nlinarith only [hlog]
  have hb := gaussianMRRefined_budget hL
  change g * T + 13 / (gaussianMR6FifthsIndex - 1) +
    LLS.PaperStatements.gaussianPrefixError (484381 / 100000) 1 (r ^ 2) +
    gaussianMR6FifthsEndpoint * ((7 / 6) * L / r) < 28 / 5 at hb
  change (m / (m - 1)) * T + 13 / (m - 1) +
    LLS.PaperStatements.gaussianPrefixError (484381 / 100000) q (r ^ 2) < 28 / 5
  linarith only [hmT, h13, hA, hb]

/-- At L>=300, the refined index-four comparison contradicts the root equation.
Subtract two thirds of the exact equation and use the rational positive gap at radius 415/2.
This completes the numerical part of the three-prime branch. -/
theorem gaussianMRRefined_triple_error {q : ℕ} {L : ℝ}
    (hL : 300 ≤ L) (hq : Real.log q ≤ L) :
    (4 / 3 : ℝ) * (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth *
      gaussianMRRefinedRoot L) +
      1839 * gaussianMR6FifthsEndpoint / (1000 * gaussianMRRefinedRadius L)) +
      13 / 3 + LLS.PaperStatements.gaussianPrefixError (484381 / 100000) q
        (gaussianMRRefinedRadius L ^ 2) < 11 := by
  have hs : 14 ≤ gaussianMRRefinedRoot L := gaussianMRRefined_root_lower hL
  have hr : (415 / 2) ≤ gaussianMRRefinedRadius L := by
    have h := gaussianMRRefined_radius_lower hL
    nlinarith only [h, hL]
  have ht := div_le_div_of_nonneg_left
    (by norm_num only [gaussianMR6FifthsEndpoint] : 0 ≤ 21 * gaussianMR6FifthsEndpoint)
    (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) < 10 * gaussianMRRefinedWidth *
      14) (mul_le_mul_of_nonneg_left hs (by norm_num only [gaussianMRRefinedWidth]))
  have hu := div_le_div_of_nonneg_left
    (by norm_num only [gaussianMR6FifthsEndpoint] : 0 ≤ 1839 * gaussianMR6FifthsEndpoint)
    (by norm_num only : (0 : ℝ) < 1000 * (415 /
      2)) (mul_le_mul_of_nonneg_left hr (by norm_num only))
  have hA := gaussianMRRefined_ambient hL hq
  norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedWidth] at ht hu ⊢
  linarith only [ht, hu, hA]

/-- At L>=300 the index-four scalar comparison contradicts the refined root equation.
Subtract two thirds of that equation and retain the positive rational gap at radius (415 / 2).
This finishes the numerical part of the remaining three-prime branch. -/
theorem gaussianMRRefined_triple {L : ℝ} (hL : 300 ≤ L)
    (hcmp :
      gaussianMRRefinedTripleD * gaussianMRRefinedRadius L ≤
        (2 / 3 : ℝ) * gaussianMRRefinedConductor * L +
          gaussianMRRefinedTripleBeta * gaussianMRRefinedRoot L +
          11) :
    False := by
  let r := gaussianMRRefinedRadius L
  let s := gaussianMRRefinedRoot L
  have hrlo : (415 / 2) ≤ r := by
    dsimp only [r]
    have hrad := gaussianMRRefined_radius_lower hL
    nlinarith only [hrad, hL]
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussianMRRefined_root_pos L
  have hsSq : s ^ 2 = r := by dsimp only [s, r, gaussianMRRefinedRadius]
  have hs14 : 14 ≤ s := by nlinarith only [hsSq, hrlo, hspos]
  have hsle : s ≤ r / 14 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 14)).2
    nlinarith only [hsSq, hs14]
  have hroot := gaussianMRRefined_equation (by linarith only [hL] : 0 ≤ L)
  have hroot' :
    gaussianMRRefinedD * r = gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 28 /
      5 := by
    simpa only [r, s] using hroot
  have hindexCmp :
    (gaussianMRRefinedTripleD -
          (2 / 3 : ℝ) * gaussianMRRefinedD) *
        r ≤
      (gaussianMRRefinedTripleBeta - (2 / 3 : ℝ) * gaussianMRRefinedBeta) *
          s +
        109 / 15 := by
    change
      gaussianMRRefinedTripleD * r ≤
        (2 / 3 : ℝ) * gaussianMRRefinedConductor * L + gaussianMRRefinedTripleBeta * s + 11 at hcmp
    nlinarith only [hcmp, hroot']
  have hbetaDiff :
    0 <
      gaussianMRRefinedTripleBeta - (2 / 3 : ℝ) * gaussianMRRefinedBeta := by
    norm_num only [gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta,
      gaussianMRRefinedBeta, gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth]
  have hgap :
    (gaussianMRRefinedTripleD -
          (2 / 3 : ℝ) * gaussianMRRefinedD) -
        (gaussianMRRefinedTripleBeta - (2 / 3 : ℝ) * gaussianMRRefinedBeta) /
          14 >
      0 := by
    norm_num only [gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMR6FifthsIndex,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
        gaussianMRRefinedConductor]
  have hmargin :
    (109 / 15 : ℝ) <
      (gaussianMRRefinedTripleD -
            (2 / 3 : ℝ) * gaussianMRRefinedD) *
          ((415 / 2)) -
        (gaussianMRRefinedTripleBeta - (2 / 3 : ℝ) * gaussianMRRefinedBeta) *
          ((415 / 28)) := by
    norm_num only [gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMR6FifthsIndex,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint,
        gaussianMRRefinedConductor]
  have hstrict :
    (109 / 15 : ℝ) <
      (gaussianMRRefinedTripleD -
            (2 / 3 : ℝ) * gaussianMRRefinedD) *
          r -
        (gaussianMRRefinedTripleBeta - (2 / 3 : ℝ) * gaussianMRRefinedBeta) *
          s := by
    have hscaled := mul_le_mul_of_nonneg_left hsle hbetaDiff.le
    have hlow := mul_le_mul_of_nonneg_left hrlo (le_of_lt hgap)
    nlinarith only [hscaled, hlow, hmargin]
  apply (not_le_of_gt hstrict)
  nlinarith only [hindexCmp]




/-- For every index m>=10^9, bound the normalized refined mass coefficient, index ratio
and root coefficient by their endpoint values. Exact rational signs justify cross-multiplication.
These are the coefficient inputs to variable-width scalar normalization. -/
theorem gaussianMRRefined_index_coeffs {m : ℝ} (hm : gaussianMR6FifthsIndex ≤ m) :
    gaussianMRRefinedD ≤ (m * gaussianMRRefinedMass - gaussianMR6FifthsEndpoint) / (m - 1) ∧
      m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1) ∧
      (m / (m - 1)) * (gaussianMRRefinedWidth * gaussianMRRefinedMass + 1 / (10 *
        gaussianMRRefinedWidth)) ≤ gaussianMRRefinedBeta := by
  have hK : (1 : ℝ) < gaussianMR6FifthsIndex := by norm_num only [gaussianMR6FifthsIndex]
  have hden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMR6FifthsIndex - 1 := by linarith only [hK]
  have hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1) := by
    rw [div_le_div_iff₀ hden hKden]
    norm_num only [gaussianMR6FifthsIndex] at hm ⊢
    nlinarith only [hm]
  have hbase : 0 ≤ gaussianMRRefinedWidth * gaussianMRRefinedMass + 1 / (10 *
    gaussianMRRefinedWidth) := by norm_num only [gaussianMRRefinedMass, gaussianMRRefinedWidth]
  refine ⟨?_, hgamma, ?_⟩
  · dsimp only [gaussianMRRefinedD]
    rw [div_le_div_iff₀ hKden hden]
    norm_num only [gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMR6FifthsEndpoint] at hm ⊢
    nlinarith only [hm]
  · dsimp only [gaussianMRRefinedBeta]
    calc
      _ ≤
          (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
            (gaussianMRRefinedWidth * gaussianMRRefinedMass + 1 / (10 * gaussianMRRefinedWidth)) :=
        mul_le_mul_of_nonneg_right hgamma hbase
      _ = gaussianMRRefinedBeta := by rfl


/-- At L>=300, the refined witness bound exceeds the ordinary 0.3 L^2 cutoff.
Square the positive linear radius lower bound and compare rational coefficients.
This places the usual finite-index witnesses below the refined cutoff. -/
theorem gaussianMRRefined_local {L : ℝ} (hL : 300 ≤ L) :
    (3 / 10 : ℝ) * L ^ 2 < gaussianMRRefinedBound L := by
  have hr := gaussianMRRefined_radius_lower hL
  have hLpos : 0 < L := by linarith only [hL]
  have hbase : (5 / 8 : ℝ) * L < gaussianMRRefinedRadius L := by linarith only [hr]
  have hrad : ((5 / 8 : ℝ) * L) ^ 2 < gaussianMRRefinedRadius L ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (by norm_num only) hLpos.le)
          (le_trans (mul_nonneg (by norm_num only) hLpos.le) hbase.le)).2
      hbase
  have hscaled := mul_lt_mul_of_pos_left hrad (by norm_num only : (0 : ℝ) < 6 / 5)
  have hcoeff : (3 / 10 : ℝ) < (6 / 5) * (5 / 8) ^ 2 := by norm_num only
  have hcoeffL := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hLpos)
  dsimp only [gaussianMRRefinedBound] at hscaled ⊢
  nlinarith only [hscaled, hcoeffL]


end PseudoPrime.Analysis
