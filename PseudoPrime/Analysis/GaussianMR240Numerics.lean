/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMR6FifthsNumerics
public import PseudoPrime.LLS.GaussianPrefixComparison

/-! # Constant-six Gaussian MR estimates from logarithmic scale 240 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The fixed constant-six root is positive for every real scale. Its numerator has a positive
beta term and a nonnegative square root. This avoids a circular start-point assumption. -/
theorem gaussianMR6_root_pos (L : ℝ) : 0 < gaussianMR6Root L := by
  have hd := gaussianMR6Fifths_coefficients_pos.1
  have hb := gaussianMR6Fifths_coefficients_pos.2
  exact
    div_pos (add_pos_of_pos_of_nonneg hb (Real.sqrt_nonneg _))
      (mul_pos (by norm_num only : (0 : ℝ) < 2) hd)

/-- At every nonnegative scale, the unchanged constant-six radius satisfies its budget equation.
Square the defining root identity and use the nonnegative discriminant. Later estimates use
this equation at scale 240 without extending the old 300-only comparison lemmas. -/
theorem gaussianMR6_equation {L : ℝ} (hL : 0 ≤ L) :
    gaussianMR6FifthsD * gaussianMR6Radius L =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR6Root L + 6 := by
  have hd := gaussianMR6Fifths_coefficients_pos.1
  have hc : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  let z :=
    Real.sqrt
      (gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6))
  have ha :
    0 ≤ gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc.le hL) (by norm_num only)))
  have hz :
    z ^ 2 =
      gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) :=
    Real.sq_sqrt ha
  have hlin :=
    div_mul_cancel₀ (gaussianMR6FifthsBeta + z)
      (ne_of_gt (mul_pos (by norm_num only : (0 : ℝ) < 2) hd))
  change gaussianMR6Root L * (2 * gaussianMR6FifthsD) = gaussianMR6FifthsBeta + z at hlin
  have hsq := congrArg (fun u : ℝ ↦ u ^ 2) hlin
  dsimp only [gaussianMR6Radius]
  norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
    gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at hz hlin hsq ⊢
  nlinarith only [hz, hlin, hsq]

/-- At scales L>=240, the root is at least 653/50. Compare its quadratic equation with the
rational anchor, using positivity rather than numerical approximation. This sharp bound
certifies that the witness cutoff reaches the new prefix. -/
theorem gaussianMR6_root_lower {L : ℝ} (hL : 240 ≤ L) : (653 / 50 : ℝ) ≤ gaussianMR6Root L := by
  have hp := gaussianMR6_root_pos L
  have he := gaussianMR6_equation (by linarith only [hL] : 0 ≤ L)
  dsimp only [gaussianMR6Radius] at he
  by_contra hn
  have ht := lt_of_not_ge hn
  have hs : gaussianMR6Root L ^ 2 ≤ (653 / 50 : ℝ) * gaussianMR6Root L := by
    nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr ht.le)]
  norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
    gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hs, ht, hL]

/-- At L>=240, the radius exceeds 5L/8+20. Combine the exact root equation with the
certified rational root anchor. This supplies a uniform positive radius for error estimates. -/
theorem gaussianMR6_radius_lower240 {L : ℝ} (hL : 240 ≤ L) :
    (5 / 8 : ℝ) * L + 20 ≤ gaussianMR6Radius L := by
  have he := gaussianMR6_equation (by linarith only [hL] : 0 ≤ L)
  have hs := gaussianMR6_root_lower hL
  norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
    gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hs, hL]

/-- At L>=240, the unchanged witness cutoff exceeds 35000. The exact root equation first
gives radius>=34157/200; squaring this positive anchor reaches the prefix.
This connects the numerical radius to the analytic checkpoint. -/
theorem gaussianMR6_prefix35000 {L : ℝ} (hL : 240 ≤ L) : (35000 : ℝ) < gaussianMR6Bound L := by
  have he := gaussianMR6_equation (by linarith only [hL] : 0 ≤ L)
  have hs := gaussianMR6_root_lower hL
  have hr : (34157 / 200 : ℝ) ≤ gaussianMR6Radius L := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
      gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at he
    nlinarith only [he, hs, hL]
  dsimp only [gaussianMR6Bound]
  nlinarith only [hr, sq_nonneg (gaussianMR6Radius L - 34157 / 200)]

/-- For radius r>=170, the left-contour and archimedean remainders are at most 147/1000
and 1/1000. The rational nineteenth-tenths anchor controls the real power. These estimates
are shared by the large-index and index-four budgets. -/
theorem gaussianMR6_tail240 {r : ℝ} (hr : 170 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 147 / 1000 ∧ (512 / 27 : ℝ) / r ^ 2 ≤ 1 / 1000 := by
  have hp : 0 < r := by linarith only [hr]
  have hx : (19 / 10 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only
    nlinarith only [hr]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 19 / 10) (by norm_num only)
      hx
  rw [Real.sqrt_sq hp.le] at hdec
  have hl := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
  constructor
  · have hc : (473 / 10 : ℝ) / ((19 / 10 : ℝ) * r) ≤ 147 / 1000 := by
      rw [div_le_iff₀ (mul_pos (by norm_num only) hp)]
      nlinarith only [hr]
    have he :
      (473 / 10 : ℝ) * (1 / ((19 / 10 : ℝ) * r)) = (473 / 10 : ℝ) / ((19 / 10 : ℝ) * r) := by ring
    exact (hl.trans_eq he).trans hc
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    nlinarith only [hr]

/-- At logarithmic scales L>=240 and log q<=L, the signed 35000-prefix ambient error
is at most 5619/1000. Bound its pole term by two and use the common tail estimates.
This coarser budget suffices for the three-prime branch. -/
theorem gaussianMR6_ambient240 {q : ℕ} {L : ℝ} (hL : 240 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianPrefixError (47 / 10) q (gaussianMR6Radius L ^ 2) ≤
      5619 / 1000 := by
  have hr := gaussianMR6_radius_lower240 hL
  have h170 : 170 ≤ gaussianMR6Radius L := by nlinarith only [hr, hL]
  have hp : 0 < gaussianMR6Radius L := by linarith only [h170]
  have ht := gaussianMR6_tail240 h170
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / gaussianMR6Radius L) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith only [hr, hq, hL]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hp.le]
  linarith only [ht.1, ht.2, hP]

/-- For L>=240, the normalized large-index residual at the unchanged root is below six.
Substitute the root equation into the pole term before rounding, keep the positive inverse-root
term and discard only the nonpositive inverse-radius term. This retains the strict MR margin. -/
theorem gaussianMR6_budget240 {L : ℝ} (hL : 240 ≤ L) :
    let r := gaussianMR6Radius L
    let s := gaussianMR6Root L
    let g := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
    g *
          (63 * gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (gaussianMR6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError (47 / 10) 1 (r ^ 2) +
        gaussianMR6FifthsEndpoint * ((7 / 6) * L / r) <
      6 := by
  let r := gaussianMR6Radius L
  let s := gaussianMR6Root L
  let g := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
  let e := gaussianMR6FifthsEndpoint
  let d := gaussianMR6FifthsD
  let b := gaussianMR6FifthsBeta
  let c := gaussianMR6FifthsConductor
  let a := g * (63 * e / 10) - 7 * e * b / (6 * c)
  let v := g * (1839 * e / 1000) + e * (4 - 7 / c)
  have hs : 13 ≤ s := le_trans (by norm_num only) (gaussianMR6_root_lower hL)
  have hr : 170 ≤ r := by
    have h := gaussianMR6_radius_lower240 hL
    change (5 / 8 : ℝ) * L + 20 ≤ r at h
    nlinarith only [h, hL]
  have hs0 : 0 < s := by linarith only [hs]
  have hr0 : 0 < r := by linarith only [hr]
  have hroot : d * r = c * L + b * s + 6 := gaussianMR6_equation (by linarith only [hL])
  have heq : s ^ 2 = r := rfl
  have hid :
    g * (63 * e / (10 * s) + 1839 * e / (1000 * r)) + e * (((7 / 6) * L + 4) / r) =
      7 * e * d / (6 * c) + a / s + v / r := by
    dsimp only [a, v]
    have hc : c ≠ 0 := by norm_num only [c, gaussianMR6FifthsConductor]
    field_simp (disch :=
      first
      | exact hs0.ne'
      | exact hr0.ne'
      | exact hc
      | norm_num only)
    linear_combination -70000 * e * s * hroot - 70000 * e * b * heq
  have ha : 0 ≤ a := by
    norm_num only [a, g, e, b, c, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsBeta, gaussianMR6FifthsMass, gaussianMR6FifthsConductor]
  have hv : v ≤ 0 := by
    norm_num only [v, g, e, c, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsConductor]
  have ha' : a / s ≤ a / 13 := div_le_div_of_nonneg_left ha (by norm_num only) hs
  have hv' : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv hr0.le
  have ht := gaussianMR6_tail240 hr
  have hrat :
    (3471 / 1000 : ℝ) + 7 * e * d / (6 * c) + a / 13 + 147 / 1000 + 1 / 1000 +
        13 / (gaussianMR6FifthsIndex - 1) <
      6 := by
    norm_num only [a, g, e, b, c, d, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
      gaussianMR6FifthsBeta, gaussianMR6FifthsMass, gaussianMR6FifthsConductor, gaussianMR6FifthsD]
  change
    g * (63 * e / (10 * s) + 1839 * e / (1000 * r)) + 13 / (gaussianMR6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError (47 / 10) 1 (r ^ 2) +
        e * ((7 / 6) * L / r) <
      6
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hr0.le]
  norm_num only [Nat.cast_one, Real.log_one, mul_zero, zero_add]
  dsimp only [e, gaussianMR6FifthsEndpoint] at hid hrat ⊢
  simp only [div_eq_mul_inv] at hid ha' hv' ht hrat ⊢
  nlinarith only [hid, ha', hv', ht.1, ht.2, hrat]

/-- At L>=240 and every index m>=10^9, the full signed residual is below six.
Bound the index ratio and principal constant, then substitute log q<=L in the coupled budget.
This is the strict inequality needed by the large-index MR contradiction. -/
theorem gaussianMR6_residual240 {q : ℕ} {L m : ℝ} (hL : 240 ≤ L) (hq : Real.log q ≤ L)
    (hm : gaussianMR6FifthsIndex ≤ m) :
    let r := gaussianMR6Radius L
    let s := gaussianMR6Root L
    (m / (m - 1)) *
          (63 * gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (47 / 10) q (r ^ 2) <
      6 := by
  let r := gaussianMR6Radius L
  let s := gaussianMR6Root L
  let g := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
  let T := 63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r)
  have hr : 0 < r := by
    have h := gaussianMR6_radius_lower240 hL
    change (5 / 8 : ℝ) * L + 20 ≤ r at h
    linarith only [h, hL]
  have hs : 0 < s := gaussianMR6_root_pos L
  have hm1 : 0 < m - 1 := by
    norm_num only [gaussianMR6FifthsIndex] at hm
    linarith only [hm]
  have hJ : 0 < gaussianMR6FifthsIndex - 1 := by norm_num only [gaussianMR6FifthsIndex]
  have hT : 0 ≤ T :=
    add_nonneg
      (div_nonneg (mul_nonneg (by norm_num only) (by norm_num only [gaussianMR6FifthsEndpoint]))
        (mul_nonneg (by norm_num only) hs.le))
      (div_nonneg (mul_nonneg (by norm_num only) (by norm_num only [gaussianMR6FifthsEndpoint]))
        (mul_nonneg (by norm_num only) hr.le))
  have hmT := mul_le_mul_of_nonneg_right (gaussianMR6Fifths_index_coefficients hm).2.1 hT
  have h13 : (13 : ℝ) / (m - 1) ≤ 13 / (gaussianMR6FifthsIndex - 1) :=
    div_le_div_of_nonneg_left (by norm_num only) hJ (sub_le_sub_right hm 1)
  have hlog :=
    mul_le_mul_of_nonneg_left hq
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ (2129 / 2000) * (7 / 6)) (inv_nonneg.mpr hr.le))
  have hA :
    LLS.PaperStatements.gaussianPrefixError (47 / 10) q (r ^ 2) ≤
      LLS.PaperStatements.gaussianPrefixError (47 / 10) 1 (r ^ 2) +
        gaussianMR6FifthsEndpoint * ((7 / 6) * L / r) := by
    dsimp only [LLS.PaperStatements.gaussianPrefixError, gaussianMR6FifthsEndpoint]
    rw [Real.sqrt_sq hr.le]
    norm_num only [Nat.cast_one, Real.log_one, mul_zero, zero_add]
    simp only [div_eq_mul_inv]
    nlinarith only [hlog]
  have hb := gaussianMR6_budget240 hL
  change
    g * T + 13 / (gaussianMR6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError (47 / 10) 1 (r ^ 2) +
        gaussianMR6FifthsEndpoint * ((7 / 6) * L / r) <
      6 at hb
  change
    (m / (m - 1)) * T + 13 / (m - 1) + LLS.PaperStatements.gaussianPrefixError (47 / 10) q (r ^ 2) <
      6
  linarith only [hmT, h13, hA, hb]

/-- At L>=240, the normalized index-four residual is below eleven.
Use the root and radius anchors with the uniform ambient cap. This supplies the
three-prime Korselt comparison without importing large-index hypotheses. -/
theorem gaussianMR6_triple_error240 {q : ℕ} {L : ℝ} (hL : 240 ≤ L) (hq : Real.log q ≤ L) :
    (4 / 3 : ℝ) *
          (63 * gaussianMR6FifthsEndpoint / (10 * gaussianMR6Root L) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * gaussianMR6Radius L)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (47 / 10) q (gaussianMR6Radius L ^ 2) <
      11 := by
  have hs : 13 ≤ gaussianMR6Root L := le_trans (by norm_num only) (gaussianMR6_root_lower hL)
  have hr : 170 ≤ gaussianMR6Radius L := by
    have h := gaussianMR6_radius_lower240 hL
    nlinarith only [h, hL]
  have ht :=
    div_le_div_of_nonneg_left
      (by norm_num only [gaussianMR6FifthsEndpoint] : 0 ≤ 63 * gaussianMR6FifthsEndpoint)
      (by norm_num only : (0 : ℝ) < 10 * 13) (mul_le_mul_of_nonneg_left hs (by norm_num only))
  have hu :=
    div_le_div_of_nonneg_left
      (by norm_num only [gaussianMR6FifthsEndpoint] : 0 ≤ 1839 * gaussianMR6FifthsEndpoint)
      (by norm_num only : (0 : ℝ) < 1000 * 170) (mul_le_mul_of_nonneg_left hr (by norm_num only))
  have hA := gaussianMR6_ambient240 hL hq
  norm_num only [gaussianMR6FifthsEndpoint] at ht hu ⊢
  linarith only [ht, hu, hA]

/-- At L>=240 the index-four scalar comparison contradicts the unchanged root equation.
Subtract two thirds of that equation and retain the positive rational gap at radius 170.
This finishes the numerical part of the remaining three-prime branch. -/
theorem gaussianMR6_triple240 {L : ℝ} (hL : 240 ≤ L)
    (hcmp :
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * gaussianMR6Radius L ≤
        (161 / 600 : ℝ) * L +
          (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * gaussianMR6Root L +
          11) :
    False := by
  let r := gaussianMR6Radius L
  let s := gaussianMR6Root L
  have hrlo : 170 ≤ r := by
    dsimp only [r]
    have hrad := gaussianMR6_radius_lower240 hL
    nlinarith only [hrad, hL]
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussianMR6_root_pos L
  have hsSq : s ^ 2 = r := by dsimp only [s, r, gaussianMR6Radius]
  have hs13 : 13 ≤ s := by nlinarith only [hsSq, hrlo, hspos]
  have hsle : s ≤ r / 13 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 13)).2
    nlinarith only [hsSq, hs13]
  have hroot := gaussianMR6_equation (by linarith only [hL] : 0 ≤ L)
  have hroot' :
    gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 6 := by
    simpa only [r, s] using hroot
  have hindexCmp :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) *
        r ≤
      ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s +
        7 := by
    change
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * r ≤
        (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * s + 11 at hcmp
    have hc : gaussianMR6FifthsConductor = 161 / 400 := by
      norm_num only [gaussianMR6FifthsConductor]
    rw [hc] at hroot'
    nlinarith only [hcmp, hroot']
  have hbetaDiff :
    0 <
      (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hgap :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) /
          13 >
      0 := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hmargin :
    (7 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          (170) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          ((170 / 13)) := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hstrict :
    (7 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          r -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s := by
    have hscaled := mul_le_mul_of_nonneg_left hsle hbetaDiff.le
    have hlow := mul_le_mul_of_nonneg_left hrlo (le_of_lt hgap)
    nlinarith only [hscaled, hlow, hmargin]
  apply (not_le_of_gt hstrict)
  nlinarith only [hindexCmp]

/-- At L>=240, the unchanged Gaussian bound dominates the ordinary 0.3 L^2 witness.
Square the positive linear radius lower bound and compare rational coefficients.
This connects the usual finite-index branch to the common witness cutoff. -/
theorem gaussianMR6_local240 {L : ℝ} (hL : 240 ≤ L) :
    (3 / 10 : ℝ) * L ^ 2 < gaussianMR6Bound L := by
  have hr := gaussianMR6_radius_lower240 hL
  have hLpos : 0 < L := by linarith only [hL]
  have hbase : (5 / 8 : ℝ) * L < gaussianMR6Radius L := by linarith only [hr]
  have hrad : ((5 / 8 : ℝ) * L) ^ 2 < gaussianMR6Radius L ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (by norm_num only) hLpos.le)
          (le_trans (mul_nonneg (by norm_num only) hLpos.le) hbase.le)).2
      hbase
  have hscaled := mul_lt_mul_of_pos_left hrad (by norm_num only : (0 : ℝ) < 6 / 5)
  have hcoeff : (3 / 10 : ℝ) < (6 / 5) * (5 / 8) ^ 2 := by norm_num only
  have hcoeffL := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hLpos)
  dsimp only [gaussianMR6Bound] at hscaled ⊢
  nlinarith only [hscaled, hcoeffL]

end PseudoPrime.Analysis
