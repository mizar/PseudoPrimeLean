/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianBudgetRoots

/-! # Two-root Gaussian budgets with the sharp 1000 prefix -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The index-four quadratic coefficient (4M-E)/3. It retains the conductor
saving and the certified Gaussian mass in the second root budget. -/
noncomputable def gaussian1000FourD : ℝ :=
  (4 * gaussianMRRefinedMass - gaussianMR6FifthsEndpoint) / 3

/-- The index-four square-root coefficient (4/3)(Mk+1/(10k)). It uses the
same relative width as the large-index root and the exact index-four normalization. -/
noncomputable def gaussian1000FourBeta : ℝ :=
  (4 / 3 : ℝ) * (gaussianMRRefinedMass * gaussianMRRefinedWidth + 1 / (10 * gaussianMRRefinedWidth))

/-- The positive large-index budget root with residual allowance 163/20.
For L>=0 its square satisfies the unmodified quadratic equation. The final
radius is increased to cover this root, the index-four root and the floor ten. -/
noncomputable def gaussian1000LargeRoot (L : ℝ) : ℝ :=
  gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
    (gaussianMRRefinedConductor * L + 163 / 20)

/-- The positive index-four budget root with conductor coefficient 2c/3
and residual allowance 127/10. It supplies the independent index-four constraint. -/
noncomputable def gaussian1000FourRoot (L : ℝ) : ℝ :=
  gaussianBudgetRoot gaussian1000FourD gaussian1000FourBeta
    ((2 / 3 : ℝ) * gaussianMRRefinedConductor * L + 127 / 10)

/-- The maximum of ten and both Gaussian budget roots. The floor ensures
the prefix and tail domains, while the two roots cover large index and index four. -/
noncomputable def gaussian1000Root (L : ℝ) : ℝ :=
  max 10 (max (gaussian1000LargeRoot L) (gaussian1000FourRoot L))

/-- The square of the combined root. Its square is the Mellin scale x;
this radius satisfies both budget inequalities after taking the maximum. -/
noncomputable def gaussian1000Radius (L : ℝ) : ℝ :=
  gaussian1000Root L ^ 2

/-- The witness cutoff (6/5)r squared for the combined 1000-prefix radius.
It is at least 12000 and will bound an actual rejecting prime for log n>=63. -/
noncomputable def gaussian1000Bound (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussian1000Radius L ^ 2

/-- Both index-four coefficients are positive by exact rational evaluation.
Their positivity supports the root equation and all later comparisons. -/
theorem gaussian1000_coefficients : 0 < gaussian1000FourD ∧ 0 < gaussian1000FourBeta := by
  norm_num only [gaussian1000FourD, gaussian1000FourBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, and_self]

/-- The large-index root is positive at every real L. Apply the generic
positive-root lemma with the certified refined coefficients. -/
theorem gaussian1000_large_pos (L : ℝ) : 0 < gaussian1000LargeRoot L :=
  gaussianBudgetRoot_pos gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2

/-- The index-four root is positive at every real L. Apply the generic
positive-root lemma with the exact index-four coefficients. -/
theorem gaussian1000_four_pos (L : ℝ) : 0 < gaussian1000FourRoot L :=
  gaussianBudgetRoot_pos gaussian1000_coefficients.1 gaussian1000_coefficients.2

/-- The combined root is at least ten for every L, by its maximum floor.
This is the anchor for the paired inverse-power residual bound. -/
theorem gaussian1000_root_ten (L : ℝ) : (10 : ℝ) ≤ gaussian1000Root L :=
  le_max_left _ _

/-- The combined root is positive for every L because it is at least ten.
This supplies positive denominators and a positive Mellin scale. -/
theorem gaussian1000_root_pos (L : ℝ) : 0 < gaussian1000Root L := by
  linarith only [gaussian1000_root_ten L]

/-- The combined radius is at least one hundred. Square the nonnegative
root floor to establish the smaller tail domain independently of L. -/
theorem gaussian1000_radius_hundred (L : ℝ) : (100 : ℝ) ≤ gaussian1000Radius L := by
  have hs := gaussian1000_root_ten L
  dsimp only [gaussian1000Radius]
  nlinarith only [hs, sq_nonneg (gaussian1000Root L - 10)]

/-- The cutoff is at least 12000 for every L. Square the radius floor and
rescale by six fifths, ensuring coverage of the certified 1000 prefix. -/
theorem gaussian1000_cutoff_floor (L : ℝ) : (12000 : ℝ) ≤ gaussian1000Bound L := by
  have hr := gaussian1000_radius_hundred L
  dsimp only [gaussian1000Bound]
  nlinarith only [hr, sq_nonneg (gaussian1000Radius L - 100)]

/-- For L>=0, the raw large-index root satisfies its quadratic equation.
Apply the generic discriminant identity before increasing the radius by a maximum. -/
theorem gaussian1000_large_equation {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedD * gaussian1000LargeRoot L ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussian1000LargeRoot L +
        163 / 20 := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have he :=
    gaussianBudgetRoot_equation (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1
      (add_nonneg (mul_nonneg hc hL) (by norm_num only : (0 : ℝ) ≤ 163 / 20))
  change
    gaussianMRRefinedD * gaussian1000LargeRoot L ^ 2 =
      gaussianMRRefinedBeta * gaussian1000LargeRoot L +
        (gaussianMRRefinedConductor * L + 163 / 20) at he
  linarith only [he]

/-- For L>=0, the raw index-four root satisfies its quadratic equation
with conductor coefficient 2c/3. This equality applies only to the raw root. -/
theorem gaussian1000_four_equation {L : ℝ} (hL : 0 ≤ L) :
    gaussian1000FourD * gaussian1000FourRoot L ^ 2 =
      (2 / 3 : ℝ) * gaussianMRRefinedConductor * L + gaussian1000FourBeta * gaussian1000FourRoot L +
        127 / 10 := by
  have hc : 0 ≤ (2 / 3 : ℝ) * gaussianMRRefinedConductor := by
    norm_num only [gaussianMRRefinedConductor]
  have he :=
    gaussianBudgetRoot_equation (b := gaussian1000FourBeta) gaussian1000_coefficients.1
      (add_nonneg (mul_nonneg hc hL) (by norm_num only : (0 : ℝ) ≤ 127 / 10))
  change
    gaussian1000FourD * gaussian1000FourRoot L ^ 2 =
      gaussian1000FourBeta * gaussian1000FourRoot L +
        ((2 / 3 : ℝ) * gaussianMRRefinedConductor * L + 127 / 10) at he
  linarith only [he]

/-- For L>=0, the combined radius satisfies the large-index budget
inequality. Compare the maximum with the raw root and use ten*d>beta.
No equality is asserted for the combined root. -/
theorem gaussian1000_large_budget {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussian1000Root L + 163 / 20 ≤
      gaussianMRRefinedD * gaussian1000Radius L := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * gaussian1000Root L := by
    have hs :=
      mul_le_mul_of_nonneg_left (gaussian1000_root_ten L) gaussianMRRefined_coefficients.1.le
    have hb : gaussianMRRefinedBeta < 10 * gaussianMRRefinedD := by
      norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    linarith only [hs, hb]
  have he :=
    gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2
      (add_nonneg (mul_nonneg hc hL) (by norm_num only : (0 : ℝ) ≤ 163 / 20)) hcoef
      ((le_max_left _ _ :
            gaussian1000LargeRoot L ≤ max (gaussian1000LargeRoot L) (gaussian1000FourRoot L)).trans
        (le_max_right _ _))
  change _ ≤ gaussianMRRefinedD * gaussian1000Radius L at he
  linarith only [he]

/-- For L>=0, the combined radius satisfies the index-four budget
inequality. Compare with the second raw root and retain its independent
conductor coefficient and residual allowance. -/
theorem gaussian1000_four_budget {L : ℝ} (hL : 0 ≤ L) :
    (2 / 3 : ℝ) * gaussianMRRefinedConductor * L + gaussian1000FourBeta * gaussian1000Root L +
        127 / 10 ≤
      gaussian1000FourD * gaussian1000Radius L := by
  have hc : 0 ≤ (2 / 3 : ℝ) * gaussianMRRefinedConductor := by
    norm_num only [gaussianMRRefinedConductor]
  have hcoef : gaussian1000FourBeta < gaussian1000FourD * gaussian1000Root L := by
    have hs := mul_le_mul_of_nonneg_left (gaussian1000_root_ten L) gaussian1000_coefficients.1.le
    have hb : gaussian1000FourBeta < 10 * gaussian1000FourD := by
      norm_num only [gaussian1000FourD, gaussian1000FourBeta, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint]
    linarith only [hs, hb]
  have he :=
    gaussianBudget_of_root_le gaussian1000_coefficients.1 gaussian1000_coefficients.2
      (add_nonneg (mul_nonneg hc hL) (by norm_num only : (0 : ℝ) ≤ 127 / 10)) hcoef
      ((le_max_right _ _ :
            gaussian1000FourRoot L ≤ max (gaussian1000LargeRoot L) (gaussian1000FourRoot L)).trans
        (le_max_right _ _))
  change _ ≤ gaussian1000FourD * gaussian1000Radius L at he
  linarith only [he]

/-- For r>=100, the contour tail is at most 271/1000 and the archimedean
term is at most 2/1000. Use the rational sixteenth-root anchor 7/4;
this avoids applying the older radius-170 estimate outside its domain. -/
theorem gaussian1000_tail {r : ℝ} (hr : 100 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 271 / 1000 ∧ (512 / 27 : ℝ) / r ^ 2 ≤ 2 / 1000 := by
  have hp : 0 < r := by linarith only [hr]
  have hx : (7 / 4 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only
    nlinarith only [hr]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 7 / 4) (by norm_num only)
      hx
  rw [Real.sqrt_sq hp.le] at hdec
  have hl := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
  constructor
  · have hc : (473 / 10 : ℝ) / ((7 / 4 : ℝ) * r) ≤ 271 / 1000 := by
      rw [div_le_iff₀ (mul_pos (by norm_num only) hp)]
      nlinarith only [hr]
    have he : (473 / 10 : ℝ) * (1 / ((7 / 4 : ℝ) * r)) = (473 / 10 : ℝ) / ((7 / 4 : ℝ) * r) := by
      ring
    exact (hl.trans_eq he).trans hc
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    nlinarith only [hr]

/-- For r=s squared>0 satisfying the large-index budget with any allowance D,
bound the pole by a constant plus retained inverse-root and inverse-radius terms.
Multiply by the positive radius and preserve the signed quadratic term. -/
theorem gaussianBudget_pole_bound {L r s D : ℝ} (hr : 0 < r) (hreq : r = s ^ 2)
    (hG : gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * r) :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) ≤
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
          (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
              (6 * gaussianMRRefinedConductor)) /
            s +
        (gaussianMR6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))) / s ^ 2 := by
  have hs : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num only)] at hreq
    exact hr.ne' hreq
  have hmul :=
    mul_le_mul_of_nonneg_left hG
      (by norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor] :
        (0 : ℝ) ≤ 7 * gaussianMR6FifthsEndpoint / (6 * gaussianMRRefinedConductor))
  have hcne : gaussianMRRefinedConductor ≠ 0 := by norm_num only [gaussianMRRefinedConductor]
  have hid :
    (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
                (6 * gaussianMRRefinedConductor)) /
              s +
          (gaussianMR6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))) / s ^ 2) *
        r =
      (7 * gaussianMR6FifthsEndpoint / (6 * gaussianMRRefinedConductor)) *
          (gaussianMRRefinedD * r - gaussianMRRefinedBeta * s - D) +
        4 * gaussianMR6FifthsEndpoint := by
    rw [hreq]
    field_simp [hs, hcne]
    ring
  have hl :
    (gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r)) * r =
      gaussianMR6FifthsEndpoint * ((7 / 6 : ℝ) * L + 4) := by
    field_simp [hr.ne']
  apply (mul_le_mul_iff_right₀ hr).mp
  norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor] at hmul hid hl ⊢
  nlinarith only [hmul, hid, hl]

/-- The coefficient of 1/s after eliminating the pole with the large-index
budget. The parameter eta is the normalized subgroup-index ratio. -/
noncomputable def gaussian1000ResidualA (eta : ℝ) : ℝ :=
  eta * (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth)) -
    7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor)

/-- The coefficient of 1/s squared after pole elimination with allowance
163/20. It must be estimated jointly with the inverse-root coefficient. -/
noncomputable def gaussian1000ResidualV (eta : ℝ) : ℝ :=
  eta * (1839 * gaussianMR6FifthsEndpoint / 1000) +
    gaussianMR6FifthsEndpoint * (4 - 7 * (163 / 20) / (6 * gaussianMRRefinedConductor))

/-- The large-index cap ratio satisfies both signed coefficient checks and
the strict residual bound below 163/20. Verify every constant by rational arithmetic. -/
theorem gaussian1000_large_checks :
    let eta := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
    0 < gaussian1000ResidualA eta ∧
      gaussian1000ResidualV eta < 0 ∧
      0 < gaussian1000ResidualA eta * 10 + gaussian1000ResidualV eta ∧
      0 < gaussian1000ResidualA eta * 10 + 2 * gaussian1000ResidualV eta ∧
      (12871 / 1000 : ℝ) - 2 * (7191 / 2000) +
          7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA eta / 10 +
          gaussian1000ResidualV eta / 100 +
          13 / (gaussianMR6FifthsIndex - 1) +
          273 / 1000 <
        163 / 20 := by
  norm_num only [gaussian1000ResidualA, gaussian1000ResidualV, gaussianMRRefinedD,
    gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, and_self]

/-- The index-four ratio satisfies both signed coefficient checks and the
strict residual bound below 127/10. Keep the pole allowance from the large-index root. -/
theorem gaussian1000_four_checks :
    0 < gaussian1000ResidualA (4 / 3) ∧
      gaussian1000ResidualV (4 / 3) < 0 ∧
      0 < gaussian1000ResidualA (4 / 3) * 10 + gaussian1000ResidualV (4 / 3) ∧
      0 < gaussian1000ResidualA (4 / 3) * 10 + 2 * gaussian1000ResidualV (4 / 3) ∧
      (12871 / 1000 : ℝ) - 2 * (7191 / 2000) +
          7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA (4 / 3) / 10 +
          gaussian1000ResidualV (4 / 3) / 100 +
          13 / 3 +
          273 / 1000 <
        127 / 10 := by
  norm_num only [gaussian1000ResidualA, gaussian1000ResidualV, gaussianMRRefinedD,
    gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, and_self]

/-- For L>=0 and log q<=L, paired inverse-power checks and a strict rational
anchor imply a strict normalized Gaussian error cap. Retain the signed pole terms
and use the radius-100 tail estimates. This serves both index branches. -/
theorem gaussian1000_error_cap {L eta eps D : ℝ} {q : ℕ} (hL : 0 ≤ L) (hq : Real.log q ≤ L)
    (h1 : 0 ≤ gaussian1000ResidualA eta * 10 + gaussian1000ResidualV eta)
    (h2 : 0 ≤ gaussian1000ResidualA eta * 10 + 2 * gaussian1000ResidualV eta)
    (hstrict :
      (12871 / 1000 : ℝ) - 2 * (7191 / 2000) +
          7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA eta / 10 +
          gaussian1000ResidualV eta / 100 +
          eps +
          273 / 1000 <
        D) :
    let s := gaussian1000Root L
    let r := gaussian1000Radius L
    eta *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        eps +
        LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) <
      D := by
  intro s r
  have hs0 : (10 : ℝ) ≤ s := gaussian1000_root_ten L
  have hr100 : (100 : ℝ) ≤ r := gaussian1000_radius_hundred L
  have hspos : 0 < s := by linarith only [hs0]
  have hrpos : 0 < r := by linarith only [hr100]
  have hreq : r = s ^ 2 := rfl
  have hpole := gaussianBudget_pole_bound hrpos hreq (gaussian1000_large_budget hL)
  have hqmul :=
    mul_le_mul_of_nonneg_left hq
      (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ gaussianMR6FifthsEndpoint * (7 / 6))
  have hqPole :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply (mul_le_mul_iff_right₀ hrpos).mp
    field_simp [hrpos.ne']
    linarith only [hqmul]
  have htail := gaussian1000_tail hr100
  have hinverse := inverse_pair_le_anchor (by norm_num only : (0 : ℝ) < 10) hs0 h1 h2
  have hid :
    eta *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
                (6 * gaussianMRRefinedConductor)) /
              s +
          (gaussianMR6FifthsEndpoint * (4 - 7 * (163 / 20) / (6 * gaussianMRRefinedConductor))) /
            s ^ 2) =
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        gaussian1000ResidualA eta / s +
        gaussian1000ResidualV eta / s ^ 2 := by
    rw [hreq]
    dsimp only [gaussian1000ResidualA, gaussian1000ResidualV]
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hpole hqPole hid hstrict ⊢
  linarith only [hpole, hqPole, htail.1, htail.2, hid, hinverse, hstrict]

/-- For L>=0 and log q<=L, the normalized index-four error is below 127/10.
Apply the common signed residual estimate at eta=4/3 and independent error 13/3. -/
theorem gaussian1000_four_error {L : ℝ} {q : ℕ} (hL : 0 ≤ L) (hq : Real.log q ≤ L) :
    let s := gaussian1000Root L
    let r := gaussian1000Radius L
    (4 / 3 : ℝ) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) <
      127 / 10 := by
  have hc := gaussian1000_four_checks
  exact gaussian1000_error_cap hL hq hc.2.2.1.le hc.2.2.2.1.le hc.2.2.2.2

/-- For L>=0, index m>=10^9 and log q<=L, the normalized error is below
163/20. Bound the ratio and independent error by their large-index caps,
then apply the common paired residual estimate. -/
theorem gaussian1000_large_error {L m : ℝ} {q : ℕ} (hL : 0 ≤ L) (hm : gaussianMR6FifthsIndex ≤ m)
    (hq : Real.log q ≤ L) :
    let s := gaussian1000Root L
    let r := gaussian1000Radius L
    (m / (m - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) <
      163 / 20 := by
  intro s r
  have hc := gaussian1000_large_checks
  have herr := gaussian1000_error_cap hL hq hc.2.2.1.le hc.2.2.2.1.le hc.2.2.2.2
  have hs : 0 < s := gaussian1000_root_pos L
  have hr : 0 < r := sq_pos_of_pos hs
  have hmain :
    0 ≤
      21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
        1839 * gaussianMR6FifthsEndpoint / (1000 * r) := by
    exact
      add_nonneg
        (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
          (mul_nonneg (by norm_num only [gaussianMRRefinedWidth]) hs.le))
        (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
          (mul_nonneg (by norm_num only) hr.le))
  have hcoef := gaussianMRRefined_index_coeffs hm
  have hratio := mul_le_mul_of_nonneg_right hcoef.2.1 hmain
  have hden : gaussianMR6FifthsIndex - 1 ≤ m - 1 := by linarith only [hm]
  have heps :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 13)
      (by norm_num only [gaussianMR6FifthsIndex] : 0 < gaussianMR6FifthsIndex - 1) hden
  change _ + _ + LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) < _ at herr
  linarith only [herr, hratio, heps]

/-- For L>=63, the combined radius exceeds 5L/8. The exact conductor
coefficient exceeds 5d/8 and the remaining budget terms are positive. -/
theorem gaussian1000_radius_linear {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < gaussian1000Radius L := by
  have hG := gaussian1000_large_budget (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (gaussian1000_root_pos L)
  have hD : (0 : ℝ) < 163 / 20 := by norm_num only
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  nlinarith only [hG, hp, hD, hm, hd]

/-- For L>=63, the cutoff exceeds 15 L squared/32. Square the positive
linear radius lower bound. This covers the local subgroup witness envelope. -/
theorem gaussian1000_bound_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussian1000Bound L := by
  have hr := gaussian1000_radius_linear hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussian1000Radius L ^ 2
  nlinarith only [hs]

end PseudoPrime.Analysis
