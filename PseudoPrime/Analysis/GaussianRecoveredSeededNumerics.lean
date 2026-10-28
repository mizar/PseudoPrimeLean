/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRClippedNumerics

/-! # Recovered seeded Gaussian bounds from strengthened actual prefixes -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The prefix cutoff N: 35000 in the false profile and 50000 in the true profile.
Both profiles reuse existing prefix data and share the refined Gaussian constants. -/
def gaussianRecoveredSeededCutoff (fifty : Bool) : ℕ :=
  if fifty then 50000 else 35000

/-- The residual allowance D: 283/50 for the 35000 profile, 136/25 for the 50000 profile. -/
noncomputable def gaussianRecoveredSeededConstant (fifty : Bool) : ℝ :=
  if fifty then 136 / 25 else 283 / 50

/-- The certified Gaussian prefix lower bound: 958409/200000 or 244919/50000.
The stronger 35000 value is reconstructed from the existing Gamma prefix. -/
noncomputable def gaussianRecoveredSeededPrefix (fifty : Bool) : ℝ :=
  if fifty then 244919 / 50000 else 958409 / 200000

/-- The inverse-root anchor s0: thirteen for 35000 and fourteen for 50000.
The floor, rather than a logarithmic entrance restriction, guarantees this lower bound. -/
noncomputable def gaussianRecoveredSeededAnchor (fifty : Bool) : ℝ :=
  if fifty then 14 else 13

/-- The positive quadratic root t of d*t^2=c*L+beta*t+D for the selected profile.
The existing refined mass, width, conductor coefficient and index split are reused. -/
noncomputable def gaussianRecoveredSeededRawRoot (fifty : Bool) (L : ℝ) : ℝ :=
  (gaussianMRRefinedBeta +
      Real.sqrt
        (gaussianMRRefinedBeta ^ 2 +
          4 * gaussianMRRefinedD *
            (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant fifty))) /
    (2 * gaussianMRRefinedD)

/-- The clipped root max(sqrt(sqrt(5N/6)),t).
The cutoff floor retains the certified prefix at every logarithmic scale. -/
noncomputable def gaussianRecoveredSeededRoot (fifty : Bool) (L : ℝ) : ℝ :=
  max (Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff fifty : ℝ))))
    (gaussianRecoveredSeededRawRoot fifty L)

/-- The squared clipped root r=s^2. Its square is the Mellin scale x. -/
noncomputable def gaussianRecoveredSeededRadius (fifty : Bool) (L : ℝ) : ℝ :=
  gaussianRecoveredSeededRoot fifty L ^ 2

/-- The cutoff (6/5)r^2 for a clipped profile. It equals max(N,(6/5)t^4).
The all-input witness theorem applies from logarithmic scale 63. -/
noncomputable def gaussianRecoveredSeededBound (fifty : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianRecoveredSeededRadius fifty L ^ 2

/-- Both residual allowances are positive, by rational evaluation of the profiles. -/
theorem gaussianRecoveredSeeded_constant_pos (f : Bool) :
    0 < gaussianRecoveredSeededConstant f := by
  cases f <;>
    norm_num only [gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false, ite_true]

/-- The raw root is positive at every L. The positive beta term and nonnegative
square root give a positive numerator; the quadratic denominator is positive. -/
theorem gaussianRecoveredSeeded_raw_pos (f : Bool) (L : ℝ) :
    0 < gaussianRecoveredSeededRawRoot f L := by
  exact
    div_pos (add_pos_of_pos_of_nonneg gaussianMRRefined_coefficients.2 (Real.sqrt_nonneg _))
      (mul_pos (by norm_num only) gaussianMRRefined_coefficients.1)

/-- The clipped root is positive because it is at least the positive raw root. -/
theorem gaussianRecoveredSeeded_root_pos (f : Bool) (L : ℝ) : 0 < gaussianRecoveredSeededRoot f L :=
  (gaussianRecoveredSeeded_raw_pos f L).trans_le (le_max_right _ _)

/-- For L>=0, the raw root satisfies its exact quadratic equation.
Square the discriminant identity. This equality is used only before clipping. -/
theorem gaussianRecoveredSeeded_raw_equation (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedD * gaussianRecoveredSeededRawRoot f L ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianRecoveredSeededRawRoot f L +
        gaussianRecoveredSeededConstant f := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  let z :=
    Real.sqrt
      (gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f))
  have ha :
    0 ≤
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
        (add_nonneg (mul_nonneg hc.le hL) (gaussianRecoveredSeeded_constant_pos f).le))
  have hz :
    z ^ 2 =
      gaussianMRRefinedBeta ^ 2 +
        4 * gaussianMRRefinedD *
          (gaussianMRRefinedConductor * L + gaussianRecoveredSeededConstant f) :=
    Real.sq_sqrt ha
  have hlin :=
    div_mul_cancel₀ (gaussianMRRefinedBeta + z)
      (ne_of_gt (mul_pos (by norm_num only : (0 : ℝ) < 2) hd))
  change
    gaussianRecoveredSeededRawRoot f L * (2 * gaussianMRRefinedD) =
      gaussianMRRefinedBeta + z at hlin
  have hsq := congrArg (fun u : ℝ ↦ u ^ 2) hlin
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
    gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsEndpoint] at hz hlin hsq ⊢
  nlinarith only [hz, hlin, hsq]

/-- Each clipped root is at least its profile anchor.
Compare nonnegative squares twice using the fixed cutoff N. -/
theorem gaussianRecoveredSeeded_root_anchor (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededAnchor f ≤ gaussianRecoveredSeededRoot f L := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ) :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have ha : 0 ≤ gaussianRecoveredSeededAnchor f := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededAnchor, Bool.false_eq_true, ite_false, ite_true]
  have h4 :
    gaussianRecoveredSeededAnchor f ^ 4 ≤ (5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededAnchor, gaussianRecoveredSeededCutoff,
        Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  have h2 :
    gaussianRecoveredSeededAnchor f ^ 2 ≤
      Real.sqrt ((5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ)) :=
    (Real.le_sqrt (sq_nonneg _) h0).mpr (by nlinarith only [h4])
  have h1 := (Real.le_sqrt ha (Real.sqrt_nonneg _)).mpr h2
  exact h1.trans (le_max_left _ _)

/-- Both profiles have clipped root at least thirteen.
This common anchor controls the width and the index-four error. -/
theorem gaussianRecoveredSeeded_root_thirteen (f : Bool) (L : ℝ) :
    (13 : ℝ) ≤ gaussianRecoveredSeededRoot f L := by
  have ha : (13 : ℝ) ≤ gaussianRecoveredSeededAnchor f := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededAnchor, Bool.false_eq_true, ite_false, ite_true]
  exact ha.trans (gaussianRecoveredSeeded_root_anchor f L)

/-- The clipped radius is at least sqrt(5N/6).
Square the nonnegative floor-to-root comparison. -/
theorem gaussianRecoveredSeeded_radius_floor (f : Bool) (L : ℝ) :
    Real.sqrt ((5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ)) ≤
      gaussianRecoveredSeededRadius f L := by
  have hs :
    Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ))) ≤
      gaussianRecoveredSeededRoot f L :=
    le_max_left _ _
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (gaussianRecoveredSeeded_root_pos f L).le).mpr hs
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)] at hsq
  exact hsq

/-- The clipped radius is at least 170, independent of L.
The cutoff floor implies the rational square comparison for both profiles. -/
theorem gaussianRecoveredSeeded_radius_large (f : Bool) (L : ℝ) :
    (170 : ℝ) ≤ gaussianRecoveredSeededRadius f L := by
  have h := gaussianRecoveredSeeded_radius_floor f L
  apply le_trans _ h
  apply (Real.le_sqrt (by norm_num only) (mul_nonneg (by norm_num only) (Nat.cast_nonneg _))).mpr
  cases f <;>
    norm_num only [gaussianRecoveredSeededCutoff, Bool.false_eq_true, ite_false, ite_true,
      Nat.cast_ofNat]

/-- The clipped witness cutoff contains the entire prefix N.
Square the radius floor and rescale by six fifths. -/
theorem gaussianRecoveredSeeded_cutoff_le (f : Bool) (L : ℝ) :
    (gaussianRecoveredSeededCutoff f : ℝ) ≤ gaussianRecoveredSeededBound f L := by
  have h := gaussianRecoveredSeeded_radius_floor f L
  have h0 : 0 ≤ (5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ) :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (sq_nonneg (gaussianRecoveredSeededRoot f L))).mpr h
  rw [Real.sq_sqrt h0] at hs
  change
    (5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ) ≤
      gaussianRecoveredSeededRadius f L ^ 2 at hs
  change _ ≤ (6 / 5 : ℝ) * gaussianRecoveredSeededRadius f L ^ 2
  linarith only [hs]

/-- For L>=0, the clipped root satisfies d*r>=c*L+beta*s+D.
Factor the difference from the raw-root equation and use 13*d>beta.
An equality is not asserted after clipping. -/
theorem gaussianRecoveredSeeded_equation_le (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianRecoveredSeededRoot f L +
        gaussianRecoveredSeededConstant f ≤
      gaussianMRRefinedD * gaussianRecoveredSeededRadius f L := by
  have ht := gaussianRecoveredSeeded_raw_equation f hL
  have hs := gaussianRecoveredSeeded_root_thirteen f L
  have hge : gaussianRecoveredSeededRawRoot f L ≤ gaussianRecoveredSeededRoot f L :=
    le_max_right _ _
  have hbeta : gaussianMRRefinedBeta < 13 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hdt :=
    mul_nonneg gaussianMRRefined_coefficients.1.le (gaussianRecoveredSeeded_raw_pos f L).le
  have hds := mul_le_mul_of_nonneg_left hs gaussianMRRefined_coefficients.1.le
  have hp :=
    mul_nonneg (sub_nonneg.mpr hge)
      (by linarith only [hbeta, hds, hdt] :
        0 ≤
          gaussianMRRefinedD *
              (gaussianRecoveredSeededRoot f L + gaussianRecoveredSeededRawRoot f L) -
            gaussianMRRefinedBeta)
  change _ ≤ gaussianMRRefinedD * gaussianRecoveredSeededRoot f L ^ 2
  nlinarith only [ht, hp]

/-- The positive inverse-root coefficient after the pole cost is eliminated
using the clipped-root inequality and the large-index ratio cap. -/
noncomputable def gaussianRecoveredSeededResidualA : ℝ :=
  (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
      (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth)) -
    7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor)

/-- The profile-dependent negative inverse-radius coefficient in the residual.
It must be estimated jointly with the positive inverse-root term. -/
noncomputable def gaussianRecoveredSeededResidualV (f : Bool) : ℝ :=
  (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
      (1839 * gaussianMR6FifthsEndpoint / 1000) +
    gaussianMR6FifthsEndpoint *
      (4 - 7 * gaussianRecoveredSeededConstant f / (6 * gaussianMRRefinedConductor))

/-- Both profiles satisfy the signed coefficient and strict residual inequalities.
Exact rational evaluation checks the anchors; no input enumeration is used. -/
theorem gaussianRecoveredSeeded_residual_checks (f : Bool) :
    0 < gaussianRecoveredSeededResidualA ∧
      gaussianRecoveredSeededResidualV f < 0 ∧
      0 <
        gaussianRecoveredSeededResidualA * gaussianRecoveredSeededAnchor f +
          2 * gaussianRecoveredSeededResidualV f ∧
      0 <
        gaussianRecoveredSeededResidualA * gaussianRecoveredSeededAnchor f +
          gaussianRecoveredSeededResidualV f ∧
      (12871 / 1000 : ℝ) - 2 * gaussianRecoveredSeededPrefix f +
          7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussianRecoveredSeededResidualA / gaussianRecoveredSeededAnchor f +
          gaussianRecoveredSeededResidualV f / gaussianRecoveredSeededAnchor f ^ 2 +
          13 / (gaussianMR6FifthsIndex - 1) +
          148 / 1000 <
        gaussianRecoveredSeededConstant f := by
  cases f <;>
    norm_num only [gaussianRecoveredSeededResidualA, gaussianRecoveredSeededResidualV,
      gaussianRecoveredSeededAnchor, gaussianRecoveredSeededPrefix, gaussianRecoveredSeededConstant,
      gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor, gaussianMRRefinedWidth,
      gaussianMRRefinedMass, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, Bool.false_eq_true,
      ite_false, ite_true, and_self]

/-- For r=s^2>0 satisfying the clipped budget, bound the pole term by the
retained inverse-root and inverse-square expression. Multiply by the positive radius
and use the exact conductor coefficient; the inequality direction is preserved. -/
theorem gaussianRecoveredSeeded_pole_bound {f : Bool} {L r s : ℝ} (hr : 0 < r) (hreq : r = s ^ 2)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s +
          gaussianRecoveredSeededConstant f ≤
        gaussianMRRefinedD * r) :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) ≤
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
          (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
              (6 * gaussianMRRefinedConductor)) /
            s +
        (gaussianMR6FifthsEndpoint *
            (4 - 7 * gaussianRecoveredSeededConstant f / (6 * gaussianMRRefinedConductor))) /
          s ^ 2 := by
  have hs : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num only)] at hreq
    exact hr.ne' hreq
  have hmul :=
    mul_le_mul_of_nonneg_left hG
      (by norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor] :
        (0 : ℝ) ≤ 7 * gaussianMR6FifthsEndpoint / (6 * gaussianMRRefinedConductor))
  have hid :
    (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
                (6 * gaussianMRRefinedConductor)) /
              s +
          (gaussianMR6FifthsEndpoint *
              (4 - 7 * gaussianRecoveredSeededConstant f / (6 * gaussianMRRefinedConductor))) /
            s ^ 2) *
        r =
      (7 * gaussianMR6FifthsEndpoint / (6 * gaussianMRRefinedConductor)) *
          (gaussianMRRefinedD * r - gaussianMRRefinedBeta * s - gaussianRecoveredSeededConstant f) +
        4 * gaussianMR6FifthsEndpoint := by
    rw [hreq]
    have hcancel (z : ℝ) : z / s * s ^ 2 = z * s := by
      rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ hs]
    simp only [add_mul, sub_mul, hcancel, div_mul_cancel₀ _ (pow_ne_zero 2 hs)]
    ring
  have hl :
    (gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r)) * r =
      gaussianMR6FifthsEndpoint * ((7 / 6 : ℝ) * L + 4) := by
    rw [mul_assoc, div_mul_cancel₀ _ hr.ne']
  apply (mul_le_mul_iff_right₀ hr).mp
  norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor] at hmul hid hl ⊢
  nlinarith only [hmul, hid, hl]

/-- For L>=63 and index m>=10^9, the normalized large-index error is strictly below D.
Use the clipped budget for the pole, the common tail caps, and the paired inverse
comparison at s0. The signed negative term is retained throughout. -/
theorem gaussianRecoveredSeeded_residual {f : Bool} {L m : ℝ} {q : ℕ} (hL : 63 ≤ L)
    (hm : gaussianMR6FifthsIndex ≤ m) (hq : Real.log q ≤ L) :
    let s := gaussianRecoveredSeededRoot f L
    let r := gaussianRecoveredSeededRadius f L
    (m / (m - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (gaussianRecoveredSeededPrefix f) q (r ^ 2) <
      gaussianRecoveredSeededConstant f := by
  intro s r
  have hs0 := gaussianRecoveredSeeded_root_anchor f L
  change gaussianRecoveredSeededAnchor f ≤ s at hs0
  have h13 := gaussianRecoveredSeeded_root_thirteen f L
  change (13 : ℝ) ≤ s at h13
  have hr170 := gaussianRecoveredSeeded_radius_large f L
  change (170 : ℝ) ≤ r at hr170
  have hspos : 0 < s := by linarith only [h13]
  have hrpos : 0 < r := by linarith only [hr170]
  have hreq : r = s ^ 2 := rfl
  have hG := gaussianRecoveredSeeded_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hpole := gaussianRecoveredSeeded_pole_bound hrpos hreq hG
  have hqmul :=
    mul_le_mul_of_nonneg_left hq
      (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ gaussianMR6FifthsEndpoint * (7 / 6))
  have hqPole :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply
      mul_le_mul_of_nonneg_left _
        (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ gaussianMR6FifthsEndpoint)
    apply div_le_div_of_nonneg_right _ hrpos.le
    linarith only [hq]
  have htail := gaussianMR6_tail240 hr170
  have hcoef := gaussianMRRefined_index_coeffs hm
  have hmain0 :
    0 ≤
      21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
        1839 * gaussianMR6FifthsEndpoint / (1000 * r) := by
    exact
      add_nonneg
        (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
          (mul_nonneg (by norm_num only [gaussianMRRefinedWidth]) hspos.le))
        (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
          (mul_nonneg (by norm_num only) hrpos.le))
  have hmRatio := mul_le_mul_of_nonneg_right hcoef.2.1 hmain0
  have hmden : gaussianMR6FifthsIndex - 1 ≤ m - 1 := by linarith only [hm]
  have h13div :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 13)
      (by norm_num only [gaussianMR6FifthsIndex] : 0 < gaussianMR6FifthsIndex - 1) hmden
  have hchecks := gaussianRecoveredSeeded_residual_checks f
  have hsanchor : 0 < gaussianRecoveredSeededAnchor f := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededAnchor, Bool.false_eq_true, ite_false, ite_true]
  have hinverse := inverse_pair_le_anchor hsanchor hs0 hchecks.2.2.2.1.le hchecks.2.2.1.le
  have hid :
    (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
                (6 * gaussianMRRefinedConductor)) /
              s +
          (gaussianMR6FifthsEndpoint *
              (4 - 7 * gaussianRecoveredSeededConstant f / (6 * gaussianMRRefinedConductor))) /
            s ^ 2) =
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        gaussianRecoveredSeededResidualA / s +
        gaussianRecoveredSeededResidualV f / s ^ 2 := by
    rw [hreq]
    dsimp only [gaussianRecoveredSeededResidualA, gaussianRecoveredSeededResidualV]
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hpole hqPole hmRatio hid hchecks ⊢
  linarith only [hmRatio, h13div, hpole, hqPole, htail.1, htail.2, hid, hinverse, hchecks.2.2.2.2]

/-- For L>=63 and log q<=L, the normalized index-four error is strictly below eleven.
Use s>=13, r>=170, the stronger 35000 prefix, and the clipped pole inequality. -/
theorem gaussianRecoveredSeeded_triple_error {f : Bool} {L : ℝ} {q : ℕ} (hL : 63 ≤ L)
    (hq : Real.log q ≤ L) :
    let s := gaussianRecoveredSeededRoot f L
    let r := gaussianRecoveredSeededRadius f L
    (4 / 3 : ℝ) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (gaussianRecoveredSeededPrefix f) q (r ^ 2) <
      11 := by
  intro s r
  have h13 := gaussianRecoveredSeeded_root_thirteen f L
  change (13 : ℝ) ≤ s at h13
  have hr170 := gaussianRecoveredSeeded_radius_large f L
  change (170 : ℝ) ≤ r at hr170
  have hs : 0 < s := by linarith only [h13]
  have hr : 0 < r := by linarith only [hr170]
  have hpole :=
    gaussianRecoveredSeeded_pole_bound hr (show r = s ^ 2 from rfl)
      (gaussianRecoveredSeeded_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L))
  have hqmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
  have hqDiv := div_le_div_of_nonneg_right hqmul hr.le
  have hqPole :=
    mul_le_mul_of_nonneg_left (add_le_add hqDiv (le_refl (4 / r)))
      (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ gaussianMR6FifthsEndpoint)
  have hneg :
    gaussianMR6FifthsEndpoint *
        (4 - 7 * gaussianRecoveredSeededConstant f / (6 * gaussianMRRefinedConductor)) ≤
      0 := by
    cases f <;>
      norm_num only [gaussianMR6FifthsEndpoint, gaussianRecoveredSeededConstant,
        gaussianMRRefinedConductor, Bool.false_eq_true, ite_false, ite_true]
  have hnegDiv := div_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg s)
  have hposDiv :
    0 ≤
      (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor)) /
        s := by
    apply div_nonneg _ hs.le
    norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedBeta, gaussianMRRefinedWidth,
      gaussianMRRefinedMass, gaussianMR6FifthsIndex, gaussianMRRefinedConductor]
  have hqId (t : ℝ) :
    gaussianMR6FifthsEndpoint * ((7 / 6) * t / r + 4 / r) =
      gaussianMR6FifthsEndpoint * (((7 / 6) * t + 4) / r) := by
    ring
  rw [hqId (Real.log q), hqId L] at hqPole
  have hPcap :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) := by
    linarith only [hqPole, hpole, hnegDiv, hposDiv]
  have hS :=
    div_le_div_of_nonneg_left
      (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ 21 * gaussianMR6FifthsEndpoint)
      (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) < 10 * gaussianMRRefinedWidth * 13)
      (mul_le_mul_of_nonneg_left h13
        (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) ≤ 10 * gaussianMRRefinedWidth))
  have hR :=
    div_le_div_of_nonneg_left
      (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ 1839 * gaussianMR6FifthsEndpoint)
      (by norm_num only : (0 : ℝ) < 1000 * 170)
      (mul_le_mul_of_nonneg_left hr170 (by norm_num only : (0 : ℝ) ≤ 1000))
  have htail := gaussianMR6_tail240 hr170
  have hprefix : (958409 / 200000 : ℝ) ≤ gaussianRecoveredSeededPrefix f := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededPrefix, Bool.false_eq_true, ite_false, ite_true]
  have hcap :
    (4 / 3 : ℝ) *
              (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * 13) +
                1839 * gaussianMR6FifthsEndpoint / (1000 * 170)) +
            13 / 3 +
            12871 / 1000 -
          2 * (958409 / 200000) +
        148 / 1000 +
        7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) <
      11 := by
    norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMRRefinedConductor, gaussianMRRefinedWidth]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hr.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hPcap hS hR hcap ⊢
  linarith only [hPcap, hS, hR, htail.1, htail.2, hprefix, hcap]

/-- The normalized index-four main margin exceeds eleven in both profiles.
Factor its increase from s=13 and use D>=136/25 with exact rational coefficients. -/
theorem gaussianRecoveredSeeded_triple_main (f : Bool) (L : ℝ) :
    (11 : ℝ) <
      (gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD) *
            gaussianRecoveredSeededRadius f L -
          (gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta) *
            gaussianRecoveredSeededRoot f L +
        (2 / 3) * gaussianRecoveredSeededConstant f := by
  let a := gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD
  let b := gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta
  let s := gaussianRecoveredSeededRoot f L
  have h13 : (13 : ℝ) ≤ s := gaussianRecoveredSeeded_root_thirteen f L
  have ha : 0 < a := by
    norm_num only [a, gaussianMRRefinedTripleD, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hab : 0 < 26 * a - b := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hp :=
    mul_nonneg (sub_nonneg.mpr h13) (by nlinarith only [ha, hab, h13] : 0 ≤ a * (s + 13) - b)
  have hD : (136 / 25 : ℝ) ≤ gaussianRecoveredSeededConstant f := by
    cases f <;>
      norm_num only [gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false, ite_true]
  have hbase : (11 : ℝ) < a * 13 ^ 2 - b * 13 + (2 / 3) * (136 / 25) := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  change (11 : ℝ) < a * s ^ 2 - b * s + (2 / 3) * gaussianRecoveredSeededConstant f
  nlinarith only [hp, hD, hbase]

/-- For L>=63, the index-four normalized budget cannot hold with error at most eleven.
Subtract two thirds of the clipped-root budget and apply the strict main margin. -/
theorem gaussianRecoveredSeeded_triple_absurd {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    ¬(gaussianMRRefinedTripleD * gaussianRecoveredSeededRadius f L ≤
        (2 / 3 : ℝ) * gaussianMRRefinedConductor * L +
          gaussianMRRefinedTripleBeta * gaussianRecoveredSeededRoot f L +
          11) := by
  intro hb
  have hG := gaussianRecoveredSeeded_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hm := gaussianRecoveredSeeded_triple_main f L
  nlinarith only [hb, hG, hm]

/-- The clipped cutoff equals max(N,(6/5)t^4) at every L.
Square the nonnegative maximum branches twice, recovering the exact prefix floor. -/
theorem gaussianRecoveredSeeded_bound_eq_max (f : Bool) (L : ℝ) :
    gaussianRecoveredSeededBound f L =
      max (gaussianRecoveredSeededCutoff f : ℝ)
        ((6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2) := by
  let u := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianRecoveredSeededCutoff f : ℝ)))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have ht := (gaussianRecoveredSeeded_raw_pos f L).le
  have hs := (gaussianRecoveredSeeded_root_pos f L).le
  have hN : (6 / 5 : ℝ) * (u ^ 2) ^ 2 = (gaussianRecoveredSeededCutoff f : ℝ) := by
    dsimp only [u]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (by norm_num only) (Nat.cast_nonneg _))]
    ring
  have h2 :=
    (sq_le_sq₀ ht hs).mpr
      (le_max_right _ _ : gaussianRecoveredSeededRawRoot f L ≤ gaussianRecoveredSeededRoot f L)
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  have hraw :
    (6 / 5 : ℝ) * (gaussianRecoveredSeededRawRoot f L ^ 2) ^ 2 ≤ gaussianRecoveredSeededBound f L :=
    mul_le_mul_of_nonneg_left h4 (by norm_num only)
  apply le_antisymm _ (max_le (gaussianRecoveredSeeded_cutoff_le f L) hraw)
  by_cases h : u ≤ gaussianRecoveredSeededRawRoot f L
  · change (6 / 5 : ℝ) * ((max u (gaussianRecoveredSeededRawRoot f L)) ^ 2) ^ 2 ≤ _
    rw [max_eq_right h]
    exact le_max_right _ _
  · change (6 / 5 : ℝ) * ((max u (gaussianRecoveredSeededRawRoot f L)) ^ 2) ^ 2 ≤ _
    rw [max_eq_left (le_of_not_ge h), hN]
    exact le_max_left _ _

/-- For L>=63, the clipped radius strictly exceeds (5/8)L.
The exact conductor coefficient is greater than (5/8)d, and beta*s+D is positive. -/
theorem gaussianRecoveredSeeded_radius_linear {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianRecoveredSeededRadius f L := by
  have hG := gaussianRecoveredSeeded_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (gaussianRecoveredSeeded_root_pos f L)
  have hD := gaussianRecoveredSeeded_constant_pos f
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  nlinarith only [hG, hp, hD, hm, hd]

/-- For L>=63, each clipped cutoff exceeds (15/32)L^2.
Square the positive linear radius lower bound and multiply by six fifths.
This supplies local-envelope coverage and the later triangular-branch comparison. -/
theorem gaussianRecoveredSeeded_bound_lower {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianRecoveredSeededBound f L := by
  have hr := gaussianRecoveredSeeded_radius_linear (f := f) hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianRecoveredSeededRadius f L ^ 2
  nlinarith only [hs]

end PseudoPrime.Analysis
