/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRRefinedNumerics
public import PseudoPrime.Analysis.GaussianMR240Numerics
public import PseudoPrime.LLS.GammaCheckpoint35000
/-! # Gaussian bounds with certified floors -/
@[expose] public section

namespace PseudoPrime.Analysis

/-- The prefix cutoff N: 35000 in the false profile and 50000 in the true profile.
Both profiles reuse existing prefix data and share the refined Gaussian constants. -/
def gaussianFloorCutoff (fifty : Bool) : ℕ := if fifty then 50000 else 35000
/-- The residual allowance D: 29/5 for the 35000 profile, 111/20 for the 50000 profile. -/
noncomputable def gaussianFloorConstant (fifty : Bool) : ℝ := if fifty then 111 / 20 else 29 / 5
/-- The certified Gaussian prefix lower bound: 189499/40000 or 484381/100000.
The stronger 35000 value is reconstructed from the existing Gamma prefix. -/
noncomputable def gaussianFloorPrefix (fifty : Bool) : ℝ :=
  if fifty then 484381 / 100000 else 189499 / 40000
/-- The inverse-root anchor s0: thirteen for 35000 and fourteen for 50000.
The floor, rather than a logarithmic entrance restriction, guarantees this lower bound. -/
noncomputable def gaussianFloorAnchor (fifty : Bool) : ℝ := if fifty then 14 else 13

/-- The positive quadratic root t of d*t^2=c*L+beta*t+D for the selected profile.
The existing refined mass, width, conductor coefficient and index split are reused. -/
noncomputable def gaussianFloorRawRoot (fifty : Bool) (L : ℝ) : ℝ :=
  (gaussianMRRefinedBeta + Real.sqrt (gaussianMRRefinedBeta ^ 2 +
    4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianFloorConstant fifty))) /
    (2 * gaussianMRRefinedD)

/-- The clipped root max(sqrt(sqrt(5N/6)),t).
The cutoff floor retains the certified prefix at every logarithmic scale. -/
noncomputable def gaussianFloorRoot (fifty : Bool) (L : ℝ) : ℝ :=
  max (Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianFloorCutoff fifty : ℝ))))
    (gaussianFloorRawRoot fifty L)

/-- The squared clipped root r=s^2. Its square is the Mellin scale x. -/
noncomputable def gaussianFloorRadius (fifty : Bool) (L : ℝ) : ℝ :=
  gaussianFloorRoot fifty L ^ 2

/-- The cutoff (6/5)r^2 for a clipped profile. It equals max(N,(6/5)t^4).
The all-input witness theorem applies from logarithmic scale 63. -/
noncomputable def gaussianFloorBound (fifty : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianFloorRadius fifty L ^ 2

/-- Both residual allowances are positive, by rational evaluation of the profiles. -/
theorem gaussianFloor_constant_pos (f : Bool) : 0 < gaussianFloorConstant f := by
  cases f <;> norm_num only [gaussianFloorConstant, Bool.false_eq_true, ite_false, ite_true]

/-- The raw root is positive at every L. The positive beta term and nonnegative
square root give a positive numerator; the quadratic denominator is positive. -/
theorem gaussianFloor_raw_pos (f : Bool) (L : ℝ) : 0 < gaussianFloorRawRoot f L := by
  exact div_pos (add_pos_of_pos_of_nonneg gaussianMRRefined_coefficients.2 (Real.sqrt_nonneg _))
    (mul_pos (by norm_num only) gaussianMRRefined_coefficients.1)

/-- The clipped root is positive because it is at least the positive raw root. -/
theorem gaussianFloor_root_pos (f : Bool) (L : ℝ) : 0 < gaussianFloorRoot f L :=
  (gaussianFloor_raw_pos f L).trans_le (le_max_right _ _)

/-- For L>=0, the raw root satisfies its exact quadratic equation.
Square the discriminant identity. This equality is used only before clipping. -/
theorem gaussianFloor_raw_equation (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedD * gaussianFloorRawRoot f L ^ 2 =
      gaussianMRRefinedConductor * L +
        gaussianMRRefinedBeta * gaussianFloorRawRoot f L + gaussianFloorConstant f := by
  have hd := gaussianMRRefined_coefficients.1
  have hc : 0 < gaussianMRRefinedConductor := by
    norm_num only [gaussianMRRefinedConductor]
  let z := Real.sqrt (gaussianMRRefinedBeta ^ 2 +
    4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianFloorConstant f))
  have ha : 0 ≤ gaussianMRRefinedBeta ^ 2 +
      4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianFloorConstant f) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num only) hd.le)
      (add_nonneg (mul_nonneg hc.le hL) (gaussianFloor_constant_pos f).le))
  have hz : z ^ 2 = gaussianMRRefinedBeta ^ 2 +
      4 * gaussianMRRefinedD * (gaussianMRRefinedConductor * L + gaussianFloorConstant f) :=
    Real.sq_sqrt ha
  have hlin := div_mul_cancel₀ (gaussianMRRefinedBeta + z)
    (ne_of_gt (mul_pos (by norm_num only : (0 : ℝ) < 2) hd))
  change gaussianFloorRawRoot f L * (2 * gaussianMRRefinedD) = gaussianMRRefinedBeta + z at hlin
  have hsq := congrArg (fun u : ℝ ↦ u ^ 2) hlin
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta,
    gaussianMRRefinedConductor,
    gaussianMR6FifthsIndex, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsEndpoint] at hz hlin hsq ⊢
  nlinarith only [hz, hlin, hsq]


/-- Each clipped root is at least its profile anchor.
Compare nonnegative squares twice using the fixed cutoff N. -/
theorem gaussianFloor_root_anchor (f : Bool) (L : ℝ) :
    gaussianFloorAnchor f ≤ gaussianFloorRoot f L := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ) :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have ha : 0 ≤ gaussianFloorAnchor f := by
    cases f <;> norm_num only [gaussianFloorAnchor, Bool.false_eq_true, ite_false, ite_true]
  have h4 : gaussianFloorAnchor f ^ 4 ≤ (5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ) := by
    cases f <;> norm_num only [gaussianFloorAnchor, gaussianFloorCutoff,
      Bool.false_eq_true, ite_false, ite_true,
      Nat.cast_ofNat]
  have h2 : gaussianFloorAnchor f ^ 2 ≤ Real.sqrt ((5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ)) :=
    (Real.le_sqrt (sq_nonneg _) h0).mpr (by nlinarith only [h4])
  have h1 := (Real.le_sqrt ha (Real.sqrt_nonneg _)).mpr h2
  exact h1.trans (le_max_left _ _)

/-- Both profiles have clipped root at least thirteen.
This common anchor controls the width and the index-four error. -/
theorem gaussianFloor_root_thirteen (f : Bool) (L : ℝ) : (13 : ℝ) ≤ gaussianFloorRoot f L := by
  have ha : (13 : ℝ) ≤ gaussianFloorAnchor f := by
    cases f <;> norm_num only [gaussianFloorAnchor, Bool.false_eq_true, ite_false, ite_true]
  exact ha.trans (gaussianFloor_root_anchor f L)

/-- The clipped radius is at least sqrt(5N/6).
Square the nonnegative floor-to-root comparison. -/
theorem gaussianFloor_radius_floor (f : Bool) (L : ℝ) :
    Real.sqrt ((5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ)) ≤ gaussianFloorRadius f L := by
  have hs : Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ))) ≤
      gaussianFloorRoot f L := le_max_left _ _
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (gaussianFloor_root_pos f L).le).mpr hs
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)] at hsq
  exact hsq

/-- The clipped radius is at least 170, independent of L.
The cutoff floor implies the rational square comparison for both profiles. -/
theorem gaussianFloor_radius_large (f : Bool) (L : ℝ) :
    (170 : ℝ) ≤ gaussianFloorRadius f L := by
  have h := gaussianFloor_radius_floor f L
  apply le_trans _ h
  apply (Real.le_sqrt (by norm_num only)
    (mul_nonneg (by norm_num only) (Nat.cast_nonneg _))).mpr
  cases f <;> norm_num only [gaussianFloorCutoff, Bool.false_eq_true,
    ite_false, ite_true, Nat.cast_ofNat]

/-- The clipped witness cutoff contains the entire prefix N.
Square the radius floor and rescale by six fifths. -/
theorem gaussianFloor_cutoff_le (f : Bool) (L : ℝ) :
    (gaussianFloorCutoff f : ℝ) ≤ gaussianFloorBound f L := by
  have h := gaussianFloor_radius_floor f L
  have h0 : 0 ≤ (5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ) :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (sq_nonneg (gaussianFloorRoot f L))).mpr h
  rw [Real.sq_sqrt h0] at hs
  change (5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ) ≤ gaussianFloorRadius f L ^ 2 at hs
  change _ ≤ (6 / 5 : ℝ) * gaussianFloorRadius f L ^ 2
  linarith only [hs]

/-- For L>=0, the clipped root satisfies d*r>=c*L+beta*s+D.
Factor the difference from the raw-root equation and use 13*d>beta.
An equality is not asserted after clipping. -/
theorem gaussianFloor_equation_le (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianFloorRoot f L +
      gaussianFloorConstant f ≤ gaussianMRRefinedD * gaussianFloorRadius f L := by
  have ht := gaussianFloor_raw_equation f hL
  have hs := gaussianFloor_root_thirteen f L
  have hge : gaussianFloorRawRoot f L ≤ gaussianFloorRoot f L := le_max_right _ _
  have hbeta : gaussianMRRefinedBeta < 13 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hdt := mul_nonneg gaussianMRRefined_coefficients.1.le (gaussianFloor_raw_pos f L).le
  have hds := mul_le_mul_of_nonneg_left hs gaussianMRRefined_coefficients.1.le
  have hp := mul_nonneg (sub_nonneg.mpr hge)
    (by linarith only [hbeta, hds, hdt] :
      0 ≤ gaussianMRRefinedD * (gaussianFloorRoot f L + gaussianFloorRawRoot f L) -
        gaussianMRRefinedBeta)
  change _ ≤ gaussianMRRefinedD * gaussianFloorRoot f L ^ 2
  nlinarith only [ht, hp]

/-- For s>=u>0, the paired expression a/s+v/s^2 is at most its anchor value
when a*u+v and a*u+2v are nonnegative. Factor the exact difference.
This retains the beneficial negative inverse-square term with its correct direction. -/
theorem inverse_pair_le_anchor {a v s u : ℝ} (hu : 0 < u) (hs : u ≤ s)
    (h1 : 0 ≤ a * u + v) (h2 : 0 ≤ a * u + 2 * v) :
    a / s + v / s ^ 2 ≤ a / u + v / u ^ 2 := by
  have hspos := hu.trans_le hs
  have hb : 0 ≤ a * s * u + v * (s + u) := by
    have he : a * s * u + v * (s + u) = (s - u) * (a * u + v) + u * (a * u + 2 * v) := by
      ring
    rw [he]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs) h1) (mul_nonneg hu.le h2)
  have hf := div_nonneg (mul_nonneg (sub_nonneg.mpr hs) hb)
    (mul_nonneg (sq_nonneg s) (sq_nonneg u))
  have hid : a / u + v / u ^ 2 - (a / s + v / s ^ 2) =
      (s - u) * (a * s * u + v * (s + u)) / (s ^ 2 * u ^ 2) := by
    field_simp [hu.ne', hspos.ne']
    ring
  linarith only [hid, hf]

/-- The positive inverse-root coefficient after the pole cost is eliminated
using the clipped-root inequality and the large-index ratio cap. -/
noncomputable def gaussianFloorResidualA : ℝ :=
  (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
    (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth)) -
    7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor)

/-- The profile-dependent negative inverse-radius coefficient in the residual.
It must be estimated jointly with the positive inverse-root term. -/
noncomputable def gaussianFloorResidualV (f : Bool) : ℝ :=
  (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
    (1839 * gaussianMR6FifthsEndpoint / 1000) +
    gaussianMR6FifthsEndpoint * (4 - 7 * gaussianFloorConstant f / (6 * gaussianMRRefinedConductor))

/-- Both profiles satisfy the signed coefficient and strict residual inequalities.
Exact rational evaluation checks the anchors; no input enumeration is used. -/
theorem gaussianFloor_residual_checks (f : Bool) :
    0 < gaussianFloorResidualA ∧ gaussianFloorResidualV f < 0 ∧
    0 < gaussianFloorResidualA * gaussianFloorAnchor f + 2 * gaussianFloorResidualV f ∧
    0 < gaussianFloorResidualA * gaussianFloorAnchor f + gaussianFloorResidualV f ∧
    (12871 / 1000 : ℝ) - 2 * gaussianFloorPrefix f +
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
      gaussianFloorResidualA / gaussianFloorAnchor f +
      gaussianFloorResidualV f / gaussianFloorAnchor f ^ 2 +
      13 / (gaussianMR6FifthsIndex - 1) + 148 / 1000 < gaussianFloorConstant f := by
  cases f <;> norm_num only [gaussianFloorResidualA, gaussianFloorResidualV,
    gaussianFloorAnchor, gaussianFloorPrefix, gaussianFloorConstant,
    gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
    gaussianMRRefinedWidth, gaussianMRRefinedMass, gaussianMR6FifthsIndex,
    gaussianMR6FifthsEndpoint, Bool.false_eq_true, ite_false, ite_true, and_self]

/-- For r=s^2>0 satisfying the clipped budget, bound the pole term by the
retained inverse-root and inverse-square expression. Multiply by the positive radius
and use the exact conductor coefficient; the inequality direction is preserved. -/
theorem gaussianFloor_pole_bound {f : Bool} {L r s : ℝ} (hr : 0 < r)
    (hreq : r = s ^ 2)
    (hG : gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s +
      gaussianFloorConstant f ≤ gaussianMRRefinedD * r) :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) ≤
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
      (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
        (6 * gaussianMRRefinedConductor)) / s +
      (gaussianMR6FifthsEndpoint * (4 - 7 * gaussianFloorConstant f /
        (6 * gaussianMRRefinedConductor))) / s ^ 2 := by
  have hs : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num only)] at hreq
    exact hr.ne' hreq
  have hmul := mul_le_mul_of_nonneg_left hG
    (by norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor] :
      (0 : ℝ) ≤ 7 * gaussianMR6FifthsEndpoint / (6 * gaussianMRRefinedConductor))
  have hcne : gaussianMRRefinedConductor ≠ 0 := by
    norm_num only [gaussianMRRefinedConductor]
  have hid : (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD /
        (6 * gaussianMRRefinedConductor) -
      (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
        (6 * gaussianMRRefinedConductor)) / s +
      (gaussianMR6FifthsEndpoint * (4 - 7 * gaussianFloorConstant f /
        (6 * gaussianMRRefinedConductor))) / s ^ 2) * r =
      (7 * gaussianMR6FifthsEndpoint / (6 * gaussianMRRefinedConductor)) *
        (gaussianMRRefinedD * r - gaussianMRRefinedBeta * s - gaussianFloorConstant f) +
        4 * gaussianMR6FifthsEndpoint := by
    rw [hreq]
    field_simp [hs, hcne]
    ring
  have hl : (gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r)) * r =
      gaussianMR6FifthsEndpoint * ((7 / 6 : ℝ) * L + 4) := by
    field_simp [hr.ne']
  apply (mul_le_mul_iff_right₀ hr).mp
  norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor] at hmul hid hl ⊢
  nlinarith only [hmul, hid, hl]

/-- For L>=63 and index m>=10^9, the normalized large-index error is strictly below D.
Use the clipped budget for the pole, the common tail caps, and the paired inverse
comparison at s0. The signed negative term is retained throughout. -/
theorem gaussianFloor_residual {f : Bool} {L m : ℝ} {q : ℕ} (hL : 63 ≤ L)
    (hm : gaussianMR6FifthsIndex ≤ m) (hq : Real.log q ≤ L) :
    let s := gaussianFloorRoot f L
    let r := gaussianFloorRadius f L
    (m / (m - 1)) *
        (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
          1839 * gaussianMR6FifthsEndpoint / (1000 * r)) + 13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (gaussianFloorPrefix f) q (r ^ 2) <
      gaussianFloorConstant f := by
  intro s r
  have hs0 := gaussianFloor_root_anchor f L
  change gaussianFloorAnchor f ≤ s at hs0
  have h13 := gaussianFloor_root_thirteen f L
  change (13 : ℝ) ≤ s at h13
  have hr170 := gaussianFloor_radius_large f L
  change (170 : ℝ) ≤ r at hr170
  have hspos : 0 < s := by linarith only [h13]
  have hrpos : 0 < r := by linarith only [hr170]
  have hreq : r = s ^ 2 := rfl
  have hG := gaussianFloor_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hpole := gaussianFloor_pole_bound hrpos hreq hG
  have hqmul := mul_le_mul_of_nonneg_left hq
    (by norm_num only [gaussianMR6FifthsEndpoint] :
      (0 : ℝ) ≤ gaussianMR6FifthsEndpoint * (7 / 6))
  have hqPole : gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply (mul_le_mul_iff_right₀ hrpos).mp
    field_simp [hrpos.ne']
    linarith only [hqmul]
  have htail := gaussianMR6_tail240 hr170
  have hcoef := gaussianMRRefined_index_coeffs hm
  have hmain0 : 0 ≤ 21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
      1839 * gaussianMR6FifthsEndpoint / (1000 * r) := by
    exact add_nonneg (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
      (mul_nonneg (by norm_num only [gaussianMRRefinedWidth]) hspos.le))
      (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
        (mul_nonneg (by norm_num only) hrpos.le))
  have hmRatio := mul_le_mul_of_nonneg_right hcoef.2.1 hmain0
  have hmden : gaussianMR6FifthsIndex - 1 ≤ m - 1 := by linarith only [hm]
  have h13div := div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 13)
    (by norm_num only [gaussianMR6FifthsIndex] : 0 < gaussianMR6FifthsIndex - 1) hmden
  have hchecks := gaussianFloor_residual_checks f
  have hsanchor : 0 < gaussianFloorAnchor f := by
    cases f <;> norm_num only [gaussianFloorAnchor, Bool.false_eq_true, ite_false, ite_true]
  have hinverse := inverse_pair_le_anchor hsanchor hs0 hchecks.2.2.2.1.le hchecks.2.2.1.le
  have hid : (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
      (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
        1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
      (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
        (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
          (6 * gaussianMRRefinedConductor)) / s +
        (gaussianMR6FifthsEndpoint * (4 - 7 * gaussianFloorConstant f /
          (6 * gaussianMRRefinedConductor))) / s ^ 2) =
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        gaussianFloorResidualA / s + gaussianFloorResidualV f / s ^ 2 := by
    rw [hreq]
    dsimp only [gaussianFloorResidualA, gaussianFloorResidualV]
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hpole hqPole hmRatio hid hchecks ⊢
  linarith only [hmRatio, h13div, hpole, hqPole, htail.1, htail.2,
    hid, hinverse, hchecks.2.2.2.2]

/-- For L>=63 and log q<=L, the normalized index-four error is strictly below eleven.
Use s>=13, r>=170, the stronger 35000 prefix, and the clipped pole inequality. -/
theorem gaussianFloor_triple_error {f : Bool} {L : ℝ} {q : ℕ} (hL : 63 ≤ L)
    (hq : Real.log q ≤ L) :
    let s := gaussianFloorRoot f L
    let r := gaussianFloorRadius f L
    (4 / 3 : ℝ) *
        (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
          1839 * gaussianMR6FifthsEndpoint / (1000 * r)) + 13 / 3 +
      LLS.PaperStatements.gaussianPrefixError (gaussianFloorPrefix f) q (r ^ 2) < 11 := by
  intro s r
  have h13 := gaussianFloor_root_thirteen f L
  change (13 : ℝ) ≤ s at h13
  have hr170 := gaussianFloor_radius_large f L
  change (170 : ℝ) ≤ r at hr170
  have hs : 0 < s := by linarith only [h13]
  have hr : 0 < r := by linarith only [hr170]
  have hpole := gaussianFloor_pole_bound hr (show r = s ^ 2 from rfl)
    (gaussianFloor_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L))
  have hqmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
  have hqDiv := div_le_div_of_nonneg_right hqmul hr.le
  have hqPole := mul_le_mul_of_nonneg_left (add_le_add hqDiv (le_refl (4 / r)))
    (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ gaussianMR6FifthsEndpoint)
  have hneg : gaussianMR6FifthsEndpoint *
      (4 - 7 * gaussianFloorConstant f / (6 * gaussianMRRefinedConductor)) ≤ 0 := by
    cases f <;> norm_num only [gaussianMR6FifthsEndpoint, gaussianFloorConstant,
      gaussianMRRefinedConductor, Bool.false_eq_true, ite_false, ite_true]
  have hnegDiv := div_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg s)
  have hposDiv : 0 ≤ (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
      (6 * gaussianMRRefinedConductor)) / s := by
    apply div_nonneg _ hs.le
    norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedBeta,
      gaussianMRRefinedWidth, gaussianMRRefinedMass, gaussianMR6FifthsIndex,
      gaussianMRRefinedConductor]
  have hqId (t : ℝ) : gaussianMR6FifthsEndpoint * ((7 / 6) * t / r + 4 / r) =
      gaussianMR6FifthsEndpoint * (((7 / 6) * t + 4) / r) := by ring
  rw [hqId (Real.log q), hqId L] at hqPole
  have hPcap : gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) := by
    linarith only [hqPole, hpole, hnegDiv, hposDiv]
  have hS := div_le_div_of_nonneg_left
    (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ 21 * gaussianMR6FifthsEndpoint)
    (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) < 10 * gaussianMRRefinedWidth * 13)
    (mul_le_mul_of_nonneg_left h13
      (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) ≤ 10 * gaussianMRRefinedWidth))
  have hR := div_le_div_of_nonneg_left
    (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ 1839 * gaussianMR6FifthsEndpoint)
    (by norm_num only : (0 : ℝ) < 1000 * 170)
    (mul_le_mul_of_nonneg_left hr170 (by norm_num only : (0 : ℝ) ≤ 1000))
  have htail := gaussianMR6_tail240 hr170
  have hprefix : (189499 / 40000 : ℝ) ≤ gaussianFloorPrefix f := by
    cases f <;> norm_num only [gaussianFloorPrefix, Bool.false_eq_true, ite_false, ite_true]
  have hcap : (4 / 3 : ℝ) *
      (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * 13) +
        1839 * gaussianMR6FifthsEndpoint / (1000 * 170)) + 13 / 3 +
      12871 / 1000 - 2 * (189499 / 40000) + 148 / 1000 +
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD /
        (6 * gaussianMRRefinedConductor) < 11 := by
    norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMRRefinedConductor, gaussianMRRefinedWidth]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hr.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hPcap hS hR hcap ⊢
  linarith only [hPcap, hS, hR, htail.1, htail.2, hprefix, hcap]

/-- The normalized index-four main margin exceeds eleven in both profiles.
Factor its increase from s=13 and use D>=111/20 with exact rational coefficients. -/
theorem gaussianFloor_triple_main (f : Bool) (L : ℝ) :
    (11 : ℝ) <
      (gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD) * gaussianFloorRadius f L -
      (gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta) * gaussianFloorRoot f L +
      (2 / 3) * gaussianFloorConstant f := by
  let a := gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD
  let b := gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta
  let s := gaussianFloorRoot f L
  have h13 : (13 : ℝ) ≤ s := gaussianFloor_root_thirteen f L
  have ha : 0 < a := by
    norm_num only [a, gaussianMRRefinedTripleD, gaussianMRRefinedD,
      gaussianMRRefinedMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hab : 0 < 26 * a - b := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta,
      gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hp := mul_nonneg (sub_nonneg.mpr h13)
    (by nlinarith only [ha, hab, h13] : 0 ≤ a * (s + 13) - b)
  have hD : (111 / 20 : ℝ) ≤ gaussianFloorConstant f := by
    cases f <;> norm_num only [gaussianFloorConstant, Bool.false_eq_true, ite_false, ite_true]
  have hbase : (11 : ℝ) < a * 13 ^ 2 - b * 13 + (2 / 3) * (111 / 20) := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta,
      gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  change (11 : ℝ) < a * s ^ 2 - b * s + (2 / 3) * gaussianFloorConstant f
  nlinarith only [hp, hD, hbase]

/-- For L>=63, the index-four normalized budget cannot hold with error at most eleven.
Subtract two thirds of the clipped-root budget and apply the strict main margin. -/
theorem gaussianFloor_triple_absurd {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    ¬(gaussianMRRefinedTripleD * gaussianFloorRadius f L ≤
      (2 / 3 : ℝ) * gaussianMRRefinedConductor * L +
      gaussianMRRefinedTripleBeta * gaussianFloorRoot f L + 11) := by
  intro hb
  have hG := gaussianFloor_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hm := gaussianFloor_triple_main f L
  nlinarith only [hb, hG, hm]

/-- The clipped cutoff equals max(N,(6/5)t^4) at every L.
Square the nonnegative maximum branches twice, recovering the exact prefix floor. -/
theorem gaussianFloor_bound_eq_max (f : Bool) (L : ℝ) :
    gaussianFloorBound f L = max (gaussianFloorCutoff f : ℝ)
      ((6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2) := by
  let u := Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianFloorCutoff f : ℝ)))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have ht := (gaussianFloor_raw_pos f L).le
  have hs := (gaussianFloor_root_pos f L).le
  have hN : (6 / 5 : ℝ) * (u ^ 2) ^ 2 = (gaussianFloorCutoff f : ℝ) := by
    dsimp only [u]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (by norm_num only) (Nat.cast_nonneg _))]
    ring
  have h2 := (sq_le_sq₀ ht hs).mpr
    (le_max_right _ _ : gaussianFloorRawRoot f L ≤ gaussianFloorRoot f L)
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  have hraw : (6 / 5 : ℝ) * (gaussianFloorRawRoot f L ^ 2) ^ 2 ≤ gaussianFloorBound f L :=
    mul_le_mul_of_nonneg_left h4 (by norm_num only)
  apply le_antisymm _ (max_le (gaussianFloor_cutoff_le f L) hraw)
  by_cases h : u ≤ gaussianFloorRawRoot f L
  · change (6 / 5 : ℝ) * ((max u (gaussianFloorRawRoot f L)) ^ 2) ^ 2 ≤ _
    rw [max_eq_right h]
    exact le_max_right _ _
  · change (6 / 5 : ℝ) * ((max u (gaussianFloorRawRoot f L)) ^ 2) ^ 2 ≤ _
    rw [max_eq_left (le_of_not_ge h), hN]
    exact le_max_left _ _

/-- For L>=63, the clipped radius strictly exceeds (5/8)L.
The exact conductor coefficient is greater than (5/8)d, and beta*s+D is positive. -/
theorem gaussianFloor_radius_linear {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianFloorRadius f L := by
  have hG := gaussianFloor_equation_le f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (gaussianFloor_root_pos f L)
  have hD := gaussianFloor_constant_pos f
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD,
      gaussianMRRefinedMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  nlinarith only [hG, hp, hD, hm, hd]

/-- For L>=63, each clipped cutoff exceeds (15/32)L^2.
Square the positive linear radius lower bound and multiply by six fifths.
This supplies local-envelope coverage and the later triangular-branch comparison. -/
theorem gaussianFloor_bound_lower {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianFloorBound f L := by
  have hr := gaussianFloor_radius_linear (f := f) hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianFloorRadius f L ^ 2
  nlinarith only [hs]

end PseudoPrime.Analysis
