/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSeededSharpComparison
public import PseudoPrime.Analysis.GaussianLowFloorNumerics

/-! # Tuned seeded roots and floor-derived error certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The tuned residual is 5.619 for the 35000 profile and 5.372 for 50000. -/
noncomputable def gaussianSeededTunedConstant (f : Bool) : ℝ :=
  if f then 1343 / 250 else 5619 / 1000

/-- The actual Gaussian prefix credit is 4.81117 or 4.915295 for the respective cutoff. -/
noncomputable def gaussianSeededTunedPrefix (f : Bool) : ℝ :=
  if f then 983059 / 200000 else 481117 / 100000

/-- The rational root anchor is 13.068 or 14.287, derived from the unchanged cutoff floor. -/
noncomputable def gaussianSeededTunedAnchor (f : Bool) : ℝ :=
  if f then 14287 / 1000 else 3267 / 250

/-- The floor-derived tail allowance is 0.1464 or 0.1197 for the respective profile. -/
noncomputable def gaussianSeededTunedTail (f : Bool) : ℝ :=
  if f then 1197 / 10000 else 183 / 1250

/-- Each profile has its own exact displacement from the current sharp residual.
The 35000 and 50000 displacements differ; no common family displacement is defined. -/
noncomputable def gaussianSeededTunedShift (f : Bool) : ℝ :=
  if f then 1900000 / 20115621 else 550000 / 20115621

/-- The positive quadratic budget root with the tuned residual and existing common coefficients. -/
noncomputable def gaussianSeededTunedRawRoot (f : Bool) (L : ℝ) : ℝ :=
  gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
    (gaussianMRRefinedConductor * L + gaussianSeededTunedConstant f)

/-- Clip the tuned raw root at the unchanged fourth-root prefix floor.
This retains the actual certified prefix at every scale. -/
noncomputable def gaussianSeededTunedRoot (f : Bool) (L : ℝ) : ℝ :=
  max (Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianSeededSharpCutoff f : ℝ))))
    (gaussianSeededTunedRawRoot f L)

/-- The square of the clipped root is the Mellin radius; its square is the scale. -/
noncomputable def gaussianSeededTunedRadius (f : Bool) (L : ℝ) : ℝ :=
  gaussianSeededTunedRoot f L ^ 2

/-- The prime-witness cutoff is six fifths of the squared Mellin radius. -/
noncomputable def gaussianSeededTunedBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianSeededTunedRadius f L ^ 2

/-- Each tuned residual equals its current sharp residual minus conductor times its own shift. -/
theorem gaussianSeededTuned_constant_shift (f : Bool) :
    gaussianSeededTunedConstant f =
      gaussianSeededSharpConstant f - gaussianMRRefinedConductor * gaussianSeededTunedShift f := by
  cases f <;>
    norm_num only [gaussianSeededTunedConstant, gaussianSeededSharpConstant,
      gaussianMRRefinedConductor, gaussianSeededTunedShift, Bool.false_eq_true, ite_false, ite_true]

/-- For numerical comparison, each tuned raw root is its current raw root at the displaced scale.
This equality does not change the input of any actual witness theorem. -/
theorem gaussianSeededTuned_raw_shift (f : Bool) (L : ℝ) :
    gaussianSeededTunedRawRoot f L =
      gaussianSeededSharpRawRoot f (L - gaussianSeededTunedShift f) := by
  have he :
    gaussianMRRefinedConductor * L + gaussianSeededTunedConstant f =
      gaussianMRRefinedConductor * (L - gaussianSeededTunedShift f) +
        gaussianSeededSharpConstant f := by
    rw [gaussianSeededTuned_constant_shift]
    ring
  rw [gaussianSeededTunedRawRoot, gaussianBudgetRoot, gaussianSeededSharpRawRoot, he]

/-- The clipped roots inherit the same profile-specific numerical displacement. -/
theorem gaussianSeededTuned_root_shift (f : Bool) (L : ℝ) :
    gaussianSeededTunedRoot f L = gaussianSeededSharpRoot f (L - gaussianSeededTunedShift f) := by
  rw [gaussianSeededTunedRoot, gaussianSeededSharpRoot, gaussianSeededTuned_raw_shift]

/-- Each full clipped bound inherits its own numerical displacement, including the prefix floor. -/
theorem gaussianSeededTuned_bound_shift (f : Bool) (L : ℝ) :
    gaussianSeededTunedBound f L = gaussianSeededSharpBound f (L - gaussianSeededTunedShift f) := by
  simp only [gaussianSeededTunedBound, gaussianSeededTunedRadius, gaussianSeededSharpBound,
    gaussianSeededSharpRadius, gaussianSeededTuned_root_shift]

/-- The positive beta and denominator make the tuned raw root positive at every real scale. -/
theorem gaussianSeededTuned_raw_pos (f : Bool) (L : ℝ) : 0 < gaussianSeededTunedRawRoot f L :=
  gaussianBudgetRoot_pos gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2

/-- The clipped root is positive because it dominates the positive raw root. -/
theorem gaussianSeededTuned_root_pos (f : Bool) (L : ℝ) : 0 < gaussianSeededTunedRoot f L :=
  (gaussianSeededTuned_raw_pos f L).trans_le (le_max_right _ _)

/-- The unchanged prefix floor implies the sharper rational anchor for each root.
Compare nonnegative squares twice using exact rational fourth-power inequalities. -/
theorem gaussianSeededTuned_root_anchor (f : Bool) (L : ℝ) :
    gaussianSeededTunedAnchor f ≤ gaussianSeededTunedRoot f L := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * (gaussianSeededSharpCutoff f : ℝ) :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have ha : 0 ≤ gaussianSeededTunedAnchor f := by
    cases f <;> norm_num only [gaussianSeededTunedAnchor, Bool.false_eq_true, ite_false, ite_true]
  have h4 : gaussianSeededTunedAnchor f ^ 4 ≤ (5 / 6 : ℝ) * (gaussianSeededSharpCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianSeededTunedAnchor, gaussianSeededSharpCutoff, Bool.false_eq_true,
        ite_false, ite_true, Nat.cast_ofNat]
  have h2 :=
    (Real.le_sqrt (sq_nonneg (gaussianSeededTunedAnchor f)) h0).mpr (by nlinarith only [h4])
  exact ((Real.le_sqrt ha (Real.sqrt_nonneg _)).mpr h2).trans (le_max_left _ _)

/-- Both tuned clipped roots retain the common lower anchor thirteen. -/
theorem gaussianSeededTuned_root13 (f : Bool) (L : ℝ) : (13 : ℝ) ≤ gaussianSeededTunedRoot f L := by
  have ha : (13 : ℝ) ≤ gaussianSeededTunedAnchor f := by
    cases f <;> norm_num only [gaussianSeededTunedAnchor, Bool.false_eq_true, ite_false, ite_true]
  exact ha.trans (gaussianSeededTuned_root_anchor f L)

/-- Each tuned cutoff retains its unchanged actual prefix cutoff, independently of scale. -/
theorem gaussianSeededTuned_cutoff_le (f : Bool) (L : ℝ) :
    (gaussianSeededSharpCutoff f : ℝ) ≤ gaussianSeededTunedBound f L := by
  rw [gaussianSeededTuned_bound_shift]
  exact gaussianSeededSharp_cutoff_le f _

/-- Both tuned radii retain the common lower bound 170 for the index-four estimate. -/
theorem gaussianSeededTuned_radius170 (f : Bool) (L : ℝ) :
    (170 : ℝ) ≤ gaussianSeededTunedRadius f L := by
  simp only [gaussianSeededTunedRadius, gaussianSeededTuned_root_shift]
  exact gaussianSeededSharp_radius_large f _

/-- At nonnegative scale, the clipped root satisfies the tuned quadratic budget.
Increasing the raw root to the fixed prefix floor preserves the required inequality. -/
theorem gaussianSeededTuned_budget (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianSeededTunedRoot f L +
        gaussianSeededTunedConstant f ≤
      gaussianMRRefinedD * gaussianSeededTunedRadius f L := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + gaussianSeededTunedConstant f := by
    have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
    have hD : 0 ≤ gaussianSeededTunedConstant f := by
      cases f <;>
        norm_num only [gaussianSeededTunedConstant, Bool.false_eq_true, ite_false, ite_true]
    exact add_nonneg (mul_nonneg hc hL) hD
  have hd :=
    mul_le_mul_of_nonneg_left (gaussianSeededTuned_root13 f L) gaussianMRRefined_coefficients.1.le
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * gaussianSeededTunedRoot f L := by
    norm_num only [gaussianMRRefinedBeta, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint] at hd ⊢
    linarith only [hd]
  have he :=
    gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 hC
      hcoef (le_max_right _ _)
  change _ ≤ gaussianMRRefinedD * gaussianSeededTunedRadius f L at he
  linarith only [he]

/-- The stronger cutoff floors certify the continuous tail allowances 0.1464 and 0.1197.
Pass their rational anchors and power checks to the existing generic real-power tail theorem. -/
theorem gaussianSeededTuned_tail (f : Bool) (L : ℝ) :
    (473 / 10 : ℝ) * (gaussianSeededTunedRadius f L ^ 2) ^ (-9 / 16 : ℝ) +
        (512 / 27 : ℝ) / gaussianSeededTunedRadius f L ^ 2 ≤
      gaussianSeededTunedTail f := by
  have ha := gaussianSeededTuned_root_anchor f L
  have hu : 0 ≤ gaussianSeededTunedAnchor f := by
    cases f <;> norm_num only [gaussianSeededTunedAnchor, Bool.false_eq_true, ite_false, ite_true]
  have hr := (sq_le_sq₀ hu (gaussianSeededTuned_root_pos f L).le).mpr ha
  have hup : 0 < gaussianSeededTunedAnchor f := by
    cases f <;> norm_num only [gaussianSeededTunedAnchor, Bool.false_eq_true, ite_false, ite_true]
  apply
    gaussianLow_tail (R0 := gaussianSeededTunedAnchor f ^ 2) (q :=
      if f then 243 / 125 else 1901 / 1000) (sq_pos_of_pos hup) hr
  · cases f <;> norm_num only [Bool.false_eq_true, ite_false, ite_true]
  · cases f <;> norm_num only [gaussianSeededTunedAnchor, Bool.false_eq_true, ite_false, ite_true]
  · cases f <;>
      norm_num only [gaussianSeededTunedAnchor, gaussianSeededTunedTail, Bool.false_eq_true,
        ite_false, ite_true]

/-- Exact rational checks certify both signed inverse-pair conditions and strict tuned residual
  caps. -/
theorem gaussianSeededTuned_residual_checks (f : Bool) :
    let eta := gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)
    0 ≤
        gaussian1000ResidualA eta * gaussianSeededTunedAnchor f +
          gaussianLowResidualV eta (gaussianSeededTunedConstant f) ∧
      0 ≤
        gaussian1000ResidualA eta * gaussianSeededTunedAnchor f +
          2 * gaussianLowResidualV eta (gaussianSeededTunedConstant f) ∧
      (12871 / 1000 : ℝ) - 2 * gaussianSeededTunedPrefix f +
          7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA eta / gaussianSeededTunedAnchor f +
          gaussianLowResidualV eta (gaussianSeededTunedConstant f) /
            gaussianSeededTunedAnchor f ^ 2 +
          13 / (gaussianMR6FifthsIndex - 1) +
          gaussianSeededTunedTail f <
        gaussianSeededTunedConstant f := by
  cases f <;>
    norm_num only [gaussianSeededTunedAnchor, gaussianSeededTunedConstant,
      gaussianSeededTunedPrefix, gaussianSeededTunedTail, gaussian1000ResidualA,
      gaussianLowResidualV, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMRRefinedConductor, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, Bool.false_eq_true, ite_false, ite_true, and_self]

/-- For every index at least one billion, the actual normalized prefix error is below the tuned
  residual.
Apply the generic signed error and index comparison with the actual profile prefix and floor tail.
-/
theorem gaussianSeededTuned_residual (f : Bool) {L m : ℝ} {q : ℕ} (hL : 0 ≤ L)
    (hm : gaussianMR6FifthsIndex ≤ m) (hq : Real.log q ≤ L) :
    let s := gaussianSeededTunedRoot f L
    let r := gaussianSeededTunedRadius f L
    (m / (m - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (gaussianSeededTunedPrefix f) q (r ^ 2) <
      gaussianSeededTunedConstant f := by
  intro s r
  have hu : 0 < gaussianSeededTunedAnchor f := by
    cases f <;> norm_num only [gaussianSeededTunedAnchor, Bool.false_eq_true, ite_false, ite_true]
  have hc := gaussianSeededTuned_residual_checks f
  have he :=
    gaussianLow_error_cap hu (gaussianSeededTuned_root_anchor f L) (gaussianSeededTuned_budget f hL)
      hq hc.1 hc.2.1 (gaussianSeededTuned_tail f L) hc.2.2
  exact
    gaussianLow_index_error (gaussianSeededTuned_root_pos f L)
      (sq_pos_of_pos (gaussianSeededTuned_root_pos f L)) hm he

/-- For any budget with root at least thirteen, radius at least 170 and the stated weak prefix,
the normalized index-four error is below eleven. Retain the signed pole savings and old common
  tail. -/
theorem seededBudget_four_error {L s r P D : ℝ} {q : ℕ} (h13 : 13 ≤ s) (hr170 : 170 ≤ r)
    (hreq : r = s ^ 2)
    (hG : gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * r)
    (hD : 1343 / 250 ≤ D) (hP : 480743 / 100000 ≤ P) (hq : Real.log q ≤ L) :
    (4 / 3 : ℝ) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError P q (r ^ 2) <
      11 := by
  have hs : 0 < s := by linarith only [h13]
  have hr : 0 < r := by linarith only [hr170]
  have hpole := gaussianBudget_pole_bound hr hreq hG
  have hqmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
  have hqDiv := div_le_div_of_nonneg_right hqmul hr.le
  have hqPole :=
    mul_le_mul_of_nonneg_left (add_le_add hqDiv (le_refl (4 / r)))
      (by norm_num only [gaussianMR6FifthsEndpoint] : (0 : ℝ) ≤ gaussianMR6FifthsEndpoint)
  have hneg : gaussianMR6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor)) ≤ 0 := by
    norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor]
    linarith only [hD]
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
  have hcap :
    (4 / 3 : ℝ) *
              (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * 13) +
                1839 * gaussianMR6FifthsEndpoint / (1000 * 170)) +
            13 / 3 +
            12871 / 1000 -
          2 * (480743 / 100000) +
        148 / 1000 +
        7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) <
      11 := by
    norm_num only [gaussianMR6FifthsEndpoint, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMRRefinedConductor, gaussianMRRefinedWidth]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hr.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hPcap hS hR hcap ⊢
  linarith only [hPcap, hS, hR, htail.1, htail.2, hP, hcap]

/-- For any root at least thirteen and residual at least 5.372, the index-four main margin exceeds
  eleven.
Factor its increase from the anchor and verify the rational anchor value. -/
theorem seededBudget_four_main {s D : ℝ} (h13 : 13 ≤ s) (hD : 1343 / 250 ≤ D) :
    (11 : ℝ) <
      (gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD) * s ^ 2 -
          (gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta) * s +
        (2 / 3) * D := by
  let a := gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD
  let b := gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta
  have ha : 0 < a := by
    norm_num only [a, gaussianMRRefinedTripleD, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hab : 0 < 26 * a - b := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hp :=
    mul_nonneg (sub_nonneg.mpr h13) (by nlinarith only [ha, hab, h13] : 0 ≤ a * (s + 13) - b)
  have hbase : (11 : ℝ) < a * 13 ^ 2 - b * 13 + (2 / 3) * (1343 / 250) := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  change (11 : ℝ) < a * s ^ 2 - b * s + (2 / 3) * D
  nlinarith only [hp, hD, hbase]

/-- Both tuned profiles satisfy the generic normalized index-four error cap at nonnegative scale. -/
theorem gaussianSeededTuned_four_error (f : Bool) {L : ℝ} {q : ℕ} (hL : 0 ≤ L)
    (hq : Real.log q ≤ L) :
    let s := gaussianSeededTunedRoot f L
    let r := gaussianSeededTunedRadius f L
    (4 / 3 : ℝ) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (gaussianSeededTunedPrefix f) q (r ^ 2) <
      11 := by
  have hD : (1343 / 250 : ℝ) ≤ gaussianSeededTunedConstant f := by
    cases f <;> norm_num only [gaussianSeededTunedConstant, Bool.false_eq_true, ite_false, ite_true]
  have hP : (480743 / 100000 : ℝ) ≤ gaussianSeededTunedPrefix f := by
    cases f <;> norm_num only [gaussianSeededTunedPrefix, Bool.false_eq_true, ite_false, ite_true]
  exact
    seededBudget_four_error (gaussianSeededTuned_root13 f L) (gaussianSeededTuned_radius170 f L) rfl
      (gaussianSeededTuned_budget f hL) hD hP hq

/-- The clipped tuned budget and generic main margin contradict the normalized index-four
  comparison. -/
theorem gaussianSeededTuned_four_absurd (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    ¬(gaussianMRRefinedTripleD * gaussianSeededTunedRadius f L ≤
        (2 / 3 : ℝ) * gaussianMRRefinedConductor * L +
          gaussianMRRefinedTripleBeta * gaussianSeededTunedRoot f L +
          11) := by
  intro hb
  have hD : (1343 / 250 : ℝ) ≤ gaussianSeededTunedConstant f := by
    cases f <;> norm_num only [gaussianSeededTunedConstant, Bool.false_eq_true, ite_false, ite_true]
  have hm := seededBudget_four_main (gaussianSeededTuned_root13 f L) hD
  have hG := gaussianSeededTuned_budget f hL
  change
    _ <
      (gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD) * gaussianSeededTunedRadius f L -
          (gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta) *
            gaussianSeededTunedRoot f L +
        (2 / 3) * gaussianSeededTunedConstant f at hm
  nlinarith only [hb, hG, hm]

/-- Above scale 63, the tuned radius exceeds five eighths of the scale.
Use the positive residual and the strict conductor-to-mass coefficient comparison. -/
theorem gaussianSeededTuned_radius_linear {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianSeededTunedRadius f L := by
  have hG := gaussianSeededTuned_budget f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (gaussianSeededTuned_root_pos f L)
  have hD :=
    (by
      cases f <;>
        norm_num only [gaussianSeededTunedConstant, Bool.false_eq_true, ite_false, ite_true] :
      (0 : ℝ) < gaussianSeededTunedConstant f)
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  nlinarith only [hG, hp, hD, hm, hd]

/-- Above scale 63, each tuned cutoff exceeds (15/32) times the scale squared.
Square the positive radius lower bound for the local and high-domain comparisons. -/
theorem gaussianSeededTuned_bound_lower {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianSeededTunedBound f L := by
  have hr := gaussianSeededTuned_radius_linear (f := f) hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianSeededTunedRadius f L ^ 2
  nlinarith only [hs]

end PseudoPrime.Analysis
