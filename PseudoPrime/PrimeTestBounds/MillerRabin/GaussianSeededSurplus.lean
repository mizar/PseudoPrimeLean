/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLowFloorNumerics

/-! # Surplus seeded roots and floor-derived error certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The surplus residual is 4.185 for the 35000 profile and 3.934 for 50000. -/
noncomputable def gaussianSeededSurplusConstant (f : Bool) : ℝ :=
  if f then 1967 / 500 else 837 / 200

/-- The actual Gaussian prefix credit is 5.54117 or 5.645295 for the respective cutoff. -/
noncomputable def gaussianSeededSurplusPrefix (f : Bool) : ℝ :=
  if f then 1129059 / 200000 else 554117 / 100000

/-- The rational root anchor is 13.068 or 14.287, derived from the unchanged cutoff floor. -/
noncomputable def gaussianSeededSurplusAnchor (f : Bool) : ℝ :=
  if f then 14287 / 1000 else 3267 / 250

/-- The floor-derived tail allowance is 0.1464 or 0.1197 for the respective profile. -/
noncomputable def gaussianSeededSurplusTail (f : Bool) : ℝ :=
  if f then 1197 / 10000 else 183 / 1250

/-- Each profile has its own exact displacement from the current sharp residual.
The 35000 and 50000 displacements differ; no common family displacement is defined. -/
noncomputable def gaussianSeededSurplusShift (f : Bool) : ℝ :=
  if f then 73800000 / 20115621 else 72250000 / 20115621

/-- The positive quadratic budget root with the surplus residual
and existing common coefficients. -/
noncomputable def gaussianSeededSurplusRawRoot (f : Bool) (L : ℝ) : ℝ :=
  Analysis.gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
    (gaussianMRRefinedConductor * L + gaussianSeededSurplusConstant f)

/-- Clip the surplus raw root at the unchanged fourth-root prefix floor.
This retains the actual certified prefix at every scale. -/
noncomputable def gaussianSeededSurplusRoot (f : Bool) (L : ℝ) : ℝ :=
  max (Real.sqrt (Real.sqrt ((5 / 6 : ℝ) * (gaussianSeededSharpCutoff f : ℝ))))
    (gaussianSeededSurplusRawRoot f L)

/-- The square of the clipped root is the Mellin radius; its square is the scale. -/
noncomputable def gaussianSeededSurplusRadius (f : Bool) (L : ℝ) : ℝ :=
  gaussianSeededSurplusRoot f L ^ 2

/-- The prime-witness cutoff is six fifths of the squared Mellin radius. -/
noncomputable def gaussianSeededSurplusBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianSeededSurplusRadius f L ^ 2

/-- Each surplus residual equals its current sharp residual minus conductor times its own shift. -/
theorem gaussianSeededSurplus_constant_shift (f : Bool) :
    gaussianSeededSurplusConstant f =
      gaussianSeededSharpConstant f -
        gaussianMRRefinedConductor * gaussianSeededSurplusShift f := by
  cases f <;>
    norm_num only [gaussianSeededSurplusConstant, gaussianSeededSharpConstant,
      gaussianMRRefinedConductor, gaussianSeededSurplusShift, Bool.false_eq_true, ite_false,
      ite_true]

/-- For numerical comparison, each surplus raw root is its current raw root at the displaced scale.
This equality does not change the input of any actual witness theorem. -/
theorem gaussianSeededSurplus_raw_shift (f : Bool) (L : ℝ) :
    gaussianSeededSurplusRawRoot f L =
      gaussianSeededSharpRawRoot f (L - gaussianSeededSurplusShift f) := by
  have he :
    gaussianMRRefinedConductor * L + gaussianSeededSurplusConstant f =
      gaussianMRRefinedConductor * (L - gaussianSeededSurplusShift f) +
        gaussianSeededSharpConstant f := by
    rw [gaussianSeededSurplus_constant_shift]
    ring
  rw [gaussianSeededSurplusRawRoot, Analysis.gaussianBudgetRoot, gaussianSeededSharpRawRoot, he]

/-- The clipped roots inherit the same profile-specific numerical displacement. -/
theorem gaussianSeededSurplus_root_shift (f : Bool) (L : ℝ) :
    gaussianSeededSurplusRoot f L =
      gaussianSeededSharpRoot f (L - gaussianSeededSurplusShift f) := by
  rw [gaussianSeededSurplusRoot, gaussianSeededSharpRoot, gaussianSeededSurplus_raw_shift]

/-- Each full clipped bound inherits its own numerical displacement, including the prefix floor. -/
theorem gaussianSeededSurplus_bound_shift (f : Bool) (L : ℝ) :
    gaussianSeededSurplusBound f L =
      gaussianSeededSharpBound f (L - gaussianSeededSurplusShift f) := by
  simp only [gaussianSeededSurplusBound, gaussianSeededSurplusRadius, gaussianSeededSharpBound,
    gaussianSeededSharpRadius, gaussianSeededSurplus_root_shift]

/-- The positive beta and denominator make the surplus raw root positive at every real scale. -/
theorem gaussianSeededSurplus_raw_pos (f : Bool) (L : ℝ) : 0 < gaussianSeededSurplusRawRoot f L :=
  Analysis.gaussianBudgetRoot_pos gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2

/-- The clipped root is positive because it dominates the positive raw root. -/
theorem gaussianSeededSurplus_root_pos (f : Bool) (L : ℝ) : 0 < gaussianSeededSurplusRoot f L :=
  (gaussianSeededSurplus_raw_pos f L).trans_le (le_max_right _ _)

/-- The unchanged prefix floor implies the sharper rational anchor for each root.
Compare nonnegative squares twice using exact rational fourth-power inequalities. -/
theorem gaussianSeededSurplus_root_anchor (f : Bool) (L : ℝ) :
    gaussianSeededSurplusAnchor f ≤ gaussianSeededSurplusRoot f L := by
  have h0 : 0 ≤ (5 / 6 : ℝ) * (gaussianSeededSharpCutoff f : ℝ) :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have ha : 0 ≤ gaussianSeededSurplusAnchor f := by
    cases f <;> norm_num only [gaussianSeededSurplusAnchor, Bool.false_eq_true, ite_false, ite_true]
  have h4 :
    gaussianSeededSurplusAnchor f ^ 4 ≤ (5 / 6 : ℝ) * (gaussianSeededSharpCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianSeededSurplusAnchor, gaussianSeededSharpCutoff, Bool.false_eq_true,
        ite_false, ite_true, Nat.cast_ofNat]
  have h2 :=
    (Real.le_sqrt (sq_nonneg (gaussianSeededSurplusAnchor f)) h0).mpr (by nlinarith only [h4])
  exact ((Real.le_sqrt ha (Real.sqrt_nonneg _)).mpr h2).trans (le_max_left _ _)

/-- Both surplus clipped roots retain the common lower anchor thirteen. -/
theorem gaussianSeededSurplus_root13 (f : Bool) (L : ℝ) :
    (13 : ℝ) ≤ gaussianSeededSurplusRoot f L := by
  have ha : (13 : ℝ) ≤ gaussianSeededSurplusAnchor f := by
    cases f <;> norm_num only [gaussianSeededSurplusAnchor, Bool.false_eq_true, ite_false, ite_true]
  exact ha.trans (gaussianSeededSurplus_root_anchor f L)

/-- Each surplus cutoff retains its unchanged actual prefix cutoff, independently of scale. -/
theorem gaussianSeededSurplus_cutoff_le (f : Bool) (L : ℝ) :
    (gaussianSeededSharpCutoff f : ℝ) ≤ gaussianSeededSurplusBound f L := by
  rw [gaussianSeededSurplus_bound_shift]
  exact gaussianSeededSharp_cutoff_le f _

/-- Both surplus radii retain the common lower bound 170 for the index-four estimate. -/
theorem gaussianSeededSurplus_radius170 (f : Bool) (L : ℝ) :
    (170 : ℝ) ≤ gaussianSeededSurplusRadius f L := by
  simp only [gaussianSeededSurplusRadius, gaussianSeededSurplus_root_shift]
  exact gaussianSeededSharp_radius_large f _

/-- At nonnegative scale, the clipped root satisfies the surplus quadratic budget.
Increasing the raw root to the fixed prefix floor preserves the required inequality. -/
theorem gaussianSeededSurplus_budget (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianSeededSurplusRoot f L +
        gaussianSeededSurplusConstant f ≤
      gaussianMRRefinedD * gaussianSeededSurplusRadius f L := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + gaussianSeededSurplusConstant f := by
    have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
    have hD : 0 ≤ gaussianSeededSurplusConstant f := by
      cases f <;>
        norm_num only [gaussianSeededSurplusConstant, Bool.false_eq_true, ite_false, ite_true]
    exact add_nonneg (mul_nonneg hc hL) hD
  have hd :=
    mul_le_mul_of_nonneg_left (gaussianSeededSurplus_root13 f L) gaussianMRRefined_coefficients.1.le
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * gaussianSeededSurplusRoot f L := by
    norm_num only [gaussianMRRefinedBeta, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint] at hd ⊢
    linarith only [hd]
  have he :=
    Analysis.gaussianBudget_of_root_le gaussianMRRefined_coefficients.1
      gaussianMRRefined_coefficients.2 hC hcoef (le_max_right _ _)
  change _ ≤ gaussianMRRefinedD * gaussianSeededSurplusRadius f L at he
  linarith only [he]

/-- The stronger cutoff floors certify the continuous tail allowances 0.1464 and 0.1197.
Pass their rational anchors and power checks to the existing generic real-power tail theorem. -/
theorem gaussianSeededSurplus_tail (f : Bool) (L : ℝ) :
    (473 / 10 : ℝ) * (gaussianSeededSurplusRadius f L ^ 2) ^ (-9 / 16 : ℝ) +
        (512 / 27 : ℝ) / gaussianSeededSurplusRadius f L ^ 2 ≤
      gaussianSeededSurplusTail f := by
  have ha := gaussianSeededSurplus_root_anchor f L
  have hu : 0 ≤ gaussianSeededSurplusAnchor f := by
    cases f <;> norm_num only [gaussianSeededSurplusAnchor, Bool.false_eq_true, ite_false, ite_true]
  have hr := (sq_le_sq₀ hu (gaussianSeededSurplus_root_pos f L).le).mpr ha
  have hup : 0 < gaussianSeededSurplusAnchor f := by
    cases f <;> norm_num only [gaussianSeededSurplusAnchor, Bool.false_eq_true, ite_false, ite_true]
  apply
    gaussianLow_tail (R0 := gaussianSeededSurplusAnchor f ^ 2) (q :=
      if f then 243 / 125 else 1901 / 1000) (sq_pos_of_pos hup) hr
  · cases f <;> norm_num only [Bool.false_eq_true, ite_false, ite_true]
  · cases f <;> norm_num only [gaussianSeededSurplusAnchor, Bool.false_eq_true, ite_false, ite_true]
  · cases f <;>
      norm_num only [gaussianSeededSurplusAnchor, gaussianSeededSurplusTail, Bool.false_eq_true,
        ite_false, ite_true]

/-- Exact rational checks certify both signed inverse-pair conditions and strict surplus residual
  caps. -/
theorem gaussianSeededSurplus_residual_checks (f : Bool) :
    let eta := gaussian6FifthsIndex / (gaussian6FifthsIndex - 1)
    0 ≤
        gaussian1000ResidualA eta * gaussianSeededSurplusAnchor f +
          gaussianLowResidualV eta (gaussianSeededSurplusConstant f) ∧
      0 ≤
        gaussian1000ResidualA eta * gaussianSeededSurplusAnchor f +
          2 * gaussianLowResidualV eta (gaussianSeededSurplusConstant f) ∧
      (12871 / 1000 : ℝ) - 2 * gaussianSeededSurplusPrefix f +
          7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA eta / gaussianSeededSurplusAnchor f +
          gaussianLowResidualV eta (gaussianSeededSurplusConstant f) /
            gaussianSeededSurplusAnchor f ^ 2 +
          13 / (gaussian6FifthsIndex - 1) +
          gaussianSeededSurplusTail f <
        gaussianSeededSurplusConstant f := by
  cases f <;>
    norm_num only [gaussianSeededSurplusAnchor, gaussianSeededSurplusConstant,
      gaussianSeededSurplusPrefix, gaussianSeededSurplusTail, gaussian1000ResidualA,
      gaussianLowResidualV, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMRRefinedConductor, gaussian6FifthsIndex,
      gaussian6FifthsEndpoint, Bool.false_eq_true, ite_false, ite_true, and_self]

/-- For every index at least one billion, the actual normalized prefix error is below the surplus
  residual.
Apply the generic signed error and index comparison with the actual profile prefix and floor tail.
-/
theorem gaussianSeededSurplus_residual (f : Bool) {L m : ℝ} {q : ℕ} (hL : 0 ≤ L)
    (hm : gaussian6FifthsIndex ≤ m) (hq : Real.log q ≤ L) :
    let s := gaussianSeededSurplusRoot f L
    let r := gaussianSeededSurplusRadius f L
    (m / (m - 1)) *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (gaussianSeededSurplusPrefix f) q (r ^ 2) <
      gaussianSeededSurplusConstant f := by
  intro s r
  have hu : 0 < gaussianSeededSurplusAnchor f := by
    cases f <;> norm_num only [gaussianSeededSurplusAnchor, Bool.false_eq_true, ite_false, ite_true]
  have hc := gaussianSeededSurplus_residual_checks f
  have he :=
    gaussianLow_error_cap hu (gaussianSeededSurplus_root_anchor f L)
      (gaussianSeededSurplus_budget f hL) hq hc.1 hc.2.1 (gaussianSeededSurplus_tail f L) hc.2.2
  exact
    gaussianLow_index_error (gaussianSeededSurplus_root_pos f L)
      (sq_pos_of_pos (gaussianSeededSurplus_root_pos f L)) hm he

/-- For any budget with root at least thirteen, radius at least 170 and the stated weak prefix,
the normalized index-four error is below ten. Retain the signed pole savings and old common
  tail. -/
theorem surplusBudget_four_error {L s r P D : ℝ} {q : ℕ} (h13 : 13 ≤ s) (hr170 : 170 ≤ r)
    (hreq : r = s ^ 2)
    (hG : gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * r)
    (hD : 1967 / 500 ≤ D) (hP : 277 / 50 ≤ P) (hq : Real.log q ≤ L) :
    (4 / 3 : ℝ) *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError P q (r ^ 2) <
      10 := by
  have hs : 0 < s := by linarith only [h13]
  have hr : 0 < r := by linarith only [hr170]
  have hpole := gaussianBudget_pole_bound hr hreq hG
  have hqmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
  have hqDiv := div_le_div_of_nonneg_right hqmul hr.le
  have hqPole :=
    mul_le_mul_of_nonneg_left (add_le_add hqDiv (le_refl (4 / r)))
      (by norm_num only [gaussian6FifthsEndpoint] : (0 : ℝ) ≤ gaussian6FifthsEndpoint)
  have hneg : gaussian6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor)) ≤ 0 := by
    norm_num only [gaussian6FifthsEndpoint, gaussianMRRefinedConductor]
    linarith only [hD]
  have hnegDiv := div_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg s)
  have hposDiv :
    0 ≤
      (7 * gaussian6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor)) /
        s := by
    apply div_nonneg _ hs.le
    norm_num only [gaussian6FifthsEndpoint, gaussianMRRefinedBeta, gaussianMRRefinedWidth,
      gaussianMRRefinedMass, gaussian6FifthsIndex, gaussianMRRefinedConductor]
  have hqId (t : ℝ) :
    gaussian6FifthsEndpoint * ((7 / 6) * t / r + 4 / r) =
      gaussian6FifthsEndpoint * (((7 / 6) * t + 4) / r) := by
    ring
  rw [hqId (Real.log q), hqId L] at hqPole
  have hPcap :
    gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) := by
    linarith only [hqPole, hpole, hnegDiv, hposDiv]
  have hS :=
    div_le_div_of_nonneg_left
      (by norm_num only [gaussian6FifthsEndpoint] : (0 : ℝ) ≤ 21 * gaussian6FifthsEndpoint)
      (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) < 10 * gaussianMRRefinedWidth * 13)
      (mul_le_mul_of_nonneg_left h13
        (by norm_num only [gaussianMRRefinedWidth] : (0 : ℝ) ≤ 10 * gaussianMRRefinedWidth))
  have hR :=
    div_le_div_of_nonneg_left
      (by norm_num only [gaussian6FifthsEndpoint] : (0 : ℝ) ≤ 1839 * gaussian6FifthsEndpoint)
      (by norm_num only : (0 : ℝ) < 1000 * 170)
      (mul_le_mul_of_nonneg_left hr170 (by norm_num only : (0 : ℝ) ≤ 1000))
  have htail := gaussian6_tail240 hr170
  have hcap :
    (4 / 3 : ℝ) *
              (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * 13) +
                1839 * gaussian6FifthsEndpoint / (1000 * 170)) +
            13 / 3 +
            12871 / 1000 -
          2 * (277 / 50) +
        148 / 1000 +
        7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) <
      10 := by
    norm_num only [gaussian6FifthsEndpoint, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussian6FifthsIndex, gaussianMRRefinedConductor, gaussianMRRefinedWidth]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hr.le]
  dsimp only [gaussian6FifthsEndpoint] at hPcap hS hR hcap ⊢
  linarith only [hPcap, hS, hR, htail.1, htail.2, hP, hcap]

/-- For any root at least thirteen and residual at least 3.934, the index-four main margin exceeds
  ten.
Factor its increase from the anchor and verify the rational anchor value. -/
theorem surplusBudget_four_main {s D : ℝ} (h13 : 13 ≤ s) (hD : 1967 / 500 ≤ D) :
    (10 : ℝ) <
      (gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD) * s ^ 2 -
          (gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta) * s +
        (2 / 3) * D := by
  let a := gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD
  let b := gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta
  have ha : 0 < a := by
    norm_num only [a, gaussianMRRefinedTripleD, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussian6FifthsEndpoint, gaussian6FifthsIndex]
  have hab : 0 < 26 * a - b := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsEndpoint,
      gaussian6FifthsIndex]
  have hp :=
    mul_nonneg (sub_nonneg.mpr h13) (by nlinarith only [ha, hab, h13] : 0 ≤ a * (s + 13) - b)
  have hbase : (10 : ℝ) < a * 13 ^ 2 - b * 13 + (2 / 3) * (1967 / 500) := by
    norm_num only [a, b, gaussianMRRefinedTripleD, gaussianMRRefinedTripleBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsEndpoint,
      gaussian6FifthsIndex]
  change (10 : ℝ) < a * s ^ 2 - b * s + (2 / 3) * D
  nlinarith only [hp, hD, hbase]

/-- Both surplus profiles satisfy the generic normalized index-four error cap
at nonnegative scale. -/
theorem gaussianSeededSurplus_four_error (f : Bool) {L : ℝ} {q : ℕ} (hL : 0 ≤ L)
    (hq : Real.log q ≤ L) :
    let s := gaussianSeededSurplusRoot f L
    let r := gaussianSeededSurplusRadius f L
    (4 / 3 : ℝ) *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (gaussianSeededSurplusPrefix f) q (r ^ 2) <
      10 := by
  have hD : (1967 / 500 : ℝ) ≤ gaussianSeededSurplusConstant f := by
    cases f <;>
      norm_num only [gaussianSeededSurplusConstant, Bool.false_eq_true, ite_false, ite_true]
  have hP : (277 / 50 : ℝ) ≤ gaussianSeededSurplusPrefix f := by
    cases f <;> norm_num only [gaussianSeededSurplusPrefix, Bool.false_eq_true, ite_false, ite_true]
  exact
    surplusBudget_four_error (gaussianSeededSurplus_root13 f L)
      (gaussianSeededSurplus_radius170 f L) rfl (gaussianSeededSurplus_budget f hL) hD hP hq

/-- The clipped surplus budget and generic main margin contradict the normalized index-four
  comparison. -/
theorem gaussianSeededSurplus_four_absurd (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    ¬(gaussianMRRefinedTripleD * gaussianSeededSurplusRadius f L ≤
        (2 / 3 : ℝ) * gaussianMRRefinedConductor * L +
          gaussianMRRefinedTripleBeta * gaussianSeededSurplusRoot f L +
          10) := by
  intro hb
  have hD : (1967 / 500 : ℝ) ≤ gaussianSeededSurplusConstant f := by
    cases f <;>
      norm_num only [gaussianSeededSurplusConstant, Bool.false_eq_true, ite_false, ite_true]
  have hm := surplusBudget_four_main (gaussianSeededSurplus_root13 f L) hD
  have hG := gaussianSeededSurplus_budget f hL
  change
    _ <
      (gaussianMRRefinedTripleD - (2 / 3) * gaussianMRRefinedD) * gaussianSeededSurplusRadius f L -
          (gaussianMRRefinedTripleBeta - (2 / 3) * gaussianMRRefinedBeta) *
            gaussianSeededSurplusRoot f L +
        (2 / 3) * gaussianSeededSurplusConstant f at hm
  nlinarith only [hb, hG, hm]

/-- Above scale 63, the surplus radius exceeds five eighths of the scale.
Use the positive residual and the strict conductor-to-mass coefficient comparison. -/
theorem gaussianSeededSurplus_radius_linear {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianSeededSurplusRadius f L := by
  have hG := gaussianSeededSurplus_budget f (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (gaussianSeededSurplus_root_pos f L)
  have hD :=
    (by
      cases f <;>
        norm_num only [gaussianSeededSurplusConstant, Bool.false_eq_true, ite_false, ite_true] :
      (0 : ℝ) < gaussianSeededSurplusConstant f)
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussian6FifthsEndpoint, gaussian6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  nlinarith only [hG, hp, hD, hm, hd]

/-- Above scale 63, each surplus cutoff exceeds (15/32) times the scale squared.
Square the positive radius lower bound for the local and high-domain comparisons. -/
theorem gaussianSeededSurplus_bound_lower {f : Bool} {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianSeededSurplusBound f L := by
  have hr := gaussianSeededSurplus_radius_linear (f := f) hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianSeededSurplusRadius f L ^ 2
  nlinarith only [hs]

/-- The raw surplus cutoff is six fifths of the fourth power of its positive quadratic root. -/
noncomputable def gaussianSeededSurplusRawBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * (gaussianSeededSurplusRawRoot f L ^ 2) ^ 2

/-- Both strengthened actual prefix candidates participate in the surplus family. -/
noncomputable def gaussianSeededSurplusFamily (L : ℝ) : ℝ :=
  min (gaussianSeededSurplusBound false L) (gaussianSeededSurplusBound true L)

/-- The surplus clipped cutoff equals the maximum of its unchanged prefix floor and raw curve. -/
theorem seededSurplus_eq_max (f : Bool) (L : ℝ) :
    gaussianSeededSurplusBound f L =
      max (gaussianSeededSharpCutoff f : ℝ) (gaussianSeededSurplusRawBound f L) := by
  rw [gaussianSeededSurplus_bound_shift, gaussianSeededSharp_eq_max]
  simp only [gaussianSeededSurplusRawBound, gaussianSeededSharpRawBound,
    gaussianSeededSurplus_raw_shift]

/-- Each surplus raw root is no larger than the current tuned root at every real scale.
The common mass, width and conductor coefficients leave only the residual comparison. -/
theorem seededSurplus_raw_le_tuned (f : Bool) (L : ℝ) :
    gaussianSeededSurplusRawRoot f L ≤ gaussianSeededTunedRawRoot f L := by
  have hD : gaussianSeededSurplusConstant f ≤ gaussianSeededTunedConstant f := by
    cases f <;>
      norm_num only [gaussianSeededSurplusConstant, gaussianSeededTunedConstant, Bool.false_eq_true,
        ite_false, ite_true]
  exact
    Analysis.gaussianBudgetRoot_mono gaussianMRRefined_coefficients.1
      (add_le_add (le_refl (gaussianMRRefinedConductor * L)) hD)

/-- Each surplus cutoff is globally no larger than its current tuned counterpart.
The certified prefix floor is identical, and both positive roots can be squared twice. -/
theorem seededSurplus_le_tuned (f : Bool) (L : ℝ) :
    gaussianSeededSurplusBound f L ≤ gaussianSeededTunedBound f L := by
  have hr : gaussianSeededSurplusRoot f L ≤ gaussianSeededTunedRoot f L :=
    max_le_max (le_refl _) (seededSurplus_raw_le_tuned f L)
  have h2 :=
    (sq_le_sq₀ (gaussianSeededSurplus_root_pos f L).le (gaussianSeededTuned_root_pos f L).le).mpr hr
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- The surplus family retains the smaller unchanged prefix floor at every real scale. -/
theorem seededSurplusFamily_floor (L : ℝ) : (35000 : ℝ) ≤ gaussianSeededSurplusFamily L := by
  have h0 := gaussianSeededSurplus_cutoff_le false L
  have h1 := gaussianSeededSurplus_cutoff_le true L
  norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true,
    Nat.cast_ofNat] at h0 h1
  exact le_min h0 ((by norm_num only : (35000 : ℝ) ≤ 50000).trans h1)

/-- Above the analytic entrance, both surplus candidates retain the common quadratic lower bound. -/
theorem seededSurplusFamily_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianSeededSurplusFamily L := by
  exact
    lt_min (gaussianSeededSurplus_bound_lower (f := false) hL)
      (gaussianSeededSurplus_bound_lower (f := true) hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
