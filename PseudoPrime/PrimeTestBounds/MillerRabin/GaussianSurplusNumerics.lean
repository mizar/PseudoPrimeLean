/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTunedProfiles

/-! # Scalar certificates for the stronger thousand-term Gaussian MR candidate

The selected floor, residual, prefix credit and scaled index-four threshold belong to this MR
application. This leaf keeps the new choices separate from the existing four-profile family.
Changing its certificates does not modify the established finite prefix data or old candidates.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A real threshold can replace the old fixed index-four residual allowance.
Input: a positive anchor, the quadratic budget, signed inverse-pair checks and a tail bound.
Claim: the scaled prefix error is strictly below the supplied threshold.
Proof: the same pole and inverse-pair comparison, retaining the threshold as a parameter.
Role: support the surplus candidate at threshold 37 while preserving the old 204/5 API. -/
theorem gaussianLow_four_error_threshold {L s P D u T K : ℝ} (hu : 0 < u) (hs : u ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * s ^ 2)
    (h1 : 0 ≤ gaussianLowFourA * u + gaussianLowFourV D)
    (h2 : 0 ≤ gaussianLowFourA * u + 2 * gaussianLowFourV D)
    (hstrict :
      3 * ((12871 / 1000 : ℝ) - 2 * P) +
          (3 / (7559 / 10000)) *
            (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
          13 +
          3 * T +
          gaussianLowFourA / u +
          gaussianLowFourV D / u ^ 2 <
        K)
    (htail :
      (473 / 10 : ℝ) * (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) +
          (512 / 27 : ℝ) / ((7559 / 10000 : ℝ) * s ^ 2) ^ 2 ≤
        T)
    {n : ℕ} (hn : Real.log n ≤ L) :
    let r := s ^ 2
    4 *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * (7559 / 10000) * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError P n (((7559 / 10000 : ℝ) * r) ^ 2) <
      K := by
  intro r
  have hspos : 0 < s := hu.trans_le hs
  have hrpos : 0 < r := sq_pos_of_pos hspos
  have hscaledpos : 0 ≤ (7559 / 10000 : ℝ) * r := mul_nonneg (by norm_num only) hrpos.le
  have hpole := gaussianBudget_pole_bound hrpos (show r = s ^ 2 from rfl) hG
  have hqPole :
    gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤
      gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply mul_le_mul_of_nonneg_left
    · apply div_le_div_of_nonneg_right
      · have hh := mul_le_mul_of_nonneg_left hn (by norm_num only : (0 : ℝ) ≤ 7 / 6)
        linarith only [hh]
      · exact hrpos.le
    · norm_num only [gaussian6FifthsEndpoint]
  have hinverse := inverse_pair_le_anchor hu hs h1 h2
  have hid :
    4 *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * (7559 / 10000) * r)) +
        (3 / (7559 / 10000)) *
          (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
              (7 * gaussian6FifthsEndpoint * gaussianMRRefinedBeta /
                  (6 * gaussianMRRefinedConductor)) /
                s +
            (gaussian6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))) / s ^ 2) =
      (3 / (7559 / 10000)) *
          (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
        gaussianLowFourA / s +
        gaussianLowFourV D / s ^ 2 := by
    dsimp only [gaussianLowFourA, gaussianLowFourV, r]
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  have hpoleEq :
    3 * (gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / ((7559 / 10000 : ℝ) * r))) =
      (3 / (7559 / 10000)) * (gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / r)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hscaledpos]
  dsimp only [gaussian6FifthsEndpoint] at hpole hqPole hid hstrict hpoleEq ⊢
  linarith only [hpole, hqPole, htail, hid, hinverse, hstrict, hpoleEq]

/-- The stronger Gaussian candidate uses the existing floor 9.1 and residual 7.6.
Input: the ambient logarithmic scale. Output: the floored quadratic budget root.
Role: select one new thousand-term candidate without changing the old four profiles. -/
noncomputable def gaussianSurplusRoot (L : ℝ) : ℝ :=
  gaussianLowRoot (91 / 10) (38 / 5) L

/-- The comparison radius is the square of the stronger candidate's budget root.
Input: the ambient logarithmic scale. Output: a nonnegative radius for relative comparison.
Role: use the same radius in the large-index and scaled index-four branches. -/
noncomputable def gaussianSurplusRadius (L : ℝ) : ℝ :=
  gaussianSurplusRoot L ^ 2

/-- Six fifths of the squared comparison radius bounds an MR rejecting prime.
Input: the ambient logarithmic scale. Output: the candidate real witness cutoff.
Role: expose one stronger Gaussian candidate for a guarded public minimum. -/
noncomputable def gaussianSurplusBound (L : ℝ) : ℝ :=
  gaussianLowBound (91 / 10) (38 / 5) L

/-- The actual thousand-term Gaussian prefix credit from the moment and finite surplus.
Input: none. Output: the exact rational lower bound 4.342585.
Role: keep every numerical check and actual-prefix consumer on the same value. -/
noncomputable def gaussianSurplusPrefix : ℝ :=
  868517 / 200000

/-- The new root retains the existing 9.1 floor at every scale.
Input: any real logarithmic scale. Claim: the floor is below the candidate root.
Proof: select the left maximum. Role: reuse the established large-index and scaled tail caps. -/
theorem gaussianSurplus_root_floor (L : ℝ) : (91 / 10 : ℝ) ≤ gaussianSurplusRoot L := by
  exact le_max_left _ _

/-- Above the unchanged floor, the scaled index-four main term exceeds 37.
Input: a real root at least 9.1. Claim: the exact main quadratic exceeds the new threshold.
Proof: rational coefficient evaluation and the squared difference from the floor.
Role: close the new scaled index-four branch on the full half-line. -/
theorem gaussianSurplus_four_margin {s : ℝ} (hs : 91 / 10 ≤ s) :
    (37 : ℝ) <
      ((7559 / 10000 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          (4 * ((7559 / 10000 : ℝ) * (81470555 / 100000000) * (2 / 5) + 1 / (10 * (2 / 5))) -
              2 * gaussianMRRefinedBeta) *
            s +
        2 * (38 / 5) := by
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussian6FifthsIndex, gaussian6FifthsEndpoint, gaussianMRRefinedWidth]
  nlinarith only [hs, sq_nonneg (s - (91 / 10))]

/-- The new floored root satisfies its exact large-index quadratic budget.
Input: a nonnegative logarithmic scale. Claim: the conductor, width and residual costs fit.
Proof: specialize the established floor-budget theorem at floor 9.1 and residual 7.6.
Role: share one budget between all actual MR witness branches. -/
theorem gaussianSurplus_budget {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianSurplusRoot L + 38 / 5 ≤
      gaussianMRRefinedD * gaussianSurplusRadius L := by
  exact
    gaussianLow_budget (by norm_num only : (9 : ℝ) ≤ 91 / 10) (by norm_num only : (0 : ℝ) ≤ 38 / 5)
      hL

/-- The actual scaled index-four error is below 37 at the unchanged floor.
Input: the quadratic budget, a root at least 9.1, and an upper logarithmic scale.
Claim: the prefix residual is below the new strict threshold on the entire half-line.
Proof: rational anchor checks and the existing low-profile tail certificate.
Role: close the scaled index-four branch with the stronger actual prefix. -/
theorem gaussianSurplus_four_error {L s : ℝ} {q : ℕ} (hs : (91 / 10 : ℝ) ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 38 / 5 ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) :
    4 *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * (7559 / 10000) * s ^ 2)) +
        13 +
        3 *
          LLS.PaperStatements.gaussianPrefixError gaussianSurplusPrefix q
            (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) <
      37 := by
  apply gaussianLow_four_error_threshold (u := 91 / 10) (T := 458 / 1000) (by norm_num only) hs hG
  · norm_num only [gaussianLowFourA, gaussianLowFourV, gaussian6FifthsEndpoint, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex,
      gaussianMRRefinedConductor]
  · norm_num only [gaussianLowFourA, gaussianLowFourV, gaussian6FifthsEndpoint, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex,
      gaussianMRRefinedConductor]
  · norm_num only [gaussianSurplusPrefix, gaussianLowFourA, gaussianLowFourV,
      gaussian6FifthsEndpoint, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussianMRRefinedConductor]
  · exact GaussianTunedProfile.low.four_tail_bound hs
  · exact hq

/-- The actual large-index residual fits allowance 7.6 at the unchanged floor.
Input: the quadratic budget, a root at least 9.1, and an upper logarithmic scale.
Claim: the normalized large-index error is strictly below the residual allowance.
Proof: signed inverse-pair anchor checks and the existing low-profile tail bound.
Role: close all large subgroup indices using the stronger actual prefix. -/
theorem gaussianSurplus_large_cap {L s : ℝ} {q : ℕ} (hs : (91 / 10 : ℝ) ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 38 / 5 ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) :
    (gaussian6FifthsIndex / (gaussian6FifthsIndex - 1)) *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * s ^ 2)) +
        13 / (gaussian6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError gaussianSurplusPrefix q ((s ^ 2) ^ 2) <
      38 / 5 := by
  apply
    gaussianLow_error_cap (u := 91 / 10) (P := gaussianSurplusPrefix) (T := 333 / 1000)
      (by norm_num only) hs hG hq
  · norm_num only [gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMRRefinedConductor, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
  · norm_num only [gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMRRefinedConductor, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
  · exact GaussianTunedProfile.low.tail_bound hs
  · norm_num only [gaussianSurplusPrefix, gaussian1000ResidualA, gaussianLowResidualV,
      gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMRRefinedConductor, gaussian6FifthsIndex, gaussian6FifthsEndpoint]

/-- The retained positive floor makes the stronger budget root positive at every scale.
Input: any real logarithmic scale. Claim: strict positivity of the root.
Proof: compare with 9.1. Role: justify division and monotone squaring in actual witness branches. -/
theorem gaussianSurplus_root_pos (L : ℝ) : 0 < gaussianSurplusRoot L := by
  exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 91 / 10) (gaussianSurplus_root_floor L)

/-- The new comparison radius retains the old squared floor.
Input: any real logarithmic scale. Claim: the radius is at least the square of 9.1.
Proof: square the nonnegative root comparison.
Role: reuse all existing tail and cutoff size certificates. -/
theorem gaussianSurplus_radius_floor (L : ℝ) : (91 / 10 : ℝ) ^ 2 ≤ gaussianSurplusRadius L := by
  exact
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 91 / 10) (gaussianSurplus_root_pos L).le).mpr
      (gaussianSurplus_root_floor L)

/-- The new cutoff retains the existing six-fifths floor cutoff.
Input: any real logarithmic scale. Claim: its cutoff is at least the old floor cutoff.
Proof: square the radius-floor bound and multiply by a nonnegative constant.
Role: justify use of the thousand-term prefix and all local fixed caps. -/
theorem gaussianSurplus_cutoff_floor (L : ℝ) :
    (6 / 5 : ℝ) * ((91 / 10) ^ 2) ^ 2 ≤ gaussianSurplusBound L := by
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (91 / 10) ^ 2) (sq_nonneg (gaussianSurplusRoot L))).mpr
      (gaussianSurplus_radius_floor L)
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- At nonnegative logarithmic scales, the new radius exceeds five eighths of the scale.
Input: a nonnegative real scale. Claim: the linear lower bound for the comparison radius.
Proof: the exact quadratic budget and the positive floor.
Role: retain the existing local-subgroup domination estimate. -/
theorem gaussianSurplus_radius_linear {L : ℝ} (hL : 0 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianSurplusRadius L := by
  have hG := gaussianSurplus_budget hL
  have hs := gaussianSurplus_root_floor L
  dsimp only [gaussianSurplusRadius] at hG ⊢
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint,
    gaussianMRRefinedConductor] at hG
  nlinarith only [hG, hs, hL]

/-- The new witness cutoff exceeds fifteen thirty-seconds of logarithmic scale squared.
Input: a nonnegative logarithmic scale. Claim: the quadratic lower bound on the cutoff.
Proof: square the positive linear radius comparison and use the six-fifths multiplier.
Role: dominate the inherited local-subgroup bound without changing its hypotheses. -/
theorem gaussianSurplus_bound_lower {L : ℝ} (hL : 0 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianSurplusBound L := by
  have hr := gaussianSurplus_radius_linear hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 8) hL
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianSurplusRadius L ^ 2
  nlinarith only [hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
