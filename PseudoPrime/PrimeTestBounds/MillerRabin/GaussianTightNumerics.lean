/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusNumerics

/-! # Tighter scalar certificates for the same thousand-term Gaussian prefix

Candidate A keeps floor 9.1, prefix 4.342585 and the existing tail certificates. Its residual
is 7.2 and both sides of the scaled index-four contradiction use threshold 36.63. The old
surplus candidate remains available for exact comparisons. No finite prefix data is changed.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive Gaussian budget root clipped at the unchanged floor 9.1, with residual 7.2.
Input: real log scale L. Output: the root used by all actual branches of candidate A. -/
noncomputable def gaussianTightRoot (L : ℝ) : ℝ :=
  gaussianLowRoot (91 / 10) (36 / 5) L

/-- Square the tighter clipped root to obtain the common Mellin comparison radius.
Input: the log scale. Output: the radius whose square supplies the prime-witness cutoff. -/
noncomputable def gaussianTightRadius (L : ℝ) : ℝ :=
  gaussianTightRoot L ^ 2

/-- The tighter witness cutoff is six fifths of the squared comparison radius.
Input: real log scale. Output: candidate A, using the unchanged thousand-term prefix. -/
noncomputable def gaussianTightBound (L : ℝ) : ℝ :=
  gaussianLowBound (91 / 10) (36 / 5) L

/-- At every scale, the tighter root retains the floor 9.1.
Project the defining maximum; this preserves the established tail domain. -/
theorem gaussianTight_root_floor (L : ℝ) : (91 / 10 : ℝ) ≤ gaussianTightRoot L := by
  exact le_max_left _ _

/-- Above floor 9.1, the scaled index-four main quadratic exceeds 36.63.
Evaluate the fixed coefficients and use the squared displacement from the floor.
The residual 7.2 is charged on the same side as in the actual index-four contradiction. -/
theorem gaussianTight_four_margin {s : ℝ} (hs : 91 / 10 ≤ s) :
    (3663 / 100 : ℝ) <
      ((7559 / 10000 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          (4 * ((7559 / 10000 : ℝ) * (81470555 / 100000000) * (2 / 5) + 1 / (10 * (2 / 5))) -
              2 * gaussianMRRefinedBeta) *
            s +
        2 * (36 / 5) := by
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussian6FifthsIndex, gaussian6FifthsEndpoint, gaussianMRRefinedWidth]
  nlinarith only [hs, sq_nonneg (s - (91 / 10))]

/-- For nonnegative scales, the tighter root satisfies the large-index budget with residual 7.2.
Specialize the existing floor-budget theorem; this common budget also feeds index four. -/
theorem gaussianTight_budget {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianTightRoot L + 36 / 5 ≤
      gaussianMRRefinedD * gaussianTightRadius L := by
  exact
    gaussianLow_budget (by norm_num only : (9 : ℝ) ≤ 91 / 10) (by norm_num only : (0 : ℝ) ≤ 36 / 5)
      hL

/-- With the tighter budget and a root at least 9.1, the scaled index-four error is below 36.63.
Use the arbitrary-threshold certificate and the existing low-profile four-tail bound.
The prefix stays 4.342585 and the error threshold matches the main margin exactly. -/
theorem gaussianTight_four_error {L s : ℝ} {q : ℕ} (hs : (91 / 10 : ℝ) ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 36 / 5 ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) :
    4 *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * (7559 / 10000) * s ^ 2)) +
        13 +
        3 *
          LLS.PaperStatements.gaussianPrefixError gaussianSurplusPrefix q
            (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) <
      3663 / 100 := by
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

/-- With the tighter budget and floor 9.1, the normalized large-index error is below 7.2.
Check the signed inverse-pair anchors exactly and retain the existing low-profile tail. -/
theorem gaussianTight_large_cap {L s : ℝ} {q : ℕ} (hs : (91 / 10 : ℝ) ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 36 / 5 ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) :
    (gaussian6FifthsIndex / (gaussian6FifthsIndex - 1)) *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * s ^ 2)) +
        13 / (gaussian6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError gaussianSurplusPrefix q ((s ^ 2) ^ 2) <
      36 / 5 := by
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

/-- The fixed positive floor makes the tighter root positive at every real scale.
This justifies divisions and the monotone squaring used in actual witness branches. -/
theorem gaussianTight_root_pos (L : ℝ) : 0 < gaussianTightRoot L := by
  exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 91 / 10) (gaussianTight_root_floor L)

/-- The tighter radius is at least the square of 9.1 at every real scale.
Square the nonnegative floor comparison to preserve the established size certificates. -/
theorem gaussianTight_radius_floor (L : ℝ) : (91 / 10 : ℝ) ^ 2 ≤ gaussianTightRadius L := by
  exact
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 91 / 10) (gaussianTight_root_pos L).le).mpr
      (gaussianTight_root_floor L)

/-- The tighter cutoff retains the fixed six-fifths fourth-power floor.
Square the radius lower bound; the unchanged prefix cutoff and local fixed cap still fit. -/
theorem gaussianTight_cutoff_floor (L : ℝ) :
    (6 / 5 : ℝ) * ((91 / 10) ^ 2) ^ 2 ≤ gaussianTightBound L := by
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (91 / 10) ^ 2) (sq_nonneg (gaussianTightRoot L))).mpr
      (gaussianTight_radius_floor L)
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- At nonnegative scales, the tighter radius exceeds five eighths of the scale.
Use the exact budget and positive root floor; this preserves the local-subgroup comparison. -/
theorem gaussianTight_radius_linear {L : ℝ} (hL : 0 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianTightRadius L := by
  have hG := gaussianTight_budget hL
  have hs := gaussianTight_root_floor L
  dsimp only [gaussianTightRadius] at hG ⊢
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint,
    gaussianMRRefinedConductor] at hG
  nlinarith only [hG, hs, hL]

/-- At nonnegative scales, the tighter cutoff exceeds fifteen thirty-seconds of scale squared.
Square the positive linear radius bound; this closes the inherited local branch. -/
theorem gaussianTight_bound_lower {L : ℝ} (hL : 0 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianTightBound L := by
  have hr := gaussianTight_radius_linear hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 8) hL
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianTightRadius L ^ 2
  nlinarith only [hs]

/-- At every real scale, candidate A is no larger than the old residual-7.6 surplus candidate.
Its floor is unchanged and its smaller residual gives ordered positive roots.
Square twice to obtain global non-worsening without a GRH assumption. -/
theorem gaussianTight_le_surplus (L : ℝ) : gaussianTightBound L ≤ gaussianSurplusBound L := by
  have hraw :=
    Analysis.gaussianBudgetRoot_mono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1
      (add_le_add (le_refl (gaussianMRRefinedConductor * L))
        (by norm_num only : (36 / 5 : ℝ) ≤ 38 / 5))
  have hr : gaussianTightRoot L ≤ gaussianSurplusRoot L := max_le_max le_rfl hraw
  have hs := (sq_le_sq₀ (gaussianTight_root_pos L).le (gaussianSurplus_root_pos L).le).mpr hr
  have hs' := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_le_mul_of_nonneg_left hs' (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Candidate A is monotone on the full real scale.
Transport the budget-root order through its positive floor and square twice.
This is used only for common-scale cumulative bounds, not public-envelope monotonicity. -/
theorem gaussianTight_mono : Monotone gaussianTightBound := by
  intro L K hLK
  have hs := gaussianLow_root_mono (u := 91 / 10) (D := 36 / 5) hLK
  have hsq := (sq_le_sq₀ (gaussianTight_root_pos L).le (gaussianTight_root_pos K).le).mpr hs
  have hsq2 :=
    (sq_le_sq₀ (sq_nonneg (gaussianTightRoot L)) (sq_nonneg (gaussianTightRoot K))).mpr hsq
  exact mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

end PseudoPrime.PrimeTestBounds.MillerRabin
