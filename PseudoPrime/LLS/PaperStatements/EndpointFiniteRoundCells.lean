/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointFiniteProfiles
public import PseudoPrime.LLS.EndpointPointwiseGrowth

/-! # Four continuous strict rounding cells for the finite principal profiles -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The four cells where the current rounded cutoff is above a new finite profile. -/
inductive FiniteRoundCell
  | p61
  | p67
  | p71
  | p73
  deriving DecidableEq

namespace FiniteRoundCell

/-- The new finite principal profile associated to the cell. -/
def profile : FiniteRoundCell → Analysis.FinitePrimeProfile
  | .p61 => .p61
  | .p67 => .p67
  | .p71 => .p71
  | .p73 => .p73

/-- The closed lower logarithmic endpoint of the strict rounding cell. -/
def left : FiniteRoundCell → ℚ
  | .p61 => 288 / 25
  | .p67 => 59 / 5
  | .p71 => 597 / 50
  | .p73 => 247 / 20

/-- A rational test radius strictly above the square root of the next prime. -/
def radius : FiniteRoundCell → ℚ
  | .p61 => 4093 / 500
  | .p67 => 8427 / 1000
  | .p71 => 1709 / 200
  | .p73 => 8889 / 1000

/-- A certified lower logarithm endpoint for the test radius. -/
def logLo : FiniteRoundCell → ℚ
  | .p61 => 2102425 / 1000000
  | .p67 => 2131440 / 1000000
  | .p71 => 2145346 / 1000000
  | .p73 => 2184814 / 1000000

/-- A certified upper logarithm endpoint for the test radius. -/
def logHi : FiniteRoundCell → ℚ
  | .p61 => 2102426 / 1000000
  | .p67 => 2131441 / 1000000
  | .p71 => 2145347 / 1000000
  | .p73 => 2184815 / 1000000

end FiniteRoundCell

/-- Taylor-eight certificates enclose the logarithm at all four test radii. -/
theorem finiteRound_log_bounds (c : FiniteRoundCell) :
    (c.logLo : ℝ) ≤ Real.log (c.radius : ℝ) ∧ Real.log (c.radius : ℝ) ≤ (c.logHi : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck c.radius 3 8 c.logLo c.logHi = true := by
    cases c <;> decide +kernel
  exact Analysis.rationalLogIntervalCheck_sound hc

/-- The test radii lie above eight and strictly above the next-prime square roots. -/
theorem finiteRound_radius_bounds (c : FiniteRoundCell) :
    (8 : ℝ) < c.radius ∧ (c.profile.nextPrime : ℝ) < (c.radius : ℝ) ^ 2 := by
  cases c <;>
    norm_num only [FiniteRoundCell.radius, FiniteRoundCell.profile,
      Analysis.FinitePrimeProfile.nextPrime, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, and_self]

/-- At the test radii, the current gap quadratic increases in its nonnegative log argument. -/
theorem finiteRound_coefficients (c : FiniteRoundCell) :
    0 ≤ lowPrimeA c.radius ∧ 0 ≤ lowPrimeB c.left c.radius := by
  cases c <;>
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, FiniteRoundCell.radius, FiniteRoundCell.left,
      Rat.cast_div, Rat.cast_ofNat, and_self]

/-- Every rational upper-log anchor of the old gap is strictly negative. -/
theorem finiteRound_anchor (c : FiniteRoundCell) :
    endpointPointwiseGap c.left (2096 / 1831) c.radius c.logHi < 0 := by
  cases c <;>
    norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, FiniteRoundCell.left, FiniteRoundCell.radius,
      FiniteRoundCell.logHi, Rat.cast_div, Rat.cast_ofNat]

/-- The actual logarithm also makes the old gap strictly negative at the cell entrance. -/
theorem finiteRound_negative (c : FiniteRoundCell) :
    endpointPointwiseGap c.left (2096 / 1831) c.radius (Real.log c.radius) < 0 := by
  have hr := finiteRound_radius_bounds c
  have hy : (c.radius : ℝ) ≠ 0 := ne_of_gt (by linarith only [hr.1])
  have hz : 0 ≤ Real.log (c.radius : ℝ) := Real.log_nonneg (by linarith only [hr.1])
  have hu := (finiteRound_log_bounds c).2
  have hs := (sq_le_sq₀ hz (hz.trans hu)).mpr hu
  have ha := (finiteRound_coefficients c).1
  have hb := (finiteRound_coefficients c).2
  have hg := finiteRound_anchor c
  rw [lowPrime_gap_quad hy] at hg ⊢
  nlinarith only [hg, mul_le_mul_of_nonneg_left hs ha, mul_le_mul_of_nonneg_left hu hb]

/-- On each closed cell and every higher level, the old pointwise cutoff exceeds the next prime. -/
theorem finiteRound_pointwise_lower (c : FiniteRoundCell) {L : ℝ} (hL : c.left ≤ L) :
    (c.profile.nextPrime : ℝ) < pointwiseCutoff L := by
  have hr := finiteRound_radius_bounds c
  have hg := finiteRound_negative c
  have hy : (8 : ℝ) ≤ c.radius := hr.1.le
  rw [pointwiseGap_eq hy] at hg
  have hd := fullEndpointEvenGapDenominator_pos hy
  have hleft : pointwiseLevel c.radius < L := by
    dsimp only [pointwiseLevel]
    nlinarith only [hg, hd, hL]
  have hs := pointwiseRadius_spec L
  have hrad : (c.radius : ℝ) < pointwiseRadius L := by
    by_contra hn
    have hm := pointwiseLevel_strictMonoOn.monotoneOn hs.1 hy (le_of_not_gt hn)
    exact not_lt.mpr (hs.2.1.trans hm) hleft
  have hsq :=
    (sq_lt_sq₀ (by linarith only [hr.1] : (0 : ℝ) ≤ c.radius)
          (by linarith only [hs.1] : (0 : ℝ) ≤ pointwiseRadius L)).mpr
      hrad
  dsimp only [pointwiseCutoff]
  exact hr.2.trans hsq

end PseudoPrime.LLS.PaperStatements
