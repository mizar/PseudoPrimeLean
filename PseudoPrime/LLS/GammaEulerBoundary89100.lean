/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerBoundaryCells
public import PseudoPrime.Analysis.GammaFiniteEulerBlockCombination

/-! # A compact whole-cell target-tail and Euler-prefix certificate -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: an endpoint selector and resolvent node. Definition: trillionth-grid intervals
at 89100 (false) or 89700 (true). Output: rational node bounds.
Role: keep the analytic boundary certificate to twenty grid numerators. -/
def gammaBoundary89100Ratios (right : Bool) (a : ℚ) : ℚ × ℚ :=
  let rs : List ℕ :=
    if right then [6303299, 2015063, 364225, 37222, 1216, 12, 0, 0, 0, 0]
    else [6347875, 2030676, 367416, 37599, 1230, 12, 0, 0, 0, 0]
  let r := rs[(Analysis.gammaResolventCoefficients.map Prod.fst).idxOf a]?.getD 0
  ((r : ℚ) / 1000000000000, ((r + 1 : ℕ) : ℚ) / 1000000000000)

/-- Input: a resolvent node. Definition: the right lower and left upper endpoint.
Output: a whole-cell node interval. Role: retain signs in weighted scalar sums. -/
def gammaBoundary89100CellRatios (a : ℚ) : ℚ × ℚ :=
  ((gammaBoundary89100Ratios true a).1, (gammaBoundary89100Ratios false a).2)

/-- Claim: the ten node intervals at 89100 pass all integer power checks.
Proof: exact kernel arithmetic. Role: certify the left endpoint without numerical trust. -/
theorem gamma_boundary89100_left_check :
    Analysis.gammaFiniteEulerRatioCheck 89100 (gammaBoundary89100Ratios false) = true := by
  decide +kernel

/-- Claim: the ten node intervals at 89700 pass all integer power checks.
Proof: exact kernel arithmetic. Role: certify the right endpoint for uniform cell transport. -/
theorem gamma_boundary89100_right_check :
    Analysis.gammaFiniteEulerRatioCheck 89700 (gammaBoundary89100Ratios true) = true := by
  decide +kernel

/-- Claim: the cell data meet the weight, slope and main-core scalar inequalities.
Proof: exact signed rational arithmetic. Role: supply compact whole-cell numerical constants. -/
theorem gamma_boundary89100_scalar_checks :
    0 ≤ gammaFiniteWeightedUpper (gammaTailRationalCoefficient 1) gammaBoundary89100CellRatios ∧
      (36 / 10000000 : ℚ) ≤ Analysis.gammaFiniteEulerLower gammaBoundary89100CellRatios ∧
      gammaFiniteWeightedUpper gammaSlopeRationalCoefficient gammaBoundary89100CellRatios ≤
        (-38 / 10000000 : ℚ) ∧
      (89700 : ℚ) *
          gammaFiniteWeightedUpper (gammaTailRationalCoefficient 1) gammaBoundary89100CellRatios ≤
        71 / 10 := by
  decide +kernel

/-- Input: 89100<=b<=89700. Claim: the weight is at least 36/10^7, the slope
at most -38/10^7 and main tail at most 71/10. Proof: transfer endpoint node certificates.
Role: enclose the actual real-valued boundary scalars throughout the cell. -/
theorem gamma_boundary89100_scalars {b : ℝ} (hlo : 89100 ≤ b) (hhi : b ≤ 89700) :
    (36 / 10000000 : ℝ) ≤ Analysis.gammaResolventEulerWeight b ∧
      gammaEulerLogSlope b ≤ (-38 / 10000000 : ℝ) ∧ gammaEulerTailMain b ≤ (71 / 10 : ℝ) := by
  have h :=
    gamma_boundary_scalar_bounds_on_cell gamma_boundary89100_left_check
      gamma_boundary89100_right_check
      (show ((89100 : ℚ) : ℝ) ≤ b by
        norm_num only [Rat.cast_ofNat]; exact hlo)
      (show b ≤ ((89700 : ℚ) : ℝ) by
        norm_num only [Rat.cast_ofNat]; exact hhi)
      gamma_boundary89100_scalar_checks.1
  change
    (Analysis.gammaFiniteEulerLower gammaBoundary89100CellRatios : ℝ) ≤ _ ∧
      _ ≤
        (gammaFiniteWeightedUpper gammaSlopeRationalCoefficient gammaBoundary89100CellRatios : ℝ) ∧
      _ ≤
        ((89700 : ℚ) : ℝ) *
          (gammaFiniteWeightedUpper (gammaTailRationalCoefficient 1) gammaBoundary89100CellRatios :
            ℝ) at h
  have hw := (Rat.cast_le (K := ℝ)).mpr gamma_boundary89100_scalar_checks.2.1
  have hs := (Rat.cast_le (K := ℝ)).mpr gamma_boundary89100_scalar_checks.2.2.1
  have hm := (Rat.cast_le (K := ℝ)).mpr gamma_boundary89100_scalar_checks.2.2.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_mul] at hw hs hm h ⊢
  exact ⟨hw.trans h.1, by linarith only [hs, h.2.1], by linarith only [hm, h.2.2]⟩

/-- Input: RH and 89100<=b<=89700. Claim: the actual boundary tail is at most 13/2.
Proof: combine signed node bounds and analytic psi/smoothed lower bounds.
Role: remove the target-tail hypothesis from prefix transport on this cell. -/
theorem gamma_boundary89100_upper (hRH : RiemannHypothesis) {b : ℝ} (hlo : 89100 ≤ b)
    (hhi : b ≤ 89700) : gammaEulerBoundaryTail b ≤ (13 / 2 : ℝ) := by
  have hc := gamma_boundary89100_scalars hlo hhi
  have ha :=
    gamma_target_boundary_arithmetic_lower hRH (by linarith only [hlo]) (by linarith only [hhi])
  have hp : (82555 : ℝ) ≤ Chebyshev.psi b := by linarith only [ha.1, hlo]
  have hA : (89045 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b := by
    linarith only [ha.2, hlo]
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only) hc.1 (by norm_num only) hp hc.2.1
      (by norm_num only) (by norm_num only) hA hc.2.2
  linarith only [h]

/-- Input: RH and 89100<=b<=89700. Claim: the full Euler prefix is at least 28923/5000.
Proof: transport the certified small seed using the proved target-tail cap.
Role: avoid listing thousands of prime-power prefix terms. -/
theorem gamma_prefix89100_lower (hRH : RiemannHypothesis) {b : ℝ} (hlo : 89100 ≤ b)
    (hhi : b ≤ 89700) :
    (28923 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    gamma_euler_prefix_lower_of_tail_upper hRH (by linarith only [hlo])
      (gamma_boundary89100_upper hRH hlo hhi)
  linarith only [h]

/-- Input: RH, odd nonsquare n, log n<=L, x>=4096, the target cell, and a dual upper cap.
Claim: the actual Jacobi joint budget has the displayed bound with no prefix/tail assumptions.
Proof: apply the established target-tail comparison and normalize constants.
Role: leave only the signed dual numerical obligation for this prefix cell. -/
theorem gamma_joint_prefix89100_bound (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {b L x D : ℝ} (hlo : 89100 ≤ b) (hhi : b ≤ 89700) (hlog : Real.log n ≤ L)
    (hx : 4096 ≤ x) (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 28923 / 2500 + 7 / 60 := by
  have h :=
    gamma_joint_prefix_le_of_tail_upper hRH hn hns (by linarith only [hlo]) hlog hx
      (gamma_boundary89100_upper hRH hlo hhi) hD
  linarith only [h]

/-- Input: RH and b>=89100. Claim: the actual full Euler prefix is at least 28923/5000.
Proof: extend the certified left endpoint using nonnegativity of all Euler weights.
Role: avoid further boundary certificates for every larger prefix cutoff. -/
theorem gamma_prefix89100_lower_halfline (hRH : RiemannHypothesis) {b : ℝ} (hb : 89100 ≤ b) :
    (28923 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hp := gamma_prefix89100_lower hRH le_rfl (by norm_num only : (89100 : ℝ) ≤ 89700)
  have hc :
    ((28923 / 5000 : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 89100, Analysis.gammaResolventMangoldtWeight m := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    simpa only [Nat.floor_ofNat] using hp
  have hn : (89100 : ℕ) ≤ ⌊b⌋₊ :=
    Nat.le_floor
      (by
        norm_num only; exact hb)
  have h := Analysis.gamma_euler_prefix_lower_mono hn hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Input: RH, odd nonsquare n, log n<=L, x>=4096, b>=89100 and a signed dual upper cap.
Claim: the actual joint budget has the displayed bound on the entire prefix half-line.
Proof: combine the monotone prefix lower bound with the factor-free comparison.
Role: remove the target-tail numerical field for every b>=89100. -/
theorem gamma_joint_prefix89100_bound_halfline (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {b L x D : ℝ} (hb : 89100 ≤ b) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 28923 / 2500 + 7 / 60 := by
  have hp := gamma_prefix89100_lower_halfline hRH hb
  have hj := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  dsimp only [gammaFactorFreeJointBudget] at hj
  linarith only [hp, hj, hD]

end PseudoPrime.LLS
