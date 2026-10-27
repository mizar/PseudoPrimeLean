/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedErrorEnvelopes

/-! # Generic soundness of compact mixed-profile separation certificates -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a checked rational profile cell starting at least at 300 and L inside it.
Claim: the actual quadratic scale lies in the cell and has all stated root enclosures.
Proof: compare squares and apply the checked endpoint root inequalities.
Role: share profile geometry across all bridge certificates. -/
theorem gamma_profile_geometry_of_checked_cell (a b : ℚ) (ha : (300 : ℝ) ≤ a)
    (hc : (Analysis.gammaProfileEnvelopeCell a b).check = true) {L : ℝ} (hlo : (a : ℝ) ≤ L)
    (hhi : L ≤ (b : ℝ)) :
    let c := Analysis.gammaProfileEnvelopeCell a b;
    let x := (2 / 5 : ℝ) * L ^ 2;
    36000 ≤ x ∧
      (c.lo : ℝ) ≤ x ∧
      x ≤ (c.hi : ℝ) ∧
      (c.rootLo : ℝ) ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (c.rootHi : ℝ) ∧ (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
  dsimp only
  let c := Analysis.gammaProfileEnvelopeCell a b
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL : (300 : ℝ) ≤ L := ha.trans hlo
  have ha0 : 0 ≤ (a : ℝ) := by linarith only [ha]
  have hL0 : 0 < L := by linarith only [hL]
  have hb0 : 0 ≤ (b : ℝ) := hL0.le.trans hhi
  have hlprod := mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hL0.le ha0)
  have hhprod := mul_nonneg (sub_nonneg.mpr hhi) (add_nonneg hL0.le hb0)
  have hlox : (c.lo : ℝ) ≤ x := by
    norm_num only [c, Analysis.gammaProfileEnvelopeCell, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat]
    dsimp only [x]
    nlinarith only [hlprod]
  have hxhic : x ≤ (c.hi : ℝ) := by
    norm_num only [c, Analysis.gammaProfileEnvelopeCell, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat]
    dsimp only [x]
    nlinarith only [hhprod]
  have hsq := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 300 by linarith only [hL])
  have hx36000 : (36000 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hsq]
  have hx0 : 0 < x := by linarith only [hx36000]
  obtain ⟨hclo, horder, hrlo0, hrlo, hrhi0, hrhi, htheta⟩ := c.check_sound hc
  have hroot := hrlo.trans (Real.sqrt_le_sqrt hlox)
  have hrootHi := (Real.sqrt_le_sqrt hxhic).trans hrhi
  have hrootL : (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  exact ⟨hx36000, hlox, hxhic, hroot, hrootHi, hrootL⟩

/-- Input: checked cell, logarithm caps and rational ramp/principal envelope caps.
Claim: all four actual non-Euler errors and the coupled root meet the stated bounds.
Proof: combine endpoint geometry, logarithm monotonicity and the generic error envelopes.
Role: turn a few rational scalar checks into uniform analytic error bounds. -/
theorem gamma_profile_errors_of_checked_cell (a b ellX ellE R P : ℚ) (ha : (300 : ℝ) ≤ a)
    (hc : (Analysis.gammaProfileEnvelopeCell a b).check = true)
    (hX : Real.log ((Analysis.gammaProfileEnvelopeCell a b).hi : ℝ) ≤ ellX)
    (hE : Real.log ((101 / 40 : ℝ) * ((Analysis.gammaProfileEnvelopeCell a b).hi : ℝ)) ≤ ellE)
    (hellX : 0 ≤ ellX) (hellE : 0 ≤ ellE)
    (hR :
      gammaRampCellRationalUpper (Analysis.gammaProfileEnvelopeCell a b).rootLo
          (Analysis.gammaProfileEnvelopeCell a b).rootHi ellE ≤
        R)
    (hP :
      gammaPrincipalCellRationalUpper (Analysis.gammaProfileEnvelopeCell a b).rootLo
          (Analysis.gammaProfileEnvelopeCell a b).rootHi ellX ≤
        P)
    {L : ℝ} (hlo : (a : ℝ) ≤ L) (hhi : L ≤ (b : ℝ)) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ P ∧
      ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 19 / 10 ∧
      43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8 ∧ (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
  dsimp only
  let c := Analysis.gammaProfileEnvelopeCell a b
  let x := (2 / 5 : ℝ) * L ^ 2
  obtain ⟨hxlo, hlox, hxhi, hrlo, hrhi, hrL⟩ :=
    gamma_profile_geometry_of_checked_cell a b ha hc hlo hhi
  change (36000 : ℝ) ≤ x at hxlo
  change (c.lo : ℝ) ≤ x at hlox
  change x ≤ (c.hi : ℝ) at hxhi
  change (c.rootLo : ℝ) ≤ Real.sqrt x at hrlo
  change Real.sqrt x ≤ (c.rootHi : ℝ) at hrhi
  change (79 / 125 : ℝ) * L ≤ Real.sqrt x at hrL
  have hx0 : 0 < x := by linarith only [hxlo]
  obtain ⟨hclo, horder, hrlo0, hrootlo, hrhi0, hroothi, htheta⟩ := c.check_sound hc
  have hlogx := (Real.log_le_log hx0 hxhi).trans hX
  have harg := mul_le_mul_of_nonneg_left hxhi (show (0 : ℝ) ≤ 101 / 40 by norm_num only)
  have hloge :=
    (Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 101 / 40) hx0) harg).trans hE
  have hargR : x * (99 / 40) ≤ (101 / 40 : ℝ) * x := by linarith only [hx0]
  have hlogr :=
    (Real.log_le_log (mul_pos hx0 (by norm_num only : (0 : ℝ) < 99 / 40)) hargR).trans hloge
  have hramp :=
    gamma_ramp_error_le_cell_envelope hx0 hrlo0 hrlo hrhi ((Rat.cast_nonneg (K := ℝ)).mpr hellE)
      hloge hlogr
  have hprincipal :=
    gamma_principal_error_le_cell_envelope hrlo0 hrlo hrhi ((Rat.cast_nonneg (K := ℝ)).mpr hellX)
      hlogx
  have hRc := (Rat.cast_le (K := ℝ)).mpr hR
  have hPc := (Rat.cast_le (K := ℝ)).mpr hP
  norm_num only [gammaRampCellRationalUpper, gammaPrincipalCellRationalUpper, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hRc hPc hramp hprincipal
  exact
    ⟨hramp.trans hRc, hprincipal.trans hPc, gamma_pole_error_le_of_threehundred_le (ha.trans hlo),
      gamma_left_error_le_of_scale_ge_36000 hxlo, hrL⟩

/-- Input: lower logarithmic endpoint and ramp, principal and dual caps.
Definition: the rational lower separation margin at that endpoint.
Output: a scalar gap allowance. Role: certify the remaining linear comparison once per cell. -/
def gammaProfileGapAt (a R P D : ℚ) : ℚ :=
  ((83125234337 / 100000000000) * (79 / 125) - 11783423 / 25000000) * a -
    ((11783423 / 25000000) * (7 / 5) + 3 / 4 + D - 28923 / 2500 + 11 + 2 * R + P + 19 / 10 + 1 / 8)

/-- Input: rational endpoints, logarithm caps, error caps and logarithm Taylor scales.
Definition: check the common cell, two logarithms, two envelopes and endpoint gap.
Output: Bool with analytic soundness proved below. Role: compact uniform separation certificates. -/
def gammaProfileSeparationCheck (a b ellX ellE R P D : ℚ) (jX jE : ℕ) : Bool :=
  let c := Analysis.gammaProfileEnvelopeCell a b
  decide
    (c.check = true ∧
      Analysis.rationalLogIntervalCheck c.hi jX 20 0 ellX = true ∧
      Analysis.rationalLogIntervalCheck ((101 / 40 : ℚ) * c.hi) jE 20 0 ellE = true ∧
      300 ≤ a ∧
      0 ≤ ellX ∧
      0 ≤ ellE ∧
      gammaRampCellRationalUpper c.rootLo c.rootHi ellE ≤ R ∧
      gammaPrincipalCellRationalUpper c.rootLo c.rootHi ellX ≤ P ∧
      7 / 60 ≤ gammaProfileGapAt a R P D)

/-- Input: RH, a successful rational separation check, L in the cell and an actual dual cap.
Claim: the actual factor-free margin is at least 7/60 throughout the cell.
Proof: retain the certified prefix gain, ramp mass and increasing linear margin.
Role: reuse one soundness theorem when changing endpoints or numerical allowances. -/
theorem gamma_factor_free_separation_of_cell_check (hRH : RiemannHypothesis)
    (a b ellX ellE R P D : ℚ) (jX jE : ℕ)
    (hc : gammaProfileSeparationCheck a b ellX ellE R P D jX jE = true) {L : ℝ} (hlo : (a : ℝ) ≤ L)
    (hhi : L ≤ (b : ℝ)) (hD : gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ D) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  obtain ⟨hcell, hXcheck, hEcheck, ha, hellX, hellE, hR, hP, hgap⟩ := of_decide_eq_true hc
  have haR := (Rat.cast_le (K := ℝ)).mpr ha
  norm_num only [Rat.cast_ofNat] at haR
  have hX := (Analysis.rationalLogIntervalCheck_sound hXcheck).2
  have hE := (Analysis.rationalLogIntervalCheck_sound hEcheck).2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hE
  obtain ⟨he1, he2, he3, he4, hroot⟩ :=
    gamma_profile_errors_of_checked_cell a b ellX ellE R P haR hcell hX hE hellX hellE hR hP hlo hhi
  let x := (2 / 5 : ℝ) * L ^ 2
  let y := (99 / 100 : ℝ) * L ^ 2
  change gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R at he1
  change
    (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ P at he2
  change ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 19 / 10 at he3
  change 43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8 at he4
  change (79 / 125 : ℝ) * L ≤ Real.sqrt x at hroot
  have hL := haR.trans hlo
  have hsq := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 300 by linarith only [hL])
  have hy : (89100 : ℝ) ≤ y := by
    dsimp only [y]; nlinarith only [hsq]
  have hp := gamma_prefix89100_lower_halfline hRH hy
  have hj :
    gammaFactorFreeJointBudget L y x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + (D : ℝ) - 28923 / 2500 := by
    unfold gammaFactorFreeJointBudget
    linarith only [hp, hD]
  have hm1 := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower (Real.sqrt_nonneg x)
  have hm2 :=
    mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 83125234337 / 100000000000 by norm_num only)
  have hm := hm2.trans hm1
  have hg := (Rat.cast_le (K := ℝ)).mpr hgap
  norm_num only [gammaProfileGapAt, Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at hg
  have hinc :=
    mul_nonneg (sub_nonneg.mpr hlo)
      (show (0 : ℝ) ≤ (83125234337 / 100000000000) * (79 / 125) - 11783423 / 25000000 by
        norm_num only)
  change 7 / 60 ≤ gammaFactorFreeSeparation L y x
  unfold gammaFactorFreeSeparation
  nlinarith only [hm, hj, he1, he2, he3, he4, hg, hinc]

end PseudoPrime.LLS
