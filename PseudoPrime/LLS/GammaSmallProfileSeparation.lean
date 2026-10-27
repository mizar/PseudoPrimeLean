/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSmallProfileGeometry
public import PseudoPrime.LLS.GammaCheckpoint50000

/-! # Rational cell checks with the analytically transported prefix at cutoff 50000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: rational lower endpoint and ramp, principal and dual upper caps.
Definition: the increasing linear margin with prefix 28423/5000 and pole cap 191/100.
Output: a rational gap. Role: check separation without enumerating input integers. -/
def gammaSmallProfileGapAt (a R P D : ℚ) : ℚ :=
  ((83125234337 / 100000000000) * (79 / 125) - 11783423 / 25000000) * a -
    ((11783423 / 25000000) * (7 / 5) + 3 / 4 + D - 28423 / 2500 + 11 + 2 * R + P + 191 / 100 +
      1 / 8)

/-- Input: rational cell endpoints and logarithm, error and dual caps.
Definition: checked cell, logarithm enclosures, elementary error caps and gap at least 7/60.
Output: executable Boolean. Role: share the numerical check for all small-profile cells. -/
def gammaSmallProfileCheck (a b ellX ellE R P D : ℚ) (jX jE : ℕ) : Bool :=
  let c := Analysis.gammaProfileEnvelopeCell a b
  decide
    (c.check = true ∧
      Analysis.rationalLogIntervalCheck c.hi jX 20 0 ellX = true ∧
      Analysis.rationalLogIntervalCheck ((101 / 40 : ℚ) * c.hi) jE 20 0 ellE = true ∧
      290 ≤ a ∧
      0 ≤ ellX ∧
      0 ≤ ellE ∧
      gammaRampCellRationalUpper c.rootLo c.rootHi ellE ≤ R ∧
      gammaPrincipalCellRationalUpper c.rootLo c.rootHi ellX ≤ P ∧
      7 / 60 ≤ gammaSmallProfileGapAt a R P D)

/-- Input: RH, a valid small-profile check, L in its cell and an actual dual upper bound.
Claim: the actual factor-free margin is at least 7/60. Proof: combine the transported
prefix with checked elementary errors, the root mass and pole/left-line allowances.
Role: connect lower-scale certificates to actual prime-witness extraction. -/
theorem gamma_small_profile_separation_of_check (hRH : RiemannHypothesis) (a b ellX ellE R P D : ℚ)
    (jX jE : ℕ) (hc : gammaSmallProfileCheck a b ellX ellE R P D jX jE = true) {L : ℝ}
    (hlo : (a : ℝ) ≤ L) (hhi : L ≤ (b : ℝ))
    (hD : gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ D) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  obtain ⟨hcell, hXcheck, hEcheck, ha, hellX, hellE, hR, hP, hgap⟩ := of_decide_eq_true hc
  have haR := (Rat.cast_le (K := ℝ)).mpr ha
  norm_num only [Rat.cast_ofNat] at haR
  have hX := (Analysis.rationalLogIntervalCheck_sound hXcheck).2
  have hE := (Analysis.rationalLogIntervalCheck_sound hEcheck).2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hE
  obtain ⟨he1, he2, hroot⟩ :=
    gamma_profile_elementary_errors_small_cell a b ellX ellE R P (by linarith only [haR]) hcell hX
      hE hellX hellE hR hP hlo hhi
  let x := (2 / 5 : ℝ) * L ^ 2
  let y := (99 / 100 : ℝ) * L ^ 2
  change gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R at he1
  change
    (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ P at he2
  change (79 / 125 : ℝ) * L ≤ Real.sqrt x at hroot
  have hL : 290 ≤ L := haR.trans hlo
  have hsq := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 290 by linarith only [hL])
  have hy : (50000 : ℝ) ≤ y := by
    dsimp only [y]; nlinarith only [hsq]
  have hx : (33000 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hsq]
  have hp := gamma_prefix50000_lower_halfline hRH hy
  have hj :
    gammaFactorFreeJointBudget L y x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + (D : ℝ) - 28423 / 2500 := by
    unfold gammaFactorFreeJointBudget
    linarith only [hp, hD]
  have he3 := gamma_small_profile_pole_error hL
  have he4 := gamma_left_error_le_of_scale_ge_33000 hx
  have hm1 := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower (Real.sqrt_nonneg x)
  have hm2 :=
    mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 83125234337 / 100000000000 by norm_num only)
  have hm := hm2.trans hm1
  have hg := (Rat.cast_le (K := ℝ)).mpr hgap
  norm_num only [gammaSmallProfileGapAt, Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at hg
  have hinc :=
    mul_nonneg (sub_nonneg.mpr hlo)
      (show (0 : ℝ) ≤ (83125234337 / 100000000000) * (79 / 125) - 11783423 / 25000000 by
        norm_num only)
  change 7 / 60 ≤ gammaFactorFreeSeparation L y x
  unfold gammaFactorFreeSeparation
  change ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 191 / 100 at he3
  nlinarith only [hm, hj, he1, he2, he3, he4, hg, hinc]

end PseudoPrime.LLS
