/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrefixCellCertificate
public import PseudoPrime.LLS.GammaPrincipalCapComparison

/-! # Parameterized scale-cell comparisons using the signed principal error -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Definition: twice the paired ramp lower bound minus the signed-variation
principal cap and factor-independent joint budget. Input: level L, prefix b and
scale x. Role: a scalar witness target retaining the stronger principal estimate. -/
noncomputable def gammaSignedPrincipalFactorFreeSeparation (L b x : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    gammaSignedVariationPrincipalCap x -
    (gammaFactorFreeJointBudget L b x + 11 + ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- Under odd-nonsquare input data, log(n) <= L, x >= 4096 and the pole log bound,
the scalar margin is below the actual joint margin plus 7/60. Compare the local
and pole costs. Role: remove factorization from the witness criterion. -/
theorem gamma_signed_principal_separation_le_joint_add_small_scale {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 4096 ≤ x)
    (hlogQ : Real.log Q ≤ L + 7 / 5) :
    gammaSignedPrincipalFactorFreeSeparation L b x ≤
      gammaJointPrefixSeparationWithPrincipalCap Q (NumberTheory.complexQuadraticCharacter n hn) b x
          (-3 / 2) (gammaSignedVariationPrincipalCap x) +
        7 / 60 := by
  have hJ := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  have hN :
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x ≤ ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith only [hlogQ]) (Real.sqrt_nonneg x)
  dsimp only [gammaSignedPrincipalFactorFreeSeparation, gammaJointPrefixSeparationWithPrincipalCap]
  linarith only [hJ, hN]

/-- Input: arbitrary scalar caps for roots, errors, dual cost and Euler prefix.
Claim: the stated rational gap gives scalar separation at least 7/60. Retain
the ramp main mass and the improved principal error. Role: certify whole cells. -/
theorem gamma_signed_principal_separation_of_scalar_caps {a L x b r R P E Z D C : ℝ} (hL : a ≤ L)
    (hroot : r * L ≤ Real.sqrt x) (hR : gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R)
    (hP : (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x ≤ P)
    (hE : ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ E) (hZ : 43 * x ^ (-9 / 16 : ℝ) ≤ Z)
    (hD : gammaScaleSignedDualBudget L x ≤ D)
    (hC : C ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hmono : 0 ≤ (83125234337 / 100000000000 : ℝ) * r - 11783423 / 25000000)
    (hgap :
      7 / 60 ≤
        ((83125234337 / 100000000000 : ℝ) * r - 11783423 / 25000000) * a -
          ((11783423 / 25000000 : ℝ) * (7 / 5) + 3 / 4 + D - 2 * C + 11 + 2 * R + P + E + Z)) :
    7 / 60 ≤ gammaSignedPrincipalFactorFreeSeparation L b x := by
  have hj :
    gammaFactorFreeJointBudget L b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * C := by
    unfold gammaFactorFreeJointBudget
    linarith only [hD, hC]
  have hm1 := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower (Real.sqrt_nonneg x)
  have hm2 :=
    mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 83125234337 / 100000000000 by norm_num only)
  have hm := hm2.trans hm1
  have hi := mul_nonneg (sub_nonneg.mpr hL) hmono
  unfold gammaSignedPrincipalFactorFreeSeparation gammaSignedVariationPrincipalCap
  nlinarith only [hm, hj, hR, hP, hE, hZ, hgap, hi]

/-- Definition: rational principal-error envelope from positive lower root,
upper root and logarithm cap. Role: check a whole scale cell by rational arithmetic. -/
def gammaSignedPrincipalCellRationalUpper (rlo rhi ell : ℚ) : ℚ :=
  (rhi / 20 + (5517 / 4000) * ell + 2469 / 800) / rlo

/-- Input: positive root lower bound, upper root and nonnegative logarithm cap.
Claim: the signed principal error lies below the cell envelope. Bound numerator
above and denominator below. Role: transfer rational cell caps to actual scales. -/
theorem gamma_signed_principal_error_le_cell_envelope {x rlo rhi ell : ℝ} (hlo : 0 < rlo)
    (hrlo : rlo ≤ Real.sqrt x) (hrhi : Real.sqrt x ≤ rhi) (hell : 0 ≤ ell)
    (hlog : Real.log x ≤ ell) :
    (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x ≤
      (rhi / 20 + (5517 / 4000 : ℝ) * ell + 2469 / 800) / rlo := by
  have hnum :
    Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800 ≤
      rhi / 20 + (5517 / 4000 : ℝ) * ell + 2469 / 800 := by
    linarith only [hrhi, hlog]
  have hnonneg : 0 ≤ rhi / 20 + (5517 / 4000 : ℝ) * ell + 2469 / 800 := by
    have hr0 := (Real.sqrt_nonneg x).trans hrhi
    linarith only [hr0, hell]
  exact
    (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)).trans
      (div_le_div₀ hnonneg le_rfl hlo hrlo)

/-- Input: a checked scale cell, root and log bounds, and rational ramp and
principal allowances. Claim: both real errors obey these allowances throughout
the cell. Role: share the analytic error transfer independently of cell constants. -/
theorem gamma_cell_signed_principal_error_bounds (c : Analysis.GammaLocalCellData)
    (ellX ellE R P : ℚ) (hc : c.check = true) (hX : Real.log (c.hi : ℝ) ≤ ellX)
    (hE : Real.log ((101 / 40 : ℝ) * (c.hi : ℝ)) ≤ ellE) (hellX : 0 ≤ ellX) (hellE : 0 ≤ ellE)
    (hR : gammaRampCellRationalUpper c.rootLo c.rootHi ellE ≤ R)
    (hP : gammaSignedPrincipalCellRationalUpper c.rootLo c.rootHi ellX ≤ P) {x : ℝ}
    (hlo : (c.lo : ℝ) ≤ x) (hhi : x ≤ (c.hi : ℝ)) :
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R ∧
      (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x ≤ P := by
  obtain ⟨hclo, _, hrlo0, hrootlo, _, hroothi, _⟩ := c.check_sound hc
  have hx := hclo.trans_le hlo
  have hrlo := hrootlo.trans (Real.sqrt_le_sqrt hlo)
  have hrhi := (Real.sqrt_le_sqrt hhi).trans hroothi
  have hlogx := (Real.log_le_log hx hhi).trans hX
  have harg := mul_le_mul_of_nonneg_left hhi (show (0 : ℝ) ≤ 101 / 40 by norm_num only)
  have hloge := (Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 101 / 40) hx) harg).trans hE
  have hargR : x * (99 / 40) ≤ (101 / 40 : ℝ) * x := by linarith only [hx]
  have hlogr :=
    (Real.log_le_log (mul_pos hx (by norm_num only : (0 : ℝ) < 99 / 40)) hargR).trans hloge
  have hramp :=
    gamma_ramp_error_le_cell_envelope hx hrlo0 hrlo hrhi ((Rat.cast_nonneg (K := ℝ)).mpr hellE)
      hloge hlogr
  have hprincipal :=
    gamma_signed_principal_error_le_cell_envelope hrlo0 hrlo hrhi
      ((Rat.cast_nonneg (K := ℝ)).mpr hellX) hlogx
  have hRc := (Rat.cast_le (K := ℝ)).mpr hR
  have hPc := (Rat.cast_le (K := ℝ)).mpr hP
  norm_num only [gammaRampCellRationalUpper, gammaSignedPrincipalCellRationalUpper, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hRc hPc hramp hprincipal
  exact ⟨hramp.trans hRc, hprincipal.trans hPc⟩

/-- Definition: geometric, support, log, error and scalar-gap checks for a scale
cell and supplied Euler prefix bound C, using the signed principal envelope.
Role: keep numerical certificate data separate from the analytic proof. -/
def GammaScaledCellCertificate.signedPrincipalPrefixCheck (c : GammaScaledCellCertificate) (C : ℚ) :
    Bool :=
  decide
    (0 < c.scale ∧
      10 ≤ c.left ∧
      0 < c.rootLoRatio ∧
      c.rootLoRatio ^ 2 ≤ c.scale ∧
      c.cell.check = true ∧
      4096 ≤ c.cell.lo ∧
      50000 ≤ (99 / 40 : ℚ) * c.cell.lo ∧
      1 + (71 / 25 : ℚ) * c.cell.rootHi ≤ c.support ∧
      (5 / 4 : ℚ) / c.rootLoRatio + c.excess ≤ c.dual ∧
      Analysis.rationalLogIntervalCheck c.cell.hi c.logIndexX 20 0 c.logX = true ∧
      Analysis.rationalLogIntervalCheck ((101 / 40 : ℚ) * c.cell.hi) c.logIndexE 20 0 c.logE =
        true ∧
      0 ≤ c.logX ∧
      0 ≤ c.logE ∧
      gammaRampCellRationalUpper c.cell.rootLo c.cell.rootHi c.logE ≤ c.ramp ∧
      gammaSignedPrincipalCellRationalUpper c.cell.rootLo c.cell.rootHi c.logX ≤ c.principal ∧
      0 ≤ c.pole ∧
      7 / 6 ≤ c.pole * c.rootLoRatio ∧
      (7 / 6 : ℚ) * (c.left + 7 / 5) + 4 ≤ c.pole * c.rootLoRatio * c.left ∧
      0 ≤ c.leftError ∧
      1 ≤ (c.leftError / 43) ^ 16 * c.cell.lo ^ 9 ∧
      0 ≤ (83125234337 / 100000000000 : ℚ) * c.rootLoRatio - 11783423 / 25000000 ∧
      7 / 60 ≤
        ((83125234337 / 100000000000 : ℚ) * c.rootLoRatio - 11783423 / 25000000) * c.left -
          ((11783423 / 25000000 : ℚ) * (7 / 5) + 3 / 4 + c.dual - 2 * C + 11 + 2 * c.ramp +
            c.principal +
            c.pole +
            c.leftError))

/-- Input: any prefix half-line lower bound, checked cell data and local row caps.
Claim: scale admissibility and signed-principal margin at least 7/60 hold in
the entire cell. Role: reuse the proof with different starting levels and constants. -/
theorem GammaScaledCellCertificate.separation_of_signed_principal_prefix
    (c : GammaScaledCellCertificate) (C : ℚ)
    (hprefixBound :
      ∀ b : ℝ,
        50000 ≤ b → (C : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hc : c.signedPrincipalPrefixCheck C = true)
    (hrows :
      ∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true)
    (hsum :
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess)
    {L : ℝ} (hlo : (c.left : ℝ) ≤ L) (hhi : L ≤ (c.right : ℝ)) :
    let x := (c.scale : ℝ) * L ^ 2;
    4096 ≤ x ∧
      50000 ≤ (99 / 40 : ℝ) * x ∧
      7 / 60 ≤ gammaSignedPrincipalFactorFreeSeparation L ((99 / 40 : ℝ) * x) x := by
  obtain
    ⟨hs, ha, hr, hrsq, hcell, hmin, hprefix, hcap, hdual, hlogX, hlogE, hellX, hellE, hR, hP, hpole,
      hslope, hbase, hZ, hpow, hmono, hgap⟩ :=
    of_decide_eq_true hc
  have hsR := (Rat.cast_pos (K := ℝ)).mpr hs
  have haR : (0 : ℝ) < c.left := by
    have h := (Rat.cast_le (K := ℝ)).mpr ha
    norm_num only [Rat.cast_ofNat] at h
    linarith only [h]
  have hrR := (Rat.cast_pos (K := ℝ)).mpr hr
  have hrsqR := (Rat.cast_le (K := ℝ)).mpr hrsq
  norm_num only [Rat.cast_pow] at hrsqR
  obtain ⟨hlox, hxhi, _, _, hroot⟩ :=
    gamma_scaled_profile_geometry c.scale c.rootLoRatio c.rootHiRatio c.left c.right hsR haR hrR
      hrsqR hcell hlo hhi
  let x := (c.scale : ℝ) * L ^ 2
  change (c.cell.lo : ℝ) ≤ x at hlox
  change x ≤ (c.cell.hi : ℝ) at hxhi
  change (c.rootLoRatio : ℝ) * L ≤ Real.sqrt x at hroot
  have hminR := (Rat.cast_le (K := ℝ)).mpr hmin
  norm_num only [Rat.cast_ofNat] at hminR
  have hx : (4096 : ℝ) ≤ x := hminR.trans hlox
  have hx0 : 0 < x := by linarith only [hx]
  have hprefR := (Rat.cast_le (K := ℝ)).mpr hprefix
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hprefR
  have hb : (50000 : ℝ) ≤ (99 / 40 : ℝ) * x :=
    hprefR.trans (mul_le_mul_of_nonneg_left hlox (by norm_num only))
  have hp := hprefixBound ((99 / 40 : ℝ) * x) hb
  have hD :=
    gamma_scaled_adaptive_dual_le c.scale c.rootLoRatio c.rootHiRatio c.left c.right c.excess
      c.support hsR haR hrR hrsqR hcell
      (by
        change (100 : ℚ) ≤ c.cell.lo; linarith only [hmin])
      hcap hrows hsum hlo hhi
  have hdR := (Rat.cast_le (K := ℝ)).mpr hdual
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hdR
  have hDcap : gammaScaleSignedDualBudget L x ≤ c.dual := hD.trans hdR
  have hX := (Analysis.rationalLogIntervalCheck_sound hlogX).2
  have hE := (Analysis.rationalLogIntervalCheck_sound hlogE).2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hE
  obtain ⟨heR, heP⟩ :=
    gamma_cell_signed_principal_error_bounds c.cell c.logX c.logE c.ramp c.principal hcell hX hE
      hellX hellE hR hP hlox hxhi
  have he0 := (Rat.cast_nonneg (K := ℝ)).mpr hpole
  have hslopeR := (Rat.cast_le (K := ℝ)).mpr hslope
  have hbaseR := (Rat.cast_le (K := ℝ)).mpr hbase
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hslopeR hbaseR
  have hePole := gamma_pole_error_le_of_coupled_root hx0 hlo hroot he0 hslopeR hbaseR
  have hZ0 := (Rat.cast_nonneg (K := ℝ)).mpr hZ
  have hpowR := (Rat.cast_le (K := ℝ)).mpr hpow
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hpowR
  have hlo0 := (c.cell.check_sound hcell).1
  have heLeft := gamma_left_error_le_of_lower_endpoint hlo0 hlox hZ0 hpowR
  have hmonoR := (Rat.cast_nonneg (K := ℝ)).mpr hmono
  have hgapR := (Rat.cast_le (K := ℝ)).mpr hgap
  norm_num only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat] at hmonoR hgapR
  exact
    ⟨hx, hb,
      gamma_signed_principal_separation_of_scalar_caps hlo hroot heR heP hePole heLeft hDcap hp
        hmonoR (by nlinarith only [hgapR])⟩

/-- Under RH and the checked cell conditions, supply the existing asymmetric
prefix lower bound 28493/5000. Claim: the signed-principal margin holds throughout
the cell. Role: remove a separate prefix hypothesis without finite input checks. -/
theorem GammaScaledCellCertificate.separation_signed_principal_asymmetric
    (c : GammaScaledCellCertificate) (hRH : RiemannHypothesis)
    (hc : c.signedPrincipalPrefixCheck (28493 / 5000) = true)
    (hrows :
      ∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true)
    (hsum :
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess)
    {L : ℝ} (hlo : (c.left : ℝ) ≤ L) (hhi : L ≤ (c.right : ℝ)) :
    let x := (c.scale : ℝ) * L ^ 2;
    4096 ≤ x ∧
      50000 ≤ (99 / 40 : ℝ) * x ∧
      7 / 60 ≤ gammaSignedPrincipalFactorFreeSeparation L ((99 / 40 : ℝ) * x) x := by
  apply c.separation_of_signed_principal_prefix (28493 / 5000) ?_ hc hrows hsum hlo hhi
  intro b hb
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  exact gamma_prefix50000_lower_asymmetric hRH hb

end PseudoPrime.LLS
