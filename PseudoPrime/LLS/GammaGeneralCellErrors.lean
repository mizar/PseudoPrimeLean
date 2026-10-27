/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaAdaptiveCellTransfer
public import PseudoPrime.LLS.GammaMixedErrorEnvelopes

/-! # Scale-independent error and scalar-separation transfer on checked cells -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: x>0, L>=a, a coupled root lower bound, nonnegative allowance and slope/base checks.
Claim: the actual pole error is at most the allowance. Proof: retain the root coupling
and extend the checked linear comparison. Role: avoid a fixed logarithmic entrance. -/
theorem gamma_pole_error_le_of_coupled_root {a L x r E : ℝ} (hx : 0 < x) (hL : a ≤ L)
    (hroot : r * L ≤ Real.sqrt x) (hE : 0 ≤ E) (hslope : 7 / 6 ≤ E * r)
    (hbase : (7 / 6) * (a + 7 / 5) + 4 ≤ E * r * a) :
    ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ E := by
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hx)]
  have hm := mul_le_mul_of_nonneg_left hroot hE
  have hi := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hslope)
  nlinarith only [hm, hi, hbase]

/-- Input: a positive lower scale, x above it, a nonnegative cap and an integer-power check.
Claim: the actual left-line error obeys the cap. Proof: power monotonicity and rational
exponent soundness. Role: reuse arbitrary rational error allowances on whole cells. -/
theorem gamma_left_error_le_of_lower_endpoint {lo x Z : ℝ} (hlo : 0 < lo) (hlox : lo ≤ x)
    (hZ : 0 ≤ Z) (hpow : 1 ≤ (Z / 43) ^ 16 * lo ^ 9) : 43 * x ^ (-9 / 16 : ℝ) ≤ Z := by
  have hx := hlo.trans_le hlox
  have hp := pow_le_pow_left₀ hlo.le hlox 9
  have hZ43 : (0 : ℝ) ≤ Z / 43 := div_nonneg hZ (by norm_num only)
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hZ43 16)
  have h :=
    Analysis.rpow_neg_nat_div_le_of_power_bound hx hZ43 9 16 (by norm_num only) (hpow.trans hm)
  norm_num only [neg_div] at h ⊢
  nlinarith only [h]

/-- Input: any checked cell, logarithm and rational envelope caps and an actual scale inside it.
Claim: the ramp and principal errors obey the stated caps. Proof: root bounds and logarithm
monotonicity. Role: decouple error transfer from the particular kernel-scale multiplier. -/
theorem gamma_cell_elementary_error_bounds (c : Analysis.GammaLocalCellData) (ellX ellE R P : ℚ)
    (hc : c.check = true) (hX : Real.log (c.hi : ℝ) ≤ ellX)
    (hE : Real.log ((101 / 40 : ℝ) * (c.hi : ℝ)) ≤ ellE) (hellX : 0 ≤ ellX) (hellE : 0 ≤ ellE)
    (hR : gammaRampCellRationalUpper c.rootLo c.rootHi ellE ≤ R)
    (hP : gammaPrincipalCellRationalUpper c.rootLo c.rootHi ellX ≤ P) {x : ℝ} (hlo : (c.lo : ℝ) ≤ x)
    (hhi : x ≤ (c.hi : ℝ)) :
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ P := by
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
    gamma_principal_error_le_cell_envelope hrlo0 hrlo hrhi ((Rat.cast_nonneg (K := ℝ)).mpr hellX)
      hlogx
  have hRc := (Rat.cast_le (K := ℝ)).mpr hR
  have hPc := (Rat.cast_le (K := ℝ)).mpr hP
  norm_num only [gammaRampCellRationalUpper, gammaPrincipalCellRationalUpper, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hRc hPc hramp hprincipal
  exact ⟨hramp.trans hRc, hprincipal.trans hPc⟩

/-- Input: root, prefix, dual and all error bounds, a nonnegative linear slope and an endpoint gap.
Claim: the actual factor-free margin is at least 7/60. Proof: preserve the ramp mass,
subtract the joint-budget cap and extend the scalar gap. Role: connect arbitrary numerical
cell certificates to actual witness separation. -/
theorem gamma_separation_le_of_scalar_caps {a L x b r R P E Z D C : ℝ} (hL : a ≤ L)
    (hroot : r * L ≤ Real.sqrt x) (hR : gammaRampPairedErrorNumerator x / Real.sqrt x ≤ R)
    (hP : (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ P)
    (hE : ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ E) (hZ : 43 * x ^ (-9 / 16 : ℝ) ≤ Z)
    (hD : gammaScaleSignedDualBudget L x ≤ D)
    (hC : C ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hmono : 0 ≤ (83125234337 / 100000000000 : ℝ) * r - 11783423 / 25000000)
    (hgap :
      7 / 60 ≤
        ((83125234337 / 100000000000 : ℝ) * r - 11783423 / 25000000) * a -
          ((11783423 / 25000000 : ℝ) * (7 / 5) + 3 / 4 + D - 2 * C + 11 + 2 * R + P + E + Z)) :
    7 / 60 ≤ gammaFactorFreeSeparation L b x := by
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
  unfold gammaFactorFreeSeparation
  nlinarith only [hm, hj, hR, hP, hE, hZ, hgap, hi]

end PseudoPrime.LLS
