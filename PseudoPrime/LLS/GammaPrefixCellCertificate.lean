/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaScaledCellCertificate
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint

/-! # Prefix-parametric scalar checks and analytic cell transfer -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: scale certificate data and a rational prefix lower bound C.
Definition: the original geometric, support, logarithmic and error checks,
with the scalar separation using twice C.
Output: a Boolean check. Role: allow analytic prefix improvements
without changing old certificates. -/
def GammaScaledCellCertificate.prefixScalarCheck (c : GammaScaledCellCertificate) (C : ℚ) : Bool :=
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
      gammaPrincipalCellRationalUpper c.cell.rootLo c.cell.rootHi c.logX ≤ c.principal ∧
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

/-- Input: a proved prefix half-line lower bound, checked scalar data and supported rows.
Claim: the scale is admissible and its actual separation is at least 7/60 throughout the cell.
Proof: preserve the supplied prefix through the generic error and dual comparisons.
Role: connect stronger prefix lemmas without fixing an RH-dependent constant in the checker. -/
theorem GammaScaledCellCertificate.separation_of_prefix (c : GammaScaledCellCertificate) (C : ℚ)
    (hprefixBound :
      ∀ b : ℝ,
        50000 ≤ b → (C : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hc : c.prefixScalarCheck C = true)
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
      50000 ≤ (99 / 40 : ℝ) * x ∧ 7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 40 : ℝ) * x) x := by
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
    gamma_cell_elementary_error_bounds c.cell c.logX c.logE c.ramp c.principal hcell hX hE hellX
      hellE hR hP hlox hxhi
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
      gamma_separation_le_of_scalar_caps hlo hroot heR heP hePole heLeft hDcap hp hmonoR
        (by nlinarith only [hgapR])⟩

/-- Input: RH, a prefix-aware scalar check and the supported adaptive row certificates.
Claim: the actual margin is at least 7/60 throughout the cell.
Proof: supply the asymmetric half-line prefix theorem to the generic transfer.
Role: eliminate the prefix field when constructing improved witness-entrance certificates. -/
theorem GammaScaledCellCertificate.separation_asymmetric (c : GammaScaledCellCertificate)
    (hRH : RiemannHypothesis) (hc : c.prefixScalarCheck (28493 / 5000) = true)
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
      50000 ≤ (99 / 40 : ℝ) * x ∧ 7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 40 : ℝ) * x) x := by
  apply c.separation_of_prefix (28493 / 5000) ?_ hc hrows hsum hlo hhi
  intro b hb
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  exact gamma_prefix50000_lower_asymmetric hRH hb

end PseudoPrime.LLS
