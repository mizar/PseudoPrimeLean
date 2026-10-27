/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedCellTransfer
public import PseudoPrime.LLS.GammaMixedErrorEnvelopes

/-! # Checked quadratic-profile geometry and errors below the previous entrance -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a checked rational cell, a>=16 and L in the cell. Claim: x=(2/5)L^2>=100
and the checked root enclosures hold. Proof: compare squares and apply cell soundness.
Role: remove the artificial entrance 300 from the geometric transfer. -/
theorem gamma_profile_geometry_small_cell (a b : ℚ) (ha : (16 : ℝ) ≤ a)
    (hc : (Analysis.gammaProfileEnvelopeCell a b).check = true) {L : ℝ} (hlo : (a : ℝ) ≤ L)
    (hhi : L ≤ (b : ℝ)) :
    let c := Analysis.gammaProfileEnvelopeCell a b;
    let x := (2 / 5 : ℝ) * L ^ 2;
    100 ≤ x ∧
      (c.lo : ℝ) ≤ x ∧
      x ≤ (c.hi : ℝ) ∧
      (c.rootLo : ℝ) ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (c.rootHi : ℝ) ∧ (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
  dsimp only
  let c := Analysis.gammaProfileEnvelopeCell a b
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL : (16 : ℝ) ≤ L := ha.trans hlo
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
  have hsq := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 16 by linarith only [hL])
  have hx100 : (100 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hsq]
  have hx0 : 0 < x := by linarith only [hx100]
  obtain ⟨hclo, horder, hrlo0, hrlo, hrhi0, hrhi, htheta⟩ := c.check_sound hc
  have hroot := hrlo.trans (Real.sqrt_le_sqrt hlox)
  have hrootHi := (Real.sqrt_le_sqrt hxhic).trans hrhi
  have hrootL : (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  exact ⟨hx100, hlox, hxhic, hroot, hrootHi, hrootL⟩

/-- Input: the same geometry and checked logarithm and rational error caps.
Claim: ramp and principal errors obey their caps, with the coupled root lower bound.
Proof: logarithm monotonicity and the generic error envelopes. Role: separate geometric
and elementary errors from prefix, pole and left-line choices. -/
theorem gamma_profile_elementary_errors_small_cell (a b ellX ellE R P : ℚ) (ha : (16 : ℝ) ≤ a)
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
      (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
  dsimp only
  let c := Analysis.gammaProfileEnvelopeCell a b
  let x := (2 / 5 : ℝ) * L ^ 2
  obtain ⟨hxlo, hlox, hxhi, hrlo, hrhi, hrL⟩ := gamma_profile_geometry_small_cell a b ha hc hlo hhi
  change (100 : ℝ) ≤ x at hxlo
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
  exact ⟨hramp.trans hRc, hprincipal.trans hPc, hrL⟩

/-- Input: a>=16, a checked cell, support, row and excess certificates, and L in the cell.
Claim: the actual signed dual budget is at most 2+C. Proof: retain the coupled price
and transfer the checked excess. Role: reuse the same certificate below scale 300. -/
theorem gamma_profile_dual_small_cell (a b C : ℚ) (K : ℕ) (ha : (16 : ℝ) ≤ a)
    (hc : (Analysis.gammaProfileEnvelopeCell a b).check = true)
    (hcap : 1 + (71 / 25 : ℚ) * (Analysis.gammaProfileEnvelopeCell a b).rootHi ≤ K)
    (hrows :
      ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
        (Analysis.gammaProfileEnvelopeRow (Analysis.gammaProfileEnvelopeCell a b) p).envelopeCheck
            (Analysis.gammaProfileEnvelopeCell a b) =
          true)
    (hsum :
      (∑ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
          (Analysis.gammaProfileEnvelopeRow (Analysis.gammaProfileEnvelopeCell a b) p).allowance) ≤
        C)
    {L : ℝ} (hlo : (a : ℝ) ≤ L) (hhi : L ≤ (b : ℝ)) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ 2 + (C : ℝ) := by
  obtain ⟨hx, hlox, hxhi, _, _, _⟩ := gamma_profile_geometry_small_cell a b ha hc hlo hhi
  have he :=
    gamma_signed_excess_le_of_profile_certificate (Analysis.gammaProfileEnvelopeCell a b) K C hc rfl
      hcap hrows hsum hlox hxhi
  have hp := gamma_quadratic_profile_price_le_two (show 0 < L by linarith only [ha, hlo])
  rw [gamma_scale_signed_dual_budget_eq_anchored_support L hx]
  linarith only [hp, he]

/-- Input: L>=290. Claim: the quadratic-profile pole allowance is at most 191/100.
Proof: preserve the root lower bound proportional to L. Role: close the small-cell pole error. -/
theorem gamma_small_profile_pole_error {L : ℝ} (hL : 290 ≤ L) :
    ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt ((2 / 5 : ℝ) * L ^ 2) ≤ 191 / 100 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hx := mul_pos (by norm_num only : (0 : ℝ) < 2 / 5) (sq_pos_of_pos hL0)
  have hr : (79 / 125 : ℝ) * L ≤ Real.sqrt ((2 / 5 : ℝ) * L ^ 2) := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx.le).mpr
    nlinarith only [sq_nonneg L]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hx)]
  linarith only [hr, hL]

/-- Input: x>=33000. Claim: 43x^(-9/16)<=1/8. Proof: an integer-power certificate
and monotonicity. Role: close the left-line error below the previous cutoff 36000. -/
theorem gamma_left_error_le_of_scale_ge_33000 {x : ℝ} (hxlo : 33000 ≤ x) :
    43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8 := by
  have hx : 0 < x := by linarith only [hxlo]
  have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 33000) hxlo 9
  have hc : (1 : ℝ) ≤ (1 / 344 : ℝ) ^ 16 * (33000 : ℝ) ^ 9 := by norm_num only
  have hd := mul_le_mul_of_nonneg_left hp (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 344) 16)
  have h :=
    Analysis.rpow_neg_nat_div_le_of_power_bound hx (by norm_num only : (0 : ℝ) ≤ 1 / 344) 9 16
      (by norm_num only) (hc.trans hd)
  norm_num only [neg_div] at h ⊢
  linarith only [h]

end PseudoPrime.LLS
