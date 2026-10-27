/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ThirdMomentEnergyAlternatives

/-! # No-band energy alternatives from the full truncated weight -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A retained full correlation weight yields a diagonal cubic bound, a
third-moment cubic bound, or a thirteenth-power bound. Keep the cutoff budget
and Fourier error explicit so the argument has no dyadic-band count. -/
theorem truncated_weight_energy_alternatives {p E B M T R : ℝ} (hp : 0 < p) (hE : 0 < E)
    (hB : 0 < B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hretain : E ≤ 2 * B) (hBupper : B ≤ E)
    (hcut : M * E ≤ 2 ^ 22 * p ^ 3) (hampl : B ^ 2 * E ≤ p ^ 4 * M * B + p ^ 3 * R)
    (hR : p ^ 2 * R ^ 2 ≤ 4 * T * E * B ^ 2 + 65536 * T * p ^ 3 * Real.sqrt E * M ^ 2 * B) :
    E ^ 3 ≤ 2 ^ 28 * p ^ 7 ∨ E ^ 3 ≤ 2 ^ 7 * p ^ 4 * T ∨ E ^ 13 ≤ 2 ^ 132 * p ^ 26 * T ^ 2 := by
  by_cases hsmall : E ^ 3 ≤ 2 ^ 28 * p ^ 7
  · exact Or.inl hsmall
  right
  have hlarge : 2 ^ 28 * p ^ 7 < E ^ 3 := lt_of_not_ge hsmall
  have hMB : M * B ≤ M * E := mul_le_mul_of_nonneg_left hBupper hM
  have hdiag : p ^ 4 * M * B ≤ 2 ^ 22 * p ^ 7 := by
    calc
      p ^ 4 * M * B = p ^ 4 * (M * B) := by ring
      _ ≤ p ^ 4 * (M * E) := mul_le_mul_of_nonneg_left hMB (pow_nonneg hp.le 4)
      _ ≤ p ^ 4 * (2 ^ 22 * p ^ 3) := mul_le_mul_of_nonneg_left hcut (pow_nonneg hp.le 4)
      _ = 2 ^ 22 * p ^ 7 := by ring
  have hdiagSmall : p ^ 4 * M * B < E ^ 3 / 64 := by nlinarith only [hdiag, hlarge]
  have hretainSq := pow_le_pow_left₀ hE.le hretain 2
  have hretainMul := mul_le_mul_of_nonneg_right hretainSq hE.le
  have hleft : E ^ 3 / 4 ≤ B ^ 2 * E := by nlinarith only [hretainMul]
  have hRlower : (15 / 64 : ℝ) * E ^ 3 ≤ p ^ 3 * R := by nlinarith only [hleft, hdiagSmall, hampl]
  have hRlowerNonneg : 0 ≤ (15 / 64 : ℝ) * E ^ 3 :=
    mul_nonneg (by norm_num only) (pow_nonneg hE.le 3)
  have hRlowerSq := pow_le_pow_left₀ hRlowerNonneg hRlower 2
  have hlowSq : (225 / 4096 : ℝ) * E ^ 6 ≤ p ^ 6 * R ^ 2 := by nlinarith only [hRlowerSq]
  have hRscaled := mul_le_mul_of_nonneg_left hR (pow_nonneg hp.le 4)
  have hcombined :
    (225 / 4096 : ℝ) * E ^ 6 ≤
      p ^ 4 * (4 * T * E * B ^ 2 + 65536 * T * p ^ 3 * Real.sqrt E * M ^ 2 * B) := by
    nlinarith only [hlowSq, hRscaled]
  have hBsquare := pow_le_pow_left₀ hB.le hBupper 2
  have hmainCoeff : 0 ≤ 4 * T * E * p ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hT) hE.le) (pow_nonneg hp.le 4)
  have hmainBound : p ^ 4 * (4 * T * E * B ^ 2) ≤ 4 * T * E ^ 3 * p ^ 4 := by
    calc
      p ^ 4 * (4 * T * E * B ^ 2) = (4 * T * E * p ^ 4) * B ^ 2 := by ring
      _ ≤ (4 * T * E * p ^ 4) * E ^ 2 := mul_le_mul_of_nonneg_left hBsquare hmainCoeff
      _ = 4 * T * E ^ 3 * p ^ 4 := by ring
  have herrCoeff : 0 ≤ 65536 * T * p ^ 7 * Real.sqrt E * M ^ 2 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 65536) hT) (pow_nonneg hp.le 7))
        (Real.sqrt_nonneg E))
      (sq_nonneg M)
  have herrBound :
    p ^ 4 * (65536 * T * p ^ 3 * Real.sqrt E * M ^ 2 * B) ≤
      65536 * T * p ^ 7 * Real.sqrt E * M ^ 2 * E := by
    calc
      p ^ 4 * (65536 * T * p ^ 3 * Real.sqrt E * M ^ 2 * B) =
          (65536 * T * p ^ 7 * Real.sqrt E * M ^ 2) * B :=
        by ring
      _ ≤ (65536 * T * p ^ 7 * Real.sqrt E * M ^ 2) * E :=
        mul_le_mul_of_nonneg_left hBupper herrCoeff
  have hbudget :
    (225 / 4096 : ℝ) * E ^ 6 ≤
      4 * T * E ^ 3 * p ^ 4 + 65536 * T * p ^ 7 * Real.sqrt E * M ^ 2 * E := by
    nlinarith only [hcombined, hmainBound, herrBound]
  by_cases hmain : (135 / 4096 : ℝ) * E ^ 6 ≤ 4 * T * E ^ 3 * p ^ 4
  · left
    have hmainProd : ((135 / 4096 : ℝ) * E ^ 3) * E ^ 3 ≤ (4 * T * p ^ 4) * E ^ 3 := by
      nlinarith only [hmain]
    have hmainCancel := (mul_le_mul_iff_left₀ (pow_pos hE 3)).mp hmainProd
    have hconst : (4 : ℝ) ≤ (135 / 4096) * 128 := by norm_num only
    have hscaleConst := mul_le_mul_of_nonneg_right hconst (mul_nonneg hT (pow_nonneg hp.le 4))
    nlinarith only [hmainCancel, hscaleConst]
  right
  have hmainLt : 4 * T * E ^ 3 * p ^ 4 < (135 / 4096 : ℝ) * E ^ 6 := lt_of_not_ge hmain
  have herrLower : (45 / 2048 : ℝ) * E ^ 6 ≤ 65536 * T * p ^ 7 * Real.sqrt E * M ^ 2 * E := by
    nlinarith only [hbudget, hmainLt]
  have hsqrtPos : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hsqrtSq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE.le
  have hcutFourth := pow_le_pow_left₀ (mul_nonneg hM hE.le) hcut 4
  have hcutFourth' : M ^ 4 * E ^ 4 ≤ 2 ^ 88 * p ^ 12 := by nlinarith only [hcutFourth]
  have hpowid : E ^ 6 = (E ^ 4 * Real.sqrt E) * (E * Real.sqrt E) := by
    calc
      E ^ 6 = E ^ 5 * (Real.sqrt E) ^ 2 := by
        rw [hsqrtSq]; ring
      _ = (E ^ 4 * Real.sqrt E) * (E * Real.sqrt E) := by ring
  have hErrProd :
    ((45 / 2048 : ℝ) * E ^ 4 * Real.sqrt E) * (E * Real.sqrt E) ≤
      (65536 * T * p ^ 7 * M ^ 2) * (E * Real.sqrt E) := by
    calc
      ((45 / 2048 : ℝ) * E ^ 4 * Real.sqrt E) * (E * Real.sqrt E) = (45 / 2048 : ℝ) * E ^ 6 := by
        calc
          _ = (45 / 2048 : ℝ) * ((E ^ 4 * Real.sqrt E) * (E * Real.sqrt E)) := by ring
          _ = (45 / 2048 : ℝ) * E ^ 6 := by rw [← hpowid]
      _ ≤ 65536 * T * p ^ 7 * Real.sqrt E * M ^ 2 * E := herrLower
      _ = (65536 * T * p ^ 7 * M ^ 2) * (E * Real.sqrt E) := by ring
  have hfactorPos : 0 < E * Real.sqrt E := mul_pos hE hsqrtPos
  have hErrCancel := (mul_le_mul_iff_left₀ hfactorPos).mp hErrProd
  have hErrCancelNonneg : 0 ≤ (45 / 2048 : ℝ) * E ^ 4 * Real.sqrt E :=
    mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg hE.le 4)) hsqrtPos.le
  have hErrCancelSq := pow_le_pow_left₀ hErrCancelNonneg hErrCancel 2
  have hcancelLeft : (45 / 2048 : ℝ) ^ 2 * E ^ 9 = ((45 / 2048 : ℝ) * E ^ 4 * Real.sqrt E) ^ 2 := by
    calc
      _ = (45 / 2048 : ℝ) ^ 2 * E ^ 8 * E := by ring
      _ = (45 / 2048 : ℝ) ^ 2 * E ^ 8 * (Real.sqrt E) ^ 2 := by rw [hsqrtSq]
      _ = _ := by ring
  have hcancelRight : (65536 * T * p ^ 7 * M ^ 2) ^ 2 = 2 ^ 32 * T ^ 2 * p ^ 14 * M ^ 4 := by ring
  have hcancelSq : (45 / 2048 : ℝ) ^ 2 * E ^ 9 ≤ 2 ^ 32 * T ^ 2 * p ^ 14 * M ^ 4 := by
    calc
      _ = ((45 / 2048 : ℝ) * E ^ 4 * Real.sqrt E) ^ 2 := hcancelLeft
      _ ≤ (65536 * T * p ^ 7 * M ^ 2) ^ 2 := hErrCancelSq
      _ = _ := hcancelRight
  have hcancelSqE4 := mul_le_mul_of_nonneg_right hcancelSq (pow_nonneg hE.le 4)
  have hcutScale : 2 ^ 32 * T ^ 2 * p ^ 14 * M ^ 4 * E ^ 4 ≤ 2 ^ 120 * T ^ 2 * p ^ 26 := by
    calc
      2 ^ 32 * T ^ 2 * p ^ 14 * M ^ 4 * E ^ 4 = (2 ^ 32 * T ^ 2 * p ^ 14) * (M ^ 4 * E ^ 4) := by
        ring
      _ ≤ (2 ^ 32 * T ^ 2 * p ^ 14) * (2 ^ 88 * p ^ 12) :=
        mul_le_mul_of_nonneg_left hcutFourth'
          (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) 32) (sq_nonneg T))
            (pow_nonneg hp.le 14))
      _ = 2 ^ 120 * T ^ 2 * p ^ 26 := by ring
  have hscaledFinal : (45 / 2048 : ℝ) ^ 2 * E ^ 13 ≤ 2 ^ 120 * T ^ 2 * p ^ 26 := by
    calc
      _ = ((45 / 2048 : ℝ) ^ 2 * E ^ 9) * E ^ 4 := by ring
      _ ≤ (2 ^ 32 * T ^ 2 * p ^ 14 * M ^ 4) * E ^ 4 := hcancelSqE4
      _ ≤ 2 ^ 120 * T ^ 2 * p ^ 26 := hcutScale
  have hcoeff : 2 ^ 120 ≤ (45 / 2048 : ℝ) ^ 2 * 2 ^ 132 := by norm_num only
  have hcoeffScaled :=
    mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (sq_nonneg T) (pow_nonneg hp.le 26))
  have hfinal : (45 / 2048 : ℝ) ^ 2 * E ^ 13 ≤ (45 / 2048 : ℝ) ^ 2 * 2 ^ 132 * T ^ 2 * p ^ 26 := by
    calc
      _ ≤ 2 ^ 120 * T ^ 2 * p ^ 26 := hscaledFinal
      _ ≤ (45 / 2048 : ℝ) ^ 2 * 2 ^ 132 * T ^ 2 * p ^ 26 := by nlinarith only [hcoeffScaled]
  have hcoeffPos : 0 < (45 / 2048 : ℝ) ^ 2 := by norm_num only
  exact (mul_le_mul_iff_left₀ hcoeffPos).mp (by nlinarith only [hfinal])

/-- The three alternatives imply the log-square energy target when the full
energy is at most p³ and the third moment is at most 2²⁰p³L. The cubic
branches are raised to the fourth power and use L²≤4p; the final branch uses
the third-moment bound directly. -/
theorem truncated_weight_alternatives_log_square_budget {p E T L : ℝ} (hp : 1 ≤ p) (hE : 0 ≤ E)
    (hT0 : 0 ≤ T) (hL : 1 ≤ L) (hEp : E ≤ p ^ 3) (hT : T ≤ 2 ^ 20 * p ^ 3 * L) (hL2 : L ^ 2 ≤ 4 * p)
    (halt :
      E ^ 3 ≤ 2 ^ 28 * p ^ 7 ∨ E ^ 3 ≤ 2 ^ 7 * p ^ 4 * T ∨ E ^ 13 ≤ 2 ^ 132 * p ^ 26 * T ^ 2) :
    E ^ 13 ≤ 2 ^ 176 * p ^ 32 * L ^ 2 := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  rcases halt with hsmall | hmain | herr
  · have hsmallPow := pow_le_pow_left₀ (pow_nonneg hE 3) hsmall 4
    have hsmallMul :=
      mul_le_mul hsmallPow hEp hE
        (pow_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 28) (pow_nonneg hp0 7)) 4)
    have hsmallBase : E ^ 13 ≤ 2 ^ 112 * p ^ 31 := by nlinarith only [hsmallMul]
    have hp31 : p ^ 31 ≤ p ^ 32 := pow_le_pow_right₀ hp (by decide : 31 ≤ 32)
    have hscale : 2 ^ 112 * p ^ 31 ≤ 2 ^ 176 * p ^ 32 * L ^ 2 := by
      calc
        2 ^ 112 * p ^ 31 ≤ 2 ^ 112 * p ^ 32 := mul_le_mul_of_nonneg_left hp31 (by norm_num only)
        _ ≤ 2 ^ 176 * p ^ 32 := by
          exact
            mul_le_mul_of_nonneg_right (by norm_num only : (2 : ℝ) ^ 112 ≤ 2 ^ 176)
              (pow_nonneg hp0 32)
        _ ≤ 2 ^ 176 * p ^ 32 * L ^ 2 := by
          have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL (n := 2)
          exact le_mul_of_one_le_right (mul_nonneg (by norm_num only) (pow_nonneg hp0 32)) hLsq
    exact hsmallBase.trans hscale
  · have hmainBound : E ^ 3 ≤ 2 ^ 27 * p ^ 7 * L := by
      calc
        E ^ 3 ≤ 2 ^ 7 * p ^ 4 * T := hmain
        _ ≤ 2 ^ 7 * p ^ 4 * (2 ^ 20 * p ^ 3 * L) :=
          mul_le_mul_of_nonneg_left hT (mul_nonneg (by norm_num only) (pow_nonneg hp0 4))
        _ = 2 ^ 27 * p ^ 7 * L := by ring
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hmainPow := pow_le_pow_left₀ (pow_nonneg hE 3) hmainBound 4
    have hmainMul :=
      mul_le_mul hmainPow hEp hE
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg hp0 7)) hL0) 4)
    have hmainBase : E ^ 13 ≤ 2 ^ 108 * p ^ 31 * L ^ 4 := by nlinarith only [hmainMul]
    have hmainAbsorb : 2 ^ 108 * p ^ 31 * L ^ 4 ≤ 2 ^ 110 * p ^ 32 * L ^ 2 := by
      calc
        2 ^ 108 * p ^ 31 * L ^ 4 = (2 ^ 108 * p ^ 31 * L ^ 2) * L ^ 2 := by ring
        _ ≤ (2 ^ 108 * p ^ 31 * L ^ 2) * (4 * p) :=
          mul_le_mul_of_nonneg_left hL2
            (mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg hp0 31)) (pow_nonneg hL0 2))
        _ = 2 ^ 110 * p ^ 32 * L ^ 2 := by ring
    have hcoeff : 2 ^ 110 * p ^ 32 * L ^ 2 ≤ 2 ^ 176 * p ^ 32 * L ^ 2 := by
      have hc : (2 : ℝ) ^ 110 ≤ 2 ^ 176 :=
        pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 2) (by decide : 110 ≤ 176)
      have hprod : 0 ≤ p ^ 32 * L ^ 2 := mul_nonneg (pow_nonneg hp0 32) (pow_nonneg hL0 2)
      calc
        2 ^ 110 * p ^ 32 * L ^ 2 = 2 ^ 110 * (p ^ 32 * L ^ 2) := by ring
        _ ≤ 2 ^ 176 * (p ^ 32 * L ^ 2) := mul_le_mul_of_nonneg_right hc hprod
        _ = 2 ^ 176 * p ^ 32 * L ^ 2 := by ring
    exact hmainBase.trans (hmainAbsorb.trans hcoeff)
  · have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hT2 := pow_le_pow_left₀ hT0 hT 2
    have hT2' : T ^ 2 ≤ 2 ^ 40 * p ^ 6 * L ^ 2 := by
      calc
        T ^ 2 ≤ (2 ^ 20 * p ^ 3 * L) ^ 2 := hT2
        _ = 2 ^ 40 * p ^ 6 * L ^ 2 := by ring
    have herrBound : 2 ^ 132 * p ^ 26 * T ^ 2 ≤ 2 ^ 172 * p ^ 32 * L ^ 2 := by
      have hTweighted :=
        mul_le_mul_of_nonneg_left hT2'
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 132) (pow_nonneg hp0 26))
      have hTnormalize :
        2 ^ 132 * p ^ 26 * (2 ^ 40 * p ^ 6 * L ^ 2) = 2 ^ 172 * p ^ 32 * L ^ 2 := by
        calc
          _ = (2 ^ 132 * 2 ^ 40) * (p ^ 26 * p ^ 6) * L ^ 2 := by ring
          _ = 2 ^ 172 * p ^ 32 * L ^ 2 := by rw [← pow_add, ← pow_add]
      have hTweighted' : 2 ^ 132 * p ^ 26 * T ^ 2 ≤ 2 ^ 172 * p ^ 32 * L ^ 2 :=
        hTweighted.trans (le_of_eq hTnormalize)
      have hc : (2 : ℝ) ^ 172 ≤ 2 ^ 176 :=
        pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 2) (by decide : 172 ≤ 176)
      have hprod : 0 ≤ p ^ 32 * L ^ 2 := mul_nonneg (pow_nonneg hp0 32) (pow_nonneg hL0 2)
      have hcoeff := mul_le_mul_of_nonneg_right hc hprod
      have hcoeff' : 2 ^ 172 * p ^ 32 * L ^ 2 ≤ 2 ^ 176 * p ^ 32 * L ^ 2 := by
        calc
          _ = 2 ^ 172 * (p ^ 32 * L ^ 2) := by ring
          _ ≤ 2 ^ 176 * (p ^ 32 * L ^ 2) := hcoeff
          _ = _ := by ring
      nlinarith only [hTweighted', hcoeff']
    have hfinalScale : 2 ^ 172 * p ^ 32 * L ^ 2 ≤ 2 ^ 176 * p ^ 32 * L ^ 2 := by
      have hc : (2 : ℝ) ^ 172 ≤ 2 ^ 176 :=
        pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 2) (by decide : 172 ≤ 176)
      have hprod : 0 ≤ p ^ 32 * L ^ 2 := mul_nonneg (pow_nonneg hp0 32) (pow_nonneg hL0 2)
      have hcoeff := mul_le_mul_of_nonneg_right hc hprod
      calc
        2 ^ 172 * p ^ 32 * L ^ 2 = 2 ^ 172 * (p ^ 32 * L ^ 2) := by ring
        _ ≤ 2 ^ 176 * (p ^ 32 * L ^ 2) := hcoeff
        _ = 2 ^ 176 * p ^ 32 * L ^ 2 := by ring
    nlinarith only [herr, herrBound, hfinalScale]

end PseudoPrime.Analysis
