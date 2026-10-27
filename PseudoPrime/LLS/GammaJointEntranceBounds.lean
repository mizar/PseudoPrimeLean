/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaJointWindowTransport
public import PseudoPrime.LLS.GammaTransportedEntranceBounds

/-! # Log-255 entrance from unchanged local rows and the joint arithmetic saving -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Left scale (101/250)*255^2 for transport of the already checked log-260 cell.
This rational endpoint adds no prime-row or input-integer certificate. -/
def gammaJointEntranceLo : ℚ :=
  (101 / 250) * 255 ^ 2

/-- Rational lower square root (1589/2500)*255 of the lowered left scale.
The reusable window transport uses its positivity and square comparison. -/
def gammaJointEntranceRoot : ℚ :=
  (1589 / 2500) * 255

/-- The unchanged prime-row factory, with lowered rational endpoints, has total
allowance at most 769/200 on odd primes through 350. Check the aggregate
with kernel rational arithmetic; no new prime-specific data are generated. -/
theorem gamma_joint_entrance_allowance_sum :
    (∑ p ∈ (Finset.Icc 3 350).filter Nat.Prime,
        loweredPrimeAllowance gammaTransportedOldCell gammaTransportedRow gammaJointEntranceLo
          gammaJointEntranceRoot p) ≤
      (769 / 200 : ℚ) := by
  decide +kernel

/-- For nonnegative L and scales in the lowered old window, the actual signed
dual budget is at most 5L/(4root)+769/200. Apply the reusable allowance
transport with the old row checks and certified Euler caps. -/
theorem gamma_joint_entrance_dual_cap {L x : ℝ} (hL : 0 ≤ L) (hlo : (gammaJointEntranceLo : ℝ) ≤ x)
    (hhi : x ≤ (gammaTransportedOldCell.hi : ℝ)) :
    gammaScaleSignedDualBudget L x ≤ (5 / (4 * ((1589 / 2500 : ℝ) * 255))) * L + 769 / 200 := by
  have he (p : ℕ) (hp : p ∈ Analysis.gammaAnchoredWindowPrimeSet gammaTransportedOldCell.hi) :
    Analysis.gammaPrimeEulerCost p ≤ ((gammaTransportedRow p).eulerUpper : ℝ) :=
    Analysis.gamma_adaptive_euler_upper_sound (Finset.mem_filter.mp hp).2
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hsum :
    (∑ p ∈ (Finset.Icc 3 350).filter Nat.Prime,
        loweredPrimeAllowance gammaTransportedOldCell gammaTransportedRow gammaJointEntranceLo
          gammaJointEntranceRoot p) ≤
      (769 / 200 : ℚ) :=
    gamma_joint_entrance_allowance_sum
  have h :=
    loweredPrimeAllowance_dual_cap gammaTransportedOldCell gammaTransportedRow
      gamma_transported_geometry.1 (show 0 < gammaJointEntranceRoot by decide +kernel)
      (show gammaJointEntranceRoot ^ 2 ≤ gammaJointEntranceLo by decide +kernel)
      (show 1 ≤ gammaJointEntranceLo by decide +kernel)
      (show gammaJointEntranceLo ≤ gammaTransportedOldCell.lo by decide +kernel)
      (show gammaJointEntranceLo ≤ gammaTransportedOldCell.hi by decide +kernel)
      ((Finset.Icc 3 350).filter Nat.Prime) gamma_transported_support_subset
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) gamma_transported_row_check he hsum hL hlo hhi
  norm_num only [gammaJointEntranceRoot, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at h
  norm_num only at h ⊢
  exact h

/-- Effective prefix credit after the transferred local costs and the 7/60
comparison allowance, retaining a joint gain of 1/3. Used in the generic
paired polynomial condition at the log-255 profile. -/
noncomputable def gammaJointEntranceCredit (L : ℝ) : ℝ :=
  28493 / 5000 -
    (3 / 4 + ((5 / (4 * ((1589 / 2500 : ℝ) * 255))) * L + 769 / 200) + 7 / 60 - 1 / 3) / 2

/-- For 255<=L<=260 the scale (101/250)L^2 lies in the transferred window,
exceeds 4096, contains prefix 50000 and lies in [16384,27556].
Exact rational geometry supplies every analytic comparison gate. -/
theorem gamma_joint_entrance_profile_inputs {L : ℝ} (hL : 255 ≤ L) (hU : L ≤ 260) :
    let x := (101 / 250 : ℝ) * L ^ 2;
    (gammaJointEntranceLo : ℝ) ≤ x ∧
      x ≤ (gammaTransportedOldCell.hi : ℝ) ∧
      4096 ≤ x ∧ 50000 ≤ (99 / 40 : ℝ) * x ∧ 16384 ≤ x ∧ x ≤ 27556 := by
  dsimp only
  have hlow := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 255 by linarith only [hL])
  have hupp := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ 260 + L by linarith only [hL])
  have hlo : (gammaJointEntranceLo : ℝ) ≤ (101 / 250 : ℝ) * L ^ 2 := by
    norm_num only [gammaJointEntranceLo, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
    nlinarith only [hlow]
  have htop : (101 / 250 : ℝ) * 260 ^ 2 ≤ (gammaTransportedOldCell.hi : ℝ) := by
    have hq :=
      Rat.cast_le (K := ℝ) |>.mpr
        (show (101 / 250 : ℚ) * 260 ^ 2 ≤ gammaTransportedOldCell.hi by decide +kernel)
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hq
    norm_num only at hq ⊢
    exact hq
  have hh : (101 / 250 : ℝ) * L ^ 2 ≤ (gammaTransportedOldCell.hi : ℝ) := by
    nlinarith only [hupp, htop]
  have hloN : (101 / 250 : ℝ) * 255 ^ 2 ≤ (101 / 250 : ℝ) * L ^ 2 := by nlinarith only [hlow]
  refine ⟨hlo, hh, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hloN]
  · nlinarith only [hloN]
  · nlinarith only [hloN]
  · nlinarith only [hupp]

/-- For all L>=255 the shared paired polynomial holds with the retained joint
credit. Bound the square root rationally and the logarithm by its tangent
at 260, then prove a positive rational quadratic in L-255. -/
theorem gamma_joint_entrance_polynomial {L : ℝ} (hL : 255 ≤ L) :
    GammaPairedPolynomialCondition (L + 7 / 5) ((101 / 250 : ℝ) * L ^ 2)
      (gammaJointEntranceCredit L) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hr : Real.sqrt ((101 / 250 : ℝ) * L ^ 2) ≤ (63561 / 100000 : ℝ) * L := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith only [hL], by nlinarith only [sq_nonneg L]⟩
  have hc : Analysis.rationalLogIntervalCheck 260 9 16 5 (55607 / 10000) = true := by decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 260) hL0
  have hlL : Real.log L ≤ (L - 260) / 260 + 55607 / 10000 := by linarith only [hl, ht]
  have hlog : Real.log ((101 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2)) ≤ L / 130 + 18283 / 2000 := by
    rw [show (101 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) = (10201 / 10000 : ℝ) * L ^ 2 by ring,
      Real.log_mul (by norm_num only) (sq_pos_of_pos hL0).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have he := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 10201 / 10000)
    linarith only [hlL, he]
  refine ⟨(63561 / 100000 : ℝ) * L, L / 130 + 18283 / 2000, hr, hlog, ?_, ?_⟩
  · dsimp only [gammaJointEntranceCredit]
    linarith only [hL]
  · dsimp only [gammaJointEntranceCredit]
    nlinarith only [hL, sq_nonneg (L - 255)]

/-- Under RH and 255<=L<=260 the factor-free joint margin at scale
(101/250)L^2 and prefix 50000 exceeds 7/60. Combine transferred local costs,
the existing analytic Euler-prefix lower bound and the joint gain 1/3. -/
theorem gamma_joint_entrance_separation (hRH : RiemannHypothesis) {L : ℝ} (hL : 255 ≤ L)
    (hU : L ≤ 260) : 7 / 60 < gammaJointFactorFreeSeparation L 50000 ((101 / 250 : ℝ) * L ^ 2) := by
  obtain ⟨hlo, hhi, hx, hb, hlow, hupp⟩ := gamma_joint_entrance_profile_inputs hL hU
  have hd := gamma_joint_entrance_dual_cap (by linarith only [hL] : 0 ≤ L) hlo hhi
  have hp := gamma_prefix50000_lower_asymmetric hRH (le_refl (50000 : ℝ))
  have hc :
    gammaJointEntranceCredit L +
        (3 / 4 + ((5 / (4 * ((1589 / 2500 : ℝ) * 255))) * L + 769 / 200) + 7 / 60 - 1 / 3) / 2 ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    dsimp only [gammaJointEntranceCredit]
    linarith only [hp]
  exact
    gamma_joint_margin_gt_of_credited_polynomial (by linarith only [hx]) hc hd
      (gamma_joint_entrance_polynomial hL) (gamma_joint_gain_ge_one_third L 50000 hlow hupp)

end PseudoPrime.LLS
