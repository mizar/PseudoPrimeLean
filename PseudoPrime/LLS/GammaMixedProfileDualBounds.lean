/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaAnchoredSupportBudget
public import PseudoPrime.Analysis.GammaMixedEulerCells

/-! # Certified actual dual costs on the logarithmic profile cell [300,310] -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: sqrt x<=1963/10. Claim: all anchored-support primes lie between 3 and 559.
Proof: compare the natural floor with the root cutoff. Role: certify complete finite support. -/
theorem gamma_anchored_support_subset_559 {x : ℝ} (hroot : Real.sqrt x ≤ (1963 / 10 : ℝ)) :
    gammaAnchoredSupportPrimeSet x ⊆ (Finset.Icc 3 559).filter Nat.Prime := by
  intro p hp
  obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
  obtain ⟨h3, hb⟩ := Finset.mem_Icc.mp hi
  have hfloor : (⌊1 + (71 / 25 : ℝ) * Real.sqrt x⌋₊ : ℝ) ≤ 1 + (71 / 25 : ℝ) * Real.sqrt x :=
    Nat.floor_le (by nlinarith only [Real.sqrt_nonneg x])
  have hpR := (Nat.cast_le (α := ℝ)).mpr hb
  have hbound : (p : ℝ) ≤ 559 := by linarith only [hpR, hfloor, hroot]
  have hp559 : p ≤ 559 := by exact_mod_cast hbound
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hp559⟩, hp⟩

/-- Input: L>0. Claim: the variable dual price times L is at most two at x=(2/5)L^2.
Proof: use the coupled square-root lower bound before dividing.
Role: avoid independent endpoint losses in the linear part of a profile cell. -/
theorem gamma_quadratic_profile_price_le_two {L : ℝ} (hL : 0 < L) :
    Analysis.gammaRamifiedDualParameter ((2 / 5 : ℝ) * L ^ 2) * L ≤ 2 := by
  have hx : 0 < (2 / 5 : ℝ) * L ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hL)
  have hr : (5 / 8 : ℝ) * L ≤ Real.sqrt ((2 / 5 : ℝ) * L ^ 2) := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL.le) hx.le).mpr
    nlinarith only [sq_nonneg L]
  dsimp only [Analysis.gammaRamifiedDualParameter]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hx))).mpr
  linarith only [hr]

/-- Input: 36000<=x<=38440. Claim: the actual signed anchored excess sum is at most 47/10.
Proof: validate all mixed Euler rows, sum their allowances and prove support coverage.
Role: discharge a numerical dual-excess obligation throughout a closed scale interval. -/
theorem gamma_profile_excess_le_300_310 {x : ℝ} (hxlo : 36000 ≤ x) (hxhi : x ≤ 38440) :
    (∑ p ∈ gammaAnchoredSupportPrimeSet x,
        Real.log p *
          max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
            0) ≤
      (47 / 10 : ℝ) := by
  let c := Analysis.gammaProfileEnvelopeCell 300 310
  let R := (Finset.Icc 3 559).filter Nat.Prime
  let row := Analysis.gammaProfileEnvelopeRow c
  have hlox : (c.lo : ℝ) ≤ x := by
    norm_num only [c, Analysis.gammaProfileEnvelopeCell, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat]
    exact hxlo
  have hxhic : x ≤ (c.hi : ℝ) := by
    norm_num only [c, Analysis.gammaProfileEnvelopeCell, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat]
    exact hxhi
  have hE : ∀ p ∈ R, Analysis.gammaPrimeEulerCost p ≤ ((row p).eulerUpper : ℝ) := by
    intro p hp
    exact
      Analysis.gamma_mixed_euler_upper_sound (Finset.mem_filter.mp hp).2
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hs :=
    Analysis.gamma_envelope_prime_sum_upper R row c Analysis.gamma_profile_cell_300_310_check
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) (fun p hp ↦ rfl)
      Analysis.gamma_profile_rows_300_310_check hE hlox hxhic
  have htheta : (c.theta : ℝ) = 5 / 4 := by
    norm_num only [c, Analysis.gammaProfileEnvelopeCell, Rat.cast_div, Rat.cast_ofNat]
  have heq :
    Analysis.gammaRamifiedThetaParameter (5 / 4) x = Analysis.gammaRamifiedDualParameter x := by
    dsimp only [Analysis.gammaRamifiedThetaParameter, Analysis.gammaRamifiedDualParameter]
    rw [div_div]
  rw [htheta, heq] at hs
  have hcap := (Rat.cast_le (K := ℝ)).mpr Analysis.gamma_profile_sum_300_310_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hcap
  have hfull :
    (∑ p ∈ R,
        Real.log p *
          max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
            0) ≤
      (47 / 10 : ℝ) :=
    hs.trans hcap
  have hroot : Real.sqrt x ≤ (1963 / 10 : ℝ) :=
    (Real.sqrt_le_iff).mpr
      ⟨by norm_num only, hxhi.trans (by norm_num only : (38440 : ℝ) ≤ (1963 / 10 : ℝ) ^ 2)⟩
  have hsub := gamma_anchored_support_subset_559 hroot
  have hext :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun p : ℕ ↦
      Real.log p *
        max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
          0)
      (fun p hp _ ↦
        mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
          (le_max_right _ _))
  exact hext.trans hfull

/-- Input: 300<=L<=310. Claim: the actual profile dual budget is at most 67/10.
Proof: combine the coupled price bound with the checked excess sum.
Role: provide a fully certified numerical dual cap for this logarithmic cell. -/
theorem gamma_profile_dual_le_300_310 {L : ℝ} (hlo : 300 ≤ L) (hhi : L ≤ 310) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ (67 / 10 : ℝ) := by
  have hlow := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 300 by linarith only [hlo])
  have hupp := mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ L + 310 by linarith only [hlo])
  have hxlo : (36000 : ℝ) ≤ (2 / 5 : ℝ) * L ^ 2 := by nlinarith only [hlow]
  have hxhi : (2 / 5 : ℝ) * L ^ 2 ≤ 38440 := by nlinarith only [hupp]
  have hp := gamma_quadratic_profile_price_le_two (show 0 < L by linarith only [hlo])
  have he := gamma_profile_excess_le_300_310 hxlo hxhi
  rw [gamma_scale_signed_dual_budget_eq_anchored_support L (by linarith only [hxlo])]
  linarith only [hp, he]

/-- Input: RH, odd nonsquare n, log n<=L and 300<=L<=310.
Claim: the actual Jacobi joint budget has the displayed explicit profile bound.
Proof: combine the prefix half-line theorem and the certified dual cap.
Role: leave only the principal, ramp and pole separation arithmetic for witness extraction. -/
theorem gamma_joint_profile_bound_300_310 (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hlo : 300 ≤ L) (hhi : L ≤ 310) (hlog : Real.log n ≤ L) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn)
        ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + 67 / 10 - 28923 / 2500 + 7 / 60 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 300 by linarith only [hlo])
  have hb : (89100 : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 := by nlinarith only [hsq]
  have hx : (4096 : ℝ) ≤ (2 / 5 : ℝ) * L ^ 2 := by nlinarith only [hsq]
  exact
    gamma_joint_prefix89100_bound_halfline hRH hn hns hb hlog hx
      (gamma_profile_dual_le_300_310 hlo hhi)

end PseudoPrime.LLS
