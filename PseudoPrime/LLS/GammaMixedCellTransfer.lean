/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedProfileDualBounds

/-! # Generic transfer from mixed prime-row certificates to actual profile dual budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: sqrt x<=r and 1+(71/25)r<=K. Claim: the anchored support is included
in the prime filter of [3,K]. Proof: compare the real cutoff and its natural floor.
Role: verify finite support coverage at arbitrary scale-cell endpoints. -/
theorem gamma_anchored_support_subset_of_root_cap {x r : ℝ} {K : ℕ} (hroot : Real.sqrt x ≤ r)
    (hcap : 1 + (71 / 25 : ℝ) * r ≤ K) :
    gammaAnchoredSupportPrimeSet x ⊆ (Finset.Icc 3 K).filter Nat.Prime := by
  intro p hp
  obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
  obtain ⟨h3, hb⟩ := Finset.mem_Icc.mp hi
  have hf : (⌊1 + (71 / 25 : ℝ) * Real.sqrt x⌋₊ : ℝ) ≤ 1 + (71 / 25 : ℝ) * Real.sqrt x :=
    Nat.floor_le (by nlinarith only [Real.sqrt_nonneg x])
  have hpR := (Nat.cast_le (α := ℝ)).mpr hb
  have hbound : (p : ℝ) ≤ K := by linarith only [hpR, hf, hroot, hcap]
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, Nat.cast_le.mp hbound⟩, hp⟩

/-- Input: a checked cell at price 5/4, a support cap, checked mixed rows and a rational sum cap.
Claim: the actual signed dual excess sum obeys that cap throughout the cell.
Proof: combine row soundness, exact support inclusion and nonnegative summands.
Role: reuse numerical certificates without repeating the actual-character arithmetic. -/
theorem gamma_signed_excess_le_of_profile_certificate (c : Analysis.GammaLocalCellData) (K : ℕ)
    (C : ℚ) (hc : c.check = true) (htheta : c.theta = 5 / 4)
    (hcap : (1 + (71 / 25 : ℚ) * c.rootHi) ≤ K)
    (hrows :
      ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
        (Analysis.gammaProfileEnvelopeRow c p).envelopeCheck c = true)
    (hsum :
      (∑ p ∈ (Finset.Icc 3 K).filter Nat.Prime, (Analysis.gammaProfileEnvelopeRow c p).allowance) ≤
        C)
    {x : ℝ} (hlo : (c.lo : ℝ) ≤ x) (hhi : x ≤ (c.hi : ℝ)) :
    (∑ p ∈ gammaAnchoredSupportPrimeSet x,
        Real.log p *
          max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
            0) ≤
      (C : ℝ) := by
  let R := (Finset.Icc 3 K).filter Nat.Prime
  let row := Analysis.gammaProfileEnvelopeRow c
  have hE : ∀ p ∈ R, Analysis.gammaPrimeEulerCost p ≤ ((row p).eulerUpper : ℝ) := by
    intro p hp
    exact
      Analysis.gamma_mixed_euler_upper_sound (Finset.mem_filter.mp hp).2
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hs :=
    Analysis.gamma_envelope_prime_sum_upper R row c hc (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun p hp ↦ rfl) hrows hE hlo hhi
  have hthetaR : (c.theta : ℝ) = 5 / 4 := by
    rw [htheta]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have heq :
    Analysis.gammaRamifiedThetaParameter (5 / 4) x = Analysis.gammaRamifiedDualParameter x := by
    dsimp only [Analysis.gammaRamifiedThetaParameter, Analysis.gammaRamifiedDualParameter]
    rw [div_div]
  rw [hthetaR, heq] at hs
  have hfull := hs.trans ((Rat.cast_le (K := ℝ)).mpr hsum)
  obtain ⟨hlo0, horder, hrlo0, hrlo, hrhi0, hrhi, hth0⟩ := c.check_sound hc
  have hroot := (Real.sqrt_le_sqrt hhi).trans hrhi
  have hcapR := (Rat.cast_le (K := ℝ)).mpr hcap
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_natCast] at hcapR
  have hsub := gamma_anchored_support_subset_of_root_cap hroot hcapR
  have hext :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun p : ℕ ↦
      Real.log p *
        max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
          0)
      (fun p hp _ ↦
        mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
          (le_max_right _ _))
  exact hext.trans hfull

/-- Input: rational profile endpoints above 300, a checked cell, support/row/sum certificates,
and a real L between the endpoints. Claim: the actual dual budget is at most 2+C.
Proof: retain the coupled linear price and transfer the certified excess cell.
Role: connect arbitrary compact bridge certificates to the profile separation. -/
theorem gamma_profile_dual_le_of_certificate (a b C : ℚ) (K : ℕ) (ha : (300 : ℝ) ≤ a)
    (hc : (Analysis.gammaProfileEnvelopeCell a b).check = true)
    (hcap : (1 + (71 / 25 : ℚ) * (Analysis.gammaProfileEnvelopeCell a b).rootHi) ≤ K)
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
  have he := gamma_signed_excess_le_of_profile_certificate c K C hc rfl hcap hrows hsum hlox hxhic
  have hp := gamma_quadratic_profile_price_le_two hL0
  have hsq := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 300 by linarith only [hL])
  have hx100 : (100 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hsq]
  change gammaScaleSignedDualBudget L x ≤ 2 + (C : ℝ)
  rw [gamma_scale_signed_dual_budget_eq_anchored_support L hx100]
  linarith only [hp, he]

end PseudoPrime.LLS
