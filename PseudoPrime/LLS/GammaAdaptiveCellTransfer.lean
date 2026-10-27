/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSmallProfileGeometry
public import PseudoPrime.Analysis.GammaAdaptiveProfileRows

/-! # Arbitrary-row and scale-parametric adaptive dual certificate transfer -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: any checked cell and matching prime rows, actual Euler bounds and a support/sum cap.
Claim: the actual signed dual excess obeys the cap throughout the cell.
Proof: row soundness, support inclusion and nonnegative extension.
Role: separate finite row validation from the choice of analytic Euler envelope. -/
theorem gamma_signed_excess_le_of_row_certificate (c : Analysis.GammaLocalCellData) (K : ℕ) (C : ℚ)
    (row : ℕ → Analysis.GammaLocalPrimeRow) (hc : c.check = true) (htheta : c.theta = 5 / 4)
    (hcap : (1 + (71 / 25 : ℚ) * c.rootHi) ≤ K)
    (hi : ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime, (row p).prime = p)
    (hE :
      ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
        Analysis.gammaPrimeEulerCost p ≤ ((row p).eulerUpper : ℝ))
    (hrows : ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime, (row p).envelopeCheck c = true)
    (hsum : (∑ p ∈ (Finset.Icc 3 K).filter Nat.Prime, (row p).allowance) ≤ C) {x : ℝ}
    (hlo : (c.lo : ℝ) ≤ x) (hhi : x ≤ (c.hi : ℝ)) :
    (∑ p ∈ gammaAnchoredSupportPrimeSet x,
        Real.log p *
          max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
            0) ≤
      (C : ℝ) := by
  let R := (Finset.Icc 3 K).filter Nat.Prime
  have hs :=
    Analysis.gamma_envelope_prime_sum_upper R row c hc (fun p hp ↦ (Finset.mem_filter.mp hp).2) hi
      hrows hE hlo hhi
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

/-- Input: positive scale, lower endpoint and root multiplier, its squared scale bound,
a checked cell and L inside it. Claim: the actual scale and roots obey the cell bounds,
including rlo*L<=sqrt(x). Proof: compare scaled squares.
Role: reuse geometry when changing the target witness coefficient. -/
theorem gamma_scaled_profile_geometry (s rlo rhi a b : ℚ) (hs : (0 : ℝ) < s) (ha : (0 : ℝ) < a)
    (hr : (0 : ℝ) < rlo) (hrsq : (rlo : ℝ) ^ 2 ≤ s)
    (hc : (Analysis.gammaScaledEnvelopeCell s rlo rhi a b).check = true) {L : ℝ} (hlo : (a : ℝ) ≤ L)
    (hhi : L ≤ (b : ℝ)) :
    let c := Analysis.gammaScaledEnvelopeCell s rlo rhi a b;
    let x := (s : ℝ) * L ^ 2;
    (c.lo : ℝ) ≤ x ∧
      x ≤ (c.hi : ℝ) ∧
      (c.rootLo : ℝ) ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (c.rootHi : ℝ) ∧ (rlo : ℝ) * L ≤ Real.sqrt x := by
  dsimp only
  let c := Analysis.gammaScaledEnvelopeCell s rlo rhi a b
  let x := (s : ℝ) * L ^ 2
  have hL : 0 < L := ha.trans_le hlo
  have hb : 0 ≤ (b : ℝ) := hL.le.trans hhi
  have hlprod := mul_nonneg hs.le (mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hL.le ha.le))
  have hhprod := mul_nonneg hs.le (mul_nonneg (sub_nonneg.mpr hhi) (add_nonneg hL.le hb))
  have hlox : (c.lo : ℝ) ≤ x := by
    norm_num only [c, Analysis.gammaScaledEnvelopeCell, Rat.cast_mul, Rat.cast_pow]
    dsimp only [x]
    nlinarith only [hlprod]
  have hxhi : x ≤ (c.hi : ℝ) := by
    norm_num only [c, Analysis.gammaScaledEnvelopeCell, Rat.cast_mul, Rat.cast_pow]
    dsimp only [x]
    nlinarith only [hhprod]
  have hx : 0 < x := mul_pos hs (sq_pos_of_pos hL)
  obtain ⟨_, _, _, hrlo, _, hrhi, _⟩ := c.check_sound hc
  have hroot : (rlo : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg hr.le hL.le) hx.le).mpr
    have hprod := mul_nonneg (sub_nonneg.mpr hrsq) (sq_nonneg L)
    dsimp only [x]
    nlinarith only [hprod]
  exact
    ⟨hlox, hxhi, hrlo.trans (Real.sqrt_le_sqrt hlox), (Real.sqrt_le_sqrt hxhi).trans hrhi, hroot⟩

/-- Input: x>0, r>0 and r*L<=sqrt(x). Claim: the coupled price is at most (5/4)/r.
Proof: multiply positive denominators and retain the coupled root bound.
Role: avoid rounding the price to two at every scale. -/
theorem gamma_scaled_profile_price_le {x L r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hroot : r * L ≤ Real.sqrt x) :
    Analysis.gammaRamifiedDualParameter x * L ≤ (5 / 4 : ℝ) / r := by
  unfold Analysis.gammaRamifiedDualParameter
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hx)) hr).mpr
  nlinarith only [hroot]

/-- Input: checked scale-parametric adaptive rows, support and excess caps and L in the cell.
Claim: the actual dual budget is at most (5/4)/rlo+C.
Proof: generic row transfer plus coupled price. Role: supply the actual dual bound
for coefficient-one and smaller-coefficient witness comparisons. -/
theorem gamma_scaled_adaptive_dual_le (s rlo rhi a b C : ℚ) (K : ℕ) (hs : (0 : ℝ) < s)
    (ha : (0 : ℝ) < a) (hr : (0 : ℝ) < rlo) (hrsq : (rlo : ℝ) ^ 2 ≤ s)
    (hc : (Analysis.gammaScaledEnvelopeCell s rlo rhi a b).check = true)
    (hmin : (100 : ℚ) ≤ (Analysis.gammaScaledEnvelopeCell s rlo rhi a b).lo)
    (hcap : 1 + (71 / 25 : ℚ) * (Analysis.gammaScaledEnvelopeCell s rlo rhi a b).rootHi ≤ K)
    (hrows :
      ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (Analysis.gammaScaledEnvelopeCell s rlo rhi a b)
                p).envelopeCheck
            (Analysis.gammaScaledEnvelopeCell s rlo rhi a b) =
          true)
    (hsum :
      (∑ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (Analysis.gammaScaledEnvelopeCell s rlo rhi a b)
              p).allowance) ≤
        C)
    {L : ℝ} (hlo : (a : ℝ) ≤ L) (hhi : L ≤ (b : ℝ)) :
    gammaScaleSignedDualBudget L ((s : ℝ) * L ^ 2) ≤ (5 / 4 : ℝ) / (rlo : ℝ) + (C : ℝ) := by
  let c := Analysis.gammaScaledEnvelopeCell s rlo rhi a b
  let row := Analysis.gammaAdaptiveProfileRow c
  let x := (s : ℝ) * L ^ 2
  obtain ⟨hlox, hxhi, _, _, hroot⟩ :=
    gamma_scaled_profile_geometry s rlo rhi a b hs ha hr hrsq hc hlo hhi
  have hE :
    ∀ p ∈ (Finset.Icc 3 K).filter Nat.Prime,
      Analysis.gammaPrimeEulerCost p ≤ ((row p).eulerUpper : ℝ) := by
    intro p hp
    exact
      Analysis.gamma_adaptive_euler_upper_sound (Finset.mem_filter.mp hp).2
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have he :=
    gamma_signed_excess_le_of_row_certificate c K C row hc rfl hcap (fun p hp ↦ rfl) hE hrows hsum
      hlox hxhi
  have hm := (Rat.cast_le (K := ℝ)).mpr hmin
  norm_num only [Rat.cast_ofNat] at hm
  have hx100 : (100 : ℝ) ≤ x := hm.trans hlox
  have hp := gamma_scaled_profile_price_le (show 0 < x by linarith only [hx100]) hr hroot
  change gammaScaleSignedDualBudget L x ≤ (5 / 4 : ℝ) / (rlo : ℝ) + (C : ℝ)
  rw [gamma_scale_signed_dual_budget_eq_anchored_support L hx100]
  linarith only [hp, he]

end PseudoPrime.LLS
