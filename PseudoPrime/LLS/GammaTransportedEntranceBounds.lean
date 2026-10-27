/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaTransportedEntranceData

/-! # Real transported local-cost bounds from unchanged log-260 rows -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: the unchanged old cell and new rational left endpoint have the
stated root bounds and support through 350. Use existing cell soundness and
small rational geometry checks. Role: avoid new scale-dependent row checks. -/
theorem gamma_transported_geometry :
    gammaTransportedOldCell.check = true ∧
      1 ≤ (gammaTransportedNewLo : ℝ) ∧
      (gammaTransportedNewLo : ℝ) ≤ (gammaTransportedOldCell.lo : ℝ) ∧
      0 < (gammaTransportedNewRootLo : ℝ) ∧
      (gammaTransportedNewRootLo : ℝ) ≤ Real.sqrt (gammaTransportedNewLo : ℝ) ∧
      Real.sqrt (gammaTransportedOldCell.hi : ℝ) ≤ (gammaTransportedOldCell.rootHi : ℝ) ∧
      max 160 (1 + (52 / 25 : ℝ) * Real.sqrt (gammaTransportedOldCell.hi : ℝ)) ≤ 350 := by
  have hc : gammaTransportedOldCell.check = true := by decide +kernel
  obtain ⟨hl, hlh, hrl, hrlo, hrh, hrhi, ht⟩ := gammaTransportedOldCell.check_sound hc
  have hlo : (1 : ℝ) ≤ (gammaTransportedNewLo : ℝ) := by
    exact_mod_cast (show (1 : ℚ) ≤ gammaTransportedNewLo by decide +kernel)
  have hab : (gammaTransportedNewLo : ℝ) ≤ (gammaTransportedOldCell.lo : ℝ) := by
    exact_mod_cast (show gammaTransportedNewLo ≤ gammaTransportedOldCell.lo by decide +kernel)
  have hpos : (0 : ℝ) < (gammaTransportedNewRootLo : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < gammaTransportedNewRootLo by decide +kernel)
  have hsq : (gammaTransportedNewRootLo : ℝ) ^ 2 ≤ (gammaTransportedNewLo : ℝ) := by
    exact_mod_cast (show gammaTransportedNewRootLo ^ 2 ≤ gammaTransportedNewLo by decide +kernel)
  have hr := (Real.le_sqrt hpos.le (zero_le_one.trans hlo)).mpr hsq
  have htop : (1 : ℝ) + (52 / 25 : ℝ) * (gammaTransportedOldCell.rootHi : ℝ) ≤ 350 := by
    have hq : (1 : ℚ) + (52 / 25 : ℚ) * gammaTransportedOldCell.rootHi ≤ 350 := by decide +kernel
    have h := (Rat.cast_le (K := ℝ)).mpr hq
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  refine ⟨hc, hlo, hab, hpos, hr, hrhi, ?_⟩
  apply max_le (by norm_num only)
  linarith only [htop, hrhi]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Claim: the anchored upper-window support lies among odd primes through
350. Transfer the certified real cutoff through natural floors.
Role: use the one compact transported aggregate. -/
theorem gamma_transported_support_subset :
    Analysis.gammaAnchoredWindowPrimeSet gammaTransportedOldCell.hi ⊆
      (Finset.Icc 3 350).filter Nat.Prime := by
  have hgeo := gamma_transported_geometry
  have hf := Nat.floor_mono hgeo.2.2.2.2.2.2
  norm_num only [Nat.floor_ofNat] at hf
  intro p hp
  obtain ⟨hm, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨h3, hcut⟩ := Finset.mem_Icc.mp hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hcut.trans hf⟩, hprime⟩

/-- Input: an odd prime through 350. Claim: the unchanged adaptive row has
the matching prime and passes its old envelope check. Restrict the existing
480-prime certificate. Role: reuse previously verified local data. -/
theorem gamma_transported_row_check (p : ℕ) (hp : p ∈ (Finset.Icc 3 350).filter Nat.Prime) :
    (gammaTransportedRow p).prime = p ∧
      (gammaTransportedRow p).envelopeCheck gammaTransportedOldCell = true := by
  obtain ⟨hm, hprime⟩ := Finset.mem_filter.mp hp
  have hmem :
    p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 0).support).filter Nat.Prime := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, ?_⟩, hprime⟩
    exact (Finset.mem_Icc.mp hm).2.trans (by decide +kernel)
  exact ⟨rfl, gamma_signed_principal_entrance_check0.2.1 p hmem⟩

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: an odd prime through 350. Claim: its actual corrected window
allowance is bounded by the rational transported allowance. Compare signed
root quotients and logarithm bounds. Role: transfer the aggregate to real costs. -/
theorem gamma_transported_row_cap (p : ℕ) (hp : p ∈ (Finset.Icc 3 350).filter Nat.Prime) :
    Real.log p *
        Analysis.gammaRamifiedWindowExcessBound gammaTransportedNewLo gammaTransportedOldCell.hi
          (gammaTransportedRow p).eulerUpper
          (((gammaTransportedRow p).rampUpper : ℝ) - 5 / 4 +
            (((p : ℝ) + 1) / (p - 1)) * ((gammaTransportedOldCell.lo : ℝ) - gammaTransportedNewLo) /
              gammaTransportedNewLo) ≤
      (gammaTransportedAllowance p : ℝ) := by
  have hcheck := gamma_transported_row_check p hp
  have hg := gamma_transported_geometry
  have hlohi : (gammaTransportedNewLo : ℝ) ≤ (gammaTransportedOldCell.hi : ℝ) :=
    hg.2.2.1.trans (gammaTransportedOldCell.check_sound hg.1).2.1
  have hw :=
    Analysis.gamma_window_excess_le_root_bounds (e := ((gammaTransportedRow p).eulerUpper : ℝ))
      (N := (((gammaTransportedRow p).rampUpper - 5 / 4 + gammaTransportedDelta p : ℚ) : ℝ))
      hg.2.2.2.1 hlohi hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hl := (Analysis.rationalLogIntervalCheck_sound (Bool.and_eq_true_iff.mp hcheck.2).1).2
  change Real.log p ≤ ((gammaTransportedRow p).logUpper : ℝ) at hl
  have hn := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  have hmul := mul_le_mul hl hw (le_max_right _ _) (hn.trans hl)
  norm_num only [gammaTransportedAllowance, gammaTransportedDelta, Rat.cast_mul, Rat.cast_max,
    Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_zero] at hmul ⊢
  exact hmul

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Claim: the corrected real allowance sum on the anchored support is at
most 377/100. Use pointwise rational caps, nonnegative extension and the
kernel aggregate bound. Role: supply the actual uniform dual estimate. -/
theorem gamma_transported_rows_upper :
    (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet gammaTransportedOldCell.hi,
        Real.log p *
          Analysis.gammaRamifiedWindowExcessBound gammaTransportedNewLo gammaTransportedOldCell.hi
            (gammaTransportedRow p).eulerUpper
            (((gammaTransportedRow p).rampUpper : ℝ) - 5 / 4 +
              (((p : ℝ) + 1) / (p - 1)) *
                  ((gammaTransportedOldCell.lo : ℝ) - gammaTransportedNewLo) /
                gammaTransportedNewLo)) ≤
      (377 / 100 : ℝ) := by
  have he := (Rat.cast_le (K := ℝ)).mpr gamma_transported_allowance_sum_le
  norm_num only [gammaTransportedAllowanceSum, Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] at he
  have hsub := gamma_transported_support_subset
  have hnonneg (p : ℕ) (hp : p ∈ (Finset.Icc 3 350).filter Nat.Prime) :
    (0 : ℝ) ≤ (gammaTransportedAllowance p : ℝ) := by
    apply le_trans ?_ (gamma_transported_row_cap p hp)
    exact
      mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
        (le_max_right _ _)
  have heS := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot ↦ hnonneg p hp)).trans he
  exact (Finset.sum_le_sum (fun p hp ↦ gamma_transported_row_cap p (hsub hp))).trans heS

/-- Input: nonnegative L and any scale in the enlarged old window.
Claim: the actual dual budget is at most delta(newLo)*L+377/100.
Apply the downward row transfer. Role: certify continuous scales below 260. -/
theorem gamma_transported_actual_dual_cap {L x : ℝ} (hL : 0 ≤ L)
    (hlox : (gammaTransportedNewLo : ℝ) ≤ x) (hxhi : x ≤ (gammaTransportedOldCell.hi : ℝ)) :
    gammaScaleSignedDualBudget L x ≤
      Analysis.gammaRamifiedDualParameter gammaTransportedNewLo * L + 377 / 100 := by
  have hg := gamma_transported_geometry
  have hsub := gamma_transported_support_subset
  have hc := fun p hp ↦ gamma_transported_row_check p (hsub hp)
  have he (p : ℕ) (hp : p ∈ Analysis.gammaAnchoredWindowPrimeSet gammaTransportedOldCell.hi) :
    Analysis.gammaPrimeEulerCost p ≤ ((gammaTransportedRow p).eulerUpper : ℝ) := by
    exact
      Analysis.gamma_adaptive_euler_upper_sound (Finset.mem_filter.mp hp).2
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact
    gamma_scale_signed_dual_budget_le_lowered_window_rows_base_ratio gammaTransportedOldCell
      gammaTransportedRow hg.1 hL hg.2.1 hg.2.2.1 hlox hxhi hc he gamma_transported_rows_upper

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: the same enlarged window and nonnegative L. Claim: replace the
left square root by its rational lower bound in the dual cap. Preserve the
linear logarithmic term. Role: feed the continuous polynomial profile. -/
theorem gamma_transported_dual_cap {L x : ℝ} (hL : 0 ≤ L) (hlox : (gammaTransportedNewLo : ℝ) ≤ x)
    (hxhi : x ≤ (gammaTransportedOldCell.hi : ℝ)) :
    gammaScaleSignedDualBudget L x ≤
      (5 / (4 * ((1589 / 2500 : ℝ) * (2591 / 10)))) * L + 377 / 100 := by
  have h := gamma_transported_actual_dual_cap hL hlox hxhi
  have hg := gamma_transported_geometry
  have hp := hg.2.2.2.1
  have hr := hg.2.2.2.2.1
  have hd :
    Analysis.gammaRamifiedDualParameter gammaTransportedNewLo ≤
      5 / (4 * ((1589 / 2500 : ℝ) * (2591 / 10))) := by
    dsimp only [Analysis.gammaRamifiedDualParameter]
    simp only [gammaTransportedNewRootLo, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hp hr
    exact
      div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 5) le_rfl (mul_pos (by norm_num only) hp)
        (mul_le_mul_of_nonneg_left hr (by norm_num only))
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hd hL) le_rfl)

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: 2591/10 <= L <= 260. Claim: the profile lies in the transported
window and admits prefix 50000. Compare squares and the old cell geometry.
Role: discharge the scale assumptions of the witness extraction. -/
theorem gamma_transported_profile_inputs {L : ℝ} (hL : 2591 / 10 ≤ L) (hU : L ≤ 260) :
    (gammaTransportedNewLo : ℝ) ≤ (101 / 250 : ℝ) * L ^ 2 ∧
      (101 / 250 : ℝ) * L ^ 2 ≤ (gammaTransportedOldCell.hi : ℝ) ∧
      4096 ≤ (101 / 250 : ℝ) * L ^ 2 ∧ 50000 ≤ (99 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hs := (sq_le_sq₀ hL0 (by norm_num only : (0 : ℝ) ≤ 260)).mpr hU
  have hlo : (gammaTransportedNewLo : ℝ) ≤ (101 / 250 : ℝ) * L ^ 2 := by
    norm_num only [gammaTransportedNewLo, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    nlinarith only [hL, sq_nonneg (L - 2591 / 10)]
  have hbound : (101 / 250 : ℝ) * 260 ^ 2 ≤ (gammaTransportedOldCell.lo : ℝ) := by
    have hq : (101 / 250 : ℚ) * 260 ^ 2 ≤ gammaTransportedOldCell.lo := by decide +kernel
    have h := (Rat.cast_le (K := ℝ)).mpr hq
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h ⊢
    exact h
  have hupper : (101 / 250 : ℝ) * L ^ 2 ≤ (gammaTransportedOldCell.hi : ℝ) :=
    (mul_le_mul_of_nonneg_left hs (by norm_num only)).trans
      (hbound.trans (gammaTransportedOldCell.check_sound gamma_transported_geometry.1).2.1)
  have hsmall : (4096 : ℝ) ≤ (gammaTransportedNewLo : ℝ) := by
    exact_mod_cast (show (4096 : ℚ) ≤ gammaTransportedNewLo by decide +kernel)
  refine ⟨hlo, hupper, hsmall.trans hlo, ?_⟩
  nlinarith only [hL, sq_nonneg (L - 2591 / 10)]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: RH and 2591/10 <= L <= 260. Claim: the retained factor-free
signed-principal margin exceeds 7/60. Combine the transported actual dual
cap, analytic prefix and polynomial profile. Role: bridge the improved
entrance to the existing half-line without new local row data. -/
theorem gamma_transported_separation (hRH : RiemannHypothesis) {L : ℝ} (hL : 2591 / 10 ≤ L)
    (hU : L ≤ 260) :
    7 / 60 <
      gammaSignedPrincipalFactorFreeSeparation L 50000 ((101 / 250 : ℝ) * L ^ 2) + 9 / 50 := by
  obtain ⟨hlo, hhi, hx, hb⟩ := gamma_transported_profile_inputs hL hU
  have hdual := gamma_transported_dual_cap (by linarith only [hL] : 0 ≤ L) hlo hhi
  have hprefix := gamma_prefix50000_lower_asymmetric hRH (le_refl (50000 : ℝ))
  have hcredit :
    gammaTransportedCredit L +
        (3 / 4 + ((5 / (4 * ((1589 / 2500 : ℝ) * (2591 / 10)))) * L + 377 / 100) + 7 / 60) / 2 ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    dsimp only [gammaTransportedCredit]
    linarith only [hprefix]
  exact
    gamma_retained_margin_gt_of_polynomial (by linarith only [hx]) hcredit hdual
      (gamma_transported_polynomial_condition hL)

end PseudoPrime.LLS
