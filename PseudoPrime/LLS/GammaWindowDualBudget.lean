/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedWindowTransport
public import PseudoPrime.LLS.GammaWindowRowBounds
public import PseudoPrime.LLS.GammaAnchoredDualBudget

/-! # Uniform signed dual budgets from endpoint row bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: nonnegative L, 1<=lo<=x<=hi and Euler/numerator row caps on the
fixed anchored support. Claim: the actual dual budget is at most delta(lo)*L+E
throughout the window. Restrict support, transport signed rows and compare
dual parameters. Role: certify intervals without rebuilding local rows. -/
theorem gamma_scale_signed_dual_budget_le_window_rows {L lo x hi E : ℝ} (hL : 0 ≤ L) (hlo : 1 ≤ lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) (e N : ℕ → ℝ)
    (he : ∀ p ∈ gammaAnchoredWindowPrimeSet hi, Analysis.gammaPrimeEulerCost p ≤ e p)
    (hN : ∀ p ∈ gammaAnchoredWindowPrimeSet hi, gammaRamifiedWindowNumerator p lo hi (5 / 4) ≤ N p)
    (hrows :
      (∑ p ∈ gammaAnchoredWindowPrimeSet hi,
          Real.log p * gammaRamifiedWindowExcessBound lo hi (e p) (N p)) ≤
        E) :
    gammaScaleSignedDualBudget L x ≤ gammaRamifiedDualParameter lo * L + E := by
  have hx : 1 ≤ x := hlo.trans hlox
  have hlo0 := zero_lt_one.trans_le hlo
  have hcap :
    gammaAnchoredThetaCutoff 160 (13 / 25) (5 / 4) x ≤
      max 160 (1 + (52 / 25 : ℝ) * Real.sqrt hi) := by
    apply (gamma_anchor160_cutoff_le hx).trans
    apply max_le_max le_rfl
    linarith only [Real.sqrt_le_sqrt hxhi]
  have hs :=
    gamma_anchored_signed_excess_le_certificate (gammaRamifiedDualPrimeSet x)
      (fun p hp ↦ ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩)
      (a := 160) (B := 13 / 25) (θ := 5 / 4) (by norm_num only) hx
      (fun p hp ha ↦ Analysis.gamma_euler_anchor160_reciprocal hp ha) hcap
  have hw :=
    gamma_ramified_window_excess_sum_le (gammaAnchoredWindowPrimeSet hi)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) hlo0 hlox hxhi e N he hN
  rw [gamma_ramified_theta_parameter_five_fourths] at hs hw
  have hd : gammaRamifiedDualParameter x ≤ gammaRamifiedDualParameter lo := by
    dsimp only [gammaRamifiedDualParameter]
    apply
      (div_le_div_iff₀ (mul_pos (by norm_num only) (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)))
          (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hlo0))).mpr
    nlinarith only [Real.sqrt_le_sqrt hlox]
  have hm := mul_le_mul_of_nonneg_right hd hL
  dsimp only [gammaAnchoredWindowPrimeSet] at hw hrows
  dsimp only [gammaScaleSignedDualBudget]
  linarith only [hs, hw, hrows, hm]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: a checked cell and checked existing rows covering the anchored
window support, plus a cap E on their joint signed allowances. Claim: the
actual dual budget is at most delta(lo)*L+E throughout the cell. Extract the
Euler/numerator caps and apply window transport. Role: reuse stored rows. -/
theorem gamma_scale_signed_dual_budget_le_checked_window_rows (c : GammaLocalCellData)
    (rows : ℕ → GammaLocalPrimeRow) (hcell : c.check = true) {L x E : ℝ} (hL : 0 ≤ L)
    (hlo : (1 : ℝ) ≤ c.lo) (hlox : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ))
    (hcheck : ∀ p ∈ gammaAnchoredWindowPrimeSet c.hi, (rows p).prime = p ∧ (rows p).check c = true)
    (hrows :
      (∑ p ∈ gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            gammaRamifiedWindowExcessBound c.lo c.hi (rows p).eulerUpper
              ((rows p).rampUpper - (5 / 4 : ℝ))) ≤
        E) :
    gammaScaleSignedDualBudget L x ≤ gammaRamifiedDualParameter c.lo * L + E := by
  have hb (p : ℕ) (hp : p ∈ gammaAnchoredWindowPrimeSet c.hi) :
    Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ) ∧
      gammaRamifiedWindowNumerator p c.lo c.hi (5 / 4) ≤ ((rows p).rampUpper : ℝ) - 5 / 4 := by
    have hprime : (rows p).prime.Prime := (hcheck p hp).1.symm ▸ (Finset.mem_filter.mp hp).2
    have h := (rows p).window_bounds c hcell hprime (hcheck p hp).2 (5 / 4)
    simpa only [(hcheck p hp).1] using h
  exact
    gamma_scale_signed_dual_budget_le_window_rows hL hlo hlox hxhi (fun p ↦ (rows p).eulerUpper)
      (fun p ↦ (rows p).rampUpper - (5 / 4 : ℝ)) (fun p hp ↦ (hb p hp).1) (fun p hp ↦ (hb p hp).2)
      hrows

end PseudoPrime.LLS
