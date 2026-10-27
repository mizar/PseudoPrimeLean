/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaExponentialScaleDifference
public import PseudoPrime.Analysis.GammaSharperScaleDifference
public import PseudoPrime.LLS.GammaWindowDualBudget

/-! # Uniform dual budgets below an existing cell's left endpoint -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: an old envelope-checked cell, a new left endpoint and checked
rows covering the upper support. Claim: the corrected fixed row sum bounds
the actual dual budget throughout the enlarged interval. Extract downward
numerator bounds and apply window transport. Role: avoid new row tables. -/
theorem gamma_scale_signed_dual_budget_le_lowered_window_rows (c : Analysis.GammaLocalCellData)
    (rows : ℕ → Analysis.GammaLocalPrimeRow) (hcell : c.check = true) {L lo x E : ℝ} (hL : 0 ≤ L)
    (hlo : 1 ≤ lo) (hab : lo ≤ (c.lo : ℝ)) (hlox : lo ≤ x) (hxhi : x ≤ (c.hi : ℝ))
    (hcheck :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
              (((rows p).rampUpper : ℝ) - 5 / 4 + (9 / 2 : ℝ) * ((c.lo : ℝ) - lo) / lo)) ≤
        E) :
    gammaScaleSignedDualBudget L x ≤ Analysis.gammaRamifiedDualParameter lo * L + E := by
  have hn (p : ℕ) (hp : p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi) :
    Analysis.gammaRamifiedWindowNumerator p lo c.hi (5 / 4) ≤
      ((rows p).rampUpper : ℝ) - 5 / 4 + (9 / 2 : ℝ) * ((c.lo : ℝ) - lo) / lo := by
    have hprime : (rows p).prime.Prime := (hcheck p hp).1.symm ▸ (Finset.mem_filter.mp hp).2
    have h3 : 3 ≤ (rows p).prime :=
      (hcheck p hp).1.symm ▸ (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have h :=
      (rows p).window_numerator_le_lowered_left c hcell hprime h3 (hcheck p hp).2
        (zero_lt_one.trans_le hlo) hab (hlo.trans hab) (5 / 4)
    simpa only [(hcheck p hp).1] using h
  exact
    gamma_scale_signed_dual_budget_le_window_rows hL hlo hlox hxhi (fun p ↦ (rows p).eulerUpper)
      (fun p ↦ ((rows p).rampUpper : ℝ) - 5 / 4 + (9 / 2 : ℝ) * ((c.lo : ℝ) - lo) / lo) he hn hrows

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: an old envelope-checked cell, a new left endpoint and checked
rows covering the upper support. Claim: the corrected fixed row sum bounds
the actual dual budget throughout the enlarged interval, using the improved
coefficient 3 for the common scale correction. Extract downward
numerator bounds and apply window transport. Role: avoid new row tables. -/
theorem gamma_scale_signed_dual_budget_le_lowered_window_rows_three
    (c : Analysis.GammaLocalCellData) (rows : ℕ → Analysis.GammaLocalPrimeRow)
    (hcell : c.check = true) {L lo x E : ℝ} (hL : 0 ≤ L) (hlo : 1 ≤ lo) (hab : lo ≤ (c.lo : ℝ))
    (hlox : lo ≤ x) (hxhi : x ≤ (c.hi : ℝ))
    (hcheck :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
              (((rows p).rampUpper : ℝ) - 5 / 4 + (3 : ℝ) * ((c.lo : ℝ) - lo) / lo)) ≤
        E) :
    gammaScaleSignedDualBudget L x ≤ Analysis.gammaRamifiedDualParameter lo * L + E := by
  have hn (p : ℕ) (hp : p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi) :
    Analysis.gammaRamifiedWindowNumerator p lo c.hi (5 / 4) ≤
      ((rows p).rampUpper : ℝ) - 5 / 4 + (3 : ℝ) * ((c.lo : ℝ) - lo) / lo := by
    have hprime : (rows p).prime.Prime := (hcheck p hp).1.symm ▸ (Finset.mem_filter.mp hp).2
    have h3 : 3 ≤ (rows p).prime :=
      (hcheck p hp).1.symm ▸ (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have h :=
      (rows p).window_numerator_le_lowered_left_three c hcell hprime h3 (hcheck p hp).2
        (zero_lt_one.trans_le hlo) hab (hlo.trans hab) (5 / 4)
    simpa only [(hcheck p hp).1] using h
  exact
    gamma_scale_signed_dual_budget_le_window_rows hL hlo hlox hxhi (fun p ↦ (rows p).eulerUpper)
      (fun p ↦ ((rows p).rampUpper : ℝ) - 5 / 4 + (3 : ℝ) * ((c.lo : ℝ) - lo) / lo) he hn hrows

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: an old envelope-checked cell, a new left endpoint and checked
rows covering the upper support. Claim: the corrected fixed row sum bounds
the actual dual budget throughout the enlarged interval, retaining the base-sensitive
coefficient in each row of the scale correction. Extract downward
numerator bounds and apply window transport. Role: avoid new row tables. -/
theorem gamma_scale_signed_dual_budget_le_lowered_window_rows_base_ratio
    (c : Analysis.GammaLocalCellData) (rows : ℕ → Analysis.GammaLocalPrimeRow)
    (hcell : c.check = true) {L lo x E : ℝ} (hL : 0 ≤ L) (hlo : 1 ≤ lo) (hab : lo ≤ (c.lo : ℝ))
    (hlox : lo ≤ x) (hxhi : x ≤ (c.hi : ℝ))
    (hcheck :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
              (((rows p).rampUpper : ℝ) - 5 / 4 +
                (((p : ℝ) + 1) / (p - 1)) * ((c.lo : ℝ) - lo) / lo)) ≤
        E) :
    gammaScaleSignedDualBudget L x ≤ Analysis.gammaRamifiedDualParameter lo * L + E := by
  have hn (p : ℕ) (hp : p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi) :
    Analysis.gammaRamifiedWindowNumerator p lo c.hi (5 / 4) ≤
      ((rows p).rampUpper : ℝ) - 5 / 4 + (((p : ℝ) + 1) / (p - 1)) * ((c.lo : ℝ) - lo) / lo := by
    have hprime : (rows p).prime.Prime := (hcheck p hp).1.symm ▸ (Finset.mem_filter.mp hp).2
    have h :=
      (rows p).window_numerator_le_lowered_left_base_ratio c hcell hprime (hcheck p hp).2
        (zero_lt_one.trans_le hlo) hab (hlo.trans hab) (5 / 4)
    simpa only [(hcheck p hp).1] using h
  exact
    gamma_scale_signed_dual_budget_le_window_rows hL hlo hlox hxhi (fun p ↦ (rows p).eulerUpper)
      (fun p ↦
        ((rows p).rampUpper : ℝ) - 5 / 4 + (((p : ℝ) + 1) / (p - 1)) * ((c.lo : ℝ) - lo) / lo)
      he hn hrows

end PseudoPrime.LLS
