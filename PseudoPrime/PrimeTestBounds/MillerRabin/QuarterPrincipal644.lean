/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrefix644
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Certified principal lower bounds on the four section 122 intervals -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem signed_cutoff_lower {a r m : ℝ} (ha : 0 < a) (hr : a ≤ r) (hm : m + 1.837 ≤ 0)
    (hψ : m ≤ Chebyshev.psi (r ^ 2) - r ^ 2) :
    4 * 0.09235072 * (m + 1.837) / a ≤
      4 * quarterWeight644 (r ^ 2) (r ^ 2) *
        (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) := by
  let w := (quarterKernel644.transform 1).re
  have hp := ha.trans_le hr
  have hw : 0 ≤ w := by
    dsimp only [w]; linarith only [quarter_unit_weight_644.1]
  have hwu : w ≤ 0.09235072 := by
    dsimp only [w]; linarith only [quarter_unit_weight_644.2]
  have hs : m + 1.837 ≤ Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi) := by
    linarith only [hψ, Analysis.log_two_mul_pi_gt]
  rw [quarter_cutoff_weight_644 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  change _ ≤ 4 * (w / r) * _
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply
    le_trans _
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num only) hw))
        hp.le)
  apply (div_le_div_iff₀ ha hp).mpr
  have h₁ := mul_le_mul_of_nonpos_right hwu hm
  have h₂ := mul_le_mul_of_nonpos_left hr (mul_nonpos_of_nonneg_of_nonpos hw hm)
  linarith only [mul_le_mul_of_nonneg_right h₁ hp.le, h₂]

private theorem boundary_lower {a r m : ℝ} (ha : 0 < a) (har : a ≤ r) (hr : r ∈ Set.Icc 316 322)
    (hm : m + 1.837 ≤ 0) (hψ : m ≤ Chebyshev.psi (r ^ 2) - r ^ 2) :
    4 * 0.09235072 * (m + 1.837) / a - 0.001308 ≤
      quarterPrincipalBoundary644 (r ^ 2) +
        3 * Real.log (2 * Real.pi) * quarterWeight644 (r ^ 2) 1 := by
  linarith only [signed_cutoff_lower ha har hm hψ, quarter_principal_boundary_644 hr]

/-- The principal gap plus the logarithmic residue at one. The residue
is paired with the character Gamma term in the final comparison. -/
noncomputable def quarterAdjustedGap644 (r : ℝ) : ℝ :=
  quarterPrincipalGap644 (r ^ 2) + 3 * Real.log (2 * Real.pi) * quarterWeight644 (r ^ 2) 1

/-- Under RH the adjusted principal gap exceeds its linear part minus the stated
loss on each section 122 interval. Each row uses the signed psi bound
from the shared certified walk and the corresponding zero-phase bound. -/
theorem quarter_principal_lower_rows_644 (hRH : RiemannHypothesis) :
    (∀ r ∈ Set.Icc 316 320, 0.71798235 * r - 0.049387 < quarterAdjustedGap644 r) ∧
      (∀ r ∈ Set.Icc 320 (1287 / 4), 0.71798235 * r - 0.027844 < quarterAdjustedGap644 r) ∧
      (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), 0.71798235 * r - 0.040189 < quarterAdjustedGap644 r) ∧
      (∀ r ∈ Set.Icc (1609 / 5) 322, 0.71798235 * r - 0.027439 < quarterAdjustedGap644 r) := by
  have h := quarter_principal_weight_rows_644 hRH
  have hψ := quarter_psi_signed_rows_644
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    have hB :=
      boundary_lower (by norm_num only : (0 : ℝ) < 316) hr.1 ⟨hr.1, hr.2.trans (by norm_num only)⟩
        (by norm_num only) (hψ.1 r hr)
    have hG := h.1 r hr
    dsimp only at hG
    unfold quarterAdjustedGap644
    linarith only [hB, hG]
  · intro r hr
    have hB :=
      boundary_lower (by norm_num only : (0 : ℝ) < 320) hr.1
        ⟨(by norm_num only : (316 : ℝ) ≤ 320).trans hr.1, hr.2.trans (by norm_num only)⟩
        (by norm_num only) (hψ.2.1 r hr)
    have hG := h.2.1 r hr
    dsimp only at hG
    unfold quarterAdjustedGap644
    linarith only [hB, hG]
  · intro r hr
    have hB :=
      boundary_lower (by norm_num only : (0 : ℝ) < 1287 / 4) hr.1
        ⟨(by norm_num only : (316 : ℝ) ≤ 1287 / 4).trans hr.1, hr.2.trans (by norm_num only)⟩
        (by norm_num only) (hψ.2.2.1 r hr)
    have hG := h.2.2.1 r hr
    dsimp only at hG
    unfold quarterAdjustedGap644
    linarith only [hB, hG]
  · intro r hr
    have hB :=
      boundary_lower (by norm_num only : (0 : ℝ) < 1609 / 5) hr.1
        ⟨(by norm_num only : (316 : ℝ) ≤ 1609 / 5).trans hr.1, hr.2⟩ (by norm_num only)
        (hψ.2.2.2 r hr)
    have hG := h.2.2.2 r hr
    dsimp only at hG
    unfold quarterAdjustedGap644
    linarith only [hB, hG]

end PseudoPrime.PrimeTestBounds.MillerRabin
