/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# A derivative norm bound from a local slope bound

A complex function vanishing at zero and bounded locally by `C * ‖s‖` has derivative
norm at most `C`. The lemma supports finite-radius derivative estimates for xi and
completed Dirichlet functions without importing their function-specific analysis.
Its existing namespace is retained so callers keep the same declaration name.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- If a function has derivative `D` at zero, vanishes there, and locally satisfies
`‖f s‖ ≤ C*‖s‖`, then `‖D‖ ≤ C`. This is a general derivative estimate. -/
theorem norm_deriv_le_of_eventually_norm_le_mul_norm {f : ℂ → ℂ} {D : ℂ} {C : ℝ}
    (hf : HasDerivAt f D 0) (hf0 : f 0 = 0)
    (hbound : ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), ‖f s‖ ≤ C * ‖s‖) : ‖D‖ ≤ C := by
  have htend := hf.tendsto_slope
  have htendNorm := (continuous_norm.tendsto D).comp htend
  have hev : ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), ‖slope f 0 s‖ ≤ C := by
    filter_upwards [hbound, self_mem_nhdsWithin] with s hs hsne
    have hsne' : s ≠ 0 := hsne
    rw [slope_def_module, norm_smul]
    have hnorm_inv : ‖(s - 0)⁻¹‖ = ‖s‖⁻¹ := by rw [sub_zero, norm_inv]
    rw [hnorm_inv, hf0, sub_zero]
    have hsnorm_pos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hsne'
    calc
      ‖s‖⁻¹ * ‖f s‖ ≤ ‖s‖⁻¹ * (C * ‖s‖) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hsnorm_pos.le)
      _ = C := by field_simp [ne_of_gt hsnorm_pos]
  exact le_of_tendsto htendNorm hev

end PseudoPrime.AnalyticNumberTheory.RiemannXi
