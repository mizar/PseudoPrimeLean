/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularNarrowBudget

/-! # Principal costs for the width-eight kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH and an index at least 33000, the width-eight principal sums at
`r²`, its reciprocal and one have the stated explicit combined cost.
Apply the principal bound at each scale and divide by the index. -/
theorem triangular8_principal_cost (hRH : RiemannHypothesis) {r h : ℝ} (hr : 0 < r)
    (hh : 33000 ≤ h) :
    ((∑' n : ℕ,
              (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)).summand
                (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re +
          (∑' n : ℕ,
              (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)).summand
                (1 : DirichletCharacter ℂ 1) (r ^ 2)⁻¹ n).re +
          2 *
            (∑' n : ℕ,
                (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)).summand
                  (1 : DirichletCharacter ℂ 1) 1 n).re) /
        h ≤
      (137 / 330 : ℝ) * (r + r⁻¹) + (4 / 15 : ℝ) * (Real.sqrt r + (Real.sqrt r)⁻¹) + 15 / 11 := by
  have hp := triangular8_principal_explicit hRH (sq_pos_of_pos hr)
  have hi := triangular8_principal_explicit hRH (inv_pos.mpr (sq_pos_of_pos hr))
  have h1 := triangular8_principal_explicit hRH (x := 1) (by norm_num only)
  have hroot : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  have hquarter : (r ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt r := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num only [Real.sqrt_eq_rpow]
  have hrooti : Real.sqrt ((r ^ 2)⁻¹) = r⁻¹ := by rw [Real.sqrt_inv, hroot]
  have hquarteri : ((r ^ 2)⁻¹) ^ (1 / 4 : ℝ) = (Real.sqrt r)⁻¹ := by
    rw [Real.inv_rpow (sq_nonneg r), hquarter]
  rw [hroot, hquarter] at hp
  rw [hrooti, hquarteri] at hi
  norm_num only [Real.sqrt_one, Real.one_rpow] at h1
  have hh0 : 0 < h := by linarith only [hh]
  apply (div_le_iff₀ hh0).2
  have hs : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hri : 0 ≤ r⁻¹ := (inv_pos.mpr hr).le
  have hsi : 0 ≤ (Real.sqrt r)⁻¹ := inv_nonneg.mpr hs
  nlinarith only [hp, hi, h1, hh, hr.le, hri, hs, hsi, mul_nonneg (sub_nonneg.mpr hh) hr.le,
    mul_nonneg (sub_nonneg.mpr hh) hri, mul_nonneg (sub_nonneg.mpr hh) hs,
    mul_nonneg (sub_nonneg.mpr hh) hsi]

end PseudoPrime.LLS.PaperStatements
