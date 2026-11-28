/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZero644
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeta
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass101

/-! # Certified zeta mass transferred to the section 122 kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem quarter_norm_transfer644 (t : ℝ) :
    ‖quarterKernel644.function (Complex.I * t)‖ ≤
      (32 / 25) * ‖quarterKernel570.function (Complex.I * t)‖ := by
  rw [quarter_zero_norm_644, quarter_zero_norm_570]
  have h : (51 / 50 : ℝ) ^ 2 + t ^ 2 ≤ (107 / 100 : ℝ) ^ 2 + t ^ 2 := by linarith only
  have hp : 0 < (51 / 50 : ℝ) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t)
  have hd := pow_le_pow_left₀ hp.le h 3
  have h₁ :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ (107 / 100) ^ 5) (pow_pos hp 3) hd
  calc
    _ ≤ (107 / 100 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + t ^ 2) ^ 3 := h₁
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by norm_num only) (pow_nonneg hp.le 3)

/-- Under RH the zeta mass for the section 122 kernel is at most 32/75000000.
Pointwise comparison reuses the already certified section 101 zero sum. -/
theorem quarter_zeta_mass_644 (hRH : RiemannHypothesis) :
    (∑' ρ, ‖quarterKernel644.zetaKernelZeroTerm ρ‖) ≤ 32 / 75000000 := by
  have ha :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel644 hRH).norm
  have hb :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel570 hRH).norm
  have h :=
    ha.tsum_le_tsum
      (fun ρ ↦ by
        unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
        rw [norm_mul, norm_mul, mul_left_comm (32 / 25 : ℝ)]
        exact mul_le_mul_of_nonneg_left (quarter_norm_transfer644 _) (norm_nonneg _))
      (hb.mul_left (32 / 25 : ℝ))
  rw [tsum_mul_left] at h
  linarith only [h, section101_zeta_mass hRH]

end PseudoPrime.PrimeTestBounds.MillerRabin
