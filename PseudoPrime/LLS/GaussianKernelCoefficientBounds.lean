/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianKernel
public import PseudoPrime.LLS.ExplicitKernelCoefficientBounds

/-! # P2 rational Gaussian main-term contracts

The endpoint is proved for the actual kernel. The cutoff-integral lower bound,
finite-conductor zero-mass majorant and numerical remainder are separate inputs.
These arithmetic contracts do not assert a Miller--Rabin witness theorem.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- At index h>=4, cutoff mass I>=8147/10000 and endpoint k<=2129/2000 give
normalized denominator at least 21943/30000. Multiply by the positive h-1 and
use the nonnegative index surplus. This is uniform in the subgroup index. -/
theorem gaussian_normalized_denominator_le {h I k : ℝ} (hh : 4 ≤ h) (hI : (8147 / 10000 : ℝ) ≤ I)
    (hk : k ≤ (2129 / 2000 : ℝ)) : (21943 / 30000 : ℝ) ≤ (h * I - k) / (h - 1) := by
  apply (le_div_iff₀ (by linarith only [hh] : 0 < h - 1)).mpr
  have hprod :=
    mul_nonneg (by linarith only [hh] : 0 ≤ h - 4)
      (by linarith only [hI] : 0 ≤ I - (21943 / 30000 : ℝ))
  nlinarith only [hprod, hI, hk]

/-- At index four the same cutoff and endpoint contracts give the unnormalized
denominator 21943/10000. Linear arithmetic retains all four cutoff terms and
the single principal endpoint. This is the three-character conductor profile. -/
theorem gaussian_triple_denominator_le {I k : ℝ} (hI : (8147 / 10000 : ℝ) ≤ I)
    (hk : k ≤ (2129 / 2000 : ℝ)) : (21943 / 10000 : ℝ) ≤ 4 * I - k := by linarith only [hI, hk]

/-- The improved cutoff lower bound and certified endpoint give the sharper
three-conductor denominator. Keep the normalized finite-index bound separate. -/
theorem gaussian_triple_denominator_le_improved {I k : ℝ} (hI : (81470555 / 100000000 : ℝ) ≤ I)
    (hk : k ≤ (2129 / 2000 : ℝ)) : (10971611 / 5000000 : ℝ) ≤ 4 * I - k := by linarith only [hI, hk]

/-- Exact rational squared margin for coefficient 16/25 and allowance 1/1000.
Normalize by cutoff 21/10. The kernel mass and numerical error remain separate
analytic inputs. This is the primary P2 coefficient 0.64 certificate. -/
theorem gaussian_index_four_coefficient_gap :
    ((161 / 400 : ℝ) + (1 / 1000 : ℝ)) ^ 2 <
      (21943 / 30000 : ℝ) ^ 2 * ((16 / 25 : ℝ) / (21 / 10)) := by
  norm_num only

/-- For positive L and error at most half the allowance, the normalized
Gaussian main term strictly exceeds mass 161/400 times L plus the error.
Apply the squared-margin comparison. No analytic mass bound is assumed here. -/
theorem gaussian_index_four_main_term_lt {L E : ℝ} (hL : 0 < L) (hE : E ≤ (1 / 1000 : ℝ) * L / 2) :
    (161 / 400 : ℝ) * L + E <
      (21943 / 30000 : ℝ) * Real.sqrt (((16 / 25 : ℝ) / (21 / 10)) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) gaussian_index_four_coefficient_gap hE

/-- Exact rational squared margin for coefficient 282976/1000000 and allowance 1/2000.
Use conductor cost twice the mass 161/400 and the sharpened unnormalized denominator.
This is the P2 three-conductor arithmetic certificate. -/
theorem gaussian_three_character_coefficient_gap :
    ((2 * (161 / 400 : ℝ)) + (1 / 2000 : ℝ)) ^ 2 <
      (10971611 / 5000000 : ℝ) ^ 2 * ((282976 / 1000000 : ℝ) / (21 / 10)) := by
  norm_num only

/-- Exact rational margin for coefficient 282924/1000000, allowance 1/2500,
and the conservative three-conductor denominator 21943/10000. -/
theorem gaussian_three_character_coefficient_gap_0282924 :
    ((2 * (161 / 400 : ℝ)) + (1 / 2500 : ℝ)) ^ 2 <
      (21943 / 10000 : ℝ) ^ 2 * ((282924 / 1000000 : ℝ) / (21 / 10)) := by
  norm_num only

/-- At positive L and error at most half the 1/2500 allowance, the three-conductor
Gaussian main term exceeds its mass term and error at coefficient 282924/1000000. -/
theorem gaussian_three_character_main_term_lt_0282924 {L E : ℝ} (hL : 0 < L)
    (hE : E ≤ (1 / 2500 : ℝ) * L / 2) :
    (2 * (161 / 400 : ℝ)) * L + E <
      (21943 / 10000 : ℝ) * Real.sqrt (((282924 / 1000000 : ℝ) / (21 / 10)) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) gaussian_three_character_coefficient_gap_0282924 hE

/-- For positive L and error at most half the allowance, the three-conductor
Gaussian main term exceeds its mass term and error. Apply the exact squared
gap without dividing the original conductor sum by three. -/
theorem gaussian_three_character_main_term_lt {L E : ℝ} (hL : 0 < L)
    (hE : E ≤ (1 / 2000 : ℝ) * L / 2) :
    (2 * (161 / 400 : ℝ)) * L + E <
      (10971611 / 5000000 : ℝ) * Real.sqrt (((282976 / 1000000 : ℝ) / (21 / 10)) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) gaussian_three_character_coefficient_gap hE

/-- For index at least four, the actual Gaussian kernel denominator has the
certified lower bound whenever its cutoff integral reaches 8147/10000.
Use the proved endpoint bound. The cutoff-integral premise remains explicit. -/
theorem gaussian_kernel_normalized_denominator_le {h : ℝ} (hh : 4 ≤ h)
    (hI :
      (8147 / 10000 : ℝ) ≤
        ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
          (PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) :
    (21943 / 30000 : ℝ) ≤
      (h *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          (PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re) /
        (h - 1) :=
  gaussian_normalized_denominator_le hh hI PaperStatements.gaussianGamma_kernel_endpoint_le

/-- The actual Gaussian index-four denominator has lower bound 21943/10000
under the same explicit cutoff-integral premise. Apply the proved endpoint
certificate. This retains the unnormalized three-conductor comparison. -/
theorem gaussian_kernel_triple_denominator_le
    (hI :
      (8147 / 10000 : ℝ) ≤
        ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
          (PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) :
    (21943 / 10000 : ℝ) ≤
      4 *
          (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
            (PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        (PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re :=
  gaussian_triple_denominator_le hI PaperStatements.gaussianGamma_kernel_endpoint_le

/-- For index h>=4, the actual fixed Gaussian denominator is at least 21943/30000.
The cutoff mass and endpoint bounds are proved for the kernel; no numerical integral
premise remains. This supplies the normalized P2 subgroup comparison denominator. -/
theorem gaussian_kernel_normalized_denominator_le_of_four_le_index {h : ℝ} (hh : 4 ≤ h) :
    (21943 / 30000 : ℝ) ≤
      (h *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          (PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re) /
        (h - 1) := by
  exact
    gaussian_kernel_normalized_denominator_le hh
      ((by norm_num only : (8147 / 10000 : ℝ) ≤ 81470555 / 100000000).trans
        PaperStatements.gaussianGamma_cutoff_gt_target.le)

/-- The actual fixed Gaussian index-four denominator is at least 10971611/5000000.
Use the sharpened cutoff mass and endpoint without a separate integral premise.
This supplies the unnormalized denominator for the three-conductor comparison. -/
theorem gaussian_kernel_triple_denominator_le_at_fixed_cutoff :
    (10971611 / 5000000 : ℝ) ≤
      4 *
          (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
            (PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        (PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re := by
  exact
    gaussian_triple_denominator_le_improved PaperStatements.gaussianGamma_cutoff_gt_target.le
      PaperStatements.gaussianGamma_kernel_endpoint_le

end PseudoPrime.LLS
