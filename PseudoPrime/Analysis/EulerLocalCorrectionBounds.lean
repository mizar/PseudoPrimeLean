/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EulerCorrectionBounds

/-!
# Local rational Euler correction factors

The rational factor on page 7 of A Short Proof of the QRH is bounded before
taking products. The statements use only elementary norm assumptions, without
assuming any zero-free region or an unquantified prime-tail estimate.
-/

@[expose] public section

namespace PseudoPrime.Analysis.EulerCorrectionBounds

/-- The local rational correction with real reciprocal norm parameter t and complex
parameters D and R. Denominator nonvanishing is supplied by the norm hypotheses below.
Its deviation from one is the input to the correction-product bounds. -/
noncomputable def localCorrection (t : ℝ) (D R : ℂ) : ℂ :=
  (1 - (t : ℂ) ^ 2) / (1 - R) * (1 + (t : ℂ) * (D - R) / (1 - D))

/-- If a complex parameter has norm at most one half, one minus that parameter is
nonzero. Use the quantitative reverse triangle bound for the local denominators. -/
theorem one_sub_ne_zero_of_norm_le_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : 1 - z ≠ 0 := by
  apply ne_zero_of_norm_sub_one_le (δ := (1 : ℝ) / 2) (by norm_num only)
  simpa only [sub_sub_cancel_left, norm_neg] using hz

/-- The inverse of one minus a parameter of norm at most one half has norm at most two.
This explicit denominator estimate is used in the local correction error. -/
theorem norm_one_sub_inv_le_two {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖(1 - z)⁻¹‖ ≤ 2 := by
  have h :=
    norm_inv_le (δ := (1 : ℝ) / 2) (z := 1 - z) (by norm_num only)
      (by simpa only [sub_sub_cancel_left, norm_neg] using hz)
  norm_num only at h
  exact h

/-- For a real reciprocal norm parameter between zero and one half, the numerator
one minus its square has norm at most one. This retains the real sign before taking norms. -/
theorem norm_one_sub_real_sq_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : ‖1 - (t : ℂ) ^ 2‖ ≤ 1 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  have ht1 : t ^ 2 ≤ 1 := by nlinarith only [ht0, ht]
  rw [Complex.norm_of_nonneg (sub_nonneg.mpr ht1)]
  linarith only [sq_nonneg t]

/-- With nonzero local denominators, the correction error splits into its direct error
and its mixed error. The identity avoids bounding the entire correction by its norm. -/
theorem localCorrection_sub_one {t : ℝ} {D R : ℂ} (hR : 1 - R ≠ 0) :
    localCorrection t D R - 1 =
      (R - (t : ℂ) ^ 2) / (1 - R) +
        (1 - (t : ℂ) ^ 2) * (1 - R)⁻¹ * ((t : ℂ) * (D - R) * (1 - D)⁻¹) := by
  dsimp only [localCorrection]
  have hiR := inv_mul_cancel₀ hR
  simp only [div_eq_mul_inv]
  linear_combination hiR

/-- The direct part of the local correction error is at most twice norm R plus t squared.
Use the inverse denominator bound and the triangle inequality. -/
theorem norm_local_direct_le {t : ℝ} {R : ℂ} (ht0 : 0 ≤ t) (hR : ‖R‖ ≤ 1 / 2) :
    ‖(R - (t : ℂ) ^ 2) / (1 - R)‖ ≤ (‖R‖ + t ^ 2) * 2 := by
  have hRi := norm_one_sub_inv_le_two hR
  rw [div_eq_mul_inv, norm_mul]
  apply mul_le_mul _ hRi (norm_nonneg _) (add_nonneg (norm_nonneg R) (sq_nonneg t))
  have hp : ‖(t : ℂ) ^ 2‖ = t ^ 2 := by rw [norm_pow, Complex.norm_of_nonneg ht0]
  exact (norm_sub_le _ _).trans_eq (congrArg (fun x : ℝ ↦ ‖R‖ + x) hp)

/-- The mixed part of the local correction error is controlled by both denominator bounds.
The real numerator bound avoids an unnecessary loss in the final constant. -/
theorem norm_local_mixed_le {t : ℝ} {D R : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hD : ‖D‖ ≤ 1 / 2)
    (hR : ‖R‖ ≤ 1 / 2) :
    ‖(1 - (t : ℂ) ^ 2) * (1 - R)⁻¹ * ((t : ℂ) * (D - R) * (1 - D)⁻¹)‖ ≤
      2 * (t * (‖D‖ + ‖R‖) * 2) := by
  have hRi := norm_one_sub_inv_le_two hR
  have hDi := norm_one_sub_inv_le_two hD
  have hn := norm_one_sub_real_sq_le ht0 ht
  simp only [norm_mul, Complex.norm_of_nonneg ht0]
  have hleft : ‖1 - (t : ℂ) ^ 2‖ * ‖(1 - R)⁻¹‖ ≤ 2 := by
    simpa only [one_mul] using mul_le_mul hn hRi (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 1)
  apply
    mul_le_mul hleft _ (mul_nonneg (mul_nonneg ht0 (norm_nonneg _)) (norm_nonneg _))
      (by norm_num only)
  apply
    mul_le_mul _ hDi (norm_nonneg _) (mul_nonneg ht0 (add_nonneg (norm_nonneg D) (norm_nonneg R)))
  exact mul_le_mul_of_nonneg_left (norm_sub_le D R) ht0

/-- For real 0 ≤ t ≤ one half and local parameters of norm at most one half, the
correction error has the explicit majorant 4(t²+t norm D+norm R).
Split the error and keep the real numerator bound to obtain the constant four. -/
theorem norm_localCorrection_sub_one_le {t : ℝ} {D R : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hD : ‖D‖ ≤ 1 / 2) (hR : ‖R‖ ≤ 1 / 2) :
    ‖localCorrection t D R - 1‖ ≤ 4 * (t ^ 2 + t * ‖D‖ + ‖R‖) := by
  rw [localCorrection_sub_one (one_sub_ne_zero_of_norm_le_half hR)]
  have hfirst := norm_local_direct_le ht0 hR
  have hsecond := norm_local_mixed_le ht0 ht hD hR
  have hsum :=
    norm_add_le ((R - (t : ℂ) ^ 2) / (1 - R))
      ((1 - (t : ℂ) ^ 2) * (1 - R)⁻¹ * ((t : ℂ) * (D - R) * (1 - D)⁻¹))
  nlinarith only [hsum, hfirst, hsecond, mul_le_mul_of_nonneg_right ht (norm_nonneg R), sq_nonneg t]

/-- Explicit majorants d and r for the two complex parameters give the local budget
4(t²+t d+r). This permits separate analytic estimates for the local powers. -/
theorem norm_localCorrection_sub_one_le_majorant {t d r : ℝ} {D R : ℂ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) (hD : ‖D‖ ≤ 1 / 2) (hR : ‖R‖ ≤ 1 / 2) (hd : ‖D‖ ≤ d) (hr : ‖R‖ ≤ r) :
    ‖localCorrection t D R - 1‖ ≤ 4 * (t ^ 2 + t * d + r) := by
  have h := norm_localCorrection_sub_one_le ht0 ht hD hR
  have hm := mul_le_mul_of_nonneg_left hd ht0
  linarith only [h, hm, hr]

/-- A finite family of the actual local rational factors obeys a logarithmic error
budget. Apply the product theorem to the local deviations from one. -/
theorem local_product_error_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (D R : ι → ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) (ht0 : ∀ j ∈ s, 0 ≤ t j) (ht : ∀ j ∈ s, t j ≤ 1 / 2) (hD : ∀ j ∈ s, ‖D j‖ ≤ 1 / 2)
    (hR : ∀ j ∈ s, ‖R j‖ ≤ 1 / 2)
    (hB : ∑ j ∈ s, 4 * ((t j) ^ 2 + t j * ‖D j‖ + ‖R j‖) ≤ Real.log (1 + δ)) :
    ‖∏ j ∈ s, localCorrection (t j) (D j) (R j) - 1‖ ≤ δ := by
  have h :=
    norm_prod_sub_one_le_of_log_budget s (fun j ↦ localCorrection (t j) (D j) (R j) - 1)
      (fun j ↦ 4 * ((t j) ^ 2 + t j * ‖D j‖ + ‖R j‖)) hδ
      (fun j hj ↦ norm_localCorrection_sub_one_le (ht0 j hj) (ht j hj) (hD j hj) (hR j hj)) hB
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- Every finite subproduct of local rational factors is nonzero and has a controlled
inverse if the full local budget is at most log(1+delta), with 0 ≤ delta < 1.
This retains the budget when conductor primes are removed. -/
theorem local_subproduct_inverse_bound {ι : Type*} (s u : Finset ι) (t : ι → ℝ) (D R : ι → ℂ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hu : u ⊆ s) (ht0 : ∀ j ∈ s, 0 ≤ t j)
    (ht : ∀ j ∈ s, t j ≤ 1 / 2) (hD : ∀ j ∈ s, ‖D j‖ ≤ 1 / 2) (hR : ∀ j ∈ s, ‖R j‖ ≤ 1 / 2)
    (hB : ∑ j ∈ s, 4 * ((t j) ^ 2 + t j * ‖D j‖ + ‖R j‖) ≤ Real.log (1 + δ)) :
    (∏ j ∈ u, localCorrection (t j) (D j) (R j)) ≠ 0 ∧
      ‖(∏ j ∈ u, localCorrection (t j) (D j) (R j))⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have h :=
    inverse_subproduct_bound s u (fun j ↦ localCorrection (t j) (D j) (R j) - 1)
      (fun j ↦ 4 * ((t j) ^ 2 + t j * ‖D j‖ + ‖R j‖)) hδ0 hδ1 hu
      (fun j hj ↦
        (norm_nonneg _).trans
          (norm_localCorrection_sub_one_le (ht0 j hj) (ht j hj) (hD j hj) (hR j hj)))
      (fun j hj ↦ norm_localCorrection_sub_one_le (ht0 j hj) (ht j hj) (hD j hj) (hR j hj)) hB
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- A summable local majorant with logarithmic total budget controls the actual infinite
product of rational factors and its inverse. Summability of the deviations is derived
from the explicit local bound, rather than required as an additional assumption. -/
theorem local_tprod_inverse_bound {ι : Type*} (t : ι → ℝ) (D R : ι → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (ht0 : ∀ j, 0 ≤ t j) (ht : ∀ j, t j ≤ 1 / 2) (hD : ∀ j, ‖D j‖ ≤ 1 / 2)
    (hR : ∀ j, ‖R j‖ ≤ 1 / 2) (hs : Summable (fun j ↦ 4 * ((t j) ^ 2 + t j * ‖D j‖ + ‖R j‖)))
    (hB : ∑' j, 4 * ((t j) ^ 2 + t j * ‖D j‖ + ‖R j‖) ≤ Real.log (1 + δ)) :
    (∏' j, localCorrection (t j) (D j) (R j)) ≠ 0 ∧
      ‖(∏' j, localCorrection (t j) (D j) (R j))⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have hn := fun j ↦ norm_localCorrection_sub_one_le (ht0 j) (ht j) (hD j) (hR j)
  have hs' := Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) hn hs
  have hsum := (Summable.tsum_le_tsum hn hs' hs).trans hB
  have h := inverse_tprod_bound (fun j ↦ localCorrection (t j) (D j) (R j) - 1) hs' hδ0 hδ1 hsum
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

end PseudoPrime.Analysis.EulerCorrectionBounds
