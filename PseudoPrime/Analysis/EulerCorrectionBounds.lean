/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Explicit bounds for small Euler correction products

The finite-product estimate used on page 7 of A Short Proof of the QRH, together
with deletion stability, the convergent-product limit, and inverse bounds.
No zero-free-region assertion from that manuscript is assumed.
-/

@[expose] public section

namespace PseudoPrime.Analysis.EulerCorrectionBounds

/-- For a finite correction product, local norm majorants with total budget B imply
closeness to one by exp B minus one. Combine the finite-product norm estimate with monotonicity. -/
theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (h : ι → ℂ) (a : ι → ℝ) {B : ℝ}
    (ha : ∀ j ∈ s, ‖h j‖ ≤ a j) (hB : ∑ j ∈ s, a j ≤ B) :
    ‖∏ j ∈ s, (1 + h j) - 1‖ ≤ Real.exp B - 1 := by
  have hsum : ∑ j ∈ s, ‖h j‖ ≤ B := (Finset.sum_le_sum ha).trans hB
  exact (s.norm_prod_one_add_sub_one_le h).trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

/-- The same explicit correction budget remains valid after deleting any finite set of factors.
Compare the sums of nonnegative local majorants before applying the product estimate. -/
theorem norm_subproduct_sub_one_le {ι : Type*} (s t : Finset ι) (h : ι → ℂ) (a : ι → ℝ) {B : ℝ}
    (ht : t ⊆ s) (ha0 : ∀ j ∈ s, 0 ≤ a j) (ha : ∀ j ∈ s, ‖h j‖ ≤ a j) (hB : ∑ j ∈ s, a j ≤ B) :
    ‖∏ j ∈ t, (1 + h j) - 1‖ ≤ Real.exp B - 1 := by
  apply norm_prod_sub_one_le t h a (fun j hj ↦ ha j (ht hj))
  exact (Finset.sum_le_sum_of_subset_of_nonneg ht (fun j hj hnot ↦ ha0 j hj)).trans hB

/-- For a summable family of correction norms, the infinite product has the same explicit
exp B minus one error bound. Pass the finite estimates to the actual convergent product. -/
theorem norm_tprod_sub_one_le {ι : Type*} (h : ι → ℂ) (hs : Summable (fun j ↦ ‖h j‖)) {B : ℝ}
    (hB : ∑' j, ‖h j‖ ≤ B) : ‖(∏' j, (1 + h j)) - 1‖ ≤ Real.exp B - 1 := by
  have hp := multipliable_one_add_of_summable hs
  apply le_of_tendsto (hp.hasProd.sub tendsto_const_nhds).norm
  exact
    Filter.Eventually.of_forall
      (fun s ↦
        norm_prod_sub_one_le s h (fun j ↦ ‖h j‖) (fun j hj ↦ le_rfl)
          ((Summable.sum_le_tsum s (fun j hj ↦ norm_nonneg _) hs).trans hB))

/-- A complex correction within delta of one has norm at least one minus delta.
Use the reverse triangle inequality to retain an explicit denominator bound. -/
theorem one_sub_le_norm {z : ℂ} {δ : ℝ} (hz : ‖z - 1‖ ≤ δ) : 1 - δ ≤ ‖z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one, norm_sub_rev] at h
  linarith only [h, hz]

/-- A complex correction within delta < 1 of one cannot vanish.
Use the positive lower norm bound instead of a qualitative nonvanishing hypothesis. -/
theorem ne_zero_of_norm_sub_one_le {z : ℂ} {δ : ℝ} (hδ : δ < 1) (hz : ‖z - 1‖ ≤ δ) : z ≠ 0 := by
  intro h
  have hn := one_sub_le_norm hz
  rw [h, norm_zero] at hn
  linarith only [hn, hδ]

/-- A complex correction within delta < 1 of one has inverse norm at most (1-delta) inverse.
Invert the positive norm lower bound to control division in an explicit formula. -/
theorem norm_inv_le {z : ℂ} {δ : ℝ} (hδ : δ < 1) (hz : ‖z - 1‖ ≤ δ) : ‖z⁻¹‖ ≤ (1 - δ)⁻¹ := by
  rw [norm_inv]
  exact
    (inv_le_inv₀ (lt_of_lt_of_le (sub_pos.mpr hδ) (one_sub_le_norm hz)) (sub_pos.mpr hδ)).mpr
      (one_sub_le_norm hz)

/-- For delta ≥ 0, a finite logarithmic budget log(1+delta) gives error at most delta.
Evaluate the exponential of the logarithm without an asymptotic constant. -/
theorem norm_prod_sub_one_le_of_log_budget {ι : Type*} (s : Finset ι) (h : ι → ℂ) (a : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (ha : ∀ j ∈ s, ‖h j‖ ≤ a j) (hB : ∑ j ∈ s, a j ≤ Real.log (1 + δ)) :
    ‖∏ j ∈ s, (1 + h j) - 1‖ ≤ δ := by
  have h := norm_prod_sub_one_le s h a ha hB
  rw [Real.exp_log (by linarith only [hδ] : 0 < 1 + δ)] at h
  linarith only [h]

/-- For 0 ≤ delta < 1, every subproduct controlled by the nonnegative logarithmic budget
is nonzero with inverse norm at most (1-delta) inverse.
Retain the full budget after deletions, then apply the quantitative inverse estimate. -/
theorem inverse_subproduct_bound {ι : Type*} (s t : Finset ι) (h : ι → ℂ) (a : ι → ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ht : t ⊆ s) (ha0 : ∀ j ∈ s, 0 ≤ a j) (ha : ∀ j ∈ s, ‖h j‖ ≤ a j)
    (hB : ∑ j ∈ s, a j ≤ Real.log (1 + δ)) :
    (∏ j ∈ t, (1 + h j)) ≠ 0 ∧ ‖(∏ j ∈ t, (1 + h j))⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have hn := norm_subproduct_sub_one_le s t h a ht ha0 ha hB
  rw [Real.exp_log (by linarith only [hδ0] : 0 < 1 + δ)] at hn
  have hz : ‖∏ j ∈ t, (1 + h j) - 1‖ ≤ δ := by linarith only [hn]
  exact ⟨ne_zero_of_norm_sub_one_le hδ1 hz, norm_inv_le hδ1 hz⟩

/-- For a summable correction family and 0 ≤ delta < 1, a total norm budget log(1+delta)
makes the actual infinite product nonzero with the same quantitative inverse norm bound.
Pass to the convergent product and use the explicit closeness estimate. -/
theorem inverse_tprod_bound {ι : Type*} (h : ι → ℂ) (hs : Summable (fun j ↦ ‖h j‖)) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB : ∑' j, ‖h j‖ ≤ Real.log (1 + δ)) :
    (∏' j, (1 + h j)) ≠ 0 ∧ ‖(∏' j, (1 + h j))⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have hn := norm_tprod_sub_one_le h hs hB
  rw [Real.exp_log (by linarith only [hδ0] : 0 < 1 + δ)] at hn
  have hz : ‖(∏' j, (1 + h j)) - 1‖ ≤ δ := by linarith only [hn]
  exact ⟨ne_zero_of_norm_sub_one_le hδ1 hz, norm_inv_le hδ1 hz⟩

end PseudoPrime.Analysis.EulerCorrectionBounds
