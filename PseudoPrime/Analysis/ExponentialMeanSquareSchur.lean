/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSymmetricKernelBounds
public import PseudoPrime.Analysis.ExponentialMeanSquareAbelBounds

/-!
# Mean-square bounds from multiplicity-weighted rows

The rational Gram kernel is controlled by Poisson height profiles.
Finite Schur bounds provide actual prefix energies without pair correlation.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- The real nonnegative Laplace Gram kernel. Its argument is a difference of real
frequencies; it is the real form of the previously computed Fourier integral. -/
noncomputable def gramKernel (x : ℝ) : ℝ :=
  4 / (4 + x ^ 2)

/-- Every real frequency difference has nonnegative Gram kernel. The denominator is
positive, supplying the sign used in row comparisons. -/
theorem gramKernel_nonneg (x : ℝ) : 0 ≤ gramKernel x := by
  exact div_nonneg (by norm_num only) (add_nonneg (by norm_num only) (sq_nonneg x))

/-- The real Gram kernel is even, so the frequency kernel is symmetric.
Squaring removes the sign of the frequency difference. -/
theorem gramKernel_sub_comm (x y : ℝ) : gramKernel (x - y) = gramKernel (y - x) := by
  dsimp only [gramKernel]
  congr 2
  ring

/-- Real inclusion identifies the complex rational Fourier kernel with the real Gram
kernel. This permits taking real parts without a norm estimate on the denominator. -/
theorem complex_gramKernel (x : ℝ) : (4 : ℂ) / (4 + (x : ℂ) ^ 2) = (gramKernel x : ℂ) := by
  simp only [gramKernel, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_ofNat]

/-- The exact finite energy equals its real Gram expansion, retaining all coefficient
cross terms. Take real parts after the previously justified finite integral. -/
theorem energy_eq_real_gram {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    energy (exponentialSum s γ a) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)).re * gramKernel (γ i - γ j) := by
  rw [energy_exponentialSum]
  change Complex.reAddGroupHom _ = _
  simp only [map_sum, complex_gramKernel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (_ * (gramKernel (γ i - γ j) : ℂ)).re = _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The actual energy is bounded by the positive Gram form in coefficient norms.
Bound each real cross term by its norm, using nonnegativity of the real kernel. -/
theorem energy_le_norm_gram {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    energy (exponentialSum s γ a) ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * gramKernel (γ i - γ j) := by
  rw [energy_eq_real_gram]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have h := Complex.re_le_norm (a i * starRingEnd ℂ (a j))
  rw [norm_mul, Complex.norm_conj] at h
  exact mul_le_mul_of_nonneg_right h (gramKernel_nonneg _)

/-- A nonnegative multiplicity weight and a uniform weighted row bound give an actual
energy bound by the weighted coefficient l2 mass. Apply the finite weighted Schur theorem. -/
theorem energy_le_weighted_rows {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a : ι → ℂ) {R : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R) :
    energy (exponentialSum s γ (fun i ↦ (m i : ℂ) * a i)) ≤ R * ∑ i ∈ s, m i * ‖a i‖ ^ 2 := by
  have he := energy_le_norm_gram s γ (fun i ↦ (m i : ℂ) * a i)
  have hs :=
    FiniteSymmetricKernel.quadratic_le_of_rows s (fun i j ↦ gramKernel (γ i - γ j)) m
      (fun i ↦ ‖a i‖) hm (fun i hi j hj ↦ gramKernel_nonneg _)
      (fun i hi j hj ↦ gramKernel_sub_comm _ _) hR
  apply le_trans he
  have heq :
    (∑ i ∈ s, ∑ j ∈ s, ‖(m i : ℂ) * a i‖ * ‖(m j : ℂ) * a j‖ * gramKernel (γ i - γ j)) =
      ∑ i ∈ s, ∑ j ∈ s, m i * m j * ‖a i‖ * ‖a j‖ * gramKernel (γ i - γ j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (hm i hi), Complex.norm_of_nonneg (hm j hj)]
    ring
  rw [heq]
  exact hs

/-- The Gram kernel is at most nine times the reciprocal quadratic height profile
with denominator nine. This transfers the existing reflected-resolvent zero mass to rows. -/
theorem gramKernel_le_poisson (x : ℝ) : gramKernel x ≤ 9 / (9 + x ^ 2) := by
  dsimp only [gramKernel]
  rw [div_le_div_iff₀ (by nlinarith only [sq_nonneg x] : 0 < 4 + x ^ 2)
      (by nlinarith only [sq_nonneg x] : 0 < 9 + x ^ 2)]
  nlinarith only [sq_nonneg x]

/-- Cutting a height prefix can only decrease the norm of each coefficient.
This does not assert that the energy itself is monotone under cutting. -/
theorem norm_heightCoefficients_le {ι : Type*} (γ : ι → ℝ) (a : ι → ℂ) (t : ℝ) (i : ι) :
    ‖heightCoefficients γ a t i‖ ≤ ‖a i‖ := by
  dsimp only [heightCoefficients]
  split_ifs
  · exact le_rfl
  · exact (norm_zero : ‖(0 : ℂ)‖ = 0).trans_le (norm_nonneg _)

/-- Real multiplicity weights commute with the actual height cutoff.
Distribute multiplication through the two branches, retaining the same finite sum. -/
theorem heightCoefficients_real_mul {ι : Type*} (γ m : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    heightCoefficients γ (fun i ↦ (m i : ℂ) * a i) t = fun i ↦
      (m i : ℂ) * heightCoefficients γ a t i := by
  funext i
  dsimp only [heightCoefficients]
  split_ifs
  · rfl
  · exact (mul_zero _).symm

/-- Every actual prefix has the same Schur energy budget, provided the row bound is
nonnegative. Bound the cut coefficient l2 mass; do not subtract prefix energies. -/
theorem energy_prefix_le_weighted_rows {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a : ι → ℂ) {R : ℝ}
    (hR0 : 0 ≤ R) (hm : ∀ i ∈ s, 0 ≤ m i) (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R)
    (t : ℝ) :
    energy (exponentialSum s γ (heightCoefficients γ (fun i ↦ (m i : ℂ) * a i) t)) ≤
      R * ∑ i ∈ s, m i * ‖a i‖ ^ 2 := by
  rw [heightCoefficients_real_mul]
  have he := energy_le_weighted_rows s γ m (heightCoefficients γ a t) hm hR
  have hl :=
    Finset.sum_le_sum (s := s)
      (fun i hi ↦
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_heightCoefficients_le γ a t i))
          (hm i hi))
  exact he.trans (mul_le_mul_of_nonneg_left hl hR0)

/-- A uniform multiplicity-weighted row bound supplies all intermediate prefix energies
in the proved Abel and Sobolev estimates. The resulting actual block bound needs no
separate energy or derivative-energy hypothesis. -/
theorem block_point_le_weighted_rows {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a : ι → ℂ)
    {U T R : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) (hR0 : 0 ≤ R) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R) :
    ‖exponentialSum s γ (heightCoefficients γ (fun i ↦ (m i : ℂ) * a i) T) 0 -
            exponentialSum s γ (heightCoefficients γ (fun i ↦ (m i : ℂ) * a i) U) 0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) * (R * ∑ i ∈ s, m i * ‖a i‖ ^ 2) := by
  apply
    block_point_le_of_prefix s γ (fun i ↦ (m i : ℂ) * a i) hU hUT
      (mul_nonneg hR0 (Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hm i hi) (sq_nonneg _))))
  exact fun t ht ↦ energy_prefix_le_weighted_rows s γ m a hR0 hm hR t

end PseudoPrime.Analysis.ExponentialMeanSquare
