/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareL2

/-! # Derivative-energy and point bounds from all intermediate height-prefix energies -/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- If the actual exponential-sum energy is at most nonnegative A, its L2 norm is at most sqrt A.
Use the proved L2 norm-square identity and the nonnegative square-root comparison. -/
theorem norm_normalizedLp_le_sqrt {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) {A : ℝ}
    (hA : 0 ≤ A) (hE : energy (exponentialSum s γ a) ≤ A) : ‖normalizedLp s γ a‖ ≤ Real.sqrt A := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [norm_normalizedLp_sq, Real.sq_sqrt hA]
  exact hE

/-- For heights in (U,T] and uniformly bounded intermediate prefix energies, the real-frequency
weighted sum has energy at most (2T-U) squared A. Apply the actual L2 vector Abel bound
and square it. Repeated real frequencies and arbitrary complex coefficients are allowed. -/
theorem energy_realWeighted_le_of_prefix {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ)
    {U T A : ℝ} (hU0 : 0 ≤ U) (hUT : U ≤ T) (hA : 0 ≤ A) (hU : ∀ j ∈ s, U < γ j)
    (hT : ∀ j ∈ s, γ j ≤ T)
    (hF : ∀ t ∈ Set.Icc U T, energy (exponentialSum s γ (heightCoefficients γ a t)) ≤ A) :
    energy (exponentialSum s γ (fun j ↦ (γ j : ℂ) * a j)) ≤ (2 * T - U) ^ 2 * A := by
  have h :=
    PseudoPrime.Analysis.FiniteHeightAbel.norm_weighted_sum_le s γ (fun j ↦ atomLp (γ j) (a j)) hU0
      hUT hU hT
      (fun t ht ↦ by
        rw [prefix_atomLp]
        exact norm_normalizedLp_le_sqrt s γ _ hA (hF t ht))
  rw [sum_real_smul_atomLp] at h
  have hB : 0 ≤ 2 * T - U := by linarith only [hU0, hUT]
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg A))).mpr h
  simpa only [norm_normalizedLp_sq, mul_pow, Real.sq_sqrt hA] using hs

/-- For ordered endpoints, the coefficient-defined block equals the actual filtered finite sum.
Check the three possible frequency regions without dropping endpoint multiplicities. -/
theorem exponentialSum_block_eq_filter {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) {U T : ℝ}
    (hUT : U ≤ T) :
    exponentialSum s γ (blockCoefficients γ a U T) =
      exponentialSum (s.filter (fun j ↦ U < γ j ∧ γ j ≤ T)) γ a := by
  funext v
  simp only [exponentialSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hu : γ j ≤ U
  · have ht := le_trans hu hUT
    have hn : ¬(U < γ j ∧ γ j ≤ T) := fun h ↦ not_lt_of_ge hu h.1
    simp only [blockCoefficients, heightCoefficients, ite_eq_left hu, ite_eq_left ht,
      ite_eq_right hn, sub_self, zero_mul]
  · by_cases ht : γ j ≤ T
    · have hm : U < γ j ∧ γ j ≤ T := ⟨lt_of_not_ge hu, ht⟩
      simp only [blockCoefficients, heightCoefficients, ite_eq_left ht, ite_eq_right hu,
        ite_eq_left hm, sub_zero]
    · have hn : ¬(U < γ j ∧ γ j ≤ T) := fun h ↦ ht h.2
      simp only [blockCoefficients, heightCoefficients, ite_eq_right ht, ite_eq_right hu,
        ite_eq_right hn, sub_self, zero_mul]

/-- For U ≤ t ≤ T, the prefix of the filtered (U,T] block equals the actual (U,t] block.
Check the frequency regions to connect the intermediate prefix energy estimates. -/
theorem exponentialSum_filtered_prefix {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ)
    {U t T : ℝ} (hUt : U ≤ t) (htT : t ≤ T) :
    exponentialSum (s.filter (fun j ↦ U < γ j ∧ γ j ≤ T)) γ (heightCoefficients γ a t) =
      exponentialSum s γ (blockCoefficients γ a U t) := by
  funext v
  simp only [exponentialSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hu : γ j ≤ U
  · have ht := le_trans hu hUt
    have hn : ¬(U < γ j ∧ γ j ≤ T) := fun h ↦ not_lt_of_ge hu h.1
    simp only [blockCoefficients, heightCoefficients, ite_eq_left hu, ite_eq_left ht,
      ite_eq_right hn, sub_self, zero_mul]
  · by_cases ht : γ j ≤ t
    · have hm : U < γ j ∧ γ j ≤ T := ⟨lt_of_not_ge hu, le_trans ht htT⟩
      simp only [blockCoefficients, heightCoefficients, ite_eq_left ht, ite_eq_right hu,
        ite_eq_left hm, sub_zero]
    · simp only [blockCoefficients, heightCoefficients, ite_eq_right ht, ite_eq_right hu, sub_self,
        zero_mul, ite_self]

/-- Pointwise scalar coefficient multiplication commutes with both height cutoffs and
their difference.
Distribute the scalar over the two conditionals for the actual derivative coefficients. -/
theorem blockCoefficients_mul {ι : Type*} (γ : ι → ℝ) (a c : ι → ℂ) (U T : ℝ) (j : ι) :
    blockCoefficients γ (fun k ↦ c k * a k) U T j = c j * blockCoefficients γ a U T j := by
  simp only [blockCoefficients, heightCoefficients, mul_sub, mul_ite, mul_zero]

/-- A constant complex multiplier factors out of a finite exponential sum.
Distribute the finite sum to separate the derivative's unit factor I. -/
theorem exponentialSum_mul_left {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (c : ℂ) :
    exponentialSum s γ (fun j ↦ c * a j) = fun v ↦ c * exponentialSum s γ a v := by
  funext v
  simp only [exponentialSum, ← Finset.mul_sum, mul_assoc]

/-- Multiplication of any complex function by I preserves its energy.
Use the unit norm of I pointwise in the real energy integral. -/
theorem energy_mul_I (f : ℝ → ℂ) : energy (fun v ↦ Complex.I * f v) = energy f := by
  simp only [energy, norm_mul, Complex.norm_I, one_mul]

/-- The actual derivative energy equals that of the real-frequency weighted coefficients.
Factor out I from the finite sum and preserve its energy. -/
theorem energy_exponentialSum_derivative {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    energy (exponentialSum s γ (fun j ↦ Complex.I * γ j * a j)) =
      energy (exponentialSum s γ (fun j ↦ (γ j : ℂ) * a j)) := by
  have he :
    exponentialSum s γ (fun j ↦ Complex.I * γ j * a j) = fun v ↦
      Complex.I * exponentialSum s γ (fun j ↦ (γ j : ℂ) * a j) v := by
    simpa only [mul_assoc] using exponentialSum_mul_left s γ (fun j ↦ (γ j : ℂ) * a j) Complex.I
  rw [he, energy_mul_I]

/-- For 0 ≤ U ≤ T, a bound A on all actual intermediate prefix energies implies the
block derivative-energy bound 4(2T-U) squared A. Restrict to the actual finite block,
use the proved 4A prefix-difference bound, and apply the L2 vector Abel estimate. -/
theorem energy_block_derivative_le_of_prefix {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ)
    {U T A : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) (hA : 0 ≤ A)
    (hF : ∀ t ∈ Set.Icc U T, energy (exponentialSum s γ (heightCoefficients γ a t)) ≤ A) :
    energy (exponentialSum s γ (fun j ↦ Complex.I * γ j * blockCoefficients γ a U T j)) ≤
      4 * (2 * T - U) ^ 2 * A := by
  have hr :=
    energy_realWeighted_le_of_prefix (s.filter (fun j ↦ U < γ j ∧ γ j ≤ T)) γ a hU hUT
      (by nlinarith only [hA] : 0 ≤ 4 * A) (fun j hj ↦ (Finset.mem_filter.mp hj).2.1)
      (fun j hj ↦ (Finset.mem_filter.mp hj).2.2)
      (fun t ht ↦ by
        rw [exponentialSum_filtered_prefix s γ a ht.1 ht.2]
        exact energy_block_le_four s γ a (hF t ht) (hF U ⟨le_rfl, hUT⟩))
  rw [energy_exponentialSum_derivative]
  have he :
    (fun j ↦ (γ j : ℂ) * blockCoefficients γ a U T j) =
      blockCoefficients γ (fun j ↦ (γ j : ℂ) * a j) U T := by
    funext j
    exact (blockCoefficients_mul γ a (fun j ↦ (γ j : ℂ)) U T j).symm
  rw [he, exponentialSum_block_eq_filter s γ _ hUT]
  nlinarith only [hr]

/-- For ordered nonnegative heights, bounds A on all actual intermediate prefix energies
imply the pointwise block bound 4(1+2T-U)A. Supply the proved actual derivative energy
to the finite-sum Sobolev estimate. No derivative-energy assumption remains. -/
theorem block_point_le_of_prefix {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) {U T A : ℝ}
    (hU : 0 ≤ U) (hUT : U ≤ T) (hA : 0 ≤ A)
    (hF : ∀ t ∈ Set.Icc U T, energy (exponentialSum s γ (heightCoefficients γ a t)) ≤ A) :
    ‖exponentialSum s γ (heightCoefficients γ a T) 0 -
            exponentialSum s γ (heightCoefficients γ a U) 0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) * A := by
  exact
    block_point_le_of_derivative_bound s γ a hU hUT hA (hF T ⟨hUT, le_rfl⟩) (hF U ⟨le_rfl, hUT⟩)
      (energy_block_derivative_le_of_prefix s γ a hU hUT hA hF)

end PseudoPrime.Analysis.ExponentialMeanSquare
