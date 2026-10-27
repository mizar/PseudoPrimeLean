/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquarePointBounds

/-!
# Height-prefix interfaces for finite exponential sums

The energy of the difference is controlled by the endpoint prefix energies.
The sharper pointwise height estimate additionally needs a derivative-energy bound.
That bound is kept explicit, rather than assumed as a pair-correlation conjecture.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- Coefficients of the prefix at height T: keep entries with frequency at most T.
Repeated frequencies retain their separate indices. This defines actual finite prefixes. -/
noncomputable def heightCoefficients {ι : Type*} (γ : ι → ℝ) (a : ι → ℂ) (T : ℝ) (j : ι) : ℂ :=
  if γ j ≤ T then a j else 0

/-- Coefficients of the difference of the prefixes at T and U.
For U ≤ T this keeps exactly U < gamma ≤ T. It supplies the finite-sum Sobolev estimate. -/
noncomputable def blockCoefficients {ι : Type*} (γ : ι → ℝ) (a : ι → ℂ) (U T : ℝ) (j : ι) : ℂ :=
  heightCoefficients γ a T j - heightCoefficients γ a U j

/-- The actual height block equals the difference of the two actual height prefixes.
Apply finite coefficient subtraction; no cancellation of energy cross terms is assumed. -/
theorem exponentialSum_block {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (U T : ℝ) :
    exponentialSum s γ (blockCoefficients γ a U T) = fun v ↦
      exponentialSum s γ (heightCoefficients γ a T) v -
        exponentialSum s γ (heightCoefficients γ a U) v := by
  exact exponentialSum_sub s γ _ _

/-- If the two endpoint prefix energies are bounded by A, the actual block energy is at most 4A.
Apply the finite-sum factor-two bound to the actual two prefix coefficient families. -/
theorem energy_block_le_four {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) {U T A : ℝ}
    (hT : energy (exponentialSum s γ (heightCoefficients γ a T)) ≤ A)
    (hU : energy (exponentialSum s γ (heightCoefficients γ a U)) ≤ A) :
    energy (exponentialSum s γ (blockCoefficients γ a U T)) ≤ 4 * A := by
  rw [exponentialSum_block]
  exact energy_exponentialSum_sub_le_four s s γ γ _ _ hT hU

/-- For nonnegative A and B, energies E ≤ 4A and E' ≤ 4B squared A imply the explicit
point bound 4(1+B)A. Bound the square-root product in the proved finite-sum Sobolev estimate. -/
theorem exponentialSum_point_le_of_energy_derivative_bound {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (a : ι → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : energy (exponentialSum s γ a) ≤ 4 * A)
    (hD : energy (exponentialSum s γ (fun j ↦ Complex.I * γ j * a j)) ≤ 4 * B ^ 2 * A) :
    ‖exponentialSum s γ a 0‖ ^ 2 ≤ 4 * (1 + B) * A := by
  have h := exponentialSum_norm_zero_sq_le s γ a
  have hm :=
    mul_le_mul hE hD (energy_nonneg (exponentialSum s γ (fun j ↦ Complex.I * γ j * a j)))
      (by nlinarith only [hA] : 0 ≤ 4 * A)
  have hs :
    Real.sqrt (energy (exponentialSum s γ a)) *
        Real.sqrt (energy (exponentialSum s γ (fun j ↦ Complex.I * γ j * a j))) ≤
      4 * B * A := by
    apply
      (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (by nlinarith only [hA, hB] : 0 ≤ 4 * B * A)).mp
    rw [mul_pow, Real.sq_sqrt (energy_nonneg _), Real.sq_sqrt (energy_nonneg _)]
    nlinarith only [hm]
  nlinarith only [h, hE, hs]

/-- For ordered nonnegative heights, endpoint prefix energies bounded by A and the explicit
block derivative-energy bound imply 4(1+2T-U)A as a pointwise bound.
Use the actual block energy and finite-sum Sobolev theorem.
The derivative-energy inequality remains an explicit input and is not proved here. -/
theorem block_point_le_of_derivative_bound {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ)
    {U T A : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) (hA : 0 ≤ A)
    (hT : energy (exponentialSum s γ (heightCoefficients γ a T)) ≤ A)
    (hU' : energy (exponentialSum s γ (heightCoefficients γ a U)) ≤ A)
    (hD :
      energy (exponentialSum s γ (fun j ↦ Complex.I * γ j * blockCoefficients γ a U T j)) ≤
        4 * (2 * T - U) ^ 2 * A) :
    ‖exponentialSum s γ (heightCoefficients γ a T) 0 -
            exponentialSum s γ (heightCoefficients γ a U) 0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) * A := by
  have hB : 0 ≤ 2 * T - U := by linarith only [hU, hUT]
  have h :=
    exponentialSum_point_le_of_energy_derivative_bound s γ (blockCoefficients γ a U T) hA hB
      (energy_block_le_four s γ a hT hU') hD
  rw [exponentialSum_block] at h
  nlinarith only [h]

end PseudoPrime.Analysis.ExponentialMeanSquare
