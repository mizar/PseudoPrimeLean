/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquare

/-!
# Finite exponential sums and their weighted energies

The rational Gram kernel and the weighted real-line integral agree. Cross terms are
retained when taking differences of partial sums.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- A finite exponential sum with real frequencies and arbitrary complex coefficients.
The finite index set counts multiplicity. This is the input to the mean-square identities. -/
noncomputable def exponentialSum {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (v : ℝ) : ℂ :=
  ∑ j ∈ s, a j * Complex.exp (Complex.I * γ j * v)

/-- Translate a finite exponential sum by shifting its coefficients by the center phase.
Distribute the frequency over the translated argument and combine the two exponentials. -/
theorem exponentialSum_translate {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (w v₀ : ℝ) :
    exponentialSum s γ a (w + v₀) =
      exponentialSum s γ (fun j ↦ a j * Complex.exp (Complex.I * γ j * v₀)) w := by
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro j hj
  have harg :
    Complex.I * γ j * ((w + v₀ : ℝ) : ℂ) =
      Complex.I * γ j * (v₀ : ℂ) + Complex.I * γ j * (w : ℂ) := by
    rw [Complex.ofReal_add]
    ring
  rw [harg, Complex.exp_add]
  ring

/-- The complex weighted product of two functions at a real displacement.
Its diagonal has real part `‖f v‖^2 * weight v`. It retains the cross terms. -/
noncomputable def crossIntegrand (f g : ℝ → ℂ) (v : ℝ) : ℂ :=
  f v * starRingEnd ℂ (g v) * (weight v : ℂ)

/-- The real weighted mean square of a function on the real line.
It is nonnegative; later integrability lemmas justify its use for finite exponential sums. -/
noncomputable def energy (f : ℝ → ℂ) : ℝ :=
  ∫ v : ℝ, ‖f v‖ ^ 2 * weight v

/-- For real frequencies, multiplying one phase by a conjugate subtracts frequencies.
Conjugate the exponent and use the exponential addition formula in the Gram expansion. -/
theorem phase_mul_conj (u w v : ℝ) :
    Complex.exp (Complex.I * u * v) * starRingEnd ℂ (Complex.exp (Complex.I * w * v)) =
      Complex.exp (Complex.I * (u - w) * v) := by
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- For two finite sums, the weighted product is a finite sum of weighted phases.
Distribute both sums and combine phases; this justifies termwise integration. -/
theorem crossIntegrand_exponentialSum {ι κ : Type*} (s : Finset ι) (r : Finset κ) (γ : ι → ℝ)
    (δ : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) (v : ℝ) :
    crossIntegrand (exponentialSum s γ a) (exponentialSum r δ b) v =
      ∑ j ∈ s, ∑ k ∈ r, (a j * starRingEnd ℂ (b k)) * kernelIntegrand (γ j - δ k) v := by
  simp only [crossIntegrand, exponentialSum, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul]
  calc
    _ =
        (a j * starRingEnd ℂ (b k)) *
          (Complex.exp (Complex.I * γ j * v) * starRingEnd ℂ (Complex.exp (Complex.I * δ k * v))) *
          (weight v : ℂ) :=
      by ring
    _ = _ := by
      rw [phase_mul_conj, kernelIntegrand]
      simp only [Complex.ofReal_sub]
      ring

/-- Every weighted product of finite exponential sums is integrable.
Use the finite expansion into integrable weighted phases, retaining complex cross terms. -/
theorem integrable_cross_exponentialSum {ι κ : Type*} (s : Finset ι) (r : Finset κ) (γ : ι → ℝ)
    (δ : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    MeasureTheory.Integrable (crossIntegrand (exponentialSum s γ a) (exponentialSum r δ b)) := by
  have h :=
    MeasureTheory.integrable_finsetSum s
      (fun j hj ↦
        MeasureTheory.integrable_finsetSum r
          (fun k hk ↦
            (integrable_kernelIntegrand (γ j - δ k)).const_mul (a j * starRingEnd ℂ (b k))))
  exact
    h.congr
      (Filter.Eventually.of_forall (fun v ↦ (crossIntegrand_exponentialSum s r γ δ a b v).symm))

/-- The integral of a finite weighted product is its rational Gram pairing.
Integrate the finite expansion and evaluate each Laplace Fourier kernel.
This provides the analytic nonnegative-kernel representation. -/
theorem integral_cross_exponentialSum {ι κ : Type*} (s : Finset ι) (r : Finset κ) (γ : ι → ℝ)
    (δ : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ v : ℝ, crossIntegrand (exponentialSum s γ a) (exponentialSum r δ b) v) =
      ∑ j ∈ s,
        ∑ k ∈ r, (a j * starRingEnd ℂ (b k)) * ((4 : ℂ) / (4 + ((γ j - δ k : ℝ) : ℂ) ^ 2)) := by
  simp only [crossIntegrand_exponentialSum]
  rw [MeasureTheory.integral_finsetSum s
      (fun j hj ↦
        MeasureTheory.integrable_finsetSum r
          (fun k hk ↦
            (integrable_kernelIntegrand (γ j - δ k)).const_mul (a j * starRingEnd ℂ (b k))))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MeasureTheory.integral_finsetSum r
      (fun k hk ↦ (integrable_kernelIntegrand (γ j - δ k)).const_mul (a j * starRingEnd ℂ (b k)))]
  simp only [MeasureTheory.integral_const_mul, integral_kernelIntegrand]

/-- The diagonal weighted product is the real inclusion of the squared norm times the weight.
Use the conjugate-product identity to identify the integrand of the energy. -/
theorem crossIntegrand_self (f : ℝ → ℂ) (v : ℝ) :
    crossIntegrand f f v = ((‖f v‖ ^ 2 * weight v : ℝ) : ℂ) := by
  rw [crossIntegrand, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]

/-- For any function, its energy is the real part of the diagonal complex integral.
Commute real inclusion with integration; this identifies the two energy conventions. -/
theorem energy_eq_re_integral (f : ℝ → ℂ) : energy f = (∫ v : ℝ, crossIntegrand f f v).re := by
  simp only [crossIntegrand_self, integral_complex_ofReal, Complex.ofReal_re, energy]

/-- Every function has nonnegative energy under the Bochner integral convention.
The integrand is a square times a positive exponential; finite sums are integrable below. -/
theorem energy_nonneg (f : ℝ → ℂ) : 0 ≤ energy f := by
  exact
    MeasureTheory.integral_nonneg
      (fun v ↦ mul_nonneg (sq_nonneg ‖f v‖) (Real.exp_pos (-2 * |v|)).le)

/-- The energy of a finite exponential sum equals the real part of its rational Gram pairing.
Use the diagonal integral identity and termwise Fourier integration.
This is the mean-square formula with all cross terms retained. -/
theorem energy_exponentialSum {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    energy (exponentialSum s γ a) =
      (∑ j ∈ s,
          ∑ k ∈ s,
            (a j * starRingEnd ℂ (a k)) * ((4 : ℂ) / (4 + ((γ j - γ k : ℝ) : ℂ) ^ 2))).re := by
  rw [energy_eq_re_integral, integral_cross_exponentialSum]

/-- The real mean-square integrand of a finite exponential sum is integrable.
Take the real part of its integrable diagonal product to justify integral comparisons. -/
theorem integrable_energy_exponentialSum {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    MeasureTheory.Integrable (fun v : ℝ ↦ ‖exponentialSum s γ a v‖ ^ 2 * weight v) := by
  have h := (integrable_cross_exponentialSum s s γ γ a a).re
  simpa only [RCLike.re_to_complex, crossIntegrand_self, Complex.ofReal_re] using h

/-- For arbitrary real frequencies and complex coefficients, the rational Gram energy is
nonnegative.
Identify it with the nonnegative integral; no zero-distribution hypothesis is required. -/
theorem gram_nonneg {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    0 ≤
      (∑ j ∈ s,
          ∑ k ∈ s,
            (a j * starRingEnd ℂ (a k)) * ((4 : ℂ) / (4 + ((γ j - γ k : ℝ) : ℂ) ^ 2))).re := by
  rw [← energy_exponentialSum]
  exact energy_nonneg _

end PseudoPrime.Analysis.ExponentialMeanSquare
