/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareHeightBounds
public import PseudoPrime.Analysis.FiniteHeightAbel

/-! # Real-height Abel summation in the L2 realization of weighted exponential sums -/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- The actual L2 class of the normalized finite exponential sum.
Its squared norm is the weighted energy, allowing vector-valued Abel summation. -/
noncomputable def normalizedLp {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  (memLp_normalize (continuous_exponentialSum s γ a) (integrable_energy_exponentialSum s γ a)).toLp
    (normalize (exponentialSum s γ a))

/-- One normalized phase as an L2 vector, represented by a singleton exponential sum.
The coefficient is included in the vector, and repeated frequencies remain separate summands. -/
noncomputable def atomLp (γ : ℝ) (a : ℂ) :
    MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  normalizedLp ({()} : Finset Unit) (fun _ ↦ γ) (fun _ ↦ a)

/-- The L2 realization agrees almost everywhere with the actual normalized finite sum.
Apply the representative theorem for the supplied L2 membership. -/
theorem coe_normalizedLp {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    (normalizedLp s γ a : ℝ → ℂ) =ᵐ[MeasureTheory.volume] normalize (exponentialSum s γ a) := by
  exact MeasureTheory.MemLp.coeFn_toLp _

/-- The squared norm of the actual L2 vector equals the weighted exponential-sum energy.
Use the L2 inner product integral and the a.e. normalized representative. -/
theorem norm_normalizedLp_sq {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    ‖normalizedLp s γ a‖ ^ 2 = energy (exponentialSum s γ a) := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def, ←
    integral_re (MeasureTheory.L2.integrable_inner (normalizedLp s γ a) (normalizedLp s γ a))]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  apply MeasureTheory.integral_congr_ae
  exact (coe_normalizedLp s γ a).mono (fun v hv ↦ by simp only [hv, norm_normalize_sq])

/-- A phase atom is represented almost everywhere by its normalized complex phase.
Specialize the singleton construction, retaining the real normalizing scalar. -/
theorem coe_atomLp (γ : ℝ) (a : ℂ) :
    (atomLp γ a : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
      (fun v ↦ decay v • (a * Complex.exp (Complex.I * γ * v))) := by
  exact
    (coe_normalizedLp ({()} : Finset Unit) (fun _ ↦ γ) (fun _ ↦ a)).mono
      (fun v hv ↦ by simpa only [atomLp, normalize, exponentialSum, Finset.sum_singleton] using hv)

/-- If each L2 vector has the normalized phase representative, their finite sum is the actual
L2 exponential sum. Compare representatives on one common full-measure set. -/
theorem sum_eq_normalizedLp_of_ae {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ)
    (u : ι → MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hu :
      ∀ j ∈ s,
        (u j : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
          (fun v ↦ decay v • (a j * Complex.exp (Complex.I * γ j * v)))) :
    (∑ j ∈ s, u j) = normalizedLp s γ a := by
  apply MeasureTheory.Lp.ext
  have hAll := (Filter.eventually_all_finset s).mpr hu
  filter_upwards [MeasureTheory.Lp.coeFn_finsetSum s u, hAll, coe_normalizedLp s γ a] with v hsum
    hall hnorm
  rw [hsum, hnorm]
  simp only [Finset.sum_apply, normalize, exponentialSum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j hj ↦ hall j hj)

/-- The sum of actual L2 phase atoms equals the L2 realization of the actual exponential sum.
Supply the singleton representatives to the finite-sum identity. -/
theorem sum_atomLp {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    (∑ j ∈ s, atomLp (γ j) (a j)) = normalizedLp s γ a := by
  exact sum_eq_normalizedLp_of_ae s γ a _ (fun j hj ↦ coe_atomLp (γ j) (a j))

/-- Real scalar multiplication of each phase atom multiplies its complex coefficient.
Use the scalar action on L2 representatives and distribute the normalizing scalar. -/
theorem sum_real_smul_atomLp {ι : Type*} (s : Finset ι) (γ r : ι → ℝ) (a : ι → ℂ) :
    (∑ j ∈ s, r j • atomLp (γ j) (a j)) = normalizedLp s γ (fun j ↦ (r j : ℂ) * a j) := by
  apply sum_eq_normalizedLp_of_ae s γ (fun j ↦ (r j : ℂ) * a j)
  intro j hj
  filter_upwards [MeasureTheory.Lp.coeFn_smul (r j) (atomLp (γ j) (a j)),
    coe_atomLp (γ j) (a j)] with v hr ha
  rw [hr]
  simp only [Pi.smul_apply, ha, Complex.real_smul]
  ring

/-- The actual L2 height prefix equals the realization of the finite exponential prefix.
Choose each atom or zero according to its height and compare the a.e. representatives. -/
theorem prefix_atomLp {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    PseudoPrime.Analysis.FiniteHeightAbel.heightPrefix s γ (fun j ↦ atomLp (γ j) (a j)) t =
      normalizedLp s γ (heightCoefficients γ a t) := by
  apply sum_eq_normalizedLp_of_ae s γ (heightCoefficients γ a t)
  intro j hj
  by_cases h : γ j ≤ t
  · simpa only [heightCoefficients, ite_eq_left h] using coe_atomLp (γ j) (a j)
  · simpa only [heightCoefficients, ite_eq_right h, zero_mul, smul_zero, Pi.zero_def] using
      (MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := MeasureTheory.volume))

end PseudoPrime.Analysis.ExponentialMeanSquare
