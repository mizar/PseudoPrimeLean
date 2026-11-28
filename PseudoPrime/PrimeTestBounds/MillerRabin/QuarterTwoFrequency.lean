/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-! # Two-frequency square completion for the sixth-pole zero sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At one zero, the difference of two auxiliary phases costs exactly the
cosine deficit at their separation. Expand the two real squares to bound the
main phase without discarding this cancellation. -/
theorem two_frequency_phase_le (θ b t k : ℝ) :
    k * (Real.cos b - Real.cos t + Real.cos (θ - b) - Real.cos (θ - t)) -
        k ^ 2 * (1 - Real.cos (t - b)) ≤
      1 + Real.cos θ := by
  have hx := sq_nonneg (1 + Real.cos θ - k * (Real.cos b - Real.cos t))
  have hy := sq_nonneg (Real.sin θ - k * (Real.sin b - Real.sin t))
  simp only [Real.cos_sub]
  nlinarith only [hx, hy, Real.sin_sq_add_cos_sq θ,
    congrArg (fun u : ℝ ↦ k ^ 2 * u) (Real.sin_sq_add_cos_sq b),
    congrArg (fun u : ℝ ↦ k ^ 2 * u) (Real.sin_sq_add_cos_sq t)]

/-- Summing the pointwise estimate with nonnegative weights gives the phase
bound over a finite multiset of zero indices, including repeated ordinates. -/
theorem two_frequency_sum_le {ι : Type*} (s : Finset ι) (w θ g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (b t k : ℝ) :
    (∑ i ∈ s,
        w i *
          (k *
              (Real.cos (b * g i) - Real.cos (t * g i) + Real.cos (θ i - b * g i) -
                Real.cos (θ i - t * g i)) -
            k ^ 2 * (1 - Real.cos ((t - b) * g i)))) ≤
      ∑ i ∈ s, w i * (1 + Real.cos (θ i)) := by
  apply Finset.sum_le_sum
  intro i hi
  rw [sub_mul]
  exact mul_le_mul_of_nonneg_left (two_frequency_phase_le _ _ _ _) (hw i hi)

/-- For any summable nonnegative zero weights, the two-shift lower bound holds
for the full sums. All five cosine series converge by domination by the mass. -/
theorem two_frequency_tsum_le {ι : Type*} (w θ g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (b t k : ℝ) :
    let W := fun (f : ι → ℝ) ↦ ∑' i, w i * Real.cos (f i)
    let M := ∑' i, w i
    k *
          (W (fun i ↦ b * g i) - W (fun i ↦ t * g i) + W (fun i ↦ θ i - b * g i) -
            W (fun i ↦ θ i - t * g i)) -
        k ^ 2 * (M - W (fun i ↦ (t - b) * g i)) ≤
      M + W θ := by
  intro W M
  have hc (f : ι → ℝ) : Summable (fun i ↦ w i * Real.cos (f i)) := by
    apply hs.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have h (f : ι → ℝ) := (hc f).hasSum
  have hl :=
    (((((h (fun i ↦ b * g i)).sub (h (fun i ↦ t * g i))).add (h (fun i ↦ θ i - b * g i))).sub
              (h (fun i ↦ θ i - t * g i))).mul_left
          k).sub
      ((hs.hasSum.sub (h (fun i ↦ (t - b) * g i))).mul_left (k ^ 2))
  apply hasSum_le _ hl (hs.hasSum.add (h θ))
  intro i
  have hi := mul_le_mul_of_nonneg_left (two_frequency_phase_le (θ i) (b * g i) (t * g i) k) (hw i)
  rw [sub_mul t b]
  linarith only [hi]

/-- Expanding the two real squares gives the phase bound with independent coefficients
for the two auxiliary frequencies. Their interaction retains the cosine of the separation. -/
theorem two_frequency_weighted_le (θ b t u v : ℝ) :
    u * (Real.cos b + Real.cos (θ - b)) - v * (Real.cos t + Real.cos (θ - t)) -
          (u ^ 2 + v ^ 2) / 2 +
        u * v * Real.cos (t - b) ≤
      1 + Real.cos θ := by
  have hx := sq_nonneg (1 + Real.cos θ - u * Real.cos b + v * Real.cos t)
  have hy := sq_nonneg (Real.sin θ - u * Real.sin b + v * Real.sin t)
  simp only [Real.cos_sub]
  nlinarith only [hx, hy, Real.sin_sq_add_cos_sq θ,
    congrArg (fun x : ℝ ↦ u ^ 2 * x) (Real.sin_sq_add_cos_sq b),
    congrArg (fun x : ℝ ↦ v ^ 2 * x) (Real.sin_sq_add_cos_sq t)]

/-- Summable nonnegative weights lift the independent-coefficient phase bound
to the cosine sums used in the two-shift zero comparison. -/
theorem two_frequency_weighted_tsum {ι : Type*} (w θ g : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (b t u v : ℝ) :
    let W := fun (f : ι → ℝ) ↦ ∑' i, w i * Real.cos (f i)
    let M := ∑' i, w i
    u * (W (fun i ↦ b * g i) + W (fun i ↦ θ i - b * g i)) -
          v * (W (fun i ↦ t * g i) + W (fun i ↦ θ i - t * g i)) -
          ((u ^ 2 + v ^ 2) / 2) * M +
        (u * v) * W (fun i ↦ (t - b) * g i) ≤
      M + W θ := by
  intro W M
  have hc (f : ι → ℝ) : Summable (fun i ↦ w i * Real.cos (f i)) := by
    apply hs.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have h (f : ι → ℝ) := (hc f).hasSum
  have hb := ((h (fun i ↦ b * g i)).add (h (fun i ↦ θ i - b * g i))).mul_left u
  have ht := ((h (fun i ↦ t * g i)).add (h (fun i ↦ θ i - t * g i))).mul_left v
  have hl :=
    ((hb.sub ht).sub (hs.hasSum.mul_left ((u ^ 2 + v ^ 2) / 2))).add
      ((h (fun i ↦ (t - b) * g i)).mul_left (u * v))
  apply hasSum_le _ hl (hs.hasSum.add (h θ))
  intro i
  have hi :=
    mul_le_mul_of_nonneg_left (two_frequency_weighted_le (θ i) (b * g i) (t * g i) u v) (hw i)
  rw [sub_mul t b]
  linarith only [hi]

end PseudoPrime.PrimeTestBounds.MillerRabin
