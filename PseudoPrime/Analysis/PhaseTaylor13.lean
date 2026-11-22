/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Degree-twelve phase Taylor bounds -/

public section

namespace PseudoPrime.Analysis

/-- A real point within a positive radius of a center has a normalized
coordinate of magnitude at most one. This transfers centered polynomial
certificates to their corresponding phase interval. -/
theorem exists_normalized_coord {v c r : ℝ} (hr : 0 < r) (hv : |v - c| ≤ r) :
    ∃ t : ℝ, |t| ≤ 1 ∧ v = c + r * t := by
  refine ⟨(v - c) / r, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hr]
    exact (div_le_one₀ hr).2 hv
  · rw [mul_comm r, div_mul_cancel₀ _ hr.ne', add_comm, sub_add_cancel]

/-- For a real phase of magnitude at most seven, the degree-twelve complex
exponential polynomial has the stated norm error. The bound uses the general
exponential remainder estimate and supplies a finite phase-sum certificate. -/
theorem phase_taylor13_error {y : ℝ} (hy : |y| ≤ 7) :
    ‖Complex.exp ((y : ℂ) * Complex.I) -
          ∑ k ∈ Finset.range 13, ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖ ≤
      |y| ^ 13 / (13 : ℕ).factorial * 2 := by
  have hn : ‖(y : ℂ) * Complex.I‖ = |y| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hs : ‖(y : ℂ) * Complex.I‖ / (13 + 1 : ℕ) ≤ 1 / 2 := by
    rw [hn]
    norm_num only
    linarith only [hy]
  simpa only [hn] using Complex.exp_bound' (n := 13) hs

/-- Multiplying a phase by a complex coefficient scales the degree-twelve
Taylor error by its norm. Taking real parts gives the bound needed for a
single term of a signed phase sum. -/
theorem phase_real_taylor13_error (c : ℂ) {y : ℝ} (hy : |y| ≤ 7) :
    |(c * Complex.exp ((y : ℂ) * Complex.I)).re -
          (c * ∑ k ∈ Finset.range 13, ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)).re| ≤
      ‖c‖ * (|y| ^ 13 / (13 : ℕ).factorial * 2) := by
  have he := mul_le_mul_of_nonneg_left (phase_taylor13_error hy) (norm_nonneg c)
  calc
    _ =
        |(c *
              (Complex.exp ((y : ℂ) * Complex.I) -
                ∑ k ∈ Finset.range 13, ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))).re| :=
      by rw [mul_sub, Complex.sub_re]
    _ ≤
        ‖c *
            (Complex.exp ((y : ℂ) * Complex.I) -
              ∑ k ∈ Finset.range 13, ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))‖ :=
      Complex.abs_re_le_norm _
    _ =
        ‖c‖ *
          ‖Complex.exp ((y : ℂ) * Complex.I) -
              ∑ k ∈ Finset.range 13, ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖ :=
      norm_mul _ _
    _ ≤ _ := he

/-- Summing the single-phase Taylor estimates bounds the difference between a
finite real phase sum and its degree-twelve approximation. The estimate keeps
the signed polynomial sum intact and only sums the nonnegative error bounds. -/
theorem phase_sum_taylor13_error {ι : Type*} (S : Finset ι) (c : ι → ℂ) (y : ι → ℝ)
    (hy : ∀ i ∈ S, |y i| ≤ 7) :
    |(∑ i ∈ S, (c i * Complex.exp ((y i : ℂ) * Complex.I)).re) -
          (∑ i ∈ S,
            (c i * ∑ k ∈ Finset.range 13, ((y i : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)).re)| ≤
      ∑ i ∈ S, ‖c i‖ * (|y i| ^ 13 / (13 : ℕ).factorial * 2) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤
        ∑ i ∈ S,
          |(c i * Complex.exp ((y i : ℂ) * Complex.I)).re -
              (c i * ∑ k ∈ Finset.range 13, ((y i : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ phase_real_taylor13_error (c i) (hy i hi))

/-- Bounds for the magnitudes of the phase increments and complex amplitudes
give a finite numerical upper bound for the degree-twelve Taylor error. The
phase-radius bounds must be at most seven. This separates the independent
amplitude and radius certificates from the signed coefficient sum. -/
theorem phase_sum_taylor13_bound {ι : Type*} (S : Finset ι) (c : ι → ℂ) (y A R : ι → ℝ)
    (hy : ∀ i ∈ S, |y i| ≤ R i) (hR : ∀ i ∈ S, R i ≤ 7) (hA : ∀ i ∈ S, ‖c i‖ ≤ A i) :
    |(∑ i ∈ S, (c i * Complex.exp ((y i : ℂ) * Complex.I)).re) -
          (∑ i ∈ S,
            (c i * ∑ k ∈ Finset.range 13, ((y i : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)).re)| ≤
      ∑ i ∈ S, A i * (R i ^ 13 / (13 : ℕ).factorial * 2) := by
  have hsize : ∀ i ∈ S, |y i| ≤ 7 := fun i hi ↦ le_trans (hy i hi) (hR i hi)
  apply le_trans (phase_sum_taylor13_error S c y hsize)
  apply Finset.sum_le_sum
  intro i hi
  have hp := pow_le_pow_left₀ (abs_nonneg (y i)) (hy i hi) 13
  have hd := div_le_div_of_nonneg_right hp (by norm_num only : (0 : ℝ) ≤ (13 : ℕ).factorial)
  have he := mul_le_mul_of_nonneg_right hd (by norm_num only : (0 : ℝ) ≤ 2)
  have hx : 0 ≤ |y i| ^ 13 / (13 : ℕ).factorial * 2 := by
    exact
      mul_nonneg
        (div_nonneg (pow_nonneg (abs_nonneg (y i)) 13)
          (by norm_num only : (0 : ℝ) ≤ (13 : ℕ).factorial))
        (by norm_num only)
  exact mul_le_mul (hA i hi) he hx (le_trans (norm_nonneg _) (hA i hi))

/-- A real centered coordinate factors out of one complex Taylor coefficient
as `t ^ k`. This identity connects termwise phase approximations to a single
polynomial whose coefficients retain cancellation across the finite family. -/
theorem phase_taylor_term_factor (c : ℂ) (g r t : ℝ) (k : ℕ) :
    (c * ((((g * r * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))).re =
      (c * ((((g * r : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))).re * t ^ k := by
  have h : (((g * r * t : ℝ) : ℂ) * Complex.I) = (((g * r : ℝ) : ℂ) * Complex.I) * (t : ℂ) := by
    rw [Complex.ofReal_mul]
    ring
  rw [h, mul_pow]
  rw [show
      c * (((((g * r : ℝ) : ℂ) * Complex.I) ^ k * (t : ℂ) ^ k) / (k.factorial : ℂ)) =
        (c * ((((g * r : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))) * (t : ℂ) ^ k
      by ring]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- A finite sum of degree-twelve phase polynomials equals one polynomial
whose degree-`k` coefficient is the signed sum of the individual real
coefficients. The equality changes only finite sums and introduces no error. -/
theorem phase_center_poly_eq {ι : Type*} (S : Finset ι) (c : ι → ℂ) (g : ι → ℝ) (r t : ℝ) :
    (∑ i ∈ S,
        (c i *
            ∑ k ∈ Finset.range 13,
              (((g i * r * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)).re) =
      ∑ k ∈ Finset.range 13,
        (∑ i ∈ S, (c i * ((((g i * r : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))).re) *
          t ^ k := by
  simp only [Finset.mul_sum, Complex.re_sum, phase_taylor_term_factor]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- On a centered cell coordinate `|t| ≤ 1`, nonnegative heights `g` and
radius `r` give phase increments `g i * r * t`. Amplitude bounds and the
explicit conditions `g i * r ≤ 7` provide a uniform Taylor error bound for
the whole cell. -/
theorem phase_center_taylor13_bound {ι : Type*} (S : Finset ι) (c : ι → ℂ) (g A : ι → ℝ) (r t : ℝ)
    (hg : ∀ i ∈ S, 0 ≤ g i) (hr : 0 ≤ r) (ht : |t| ≤ 1) (hsize : ∀ i ∈ S, g i * r ≤ 7)
    (hA : ∀ i ∈ S, ‖c i‖ ≤ A i) :
    |(∑ i ∈ S, (c i * Complex.exp (((g i * r * t : ℝ) : ℂ) * Complex.I)).re) -
          (∑ i ∈ S,
            (c i *
                ∑ k ∈ Finset.range 13,
                  (((g i * r * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)).re)| ≤
      ∑ i ∈ S, A i * ((g i * r) ^ 13 / (13 : ℕ).factorial * 2) := by
  apply phase_sum_taylor13_bound S c (fun i ↦ g i * r * t) A (fun i ↦ g i * r) _ hsize hA
  intro i hi
  rw [abs_mul, abs_of_nonneg (mul_nonneg (hg i hi) hr)]
  calc
    g i * r * |t| ≤ g i * r * 1 := mul_le_mul_of_nonneg_left ht (mul_nonneg (hg i hi) hr)
    _ = g i * r := mul_one _

/-- The centered phase sum differs from the polynomial of signed aggregate
coefficients by at most the shared Taylor error budget. This combines the
finite coefficient identity with the cell-wide error estimate. -/
theorem phase_center_poly_error {ι : Type*} (S : Finset ι) (c : ι → ℂ) (g A : ι → ℝ) (r t : ℝ)
    (hg : ∀ i ∈ S, 0 ≤ g i) (hr : 0 ≤ r) (ht : |t| ≤ 1) (hsize : ∀ i ∈ S, g i * r ≤ 7)
    (hA : ∀ i ∈ S, ‖c i‖ ≤ A i) :
    |(∑ i ∈ S, (c i * Complex.exp (((g i * r * t : ℝ) : ℂ) * Complex.I)).re) -
          (∑ k ∈ Finset.range 13,
            (∑ i ∈ S, (c i * ((((g i * r : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))).re) *
              t ^ k)| ≤
      ∑ i ∈ S, A i * ((g i * r) ^ 13 / (13 : ℕ).factorial * 2) := by
  have h := phase_center_taylor13_bound S c g A r t hg hr ht hsize hA
  rw [phase_center_poly_eq] at h
  exact h

end PseudoPrime.Analysis
