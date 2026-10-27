/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic

/-! # Positivity of signed exponential combinations from finite moment certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For any finite signed real combination, its power-moment series sums to the
corresponding exponential combination at every real t. Induct on the list
and combine the absolutely convergent exponential series exactly. -/
theorem hasSum_list_exp_moments {ι : Type*} (l : List ι) (b r : ι → ℝ) (t : ℝ) :
    HasSum (fun k : ℕ ↦ ((l.map (fun i ↦ b i * (r i) ^ k)).sum) * t ^ k / k.factorial)
      ((l.map (fun i ↦ b i * Real.exp (r i * t))).sum) := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.sum_nil, zero_mul, zero_div] using
      (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
  | cons a l ih =>
    have ha := (NormedSpace.expSeries_div_hasSum_exp (r a * t)).mul_left (b a)
    rw [← Real.exp_eq_exp_ℝ] at ha
    simpa only [List.map_cons, List.sum_cons, add_mul, add_div, mul_pow, mul_div_assoc,
      mul_assoc] using ha.add ih

/-- If all signed power moments are nonnegative, the exponential combination is
nonnegative for t>=0. Use the moment series with nonnegative factorial terms.
No sign assumption on individual coefficients is required. -/
theorem list_exp_nonneg_of_moments {ι : Type*} (l : List ι) (b r : ι → ℝ)
    (hm : ∀ k : ℕ, 0 ≤ (l.map (fun i ↦ b i * (r i) ^ k)).sum) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (l.map (fun i ↦ b i * Real.exp (r i * t))).sum := by
  exact
    HasSum.nonneg (fun k ↦ div_nonneg (mul_nonneg (hm k) (pow_nonneg ht k)) (Nat.cast_nonneg _))
      (hasSum_list_exp_moments l b r t)

/-- For 0<=r<=R and any signed weight b, a higher weighted power is bounded
below by its negative part at order n times R^k. Compare powers only after
retaining the coefficient sign. Used to certify every moment beyond a fixed order. -/
theorem weighted_power_lower_of_range {b r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) (n k : ℕ) :
    -(max 0 (-b) * r ^ n) * R ^ k ≤ b * r ^ (n + k) := by
  have hb : -max 0 (-b) ≤ b := by linarith only [le_max_right 0 (-b)]
  have hp := pow_le_pow_left₀ hr hR k
  have h1 := mul_le_mul_of_nonneg_right hb (pow_nonneg hr (n + k))
  have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg (le_max_left 0 (-b)) (pow_nonneg hr n))
  rw [pow_add] at h1 ⊢
  nlinarith only [h1, h2]

/-- If an anchor dominates the negative moment at order n and all remaining
bases lie in [0,R], the full moment is nonnegative at every order n+k.
Sum the signed lower bounds and retain the anchor before multiplying by R^k. -/
theorem list_moment_tail_nonneg {ι : Type*} (l : List ι) (b r : ι → ℝ) {B R : ℝ} (hR : 0 ≤ R)
    (hr : ∀ i ∈ l, 0 ≤ r i ∧ r i ≤ R) (n k : ℕ)
    (hcert : (l.map (fun i ↦ max 0 (-b i) * (r i) ^ n)).sum ≤ B * R ^ n) :
    0 ≤ B * R ^ (n + k) + (l.map (fun i ↦ b i * (r i) ^ (n + k))).sum := by
  have ht (i : ι) (hi : i ∈ l) : (-R ^ k) * (max 0 (-b i) * (r i) ^ n) ≤ b i * (r i) ^ (n + k) := by
    have h := weighted_power_lower_of_range (b := b i) (hr i hi).1 (hr i hi).2 n k
    nlinarith only [h]
  have hs := List.sum_le_sum ht
  rw [List.sum_map_mul_left] at hs
  have hc := mul_le_mul_of_nonneg_right hcert (pow_nonneg hR k)
  rw [pow_add]
  nlinarith only [hs, hc]

/-- A nonnegative largest anchor, finitely many nonnegative moments below N,
and domination of all negative coefficients at order N imply nonnegativity
of every moment. Split the natural order and apply the uniform tail theorem. -/
theorem list_moments_nonneg_of_finite_certificate {ι : Type*} (a : ι) (l : List ι) (b r : ι → ℝ)
    {N : ℕ} (ha : 0 ≤ r a) (hr : ∀ i ∈ l, 0 ≤ r i ∧ r i ≤ r a)
    (hsmall : ∀ n < N, 0 ≤ ((a :: l).map (fun i ↦ b i * (r i) ^ n)).sum)
    (hcert : (l.map (fun i ↦ max 0 (-b i) * (r i) ^ N)).sum ≤ b a * (r a) ^ N) :
    ∀ n : ℕ, 0 ≤ ((a :: l).map (fun i ↦ b i * (r i) ^ n)).sum := by
  intro n
  by_cases hn : n < N
  · exact hsmall n hn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    simpa only [List.map_cons, List.sum_cons] using list_moment_tail_nonneg l b r ha hr N k hcert

end PseudoPrime.Analysis
