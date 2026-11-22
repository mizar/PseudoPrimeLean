/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Finite sums with explicit integer endpoint constructors -/

public section

namespace PseudoPrime.Analysis

/-- Termwise real interval bounds give containment in the interval whose
endpoints are the exact integer sums. The explicit constructor permits
independent kernel reduction of endpoint sums in certificate consumers. -/
theorem finite_sum_explicit_contains {ι : Type*} (S : Finset ι) (R : ι → IntegerInterval)
    (v : ι → ℝ) (G : ℤ) (h : ∀ i ∈ S, (R i).Contains G (v i)) :
    (IntegerInterval.mk (∑ i ∈ S, (R i).lower) (∑ i ∈ S, (R i).upper)).Contains G
      (∑ i ∈ S, v i) := by
  constructor
  · change ((∑ i ∈ S, (R i).lower : ℤ) : ℝ) / G ≤ ∑ i ∈ S, v i
    rw [Int.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum (fun i hi ↦ (h i hi).1)
  · change (∑ i ∈ S, v i) ≤ ((∑ i ∈ S, (R i).upper : ℤ) : ℝ) / G
    rw [Int.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum (fun i hi ↦ (h i hi).2)

/-- Integer-weighted finite sums are enclosed by adding the scaled input
intervals. Negative weights reverse endpoint order through `scale`; each
coefficient transformation can therefore be checked independently. -/
theorem weighted_sum_contains {ι : Type*} (S : Finset ι) (R : ι → IntegerInterval) (c : ι → ℤ)
    (v : ι → ℝ) (G : ℤ) (h : ∀ i ∈ S, (R i).Contains G (v i)) :
    (IntegerInterval.mk (∑ i ∈ S, ((R i).scale (c i)).lower)
          (∑ i ∈ S, ((R i).scale (c i)).upper)).Contains
      G (∑ i ∈ S, (c i : ℝ) * v i) := by
  exact
    finite_sum_explicit_contains S (fun i ↦ (R i).scale (c i)) (fun i ↦ (c i : ℝ) * v i) G
      (fun i hi ↦ IntegerInterval.scale_contains (h i hi))

/-- Dividing a contained real number by a positive integer multiplies the
interval scale by that integer. This avoids rounding when a common denominator
is used for rational linear combinations. -/
theorem IntegerInterval.div_scale_contains {I : IntegerInterval} {G D : ℤ} {x : ℝ} (hD : 0 < D)
    (hx : I.Contains G x) : I.Contains (G * D) (x / D) := by
  have hd : (0 : ℝ) ≤ D := by exact_mod_cast hD.le
  constructor
  · simpa only [IntegerInterval.Contains, Int.cast_mul, div_div] using
      div_le_div_of_nonneg_right hx.1 hd
  · simpa only [IntegerInterval.Contains, Int.cast_mul, div_div] using
      div_le_div_of_nonneg_right hx.2 hd

/-- Integer interval bounds for a rational linear combination with common
positive denominator. Signed numerator weights are handled termwise, and
the denominator is carried exactly in the output scale. -/
theorem weighted_sum_div_contains {ι : Type*} (S : Finset ι) (R : ι → IntegerInterval) (c : ι → ℤ)
    (v : ι → ℝ) (G D : ℤ) (hD : 0 < D) (h : ∀ i ∈ S, (R i).Contains G (v i)) :
    (IntegerInterval.mk (∑ i ∈ S, ((R i).scale (c i)).lower)
          (∑ i ∈ S, ((R i).scale (c i)).upper)).Contains
      (G * D) ((∑ i ∈ S, (c i : ℝ) * v i) / D) := by
  exact IntegerInterval.div_scale_contains hD (weighted_sum_contains S R c v G h)

/-- Certified complex coordinates compose into a finite sum with explicit
integer endpoint sums. No indexed list lookup or unproved summation identity
is required to consume a generated finite Dirichlet certificate. -/
theorem complex_sum_explicit_contains {ι : Type*} (S : Finset ι) (R I : ι → IntegerInterval)
    (v : ι → ℂ) (G : ℤ) (h : ∀ i ∈ S, complexIntervalContains (R i) (I i) G (v i)) :
    complexIntervalContains ⟨∑ i ∈ S, (R i).lower, ∑ i ∈ S, (R i).upper⟩
      ⟨∑ i ∈ S, (I i).lower, ∑ i ∈ S, (I i).upper⟩ G (∑ i ∈ S, v i) := by
  constructor
  · rw [Complex.re_sum]
    exact finite_sum_explicit_contains S R (fun i ↦ (v i).re) G (fun i hi ↦ (h i hi).1)
  · rw [Complex.im_sum]
    exact finite_sum_explicit_contains S I (fun i ↦ (v i).im) G (fun i hi ↦ (h i hi).2)

end PseudoPrime.Analysis
