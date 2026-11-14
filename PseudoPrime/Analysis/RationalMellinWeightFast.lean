/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalMellinWeight

/-! # Transposed rational Mellin weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Scalar multiplication distributes over a finite sum of rational pairs. -/
theorem rational_scale_sum {ι : Type*} (s : Finset ι) (c : ℚ) (f : ι → ℚ × ℚ) :
    rationalComplexScale c (∑ i ∈ s, f i) = ∑ i ∈ s, rationalComplexScale c (f i) := by
  apply Prod.ext <;> simp only [rationalComplexScale, Prod.fst_sum, Prod.snd_sum, Finset.mul_sum]

/-- Summing rational scalar multiples of one pair factors out that pair. -/
theorem rational_sum_scale {ι : Type*} (s : Finset ι) (c : ι → ℚ) (z : ℚ × ℚ) :
    (∑ i ∈ s, rationalComplexScale (c i) z) = rationalComplexScale (∑ i ∈ s, c i) z := by
  apply Prod.ext <;> simp only [rationalComplexScale, Prod.fst_sum, Prod.snd_sum, Finset.sum_mul]

/-- Consecutive rational scalar multiplications multiply their scalars. -/
theorem rational_scale_scale (a b : ℚ) (z : ℚ × ℚ) :
    rationalComplexScale a (rationalComplexScale b z) = rationalComplexScale (a * b) z := by
  apply Prod.ext <;> dsimp only [rationalComplexScale] <;> ring

/-- A finite triangular sum can be evaluated by the inner index first.
The interval is empty automatically when its lower endpoint is too large. -/
theorem sum_triangle_transpose {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    (∑ l ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (l + 1), f l j) =
      ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.Icc j n, f l j := by
  apply Finset.sum_comm'
  intro l j
  simp only [Finset.mem_range, Nat.lt_succ_iff, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨⟨h.2, h.1⟩, Nat.le_trans h.2 h.1⟩
  · intro h
    exact ⟨h.1.2, h.1.1⟩

/-- The rational Gaussian weight with the finite triangular sum transposed.
Each falling product is formed once for its index and scaled by the sum of
its coefficients. Inputs and output agree with `rationalGaussianWeight`. -/
def rationalGaussianWeightFast (t a b p : ℚ) (n k : ℕ) : ℚ × ℚ :=
  rationalComplexScale 2
    (∑ j ∈ Finset.range (n + 1),
      rationalComplexScale
        ((a ^ j)⁻¹ *
          ∑ l ∈ Finset.Icc j n,
            ((l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) * (l.choose j : ℚ) *
              (-p * ((k : ℚ) + 1) ^ 2) ^ (l - j))
        (rationalMellinFalling t j))

/-- Transposing the finite weight sum preserves its exact rational value.
The proof distributes scalar products and exchanges the triangular indices. -/
theorem rational_gaussian_weight_fast_eq (t a b p : ℚ) (n k : ℕ) :
    rationalGaussianWeightFast t a b p n k = rationalGaussianWeight t a b p n k := by
  rw [rationalGaussianWeightFast, rationalGaussianWeight]
  congr 1
  simp only [rationalGaussianPoly, rational_scale_sum, rational_scale_scale]
  rw [sum_triangle_transpose]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rational_sum_scale]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

end PseudoPrime.Analysis
