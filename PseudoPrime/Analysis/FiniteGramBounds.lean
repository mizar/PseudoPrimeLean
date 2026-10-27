/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Finite Gram matrix bounds -/

@[expose] public section

namespace PseudoPrime.Analysis.FiniteGramBounds

/--
Inputs: a finite index type, a nonnegative real weight on ordered pairs, a real vector, and a
uniform upper bound for every row and column sum of the weights.

Claim: the weighted bilinear form is bounded by the row-sum bound times the vector's squared
Euclidean norm.

Proof: apply $2ab \le a^2+b^2$ termwise, then use the row and column bounds on the two resulting
quadratic sums.

Role: supplies the finite Schur estimate needed to control the Gram form in the additive large
sieve argument.
-/
theorem real_nonnegative_bilinear_le_row_col_sums {ι : Type*} [Fintype ι] (w : ι → ι → ℝ)
    (v : ι → ℝ) (R : ℝ) (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, (∑ j, w i j) ≤ R)
    (hcol : ∀ j, (∑ i, w i j) ≤ R) : ∑ i, ∑ j, w i j * (v i * v j) ≤ R * ∑ i, (v i) ^ 2 := by
  classical
  have hleft : (∑ i, ∑ j, w i j * (v i) ^ 2) ≤ R * ∑ i, (v i) ^ 2 := by
    calc
      _ = ∑ i, (v i) ^ 2 * ∑ j, w i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_mul]
        exact mul_comm _ _
      _ ≤ ∑ i, R * (v i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          (v i) ^ 2 * ∑ j, w i j ≤ (v i) ^ 2 * R :=
            mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (v i))
          _ = R * (v i) ^ 2 := by ring
      _ = _ := by rw [← Finset.mul_sum]
  have hright : (∑ i, ∑ j, w i j * (v j) ^ 2) ≤ R * ∑ i, (v i) ^ 2 := by
    calc
      _ = ∑ j, (v j) ^ 2 * ∑ i, w i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul]
        exact mul_comm _ _
      _ ≤ ∑ j, R * (v j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (v j) ^ 2 * ∑ i, w i j ≤ (v j) ^ 2 * R :=
            mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg (v j))
          _ = R * (v j) ^ 2 := by ring
      _ = _ := by rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, ((1 / 2 : ℝ) * (w i j * (v i) ^ 2) + (1 / 2 : ℝ) * (w i j * (v j) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        w i j * (v i * v j) ≤ w i j * ((v i ^ 2 + v j ^ 2) / 2) := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith only [sq_nonneg (v i - v j)]
          · exact hw i j
        _ = _ := by ring
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, w i j * (v i) ^ 2) + (1 / 2 : ℝ) * (∑ i, ∑ j, w i j * (v j) ^ 2) :=
      by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) * (R * ∑ i, (v i) ^ 2) + (1 / 2 : ℝ) * (R * ∑ i, (v i) ^ 2) := by
      exact
        add_le_add (mul_le_mul_of_nonneg_left hleft (by norm_num only))
          (mul_le_mul_of_nonneg_left hright (by norm_num only))
    _ = _ := by ring

/--
Inputs: a finite index type, a nonnegative symmetric real weight on ordered pairs, and a real
vector.

Claim: the weighted bilinear form is bounded by the sum of the squared coordinates weighted by
their Gram row sums.

Proof: apply $2ab \le a^2+b^2$ termwise; symmetry makes the two resulting sums equal to the
row-sum-weighted square sum.

Role: gives the variable-row form of Schur's estimate used in Selberg's inner-product inequality.
-/
theorem real_symmetric_bilinear_le_weighted_row_sums {ι : Type*} [Fintype ι] (w : ι → ι → ℝ)
    (v : ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hsym : ∀ i j, w i j = w j i) :
    ∑ i, ∑ j, w i j * (v i * v j) ≤ ∑ i, (v i) ^ 2 * ∑ j, w i j := by
  classical
  have hleft : (∑ i, ∑ j, w i j * (v i) ^ 2) = ∑ i, (v i) ^ 2 * ∑ j, w i j := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_mul]
    exact mul_comm _ _
  have hright : (∑ i, ∑ j, w i j * (v j) ^ 2) = ∑ j, (v j) ^ 2 * ∑ i, w j i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      _ = (∑ i, w i j) * (v j) ^ 2 := by rw [← Finset.sum_mul]
      _ = (v j) ^ 2 * ∑ i, w j i := by
        rw [show (∑ i, w i j) = ∑ i, w j i
            by
            apply Finset.sum_congr rfl
            intro i hi
            exact hsym i j]
        exact mul_comm _ _
  calc
    _ ≤ ∑ i, ∑ j, ((1 / 2 : ℝ) * (w i j * (v i) ^ 2) + (1 / 2 : ℝ) * (w i j * (v j) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        w i j * (v i * v j) ≤ w i j * ((v i ^ 2 + v j ^ 2) / 2) := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith only [sq_nonneg (v i - v j)]
          · exact hw i j
        _ = _ := by ring
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, w i j * (v i) ^ 2) + (1 / 2 : ℝ) * (∑ i, ∑ j, w i j * (v j) ^ 2) :=
      by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i, (v i) ^ 2 * ∑ j, w i j := by
      rw [hleft, hright]
      ring

/--
Inputs: a finite complex matrix whose entry norms are symmetric, and a finite complex coefficient
vector.

Claim: the real part of the associated Gram quadratic form is bounded by the coefficient norms
weighted by the row sums of the entry norms.

Proof: bound the real part by the norm, apply the triangle inequality to the finite double sum,
and use `real_symmetric_bilinear_le_weighted_row_sums`.

Role: converts a complex inner-product Gram expansion into the real Schur estimate needed by
Selberg's large-sieve argument.
-/
theorem complex_gram_real_part_le_weighted_row_sums {ι : Type*} [Fintype ι] (g : ι → ι → ℂ)
    (c : ι → ℂ) (hsym : ∀ i j, ‖g i j‖ = ‖g j i‖) :
    Complex.re (∑ i, ∑ j, star (c i) * c j * g i j) ≤ ∑ i, (‖c i‖) ^ 2 * ∑ j, ‖g i j‖ := by
  classical
  have hnormsum : ‖∑ i, ∑ j, star (c i) * c j * g i j‖ ≤ ∑ i, ∑ j, ‖star (c i) * c j * g i j‖ := by
    calc
      _ ≤ ∑ i, ‖∑ j, star (c i) * c j * g i j‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
  calc
    _ ≤ ‖∑ i, ∑ j, star (c i) * c j * g i j‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖star (c i) * c j * g i j‖ := hnormsum
    _ = ∑ i, ∑ j, ‖g i j‖ * (‖c i‖ * ‖c j‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_star]
      ring
    _ ≤ ∑ i, (‖c i‖) ^ 2 * ∑ j, ‖g i j‖ := by
      exact
        real_symmetric_bilinear_le_weighted_row_sums (fun i j => ‖g i j‖) (fun i => ‖c i‖)
          (fun _ _ => norm_nonneg _) hsym

/--
Inputs: a finite family of vectors in a complex inner-product space and complex coefficients.

Claim: the squared norm of their linear combination is bounded by the coefficient norm squares
weighted by the row sums of the norms of pairwise inner products.

Proof: expand the squared norm as the real part of the Gram quadratic form and apply
`complex_gram_real_part_le_weighted_row_sums`.

Role: is the inner-product form of the Schur estimate used to prove the additive large sieve.
-/
theorem inner_product_sum_smul_norm_sq_le_weighted_gram_rows {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (φ : ι → E) (c : ι → ℂ) :
    ‖∑ i, c i • φ i‖ ^ 2 ≤ ∑ i, (‖c i‖) ^ 2 * ∑ j, ‖inner ℂ (φ i) (φ j)‖ := by
  classical
  let z : E := ∑ i, c i • φ i
  let g : ι → ι → ℂ := fun i j => inner ℂ (φ i) (φ j)
  have hexpand : inner ℂ z z = ∑ i, ∑ j, star (c i) * c j * g i j := by
    dsimp only [z]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_smul_left, inner_smul_right]
    dsimp only [g]
    simp only [starRingEnd_apply]
    ac_rfl
  have hsym : ∀ i j, ‖g i j‖ = ‖g j i‖ := by
    intro i j
    exact norm_inner_symm (φ i) (φ j)
  calc
    _ = Complex.re (inner ℂ z z) := by
      change ‖z‖ ^ 2 = Complex.re (inner ℂ z z)
      exact norm_sq_eq_re_inner (𝕜 := ℂ) z
    _ = Complex.re (∑ i, ∑ j, star (c i) * c j * g i j) := by rw [hexpand]
    _ ≤ ∑ i, (‖c i‖) ^ 2 * ∑ j, ‖g i j‖ := complex_gram_real_part_le_weighted_row_sums g c hsym
    _ = _ := by simp only [g]

/--
Inputs: a finite family of vectors in a complex inner-product space, complex coefficients, and a
uniform upper bound for the Gram row sums.

Claim: the squared norm of the linear combination is bounded by the row-sum bound times the
coefficient norm-square sum.

Proof: apply `inner_product_sum_smul_norm_sq_le_weighted_gram_rows`, then use the uniform row bound
termwise and factor the constant out of the finite sum.

Role: is the dual large-sieve interface once the additive frequency Gram rows have been bounded.
-/
theorem inner_product_sum_smul_norm_sq_le_of_gram_row_bound {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (φ : ι → E) (c : ι → ℂ) (R : ℝ)
    (hrow : ∀ i, (∑ j, ‖inner ℂ (φ i) (φ j)‖) ≤ R) :
    ‖∑ i, c i • φ i‖ ^ 2 ≤ R * ∑ i, (‖c i‖) ^ 2 := by
  calc
    _ ≤ ∑ i, (‖c i‖) ^ 2 * ∑ j, ‖inner ℂ (φ i) (φ j)‖ :=
      inner_product_sum_smul_norm_sq_le_weighted_gram_rows φ c
    _ ≤ ∑ i, (‖c i‖) ^ 2 * R := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (‖c i‖))
    _ = _ := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _

/--
Inputs: a finite family of vectors in a complex inner-product space, a nonnegative uniform bound
for its Gram row sums, and a test vector.

Claim: the sum of squared inner products of the family with the test vector is bounded by the
Gram row bound times the test vector's squared norm.

Proof: choose the family inner products as synthesis coefficients, use the synthesis estimate,
and apply Cauchy-Schwarz to the resulting inner product.

Role: transfers the dual synthesis bound to the additive large-sieve analysis operator.
-/
theorem sum_inner_product_norm_sq_le_of_gram_row_bound {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (φ : ι → E) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, (∑ j, ‖inner ℂ (φ i) (φ j)‖) ≤ R) (x : E) :
    (∑ i, ‖inner ℂ (φ i) x‖ ^ 2) ≤ R * ‖x‖ ^ 2 := by
  classical
  let c : ι → ℂ := fun i => inner ℂ (φ i) x
  let A : ℝ := ∑ i, ‖c i‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg (‖c i‖)
  have hinner : inner ℂ x (∑ i, c i • φ i) = (A : ℂ) := by
    rw [inner_sum]
    calc
      (∑ i, inner ℂ x (c i • φ i)) = ∑ i, (↑(‖c i‖ : ℝ) ^ 2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_smul_right]
        have hsym : inner ℂ x (φ i) = star (c i) := by exact (inner_conj_symm x (φ i)).symm
        rw [hsym]
        exact Complex.mul_conj' _
      _ = (A : ℂ) := by
        dsimp only [A]
        rw [Complex.ofReal_sum]
        simp only [Complex.ofReal_pow]
  have hT : ‖∑ i, c i • φ i‖ ^ 2 ≤ R * A := by
    simpa only [A] using inner_product_sum_smul_norm_sq_le_of_gram_row_bound φ c R hrow
  have hCauchy : A ≤ ‖x‖ * ‖∑ i, c i • φ i‖ := by
    calc
      A = ‖(A : ℂ)‖ := (Complex.norm_of_nonneg hA).symm
      _ = ‖inner ℂ x (∑ i, c i • φ i)‖ := by rw [hinner]
      _ ≤ _ := norm_inner_le_norm _ _
  have hB : 0 ≤ ‖x‖ * ‖∑ i, c i • φ i‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hA2 : A ^ 2 ≤ (‖x‖ * ‖∑ i, c i • φ i‖) ^ 2 := by
    calc
      A ^ 2 = A * A := by ring
      _ ≤ (‖x‖ * ‖∑ i, c i • φ i‖) * (‖x‖ * ‖∑ i, c i • φ i‖) := mul_le_mul hCauchy hCauchy hA hB
      _ = (‖x‖ * ‖∑ i, c i • φ i‖) ^ 2 := by ring
  have hprod : A * A ≤ (R * ‖x‖ ^ 2) * A := by
    calc
      A * A = A ^ 2 := by ring
      _ ≤ (‖x‖ * ‖∑ i, c i • φ i‖) ^ 2 := hA2
      _ = ‖x‖ ^ 2 * ‖∑ i, c i • φ i‖ ^ 2 := by ring
      _ ≤ ‖x‖ ^ 2 * (R * A) := mul_le_mul_of_nonneg_left hT (sq_nonneg ‖x‖)
      _ = (R * ‖x‖ ^ 2) * A := by ring
  by_cases hApos : 0 < A
  · change A ≤ R * ‖x‖ ^ 2
    exact le_of_mul_le_mul_right hprod hApos
  · have hAzero : A = 0 := le_antisymm (le_of_not_gt hApos) hA
    change A ≤ R * ‖x‖ ^ 2
    rw [hAzero]
    exact mul_nonneg hR (sq_nonneg ‖x‖)

end PseudoPrime.Analysis.FiniteGramBounds
