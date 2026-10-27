/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.StepanovJets
public import Mathlib.Algebra.Polynomial.OfFn

/-! # Rectangular coefficient arrays and actual auxiliary polynomials -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The linear projection to one coefficient of a C by A by B array. It supplies the coefficient
functionals in the rectangular polynomial map. -/
def rectangularCoefficient {R : Type*} [CommRing R] (A B C : ℕ) (c : Fin C) (a : Fin A)
    (b : Fin B) : (Fin C → Fin A → Fin B → R) →ₗ[R] R
    where
  toFun v := v c a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear map from a rectangular coefficient array to the sum of scalar multiples of X^a
Y^b Z^c. Indices range over Fin A, Fin B and Fin C. -/
noncomputable def rectangularPolynomial {R : Type*} [CommRing R] (A B C : ℕ) :
    (Fin C → Fin A → Fin B → R) →ₗ[R] MvPolynomial (Fin 3) R :=
  ∑ c : Fin C,
    ∑ a : Fin A,
      ∑ b : Fin B,
        (rectangularCoefficient A B C c a b).smulRight
          (MvPolynomial.X 0 ^ (a : ℕ) * MvPolynomial.X 1 ^ (b : ℕ) * MvPolynomial.X 2 ^ (c : ℕ) :
            MvPolynomial (Fin 3) R)

/-- The explicit monomial expansion of the rectangular polynomial map. Unfold the sum of
coefficient functionals. -/
theorem rectangularPolynomial_apply {R : Type*} [CommRing R] (A B C : ℕ)
    (v : Fin C → Fin A → Fin B → R) :
    rectangularPolynomial A B C v =
      ∑ c : Fin C,
        ∑ a : Fin A,
          ∑ b : Fin B,
            v c a b •
              (MvPolynomial.X 0 ^ (a : ℕ) * MvPolynomial.X 1 ^ (b : ℕ) *
                MvPolynomial.X 2 ^ (c : ℕ)) := by
  simp only [rectangularPolynomial, LinearMap.sum_apply, LinearMap.smulRight_apply,
    rectangularCoefficient]
  rfl

/-- If every polynomial in a finite sum has total degree at most N, so does the sum. Apply the
support supremum bound. -/
theorem totalDegree_sum_le_of_bound {R σ ι : Type*} [CommSemiring R] (S : Finset ι)
    (F : ι → MvPolynomial σ R) (N : ℕ) (h : ∀ i ∈ S, (F i).totalDegree ≤ N) :
    (∑ i ∈ S, F i).totalDegree ≤ N :=
  (MvPolynomial.totalDegree_finsetSum S F).trans (Finset.sup_le h)

/-- The rectangular polynomial has total degree at most A+B+C over a nontrivial commutative
ring. Bound the degree of each scalar monomial before summing. -/
theorem totalDegree_rectangularPolynomial_le {R : Type*} [CommRing R] [Nontrivial R] (A B C : ℕ)
    (v : Fin C → Fin A → Fin B → R) : (rectangularPolynomial A B C v).totalDegree ≤ A + B + C := by
  rw [rectangularPolynomial_apply]
  apply totalDegree_sum_le_of_bound
  intro c _
  apply totalDegree_sum_le_of_bound
  intro a _
  apply totalDegree_sum_le_of_bound
  intro b _
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  have h1 :=
    MvPolynomial.totalDegree_mul (MvPolynomial.X (0 : Fin 3) ^ (a : ℕ) : MvPolynomial (Fin 3) R)
      (MvPolynomial.X 1 ^ (b : ℕ))
  have h2 :=
    MvPolynomial.totalDegree_mul
      (MvPolynomial.X (0 : Fin 3) ^ (a : ℕ) * MvPolynomial.X 1 ^ (b : ℕ) : MvPolynomial (Fin 3) R)
      (MvPolynomial.X 2 ^ (c : ℕ))
  simp only [MvPolynomial.totalDegree_X_pow] at h1 h2
  linarith only [h1, h2, a.isLt, b.isLt, c.isLt]

/-- The same coefficient array encoded as R[Y][X][Z] using Polynomial.ofFn at each level. This
interfaces with the proved nonvanishing and degree theorems. -/
noncomputable def rectangularNested {R : Type*} [CommRing R] [DecidableEq R] (A B C : ℕ)
    (v : Fin C → Fin A → Fin B → R) : Polynomial (Polynomial (Polynomial R)) :=
  Polynomial.ofFn C (fun c ↦ Polynomial.ofFn A (fun a ↦ Polynomial.ofFn B (v c a)))

/-- Taking the three indexed coefficients of the nested polynomial recovers the input array
entry. Use the coefficient formula for ofFn. -/
theorem rectangularNested_coeff {R : Type*} [CommRing R] [DecidableEq R] (A B C : ℕ)
    (v : Fin C → Fin A → Fin B → R) (c : Fin C) (a : Fin A) (b : Fin B) :
    (((rectangularNested A B C v).coeff c).coeff a).coeff b = v c a b := by
  simp only [rectangularNested, Polynomial.ofFn_coeff_eq_val_of_lt _ c.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt _ a.isLt, Polynomial.ofFn_coeff_eq_val_of_lt _ b.isLt]

/-- A nonzero coefficient array gives a nonzero nested polynomial. If the polynomial vanished,
all three-index coefficients would be zero. -/
theorem rectangularNested_ne_zero {R : Type*} [CommRing R] [DecidableEq R] (A B C : ℕ)
    (v : Fin C → Fin A → Fin B → R) (hv : v ≠ 0) : rectangularNested A B C v ≠ 0 := by
  intro hz
  apply hv
  funext c a b
  have he :=
    congrArg (fun P : Polynomial (Polynomial (Polynomial R)) ↦ ((P.coeff c).coeff a).coeff b) hz
  simpa only [rectangularNested_coeff, Polynomial.coeff_zero, Pi.zero_apply] using he

/-- Evaluation of a coefficient vector polynomial is the finite sum of the mapped coefficients
times powers. Expand ofFn into its monomials. -/
theorem eval₂_ofFn_sum {R S : Type*} [CommRing R] [CommRing S] [DecidableEq R] (f : R →+* S) (x : S)
    (N : ℕ) (v : Fin N → R) :
    (Polynomial.ofFn N v).eval₂ f x = ∑ i : Fin N, f (v i) * x ^ (i : ℕ) := by
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  exact Polynomial.eval₂_monomial _ _

/-- Actual evaluation of the multivariate rectangular polynomial equals Frobenius-logarithmic
substitution of the nested encoding. Expand both finite sums and compare monomials. -/
theorem stepanovEvaluation_rectangular_eq {p A B C : ℕ} (v : Fin C → Fin A → Fin B → ZMod p) :
    stepanovEvaluation p (rectangularPolynomial A B C v) =
      frobeniusLogarithmicSubstitution (rectangularNested A B C v) := by
  classical
  rw [rectangularPolynomial_apply, map_sum, frobeniusLogarithmicSubstitution, rectangularNested,
    eval₂_ofFn_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_sum]
  change
    (∑ a : Fin A,
        stepanovEvaluation p
          (∑ b : Fin B,
            v c a b •
              (MvPolynomial.X 0 ^ (a : ℕ) * MvPolynomial.X 1 ^ (b : ℕ) *
                MvPolynomial.X 2 ^ (c : ℕ)))) =
      (Polynomial.ofFn A (fun a ↦ Polynomial.ofFn B (v c a))).eval₂
          (Polynomial.compRingHom (truncatedLog p)) Polynomial.X *
        (Polynomial.X ^ p) ^ (c : ℕ)
  rw [eval₂_ofFn_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum]
  change
    (∑ b : Fin B,
        stepanovEvaluation p
          (v c a b •
            (MvPolynomial.X 0 ^ (a : ℕ) * MvPolynomial.X 1 ^ (b : ℕ) *
              MvPolynomial.X 2 ^ (c : ℕ)))) =
      Polynomial.compRingHom (truncatedLog p) (Polynomial.ofFn B (v c a)) * Polynomial.X ^ (a : ℕ) *
        (Polynomial.X ^ p) ^ (c : ℕ)
  rw [Polynomial.coe_compRingHom_apply, Polynomial.comp, eval₂_ofFn_sum, Finset.sum_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [← MvPolynomial.C_mul', map_mul, map_pow, stepanovEvaluation_C, stepanovEvaluation_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-- For prime p, A,B positive and AB<=p, a nonzero coefficient array gives a nonzero actual
auxiliary polynomial. Transfer to the nested encoding and apply Lemma 17. -/
theorem stepanovEvaluation_rectangular_ne_zero {p A B C : ℕ} [Fact p.Prime]
    (v : Fin C → Fin A → Fin B → ZMod p) (hv : v ≠ 0) (hA : 0 < A) (hB : 0 < B) (hAB : A * B ≤ p) :
    stepanovEvaluation p (rectangularPolynomial A B C v) ≠ 0 := by
  classical
  rw [stepanovEvaluation_rectangular_eq]
  apply frobenius_logarithmic_substitution_ne_zero _ hB hAB (rectangularNested_ne_zero A B C v hv)
  · intro c
    by_cases hc : c < C
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_val_of_lt _ hc]
      exact Polynomial.ofFn_natDegree_lt hA _
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hc),
        Polynomial.natDegree_zero]
      exact hA
  · intro c a
    by_cases hc : c < C
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_val_of_lt _ hc]
      by_cases ha : a < A
      · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ ha]
        exact Polynomial.ofFn_natDegree_lt hB _
      · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt ha), Polynomial.natDegree_zero]
        exact hB
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hc),
        Polynomial.coeff_zero, Polynomial.natDegree_zero]
      exact hB

/-- For positive A,B,C, the nested rectangular encoding has the required strict degree bounds in
all variables. Apply the ofFn bounds coefficientwise. -/
theorem rectangularNested_degree_bounds {R : Type*} [CommRing R] [DecidableEq R] (A B C : ℕ)
    (v : Fin C → Fin A → Fin B → R) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    (rectangularNested A B C v).natDegree < C ∧
      (∀ c : ℕ, ((rectangularNested A B C v).coeff c).natDegree < A) ∧
      ∀ c a : ℕ, (((rectangularNested A B C v).coeff c).coeff a).natDegree < B := by
  refine ⟨Polynomial.ofFn_natDegree_lt hC _, ?_, ?_⟩
  · intro c
    by_cases hc : c < C
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_val_of_lt _ hc]
      exact Polynomial.ofFn_natDegree_lt hA _
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hc),
        Polynomial.natDegree_zero]
      exact hA
  · intro c a
    by_cases hc : c < C
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_val_of_lt _ hc]
      by_cases ha : a < A
      · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ ha]
        exact Polynomial.ofFn_natDegree_lt hB _
      · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt ha), Polynomial.natDegree_zero]
        exact hB
    · rw [rectangularNested, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hc),
        Polynomial.coeff_zero, Polynomial.natDegree_zero]
      exact hB

end PseudoPrime.NumberTheory.Heilbronn
