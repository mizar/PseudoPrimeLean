/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.Tactic

/-!
# Integral models of quadratic number fields

Construct an integral quadratic algebra model and identify its discriminant with the
number-field discriminant. The model provides coordinates for later proofs about
fundamental discriminants and prime ideal splitting.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For integral `a`, `b` and `z` in the algebra with `ω² = a + bω`, the algebra trace
is `2z.re + b z.im`. Compute it in the canonical basis `1, ω`.
The diagonal entries of multiplication by `z` are `z.re` and `z.re + b * z.im`.
This calculation supplies the trace matrix used for the integral discriminant. -/
private theorem quadraticAlgebra_trace (a b : ℤ) (z : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) z = 2 * z.re + b * z.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  simp only [Algebra.leftMulMatrix_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
    QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.basis_apply_zero,
    QuadraticAlgebra.basis_apply_one, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_omega,
    QuadraticAlgebra.im_omega, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
    add_zero, zero_add]
  ring

/-- The canonical basis of the integral quadratic algebra has discriminant `b² + 4a`.
Compute its four trace pairings and the determinant of the resulting two by two matrix.
This identifies the number-field discriminant after transporting an integral basis. -/
private theorem quadraticAlgebra_discr (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = b ^ 2 + 4 * a := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, quadraticAlgebra_trace,
    QuadraticAlgebra.basis_apply_zero, QuadraticAlgebra.basis_apply_one, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, mul_one, mul_zero, add_zero, zero_add]
  ring

/-- A degree-two number field has an integral quadratic algebra model with its exact discriminant.
The equivalence identifies the entire ring of integers, rather than an arbitrary quadratic order.
Its coefficients `a`, `b` describe a generator satisfying `ω² = a + bω`;
the field discriminant is `b² + 4a`. Complete `1` to an integral basis, then transport
its trace discriminant along the algebra equivalence. This supplies integral coordinates
for the arithmetic construction of the character attached to a quadratic field. -/
theorem quadratic_ringOfIntegers_model (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    ∃ a b : ℤ,
      ∃ _f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b,
        NumberField.discr K = b ^ 2 + 4 * a := by
  let : Algebra.IsQuadraticExtension ℤ (NumberField.RingOfIntegers K) :=
    ⟨(NumberField.RingOfIntegers.rank K).trans h⟩
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A :=
      NumberField.RingOfIntegers K)
  refine ⟨a, b, f, ?_⟩
  have hd := NumberField.discr_eq_discr K ((QuadraticAlgebra.basis a b).map f.symm.toLinearEquiv)
  rw [← hd, Algebra.discr_eq_discr_of_algEquiv _ f]
  have he :
    (fun i => f (((QuadraticAlgebra.basis a b).map f.symm.toLinearEquiv) i)) =
      (QuadraticAlgebra.basis a b : Fin 2 → QuadraticAlgebra ℤ a b) := by
    funext i
    exact f.apply_symm_apply _
  change
    Algebra.discr ℤ (fun i => f (((QuadraticAlgebra.basis a b).map f.symm.toLinearEquiv) i)) = _
  rw [he]
  exact quadraticAlgebra_discr a b

/-- The discriminant of a degree-two number field is congruent to zero or one modulo four.
The integral quadratic model expresses it as `b² + 4a`; the square residue is `b % 2`.
This proves the congruence condition required for a fundamental discriminant,
without asserting the separate primitivity condition on square divisors. -/
theorem quadratic_discr_emod_four (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) : NumberField.discr K % 4 = 0 ∨ NumberField.discr K % 4 = 1 := by
  obtain ⟨a, b, _f, hd⟩ := quadratic_ringOfIntegers_model K h
  simp only [hd, Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod, add_zero,
    Int.sq_emod_four]
  rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · exact Or.inl (hb ▸ Int.zero_emod 4)
  · rw [hb]
    right
    norm_num only

end PseudoPrime.NumberTheory
