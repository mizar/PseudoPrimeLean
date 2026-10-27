/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.FrobeniusAuxiliary
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.FinCases

/-! # Stepanov jets and affine specialization -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The derivation g(X) partial_X+(X-Z) partial_Y on three variables, where g=X(1-X). The Z
derivative is zero. After Y=f(X), Z=X^p this encodes weighted ordinary differentiation. -/
noncomputable def stepanovDerivation {R : Type*} [CommRing R] :
    Derivation R (MvPolynomial (Fin 3) R) (MvPolynomial (Fin 3) R) :=
  (MvPolynomial.X 0 * (1 - MvPolynomial.X 0) : MvPolynomial (Fin 3) R) • MvPolynomial.pderiv 0 +
    (MvPolynomial.X 0 - MvPolynomial.X 2 : MvPolynomial (Fin 3) R) • MvPolynomial.pderiv 1

/-- The explicit two-term formula for the Stepanov derivation. Unfold scalar multiplication of
derivations. -/
theorem stepanovDerivation_apply {R : Type*} [CommRing R] (F : MvPolynomial (Fin 3) R) :
    stepanovDerivation F =
      MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * MvPolynomial.pderiv 0 F +
        (MvPolynomial.X 0 - MvPolynomial.X 2) * MvPolynomial.pderiv 1 F := by
  simp only [stepanovDerivation, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

/-- The ring homomorphism substituting X, the truncated logarithm f(X), and X^p for the three
variables. It produces the actual auxiliary polynomial. -/
noncomputable def stepanovEvaluation (p : ℕ) :
    MvPolynomial (Fin 3) (ZMod p) →+* Polynomial (ZMod p) :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, truncatedLog p, Polynomial.X ^ p]

/-- The evaluation of a variable is its assigned substitution. Use the universal evaluation
homomorphism. -/
theorem stepanovEvaluation_X (p : ℕ) (i : Fin 3) :
    stepanovEvaluation p (MvPolynomial.X i) =
      ![Polynomial.X, truncatedLog p, Polynomial.X ^ p] i := by
  exact MvPolynomial.eval₂_X _ _ _

/-- For prime p, the evaluated derivation of each variable equals g times its evaluated ordinary
derivative. Use the truncated-log identity and characteristic p. -/
theorem stepanovEvaluation_derivation_X {p : ℕ} [Fact p.Prime] (i : Fin 3) :
    stepanovEvaluation p (stepanovDerivation (MvPolynomial.X i)) =
      weight p * Polynomial.derivative (stepanovEvaluation p (MvPolynomial.X i)) := by
  rw [stepanovDerivation_apply, stepanovEvaluation_X]
  fin_cases i
  · change
      stepanovEvaluation p
          ((MvPolynomial.X (0 : Fin 3) * (1 - MvPolynomial.X 0)) *
              MvPolynomial.pderiv 0 (MvPolynomial.X 0) +
            (MvPolynomial.X 0 - MvPolynomial.X 2) * MvPolynomial.pderiv 1 (MvPolynomial.X 0)) =
        weight p * Polynomial.derivative (Polynomial.X : Polynomial (ZMod p))
    rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1)]
    simp only [mul_one, mul_zero, add_zero, map_mul, stepanovEvaluation_X, Matrix.cons_val_zero,
      map_sub, map_one, weight, Polynomial.derivative_X]
  · change
      stepanovEvaluation p
          ((MvPolynomial.X (0 : Fin 3) * (1 - MvPolynomial.X 0)) *
              MvPolynomial.pderiv 0 (MvPolynomial.X 1) +
            (MvPolynomial.X 0 - MvPolynomial.X 2) * MvPolynomial.pderiv 1 (MvPolynomial.X 1)) =
        weight p * Polynomial.derivative (truncatedLog p : Polynomial (ZMod p))
    rw [MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0), MvPolynomial.pderiv_X_self,
      mul_zero, mul_one, zero_add, map_sub]
    simp only [stepanovEvaluation_X, Matrix.cons_val_zero, Matrix.cons_val_two]
    exact (weight_mul_derivative_truncatedLog (p := p)).symm
  · change
      stepanovEvaluation p
          ((MvPolynomial.X (0 : Fin 3) * (1 - MvPolynomial.X 0)) *
              MvPolynomial.pderiv 0 (MvPolynomial.X 2) +
            (MvPolynomial.X 0 - MvPolynomial.X 2) * MvPolynomial.pderiv 1 (MvPolynomial.X 2)) =
        weight p * Polynomial.derivative (Polynomial.X ^ p : Polynomial (ZMod p))
    rw [MvPolynomial.pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0),
      MvPolynomial.pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1), mul_zero, mul_zero, add_zero,
      map_zero, Polynomial.derivative_X_pow, ZMod.natCast_self, Polynomial.C_0, zero_mul, mul_zero]

/-- For prime p and any trivariate polynomial, evaluation intertwines the Stepanov derivation
with g times the ordinary derivative. Prove this on constants, sums and variable products. -/
theorem stepanovEvaluation_derivation {p : ℕ} [Fact p.Prime] (F : MvPolynomial (Fin 3) (ZMod p)) :
    stepanovEvaluation p (stepanovDerivation F) =
      weight p * Polynomial.derivative (stepanovEvaluation p F) := by
  induction F using MvPolynomial.induction_on with
  | C
    a =>
    rw [show stepanovDerivation (MvPolynomial.C a) = 0 by exact Derivation.map_algebraMap _ a,
      map_zero]
    simp only [stepanovEvaluation, MvPolynomial.eval₂Hom_C, Polynomial.derivative_C, mul_zero]
  | add F G hF hG => rw [map_add, map_add, hF, hG, map_add, Polynomial.derivative_add, mul_add]
  | mul_X F i
    hF =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hF,
      stepanovEvaluation_derivation_X, map_mul, Polynomial.derivative_mul]
    ring

/-- The linear r-th weighted jet operator. Start at the identity and recur by
delta(J_r)-r(1-2X)J_r. Evaluation equals g^r times the ordinary r-th derivative. -/
noncomputable def stepanovJet {R : Type*} [CommRing R] :
    ℕ → MvPolynomial (Fin 3) R →ₗ[R] MvPolynomial (Fin 3) R
  | 0 => LinearMap.id
  | r + 1 =>
    stepanovDerivation.toLinearMap.comp (stepanovJet r) -
      (LinearMap.mulLeft R
            (MvPolynomial.C (r : R) * (1 - MvPolynomial.C 2 * MvPolynomial.X 0))).comp
        (stepanovJet r)

/-- The derivative of the clearing weight g=X(1-X) is 1-2X over every ZMod ring. Expand the
product and collect terms. -/
theorem derivative_weight (p : ℕ) :
    Polynomial.derivative (weight p) = 1 - Polynomial.C (2 : ZMod p) * Polynomial.X := by
  rw [weight, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X, Polynomial.C_ofNat]
  ring

/-- Constants evaluate to constant univariate polynomials. This supplies the coefficient
compatibility of the evaluation. -/
theorem stepanovEvaluation_C (p : ℕ) (a : ZMod p) :
    stepanovEvaluation p (MvPolynomial.C a) = Polynomial.C a := by
  exact MvPolynomial.eval₂Hom_C _ _ _

/-- The evaluated correction factor 1-2X is the derivative of the clearing weight. Apply
evaluation to its two terms. -/
theorem stepanovEvaluation_slope (p : ℕ) :
    stepanovEvaluation p (1 - MvPolynomial.C (2 : ZMod p) * MvPolynomial.X 0) =
      Polynomial.derivative (weight p) := by
  rw [map_sub, map_one, map_mul, stepanovEvaluation_C, stepanovEvaluation_X, derivative_weight]
  rfl

/-- For every nonnegative r over a commutative ring, differentiating g^r F and subtracting the
weight derivative leaves g^(r+1)F'. Include the zero-order case explicitly. -/
theorem weighted_derivative_step_all {R : Type*} [CommRing R] (g F : Polynomial R) (r : ℕ) :
    g * Polynomial.derivative (g ^ r * F) -
        Polynomial.C (r : R) * Polynomial.derivative g * (g ^ r * F) =
      g ^ (r + 1) * Polynomial.derivative F := by
  cases r with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_zero, Polynomial.C_0, zero_mul, sub_zero, Nat.zero_add,
      pow_one]
  | succ r => exact weighted_derivative_step g F r

/-- The defining recurrence of the weighted jet at order r+1. It removes the derivative of g^r. -/
theorem stepanovJet_apply {R : Type*} [CommRing R] (r : ℕ) (F : MvPolynomial (Fin 3) R) :
    stepanovJet (r + 1) F =
      stepanovDerivation (stepanovJet r F) -
        MvPolynomial.C (r : R) * (1 - MvPolynomial.C 2 * MvPolynomial.X 0) * stepanovJet r F :=
  rfl

/-- For prime p, evaluating the r-th jet gives g^r times the r-th derivative of the auxiliary
polynomial. Induct with the weighted derivative recurrence. -/
theorem stepanovEvaluation_jet {p : ℕ} [Fact p.Prime] (F : MvPolynomial (Fin 3) (ZMod p)) (r : ℕ) :
    stepanovEvaluation p (stepanovJet r F) =
      weight p ^ r * Polynomial.derivative^[r] (stepanovEvaluation p F) := by
  induction r with
  | zero =>
    change stepanovEvaluation p F = weight p ^ 0 * (stepanovEvaluation p F)
    rw [pow_zero, one_mul]
  | succ r
    ih =>
    rw [stepanovJet_apply, map_sub, map_mul, map_mul, stepanovEvaluation_derivation,
      stepanovEvaluation_C, stepanovEvaluation_slope, ih, weighted_derivative_step_all]
    rw [Function.iterate_succ_apply']

/-- A partial derivative does not increase total degree over any commutative semiring. Compare
each nonzero coefficient with the exponent shifted by one. -/
theorem totalDegree_pderiv_le {R σ : Type*} [CommSemiring R] (i : σ) (F : MvPolynomial σ R) :
    (MvPolynomial.pderiv i F).totalDegree ≤ F.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc))
  have hs : (m + Finsupp.single i 1).sum (fun _ e ↦ e) = m.sum (fun _ e ↦ e) + 1 := by
    rw [Finsupp.sum_add_index (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl),
      Finsupp.sum_single_index (by rfl)]
  rw [hs] at hd
  linarith only [hd]

/-- Over a nontrivial commutative ring, the Stepanov derivation increases total degree by at
most two. Bound its two polynomial coefficients and partial derivatives. -/
theorem totalDegree_stepanovDerivation_le {R : Type*} [CommRing R] [Nontrivial R]
    (F : MvPolynomial (Fin 3) R) : (stepanovDerivation F).totalDegree ≤ F.totalDegree + 2 := by
  have hg :
    (MvPolynomial.X (0 : Fin 3) * (1 - MvPolynomial.X 0) : MvPolynomial (Fin 3) R).totalDegree ≤
      2 := by
    have hs := MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin 3) R) (MvPolynomial.X 0)
    rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X] at hs
    have hm :=
      MvPolynomial.totalDegree_mul (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) R)
        (1 - MvPolynomial.X 0)
    rw [MvPolynomial.totalDegree_X] at hm
    exact hm.trans (by simpa only [max_eq_right (Nat.zero_le 1)] using Nat.add_le_add_left hs 1)
  have hh :
    (MvPolynomial.X (0 : Fin 3) - MvPolynomial.X 2 : MvPolynomial (Fin 3) R).totalDegree ≤ 1 := by
    simpa only [MvPolynomial.totalDegree_X, max_self] using
      MvPolynomial.totalDegree_sub (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) R)
        (MvPolynomial.X 2)
  rw [stepanovDerivation_apply]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · have hm :=
      (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hg (totalDegree_pderiv_le 0 F))
    linarith only [hm]
  · have hm :=
      (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hh (totalDegree_pderiv_le 1 F))
    linarith only [hm]

/-- The r-th jet has total degree at most the input total degree plus 2r. Induct through its
linear recurrence. -/
theorem totalDegree_stepanovJet_le {R : Type*} [CommRing R] [Nontrivial R]
    (F : MvPolynomial (Fin 3) R) (r : ℕ) :
    (stepanovJet r F).totalDegree ≤ F.totalDegree + 2 * r := by
  induction r with
  | zero => exact Nat.le_add_right _ _
  | succ r ih =>
    have hd := totalDegree_stepanovDerivation_le (stepanovJet r F)
    have hs : (1 - MvPolynomial.C (2 : R) * MvPolynomial.X (0 : Fin 3)).totalDegree ≤ 1 := by
      have hm := MvPolynomial.totalDegree_mul (MvPolynomial.C (2 : R)) (MvPolynomial.X (0 : Fin 3))
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, Nat.zero_add] at hm
      exact
        (MvPolynomial.totalDegree_sub _ _).trans
          (max_le
            (by
              rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _)
            hm)
    have hc :=
      MvPolynomial.totalDegree_mul (MvPolynomial.C (r : R))
        (1 - MvPolynomial.C 2 * MvPolynomial.X (0 : Fin 3))
    rw [MvPolynomial.totalDegree_C, Nat.zero_add] at hc
    have hm := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hc.trans hs) ih)
    rw [stepanovJet_apply]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · linarith only [hd, ih]
    · linarith only [hm]

/-- Substituting univariate polynomials of degree at most one bounds output degree by input
total degree. Expand into monomials and bound every product. -/
theorem natDegree_eval₂_linear_le_totalDegree {R σ : Type*} [CommSemiring R] (g : σ → Polynomial R)
    (hg : ∀ i, (g i).natDegree ≤ 1) (F : MvPolynomial σ R) :
    (MvPolynomial.eval₂Hom Polynomial.C g F).natDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum F]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le m.support _).trans
  apply
    (Finset.sum_le_sum
        (fun i _ ↦
          show ((g i) ^ m i).natDegree ≤ m i by
            exact
              Polynomial.natDegree_pow_le.trans
                (by simpa only [mul_one] using Nat.mul_le_mul_left (m i) (hg i)))).trans
  exact MvPolynomial.le_totalDegree hm

/-- The algebra homomorphism substituting X, alpha X+beta, X for the three variables. This
represents the finite-field curves used in the Stepanov constraints. -/
noncomputable def affineSpecialization {R : Type*} [CommSemiring R] (α β : R) :
    MvPolynomial (Fin 3) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C α * Polynomial.X + Polynomial.C β, Polynomial.X]

/-- The affine specialization sends each variable to its specified linear polynomial. Apply the
algebraic evaluation formula. -/
theorem affineSpecialization_X {R : Type*} [CommSemiring R] (α β : R) (i : Fin 3) :
    affineSpecialization α β (MvPolynomial.X i) =
      ![Polynomial.X, Polynomial.C α * Polynomial.X + Polynomial.C β, Polynomial.X] i := by
  exact MvPolynomial.aeval_X _ _

/-- Affine specialization cannot increase total degree into univariate degree. Check the three
linear substitutions and apply the generic degree bound. -/
theorem natDegree_affineSpecialization_le {R : Type*} [CommRing R] [Nontrivial R] (α β : R)
    (F : MvPolynomial (Fin 3) R) : (affineSpecialization α β F).natDegree ≤ F.totalDegree := by
  apply natDegree_eval₂_linear_le_totalDegree
  intro i
  fin_cases i
  · change (Polynomial.X : Polynomial R).natDegree ≤ 1
    exact Polynomial.natDegree_X.le
  · change (Polynomial.C α * Polynomial.X + Polynomial.C β).natDegree ≤ 1
    exact
      (Polynomial.natDegree_add_le _ _).trans
        (max_le ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X.le)
          (by
            rw [Polynomial.natDegree_C]; exact Nat.zero_le _))
  · change (Polynomial.X : Polynomial R).natDegree ≤ 1
    exact Polynomial.natDegree_X.le

/-- The specialized r-th jet has degree at most the input total degree plus 2r. Compose the jet
and linear-substitution bounds. -/
theorem natDegree_affineSpecialization_jet_le {R : Type*} [CommRing R] [Nontrivial R] (α β : R)
    (F : MvPolynomial (Fin 3) R) (r : ℕ) :
    (affineSpecialization α β (stepanovJet r F)).natDegree ≤ F.totalDegree + 2 * r :=
  (natDegree_affineSpecialization_le α β _).trans (totalDegree_stepanovJet_le F r)

/-- For prime p and f(x)=alpha x+beta, actual and affine specialization agree at x. Match the
evaluation homomorphisms on constants and all three variables. -/
theorem stepanovEvaluation_eval_eq_affine {p : ℕ} [Fact p.Prime] (α β x : ZMod p)
    (hx : (truncatedLog p).eval x = α * x + β) (F : MvPolynomial (Fin 3) (ZMod p)) :
    (stepanovEvaluation p F).eval x = (affineSpecialization α β F).eval x := by
  have he :
    (Polynomial.evalRingHom x).comp (stepanovEvaluation p) =
      (Polynomial.evalRingHom x).comp (affineSpecialization α β).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change
        (stepanovEvaluation p (MvPolynomial.C a)).eval x =
          (affineSpecialization α β (MvPolynomial.C a)).eval x
      rw [stepanovEvaluation_C]
      simp only [affineSpecialization, MvPolynomial.aeval_C, Polynomial.algebraMap_apply]
      rfl
    · intro i
      change
        (stepanovEvaluation p (MvPolynomial.X i)).eval x =
          (affineSpecialization α β (MvPolynomial.X i)).eval x
      rw [stepanovEvaluation_X, affineSpecialization_X]
      fin_cases i
      · rfl
      · change (truncatedLog p).eval x = (Polynomial.C α * Polynomial.X + Polynomial.C β).eval x
        simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X] using hx
      · change (Polynomial.X ^ p : Polynomial (ZMod p)).eval x = Polynomial.X.eval x
        rw [Polynomial.eval_pow, Polynomial.eval_X, ZMod.pow_card]
  exact DFunLike.congr_fun he F

/-- For prime p and x different from 0,1 satisfying the affine curve equation, a vanishing
specialized jet forces the corresponding ordinary derivative to vanish at x. Cancel the nonzero
clearing weight. -/
theorem derivative_eval_zero_of_specialized_jet_zero {p : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin 3) (ZMod p)) (r : ℕ) (α β x : ZMod p)
    (hx : (truncatedLog p).eval x = α * x + β) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hjet : affineSpecialization α β (stepanovJet r F) = 0) :
    (Polynomial.derivative^[r] (stepanovEvaluation p F)).eval x = 0 := by
  have he := stepanovEvaluation_eval_eq_affine α β x hx (stepanovJet r F)
  rw [stepanovEvaluation_jet, Polynomial.eval_mul, Polynomial.eval_pow, hjet,
    Polynomial.eval_zero] at he
  have hw : (weight p).eval x ≠ 0 := by
    rw [weight, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
    exact mul_ne_zero hx0 (sub_ne_zero.mpr hx1.symm)
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero r hw)

end PseudoPrime.NumberTheory.Heilbronn
