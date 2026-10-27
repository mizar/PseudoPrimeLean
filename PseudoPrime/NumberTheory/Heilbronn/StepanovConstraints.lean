/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RectangularAuxiliary
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Constructing Stepanov multiplicities by linear constraints -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The linear map recording the first N coefficients of each affine-specialized jet for s
curves and D derivative orders. Its kernel supplies the auxiliary coefficients. -/
noncomputable def stepanovConstraints {p s : ℕ} [Fact p.Prime] (A B C D N : ℕ)
    (α β : Fin s → ZMod p) :
    (Fin C → Fin A → Fin B → ZMod p) →ₗ[ZMod p] (Fin s → Fin D → Fin N → ZMod p) :=
  LinearMap.pi
    (fun i ↦
      LinearMap.pi
        (fun r ↦
          (Polynomial.toFn N).comp
            ((affineSpecialization (α i) (β i)).toLinearMap.comp
              ((stepanovJet (r : ℕ)).comp (rectangularPolynomial A B C)))))

/-- A constraint coordinate is the indicated coefficient of the specialized jet. Unfold the
projection maps and coefficient vector. -/
theorem stepanovConstraints_apply {p s : ℕ} [Fact p.Prime] (A B C D N : ℕ) (α β : Fin s → ZMod p)
    (v : Fin C → Fin A → Fin B → ZMod p) (i : Fin s) (r : Fin D) (j : Fin N) :
    stepanovConstraints A B C D N α β v i r j =
      (affineSpecialization (α i) (β i) (stepanovJet (r : ℕ) (rectangularPolynomial A B C v))).coeff
        j :=
  rfl

/-- For prime p, sDN<CAB forces a nonzero rectangular coefficient vector in the constraint
kernel. Compare finite-dimensional ranks and use rank-nullity. -/
theorem exists_rectangular_coefficients_constraints_zero {p s : ℕ} [Fact p.Prime] (A B C D N : ℕ)
    (α β : Fin s → ZMod p) (hcount : s * D * N < C * A * B) :
    ∃ v : Fin C → Fin A → Fin B → ZMod p, v ≠ 0 ∧ stepanovConstraints A B C D N α β v = 0 := by
  have hdim :
    Module.finrank (ZMod p) (Fin s → Fin D → Fin N → ZMod p) <
      Module.finrank (ZMod p) (Fin C → Fin A → Fin B → ZMod p) := by
    simpa only [Module.finrank_pi_fintype, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Nat.mul_assoc] using hcount
  obtain ⟨v, hv, hn⟩ :=
    (Submodule.ne_bot_iff _).mp
      (LinearMap.ker_ne_bot_of_finrank_lt (f := stepanovConstraints A B C D N α β) hdim)
  exact ⟨v, hn, LinearMap.mem_ker.mp hv⟩

/-- For prime p, if sD(A+B+C+2D)<CAB, a nonzero coefficient array makes every specialized jet
through order D-1 vanish as a polynomial. The degree bound turns zero coefficient constraints
into zero polynomials. -/
theorem exists_nonzero_rectangular_jets_vanish {p s : ℕ} [Fact p.Prime] (A B C D : ℕ)
    (α β : Fin s → ZMod p) (hcount : s * D * (A + B + C + 2 * D) < C * A * B) :
    ∃ v : Fin C → Fin A → Fin B → ZMod p,
      v ≠ 0 ∧
        ∀ (i : Fin s) (r : Fin D),
          affineSpecialization (α i) (β i) (stepanovJet (r : ℕ) (rectangularPolynomial A B C v)) =
            0 := by
  obtain ⟨v, hv, hk⟩ :=
    exists_rectangular_coefficients_constraints_zero A B C D (A + B + C + 2 * D) α β hcount
  refine ⟨v, hv, ?_⟩
  intro i r
  have hd :=
    (natDegree_affineSpecialization_jet_le (α i) (β i) (rectangularPolynomial A B C v)
          (r : ℕ)).trans
      (Nat.add_le_add_right (totalDegree_rectangularPolynomial_le A B C v) (2 * (r : ℕ)))
  have hlt :
    (affineSpecialization (α i) (β i)
          (stepanovJet (r : ℕ) (rectangularPolynomial A B C v))).natDegree <
      A + B + C + 2 * D := by
    linarith only [hd, r.isLt]
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_zero]
  by_cases hj : j < A + B + C + 2 * D
  · have he := congrFun (congrFun (congrFun hk i) r) ⟨j, hj⟩
    simpa only [stepanovConstraints_apply, Pi.zero_apply] using he
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hlt.trans_le (Nat.le_of_not_gt hj))

/-- For a nonzero polynomial over ZMod p and 0<D<=p, vanishing ordinary derivatives through
order D-1 imply multiplicity at least D. Use the root-multiplicity criterion and invert nonzero
integers below p. -/
theorem X_sub_C_pow_dvd_of_derivatives_zero {p : ℕ} [Fact p.Prime] (P : Polynomial (ZMod p))
    (hP : P ≠ 0) (x : ZMod p) {D : ℕ} (hD : 0 < D) (hDp : D ≤ p)
    (hzero : ∀ r : ℕ, r < D → (Polynomial.derivative^[r] P).eval x = 0) :
    (Polynomial.X - Polynomial.C x) ^ D ∣ P := by
  have hpred : D - 1 < D := Nat.sub_lt hD (by decide : 0 < 1)
  have hm :=
    Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hP
      (fun r hr ↦ hzero r (hr.trans_lt hpred))
      (fun r hr hr0 ↦
        show (r : ZMod p) ∈ nonZeroDivisors (ZMod p)
          by
          apply mem_nonZeroDivisors_iff_ne_zero.mpr
          intro hz
          have hdvd := (ZMod.natCast_eq_zero_iff r p).mp hz
          exact
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hdvd).not_gt ((hr.trans_lt hpred).trans_le hDp))
  have hmult : D ≤ P.rootMultiplicity x := by
    have hc := Nat.sub_add_cancel (Nat.succ_le_of_lt hD)
    linarith only [hm, hc]
  exact (pow_dvd_pow (Polynomial.X - Polynomial.C x) hmult).trans (P.pow_rootMultiplicity_dvd x)

/-- For prime p, AB<=p and the strict constraint count, construct a nonzero auxiliary polynomial
having multiplicity D at every nonexceptional point on the specified affine truncated-log
curves. The multiplicities are proved, not assumed. -/
theorem exists_rectangular_auxiliary_multiplicities {p s : ℕ} [Fact p.Prime] (A B C D : ℕ)
    (α β : Fin s → ZMod p) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hDp : D ≤ p) (hAB : A * B ≤ p)
    (hcount : s * D * (A + B + C + 2 * D) < C * A * B) :
    ∃ v : Fin C → Fin A → Fin B → ZMod p,
      v ≠ 0 ∧
        stepanovEvaluation p (rectangularPolynomial A B C v) ≠ 0 ∧
        ∀ x : ZMod p,
          x ≠ 0 →
            x ≠ 1 →
            (∃ i : Fin s, (truncatedLog p).eval x = α i * x + β i) →
            (Polynomial.X - Polynomial.C x) ^ D ∣
              stepanovEvaluation p (rectangularPolynomial A B C v) := by
  obtain ⟨v, hv, hjet⟩ := exists_nonzero_rectangular_jets_vanish A B C D α β hcount
  have hn := stepanovEvaluation_rectangular_ne_zero v hv hA hB hAB
  refine ⟨v, hv, hn, ?_⟩
  intro x hx0 hx1 hx
  obtain ⟨i, hi⟩ := hx
  apply X_sub_C_pow_dvd_of_derivatives_zero _ hn x hD hDp
  intro r hr
  exact derivative_eval_zero_of_specialized_jet_zero _ r (α i) (β i) x hi hx0 hx1 (hjet i ⟨r, hr⟩)

/-- Under positive rectangular parameters, AB<=p, D<=p and the strict constraint count, any
finite set of nonexceptional curve solutions has card(S)D at most A-1+(B-1)(p-1)+p(C-1).
Construct the auxiliary polynomial and apply the proved multiplicity root bound. -/
theorem card_affine_truncatedLog_solutions_mul_le {p s : ℕ} [Fact p.Prime] (A B C D : ℕ)
    (α β : Fin s → ZMod p) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hDp : D ≤ p)
    (hAB : A * B ≤ p) (hcount : s * D * (A + B + C + 2 * D) < C * A * B) (S : Finset (ZMod p))
    (hS : ∀ x ∈ S, x ≠ 0 ∧ x ≠ 1 ∧ ∃ i : Fin s, (truncatedLog p).eval x = α i * x + β i) :
    S.card * D ≤ (A - 1) + (B - 1) * (p - 1) + p * (C - 1) := by
  obtain ⟨v, hv, _, hm⟩ :=
    exists_rectangular_auxiliary_multiplicities A B C D α β hA hB hD hDp hAB hcount
  classical
  have hd := rectangularNested_degree_bounds A B C v hA hB hC
  apply
    card_mul_le_of_frobenius_logarithmic_roots _ hB hAB (rectangularNested_ne_zero A B C v hv) hd.1
      hd.2.1 hd.2.2 S D
  intro x hx
  rw [← stepanovEvaluation_rectangular_eq]
  exact hm x (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2

/-- For prime p, positive s,t and 64s^2 t^3<=p, nonexceptional solutions of s affine
truncated-log equations satisfy card(S)t<=32t+4p. Choose A=32st^2, B=C=2st, D=st^2
in the constructed Stepanov bound and prove all size and constraint conditions. -/
theorem card_affine_truncatedLog_solutions_scaled {p s t : ℕ} [Fact p.Prime] (α β : Fin s → ZMod p)
    (hs : 0 < s) (ht : 0 < t) (hsize : 64 * s ^ 2 * t ^ 3 ≤ p) (S : Finset (ZMod p))
    (hS : ∀ x ∈ S, x ≠ 0 ∧ x ≠ 1 ∧ ∃ i : Fin s, (truncatedLog p).eval x = α i * x + β i) :
    S.card * t ≤ 32 * t + 4 * p := by
  have hA : 0 < 32 * s * t ^ 2 := mul_pos (mul_pos (by decide : 0 < 32) hs) (pow_pos ht 2)
  have hB : 0 < 2 * s * t := mul_pos (mul_pos (by decide : 0 < 2) hs) ht
  have hD : 0 < s * t ^ 2 := mul_pos hs (pow_pos ht 2)
  have hAB : (32 * s * t ^ 2) * (2 * s * t) ≤ p := by
    have he : (32 * s * t ^ 2) * (2 * s * t) = 64 * s ^ 2 * t ^ 3 := by ring
    exact he ▸ hsize
  have hDp : s * t ^ 2 ≤ p := by
    have h := Nat.le_mul_of_pos_right (s * t ^ 2) (mul_pos (mul_pos (by decide : 0 < 64) hs) ht)
    have he : (s * t ^ 2) * (64 * s * t) = 64 * s ^ 2 * t ^ 3 := by ring
    rw [he] at h
    exact h.trans hsize
  have hcount :
    s * (s * t ^ 2) * (32 * s * t ^ 2 + 2 * s * t + 2 * s * t + 2 * (s * t ^ 2)) <
      (2 * s * t) * (32 * s * t ^ 2) * (2 * s * t) := by
    have ht1 := Nat.succ_le_of_lt ht
    have hn : 34 * t + 4 < 128 * t := by linarith only [ht1]
    have hm := mul_lt_mul_of_pos_right hn (mul_pos (pow_pos hs 3) (pow_pos ht 3))
    convert hm using 1 <;> ring
  have hb :=
    card_affine_truncatedLog_solutions_mul_le (32 * s * t ^ 2) (2 * s * t) (2 * s * t) (s * t ^ 2) α
      β hA hB hB hD hDp hAB hcount S hS
  have hcoarse :
    (32 * s * t ^ 2 - 1) + (2 * s * t - 1) * (p - 1) + p * (2 * s * t - 1) ≤
      32 * s * t ^ 2 + (2 * s * t) * p + p * (2 * s * t) :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)))
      (Nat.mul_le_mul_left p (Nat.sub_le _ _))
  have hc : (S.card * t) * (s * t) ≤ (32 * t + 4 * p) * (s * t) := by
    have h := hb.trans hcoarse
    convert h using 1 <;> ring
  exact Nat.le_of_mul_le_mul_right hc (mul_pos hs ht)

end PseudoPrime.NumberTheory.Heilbronn
