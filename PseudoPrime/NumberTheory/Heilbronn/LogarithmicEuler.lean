/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TruncatedLogDerivative
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Tactic.Abel

/-! # Euler elimination for truncated logarithmic blocks -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The linear coefficient operator F maps to F'+cF. At nonzero c its powers preserve nonzero
polynomials; at zero c they are ordinary iterated derivatives. -/
noncomputable def affineDerivative {R : Type*} [CommRing R] (c : R) :
    Polynomial R →ₗ[R] Polynomial R :=
  Polynomial.derivative + LinearMap.mulLeft R (Polynomial.C c)

/-- The linear Euler operator F maps to (1-X)F'+cF. It eliminates coefficient blocks in the
shifted basis (1-X)^a F_a(f(X)). -/
noncomputable def affineEuler {R : Type*} [CommRing R] (c : R) : Polynomial R →ₗ[R] Polynomial R :=
  (LinearMap.mulLeft R (1 - Polynomial.X)).comp Polynomial.derivative +
    LinearMap.mulLeft R (Polynomial.C c)

/-- The coefficient endomorphism acts by F'+cF. Unfold its linear-map definition. -/
theorem affineDerivative_apply {R : Type*} [CommRing R] (c : R) (F : Polynomial R) :
    affineDerivative c F = Polynomial.derivative F + Polynomial.C c * F :=
  rfl

/-- The Euler endomorphism acts by (1-X)F'+cF. This is its explicit action on polynomials. -/
theorem affineEuler_apply {R : Type*} [CommRing R] (c : R) (F : Polynomial R) :
    affineEuler c F = (1 - Polynomial.X) * Polynomial.derivative F + Polynomial.C c * F :=
  rfl

/-- Over a field with c nonzero, F'+cF=0 if and only if F=0. The derivative of a nonzero
polynomial has smaller degree than cF. -/
theorem affineDerivative_eq_zero_iff {K : Type*} [Field K] {c : K} (hc : c ≠ 0) (F : Polynomial K) :
    affineDerivative c F = 0 ↔ F = 0 := by
  constructor
  · intro h
    by_contra hF
    have he : Polynomial.derivative F = -Polynomial.C c * F := by
      rw [affineDerivative_apply] at h
      linear_combination h
    have hd := Polynomial.degree_derivative_lt hF
    rw [he, ← Polynomial.C_neg, Polynomial.degree_C_mul (neg_ne_zero.mpr hc)] at hd
    exact lt_irrefl _ hd
  · rintro rfl
    exact map_zero _

/-- The coefficient operator does not increase natural degree. Use the derivative and
constant-multiplication bounds. -/
theorem natDegree_affineDerivative_le {R : Type*} [CommRing R] (c : R) (F : Polynomial R) :
    (affineDerivative c F).natDegree ≤ F.natDegree := by
  rw [affineDerivative_apply]
  have hd := (Polynomial.natDegree_derivative_le F).trans (Nat.sub_le _ _)
  simpa only [max_self] using
    Polynomial.natDegree_add_le_of_le hd (Polynomial.natDegree_C_mul_le c F)

/-- For prime p the truncated logarithm satisfies (1-X)f'=1-X^(p-1). This exact identity retains
the error in the Euler comparison. -/
theorem one_sub_X_mul_derivative_truncatedLog {p : ℕ} [Fact p.Prime] :
    (1 - Polynomial.X) * Polynomial.derivative (truncatedLog p) =
      1 - (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) := by
  rw [derivative_truncatedLog]
  have he := geom_sum_mul (Polynomial.X : Polynomial (ZMod p)) (p - 1)
  linear_combination -he

/-- For every exponent a, (1-X)((1-X)^a)'=-a(1-X)^a. The zero exponent is handled separately. -/
theorem one_sub_X_mul_derivative_pow {R : Type*} [CommRing R] (a : ℕ) :
    (1 - Polynomial.X) * Polynomial.derivative ((1 - Polynomial.X : Polynomial R) ^ a) =
      -Polynomial.C (a : R) * (1 - Polynomial.X) ^ a := by
  cases a with
  | zero =>
    simp only [pow_zero, Polynomial.derivative_one, mul_zero, Nat.cast_zero, Polynomial.C_0,
      neg_zero, zero_mul]
  | succ
    a =>
    rw [Polynomial.derivative_pow, Nat.succ_sub_one, Polynomial.derivative_sub,
      Polynomial.derivative_one, Polynomial.derivative_X, zero_sub, pow_succ]
    ring

/-- The block (1-X)^a F(f(X)), where f is the truncated logarithm over ZMod p. Finite sums of
blocks express the shifted bivariate substitution. -/
noncomputable def logarithmicBlock {p : ℕ} (a : ℕ) (F : Polynomial (ZMod p)) :
    Polynomial (ZMod p) :=
  (1 - Polynomial.X) ^ a * F.comp (truncatedLog p)

/-- For prime p the Euler image of a block equals the coefficient shift F'+(c-a)F plus an
explicit multiple of X^(p-1). Use the truncated-log differential identity. -/
theorem affineEuler_logarithmicBlock {p : ℕ} [Fact p.Prime] (a : ℕ) (c : ZMod p)
    (F : Polynomial (ZMod p)) :
    affineEuler c (logarithmicBlock a F) =
      logarithmicBlock a (affineDerivative (c - a) F) -
        Polynomial.X ^ (p - 1) * (1 - Polynomial.X) ^ a *
          (Polynomial.derivative F).comp (truncatedLog p) := by
  have ha := one_sub_X_mul_derivative_pow (R := ZMod p) a
  have hf := one_sub_X_mul_derivative_truncatedLog (p := p)
  dsimp only [logarithmicBlock]
  rw [affineEuler_apply, affineDerivative_apply, Polynomial.derivative_mul,
    Polynomial.derivative_comp, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.C_sub]
  linear_combination
    F.comp (truncatedLog p) * ha +
      (1 - Polynomial.X) ^ a * (Polynomial.derivative F).comp (truncatedLog p) * hf

/-- Over a field with c nonzero, every power of the coefficient operator preserves nonzero
polynomials. Induct using the one-step kernel characterization. -/
theorem affineDerivative_pow_eq_zero_iff {K : Type*} [Field K] {c : K} (hc : c ≠ 0) (k : ℕ)
    (F : Polynomial K) : (affineDerivative c ^ k) F = 0 ↔ F = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, affineDerivative_eq_zero_iff hc, ih]

/-- Every power of the coefficient operator preserves the natural degree bound. Apply the
one-step estimate repeatedly. -/
theorem natDegree_affineDerivative_pow_le {R : Type*} [CommRing R] (c : R) (k : ℕ)
    (F : Polynomial R) : ((affineDerivative c ^ k) F).natDegree ≤ F.natDegree := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (natDegree_affineDerivative_le c _).trans ih

/-- At c=0, powers of the coefficient operator are the ordinary iterated derivatives. These kill
coefficients of degree below the number of steps. -/
theorem affineDerivative_zero_pow {R : Type*} [CommRing R] (k : ℕ) (F : Polynomial R) :
    (affineDerivative (0 : R) ^ k) F = Polynomial.derivative^[k] F := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, affineDerivative_apply, Polynomial.C_0, zero_mul, add_zero,
      ih, Function.iterate_succ_apply']

/-- If X^(m+1) divides F, then X^m divides its Euler image. Differentiation loses at most one
power and multiplication does not increase the loss. -/
theorem X_pow_dvd_affineEuler {R : Type*} [CommRing R] (c : R) {F : Polynomial R} {m : ℕ}
    (h : Polynomial.X ^ (m + 1) ∣ F) : Polynomial.X ^ m ∣ affineEuler c F := by
  have hd := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
  rw [Nat.add_sub_cancel_right] at hd
  rw [affineEuler_apply]
  exact
    dvd_add (dvd_mul_of_dvd_right hd _)
      (dvd_mul_of_dvd_right ((pow_dvd_pow Polynomial.X (Nat.le_succ m)).trans h) _)

/-- If X^(m+k) divides F, k Euler steps retain divisibility by X^m. Induct with a varying target
multiplicity. -/
theorem X_pow_dvd_affineEuler_pow {R : Type*} [CommRing R] (c : R) {F : Polynomial R} (m k : ℕ)
    (h : Polynomial.X ^ (m + k) ∣ F) : Polynomial.X ^ m ∣ (affineEuler c ^ k) F := by
  induction k generalizing m with
  | zero => exact h
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    apply X_pow_dvd_affineEuler c
    exact ih (m + 1) (by simpa only [Nat.add_assoc, Nat.add_comm k 1] using h)

/-- The discrepancy between the Euler image and the shifted block is divisible by X^(p-1). Use
the exact block identity. -/
theorem X_pow_dvd_affineEuler_block_error {p : ℕ} [Fact p.Prime] (a : ℕ) (c : ZMod p)
    (F : Polynomial (ZMod p)) :
    (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) ∣
      affineEuler c (logarithmicBlock a F) - logarithmicBlock a (affineDerivative (c - a) F) := by
  rw [affineEuler_logarithmicBlock]
  have he :
    logarithmicBlock a (affineDerivative (c - a) F) -
        Polynomial.X ^ (p - 1) * (1 - Polynomial.X) ^ a *
          (Polynomial.derivative F).comp (truncatedLog p) -
        logarithmicBlock a (affineDerivative (c - a) F) =
      Polynomial.X ^ (p - 1) *
        (-((1 - Polynomial.X) ^ a * (Polynomial.derivative F).comp (truncatedLog p))) := by
    ring
  rw [he]
  exact dvd_mul_right _ _

/-- For prime p and m+k<=p, k Euler steps agree modulo X^m with k coefficient shifts. Retain and
differentiate the error at each step. -/
theorem X_pow_dvd_affineEuler_pow_block_error {p : ℕ} [Fact p.Prime] (a : ℕ) (c : ZMod p)
    (F : Polynomial (ZMod p)) (m k : ℕ) (hbudget : m + k ≤ p) :
    (Polynomial.X : Polynomial (ZMod p)) ^ m ∣
      (affineEuler c ^ k) (logarithmicBlock a F) -
        logarithmicBlock a ((affineDerivative (c - a) ^ k) F) := by
  induction k generalizing m with
  | zero =>
    change Polynomial.X ^ m ∣ logarithmicBlock a F - logarithmicBlock a F
    rw [sub_self]
    exact dvd_zero _
  | succ k ih =>
    have hi := ih (m + 1) (by linarith only [hbudget])
    have h1 := X_pow_dvd_affineEuler c hi
    have h2 := X_pow_dvd_affineEuler_block_error a c ((affineDerivative (c - a) ^ k) F)
    have hmp : m ≤ p - 1 := Nat.le_sub_of_add_le (by linarith only [hbudget])
    have h2' := (pow_dvd_pow (Polynomial.X : Polynomial (ZMod p)) hmp).trans h2
    have hd := dvd_add h1 h2'
    rw [map_sub] at hd
    have he :
      affineEuler c ((affineEuler c ^ k) (logarithmicBlock a F)) -
            affineEuler c (logarithmicBlock a ((affineDerivative (c - a) ^ k) F)) +
          (affineEuler c (logarithmicBlock a ((affineDerivative (c - a) ^ k) F)) -
            logarithmicBlock a (affineDerivative (c - a) ((affineDerivative (c - a) ^ k) F))) =
        (affineEuler c ^ (k + 1)) (logarithmicBlock a F) -
          logarithmicBlock a ((affineDerivative (c - a) ^ (k + 1)) F) := by
      rw [pow_succ' (affineEuler c), pow_succ' (affineDerivative (c - a))]
      simp only [Module.End.mul_apply]
      abel
    exact he ▸ hd

/-- For prime p and m+k<=p, divisibility of a block sum by X^(m+k) gives divisibility of the
coefficient-shifted sum by X^m. Sum the errors and subtract. -/
theorem X_pow_dvd_logarithmicSum_shift {p : ℕ} [Fact p.Prime] (S : Finset ℕ)
    (F : ℕ → Polynomial (ZMod p)) (c : ZMod p) (m k : ℕ) (hbudget : m + k ≤ p)
    (h : Polynomial.X ^ (m + k) ∣ ∑ a ∈ S, logarithmicBlock a (F a)) :
    Polynomial.X ^ m ∣ ∑ a ∈ S, logarithmicBlock a ((affineDerivative (c - a) ^ k) (F a)) := by
  have hop := X_pow_dvd_affineEuler_pow c m k h
  have herr :
    Polynomial.X ^ m ∣
      (affineEuler c ^ k) (∑ a ∈ S, logarithmicBlock a (F a)) -
        ∑ a ∈ S, logarithmicBlock a ((affineDerivative (c - a) ^ k) (F a)) := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum (fun a _ ↦ X_pow_dvd_affineEuler_pow_block_error a c (F a) m k hbudget)
  have hd := dvd_sub hop herr
  simpa only [sub_sub_cancel] using hd

/-- For prime p, a coefficient of degree below B is removed by B Euler steps at its eigenvalue.
If m+B<=p, the transformed sum with this index erased is divisible by X^m. -/
theorem X_pow_dvd_logarithmicSum_erase {p : ℕ} [Fact p.Prime] (S : Finset ℕ)
    (F : ℕ → Polynomial (ZMod p)) (a m B : ℕ) (ha : a ∈ S) (hbudget : m + B ≤ p)
    (hF : (F a).natDegree < B) (h : Polynomial.X ^ (m + B) ∣ ∑ b ∈ S, logarithmicBlock b (F b)) :
    Polynomial.X ^ m ∣
      ∑ b ∈ S.erase a, logarithmicBlock b ((affineDerivative ((a : ZMod p) - b) ^ B) (F b)) := by
  have hd := X_pow_dvd_logarithmicSum_shift S F (a : ZMod p) m B hbudget h
  have hz : (affineDerivative ((a : ZMod p) - a) ^ B) (F a) = 0 := by
    rw [sub_self, affineDerivative_zero_pow]
    exact Polynomial.iterate_derivative_eq_zero hF
  rw [← Finset.sum_erase_add _ _ ha, hz] at hd
  simpa only [logarithmicBlock, Polynomial.zero_comp, mul_zero, add_zero] using hd

end PseudoPrime.NumberTheory.Heilbronn
