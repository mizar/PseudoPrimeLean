/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Truncated logarithm derivative reduction for the Heilbronn method -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The truncated logarithm over ZMod p: sum of X^(j+1)/(j+1) for j<p-1.
For prime p all denominators are units. It is the polynomial in the Heilbronn
Stepanov method, not a real or formal logarithm. -/
noncomputable def truncatedLog (p : ℕ) : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.range (p - 1), Polynomial.C ((j + 1 : ℕ) : ZMod p)⁻¹ * Polynomial.X ^ (j + 1)

/-- The polynomial X(1-X) over ZMod p. Its powers clear denominators in
iterated derivatives of the truncated logarithm. -/
noncomputable def weight (p : ℕ) : Polynomial (ZMod p) :=
  Polynomial.X * (1 - Polynomial.X)

/-- For prime p, differentiating the truncated logarithm gives the geometric
sum through exponent p-2. Cancel the nonzero denominator of each coefficient. -/
theorem derivative_truncatedLog {p : ℕ} [Fact p.Prime] :
    Polynomial.derivative (truncatedLog p) =
      ∑ j ∈ Finset.range (p - 1), (Polynomial.X : Polynomial (ZMod p)) ^ j := by
  rw [truncatedLog, Polynomial.derivative_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j + 1 < p := by
    have h := Finset.mem_range.mp hj
    have hp := Fact.out (p := p.Prime)
    exact (Nat.add_lt_add_right h 1).trans_le (Nat.sub_add_cancel hp.one_lt.le).le
  have hj0 : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff (j + 1) p).mp hz
    exact (Nat.le_of_dvd (Nat.succ_pos j) hd).not_gt hjp
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_X_pow, Nat.add_sub_cancel_right, ← mul_assoc, ← Polynomial.C_mul,
    inv_mul_cancel₀ hj0, Polynomial.C_1, one_mul]

/-- For prime p, X(1-X) times the first derivative equals X-X^p.
Multiply the derivative geometric series; this starts the reduction recurrence. -/
theorem weight_mul_derivative_truncatedLog {p : ℕ} [Fact p.Prime] :
    weight p * Polynomial.derivative (truncatedLog p) =
      Polynomial.X - (Polynomial.X : Polynomial (ZMod p)) ^ p := by
  rw [derivative_truncatedLog]
  have hg := geom_sum_mul (Polynomial.X : Polynomial (ZMod p)) (p - 1)
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.Prime.one_lt Fact.out).le
  have he : (Polynomial.X : Polynomial (ZMod p)) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
    exact
      (congrArg (fun k : ℕ ↦ (Polynomial.X : Polynomial (ZMod p)) ^ k) hp).symm.trans
        (pow_succ Polynomial.X (p - 1))
  dsimp only [weight]
  rw [he]
  linear_combination -Polynomial.X * hg

/-- For index k, the pair (Q,H) reducing the (k+1)-st weighted derivative.
Start with (0,-1); differentiate the identity and subtract the derivative of the
weight power. The recurrence gives Q degree at most k+2 and H degree at most k
for prime p, and supplies exact identities used in the Stepanov reduction. -/
noncomputable def reductionPair (p : ℕ) : ℕ → Polynomial (ZMod p) × Polynomial (ZMod p)
  | 0 => (0, -1)
  | k + 1 =>
    let Q := (reductionPair p k).1
    let H := (reductionPair p k).2
    (weight p * Polynomial.derivative Q -
        Polynomial.C ((k + 1 : ℕ) : ZMod p) * Polynomial.derivative (weight p) * Q -
        weight p * H,
      weight p * Polynomial.derivative H -
        Polynomial.C ((k + 1 : ℕ) : ZMod p) * Polynomial.derivative (weight p) * H)

/-- In characteristic p, the derivative of X^p-X is -1.
This identity makes the error term stable under repeated weighted differentiation. -/
theorem derivative_frobenius_error {p : ℕ} :
    Polynomial.derivative ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) = -1 := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, ZMod.natCast_self, Polynomial.C_0,
    zero_mul, Polynomial.derivative_X, zero_sub]

/-- For any commutative ring and polynomials g,F, differentiate g^(k+1)F
and cancel the derivative of the weight. The remainder is g^(k+2)F'.
This algebraic identity drives every order of the reduction. -/
theorem weighted_derivative_step {R : Type*} [CommRing R] (g F : Polynomial R) (k : ℕ) :
    g * Polynomial.derivative (g ^ (k + 1) * F) -
        Polynomial.C ((k + 1 : ℕ) : R) * Polynomial.derivative g * (g ^ (k + 1) * F) =
      g ^ (k + 2) * Polynomial.derivative F := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Nat.add_sub_cancel_right,
    show k + 2 = (k + 1) + 1 by rfl, pow_succ, pow_succ]
  ring

/-- For prime p and k≥0, the (k+1)-st derivative times weight^(k+1)
equals Q_k+(X^p-X)H_k. Induct with the explicit polynomial pair recurrence.
This is the exact, unreduced identity underlying the finite-field evaluations. -/
theorem weighted_iterated_derivative_eq {p : ℕ} [Fact p.Prime] (k : ℕ) :
    weight p ^ (k + 1) * Polynomial.derivative^[k + 1] (truncatedLog p) =
      (reductionPair p k).1 +
        ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) * (reductionPair p k).2 := by
  induction k with
  | zero =>
    simp only [pow_one, Function.iterate_one, reductionPair, zero_add, mul_neg, mul_one]
    rw [weight_mul_derivative_truncatedLog]
    ring
  | succ k
    ih =>
    have hs :=
      weighted_derivative_step (weight p) (Polynomial.derivative^[k + 1] (truncatedLog p)) k
    rw [ih] at hs
    rw [← Function.iterate_succ_apply' Polynomial.derivative (k + 1) (truncatedLog p)] at hs
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul, derivative_frobenius_error,
      neg_one_mul] at hs
    dsimp only [reductionPair]
    rw [← hs]
    ring

/-- For prime p the clearing polynomial X(1-X) has natural degree at most two.
Use the degree bounds for a product and a difference. -/
theorem natDegree_weight_le (p : ℕ) [Fact p.Prime] : (weight p).natDegree ≤ 2 := by
  have hsub := Polynomial.natDegree_sub_le (1 : Polynomial (ZMod p)) Polynomial.X
  rw [Polynomial.natDegree_one, Polynomial.natDegree_X] at hsub
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (Polynomial.natDegree_X.le) hsub)

/-- For prime p the derivative of the clearing polynomial has degree at most one.
Apply the derivative degree bound to the quadratic weight. -/
theorem natDegree_derivative_weight_le (p : ℕ) [Fact p.Prime] :
    (Polynomial.derivative (weight p)).natDegree ≤ 1 := by
  exact
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right (natDegree_weight_le p) 1)

/-- For prime p, the reduction pair at index k has degrees at most k+2 and k.
Induct through the recurrence; separate the constant initial error for its derivative.
These are the degree bounds in the truncated-log derivative reduction. -/
theorem reductionPair_degrees (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (reductionPair p k).1.natDegree ≤ k + 2 ∧ (reductionPair p k).2.natDegree ≤ k := by
  induction k with
  | zero =>
    simp only [reductionPair, Polynomial.natDegree_zero, Polynomial.natDegree_neg,
      Polynomial.natDegree_one]
    exact ⟨by decide, le_rfl⟩
  | succ k
    ih =>
    have hqD := (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right ih.1 1)
    have hq1 : (weight p * Polynomial.derivative (reductionPair p k).1).natDegree ≤ k + 3 := by
      have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (natDegree_weight_le p) hqD)
      rw [Nat.add_sub_assoc (by decide : 1 ≤ 2)] at h
      linarith only [h]
    have hq2 :
      (Polynomial.C ((k + 1 : ℕ) : ZMod p) * Polynomial.derivative (weight p) *
            (reductionPair p k).1).natDegree ≤
        k + 3 := by
      have hc :=
        Polynomial.natDegree_C_mul_le ((k + 1 : ℕ) : ZMod p) (Polynomial.derivative (weight p))
      have h :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (hc.trans (natDegree_derivative_weight_le p)) ih.1)
      linarith only [h]
    have hq3 : (weight p * (reductionPair p k).2).natDegree ≤ k + 3 := by
      have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (natDegree_weight_le p) ih.2)
      linarith only [h]
    have hq := Polynomial.natDegree_sub_le_of_le (Polynomial.natDegree_sub_le_of_le hq1 hq2) hq3
    have hh1 : (weight p * Polynomial.derivative (reductionPair p k).2).natDegree ≤ k + 1 := by
      by_cases hk : k = 0
      · subst k
        simp only [reductionPair, Polynomial.derivative_neg, Polynomial.derivative_one, neg_zero,
          mul_zero, Polynomial.natDegree_zero]
        exact Nat.zero_le _
      · have hd := (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right ih.2 1)
        have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (natDegree_weight_le p) hd)
        have hk1 := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
        linarith only [h, hk1]
    have hh2 :
      (Polynomial.C ((k + 1 : ℕ) : ZMod p) * Polynomial.derivative (weight p) *
            (reductionPair p k).2).natDegree ≤
        k + 1 := by
      have hc :=
        Polynomial.natDegree_C_mul_le ((k + 1 : ℕ) : ZMod p) (Polynomial.derivative (weight p))
      have h :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (hc.trans (natDegree_derivative_weight_le p)) ih.2)
      linarith only [h]
    have hh := Polynomial.natDegree_sub_le_of_le hh1 hh2
    simp only [max_self] at hq hh
    exact ⟨hq, hh⟩

/-- For prime p and r≥1, there exist Q,H of natural degrees at most r+1,r-1
with weight^r times the r-th derivative equal to Q+(X^p-X)H.
Use index r-1 in the proved recurrence. This is the content of Lemma 16 in
Shkredov-Solodkova-Vyugin (arXiv:1302.3839v3), including the prime two. -/
theorem exists_low_degree_reduction {p : ℕ} [Fact p.Prime] {r : ℕ} (hr : 1 ≤ r) :
    ∃ Q H : Polynomial (ZMod p),
      Q.natDegree ≤ r + 1 ∧
        H.natDegree ≤ r - 1 ∧
        weight p ^ r * Polynomial.derivative^[r] (truncatedLog p) =
          Q + ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) * H := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  refine ⟨(reductionPair p k).1, (reductionPair p k).2, ?_, ?_, ?_⟩
  · simpa only [Nat.add_comm 1 k, Nat.add_assoc] using (reductionPair_degrees p k).1
  · simpa only [Nat.add_comm 1 k, Nat.add_sub_cancel] using (reductionPair_degrees p k).2
  · simpa only [Nat.add_comm 1 k] using weighted_iterated_derivative_eq k

/-- At every point of the prime field, the Frobenius error vanishes.
Thus the weighted derivative evaluates to the low-degree numerator Q_k.
This connects the exact reduction to the finite-field constraints in Stepanov's method. -/
theorem weighted_derivative_eval_eq {p : ℕ} [Fact p.Prime] (k : ℕ) (x : ZMod p) :
    (x * (1 - x)) ^ (k + 1) * (Polynomial.derivative^[k + 1] (truncatedLog p)).eval x =
      (reductionPair p k).1.eval x := by
  have he := congrArg (Polynomial.eval x) (weighted_iterated_derivative_eq (p := p) k)
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, weight, ZMod.pow_card, sub_self, zero_mul,
    add_zero] using he

/-- Away from 0 and 1 in the prime field, divide the weighted evaluation by
its nonzero clearing factor. The derivative is the low-degree numerator over
(x(1-x))^(k+1); no choice of a representative integer is needed. -/
theorem iterated_derivative_eval_eq_div {p : ℕ} [Fact p.Prime] (k : ℕ) (x : ZMod p) (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) :
    (Polynomial.derivative^[k + 1] (truncatedLog p)).eval x =
      (reductionPair p k).1.eval x / (x * (1 - x)) ^ (k + 1) := by
  apply (eq_div_iff (pow_ne_zero _ (mul_ne_zero hx0 (sub_ne_zero.mpr hx1.symm)))).mpr
  simpa only [mul_comm] using weighted_derivative_eval_eq k x

/-- For prime p, if Q_k is nonzero, any finite set of zeros of the (k+1)-st
derivative has cardinality at most k+2. Transfer to Q_k using the weighted evaluation
and apply the polynomial root bound. Nonvanishing is an explicit necessary condition. -/
theorem card_derivative_zero_set_le {p : ℕ} [Fact p.Prime] (k : ℕ) (S : Finset (ZMod p))
    (hQ : (reductionPair p k).1 ≠ 0)
    (hzero : ∀ x ∈ S, (Polynomial.derivative^[k + 1] (truncatedLog p)).eval x = 0) :
    S.card ≤ k + 2 := by
  by_contra hcard
  apply hQ
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
  · intro x hx
    have he := weighted_derivative_eval_eq k x
    rw [hzero x hx, mul_zero] at he
    exact he.symm
  · exact lt_of_le_of_lt (reductionPair_degrees p k).1 (Nat.lt_of_not_ge hcard)

end PseudoPrime.NumberTheory.Heilbronn
