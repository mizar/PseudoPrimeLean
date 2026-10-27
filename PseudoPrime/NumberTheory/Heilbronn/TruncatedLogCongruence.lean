/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PrimeSquareLifts
public import PseudoPrime.NumberTheory.Heilbronn.FrobeniusAuxiliary
public import Mathlib.Algebra.Polynomial.OfFn

/-! # Truncated logarithms and prime-square coset differences -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For prime p, polynomials with equal reductions have equal p-multiples,
coefficient by coefficient. This transfers derivative identities to ZMod(p^2). -/
theorem prime_mul_polynomial_eq_of_map_eq {p : ℕ} [Fact p.Prime] {F G : Polynomial (ZMod (p ^ 2))}
    (h : F.map (squareReduction p) = G.map (squareReduction p)) :
    Polynomial.C (p : ZMod (p ^ 2)) * F = Polynomial.C (p : ZMod (p ^ 2)) * G := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  apply prime_mul_eq_of_reduction_eq
  have he := congrArg (fun P : Polynomial (ZMod p) ↦ P.coeff n) h
  simpa only [Polynomial.coeff_map] using he

/-- Polynomial of degree less than p formed from canonical lifts of truncated-log
coefficients. Its reduction is the truncated logarithm for prime p. -/
noncomputable def liftedTruncatedLog (p : ℕ) : Polynomial (ZMod (p ^ 2)) := by
  classical exact Polynomial.ofFn p (fun j ↦ (((truncatedLog p).coeff j).val : ZMod (p ^ 2)))

/-- For prime p reduction of the lifted polynomial recovers the truncated logarithm. -/
theorem map_liftedTruncatedLog {p : ℕ} [Fact p.Prime] :
    (liftedTruncatedLog p).map (squareReduction p) = truncatedLog p := by
  classical
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map]
  by_cases hn : n < p
  · rw [liftedTruncatedLog, Polynomial.ofFn_coeff_eq_val_of_lt _ hn, squareReduction_lift_val]
  · rw [liftedTruncatedLog, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hn), map_zero]
    exact
      (Polynomial.coeff_eq_zero_of_natDegree_lt
          (natDegree_truncatedLog_le.trans_lt
            ((Nat.sub_lt (Nat.Prime.pos Fact.out) (by decide : 0 < 1)).trans_le
              (Nat.le_of_not_gt hn)))).symm

/-- For prime p the lifted truncated logarithm has degree less than p, by ofFn support. -/
theorem natDegree_liftedTruncatedLog_lt {p : ℕ} [Fact p.Prime] :
    (liftedTruncatedLog p).natDegree < p := by
  classical exact Polynomial.ofFn_natDegree_lt (Nat.Prime.pos Fact.out) _

/-- For prime p, p times the lifted evaluation is the additive lift of the reduced evaluation. -/
theorem prime_mul_liftedTruncatedLog_eval {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * (liftedTruncatedLog p).eval x =
      primeLift p ((truncatedLog p).eval (squareReduction p x)) := by
  have he :
    squareReduction p ((liftedTruncatedLog p).eval x) =
      (truncatedLog p).eval (squareReduction p x) := by
    rw [← map_liftedTruncatedLog]
    exact (Polynomial.eval_map_apply (f := squareReduction p) x).symm
  rw [← he, primeLift_reduction]

/-- For prime p a polynomial over ZMod(p^2) of degree less than p, with zero
derivative and constant coefficient, vanishes. Each positive coefficient index below p is a unit. -/
theorem polynomial_eq_zero_of_derivative_eq_zero {p : ℕ} [Fact p.Prime]
    {F : Polynomial (ZMod (p ^ 2))} (hd : F.natDegree < p) (hder : F.derivative = 0)
    (h0 : F.coeff 0 = 0) : F = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn : n = 0
  · exact hn ▸ h0
  by_cases hnp : n < p
  · have hcop : n.Coprime (p ^ 2) :=
      Nat.Coprime.pow_right 2
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
            (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) hnp)).symm
    have he := congrArg (fun P : Polynomial (ZMod (p ^ 2)) ↦ P.coeff (n - 1)) hder
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at he
    have hs : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
    rw [← Nat.cast_one (R := ZMod (p ^ 2)), ← Nat.cast_add, hs] at he
    exact ((ZMod.isUnit_iff_coprime n (p ^ 2)).mpr hcop).mul_left_eq_zero.mp he
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_le (Nat.le_of_not_gt hnp))

/-- For prime p the truncated-log derivative is (1-X)^(p-1)-X^(p-1).
Multiply by X(1-X), use Frobenius and cancel the nonzero weight. -/
theorem derivative_truncatedLog_eq_sub_powers {p : ℕ} [Fact p.Prime] :
    (truncatedLog p).derivative =
      (1 - Polynomial.X) ^ (p - 1) - (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.Prime.one_lt Fact.out).le
  have hf : (1 - Polynomial.X : Polynomial (ZMod p)) ^ p = 1 - Polynomial.X ^ p := by
    rw [sub_pow_char, one_pow]
  have he :
    weight p * ((1 - Polynomial.X) ^ (p - 1) - (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1)) =
      Polynomial.X - Polynomial.X ^ p := by
    have h1 :
      (1 - Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) * (1 - Polynomial.X) =
        1 - Polynomial.X ^ p := by
      rw [← pow_succ, hp, hf]
    have h2 : (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) * Polynomial.X = Polynomial.X ^ p := by
      rw [← pow_succ, hp]
    dsimp only [weight]
    linear_combination Polynomial.X * h1 - (1 - Polynomial.X) * h2
  have hw : weight p ≠ 0 := by
    dsimp only [weight]
    apply mul_ne_zero Polynomial.X_ne_zero
    intro hz
    have hc := congrArg (fun P : Polynomial (ZMod p) ↦ P.coeff 1) hz
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X, one_ne_zero,
      ite_false, ite_true, zero_sub, Polynomial.coeff_zero, neg_eq_zero] at hc
  exact mul_left_cancel₀ hw ((weight_mul_derivative_truncatedLog).trans he.symm)

/-- Polynomial (1-X)^p-1+X^p over ZMod(p^2). For odd prime p its top
coefficient cancels; its remaining terms encode the lifted truncated logarithm. -/
noncomputable def binomialError (p : ℕ) : Polynomial (ZMod (p ^ 2)) :=
  (1 - Polynomial.X) ^ p - 1 + Polynomial.X ^ p

/-- For odd prime p the binomial error has degree less than p.
Bound the degree by p and cancel the coefficient of X^p using oddness. -/
theorem natDegree_binomialError_lt {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (binomialError p).natDegree < p := by
  let : Nontrivial (ZMod (p ^ 2)) := (squareReduction p).domain_nontrivial
  have hlin : (1 - Polynomial.X : Polynomial (ZMod (p ^ 2))).natDegree ≤ 1 := by
    exact
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le (Polynomial.natDegree_one.le.trans (Nat.zero_le 1)) Polynomial.natDegree_X.le)
  have hpow : ((1 - Polynomial.X : Polynomial (ZMod (p ^ 2))) ^ p).natDegree ≤ p := by
    exact Polynomial.natDegree_pow_le.trans ((Nat.mul_le_mul_left p hlin).trans_eq (Nat.mul_one p))
  have hdeg : (binomialError p).natDegree ≤ p := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact
        (Polynomial.natDegree_sub_le _ _).trans
          (max_le hpow (Polynomial.natDegree_one.le.trans (Nat.zero_le p)))
    · exact Polynomial.natDegree_X_pow_le p
  have hc : (binomialError p).coeff p = 0 := by
    have hp0 : p ≠ 0 := Nat.Prime.ne_zero Fact.out
    have ht :
      ((1 - Polynomial.X : Polynomial (ZMod (p ^ 2))) ^ p).coeff p = (-1 : ZMod (p ^ 2)) ^ p := by
      have he := Polynomial.coeff_pow_of_natDegree_le (m := p) hlin
      simpa only [Nat.mul_one, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X,
        one_ne_zero, ite_false, ite_true, zero_sub] using he
    dsimp only [binomialError]
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, ht, hodd.neg_one_pow]
    simp only [Polynomial.coeff_one, hp0, ite_false, sub_zero, Polynomial.coeff_X_pow_self,
      neg_add_cancel]
  exact
    (Polynomial.natDegree_le_pred hdeg hc).trans_lt
      (Nat.sub_lt (Nat.Prime.pos Fact.out) (by decide : 0 < 1))

/-- For odd prime p, (1-X)^p-1+X^p equals -p times the lifted logarithm.
The reduced derivative identity makes the derivative zero, and degree and constant term finish. -/
theorem binomialError_add_liftedTruncatedLog {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    binomialError p + Polynomial.C (p : ZMod (p ^ 2)) * liftedTruncatedLog p = 0 := by
  apply polynomial_eq_zero_of_derivative_eq_zero
  · exact
      (Polynomial.natDegree_add_le _ _).trans_lt
        (max_lt (natDegree_binomialError_lt hodd)
          ((Polynomial.natDegree_C_mul_le _ _).trans_lt natDegree_liftedTruncatedLog_lt))
  · have hm :
      (-(1 - Polynomial.X) ^ (p - 1) + (Polynomial.X : Polynomial (ZMod (p ^ 2))) ^ (p - 1) +
              (liftedTruncatedLog p).derivative).map
          (squareReduction p) =
        0 := by
      rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_neg, Polynomial.map_pow,
        Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, ←
        Polynomial.derivative_map, map_liftedTruncatedLog, derivative_truncatedLog_eq_sub_powers]
      ring
    have hz :=
      prime_mul_polynomial_eq_of_map_eq (G := 0)
        (hm.trans (Polynomial.map_zero (squareReduction p)).symm)
    rw [mul_zero] at hz
    rw [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
      zero_add]
    dsimp only [binomialError]
    rw [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_pow,
      Polynomial.derivative_one, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X, zero_sub, Polynomial.derivative_X_pow]
    linear_combination hz
  · have hp0 : p ≠ 0 := Nat.Prime.ne_zero Fact.out
    have hf0 : (truncatedLog p).coeff 0 = 0 := by
      rw [truncatedLog, Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp only [Nat.zero_ne_add_one, ite_false, mul_zero]
    dsimp only [binomialError]
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hl0 : (liftedTruncatedLog p).coeff 0 = 0 := by
      classical
        rw [liftedTruncatedLog, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.Prime.pos Fact.out), hf0,
        ZMod.val_zero, Nat.cast_zero]
    rw [hl0, mul_zero, add_zero]
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      sub_zero, one_pow, Polynomial.coeff_one, ite_true, sub_self, Polynomial.coeff_X_pow,
      Ne.symm hp0, ite_false, add_zero]

/-- For odd prime p and x modulo p^2, x^p-(x-1)^p equals one minus the
additive lift of the truncated logarithm at the reduction of x. Evaluate the polynomial identity. -/
theorem pow_sub_pow_eq_truncatedLog {p : ℕ} [Fact p.Prime] (hodd : Odd p) (x : ZMod (p ^ 2)) :
    x ^ p - (x - 1) ^ p = 1 - primeLift p ((truncatedLog p).eval (squareReduction p x)) := by
  have he :=
    congrArg (fun P : Polynomial (ZMod (p ^ 2)) ↦ P.eval x)
      (binomialError_add_liftedTruncatedLog hodd)
  dsimp only [binomialError] at he
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero,
    prime_mul_liftedTruncatedLog_eval] at he
  have hn : (x - 1) ^ p = -(1 - x) ^ p := by rw [← neg_sub, hodd.neg_pow]
  rw [hn]
  linear_combination he

/-- For odd prime p, the difference of lifts of b and b-1 equals one minus
the additive lift of the truncated logarithm. This is the basic Heilbronn difference formula. -/
theorem teichLift_sub_teichLift {p : ℕ} [Fact p.Prime] (hodd : Odd p) (b : ZMod p) :
    teichLift p b - teichLift p (b - 1) = 1 - primeLift p ((truncatedLog p).eval b) := by
  have ht : teichLift p (b - 1) = ((b.val : ZMod (p ^ 2)) - 1) ^ p := by
    rw [← teichLift_reduction]
    rw [map_sub, squareReduction_lift_val, map_one]
  rw [ht, teichLift, pow_sub_pow_eq_truncatedLog hodd, squareReduction_lift_val]

/-- For odd prime p, compute the difference of two principal-shifted Teichmuller
lifts with residues b and b-1. Preserve the affine truncated-log error exactly. -/
theorem shifted_teichLift_difference {p : ℕ} [Fact p.Prime] (hodd : Odd p) (i j b : ZMod p) :
    principalShift p i * teichLift p b - principalShift p j * teichLift p (b - 1) =
      1 + primeLift p ((i - j) * b + j - (truncatedLog p).eval b) := by
  have hi := primeLift_mul i (teichLift p b)
  have hj := primeLift_mul j (teichLift p (b - 1))
  rw [squareReduction_teichLift] at hi hj
  rw [primeLift_sub, primeLift_add]
  dsimp only [principalShift]
  rw [add_mul, add_mul, one_mul, one_mul, ← hi, ← hj]
  have he := teichLift_sub_teichLift hodd b
  have ha : primeLift p ((i - j) * b) = primeLift p (i * b) - primeLift p (j * b) := by
    rw [sub_mul, primeLift_sub]
  rw [ha]
  have hb : primeLift p (j * (b - 1)) = primeLift p (j * b) - primeLift p j := by
    rw [mul_sub, mul_one, primeLift_sub]
  rw [hb]
  linear_combination he

/-- For odd prime p, a normalized coset difference equals the principal shift of tau
exactly when f(b)=(i-j)b+j-tau. Injectivity of the additive lift proves both directions. -/
theorem shifted_teichLift_difference_iff {p : ℕ} [Fact p.Prime] (hodd : Odd p) (i j τ b : ZMod p) :
    principalShift p i * teichLift p b - principalShift p j * teichLift p (b - 1) =
        principalShift p τ ↔
      (truncatedLog p).eval b = (i - j) * b + j - τ := by
  rw [shifted_teichLift_difference hodd]
  dsimp only [principalShift]
  rw [add_right_inj, primeLift_injective.eq_iff]
  constructor <;> intro h <;> linear_combination -h

end PseudoPrime.NumberTheory.Heilbronn
