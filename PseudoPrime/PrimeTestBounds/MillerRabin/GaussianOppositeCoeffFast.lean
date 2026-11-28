/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassCoefficients
import Mathlib.Tactic.Ring

/-! # Binomial coefficients for mixed poles

The closed form evaluates coefficients directly from the pole orders and output degree.
-/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At or above the positive pole order, the mixed coefficient is zero. -/
public theorem opposite_coeff_eq_zero (a : ℚ) (p q j : ℕ) (hj : p ≤ j) :
    oppositePoleCoeff a p q j = 0 := by
  induction p, q using oppositePolePolynomial.induct with
  | case1 q => simp only [oppositePoleCoeff]
  | case2 n =>
    have hn : n ≠ j := (Nat.lt_of_succ_le hj).ne
    simp only [oppositePoleCoeff, ite_eq_right hn]
  | case3 =>
    have hn : j ≠ 0 := Nat.ne_of_gt (show 0 < j from hj)
    simp only [oppositePoleCoeff, ite_eq_right hn]
  | case4 p q hne hp hq =>
    rw [oppositePoleCoeff.eq_4 a j p q hne, hp ((Nat.le_succ p).trans hj), hq hj, add_zero,
      mul_zero]

/-- At the highest possible degree, only the recurrence along the negative pole survives. -/
private theorem opposite_coeff_top_succ (a : ℚ) (j q : ℕ) :
    oppositePoleCoeff a (j + 1) (q + 1) j = (1 / (2 * a)) * oppositePoleCoeff a (j + 1) q j := by
  by_cases h : j = 0 ∧ q = 0
  · rcases h with ⟨rfl, rfl⟩
    change oppositePoleCoeff a 1 1 0 = _
    simp only [oppositePoleCoeff, ite_true, Nat.factorial_zero, Nat.cast_one, div_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [oppositePoleCoeff.eq_4 a j j q (fun hj hq ↦ h ⟨hj, hq⟩),
      opposite_coeff_eq_zero a j (q + 1) j le_rfl, zero_add]

/-- The highest surviving Fourier coefficient is a single reciprocal power. -/
private theorem opposite_coeff_top (a : ℚ) (j q : ℕ) :
    oppositePoleCoeff a (j + 1) q j = (2 / (j.factorial : ℚ)) / (2 * a) ^ q := by
  induction q with
  | zero => simp only [oppositePoleCoeff, ite_true, pow_zero, div_one]
  | succ q ih =>
    rw [opposite_coeff_top_succ, ih, pow_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- At negative pole order one the mixed coefficient has no binomial factor. -/
private theorem opposite_coeff_second_one (a : ℚ) (j u : ℕ) :
    oppositePoleCoeff a (j + 1 + u) 1 j = (2 / (j.factorial : ℚ)) / (2 * a) ^ (u + 1) := by
  induction u with
  | zero => exact opposite_coeff_top a j 1
  | succ u
    ih =>
    have hne : j + 1 + u = 0 → (0 : ℕ) = 0 → False := fun h _ ↦
      (Nat.succ_ne_zero (j + u)) (by simpa only [Nat.add_right_comm j 1 u] using h)
    change oppositePoleCoeff a (j + 1 + u).succ (Nat.succ 0) j = _
    rw [oppositePoleCoeff.eq_4 a j (j + 1 + u) 0 hne, ih]
    have hj : j < j + 1 + u := (Nat.lt_succ_self j).trans_le (Nat.le_add_right _ _)
    have hn : oppositePoleCoeff a ((j + 1 + u) + 1) 0 j = 0 := by
      simp only [oppositePoleCoeff, ite_eq_right hj.ne']
    rw [hn, add_zero, show u.succ + 1 = (u + 1) + 1 by rfl, pow_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The mixed-pole coefficient at degree `j` is a binomial times a reciprocal power.
Induction on the excess pole orders gives Pascal's identity in the interior. -/
public theorem opposite_coeff_binomial (a : ℚ) (j u v : ℕ) :
    oppositePoleCoeff a (j + 1 + u) (v + 1) j =
      (2 / (j.factorial : ℚ)) * ((u + v).choose v : ℚ) / (2 * a) ^ (u + v + 1) := by
  induction u generalizing v with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Nat.choose_self, Nat.cast_one, mul_one] using
      opposite_coeff_top a j (v + 1)
  | succ u ihu =>
    induction v with
    | zero =>
      simpa only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using
        opposite_coeff_second_one a j u.succ
    | succ v ihv =>
      change oppositePoleCoeff a (j + 1 + u).succ (v + 1).succ j = _
      rw [oppositePoleCoeff.eq_4 a j (j + 1 + u) (v + 1) (fun _ ↦ Nat.succ_ne_zero v), ihu (v + 1),
        Nat.add_assoc (j + 1) u 1, ihv]
      have hadd : u + 1 + v = u + (v + 1) := by rw [Nat.add_right_comm u 1 v, Nat.add_assoc]
      have hsum : u + 1 + (v + 1) = (u + (v + 1)).succ := congrArg Nat.succ hadd
      rw [hadd, hsum, Nat.choose_succ_succ, Nat.cast_add]
      change
        _ =
          (2 / (j.factorial : ℚ)) *
              (((u + (v + 1)).choose v : ℚ) + ((u + (v + 1)).choose (v + 1) : ℚ)) /
            (2 * a) ^ ((u + (v + 1) + 1) + 1)
      rw [pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Compute a mixed coefficient using the two pole orders and the output degree. -/
@[expose]
public def oppositeCoeffFast (a : ℚ) (p q j : ℕ) : ℚ :=
  if j < p then
    match q with
    | 0 => if p = j + 1 then 2 / (j.factorial : ℚ) else 0
    | v + 1 =>
      let u := p - (j + 1)
      (2 / (j.factorial : ℚ)) * (Nat.fast_choose (u + v) v : ℚ) / (2 * a) ^ (u + v + 1)
  else 0

/-- The binomial computation agrees with the recurrence at every pole order and degree. -/
public theorem oppositeCoeffFast_eq (a : ℚ) (p q j : ℕ) :
    oppositeCoeffFast a p q j = oppositePoleCoeff a p q j := by
  by_cases hj : j < p
  · cases q with
    | zero =>
      cases p with
      | zero => exact (Nat.not_lt_zero j hj).elim
      | succ
        p =>
        simp only [oppositeCoeffFast, ite_eq_left hj, oppositePoleCoeff, Nat.succ.injEq]
        split
        · rename_i h
          rw [h]
        · rfl
    | succ v =>
      have hp := Nat.add_sub_of_le (Nat.succ_le_of_lt hj)
      rw [oppositeCoeffFast, ite_eq_left hj, ← Nat.choose_eq_fast_choose, ← opposite_coeff_binomial,
        hp]
  · rw [oppositeCoeffFast.eq_def, ite_eq_right hj,
      opposite_coeff_eq_zero a p q j (Nat.le_of_not_gt hj)]

end PseudoPrime.PrimeTestBounds.MillerRabin
