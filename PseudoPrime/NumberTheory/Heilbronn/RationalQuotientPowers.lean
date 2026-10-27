/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalPowerCutoff
public import PseudoPrime.NumberTheory.Heilbronn.RationalUniformTail
public import PseudoPrime.NumberTheory.Heilbronn.RationalQuotientBase

/-! # Iterated quotient-set bounds with a natural power parameter -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a fixed height envelope U0, divisor bound T, logarithm bound K and positive
C at least 8*K*T^2, promote the n-th-power quotient estimate to exponent n+1.
Use a natural root cutoff unless the initial quotient bound already suffices; height descent
bounds all large slices. This is the induction step, with all rounding losses explicit. -/
theorem quotient_power_step {U0 K T C n : ℕ} (hCpos : 0 < C) (hC : 8 * K * T ^ 2 ≤ C)
    (hK : 1 + Real.log (U0 : ℝ) ≤ K) (hT : maxDivisorCount U0 ≤ T) (hn : 0 < n)
    (hrec :
      ∀ (Q D : ℕ) (A B : Finset ℚ),
        Q * D ≤ U0 →
          (∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) →
          (∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) →
          (A.card * B.card) ^ n ≤ C ^ (n ^ 2) * (Q * D) * (rationalQuotientSet A B).card ^ n)
    {Q D : ℕ} {A B : Finset ℚ} (hU : Q * D ≤ U0)
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    (A.card * B.card) ^ (n + 1) ≤
      C ^ ((n + 1) ^ 2) * (Q * D) * (rationalQuotientSet A B).card ^ (n + 1) := by
  classical
  let R := (rationalQuotientSet A B).card
  have hmono : C ^ (n ^ 2) ≤ C ^ ((n + 1) ^ 2) :=
    Nat.pow_le_pow_right hCpos (Nat.pow_le_pow_left (Nat.le_succ n) 2)
  by_cases hzero : Q * D = 0
  · have hz : A.card * B.card = 0 :=
      Nat.eq_zero_of_le_zero
        (by simpa only [hzero, Nat.zero_mul] using rational_quotient_base_bound (A := A) hB)
    rw [hz, zero_pow (Nat.succ_ne_zero n)]
    exact Nat.zero_le _
  · have hmass : 0 < C ^ (n ^ 2) * (Q * D) :=
      Nat.mul_pos (Nat.pow_pos hCpos) (Nat.pos_of_ne_zero hzero)
    rcases exists_power_cutoff_or_base (U := Q * D) hmass (Nat.succ_pos n) with
      ⟨x, hx, hxU, hxlow, hxhigh⟩ | hbase
    · have hlog : 1 + Real.log (x : ℝ) ≤ K := by
        have hl := Real.log_le_log (Nat.cast_pos.mpr hx) (Nat.cast_le.mpr (hxU.trans hU))
        linarith only [hl, hK]
      have hdiv : maxDivisorCount (Q * D) ≤ T := (maxDivisorCount_mono hU).trans hT
      have hsmall :
        ∀ rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x),
          (divisorSlice A rs.1 rs.2).card * (divisorSlice B rs.1 rs.2).card ≤ x * R := by
        intro rs hrs
        have hm := Finset.mem_filter.mp hrs
        have hp := quotientGcdIndex_pos (fun q hq ↦ (hA q hq).1) hm.1
        have ht :=
          slice_power_mul_indices_le_of_recursive_bound hA hB hp.1 hp.2
            (fun A' B' hA' hB' ↦
              hrec (Q / rs.1) (D / rs.2) A' B'
                ((Nat.mul_le_mul (Nat.div_le_self Q rs.1) (Nat.div_le_self D rs.2)).trans hU) hA'
                hB')
        exact
          product_le_of_powered_index_budget hx hn (Nat.le_of_lt (Nat.lt_of_not_ge hm.2)) ht hxlow
      have hb := quotient_bound_of_uniform_tail hA hB hx hlog hdiv hsmall
      have he : A.card * B.card ≤ (4 * K * T ^ 2 * R) * x := by
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb
      calc
        _ ≤ ((4 * K * T ^ 2 * R) * x) ^ (n + 1) := Nat.pow_le_pow_left he (n + 1)
        _ = (4 * K * T ^ 2 * R) ^ (n + 1) * x ^ (n + 1) := mul_pow _ _ _
        _ ≤ (4 * K * T ^ 2 * R) ^ (n + 1) * (2 ^ (n + 1) * (C ^ (n ^ 2) * (Q * D))) :=
          Nat.mul_le_mul_left _ hxhigh
        _ = (8 * K * T ^ 2) ^ (n + 1) * C ^ (n ^ 2) * (Q * D) * R ^ (n + 1) := by
          rw [show 8 = 4 * 2 from rfl]
          simp only [mul_pow]
          ring
        _ ≤ C ^ (n + 1) * C ^ (n ^ 2) * (Q * D) * R ^ (n + 1) :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hC (n + 1))))
        _ ≤ _ := by
          have hp := Nat.pow_le_pow_right hCpos (show n + 1 + n ^ 2 ≤ (n + 1) ^ 2 by nlinarith only)
          have ht := Nat.mul_le_mul_right ((Q * D) * R ^ (n + 1)) hp
          simpa only [pow_add, Nat.mul_assoc] using ht
    · have hb := Nat.pow_le_pow_left (rational_quotient_base_bound (A := A) hB) (n + 1)
      have ht := Nat.mul_le_mul_right (R ^ (n + 1)) hbase
      have hu := Nat.mul_le_mul_right ((Q * D) * R ^ (n + 1)) hmono
      calc
        _ ≤ ((Q * D) * R) ^ (n + 1) := hb
        _ = (Q * D) ^ (n + 1) * R ^ (n + 1) := mul_pow _ _ _
        _ ≤ C ^ (n ^ 2) * (Q * D) * R ^ (n + 1) := ht
        _ ≤ _ := by simpa only [Nat.mul_assoc] using hu

/-- For a height envelope U0, logarithm and divisor bounds K,T, and positive C at least
8*K*T^2, every positive bounded rational pair of families satisfies
(card(A)*card(B))^n at most C^(n^2)*Q*D*card(A/B)^n for each positive natural n.
Induct from the initial quotient estimate using the powered cutoff step. -/
theorem rational_quotient_power_bound {U0 K T C n : ℕ} (hCpos : 0 < C) (hC : 8 * K * T ^ 2 ≤ C)
    (hK : 1 + Real.log (U0 : ℝ) ≤ K) (hT : maxDivisorCount U0 ≤ T) (hn : 0 < n) :
    ∀ (Q D : ℕ) (A B : Finset ℚ),
      Q * D ≤ U0 →
        (∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) →
        (∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) →
        (A.card * B.card) ^ n ≤ C ^ (n ^ 2) * (Q * D) * (rationalQuotientSet A B).card ^ n := by
  refine Nat.le_induction ?_ ?_ n hn
  · intro Q D A B hU hA hB
    have hb := rational_quotient_base_bound (A := A) hB
    have hm := Nat.le_mul_of_pos_left ((Q * D) * (rationalQuotientSet A B).card) hCpos
    norm_num only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
    simpa only [Nat.mul_assoc] using hb.trans hm
  · intro k hk hrec Q D A B hU hA hB
    exact quotient_power_step hCpos hC hK hT hk hrec hU hA hB

/-- The natural coefficient 8*ceil(1+log U)*maxDivisorCount(U)^2 for quotient induction.
Input U bounds the numerator-denominator height product. The ceiling keeps the induction
and its cutoff selection in natural arithmetic, without finite enumeration. -/
noncomputable def quotientPowerConstant (U : ℕ) : ℕ :=
  8 * Nat.ceil (1 + Real.log (U : ℝ)) * maxDivisorCount U ^ 2

/-- For positive height product U, the quotient coefficient is positive.
The logarithm is nonnegative and the divisor-count maximum contains the divisor count of 1. -/
theorem quotientPowerConstant_pos {U : ℕ} (hU : 0 < U) : 0 < quotientPowerConstant U := by
  have hl : 0 ≤ Real.log (U : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hU)
  have hk : 0 < Nat.ceil (1 + Real.log (U : ℝ)) := Nat.ceil_pos.mpr (by linarith only [hl])
  have ht : 1 ≤ maxDivisorCount U := by
    have h := divisors_card_le_maxDivisorCount (d := 1) hU
    simpa only [Nat.divisors_one, Finset.card_singleton] using h
  exact Nat.mul_pos (Nat.mul_pos (by norm_num only) hk) (Nat.pow_pos ht)

/-- For positive height product Q*D and positive n, obtain the n-th-power quotient bound
with the explicit quotientPowerConstant and no additional analytic premise.
Instantiate the generic height envelope at Q*D and use the ceiling logarithm bound. -/
theorem rational_quotient_power_bound_explicit {A B : Finset ℚ} {Q D n : ℕ} (hU : 0 < Q * D)
    (hn : 0 < n) (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    (A.card * B.card) ^ n ≤
      quotientPowerConstant (Q * D) ^ (n ^ 2) * (Q * D) * (rationalQuotientSet A B).card ^ n := by
  exact
    rational_quotient_power_bound (quotientPowerConstant_pos hU) (le_refl _) (Nat.le_ceil _)
      (le_refl _) hn Q D A B (le_refl _) hA hB

/-- Extract an n-th root of a natural count inequality with coefficient C^(n^2).
For positive n, a^n at most C^(n^2)*U*R^n implies a at most C^n*U^(1/n)*R over the reals.
Compare n-th powers of nonnegative reals and cancel the natural root of U. -/
theorem root_of_natural_power_bound {a C U R n : ℕ} (hn : 0 < n)
    (h : a ^ n ≤ C ^ (n ^ 2) * U * R ^ n) : (a : ℝ) ≤ (C : ℝ) ^ n * (U : ℝ) ^ ((n : ℝ)⁻¹) * R := by
  have hright : 0 ≤ (C : ℝ) ^ n * (U : ℝ) ^ ((n : ℝ)⁻¹) * R :=
    mul_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg C) _) (Real.rpow_nonneg (Nat.cast_nonneg U) _))
      (Nat.cast_nonneg R)
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg a) hright (ne_of_gt hn)).mp
  have he :
    ((C : ℝ) ^ n * (U : ℝ) ^ ((n : ℝ)⁻¹) * R) ^ n = (C : ℝ) ^ (n ^ 2) * U * (R : ℝ) ^ n := by
    simp only [mul_pow, ← pow_mul, ← pow_two,
      Real.rpow_inv_natCast_pow (Nat.cast_nonneg U) (ne_of_gt hn)]
  rw [he]
  have hc := Nat.cast_le (α := ℝ).mpr h
  simpa only [Nat.cast_mul, Nat.cast_pow] using hc

/-- For positive height product Q*D and positive n, bound card(A)*card(B) by
quotientPowerConstant(Q*D)^n*(Q*D)^(1/n)*card(A/B).
Take the positive natural root of the proved powered estimate. The height exponent 1/n
is available for arbitrary n, with the divisor and logarithmic coefficient retained. -/
theorem rational_quotient_root_bound {A B : Finset ℚ} {Q D n : ℕ} (hU : 0 < Q * D) (hn : 0 < n)
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    (A.card : ℝ) * B.card ≤
      (quotientPowerConstant (Q * D) : ℝ) ^ n * ((Q * D : ℕ) : ℝ) ^ ((n : ℝ)⁻¹) *
        (rationalQuotientSet A B).card := by
  have h := root_of_natural_power_bound hn (rational_quotient_power_bound_explicit hU hn hA hB)
  simpa only [Nat.cast_mul] using h

end PseudoPrime.NumberTheory.Heilbronn
