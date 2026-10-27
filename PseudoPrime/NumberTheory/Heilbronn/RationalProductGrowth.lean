/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalProductHeights

/-! # Iterated growth of finite rational product sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a positive height-H rational family, apply the n-th-power quotient bound to its m-fold
product set and inverse family. A fixed height envelope and coefficient give
(card(P_m)*card(A))^n at most C^(n^2)*H^(2m)*card(P_(m+1))^n.
Identify the quotient with the next product set and preserve the inverse family's cardinality. -/
theorem rationalProductSet_power_step {A : Finset ℚ} {H U0 K T C n m : ℕ} (hH : 0 < H) (hm : 0 < m)
    (hn : 0 < n) (hCpos : 0 < C) (hC : 8 * K * T ^ 2 ≤ C) (hK : 1 + Real.log (U0 : ℝ) ≤ K)
    (hT : maxDivisorCount U0 ≤ T) (hU : H ^ (2 * m) ≤ U0)
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H) :
    ((rationalProductSet A m).card * A.card) ^ n ≤
      C ^ (n ^ 2) * H ^ (2 * m) * (rationalProductSet A (m + 1)).card ^ n := by
  classical
  have hh : H ≤ H ^ m := by
    have h := Nat.pow_le_pow_right hH hm
    simpa only [pow_one] using h
  have hi : ∀ q ∈ A.image (fun q ↦ q⁻¹), 0 < q ∧ q.num.natAbs ≤ H ^ m ∧ q.den ≤ H ^ m := by
    intro q hq
    have h := inverse_family_height hA q hq
    exact ⟨h.1, h.2.1.trans hh, h.2.2.trans hh⟩
  have he : H ^ m * H ^ m = H ^ (2 * m) := by
    rw [← pow_add]
    congr 1
    ring
  have h :=
    rational_quotient_power_bound hCpos hC hK hT hn (H ^ m) (H ^ m) (rationalProductSet A m)
      (A.image (fun q ↦ q⁻¹)) (he ▸ hU) (rationalProductSet_height hA) hi
  rw [Finset.card_image_of_injective _ inv_injective, quotient_inverse_eq_product_succ, he] at h
  exact h

/-- For a positive height-H rational family and fixed envelope H^(2M), telescope the powered
quotient bounds for the first k+1 product sets, where k is less than M.
The result is card(A)^(n*(k+1)) at most
C^(n^2*k)*H^(k*(k+1))*card(P_(k+1))^n. Keep all losses explicit in natural powers. -/
theorem rationalProductSet_power_growth {A : Finset ℚ} {H M K T C n : ℕ} (hH : 0 < H) (hn : 0 < n)
    (hCpos : 0 < C) (hC : 8 * K * T ^ 2 ≤ C) (hK : 1 + Real.log ((H ^ (2 * M) : ℕ) : ℝ) ≤ K)
    (hT : maxDivisorCount (H ^ (2 * M)) ≤ T) (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H) :
    ∀ k : ℕ,
      k < M →
        A.card ^ (n * (k + 1)) ≤
          C ^ (n ^ 2 * k) * H ^ (k * (k + 1)) * (rationalProductSet A (k + 1)).card ^ n := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [rationalProductSet_one]
    norm_num only [Nat.zero_add, Nat.mul_one, Nat.mul_zero, pow_zero, Nat.one_mul]
    exact le_refl _
  | succ k ih =>
    intro hk
    have hi := ih (Nat.lt_trans (Nat.lt_succ_self k) hk)
    have hstep :=
      rationalProductSet_power_step hH (Nat.succ_pos k) hn hCpos hC hK hT
        (Nat.pow_le_pow_right hH (Nat.mul_le_mul_left 2 (Nat.le_of_lt hk))) hA
    have hmul := Nat.mul_le_mul_right (A.card ^ n) hi
    have hsub := Nat.mul_le_mul_left (C ^ (n ^ 2 * k) * H ^ (k * (k + 1))) hstep
    have hleft : A.card ^ (n * (k + 1 + 1)) = A.card ^ (n * (k + 1)) * A.card ^ n := by
      rw [← pow_add]
      congr 1
    have hright :
      (C ^ (n ^ 2 * k) * H ^ (k * (k + 1))) *
          (C ^ (n ^ 2) * H ^ (2 * (k + 1)) * (rationalProductSet A (k + 1 + 1)).card ^ n) =
        C ^ (n ^ 2 * (k + 1)) * H ^ ((k + 1) * (k + 1 + 1)) *
          (rationalProductSet A (k + 1 + 1)).card ^ n := by
      rw [show n ^ 2 * (k + 1) = n ^ 2 * k + n ^ 2 from by ring,
        show (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) from by ring, pow_add, pow_add]
      ring
    rw [hleft]
    apply LE.le.trans _ (hright ▸ hsub)
    simpa only [mul_pow, Nat.mul_assoc] using hmul

/-- For positive height H and positive product count m and power parameter n, prove
card(A)^(n*m) at most quotientPowerConstant(H^(2m))^(n^2*(m-1)) times
H^((m-1)*m)*card(P_m)^n. Instantiate the telescoped growth estimate without a supplied
growth hypothesis or additional analytic input. -/
theorem rationalProductSet_power_growth_explicit {A : Finset ℚ} {H m n : ℕ} (hH : 0 < H)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H) :
    A.card ^ (n * m) ≤
      quotientPowerConstant (H ^ (2 * m)) ^ (n ^ 2 * (m - 1)) * H ^ ((m - 1) * m) *
        (rationalProductSet A m).card ^ n := by
  have h :=
    rationalProductSet_power_growth hH hn (quotientPowerConstant_pos (Nat.pow_pos hH)) (le_refl _)
      (Nat.le_ceil _) (le_refl _) hA (m - 1) (Nat.sub_lt hm (by norm_num only))
  simpa only [Nat.sub_add_cancel hm] using h

end PseudoPrime.NumberTheory.Heilbronn
