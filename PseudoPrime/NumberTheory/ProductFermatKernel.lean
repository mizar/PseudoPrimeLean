/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic

/-! # Exact ambient Fermat kernels at a product factor -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For positive p,m, gcd(p-1,pm-1)=gcd(p-1,m-1).
Expand pm-1 as m(p-1)+(m-1) and remove the first multiple.
This identifies the ambient local Fermat kernel from the cofactor. -/
theorem gcd_predecessor_product {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    (p - 1).gcd (p * m - 1) = (p - 1).gcd (m - 1) := by
  have hp' := Nat.sub_add_cancel hp
  have hm' := Nat.sub_add_cancel hm
  have hn' := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hp hm))
  have he : p * m - 1 = (m - 1) + m * (p - 1) := by nlinarith only [hp', hm', hn']
  rw [he, Nat.gcd_add_mul_right_right]

/-- For p>0 and m>1, the ambient kernel size gcd(p-1,pm-1) is at most
m-1. Use the exact cofactor identity and the positive right argument.
This turns a small cofactor into a small local Fermat kernel. -/
theorem gcd_predecessor_product_le_cofactor {p m : ℕ} (hp : 0 < p) (hm : 1 < m) :
    (p - 1).gcd (p * m - 1) ≤ m - 1 := by
  rw [gcd_predecessor_product hp (Nat.zero_lt_of_lt hm)]
  exact Nat.gcd_le_right _ (Nat.sub_pos_of_lt hm)

/-- For 0<p<m, the local Fermat kernel divides the positive gap m-p.
Subtract p-1 from m-1 after reducing to the cofactor predecessor.
This retains odd-part information for close factors rather than just signs. -/
theorem gcd_predecessor_product_dvd_gap {p m : ℕ} (hp : 0 < p) (hm : p < m) :
    (p - 1).gcd (p * m - 1) ∣ m - p := by
  rw [gcd_predecessor_product hp (hp.trans hm)]
  have hd := Nat.dvd_sub (Nat.gcd_dvd_right (p - 1) (m - 1)) (Nat.gcd_dvd_left (p - 1) (m - 1))
  rw [Nat.sub_sub_sub_cancel_right hp] at hd
  exact hd

/-- For 0<p<m, the ambient local Fermat kernel is at most m-p.
Combine gap divisibility with positivity. This is the arithmetic input
for a logarithmic-power MR bound on close-factor products. -/
theorem gcd_predecessor_product_le_gap {p m : ℕ} (hp : 0 < p) (hm : p < m) :
    (p - 1).gcd (p * m - 1) ≤ m - p := by
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hm) (gcd_predecessor_product_dvd_gap hp hm)

end PseudoPrime.NumberTheory
