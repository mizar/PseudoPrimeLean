/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ProductFermatKernel

/-! # Local Fermat kernels for affine cofactor progressions -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For p>0 and cofactor k(p-1)+r+1, the exact local Fermat kernel is
gcd(p-1,r). Remove the cofactor predecessor's multiple of p-1.
This allows an arbitrarily large cofactor with a small positive remainder. -/
theorem gcd_predecessor_affine_product {p k r : ℕ} (hp : 0 < p) :
    (p - 1).gcd (p * (k * (p - 1) + r + 1) - 1) = (p - 1).gcd r := by
  rw [gcd_predecessor_product hp (Nat.succ_pos _), Nat.succ_sub_one]
  rw [Nat.add_comm (k * (p - 1)) r, Nat.gcd_add_mul_right_right]

/-- For p>0, the affine product's local kernel divides r. Apply the exact
gcd identity. This supplies a finite exponent for pointwise MR rejection. -/
theorem gcd_predecessor_affine_product_dvd {p k r : ℕ} (hp : 0 < p) :
    (p - 1).gcd (p * (k * (p - 1) + r + 1) - 1) ∣ r := by
  rw [gcd_predecessor_affine_product hp]
  exact Nat.gcd_dvd_right (p - 1) r

/-- If r>0, the affine product's local kernel is at most r. The multiplier
k is unrestricted, so the estimate is uniform along the cofactor progression.
This is the input to the existing logarithmic-power kernel theorem. -/
theorem gcd_predecessor_affine_product_le {p k r : ℕ} (hp : 0 < p) (hr : 0 < r) :
    (p - 1).gcd (p * (k * (p - 1) + r + 1) - 1) ≤ r := by
  exact Nat.le_of_dvd hr (gcd_predecessor_affine_product_dvd hp)

/-- The local kernel divides the Euclidean remainder of m-1 modulo p-1.
Use the product identity and the gcd recursion. This lets a computed
remainder supply the affine offset without enumerating the multiplier. -/
theorem gcd_predecessor_product_dvd_remainder {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    (p - 1).gcd (p * m - 1) ∣ (m - 1) % (p - 1) := by
  rw [gcd_predecessor_product hp hm, Nat.gcd_rec]
  exact Nat.gcd_dvd_left ((m - 1) % (p - 1)) (p - 1)

end PseudoPrime.NumberTheory
