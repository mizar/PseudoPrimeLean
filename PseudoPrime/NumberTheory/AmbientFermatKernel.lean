/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitPowerCardinality

/-! # Ambient Fermat power kernels at odd prime powers -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For an odd prime power p^a dividing n>1, the ambient (n-1)-power kernel
has size gcd(p-1,n-1). Coprimality of p and n-1 cancels the p-power factor.
Used to bound the local subgroup by p-1 in unconditional witness counting. -/
theorem card_local_fermat_kernel_prime_pow {n p a : ℕ} (hn : 1 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hdiv : p ^ a ∣ n) :
    Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker =
      (p - 1).gcd (n - 1) := by
  have hcop : p.Coprime (n - 1) :=
    ((Nat.coprime_self_sub_right hn.le).mpr (Nat.coprime_one_right n)).of_dvd_left
      ((dvd_pow_self p ha.ne').trans hdiv)
  rw [card_unitPowerKernel_prime_pow hp hp2 ha]
  exact (hcop.pow_left (a - 1)).gcd_mul_left_cancel (p - 1)

end PseudoPrime.NumberTheory
